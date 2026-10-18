import Mathlib

/-!
# The Arzelà–Ascoli theorem
-/

open Filter Topology

namespace ArzelaAscoli

variable {K : Type*} [MetricSpace K] [CompactSpace K]

/-! ### Definitions -/

/-- `F ⊆ C(K)` is *equicontinuous*: for every `x` and `ε > 0` there is a `δ > 0`
(depending on `x` and `ε`, but not on `f ∈ F`) such that `d(x, y) < δ → |f x - f y| < ε`
for all `f ∈ F`. -/
def Equicont (F : Set C(K, ℝ)) : Prop :=
  ∀ x : K, ∀ ε > 0, ∃ δ > 0, ∀ y : K, dist x y < δ → ∀ f ∈ F, dist (f x) (f y) < ε

/-- `F ⊆ C(K)` is *uniformly equicontinuous*: `δ` depends only on `ε`. -/
def UniEquicont (F : Set C(K, ℝ)) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x y : K, dist x y < δ → ∀ f ∈ F, dist (f x) (f y) < ε

/-! ### Small helper lemmas -/

/-- `|f x| ≤ ‖f‖` for the sup norm. -/
lemma norm_apply_le (f : C(K, ℝ)) (x : K) : |f x| ≤ ‖f‖ := by
  have h : ‖f x‖ ≤ ‖f‖ := by
    first
    | exact f.norm_coe_le_norm x
  rwa [Real.norm_eq_abs] at h

/-- Pointwise distance is bounded by the sup distance. -/
lemma dist_apply_le (f g : C(K, ℝ)) (x : K) : dist (f x) (g x) ≤ dist f g := by
  first
  | exact ContinuousMap.dist_apply_le_dist (f := f) (g := g) x

/-- The sup distance is bounded by a uniform pointwise bound. -/
lemma dist_le_of_forall (f g : C(K, ℝ)) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x, dist (f x) (g x) ≤ C) : dist f g ≤ C := by
  first
  | exact (ContinuousMap.dist_le (f := f) (g := g) hC).2 h

/-- A subset of `C(K)` is bounded iff its elements have uniformly bounded sup norm. -/
lemma isBounded_iff_norm {F : Set C(K, ℝ)} :
    Bornology.IsBounded F ↔ ∃ C, ∀ f ∈ F, ‖f‖ ≤ C := by
  rw [Metric.isBounded_iff_subset_closedBall (0 : C(K, ℝ))]
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r, fun f hf => by simpa using hr hf⟩
  · rintro ⟨C, hC⟩
    exact ⟨C, fun f hf => by simpa using hC f hf⟩

/-- A dense sequence comes arbitrarily close to every point. -/
lemma exists_dense_close {x : ℕ → K} (hx : DenseRange x) (p : K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ i, dist p (x i) < δ := by
  obtain ⟨y, ⟨i, rfl⟩, hy⟩ := Metric.mem_closure_iff.1 (hx p) δ hδ
  exact ⟨i, hy⟩

/-- The minimum of finitely many positive numbers is positive. -/
lemma exists_pos_le_of_finite {ι : Type*} {s : Set ι} (hs : s.Finite) (r : ι → ℝ)
    (hr : ∀ i, 0 < r i) : ∃ δ > 0, ∀ i ∈ s, δ ≤ r i := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, fun i hi => by simp at hi⟩
  · obtain ⟨i₀, -, hmin⟩ := Set.exists_min_image s r hs hne
    exact ⟨r i₀, hr i₀, hmin⟩

/-- Theorem 1.67 (Heine–Cantor), in the form used below: every `f ∈ C(K)` is uniformly
continuous. -/
lemma unifCont (f : C(K, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x y : K, dist x y < δ → dist (f x) (f y) < ε := by
  obtain ⟨δ, hδ, h⟩ :=
    Metric.uniformContinuous_iff.1
      (CompactSpace.uniformContinuous_of_continuous f.continuous) ε hε
  exact ⟨δ, hδ, fun x y hxy => h hxy⟩

/-- Bolzano–Weierstrass: a bounded real sequence has a convergent subsequence. -/
lemma bolzano_weierstrass (y : ℕ → ℝ) (C : ℝ) (hy : ∀ n, |y n| ≤ C) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ L : ℝ, Tendsto (y ∘ ψ) atTop (𝓝 L) := by
  have hmem : ∀ n, y n ∈ Set.Icc (-C) C := fun n => abs_le.1 (hy n)
  obtain ⟨L, -, ψ, hψ, hL⟩ := isCompact_Icc.tendsto_subseq hmem
  exact ⟨ψ, hψ, L, hL⟩

/-! ### Theorem 2.11 -/

/-- **Theorem 2.11.** On a compact metric space, an equicontinuous family is uniformly
equicontinuous. -/
lemma uniformEquicont_of_equicont {F : Set C(K, ℝ)} (hF : Equicont F) : UniEquicont F := by
  intro ε hε
  have h : ∀ x : K, ∃ δ > 0, ∀ y : K, dist x y < δ → ∀ f ∈ F, dist (f x) (f y) < ε / 2 :=
    fun x => hF x (ε / 2) (half_pos hε)
  choose δ hδ hδ' using h
  -- cover `K` by finitely many balls `B(x, δ x / 2)`
  obtain ⟨t, ht⟩ := (isCompact_univ : IsCompact (Set.univ : Set K)).elim_finite_subcover
    (fun x : K => Metric.ball x (δ x / 2)) (fun x => Metric.isOpen_ball)
    (fun y _ => Set.mem_iUnion.2 ⟨y, Metric.mem_ball_self (half_pos (hδ y))⟩)
  -- `η` is the minimum of the finitely many radii `δ x / 2`, `x ∈ t`
  obtain ⟨η, hη, hηle⟩ :=
    exists_pos_le_of_finite t.finite_toSet (fun x => δ x / 2) (fun x => half_pos (hδ x))
  refine ⟨η, hη, fun y z hyz f hf => ?_⟩
  obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
  have hy : dist y x < δ x / 2 := Metric.mem_ball.1 hyx
  have hδx : 0 < δ x := hδ x
  have hxy : dist x y < δ x := by rw [dist_comm]; linarith
  have hηx : η ≤ δ x / 2 := hηle x (Finset.mem_coe.2 hxt)
  have hxz : dist x z < δ x := by
    have h1 : dist x z ≤ dist x y + dist y z := dist_triangle _ _ _
    have h2 : dist x y = dist y x := dist_comm _ _
    linarith
  have h1 := hδ' x y hxy f hf
  have h2 := hδ' x z hxz f hf
  have h3 : dist (f y) (f z) ≤ dist (f y) (f x) + dist (f x) (f z) := dist_triangle _ _ _
  have h4 : dist (f y) (f x) = dist (f x) (f y) := dist_comm _ _
  linarith

/-! ### Part 1: an unbounded set is not precompact -/

lemma not_isCompact_closure_of_unbounded {F : Set C(K, ℝ)}
    (hF : ¬ Bornology.IsBounded F) : ¬ IsCompact (closure F) := by
  intro hcpt
  -- since `F` is unbounded, there is always some `f ∈ F` with `‖f‖ > r + 1`
  have hex : ∀ r : ℝ, ∃ f ∈ F, r + 1 < ‖f‖ := by
    intro r
    by_contra h
    apply hF
    rw [isBounded_iff_norm]
    refine ⟨r + 1, fun f hf => ?_⟩
    by_contra hlt
    exact h ⟨f, hf, not_le.1 hlt⟩
  choose g hgF hgnorm using hex
  -- a sequence `u n ∈ F` with `‖u (n+1)‖ ≥ ‖u n‖ + 1`
  obtain ⟨u, hu0, hu⟩ : ∃ u : ℕ → C(K, ℝ), u 0 = g 0 ∧ ∀ n, u (n + 1) = g ‖u n‖ :=
    ⟨fun n => Nat.rec (motive := fun _ => C(K, ℝ)) (g 0) (fun _ prev => g ‖prev‖) n,
      rfl, fun n => rfl⟩
  have huF : ∀ n, u n ∈ F
    | 0 => by rw [hu0]; exact hgF 0
    | n + 1 => by rw [hu n]; exact hgF _
  have hgap : ∀ n, ‖u n‖ + 1 ≤ ‖u (n + 1)‖ := by
    intro n
    rw [hu n]
    exact (hgnorm ‖u n‖).le
  have key : ∀ m k : ℕ, ‖u m‖ + 1 ≤ ‖u (m + k + 1)‖ := by
    intro m k
    induction k with
    | zero =>
      first
      | exact hgap m
    | succ k ih =>
      have h1 := hgap (m + k + 1)
      change ‖u m‖ + 1 ≤ ‖u (m + k + 1 + 1)‖
      linarith
  -- hence `‖u m - u n‖ ≥ 1` for `m < n`
  have hsep : ∀ m n : ℕ, m < n → 1 ≤ dist (u m) (u n) := by
    intro m n hmn
    obtain ⟨k, rfl⟩ : ∃ k, n = m + k + 1 := ⟨n - m - 1, by omega⟩
    have h := key m k
    have h2 : ‖u (m + k + 1)‖ - ‖u m‖ ≤ ‖u (m + k + 1) - u m‖ := by
      first
      | exact norm_sub_norm_le _ _
    rw [dist_comm, dist_eq_norm]
    linarith
  -- but `closure F` is compact, so `(u n)` has a convergent, hence Cauchy, subsequence
  have hu_mem : ∀ n, u n ∈ closure F := fun n => subset_closure (huF n)
  obtain ⟨a, -, φ, hφ, hlim⟩ := hcpt.tendsto_subseq hu_mem
  have hcau : CauchySeq (u ∘ φ) := hlim.cauchySeq
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hcau 1 one_pos
  have h1 : dist (u (φ N)) (u (φ (N + 1))) < 1 := hN N le_rfl (N + 1) (Nat.le_succ N)
  have h2 := hsep (φ N) (φ (N + 1)) (hφ (by omega : N < N + 1))
  linarith

/-! ### Part 2: a precompact set is (uniformly) equicontinuous -/

lemma uniformEquicont_of_isCompact_closure {F : Set C(K, ℝ)}
    (hF : IsCompact (closure F)) : UniEquicont F := by
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  -- `closure F ⊆ ⋃_{f ∈ F} B_{ε/3}(f)`, because `F` is dense in its closure
  have hcover : closure F ⊆ ⋃ f ∈ F, Metric.ball f (ε / 3) := by
    intro g hg
    obtain ⟨f, hfF, hgf⟩ := Metric.mem_closure_iff.1 hg (ε / 3) hε3
    exact Set.mem_iUnion₂.2 ⟨f, hfF, Metric.mem_ball.2 hgf⟩
  have hopen : ∀ f ∈ F, IsOpen (Metric.ball f (ε / 3)) := fun f _ => Metric.isOpen_ball
  -- by compactness a finite subfamily `{f₁, …, f_k} ⊆ F` suffices
  obtain ⟨b, hbF, hbfin, hbcover⟩ := hF.elim_finite_subcover_image hopen hcover
  -- each `f` is uniformly continuous: choose `δ f` for `ε / 3`
  have hu : ∀ f : C(K, ℝ), ∃ δ > 0, ∀ x y : K, dist x y < δ → dist (f x) (f y) < ε / 3 :=
    fun f => unifCont f hε3
  choose δ hδ hδ' using hu
  -- `δ₀ = min δ_i > 0`
  obtain ⟨δ₀, hδ₀, hδ₀le⟩ := exists_pos_le_of_finite hbfin δ hδ
  refine ⟨δ₀, hδ₀, fun x y hxy g hg => ?_⟩
  -- pick `f = f_i` with `‖g - f_i‖ < ε/3`
  obtain ⟨f, hfb, hgf⟩ := Set.mem_iUnion₂.1 (hbcover (subset_closure hg))
  have h1 : dist (f x) (f y) < ε / 3 := hδ' f x y (lt_of_lt_of_le hxy (hδ₀le f hfb))
  have h2 : dist g f < ε / 3 := Metric.mem_ball.1 hgf
  have h3 : dist f g < ε / 3 := by rw [dist_comm]; exact h2
  have h4 : dist (g x) (f x) ≤ dist g f := dist_apply_le g f x
  have h5 : dist (f y) (g y) ≤ dist f g := dist_apply_le f g y
  have t1 : dist (g x) (g y) ≤ dist (g x) (f x) + dist (f x) (g y) := dist_triangle _ _ _
  have t2 : dist (f x) (g y) ≤ dist (f x) (f y) + dist (f y) (g y) := dist_triangle _ _ _
  linarith

/-! ### Part 3: a bounded, equicontinuous set is precompact -/

/-- The diagonal argument.  If `a k n` is a bounded double sequence, there is a single
subsequence `D` along which `n ↦ a k (D n)` converges for **every** `k`.

Construction (as in the paper): `Φ 0 = id` and `Φ (k+1) = Φ k ∘ ψ k (Φ k)`, where
`ψ k φ` is a subsequence along which `a k ∘ φ` converges; then take `D n = Φ (n+1) n`. -/
lemma diagonal_subseq (a : ℕ → ℕ → ℝ) (C : ℝ) (hbd : ∀ k n, |a k n| ≤ C) :
    ∃ D : ℕ → ℕ, StrictMono D ∧
      ∀ k, ∃ L : ℝ, Tendsto (fun n => a k (D n)) atTop (𝓝 L) := by
  -- one step: any subsequence `φ` has a further subsequence along which `a k` converges
  have step : ∀ (k : ℕ) (φ : ℕ → ℕ), ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∃ L : ℝ, Tendsto (fun n => a k (φ (ψ n))) atTop (𝓝 L) := by
    intro k φ
    obtain ⟨ψ, hψ, L, hL⟩ :=
      bolzano_weierstrass (fun n => a k (φ n)) C (fun n => hbd k (φ n))
    exact ⟨ψ, hψ, L, hL⟩
  choose ψ hψ hψL using step
  -- the nested subsequences
  obtain ⟨Φ, hΦ0, hΦ⟩ : ∃ Φ : ℕ → ℕ → ℕ, Φ 0 = id ∧
      ∀ k, Φ (k + 1) = Φ k ∘ ψ k (Φ k) :=
    ⟨fun k => Nat.rec (motive := fun _ => ℕ → ℕ) id (fun j φ => φ ∘ ψ j φ) k,
      rfl, fun k => rfl⟩
  have hΦmono : ∀ k, StrictMono (Φ k) := by
    intro k
    induction k with
    | zero => rw [hΦ0]; exact strictMono_id
    | succ k ih => rw [hΦ k]; exact ih.comp (hψ k (Φ k))
  -- `Φ m` is a subsequence of `Φ k` whenever `k ≤ m`
  have factor : ∀ k d : ℕ, ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∀ n, Φ (k + d) n = Φ k (θ n) := by
    intro k d
    induction d with
    | zero => exact ⟨id, strictMono_id, fun n => rfl⟩
    | succ d ih =>
      obtain ⟨θ, hθ, hθ'⟩ := ih
      refine ⟨θ ∘ ψ (k + d) (Φ (k + d)), hθ.comp (hψ _ _), fun n => ?_⟩
      have h1 : Φ (k + d + 1) n = Φ (k + d) (ψ (k + d) (Φ (k + d)) n) :=
        congrFun (hΦ (k + d)) n
      have h2 := hθ' (ψ (k + d) (Φ (k + d)) n)
      change Φ (k + d + 1) n = Φ k (θ (ψ (k + d) (Φ (k + d)) n))
      rw [h1]
      exact h2
  refine ⟨fun n => Φ (n + 1) n, ?_, ?_⟩
  · -- the diagonal sequence is strictly increasing
    apply strictMono_nat_of_lt_succ
    intro n
    have h1 : n + 1 ≤ ψ (n + 1) (Φ (n + 1)) (n + 1) :=
      (hψ (n + 1) (Φ (n + 1))).id_le (n + 1)
    have h2 : Φ (n + 1) n < Φ (n + 1) (n + 1) :=
      hΦmono (n + 1) (by omega : n < n + 1)
    have h3 : Φ (n + 1) (n + 1) ≤ Φ (n + 1) (ψ (n + 1) (Φ (n + 1)) (n + 1)) :=
      (hΦmono (n + 1)).monotone h1
    have h4 : Φ (n + 1 + 1) (n + 1) = Φ (n + 1) (ψ (n + 1) (Φ (n + 1)) (n + 1)) :=
      congrFun (hΦ (n + 1)) (n + 1)
    change Φ (n + 1) n < Φ (n + 1 + 1) (n + 1)
    exact lt_of_lt_of_le h2 (h3.trans h4.symm.le)
  · -- for each `k`, the diagonal sequence is eventually a subsequence of `Φ (k+1)`
    intro k
    obtain ⟨L, hL⟩ := hψL k (Φ k)
    have hL' : Tendsto (fun m => a k (Φ (k + 1) m)) atTop (𝓝 L) := by
      rw [hΦ k]; exact hL
    refine ⟨L, Metric.tendsto_atTop.2 fun ε hε => ?_⟩
    obtain ⟨M, hM⟩ := Metric.tendsto_atTop.1 hL' ε hε
    refine ⟨max M k, fun n hn => ?_⟩
    have hkn : k ≤ n := le_trans (le_max_right _ _) hn
    have hMn : M ≤ n := le_trans (le_max_left _ _) hn
    obtain ⟨θ, hθ, hθ'⟩ := factor (k + 1) (n - k)
    have hidx : k + 1 + (n - k) = n + 1 := by omega
    rw [hidx] at hθ'
    have hθn : n ≤ θ n := hθ.id_le n
    have h := hM (θ n) (le_trans hMn hθn)
    change dist (a k (Φ (n + 1) n)) L < ε
    rw [hθ' n]
    exact h

/-- Every sequence in a bounded, uniformly equicontinuous family has a Cauchy subsequence
(for the sup norm).  This is the "third part" of the paper's proof. -/
lemma exists_cauchy_subseq [Nonempty K] {F : Set C(K, ℝ)} {C : ℝ}
    (hC : ∀ f ∈ F, ‖f‖ ≤ C) (hF : UniEquicont F)
    (f : ℕ → C(K, ℝ)) (hf : ∀ n, f n ∈ F) :
    ∃ D : ℕ → ℕ, StrictMono D ∧ CauchySeq (fun k => f (D k)) := by
  -- Lemma 1.63: a countable dense set `{x₀, x₁, …}` in `K`
  obtain ⟨x, hx⟩ := TopologicalSpace.exists_dense_seq K
  -- diagonal subsequence `g k = f (D k)` with `g k (x i)` convergent for all `i`
  have hbd : ∀ k n, |f n (x k)| ≤ C :=
    fun k n => (norm_apply_le (f n) (x k)).trans (hC _ (hf n))
  obtain ⟨D, hD, hconv⟩ := diagonal_subseq (fun k n => f n (x k)) C hbd
  refine ⟨D, hD, ?_⟩
  -- uniform Cauchy-ness
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hη : 0 < ε / 4 := by positivity
  -- uniform equicontinuity gives one `δ` for all `g k`
  obtain ⟨δ, hδ, hδF⟩ := hF (ε / 4) hη
  -- `K ⊆ ⋃ B_δ(x_i)`, and by compactness finitely many `i ∈ t` suffice
  obtain ⟨t, ht⟩ := (isCompact_univ : IsCompact (Set.univ : Set K)).elim_finite_subcover
    (fun i : ℕ => Metric.ball (x i) δ) (fun i => Metric.isOpen_ball)
    (fun p _ => by
      obtain ⟨i, hi⟩ := exists_dense_close hx p hδ
      exact Set.mem_iUnion.2 ⟨i, Metric.mem_ball.2 hi⟩)
  -- each `(g k (x i))_k` converges, hence is Cauchy
  have hN : ∀ i : ℕ, ∃ N : ℕ, ∀ j ≥ N, ∀ k ≥ N,
      dist (f (D j) (x i)) (f (D k) (x i)) < ε / 4 := by
    intro i
    obtain ⟨L, hL⟩ := hconv i
    exact Metric.cauchySeq_iff.1 hL.cauchySeq (ε / 4) hη
  choose N hN using hN
  refine ⟨t.sup N, fun j hj k hk => ?_⟩
  show dist (f (D j)) (f (D k)) < ε
  have hdist : dist (f (D j)) (f (D k)) ≤ ε / 4 * 3 := by
    refine dist_le_of_forall _ _ (by positivity) (fun p => ?_)
    -- `p ∈ B_δ(x_i)` for some `i ∈ t`
    obtain ⟨i, hit, hpi⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ p))
    have hpi' : dist p (x i) < δ := Metric.mem_ball.1 hpi
    have h1 := hδF p (x i) hpi' (f (D j)) (hf (D j))
    have h2 := hδF p (x i) hpi' (f (D k)) (hf (D k))
    have hjN : N i ≤ j := le_trans (Finset.le_sup (f := N) hit) hj
    have hkN : N i ≤ k := le_trans (Finset.le_sup (f := N) hit) hk
    have h3 := hN i j hjN k hkN
    have h2' : dist (f (D k) (x i)) (f (D k) p) < ε / 4 := by rw [dist_comm]; exact h2
    have t1 := dist_triangle (f (D j) p) (f (D j) (x i)) (f (D k) p)
    have t2 := dist_triangle (f (D j) (x i)) (f (D k) (x i)) (f (D k) p)
    linarith
  linarith

/-- Part 3: a bounded, equicontinuous set is precompact (its closure is compact). -/
lemma isCompact_closure_of_bounded_equicont {F : Set C(K, ℝ)}
    (hb : Bornology.IsBounded F) (he : Equicont F) : IsCompact (closure F) := by
  rcases isEmpty_or_nonempty K with hK | hK
  · -- if `K` is empty, `C(K)` has at most one point
    have hsub : (closure F).Subsingleton :=
      fun f _ g _ => ContinuousMap.ext fun p => (hK.false p).elim
    first
    | exact hsub.isCompact
  · obtain ⟨C, hC⟩ := isBounded_iff_norm.1 hb
    have hue : UniEquicont F := uniformEquicont_of_equicont he   -- Theorem 2.11
    -- in a metric space, compact ⇔ sequentially compact
    have hseq : IsSeqCompact (closure F) := by
      intro h hh
      -- approximate `h n ∈ closure F` by `f n ∈ F`
      have hex : ∀ n : ℕ, ∃ f ∈ F, dist (h n) f < 1 / ((n : ℝ) + 1) := fun n =>
        Metric.mem_closure_iff.1 (hh n) (1 / ((n : ℝ) + 1)) (by positivity)
      choose f hfF hfh using hex
      -- a Cauchy subsequence of `(f n)`, convergent since `C(K)` is complete
      obtain ⟨D, hD, hcau⟩ := exists_cauchy_subseq hC hue f hfF
      obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hcau
      refine ⟨a, ?_, D, hD, ?_⟩
      · exact mem_closure_of_tendsto ha (Filter.eventually_atTop.2 ⟨0, fun n _ => hfF (D n)⟩)
      · refine Metric.tendsto_atTop.2 fun ε hε => ?_
        obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1 ha (ε / 2) (half_pos hε)
        obtain ⟨N₂, hN₂⟩ := exists_nat_one_div_lt (half_pos hε)
        refine ⟨max N₁ N₂, fun n hn => ?_⟩
        have hn1 : N₁ ≤ n := le_trans (le_max_left _ _) hn
        have hn2 : N₂ ≤ n := le_trans (le_max_right _ _) hn
        have hDn : n ≤ D n := hD.id_le n
        have h1 : dist (f (D n)) a < ε / 2 := hN₁ n hn1
        have h2 : dist (h (D n)) (f (D n)) < 1 / (((D n : ℕ) : ℝ) + 1) := hfh (D n)
        have h3 : 1 / (((D n : ℕ) : ℝ) + 1) ≤ 1 / ((N₂ : ℝ) + 1) := by
          apply one_div_le_one_div_of_le
          · positivity
          · have : (N₂ : ℝ) ≤ (D n : ℝ) := by exact_mod_cast hn2.trans hDn
            linarith
        have h4 : dist (h (D n)) a ≤ dist (h (D n)) (f (D n)) + dist (f (D n)) a :=
          dist_triangle _ _ _
        change dist (h (D n)) a < ε
        linarith
    first
    | exact hseq.isCompact

/-! ### The Arzelà–Ascoli theorem -/

/-- **Arzelà–Ascoli.**  Let `K` be a compact metric space.  A subset of `C(K)` is compact if and
only if it is closed, bounded and equicontinuous. -/
theorem arzela_ascoli (F : Set C(K, ℝ)) :
    IsCompact F ↔ IsClosed F ∧ Bornology.IsBounded F ∧ Equicont F := by
  constructor
  · intro hF
    -- compact ⇒ closed, and precompact (closure = F)
    have hclosed : IsClosed F := hF.isClosed
    have hpre : IsCompact (closure F) := by rwa [hclosed.closure_eq]
    refine ⟨hclosed, ?_, ?_⟩
    · -- Part 1: precompact ⇒ bounded
      by_contra hunb
      exact not_isCompact_closure_of_unbounded hunb hpre
    · -- Part 2: precompact ⇒ equicontinuous
      intro x ε hε
      obtain ⟨δ, hδ, h⟩ := uniformEquicont_of_isCompact_closure hpre ε hε
      exact ⟨δ, hδ, fun y hxy f hf => h x y hxy f hf⟩
  · rintro ⟨hclosed, hb, he⟩
    -- Part 3: bounded ∧ equicontinuous ⇒ precompact; closed ⇒ compact
    have hpre : IsCompact (closure F) := isCompact_closure_of_bounded_equicont hb he
    rwa [hclosed.closure_eq] at hpre

end ArzelaAscoli

#print axioms ArzelaAscoli.arzela_ascoli
