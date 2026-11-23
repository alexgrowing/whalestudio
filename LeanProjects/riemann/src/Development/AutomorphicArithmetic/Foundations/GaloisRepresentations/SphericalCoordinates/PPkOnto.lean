import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFrameEx

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

namespace UpperTheory.Gal.W2.PeriodSurjective

variable {p : ℕ} [Fact p.Prime]

private theorem tr_bound (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ z : K, ‖Algebra.trace ℚ_[p] K z‖ ≤ c * ‖(z : PadicAlgCl p)‖ := by
  let f : K →L[ℚ_[p]] ℚ_[p] := LinearMap.toContinuousLinearMap (Algebra.trace ℚ_[p] K)
  refine ⟨‖f‖, norm_nonneg _, fun z => ?_⟩
  exact f.le_opNorm z

private theorem norm_nat_coprime {m : ℕ} (hm : m.Coprime p) : ‖((m : ℕ) : PadicAlgCl p)‖ = 1 := by
  have hp : p.Prime := Fact.out
  have h1 : ((m : ℕ) : PadicAlgCl p) = (((m : ℚ) : ℚ_[p]) : PadicAlgCl p) := by simp
  rw [h1, PadicAlgCl.norm_extends, Padic.eq_padicNorm]
  have hnd : ¬ p ∣ m := (Nat.Prime.coprime_iff_not_dvd hp).1 hm.symm
  have := (padicNorm.nat_eq_one_iff m).2 hnd
  exact_mod_cast this

private theorem norm_p_lt : ‖((p : ℕ) : PadicAlgCl p)‖ < 1 := by
  have h1 : ((p : ℕ) : PadicAlgCl p) = (((p : ℕ) : ℚ_[p]) : PadicAlgCl p) := by simp
  rw [h1, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

private theorem pairL_comm {G : HTGroup p} (a b : Loc G) : pairL a b = pairL b a := by
  unfold pairL
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [dotProduct_comm]

private theorem pairL_add {G : HTGroup p} (a b b' : Loc G) : pairL a (b + b') = pairL a b + pairL a b' := by
  unfold pairL
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Pi.add_apply, dotProduct_add, map_add]

private theorem pair_small {G : HTGroup p} (t : Loc G) {e : ℝ} (he : 0 < e) :
    ∃ d : ℝ, 0 < d ∧ ∀ b : Loc G, (∀ w i, ‖(b w i : PadicAlgCl p)‖ < d) → ‖pairL t b‖ ≤ e := by
  have hfd : ∀ w, ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : G.Fw w, ‖Algebra.trace ℚ_[p] (G.Fw w) z‖ ≤ C * ‖(z : PadicAlgCl p)‖ :=
    fun w => tr_bound (G.Fw w)
  choose C hC0 hC using hfd
  have hK : 0 < 1 + ∑ w, ∑ i, ‖(t w i : PadicAlgCl p)‖ := by positivity
  set K := 1 + ∑ w, ∑ i, ‖(t w i : PadicAlgCl p)‖ with hKeq
  have htK : ∀ w i, ‖(t w i : PadicAlgCl p)‖ ≤ K := by
    intro w i
    have h1 : ‖(t w i : PadicAlgCl p)‖ ≤ ∑ i', ‖(t w i' : PadicAlgCl p)‖ :=
      Finset.single_le_sum (f := fun i' => ‖(t w i' : PadicAlgCl p)‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_univ i)
    have h2 : ∑ i', ‖(t w i' : PadicAlgCl p)‖ ≤ ∑ w', ∑ i', ‖(t w' i' : PadicAlgCl p)‖ :=
      Finset.single_le_sum (f := fun w' => ∑ i', ‖(t w' i' : PadicAlgCl p)‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ w)
    linarith
  have hCs : 0 ≤ ∑ w, C w := Finset.sum_nonneg fun w _ => hC0 w
  have hC' : 0 < 1 + ∑ w, C w := by linarith
  set C' := 1 + ∑ w, C w with hCeq
  have hCw : ∀ w, C w ≤ C' := by
    intro w
    have := Finset.single_le_sum (f := C) (fun w _ => hC0 w) (Finset.mem_univ w)
    linarith
  refine ⟨e / (C' * K), by positivity, fun b hb => ?_⟩
  unfold pairL
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg he.le fun w _ => ?_
  have hdot : ‖((t w ⬝ᵥ b w : G.Fw w) : PadicAlgCl p)‖ ≤ K * (e / (C' * K)) := by
    rw [dotProduct, IntermediateField.coe_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i _ => ?_
    rw [IntermediateField.coe_mul, norm_mul]
    exact mul_le_mul (htK w i) (hb w i).le (norm_nonneg _) hK.le
  calc ‖Algebra.trace ℚ_[p] (G.Fw w) (t w ⬝ᵥ b w)‖
      ≤ C w * ‖((t w ⬝ᵥ b w : G.Fw w) : PadicAlgCl p)‖ := hC w _
    _ ≤ C' * (K * (e / (C' * K))) := mul_le_mul (hCw w) hdot (norm_nonneg _) hC'.le
    _ = e := by field_simp

private theorem dense_top (K : IntermediateField ℚ_[p] (PadicAlgCl p)) {n : ℕ} (W : Submodule K (Fin n → K))
    (hd : ∀ (i : Fin n) (k : ℕ), ∃ a' : Fin n → K, (∀ j, ‖(a' j : PadicAlgCl p)‖ ≤ 1) ∧ (Pi.single i 1 + p ^ k • a' : Fin n → K) ∈ W) :
    W = ⊤ := by
  classical
  choose a' ha'1 ha'W using fun i => hd i 1
  let v : Fin n → (Fin n → K) := fun i => Pi.single i 1 + p ^ 1 • a' i
  have hli : LinearIndependent K v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    by_contra hne
    push_neg at hne
    obtain ⟨i0, hi0⟩ := hne
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ
      (fun i => ‖(c i : PadicAlgCl p)‖) ⟨i0, Finset.mem_univ _⟩
    have hcj : ∑ i, c i * v i j = 0 := by
      have := congrFun hc j
      simpa [Finset.sum_apply] using this
    have e1 : ∑ i, c i * v i j = c j + (p : K) * ∑ i, c i * a' i j := by
      simp [v, mul_add, Finset.sum_add_distrib, Pi.single_apply, Finset.mul_sum, mul_left_comm]
    have e2 : c j = -((p : K) * ∑ i, c i * a' i j) := by
      rw [eq_neg_iff_add_eq_zero, ← e1]
      exact hcj
    have hS : ‖((∑ i, c i * a' i j : K) : PadicAlgCl p)‖ ≤ ‖(c j : PadicAlgCl p)‖ := by
      push_cast
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
      rw [norm_mul]
      calc ‖(c i : PadicAlgCl p)‖ * ‖(a' i j : PadicAlgCl p)‖ ≤ ‖(c i : PadicAlgCl p)‖ * 1 :=
            mul_le_mul_of_nonneg_left (ha'1 i j) (norm_nonneg _)
        _ = ‖(c i : PadicAlgCl p)‖ := _root_.mul_one _
        _ ≤ ‖(c j : PadicAlgCl p)‖ := hj i (Finset.mem_univ _)
    have hpc : (((p : K)) : PadicAlgCl p) = ((p : ℕ) : PadicAlgCl p) := by simp
    have hcj' : ‖(c j : PadicAlgCl p)‖ =
        ‖((p : ℕ) : PadicAlgCl p)‖ * ‖((∑ i, c i * a' i j : K) : PadicAlgCl p)‖ := by
      rw [e2, IntermediateField.coe_neg, IntermediateField.coe_mul, norm_neg, norm_mul, hpc]
    have hne0 : (c i0 : PadicAlgCl p) ≠ 0 := by exact_mod_cast hi0
    have hpos : 0 < ‖(c j : PadicAlgCl p)‖ :=
      lt_of_lt_of_le (norm_pos_iff.2 hne0) (hj i0 (Finset.mem_univ _))
    have hp := norm_p_lt (p := p)
    have h1 : ‖((p : ℕ) : PadicAlgCl p)‖ * ‖((∑ i, c i * a' i j : K) : PadicAlgCl p)‖ ≤
        ‖((p : ℕ) : PadicAlgCl p)‖ * ‖(c j : PadicAlgCl p)‖ :=
      mul_le_mul_of_nonneg_left hS (norm_nonneg _)
    have h2 : ‖((p : ℕ) : PadicAlgCl p)‖ * ‖(c j : PadicAlgCl p)‖ < 1 * ‖(c j : PadicAlgCl p)‖ :=
      mul_lt_mul_of_pos_right hp hpos
    linarith
  have htop : Submodule.span K (Set.range v) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simp)
  rw [eq_top_iff, ← htop, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact ha'W i

variable {D : Datum p} {G : HTGroup p} {L : Link D G} {β : G.Cˣ}

private theorem T_span (A : PFrame L β) (s₀ : Finset (VQ D)) (hs : Submodule.span ℚ (s₀ : Set (VQ D)) = ⊤) (w : Fin G.m) :
    Submodule.span (G.Fw w) ((s₀.image fun y => A.T y w : Finset (Fin G.n → G.Fw w)) : Set (Fin G.n → G.Fw w)) = ⊤ := by
  set W := Submodule.span (G.Fw w)
    (((s₀.image fun y => A.T y w : Finset (Fin G.n → G.Fw w))) : Set (Fin G.n → G.Fw w)) with hW
  have hmem : ∀ x : VQ D, A.T x w ∈ W := by
    intro x
    have hx : x ∈ Submodule.span ℚ (s₀ : Set (VQ D)) := by
      rw [hs]
      trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      apply Submodule.subset_span
      rw [Finset.coe_image]
      exact Set.mem_image_of_mem _ hy
    | zero =>
      rw [map_zero]
      exact W.zero_mem
    | add x y _ _ hx hy =>
      rw [map_add, Pi.add_apply]
      exact W.add_mem hx hy
    | smul q x _ hx =>
      rw [map_rat_smul, Pi.smul_apply]
      exact W.smul_of_tower_mem q hx
  apply dense_top (G.Fw w) W
  intro i k
  obtain ⟨x, a', b', ha', -, hT, -⟩ := A.dense (Pi.single w (Pi.single i 1)) 0 k
  unfold IntL at ha'
  refine ⟨a' w, fun j => ha' w j, ?_⟩
  have := congrFun hT w
  rw [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same] at this
  rw [← this]
  exact hmem x

private theorem scal_mulVec {K : Type} [Field K] {n : ℕ} (c : K) (v : Fin n → K) :
    Matrix.scalar (Fin n) c *ᵥ v = c • v := by
  ext i
  simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

private theorem scalT_mulVec {K : Type} [Field K] {n : ℕ} (c : K) (v : Fin n → K) :
    (Matrix.scalar (Fin n) c)ᵀ *ᵥ v = c • v := by
  rw [Matrix.scalar_apply, Matrix.diagonal_transpose, ← Matrix.scalar_apply]
  exact scal_mulVec c v

private theorem T_F (A : PFrame L β) (x : G.F) (y : VQ D) (w : Fin G.m) :
    A.T (L.rep (algebraMap G.F G.C x) y) w = G.embW w x • A.T y w := by
  rw [A.act, G.rho_F]
  exact scal_mulVec _ _

private theorem T'_F (A : PFrame L β) (x : G.F) (y : VQ D) (w : Fin G.m) :
    A.T' (L.rep (algebraMap G.F G.C x) y) w = G.embW w (IsCMField.complexConj G.F x) • A.T' y w := by
  rw [A.act', sh_algebraMap, ← Algebra.commutes, _root_.mul_assoc, Units.mul_inv, _root_.mul_one,
    G.rho_F, scalT_mulVec]
  rfl

private theorem rep_mem (hFI : FInt) {M : AddSubgroup (VQ D)} (hM : IsPLat D M) (x : G.F)
    (hx : ∀ w, ‖(G.embW w x : PadicAlgCl p)‖ ≤ 1 ∧ ‖(G.embW w (IsCMField.complexConj G.F x) : PadicAlgCl p)‖ ≤ 1)
    {y : VQ D} (hy : y ∈ M) : L.rep (algebraMap G.F G.C x) y ∈ M := by
  have hFI' := hFI
  unfold FInt at hFI'
  obtain ⟨m, c, hmc, hc⟩ := hFI' p G x hx
  unfold IsPLat at hM
  obtain ⟨hO, s, -, hMs⟩ := hM
  have key : m • (L.rep (algebraMap G.F G.C x) y) ∈ M := by
    have e1 : m • (L.rep (algebraMap G.F G.C x) y) = L.rep (algebraMap G.F G.C (c : G.F)) y := by
      rw [hc, map_mul, map_natCast, map_mul, map_natCast, Module.End.mul_apply,
        Module.End.natCast_apply]
    rw [e1]
    let c' : 𝓞 D.F := (RingOfIntegers.mapRingEquiv L.e).symm c
    have hc' : L.e (c' : D.F) = (c : G.F) := by
      simp [c']
    rw [← hc', L.rep_F]
    exact hO _ y hy
  obtain ⟨m', hm', hm'y⟩ := (hMs _).1 key
  refine (hMs _).2 ⟨m' * m, Nat.Coprime.mul hm' hmc, ?_⟩
  rw [mul_smul]
  exact hm'y

private theorem loc_bdd (t : Loc G) : ∃ K : ℝ, 0 < K ∧ ∀ w i, ‖(t w i : PadicAlgCl p)‖ ≤ K := by
  refine ⟨1 + ∑ w, ∑ i, ‖(t w i : PadicAlgCl p)‖, by positivity, fun w i => ?_⟩
  have h1 : ‖(t w i : PadicAlgCl p)‖ ≤ ∑ i', ‖(t w i' : PadicAlgCl p)‖ :=
    Finset.single_le_sum (f := fun i' => ‖(t w i' : PadicAlgCl p)‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ i)
  have h2 : ∑ i', ‖(t w i' : PadicAlgCl p)‖ ≤ ∑ w', ∑ i', ‖(t w' i' : PadicAlgCl p)‖ :=
    Finset.single_le_sum (f := fun w' => ∑ i', ‖(t w' i' : PadicAlgCl p)‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ w)
  linarith

private theorem small_mul {a b d K : ℝ} (hK : 0 < K) (ha0 : 0 ≤ a) (ha : a < d / K) (hb0 : 0 ≤ b) (hb : b ≤ K) : a * b < d := by
  calc a * b ≤ a * K := mul_le_mul_of_nonneg_left hb ha0
    _ < d / K * K := mul_lt_mul_of_pos_right ha hK
    _ = d := div_mul_cancel₀ d hK.ne'

private theorem twoVariableSeriesVanishesBelowDegree_one_shiftVariable (s : ℝ) (hs : 0 ≤ s) {t : ℝ} (h : t ≤ 1 / (s + 1)) (ht : 0 ≤ t) : s * t ≤ 1 := by
  have h1 : 0 < s + 1 := by linarith
  calc s * t ≤ s * (1 / (s + 1)) := mul_le_mul_of_nonneg_left h hs
    _ ≤ 1 := by
      rw [mul_one_div, div_le_one h1]
      linarith

private theorem core (hFA : FApprox) (hFI : FInt) (A : PFrame L β) {M : AddSubgroup (VQ D)} (hM : IsPLat D M)
    {s : ℚ} (hP : PerfAt L β s M) {x y : VQ D} (hx : x ∈ M) (hy : y ∈ M) (a : ∀ w, G.Fw w)
    (ha : ∀ w, ‖(a w : PadicAlgCl p)‖ ≤ 1) :
    ‖(s : ℚ_[p]) * pairL (A.T' x) (fun w => a w • A.T y w)‖ ≤ 1 := by
  have hp : p.Prime := Fact.out
  set S : ℝ := ‖(s : ℚ_[p])‖ with hS
  have hS0 : 0 ≤ S := norm_nonneg _
  have he : (0 : ℝ) < 1 / (S + 1) := by positivity
  obtain ⟨d₁, hd₁, hsm₁⟩ := pair_small (A.T' x) he
  obtain ⟨d₂, hd₂, hsm₂⟩ := pair_small (A.T x) he
  obtain ⟨K₁, hK₁, hb₁⟩ := loc_bdd (A.T y)
  obtain ⟨K₂, hK₂, hb₂⟩ := loc_bdd (A.T' y)
  set ε : ℝ := min (min (d₁ / K₁) (d₂ / K₂)) 1 with hε
  have hε0 : 0 < ε := lt_min (lt_min (div_pos hd₁ hK₁) (div_pos hd₂ hK₂)) one_pos
  have hε1 : ε ≤ d₁ / K₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hε2 : ε ≤ d₂ / K₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hε3 : ε ≤ 1 := min_le_right _ _
  have hFA' := hFA
  unfold FApprox at hFA'
  obtain ⟨xF, hxF⟩ := hFA' p G a 0 ε hε0
  have hda : ∀ w, ‖((a w - G.embW w xF : G.Fw w) : PadicAlgCl p)‖ < ε := by
    intro w
    rw [AddSubgroupClass.coe_sub, norm_sub_rev, ← AddSubgroupClass.coe_sub]
    exact (hxF w).1
  have hdc : ∀ w, ‖((G.embW w (IsCMField.complexConj G.F xF) : G.Fw w) : PadicAlgCl p)‖ < ε := by
    intro w
    have := (hxF w).2
    rw [Pi.zero_apply, sub_zero] at this
    exact this
  have hint : ∀ w, ‖((G.embW w xF : G.Fw w) : PadicAlgCl p)‖ ≤ 1 ∧
      ‖((G.embW w (IsCMField.complexConj G.F xF) : G.Fw w) : PadicAlgCl p)‖ ≤ 1 := by
    intro w
    refine ⟨?_, (hdc w).le.trans hε3⟩
    have e1 : ((G.embW w xF : G.Fw w) : PadicAlgCl p) =
        ((G.embW w xF - a w : G.Fw w) : PadicAlgCl p) + (a w : PadicAlgCl p) := by
      rw [AddSubgroupClass.coe_sub, sub_add_cancel]
    rw [e1]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (ha w))
    rw [AddSubgroupClass.coe_sub, norm_sub_rev, ← AddSubgroupClass.coe_sub]
    exact (hda w).le.trans hε3
  set y' := L.rep (algebraMap G.F G.C xF) y with hy'
  have hy'M : y' ∈ M := rep_mem hFI hM xF hint hy
  have hden := (hP y').1 hy'M x hx
  have hform : ‖((s * formB L β y' x : ℚ) : ℚ_[p])‖ ≤ 1 := by
    apply Padic.norm_rat_le_one
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 hden.symm
  have hsplit : (fun w => a w • A.T y w) = A.T y' + (fun w => (a w - G.embW w xF) • A.T y w) := by
    funext w
    rw [Pi.add_apply, hy', T_F, sub_smul, add_sub_cancel]
  have hAf := A.form y' x
  have hdecomp : (s : ℚ_[p]) * pairL (A.T' x) (fun w => a w • A.T y w) =
      ((s * formB L β y' x : ℚ) : ℚ_[p]) + (s : ℚ_[p]) * pairL (A.T x) (A.T' y') +
        (s : ℚ_[p]) * pairL (A.T' x) (fun w => (a w - G.embW w xF) • A.T y w) := by
    rw [hsplit, pairL_add, Rat.cast_mul, hAf, pairL_comm (A.T x) (A.T' y')]
    ring
  have hsmall1 : ‖(s : ℚ_[p]) * pairL (A.T' x) (fun w => (a w - G.embW w xF) • A.T y w)‖ ≤ 1 := by
    rw [norm_mul]
    refine twoVariableSeriesVanishesBelowDegree_one_shiftVariable S hS0 (hsm₁ _ fun w i => ?_) (norm_nonneg _)
    rw [Pi.smul_apply, smul_eq_mul, IntermediateField.coe_mul, norm_mul]
    exact small_mul hK₁ (norm_nonneg _) ((hda w).trans_le hε1) (norm_nonneg _) (hb₁ w i)
  have hsmall2 : ‖(s : ℚ_[p]) * pairL (A.T x) (A.T' y')‖ ≤ 1 := by
    rw [norm_mul]
    refine twoVariableSeriesVanishesBelowDegree_one_shiftVariable S hS0 (hsm₂ _ fun w i => ?_) (norm_nonneg _)
    rw [hy', T'_F, Pi.smul_apply, smul_eq_mul, IntermediateField.coe_mul, norm_mul]
    exact small_mul hK₂ (norm_nonneg _) ((hdc w).trans_le hε2) (norm_nonneg _) (hb₂ w i)
  rw [hdecomp]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hsmall1)
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hform hsmall2)

private def intSub (K : IntermediateField ℚ_[p] (PadicAlgCl p)) {n : ℕ} (g : Matrix (Fin n) (Fin n) K) :
    AddSubgroup (Fin n → K) where
  carrier := {v | ∀ i, ‖(((g *ᵥ v) i : K) : PadicAlgCl p)‖ ≤ 1}
  zero_mem' := by
    intro i
    simp
  add_mem' := by
    intro a b ha hb i
    rw [Matrix.mulVec_add, Pi.add_apply, IntermediateField.coe_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha i) (hb i))
  neg_mem' := by
    intro a ha i
    rw [Matrix.mulVec_neg, Pi.neg_apply, IntermediateField.coe_neg, norm_neg]
    exact ha i

private theorem intSub_div (K : IntermediateField ℚ_[p] (PadicAlgCl p)) {n : ℕ} (g : Matrix (Fin n) (Fin n) K)
    {m : ℕ} (hm : m.Coprime p) {v : Fin n → K} (h : m • v ∈ intSub K g) : v ∈ intSub K g := by
  intro i
  have hi : ‖(((g *ᵥ (m • v)) i : K) : PadicAlgCl p)‖ ≤ 1 := h i
  have e1 : (g *ᵥ (m • v)) i = (m : K) * (g *ᵥ v) i := by
    rw [← Nat.cast_smul_eq_nsmul K, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  rw [e1, IntermediateField.coe_mul, norm_mul] at hi
  have e2 : ((m : K) : PadicAlgCl p) = ((m : ℕ) : PadicAlgCl p) := by simp
  rw [e2, norm_nat_coprime hm, _root_.one_mul] at hi
  exact hi

private def pairSub (c : ℚ_[p]) (t : Loc G) : AddSubgroup (Loc G) where
  carrier := {b | ‖c * pairL t b‖ ≤ 1}
  zero_mem' := by
    simp [pairL]
  add_mem' := by
    intro a b ha hb
    show ‖c * pairL t (a + b)‖ ≤ 1
    rw [pairL_add, mul_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  neg_mem' := by
    intro a ha
    show ‖c * pairL t (-a)‖ ≤ 1
    have : pairL t (-a) = -pairL t a := by
      simp only [pairL, Pi.neg_apply, dotProduct_neg, map_neg, Finset.sum_neg_distrib]
    rw [this, mul_neg, norm_neg]
    exact ha

private theorem le_mem (hLL : LocLat) (hFA : FApprox) (hFI : FInt) (A : PFrame L β) {M : AddSubgroup (VQ D)}
    (hM : IsPLat D M) {s : ℚ} (hP : PerfAt L β s M) (c : ℚ_[p]ˣ) (hc : ((c⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) = (s : ℚ_[p])) :
    ∃ g : (w : Fin G.m) → GL (Fin G.n) (G.Fw w), ∀ x ∈ M, A.Mem (c, g) x := by
  have hM' := hM
  unfold IsPLat at hM
  obtain ⟨-, s₀, hs₀, hMs⟩ := hM
  have hs₀M : ∀ y ∈ s₀, y ∈ M := by
    intro y hy
    refine (hMs y).2 ⟨1, Nat.coprime_one_left p, ?_⟩
    rw [one_smul]
    exact AddSubgroup.subset_closure hy
  have hLL' := hLL
  unfold LocLat at hLL'
  choose g hg using fun w => hLL' p G w (s₀.image fun y => A.T y w) (T_span A s₀ hs₀ w)
  refine ⟨g, fun x hx => ?_⟩
  unfold PFrame.Mem
  refine ⟨?_, ?_⟩
  · unfold IntL
    intro w
    obtain ⟨m, hm, hmx⟩ := (hMs x).1 hx
    let N : AddSubgroup (VQ D) := (intSub (G.Fw w) ((g w)⁻¹ : GL (Fin G.n) (G.Fw w)).val).comap
      ((Pi.evalAddMonoidHom (fun w => Fin G.n → G.Fw w) w).comp A.T)
    have hcl : AddSubgroup.closure (s₀ : Set (VQ D)) ≤ N := by
      rw [AddSubgroup.closure_le]
      intro y hy
      have hy' : A.T y w ∈ s₀.image fun y => A.T y w := Finset.mem_image_of_mem _ hy
      refine (hg w (A.T y w)).2 ⟨fun v => if v = A.T y w then 1 else 0, ?_, ?_⟩
      · intro v
        dsimp only
        split_ifs <;> simp
      · symm
        rw [Finset.sum_eq_single (A.T y w)]
        · simp
        · intro v _ hv
          simp [hv]
        · intro h
          exact absurd hy' h
    have h1 : A.T (m • x) w ∈ intSub (G.Fw w) ((g w)⁻¹ : GL (Fin G.n) (G.Fw w)).val := hcl hmx
    rw [map_nsmul, Pi.smul_apply] at h1
    exact intSub_div _ _ hm h1
  · intro z hz
    unfold IntL at hz
    rw [hc]
    have hzi : ∀ w, ∀ i, ‖((((g w)⁻¹ : GL (Fin G.n) (G.Fw w)).val *ᵥ ((g w).val *ᵥ z w)) i : PadicAlgCl p)‖ ≤ 1 := by
      intro w i
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      exact hz w i
    choose a ha hsum using fun w => (hg w ((g w).val *ᵥ z w)).1 (hzi w)
    have key : (fun w => (g w).val *ᵥ z w) ∈ pairSub (s : ℚ_[p]) (A.T' x) := by
      have e : (fun w => (g w).val *ᵥ z w) =
          ∑ w, Pi.single w (∑ y ∈ s₀.image (fun y => A.T y w), a w y • y) := by
        conv_lhs => rw [← Finset.univ_sum_single (fun w => (g w).val *ᵥ z w)]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [← hsum w]
      rw [e]
      refine AddSubgroup.sum_mem _ fun w _ => ?_
      have e2 : (Pi.single w (∑ y ∈ s₀.image (fun y => A.T y w), a w y • y) : Loc G) =
          ∑ y ∈ s₀.image (fun y => A.T y w), (Pi.single w (a w y • y) : Loc G) :=
        map_sum (AddMonoidHom.single (fun w => Fin G.n → G.Fw w) w) _ _
      rw [e2]
      refine AddSubgroup.sum_mem _ fun y hy => ?_
      obtain ⟨y₀, hy₀, rfl⟩ := Finset.mem_image.1 hy
      have e3 : (Pi.single w (a w (A.T y₀ w) • A.T y₀ w) : Loc G) =
          fun w' => (Pi.single w (a w (A.T y₀ w)) : ∀ w', G.Fw w') w' • A.T y₀ w' := by
        funext w'
        by_cases h : w' = w
        · subst h
          simp
        · simp [Pi.single_eq_of_ne h]
      rw [e3]
      show ‖(s : ℚ_[p]) * pairL (A.T' x) _‖ ≤ 1
      refine core hFA hFI A hM' hP hx (hs₀M y₀ hy₀) _ fun w' => ?_
      by_cases h : w' = w
      · subst h
        rw [Pi.single_eq_same]
        exact ha w' _
      · rw [Pi.single_eq_of_ne h]
        simp
    exact key

end UpperTheory.Gal.W2.PeriodSurjective

theorem UpperTheory.Gal.W2.pkOnto_of :
    UpperTheory.Gal.W2.LocLat → UpperTheory.Gal.W2.FApprox → UpperTheory.Gal.W2.FInt → UpperTheory.Gal.W2.PkLat → UpperTheory.Gal.W2.PkPerf → UpperTheory.Gal.W2.OOnto → UpperTheory.Gal.W2.PkOnto := by
  intro hLL hFA hFI hPL hPP _hOO
  unfold PkLat at hPL
  unfold PkPerf at hPP
  unfold PkOnto
  intro p _ D G L β A hm M s hM hs hP
  have hs0 : (s : ℚ_[p]) ≠ 0 := by exact_mod_cast hs.ne'
  let c : ℚ_[p]ˣ := (Units.mk0 (s : ℚ_[p]) hs0)⁻¹
  have hc : ((c⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) = (s : ℚ_[p]) := by simp [c]
  obtain ⟨g, hg⟩ := UpperTheory.Gal.W2.PeriodSurjective.le_mem hLL hFA hFI A hM hP c hc
  refine ⟨(c, g), ?_⟩
  obtain ⟨M', hM', -⟩ := hPL p D G L β A hm (c, g)
  have hsc1 : (s : ℚ_[p]) * (c : ℚ_[p]) = 1 := by
    simp [c, hs0]
  have hsc : ‖(s : ℚ_[p]) * (((c, g) : Gp G).1 : ℚ_[p])‖ = 1 := by
    rw [show (((c, g) : Gp G).1 : ℚ_[p]) = (c : ℚ_[p]) from rfl, hsc1, norm_one]
  have hP' := hPP p D G L β A (c, g) s hsc M' hM'
  have hsub : ∀ x ∈ M, x ∈ M' := fun x hx => (hM' x).2 (hg x hx)
  intro x
  constructor
  · intro hx
    exact hg x hx
  · intro hx
    have hx' : x ∈ M' := (hM' x).2 hx
    rw [hP x]
    intro u hu
    exact (hP' x).1 hx' u (hsub u hu)
