import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsApprox
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPointStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLineStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOneStatement

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.NormSum.Expand

variable {D : D7}

theorem levC_nat (n : ℕ) : Formalism.UG.P.levelafC (F := ℚ) D.host.E (n : 𝓞 ℚ) = (n : AE D) := by
  rw [← Formalism.UG.P.adelstab_incl_C, map_natCast, map_natCast]

theorem levC_int (n : ℤ) : Formalism.UG.P.levelafC (F := ℚ) D.host.E (n : 𝓞 ℚ) = (n : AE D) := by
  rw [← Formalism.UG.P.adelstab_incl_C, map_intCast, map_intCast]

theorem denom (x : AE D) : ∃ n : ℕ, 0 < n ∧ (n : AE D) * x ∈ OhE D := by
  obtain ⟨d, hd, h⟩ := Formalism.UG.P.levelaf_denom (F := ℚ) (E := D.host.E) x
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, d = (m : 𝓞 ℚ) := by
    refine ⟨Rat.ringOfIntegersEquiv d, ?_⟩
    apply Rat.ringOfIntegersEquiv.injective
    simp
  rw [levC_int] at h
  have hm : m ≠ 0 := by rintro rfl; simp at hd
  refine ⟨m.natAbs * m.natAbs, by positivity, ?_⟩
  have : ((m.natAbs * m.natAbs : ℕ) : AE D) = (m : AE D) * (m : AE D) := by
    rw [← Int.cast_natCast, Int.natAbs_mul_self, Int.cast_mul]
  rw [this, mul_assoc]
  exact mul_mem (intCast_mem _ m) h

theorem denom_fin {κ : Type} [Fintype κ] (f : κ → AE D) :
    ∃ n : ℕ, 0 < n ∧ ∀ k, (n : AE D) * f k ∈ OhE D := by
  choose n hn h using fun k => denom (f k)
  refine ⟨∏ k, n k, Finset.prod_pos fun k _ => hn k, fun k => ?_⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k), Nat.cast_mul, mul_right_comm]
  exact mul_mem (h k) (natCast_mem _ _)

theorem approx (x : AE D) (M : ℕ) (hM : 0 < M) :
    ∃ e : D.host.E, ∃ w ∈ OhE D, inc D e - x = (M : AE D) * w := by
  obtain ⟨n, hn, h⟩ := denom x
  obtain ⟨y, -, w, hw, e⟩ := Formalism.UG.P.csSpan_approx (F := ℚ) (E := D.host.E) Formalism.UG.P.integral_adele_approximation_holds
    ((n * M : ℕ) : 𝓞 ℚ) (Nat.cast_ne_zero.2 (by positivity)) h
  rw [levC_nat] at e
  refine ⟨y / n, -w, neg_mem hw, ?_⟩
  have hn0 : (n : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hu : IsUnit (n : AE D) := by
    have := (IsUnit.mk0 _ hn0).map (inc D)
    rwa [map_natCast] at this
  apply hu.mul_left_cancel
  have h1 : (n : AE D) * inc D (y / n) = inc D y := by
    rw [← map_natCast (inc D), ← map_mul, mul_div_cancel₀ _ hn0]
  rw [mul_sub, h1, e]
  change inc D y - (inc D y + _) = _
  push_cast
  ring

theorem inc_int (b : 𝓞 D.host.E) : inc D (algebraMap (𝓞 D.host.E) D.host.E b) ∈ OhE D :=
  Formalism.UG.CS.incl_int (F := ℚ) b

theorem homL_std {N N' : ℕ} {A : Matrix (Fin N') (Fin N) D.host.E}
    (hA : A ∈ homL D (stdL D N) (stdL D N')) : ∀ i j, inc D (A i j) ∈ OhE D := by
  refine Submodule.span_induction (p := fun A _ => ∀ i j, inc D (A i j) ∈ OhE D) ?_ ?_ ?_ ?_ hA
  · intro A hA i j
    have h1 : (Pi.single j 1 : Fin N → D.host.E) ∈ stdL D N := by
      intro k _
      by_cases h : k = j
      · subst h; simp only [Pi.single_eq_same]; exact Submodule.one_le.1 le_rfl
      · rw [Pi.single_eq_of_ne h]; exact zero_mem _
    have h2 := hA _ h1 i (Set.mem_univ i)
    rw [Matrix.mulVec_single_one] at h2
    obtain ⟨b, hb⟩ := Submodule.mem_one.1 h2
    have : A i j = algebraMap _ _ b := hb.symm
    rw [this]; exact inc_int b
  · intro i j; simp only [Matrix.zero_apply, map_zero]; exact zero_mem _
  · intro A B _ _ hA hB i j
    rw [Matrix.add_apply, map_add]; exact add_mem (hA i j) (hB i j)
  · intro r A _ hA i j
    rw [Matrix.smul_apply, Algebra.smul_def, map_mul]; exact mul_mem (inc_int r) (hA i j)

def dif {N N' : ℕ} (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D))
    (z z' : Matrix (Fin N') (Fin N) D.host.E) : Matrix (Fin N') (Fin N) (AE D) :=
  z'.map (inc D) - (g' : Matrix (Fin N') (Fin N') (AE D)) * z.map (inc D) *
      ((g⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))

theorem dif_add {N N' : ℕ} (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D))
    (z z' w w' : Matrix (Fin N') (Fin N) D.host.E) :
    dif g g' (z + w) (z' + w') = dif g g' z z' + dif g g' w w' := by
  simp only [dif, Matrix.map_add _ (map_add (inc D)), Matrix.mul_add, Matrix.add_mul]
  abel

theorem dif_smul {N N' : ℕ} (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D)) (a : D.host.E)
    (z z' : Matrix (Fin N') (Fin N) D.host.E) :
    dif g g' (a • z) (a • z') = inc D a • dif g g' z z' := by
  have h : ∀ z : Matrix (Fin N') (Fin N) D.host.E, (a • z).map (inc D) = inc D a • z.map (inc D) := by
    intro z; ext i j; simp
  simp only [dif, h, Matrix.mul_smul, Matrix.smul_mul, smul_sub]

theorem conj_int {R : Type} [CommRing R] (O : Subring R) {N N' : ℕ} (g : GL (Fin N) R) (g' : GL (Fin N') R)
    (S A w : Matrix (Fin N') (Fin N) R) (M n n' : ℕ)
    (h : ∀ i j, (n : R) * (g : Matrix (Fin N) (Fin N) R) i j ∈ O)
    (h' : ∀ i j, (n' : R) * ((g'⁻¹ : GL (Fin N') R) : Matrix (Fin N') (Fin N') R) i j ∈ O)
    (hS : ∀ i j, S i j ∈ O) (hw : ∀ i j, w i j ∈ O)
    (he : ∀ i j, A i j - ((g' : Matrix (Fin N') (Fin N') R) * S *
      ((g⁻¹ : GL (Fin N) R) : Matrix (Fin N) (Fin N) R)) i j = ((M * (n' * n) : ℕ) : R) * w i j)
    (x : Fin N → R) (hx : ∀ i, ((g⁻¹ : GL (Fin N) R) : Matrix (Fin N) (Fin N) R).mulVec x i ∈ O) :
    ∀ i, ((g'⁻¹ : GL (Fin N') R) : Matrix (Fin N') (Fin N') R).mulVec (A.mulVec x) i ∈ O := by
  set u := ((g⁻¹ : GL (Fin N) R) : Matrix (Fin N) (Fin N) R).mulVec x with hu
  have hxu : x = (g : Matrix (Fin N) (Fin N) R).mulVec u := by
    rw [hu, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have h2 : A = (g' : Matrix (Fin N') (Fin N') R) * S *
    ((g⁻¹ : GL (Fin N) R) : Matrix (Fin N) (Fin N) R) + ((M * (n' * n) : ℕ) : R) • w := by
    ext i j
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, ← he]
    ring
  have h3 : ((g'⁻¹ : GL (Fin N') R) : Matrix (Fin N') (Fin N') R) * A *
      (g : Matrix (Fin N) (Fin N) R) = S + (M : R) •
        (((n' : R) • ((g'⁻¹ : GL (Fin N') R) : Matrix (Fin N') (Fin N') R)) * w *
          ((n : R) • (g : Matrix (Fin N) (Fin N) R))) := by
    rw [h2, Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_assoc _ _ (g : Matrix (Fin N) (Fin N) R),
      ← Units.val_mul, ← Units.val_mul, inv_mul_cancel, inv_mul_cancel, Units.val_one, Units.val_one,
      Matrix.one_mul, Matrix.mul_one]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    congr 2
    push_cast; ring
  rw [hxu, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h3]
  intro i
  rw [Matrix.mulVec, dotProduct]
  refine sum_mem fun j _ => mul_mem ?_ (hx j)
  rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  refine add_mem (hS i j) (mul_mem (natCast_mem _ _) ?_)
  rw [Matrix.mul_apply]
  refine sum_mem fun k _ => mul_mem ?_ (h k j)
  rw [Matrix.mul_apply]
  exact sum_mem fun l _ => mul_mem (h' i l) (hw l k)

theorem approx_hom {N N' : ℕ} (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D)) {L L'}
    (hL : Moves D g L) (hL' : Moves D g' L') (A : Matrix (Fin N') (Fin N) D.host.E)
    (hA : ∀ i j, inc D (A i j) ∈ OhE D) (M : ℕ) (hM : 0 < M) :
    ∃ A' ∈ homL D L L', ∀ i j, ∃ w ∈ OhE D, dif g g' A A' i j = (M : AE D) * w := by
  obtain ⟨n, hn, h⟩ := denom_fin (fun k : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) (AE D)) k.1 k.2)
  obtain ⟨n', hn', h'⟩ := denom_fin (fun k : Fin N' × Fin N' =>
    ((g'⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) k.1 k.2)
  choose e w hw he using fun (i : Fin N') (j : Fin N) => approx (((g' : Matrix (Fin N') (Fin N') (AE D)) * A.map (inc D) *
      ((g⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))) i j) (M * (n' * n)) (by positivity)
  refine ⟨Matrix.of e, Submodule.subset_span ?_, fun i j => ⟨((n' * n : ℕ) : AE D) * w i j,
    mul_mem (natCast_mem _ _) (hw i j), ?_⟩⟩
  · intro x hx
    have hx' := (hL x).1 hx
    rw [hL']
    have h1 : (fun j => inc D ((Matrix.of e).mulVec x j)) =
        ((Matrix.of e).map (inc D)).mulVec (fun j => inc D (x j)) := by
      funext i
      exact RingHom.map_mulVec (inc D) (Matrix.of e) x i
    rw [h1]
    exact conj_int (OhE D) g g' (A.map (inc D)) _ (Matrix.of w) M n n' (fun i j => h (i, j))
      (fun i j => h' (i, j)) hA hw he _ hx'
  · have := he i j
    rw [dif, Matrix.sub_apply, Matrix.map_apply, Matrix.of_apply, this, Nat.cast_mul, mul_assoc]

theorem IhE_mul {cc : Ideal (𝓞 D.host.K)} {s y : AE D} (hs : s ∈ OhE D) (hy : y ∈ IhE D cc) :
    s * y ∈ IhE D cc := by
  refine AddSubgroup.closure_induction (p := fun y _ => s * y ∈ IhE D cc) ?_ ?_ ?_ ?_ hy
  · rintro y ⟨c, hc, a, ha, t, ht, rfl⟩
    exact AddSubgroup.subset_closure ⟨c, hc, a, ha, s * t, mul_mem hs ht, by ring⟩
  · rw [mul_zero]; exact zero_mem _
  · intro a b _ _ ha hb; rw [mul_add]; exact add_mem ha hb
  · intro a _ ha; rw [mul_neg]; exact neg_mem ha

theorem closeTo_iff {cc : Ideal (𝓞 D.host.K)} {N N' m : ℕ} {g : GL (Fin N) (AE D)} {g' : GL (Fin N') (AE D)}
    {z z' : Matrix (Fin N') (Fin N) D.host.E} :
    CloseTo D cc m g g' z z' ↔ ∀ i j, ∃ y ∈ IhE D cc, dif g g' z z' i j = (m : AE D) * y := Iff.rfl

theorem closeTo_add {cc : Ideal (𝓞 D.host.K)} {N N' m : ℕ} {g : GL (Fin N) (AE D)} {g' : GL (Fin N') (AE D)}
    {z z' w w' : Matrix (Fin N') (Fin N) D.host.E} (h : CloseTo D cc m g g' z z') (h' : CloseTo D cc m g g' w w') :
    CloseTo D cc m g g' (z + w) (z' + w') := by
  rw [closeTo_iff] at *
  intro i j
  obtain ⟨y, hy, e⟩ := h i j
  obtain ⟨y', hy', e'⟩ := h' i j
  exact ⟨y + y', add_mem hy hy', by rw [dif_add, Matrix.add_apply, e, e', mul_add]⟩

theorem closeTo_smul {cc : Ideal (𝓞 D.host.K)} {N N' m : ℕ} {g : GL (Fin N) (AE D)} {g' : GL (Fin N') (AE D)}
    {z z' : Matrix (Fin N') (Fin N) D.host.E} (h : CloseTo D cc m g g' z z') (a : D.host.E)
    (ha : inc D a ∈ OhE D) : CloseTo D cc m g g' (a • z) (a • z') := by
  rw [closeTo_iff] at *
  intro i j
  obtain ⟨y, hy, e⟩ := h i j
  exact ⟨inc D a * y, IhE_mul ha hy, by rw [dif_smul, Matrix.smul_apply, e, smul_eq_mul]; ring⟩

theorem closeTo_zero {cc : Ideal (𝓞 D.host.K)} {N N' m : ℕ} {g : GL (Fin N) (AE D)} {g' : GL (Fin N') (AE D)} :
    CloseTo D cc m g g' 0 0 := by
  rw [closeTo_iff]
  intro i j
  exact ⟨0, zero_mem _, by simp [dif]⟩

theorem closeTo_div {cc : Ideal (𝓞 D.host.K)} {N N' m Q : ℕ} (hQ : 0 < Q) {g : GL (Fin N) (AE D)}
    {g' : GL (Fin N') (AE D)}
    {z z' : Matrix (Fin N') (Fin N) D.host.E} (h : CloseTo D cc (m * Q) g g' z z') :
    CloseTo D cc m g g' ((Q : D.host.E)⁻¹ • z) ((Q : D.host.E)⁻¹ • z') := by
  rw [closeTo_iff] at *
  intro i j
  obtain ⟨y, hy, e⟩ := h i j
  refine ⟨y, hy, ?_⟩
  have hQ0 : (Q : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hQ.ne'
  have h1 : inc D (Q : D.host.E)⁻¹ * (Q : AE D) = 1 := by
    rw [← map_natCast (inc D), ← map_mul, inv_mul_cancel₀ hQ0, map_one]
  rw [dif_smul, Matrix.smul_apply, e, smul_eq_mul, Nat.cast_mul]
  linear_combination (m * y) * h1

theorem approx_YY {cc : Ideal (𝓞 D.host.K)} {N N' : ℕ} (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D)) {L L'}
    (hL : Moves D g L) (hL' : Moves D g' L') (M : ℕ) (hM : 0 < M) {B : Matrix (Fin N') (Fin N) D.host.E}
    (hB : B ∈ YYl D (stdL D N) (stdL D N')) :
    ∃ B' ∈ YYl D L L', ∀ c ∈ cc, CloseTo D cc M g g' ((((c : D.host.K) : D.host.E)) • B)
      ((((c : D.host.K) : D.host.E)) • B') := by
  refine Submodule.span_induction (p := fun B _ => ∃ B' ∈ YYl D L L', ∀ c ∈ cc,
    CloseTo D cc M g g' ((((c : D.host.K) : D.host.E)) • B) ((((c : D.host.K) : D.host.E)) • B')) ?_ ?_ ?_ ?_ hB
  · rintro B ⟨a, ha, A, hA, rfl⟩
    obtain ⟨A', hA', h⟩ := approx_hom g g' hL hL' A (homL_std hA) M hM
    refine ⟨a • A', Submodule.subset_span ⟨a, ha, A', hA', rfl⟩, fun c hc => ?_⟩
    rw [closeTo_iff]
    intro i j
    obtain ⟨w, hw, e⟩ := h i j
    refine ⟨_, AddSubgroup.subset_closure ⟨c, hc, a, ha, w, hw, rfl⟩, ?_⟩
    rw [smul_smul, smul_smul, dif_smul, Matrix.smul_apply, e, smul_eq_mul]
    ring
  · exact ⟨0, zero_mem _, fun c _ => by rw [smul_zero]; exact closeTo_zero⟩
  · rintro A B _ _ ⟨A', hA', hA⟩ ⟨B', hB', hB⟩
    exact ⟨A' + B', add_mem hA' hB', fun c hc => by
      rw [smul_add, smul_add]; exact closeTo_add (hA c hc) (hB c hc)⟩
  · rintro r A _ ⟨A', hA', hA⟩
    refine ⟨r • A', Submodule.smul_mem _ r hA', fun c hc => ?_⟩
    have := closeTo_smul (hA c hc) _ (inc_int r)
    rw [smul_comm _ r A, smul_comm _ r A', ← algebraMap_smul D.host.E r, ← algebraMap_smul D.host.E r]
    exact this

theorem lamOf_mem {cc : Ideal (𝓞 D.host.K)} {δ w : ℂ} (hw : w ∈ lamOf D cc δ) :
    ∃ c ∈ cc, w = δ * D.host.φ₀ (((c : D.host.K) : D.host.E)) := by
  refine AddSubgroup.closure_induction
    (p := fun w _ => ∃ c ∈ cc, w = δ * D.host.φ₀ (((c : D.host.K) : D.host.E))) ?_ ?_ ?_ ?_ hw
  · exact fun w h => h
  · exact ⟨0, zero_mem _, by simp⟩
  · rintro _ _ _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, add_mem ha hb, by simp [mul_add]⟩
  · rintro _ _ ⟨a, ha, rfl⟩
    exact ⟨-a, neg_mem ha, by simp⟩

theorem pt_add {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ} (z w : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (z + w) = pt D (tor0 D cc δ) δ z + pt D (tor0 D cc δ) δ w := by
  ext τ i j; simp [pt, embV, tor0, mul_add]

theorem pt_neg {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ} (z : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ ((-1 : D.host.E) • z) = -pt D (tor0 D cc δ) δ z := by
  ext τ i j; simp [pt, embV, tor0]

theorem pt_div {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ} (Q : ℕ) (z : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ ((Q : D.host.E)⁻¹ • z) = (Q : ℂ)⁻¹ • pt D (tor0 D cc δ) δ z := by
  ext τ i j; simp [pt, embV, tor0]; ring

theorem pt_K (hψ : GL3Theta.InducedCMType D) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ} (c : D.host.K)
    (z : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ ((c : D.host.E) • z) = (δ * D.host.φ₀ (c : D.host.E)) • embV D (tor0 D cc δ) z := by
  ext τ i j
  simp only [pt, embV, tor0, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hψ τ c]
  ring

theorem approx_La (hψ : GL3Theta.InducedCMType D) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}
    (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D)) {L L'}
    (hL : Moves D g L) (hL' : Moves D g' L') {x : VC D N N'} (hx : x ∈ La0 D (tor0 D cc δ) N N') :
    ∃ B, x = pt D (tor0 D cc δ) δ B ∧ ∀ M : ℕ, 0 < M →
      ∃ B', pt D (tor0 D cc δ) δ B' ∈ La D (tor0 D cc δ) L L' ∧ CloseTo D cc M g g' B B' := by
  refine AddSubgroup.closure_induction (p := fun x _ => ∃ B, x = pt D (tor0 D cc δ) δ B ∧ ∀ M : ℕ, 0 < M →
      ∃ B', pt D (tor0 D cc δ) δ B' ∈ La D (tor0 D cc δ) L L' ∧ CloseTo D cc M g g' B B') ?_ ?_ ?_ ?_ hx
  · rintro x ⟨w, hw, A, hA, rfl⟩
    obtain ⟨c, hc, rfl⟩ := lamOf_mem hw
    refine ⟨_, (pt_K hψ c A).symm, fun M hM => ?_⟩
    obtain ⟨B', hB', h⟩ := approx_YY (cc := cc) g g' hL hL' M hM hA
    refine ⟨_, ?_, h c hc⟩
    rw [pt_K hψ]
    exact AddSubgroup.subset_closure ⟨_, hw, B', hB', rfl⟩
  · have h0 : pt D (tor0 D cc δ) δ (0 : Matrix (Fin N') (Fin N) D.host.E) = 0 := by
      ext τ i j; simp [pt, embV, tor0]
    exact ⟨0, h0.symm, fun M _ => ⟨0, by rw [h0]; exact zero_mem _, closeTo_zero⟩⟩
  · rintro _ _ _ _ ⟨A, rfl, hA⟩ ⟨B, rfl, hB⟩
    refine ⟨A + B, (pt_add A B).symm, fun M hM => ?_⟩
    obtain ⟨A', h1, h2⟩ := hA M hM
    obtain ⟨B', h3, h4⟩ := hB M hM
    exact ⟨A' + B', by rw [pt_add]; exact add_mem h1 h3, closeTo_add h2 h4⟩
  · rintro _ _ ⟨A, rfl, hA⟩
    refine ⟨_, (pt_neg A).symm, fun M hM => ?_⟩
    obtain ⟨A', h1, h2⟩ := hA M hM
    exact ⟨_, by rw [pt_neg]; exact neg_mem h1,
      closeTo_smul h2 (-1) (by rw [map_neg, map_one]; exact neg_mem (one_mem _))⟩

section Theta

variable {T : Tor D} {N N' : ℕ}

theorem Hf_add_left (x y w : VC D N N') : Hf D T (x + y) w = Hf D T x w + Hf D T y w := by
  simp only [Hf, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div]

theorem Hf_smul_left (c : ℂ) (x w : VC D N N') : Hf D T (c • x) w = c * Hf D T x w := by
  simp only [Hf, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, mul_div_assoc]

theorem Hf_conj (x w : VC D N N') : Hf D T w x = (starRingEnd ℂ) (Hf D T x w) := by
  simp only [Hf, map_div₀, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal, mul_comm]

theorem Hf_nsmul_left (n : ℕ) (x w : VC D N N') : Hf D T (n • x) w = n * Hf D T x w := by
  rw [← Nat.cast_smul_eq_nsmul ℂ, Hf_smul_left]

theorem Hf_nsmul_right (n : ℕ) (x w : VC D N N') : Hf D T x (n • w) = n * Hf D T x w := by
  rw [Hf_conj, Hf_nsmul_left, map_mul, ← Hf_conj, map_natCast]

theorem qH_nsmul (n : ℕ) (x : VC D N N') : qH D T (n • x) = n ^ 2 * qH D T x := by
  rw [qH, qH, Hf_nsmul_left, Hf_nsmul_right, ← mul_assoc, ← Nat.cast_mul, ← Complex.ofReal_natCast,
    Complex.re_ofReal_mul]
  push_cast; ring

theorem Hf_diff (x : VC D N N') : Differentiable ℂ (fun z : VC D N N' => Hf D T z x) := by
  unfold Hf
  fun_prop

theorem Wd_diff (x : VC D N N') {F : VC D N N' → ℂ} (hF : Differentiable ℂ F) :
    Differentiable ℂ (Wd D T x F) := by
  have h := Hf_diff (T := T) x
  unfold Wd U
  fun_prop

theorem Wd_comm (a x : VC D N N') (m : ℤ) (h : (Hf D T a x).im = m) (F : VC D N N' → ℂ) :
    Wd D T a (Wd D T x F) = Wd D T x (Wd D T a F) := by
  funext z
  have h1 : Hf D T x a = Hf D T a x - 2 * m * Complex.I := by
    rw [Hf_conj a x]
    apply Complex.ext <;> simp [h]
    ring
  have h2 : Complex.exp (-(Real.pi : ℂ) * Hf D T (z + x) a - (Real.pi : ℂ) * Hf D T a a / 2) *
      Complex.exp (-(Real.pi : ℂ) * Hf D T z x - (Real.pi : ℂ) * Hf D T x x / 2) =
      Complex.exp (-(Real.pi : ℂ) * Hf D T (z + a) x - (Real.pi : ℂ) * Hf D T x x / 2) *
      Complex.exp (-(Real.pi : ℂ) * Hf D T z a - (Real.pi : ℂ) * Hf D T a a / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
    refine ⟨m, ?_⟩
    rw [Hf_add_left, Hf_add_left, h1]
    ring
  simp only [Wd, U]
  rw [add_right_comm z a x]
  linear_combination (-(wdPh D T a * wdPh D T x * F (z + x + a))) * h2

theorem Wd_add (x : VC D N N') (F G : VC D N N' → ℂ) : Wd D T x (F + G) = Wd D T x F + Wd D T x G := by
  funext z; simp only [Wd, U, Pi.add_apply]; ring

theorem Wd_smul (x : VC D N N') (c : ℂ) (F : VC D N N' → ℂ) : Wd D T x (c • F) = c • Wd D T x F := by
  funext z; simp only [Wd, U, Pi.smul_apply, smul_eq_mul]; ring

theorem TT_add {F G : VC D N N' → ℂ} (hF : F ∈ TT D T N N') (hG : G ∈ TT D T N N') : F + G ∈ TT D T N N' := by
  obtain ⟨d, m, hm, h⟩ := hF
  obtain ⟨d', m', hm', h'⟩ := hG
  refine ⟨d.add d', m * m', by positivity, fun x hx => ?_⟩
  rw [Wd_add]
  congr 1
  · rw [mul_nsmul']; exact h _ (nsmul_mem hx _)
  · rw [mul_nsmul]; exact h' _ (nsmul_mem hx _)

theorem TT_smul (c : ℂ) {F : VC D N N' → ℂ} (hF : F ∈ TT D T N N') : c • F ∈ TT D T N N' := by
  obtain ⟨d, m, hm, h⟩ := hF
  exact ⟨d.const_smul c, m, hm, fun x hx => by rw [Wd_smul, h x hx]⟩

theorem TT_zero : (0 : VC D N N' → ℂ) ∈ TT D T N N' :=
  ⟨differentiable_const 0, 1, one_pos, fun x _ => by funext z; simp [Wd, U]⟩

end Theta

theorem Om_sum {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ} {e0 : VC D N N' → ℂ} (W : WeilO D cc δ N N' e0)
    (g : GA D N) (g' : GA D N') {κ : Type} (s : Finset κ) (r : κ → ℂ) (F : κ → VC D N N' → ℂ)
    (hF : ∀ i, F i ∈ TT D (tor0 D cc δ) N N') :
    (∑ i ∈ s, r i • F i) ∈ TT D (tor0 D cc δ) N N' ∧
      W.Om g g' (∑ i ∈ s, r i • F i) = ∑ i ∈ s, r i • W.Om g g' (F i) := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using TT_zero, ?_⟩
    have := W.smul g g' 0 0 TT_zero
    simpa using this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine ⟨TT_add (TT_smul _ (hF a)) ih.1, ?_⟩
    rw [W.add g g' _ (TT_smul _ (hF a)) _ ih.1, W.smul g g' _ _ (hF a), ih.2]

theorem root_unity {ζ : ℂ} {n : ℕ} (hn : 0 < n) (h : ζ ^ n = 1) :
    ∃ u : Qbar, (u : ℂ) = ζ ∧ IsIntegral ℤ u ∧ ∀ ρ : Qbar →+* ℂ, ‖ρ u‖ = 1 := by
  have hi : IsIntegral ℤ ζ := IsIntegral.of_pow hn (by rw [h]; exact isIntegral_one)
  have hq : ζ ∈ Qbar := mem_algebraicClosure_iff'.2 hi.tower_top
  have hu : (⟨ζ, hq⟩ : Qbar) ^ n = 1 := Subtype.ext (by simpa using h)
  refine ⟨⟨ζ, hq⟩, rfl, IsIntegral.of_pow hn (by rw [hu]; exact isIntegral_one), fun ρ => ?_⟩
  have : ‖ρ ⟨ζ, hq⟩‖ ^ n = 1 := by rw [← norm_pow, ← map_pow, hu, map_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this

theorem wdPh_pow {T : Tor D} {N N' Q : ℕ} (x : VC D N N') (m : ℤ) (h : qH D T (Q • x) = m) :
    wdPh D T x ^ (2 * Q ^ 2) = 1 := by
  rw [qH_nsmul] at h
  rw [wdPh, ee, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
  refine ⟨m, ?_⟩
  have h' : (Q : ℂ) ^ 2 * (qH D T x : ℂ) = m := by exact_mod_cast h
  rw [← h']
  push_cast; ring

theorem om_expand : ∀ (D : D7), Inp D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ) (Q : ℕ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (P : Pair D cc δ t0 Q), ∀ (g : GA D P.a) (g' : GA D P.d) L₁ L₁', Moves D (g : GL (Fin P.a) (AE D)) L₁ → Moves D (g' : GL (Fin P.d) (AE D)) L₁' → ∃ (c : ℂ) (k : ℕ) (r : Fin k → Qbar) (y : Fin k → VC D P.a P.d), 0 < Q → (Mod1All c ∧ (∀ i, Q • y i ∈ La D (tor0 D cc δ) L₁ L₁') ∧ (∀ i, IsIntegral ℤ ((Q : Qbar) ^ (P.a * P.d) * r i)) ∧ (∀ ρ : Qbar →+* ℂ, (∑ i, ‖ρ (r i)‖) ^ 2 ≤ (Q : ℝ) ^ (P.a * P.d)) ∧ (P.W.Om g g' P.F = fun z => c * ∑ i, (r i : ℂ) * U D (tor0 D cc δ) (y i) (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) P.a P.d) (La D (tor0 D cc δ) L₁ L₁') P.e0) z) ∧ ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (k' : GA D P.d), k' ∈ intG D P.d → TrivAt D p (g : GL (Fin P.a) (AE D)) → TrivAt D p ((g' * k' : GA D P.d) : GL (Fin P.d) (AE D)) → ‖lamC lam c‖ = 1) := by
  intro D hI cc δ t0 Q hC _ P g g' L₁ L₁' hL hL'
  rcases Nat.eq_zero_or_pos Q with hQ | hQ
  · exact ⟨0, 0, Fin.elim0, Fin.elim0, fun h => absurd h (by omega)⟩
  have hSD : ∀ (N : ℕ) (g : GA D N) L, Moves D (g : GL (Fin N) (AE D)) L → SD D L := by
    intro N g L hL
    obtain ⟨Lt, h1, -⟩ := GlobalTheory.T.Lt_eq_iff_inv_mul_mem_intG_and_transport D N
    have : L = Lt g := by
      ext x; rw [hL x, (h1 g).1 x]
    rw [this]; exact (h1 g).2
  have hSD0 : ∀ N : ℕ, SD D (stdL D N) := by
    intro N
    obtain ⟨Lt, h1, h2, -⟩ := GlobalTheory.T.Lt_eq_iff_inv_mul_mem_intG_and_transport D N
    rw [← h2]; exact (h1 1).2
  obtain ⟨-, hW, hint, -⟩ := GlobalTheory.T.theta_space_selfDual_pair_at_most_line D hI.g1 cc δ hC P.a P.d (La0 D (tor0 D cc δ) P.a P.d)
    (Or.inr ⟨_, _, hSD0 _, hSD0 _, rfl⟩)
  obtain ⟨-, -, -, -, -, -, hq⟩ := GlobalTheory.T.theta_space_selfDual_pair_at_most_line D hI.g1 cc δ hC P.a P.d (La D (tor0 D cc δ) L₁ L₁')
    (Or.inr ⟨_, _, hSD _ g _ hL, hSD _ g' _ hL', rfl⟩)
  have he0 : P.e0 ∈ Th D (tor0 D cc δ) (stdL D P.a) (stdL D P.d) := P.vac.1
  have hfix : ∀ x ∈ La0 D (tor0 D cc δ) P.a P.d, Wd D (tor0 D cc δ) x P.e0 = P.e0 := by
    intro x hx
    rw [hW x hx]; funext z; exact he0.2 x hx z
  have heT : P.e0 ∈ TT D (tor0 D cc δ) P.a P.d :=
    ⟨he0.1, 1, one_pos, fun x hx => by rw [one_nsmul]; exact hfix x hx⟩
  obtain ⟨c, hc1, hc2, hc3⟩ := GlobalTheory.T.vacuum_under_adelic_pair_modulus_one D hI cc δ hC P.a P.d (P.d_even.mul_left _) P.e0 he0 P.W g g'
    L₁ L₁' hL hL'
  obtain ⟨k, r, z, hz, hr1, hr2, hF⟩ := P.pres
  have hT : ∀ i, Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) P.e0 ∈ TT D (tor0 D cc δ) P.a P.d := by
    intro i
    refine ⟨Wd_diff _ he0.1, Q, hQ, fun x hx => ?_⟩
    obtain ⟨m, hm⟩ := hint x hx _ (hz i)
    rw [Hf_nsmul_right, ← Hf_nsmul_left] at hm
    rw [Wd_comm _ _ m hm, hfix _ (nsmul_mem hx _)]
  have hQc : (Q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hQ.ne'
  have key : ∀ i, ∃ y : VC D P.a P.d, Q • y ∈ La D (tor0 D cc δ) L₁ L₁' ∧
      P.W.Om g g' (Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) P.e0) =
        Wd D (tor0 D cc δ) y (P.W.Om g g' P.e0) := by
    intro i
    obtain ⟨B, hB, h⟩ := approx_La hI.g1.1 _ _ hL hL' (hz i)
    obtain ⟨m, hm, hl⟩ := P.W.lift g g' ((Q : D.host.E)⁻¹ • B) P.e0 heT
    obtain ⟨B', h1, h2⟩ := h (m * Q) (by positivity)
    refine ⟨pt D (tor0 D cc δ) δ ((Q : D.host.E)⁻¹ • B'), ?_, ?_⟩
    · rw [pt_div, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hQc, one_smul]; exact h1
    · rw [← hl _ (closeTo_div hQ h2), pt_div, ← hB, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
        inv_mul_cancel₀ hQc, one_smul]
  choose y hy1 hy2 using key
  have hu : ∀ i, ∃ u : Qbar, (u : ℂ) = wdPh D (tor0 D cc δ) (y i) ∧ IsIntegral ℤ u ∧
      ∀ ρ : Qbar →+* ℂ, ‖ρ u‖ = 1 := by
    intro i
    obtain ⟨m, hm⟩ := hq _ (hy1 i)
    exact root_unity (by positivity) (wdPh_pow _ m hm)
  choose u hu1 hu2 hu3 using hu
  refine ⟨c, k, fun i => r i * u i, y, fun _ => ⟨hc1, hy1, fun i => ?_, fun ρ => ?_, ?_, hc3⟩⟩
  · rw [← mul_assoc]; exact (hr1 i).mul (hu2 i)
  · simpa only [map_mul, norm_mul, hu3, mul_one] using hr2 ρ
  · have hF' : P.F = ∑ i, (r i : ℂ) • Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) P.e0 := by
      rw [hF]; funext w; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hF', (Om_sum P.W g g' Finset.univ _ _ hT).2]
    funext w
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hy2, hc2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [IntermediateField.coe_mul, hu1]
    simp only [Wd, U]
    ring

end GlobalTheory.NormSum.Expand
