import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
noncomputable section
namespace GlobalTheory.ArchRec.JointTransfer

theorem phi_apply {p q n : ℕ} (br : Bool) (e : Ix p q ≃ Fin n) (Y : Mat p q) (i j : Ix p q) :
    phi br e Y (e i) (e j) = cjc br (Y i j) := by
  cases br <;> simp [phi, plainMat, barMat, cjc]

theorem cjc_eq_zero (br : Bool) (z : ℂ) : cjc br z = 0 ↔ z = 0 := by
  cases br <;> simp [cjc]

theorem isPC_iff {p q : ℕ} (Y : Mat p q) : IsPC Y ↔ ∀ i j : Ix p q, i.isLeft = j.isLeft → Y i j = 0 := by
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rcases i with i | i <;> rcases j with j | j <;> simp [sameBlock]

theorem trace_eq_zero_of_isPC {p q : ℕ} {Y : Mat p q} (h : IsPC Y) : Y.trace = 0 := by
  rw [isPC_iff] at h
  simp [Matrix.trace, h _ _ rfl]

theorem anticomm_iff {p q n : ℕ} {ε : Fin n → Bool} {e : Ix p q ≃ Fin n} (he : SignCompat ε e) (br : Bool)
    (Y : Mat p q) : Formalism.REAL.Jm ε * phi br e Y = -(phi br e Y * Formalism.REAL.Jm ε) ↔ IsPC Y := by
  rw [isPC_iff, ← Matrix.ext_iff, e.surjective.forall]
  refine forall_congr' fun i => ?_
  rw [e.surjective.forall]
  refine forall_congr' fun j => ?_
  simp only [Formalism.REAL.Jm, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.neg_apply, phi_apply, he i, he j]
  rw [← cjc_eq_zero br]
  generalize cjc br (Y i j) = z
  cases i.isLeft <;> cases j.isLeft <;> simp [neg_eq_iff_add_eq_zero, eq_neg_iff_add_eq_zero]

theorem conj_anticomm_iff {n : ℕ} {fr : Mn n} (h : IsUnit fr) (J X : Mn n) :
    fr⁻¹ * J * fr * (fr⁻¹ * X * fr) = -(fr⁻¹ * X * fr * (fr⁻¹ * J * fr)) ↔ J * X = -(X * J) := by
  have hd : IsUnit fr.det := (Matrix.isUnit_iff_isUnit_det _).1 h
  have h1 : ∀ A B : Mn n, fr⁻¹ * A * fr * (fr⁻¹ * B * fr) = fr⁻¹ * (A * B) * fr := fun A B => by
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd]
  rw [h1, h1]
  constructor
  · intro h2
    have h3 := congrArg (fun Y => fr * Y * fr⁻¹) h2
    simpa only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd,
      Matrix.mul_nonsing_inv _ hd, Matrix.mul_one] using h3
  · intro h2
    rw [h2, Matrix.mul_neg, Matrix.neg_mul]

theorem posC_iff {p q : ℕ} {lam : Ix p q → ℚ} (h : IsParam lam) (i j : Ix p q) :
    posC i j ↔ i.isLeft = j.isLeft ∧ lam j < lam i := by
  constructor
  · intro hp
    refine ⟨?_, h.2.1 i j hp⟩
    rcases i with i | i <;> rcases j with j | j <;> simp_all [posC]
  · rintro ⟨hs, hl⟩
    by_contra hn
    have hne : i ≠ j := by rintro rfl; exact lt_irrefl _ hl
    have : posC j i := by
      rcases i with i | i <;> rcases j with j | j <;> simp_all [posC] <;> omega
    exact lt_asymm hl (h.2.1 j i this)

theorem jm_eq (p q : ℕ) : Formalism.BasicNotions.TH.Jm p q = Matrix.diagonal fun i : Ix p q => if i.isLeft then (1 : ℂ) else -1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Formalism.BasicNotions.TH.Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem jm_comm {p q : ℕ} {i j : Ix p q} (h : i.isLeft = j.isLeft) :
    Formalism.BasicNotions.TH.Jm p q * Eab i j = Eab i j * Formalism.BasicNotions.TH.Jm p q := by
  ext a b
  rw [jm_eq, Matrix.diagonal_mul, Matrix.mul_diagonal, Eab, Matrix.single_apply]
  split_ifs <;> simp_all

theorem eab_conjTranspose {p q : ℕ} (i j : Ix p q) : (Eab i j)ᴴ = Eab j i := by
  simp [Eab]

theorem skew_mem_upq {p q : ℕ} {i j : Ix p q} (h : i.isLeft = j.isLeft) : Eab i j - Eab j i ∈ upq p q := by
  simp only [upq, Set.mem_setOf_eq, Matrix.conjTranspose_sub, eab_conjTranspose, Matrix.mul_sub, Matrix.sub_mul,
    jm_comm h, jm_comm h.symm]
  abel

theorem symm_mem_upq {p q : ℕ} {i j : Ix p q} (h : i.isLeft = j.isLeft) (t : ℝ) :
    ((t : ℂ) * Complex.I) • (Eab i j + Eab j i) ∈ upq p q := by
  simp only [upq, Set.mem_setOf_eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, eab_conjTranspose,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, jm_comm h, jm_comm h.symm]
  have : star ((t : ℂ) * Complex.I) = -((t : ℂ) * Complex.I) := by simp
  rw [this]
  module

def sb (br : Bool) : ℝ := if br then -1 else 1

theorem sb_sq (br : Bool) : sb br * sb br = 1 := by cases br <;> simp [sb]

theorem phi_skew {p q n : ℕ} (br : Bool) (e : Ix p q ≃ Fin n) (i j : Ix p q) :
    phi br e (Eab i j - Eab j i) = Matrix.single (e i) (e j) 1 - Matrix.single (e j) (e i) 1 := by
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  rw [phi_apply]
  cases br <;> simp [cjc, Eab, Matrix.single_apply] <;> split_ifs <;> simp

theorem phi_symm {p q n : ℕ} (br : Bool) (e : Ix p q ≃ Fin n) (i j : Ix p q) :
    phi br e (((sb br : ℂ) * Complex.I) • (Eab i j + Eab j i)) =
      Complex.I • (Matrix.single (e i) (e j) 1 + Matrix.single (e j) (e i) 1) := by
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  rw [phi_apply]
  cases br <;> simp [cjc, sb, Eab, Matrix.single_apply] <;> split_ifs <;> simp

theorem phi_torus {p q n : ℕ} (br : Bool) (e : Ix p q ≃ Fin n) (x : Fin n → ℝ) :
    phi br e (Matrix.diagonal fun j => Complex.exp (((sb br * x (e j) : ℝ) : ℂ) * Complex.I)) =
      Matrix.diagonal fun a => Complex.exp ((x a : ℂ) * Complex.I) := by
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  rw [phi_apply]
  by_cases h : a = b
  · subst h
    cases br <;> simp [cjc, sb, ← Complex.exp_conj]
  · simp [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (e.injective.ne h), cjc]

section One

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {τ : D.what₂.Tau} {ι σ Z : Type}
  {A : Mn V.rank → (Z → ℂ) → (Z → ℂ)} {pt : MvPolynomial ι ℂ → (Z → ℂ)}
  {κ : MvPolynomial ι ℂ ≃ₗ[ℂ] MvPolynomial σ ℂ} {p q : ℕ} {a : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)}
  {c : ℚ} {br : Bool} {e : Ix p q ≃ Fin V.rank}

theorem isHarm_iff (hs : SignCompat (M.ε τ) e) (hl : phiFr (M.fr τ) br e '' upq p q = lieAt V τ)
    (hA : Side A pt κ (phiFr (M.fr τ) br e) c a) (hκ : Graded κ) (d : ℕ) (P : MvPolynomial ι ℂ) :
    IsHarm M τ A pt d P ↔ (κ P).IsHomogeneous d ∧ ∀ Y ∈ pR p q, (a Y (κ P)).IsHomogeneous (d + 2) := by
  refine and_congr (hκ d P).symm ?_
  rw [← hl, Set.forall_mem_image]
  constructor
  · intro h Y hY
    obtain ⟨P', h1, h2⟩ := h hY.1 (by
      rw [cart, phiFr, conj_anticomm_iff (M.fr_unit τ), anticomm_iff hs]; exact hY.2)
    rw [hA.der Y hY.1, trace_eq_zero_of_isPC hY.2, mul_zero, zero_smul, add_zero] at h1
    rw [← h1]
    exact (hκ _ _).2 h2
  · intro h Y hY hc
    rw [cart, phiFr, conj_anticomm_iff (M.fr_unit τ), anticomm_iff hs] at hc
    refine ⟨κ.symm (a Y (κ P)), ?_, ?_⟩
    · rw [hA.der Y hY, trace_eq_zero_of_isPC hc, mul_zero, zero_smul, add_zero, κ.apply_symm_apply]
    · rw [← hκ, κ.apply_symm_apply]
      exact h Y ⟨hY, hc⟩

theorem hasWt_iff (hA : Side A pt κ (phiFr (M.fr τ) br e) c a) {μ : Fin V.rank → ℝ} {Λ : Ix p q → ℚ}
    (hμ : ∀ j, sb br * μ (e j) = ((Λ j + c : ℚ) : ℝ)) (P : MvPolynomial ι ℂ) :
    HasWt M τ A pt μ P ↔ κ P ∈ wtSub a Λ := by
  rw [hA.wt]
  have key : ∀ x : Fin V.rank → ℝ, ∑ j, ((Λ j + c : ℚ) : ℝ) * (sb br * x (e j)) = ∑ b, μ b * x b := fun x => by
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hμ]
    linear_combination (μ (e j) * x (e j)) * sb_sq br
  constructor
  · intro h y
    have h1 := h fun b => sb br * y (e.symm b)
    have h2 : ∀ j, sb br * (sb br * y (e.symm (e j))) = y j := fun j => by
      rw [e.symm_apply_apply, ← mul_assoc, sb_sq, one_mul]
    rw [ofFr, ← phi_torus br e, ← key] at h1
    simp only [h2] at h1
    exact h1
  · intro h x
    have h1 := h fun j => sb br * x (e j)
    rw [phiFr, phi_torus, key] at h1
    exact h1

theorem killedBy_iff (hA : Side A pt κ (phiFr (M.fr τ) br e) c a) {i j : Ix p q} (hij : i ≠ j)
    (h : i.isLeft = j.isLeft) (P : MvPolynomial ι ℂ) :
    KilledBy M τ A pt (e i) (e j) P ↔ a (if br then Eab j i else Eab i j) (κ P) = 0 := by
  have t1 : (Eab i j - Eab j i).trace = 0 := by
    simp [Eab, Matrix.trace_sub, Matrix.trace_single_eq_of_ne _ _ _ hij, Matrix.trace_single_eq_of_ne _ _ _ hij.symm]
  have t2 : (((sb br : ℂ) * Complex.I) • (Eab i j + Eab j i)).trace = 0 := by
    simp [Eab, Matrix.trace_add, Matrix.trace_single_eq_of_ne _ _ _ hij, Matrix.trace_single_eq_of_ne _ _ _ hij.symm]
  have d1 := hA.der _ (skew_mem_upq h) P
  have d2 := hA.der _ (symm_mem_upq h (sb br)) P
  rw [t1, phiFr, phi_skew] at d1
  rw [t2, phiFr, phi_symm] at d2
  have key : a (Eab i j - Eab j i) (κ P) = Complex.I • a (((sb br : ℂ) * Complex.I) • (Eab i j + Eab j i)) (κ P) ↔
      a (if br then Eab j i else Eab i j) (κ P) = 0 := by
    simp only [map_sub, map_smul, map_add, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.add_apply, smul_smul]
    have hI : Complex.I * ((sb br : ℂ) * Complex.I) = -(sb br : ℂ) := by
      linear_combination (sb br : ℂ) * Complex.I_mul_I
    rw [hI]
    have h2 : ∀ v : MvPolynomial σ ℂ, v + v = 0 → v = 0 := fun v hv => by
      rw [← two_smul ℂ v] at hv
      simpa using hv
    cases br
    · simp only [sb, Bool.false_eq_true, if_false, Complex.ofReal_one, neg_smul, one_smul]
      exact ⟨fun hv => h2 _ (by linear_combination hv), fun hv => by rw [hv]; ring⟩
    · simp only [sb, if_true, Complex.ofReal_neg, Complex.ofReal_one, neg_neg, one_smul]
      exact ⟨fun hv => h2 _ (by linear_combination -hv), fun hv => by rw [hv]; ring⟩
  simp only [mul_zero, zero_smul, add_zero] at d1 d2
  rw [← key]
  constructor
  · rintro ⟨PX, PY, h1, h2, h3⟩
    rw [← (d1 PX).1 h1, ← (d2 PY).1 h2, h3, map_smul]
  · intro hk
    refine ⟨κ.symm _, κ.symm _, (d1 _).2 (κ.apply_symm_apply _), (d2 _).2 (κ.apply_symm_apply _), ?_⟩
    rw [hk, map_smul]

theorem lt_iff {lam : Ix p q → ℚ} {t : ℝ} (ho : IsOrd (M.ε τ) (M.lam τ) lam c t e) (i j : Ix p q) :
    e i < e j ↔ t * (lam j : ℝ) < t * (lam i : ℝ) := by
  rw [← (M.enum τ).1.lt_iff_gt, ho.2.1, ho.2.1]
  push_cast
  constructor <;> intro h <;> linarith

theorem mem_hwSub (Λ : Ix p q → ℚ) (v : MvPolynomial σ ℂ) :
    v ∈ hwSub a Λ ↔ v ∈ wtSub a Λ ∧ ∀ i j, posC i j → a (Eab i j) v = 0 := by
  simp [hwSub, Submodule.mem_iInf]

theorem isHi_iff {lam : Ix p q → ℚ} (hp : IsParam lam) (ho : IsOrd (M.ε τ) (M.lam τ) lam c (sg br false) e)
    (hA : Side A pt κ (phiFr (M.fr τ) br e) c a) (P : MvPolynomial ι ℂ) :
    IsHi M τ A pt P ↔ κ P ∈ hwSub a (blattner lam) := by
  rw [mem_hwSub]
  refine and_congr (hasWt_iff hA (fun j => ?_) P) ?_
  · rw [ho.2.2]
    cases br <;> simp [sb, sg]
  · simp only [e.surjective.forall, ho.1 _, lt_iff ho, posC_iff hp]
    cases br
    · simp only [sg, if_true, one_mul, Rat.cast_lt]
      constructor
      · rintro h i j ⟨h1, h2⟩
        exact (killedBy_iff hA (fun hh => by subst hh; exact lt_irrefl _ h2) h1 P).1 (h i j h2 h1)
      · intro h i j h2 h1
        exact (killedBy_iff hA (fun hh => by subst hh; exact lt_irrefl _ h2) h1 P).2 (h i j ⟨h1, h2⟩)
    · simp only [sg, Bool.true_eq_false, if_false, neg_mul, one_mul, neg_lt_neg_iff, Rat.cast_lt]
      constructor
      · rintro h i j ⟨h1, h2⟩
        exact (killedBy_iff hA (fun hh => by subst hh; exact lt_irrefl _ h2) h1.symm P).1 (h j i h2 h1.symm)
      · intro h i j h2 h1
        exact (killedBy_iff hA (fun hh => by subst hh; exact lt_irrefl _ h2) h1 P).2 (h j i ⟨h1.symm, h2⟩)

theorem isLo_iff {lam : Ix p q → ℚ} (hp : IsParam lam) (ho : IsOrd (M.ε τ) (M.lam τ) lam c (sg br true) e)
    (hA : Side A pt κ (phiFr (M.fr τ) br e) c a) (P : MvPolynomial ι ℂ) :
    IsLo M τ A pt P ↔ κ P ∈ hwSub a (blattner lam) := by
  rw [mem_hwSub]
  refine and_congr (hasWt_iff hA (fun j => ?_) P) ?_
  · rw [Pi.neg_apply, ho.2.2]
    cases br <;> simp [sb, sg]
  · simp only [e.surjective.forall, ho.1 _, lt_iff ho, posC_iff hp]
    cases br
    · simp only [sg, Bool.false_eq_true, if_false, neg_mul, one_mul, neg_lt_neg_iff, Rat.cast_lt]
      constructor
      · rintro h i j ⟨h1, h2⟩
        exact (killedBy_iff hA (fun hh => by subst hh; exact lt_irrefl _ h2) h1 P).1 (h j i h2 h1.symm)
      · intro h i j h2 h1
        exact (killedBy_iff hA (fun hh => by subst hh; exact lt_irrefl _ h2) h1.symm P).2 (h j i ⟨h1.symm, h2⟩)
    · simp only [sg, if_true, one_mul, Rat.cast_lt]
      constructor
      · rintro h i j ⟨h1, h2⟩
        exact (killedBy_iff hA (fun hh => by subst hh; exact lt_irrefl _ h2) h1.symm P).1 (h i j h2 h1)
      · intro h i j h2 h1
        exact (killedBy_iff hA (fun hh => by subst hh; exact lt_irrefl _ h2) h1.symm P).2 (h i j ⟨h1, h2⟩)

end One

theorem isJoint_iff_cJoint : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (W : HSp D) (S' : D.what₂.Tau → SPar) (N : DSModel W S') (τ : D.what₂.Tau) (ι σ Z : Type) (A : Mn V.rank → (Z → ℂ) → (Z → ℂ)) (B : Mn W.rank → (Z → ℂ) → (Z → ℂ)) (pt : MvPolynomial ι ℂ → (Z → ℂ)) (κ : MvPolynomial ι ℂ ≃ₗ[ℂ] MvPolynomial σ ℂ) (p q r s : ℕ) (T₁ : GrpData p q) (T₂ : GrpData r s) (R₁ : DSRep T₁) (R₂ : DSRep T₂) (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) (a₂ : Mat r s →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) (l₁ : Ix p q → ℚ) (l₂ : Ix r s → ℚ) (c₁ c₂ : ℚ) (b₁ b₂ : Bool) (e₁ : Ix p q ≃ Fin V.rank) (e₂ : Ix r s ≃ Fin W.rank) (u₁ : kfin M τ → R₁.HK.V) (u₂ : kfin N τ → R₂.HK.V), KTie R₁ M τ l₁ c₁ b₁ true e₁ u₁ → KTie R₂ N τ l₂ c₂ b₂ false e₂ u₂ → Side A pt κ (phiFr (M.fr τ) b₁ e₁) c₁ a₁ → Side B pt κ (phiFr (N.fr τ) b₂ e₂) c₂ a₂ → Graded κ → ∀ Φ, IsJoint M τ A pt N B Φ ↔ CJoint a₁ a₂ (blattner l₁) (blattner l₂) (κ Φ) := by
  intro D V S M W S' N τ ι σ Z A B pt κ p q r s T₁ T₂ R₁ R₂ a₁ a₂ l₁ l₂ c₁ c₂ b₁ b₂ e₁ e₂ u₁ u₂ h₁ h₂ hA hB hκ Φ
  simp only [IsJoint, CJoint, IsHW, isHarm_iff h₁.ord.1 h₁.lie hA hκ, isHarm_iff h₂.ord.1 h₂.lie hB hκ,
    isLo_iff h₁.par h₁.ord hA, isHi_iff h₂.par h₂.ord hB, ne_eq, EmbeddingLike.map_eq_zero_iff]
  constructor
  · rintro ⟨h0, ⟨d, ⟨x1, x2⟩, -, x3⟩, y1, y2⟩
    exact ⟨⟨d, x1, x2, x3⟩, ⟨h0, y1⟩, h0, y2⟩
  · rintro ⟨⟨d, x1, x2, x3⟩, ⟨h0, y1⟩, -, y2⟩
    exact ⟨h0, ⟨d, ⟨x1, x2⟩, x1, x3⟩, y1, y2⟩

end GlobalTheory.ArchRec.JointTransfer
end
