import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DifferentiableOnProdOfForall
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueThetaCharAtPoint
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.RiemannFormBijectiveOfWeilNondeg

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusRM.DiagFrame

variable {A : Over (Sp ℂ)} [GrpObj A] [IsCommMonObj A]

theorem padd_eq {T : Over (Sp ℂ)} (a b : T ⟶ A) : padd A a b = a * b := (Hom.mul_def a b).symm

theorem pzero_eq (T : Over (Sp ℂ)) : pzero A T = 1 := by
  rw [pzero, Hom.one_def]

theorem pt_diag_psum (y : 𝟙_ (Over (Sp ℂ)) ⟶ A) (I : Finset (Fin 2)) :
    y ≫ (lift (𝟙 A) (𝟙 A) ≫ psum A (x2 A) I) = y ^ I.card := by
  have h0 : y ≫ lift (𝟙 A) (𝟙 A) ≫ fst A A = y := by simp
  have h1 : y ≫ lift (𝟙 A) (𝟙 A) ≫ snd A A = y := by simp
  have hI : I = ∅ ∨ I = {0} ∨ I = {1} ∨ I = {0, 1} := by revert I; decide
  rcases hI with rfl | rfl | rfl | rfl <;>
    simp [psum, padd_eq, pzero_eq, x2, List.finRange_succ, comp_mul, comp_one, h0, h1, pow_two]

theorem sum_exp_sq :
    (∑ I : ULift.{0} (Finset (Fin 2)), (((-1 : ℤ) ^ (2 - I.down.card) : ℤ) : ℂ) * ((I.down.card : ℕ) : ℂ) ^ 2) = 2 := by
  have hZ : (∑ I : Finset (Fin 2), ((-1 : ℤ) ^ (2 - I.card)) * (I.card : ℤ) ^ 2) = 2 := by decide
  have hU : (∑ I : ULift.{0} (Finset (Fin 2)), ((-1 : ℤ) ^ (2 - I.down.card)) * (I.down.card : ℤ) ^ 2) = 2 :=
    (Fintype.sum_equiv Equiv.ulift _ (fun I : Finset (Fin 2) => ((-1 : ℤ) ^ (2 - I.card)) * (I.card : ℤ) ^ 2)
      (fun _ => rfl)).trans hZ
  exact_mod_cast hU

theorem herm_smul_nat {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (c : ℕ) (z l : Fin g → ℂ) :
    ((c : ℂ) • z) ⬝ᵥ Hm.mulVec (star ((c : ℂ) • l)) = (c : ℂ) ^ 2 * (z ⬝ᵥ Hm.mulVec (star l)) := by
  have hs : star ((c : ℂ) • l) = (c : ℂ) • star l := by
    rw [star_smul]; simp
  rw [hs, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  ring

end GlobalTheory.TorusRM.DiagFrame

namespace GlobalTheory.TorusRM.DiagFrame

variable {A : Over (Sp ℂ)} [GrpObj A] [IsCommMonObj A]

def diagSum (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (I : ULift.{0} (Finset (Fin 2))) : A ⟶ A :=
  lift (𝟙 A) (𝟙 A) ≫ psum A (x2 A) I.down

theorem chart (M : LB A.left) (x : Sp ℂ ⟶ A.left) (J : ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left).ι) :
    (⊤ : (Sp ℂ).Opens) ≤ x ⁻¹ᵁ ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left).U J ↔
      ∀ I, ⊤ ≤ (x ≫ (diagSum A I).left) ⁻¹ᵁ M.U (J PUnit.unit I) := by
  rw [GlobalTheory.ThetaPoint.top_le_pull_iff]
  show ⊤ ≤ (x ≫ (lift (𝟙 A) (𝟙 A)).left) ⁻¹ᵁ
      LB.wchart M (fun I : ULift.{0} (Finset (Fin 2)) => (psum A (x2 A) I.down).left) (J PUnit.unit) ↔ _
  refine (CubeValues.le_preimage_wchart _ M (fun I : ULift.{0} (Finset (Fin 2)) => (psum A (x2 A) I.down).left)
    (J PUnit.unit : ULift.{0} (Finset (Fin 2)) → M.ι)).trans ?_
  simp only [diagSum, Over.comp_left, Category.assoc]

theorem chart' (M : LB A.left) (x : Sp ℂ ⟶ A.left) (j : ULift.{0} (Finset (Fin 2)) → M.ι) :
    (⊤ : (Sp ℂ).Opens) ≤ x ⁻¹ᵁ LB.wchart M (fun I => (diagSum A I).left) j ↔
      ∀ I, ⊤ ≤ (x ≫ (diagSum A I).left) ⁻¹ᵁ M.U (j I) :=
  CubeValues.le_preimage_wchart _ _ _ _

end GlobalTheory.TorusRM.DiagFrame

namespace GlobalTheory.TorusRM.DiagFrame

variable {A : Over (Sp ℂ)} [GrpObj A] [IsCommMonObj A]

def expo (I : ULift.{0} (Finset (Fin 2))) : ℤ := (-1) ^ (2 - I.down.card)

theorem val_g (M : LB A.left) (x : Sp ℂ ⟶ A.left) (J J' : ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left).ι)
    (h : (⊤ : (Sp ℂ).Opens) ≤ x ⁻¹ᵁ ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left).U J)
    (h' : (⊤ : (Sp ℂ).Opens) ≤ x ⁻¹ᵁ ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left).U J') :
    valAt' x (((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left).U J ⊓ ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left).U J')
        (((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left).g J J').val =
      valAt' x ((M.LinComb (fun I => (diagSum A I).left) expo).U (J PUnit.unit) ⊓
          (M.LinComb (fun I => (diagSum A I).left) expo).U (J' PUnit.unit))
        ((M.LinComb (fun I => (diagSum A I).left) expo).g (J PUnit.unit) (J' PUnit.unit)).val := by
  refine (GlobalTheory.ThetaPoint.valAt'_pull_g _ _ _ _ _ h h').trans ?_
  have hL := (GlobalTheory.ThetaPoint.top_le_pull_iff _ _ _ _).1 h
  have hL' := (GlobalTheory.ThetaPoint.top_le_pull_iff _ _ _ _).1 h'
  have hc := (chart' M x (J PUnit.unit)).2 ((chart M x J).1 h)
  have hc' := (chart' M x (J' PUnit.unit)).2 ((chart M x J').1 h')
  refine (CubeValues.val_linComb (x ≫ (lift (𝟙 A) (𝟙 A)).left) valAt'_rules M
    (fun I : ULift.{0} (Finset (Fin 2)) => (psum A (x2 A) I.down).left) expo
    (J PUnit.unit : ULift.{0} (Finset (Fin 2)) → M.ι) (J' PUnit.unit : ULift.{0} (Finset (Fin 2)) → M.ι) hL hL').trans ?_
  refine Eq.trans ?_ (CubeValues.val_linComb x valAt'_rules M (fun I => (diagSum A I).left) expo _ _ hc hc').symm
  simp only [diagSum, Over.comp_left, Category.assoc]

end GlobalTheory.TorusRM.DiagFrame

namespace GlobalTheory.TorusRM.DiagFrame

variable {A : Over (Sp ℂ)} [GrpObj A] [IsCommMonObj A] {M : LB A.left} {g : ℕ}

def mulCard (g : ℕ) (I : ULift.{0} (Finset (Fin 2))) : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
  ((I.down.card : ℕ) : ℂ) • LinearMap.id

theorem mulCard_apply (I : ULift.{0} (Finset (Fin 2))) (z : Fin g → ℂ) :
    mulCard g I z = ((I.down.card : ℕ) : ℂ) • z := rfl

theorem ex_mulCard (u : HolUnif A M g) (I : ULift.{0} (Finset (Fin 2))) (z : Fin g → ℂ) :
    u.ex (mulCard g I z) = u.ex z ≫ diagSum A I := by
  rw [mulCard_apply, Nat.cast_smul_eq_nsmul, holUnif_ex_nsmul_eq_pow]
  exact (pt_diag_psum (u.ex z) I.down).symm

theorem smul_mem_lat (u : HolUnif A M g) (l : u.Λ) (I : ULift.{0} (Finset (Fin 2))) :
    ((I.down.card : ℕ) : ℂ) • (l : Fin g → ℂ) ∈ u.Λ := by
  rw [Nat.cast_smul_eq_nsmul]
  exact nsmul_mem l.2 _

def diagUnif (u : HolUnif A M g) : HolUnif A ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left) g :=
  let u₁ := linCombUnif u u (diagSum A) (mulCard g) expo (ex_mulCard u)
  have hc : ∀ (J : ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left).ι) (z : Fin g → ℂ),
      (⊤ : (Sp ℂ).Opens) ≤ (u.ex z).left ⁻¹ᵁ ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left).U J →
      (⊤ : (Sp ℂ).Opens) ≤ (u₁.ex z).left ⁻¹ᵁ (M.LinComb (fun I => (diagSum A I).left) expo).U (J PUnit.unit) :=
    fun J z hz => (chart' M _ (J PUnit.unit)).2 ((chart M _ J).1 hz)
  { ex := u.ex
    ex_add := u.ex_add
    ex_onto := u.ex_onto
    Λ := u.Λ
    ker := u.ker
    discrete := u.discrete
    full := u.full
    hol := u.hol
    fr := fun J z => u₁.fr (J PUnit.unit) z
    fr_hol := fun J => (u₁.fr_hol (J PUnit.unit)).mono fun z hz => hc J z hz
    fr_ne := fun J z hz => u₁.fr_ne _ z (hc J z hz)
    fr_compat := fun J J' z hz => by
      obtain ⟨h1, h2⟩ := (top_le_preimage_inf _ _ _).1 hz
      rw [val_g M _ J J' h1 h2]
      exact u₁.fr_compat _ _ z ((top_le_preimage_inf _ _ _).2 ⟨hc J z h1, hc J' z h2⟩) }

theorem diagUnif_fr (u : HolUnif A M g) (J : ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left).ι) (z : Fin g → ℂ) :
    (diagUnif u).fr J z = ∏ I, u.fr (J PUnit.unit I) (((I.down.card : ℕ) : ℂ) • z) ^ expo I := rfl

theorem diagUnif_ex (u : HolUnif A M g) : (diagUnif u).ex = u.ex := rfl

def diagChar (u : HolUnif A M g) (χ : u.Λ → ℂ) (l : u.Λ) : ℂ :=
  ∏ I, χ ⟨((I.down.card : ℕ) : ℂ) • (l : Fin g → ℂ), smul_mem_lat u l I⟩ ^ expo I

end GlobalTheory.TorusRM.DiagFrame

namespace GlobalTheory.TorusRM.DiagFrame

variable {A : Over (Sp ℂ)} [GrpObj A] [IsCommMonObj A] {M : LB A.left} {g : ℕ}

theorem isFactorAH_diagUnif (u : HolUnif A M g) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    (hF : IsFactorAH u Hm χ) : IsFactorAH (diagUnif u) ((2 : ℂ) • Hm) (diagChar u χ) := by
  refine ⟨?_, fun l => ?_, fun l J z hz => ?_⟩
  · show Matrix.conjTranspose ((2 : ℂ) • Hm) = (2 : ℂ) • Hm
    rw [Matrix.conjTranspose_smul, hF.1.eq]
    simp
  · show ‖∏ I, _‖ = 1
    rw [norm_prod]
    exact Finset.prod_eq_one fun I _ => by rw [norm_zpow, hF.2.1, one_zpow]
  · have hc : ∀ I, (⊤ : (Sp ℂ).Opens) ≤ (u.ex (((I.down.card : ℕ) : ℂ) • z)).left ⁻¹ᵁ M.U (J PUnit.unit I) := by
      intro I
      have h := (chart M _ J).1 hz I
      rw [← mulCard_apply, ex_mulCard, Over.comp_left]
      exact h
    set E : ℂ := Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
      Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) with hE
    have key : ∀ I : ULift.{0} (Finset (Fin 2)),
        u.fr (J PUnit.unit I) (((I.down.card : ℕ) : ℂ) • z) ^ expo I =
          χ ⟨((I.down.card : ℕ) : ℂ) • (l : Fin g → ℂ), smul_mem_lat u l I⟩ ^ expo I *
            Complex.exp ((expo I : ℂ) * ((((I.down.card : ℕ) : ℂ)) ^ 2 * E)) *
            u.fr (J PUnit.unit I) (((I.down.card : ℕ) : ℂ) • (z + (l : Fin g → ℂ))) ^ expo I := by
      intro I
      rw [hF.2.2 ⟨((I.down.card : ℕ) : ℂ) • (l : Fin g → ℂ), smul_mem_lat u l I⟩ (J PUnit.unit I) _ (hc I)]
      simp only []
      rw [herm_smul_nat, herm_smul_nat, smul_add, mul_zpow, mul_zpow, Complex.exp_int_mul]
      congr 3
      rw [hE]
      ring_nf
    rw [diagUnif_fr, diagUnif_fr, Finset.prod_congr rfl fun I _ => key I, Finset.prod_mul_distrib,
      Finset.prod_mul_distrib, ← Complex.exp_sum]
    congr 2
    have hs := sum_exp_sq
    have e1 : (∑ I : ULift.{0} (Finset (Fin 2)), (expo I : ℂ) * ((((I.down.card : ℕ) : ℂ)) ^ 2 * E)) =
        (∑ I : ULift.{0} (Finset (Fin 2)), (((-1 : ℤ) ^ (2 - I.down.card) : ℤ) : ℂ) * ((I.down.card : ℕ) : ℂ) ^ 2) * E := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun I _ => ?_
      simp only [expo]
      ring
    rw [e1, hs, hE, Matrix.smul_mulVec, dotProduct_smul, dotProduct_smul,
      smul_eq_mul, smul_eq_mul]
    congr 1
    ring

end GlobalTheory.TorusRM.DiagFrame

open GlobalTheory GlobalTheory.TorusRM.DiagFrame in

theorem GlobalTheory.TorusRM.exists_isFactorAH_lam_diag : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A →
    ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ),
    M.IsLB → IsFactorAH u Hm χ →
    ∃ (u' : HolUnif A ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left) g) (χ' : u'.Λ → ℂ),
      u'.ex = u.ex ∧ IsFactorAH u' ((2 : ℂ) • Hm) χ' := by
  intro g A _ hA M u Hm χ hM hF
  haveI : IsCommMonObj A := hA.comm
  exact ⟨diagUnif u, diagChar u χ, rfl, isFactorAH_diagUnif u hF⟩
