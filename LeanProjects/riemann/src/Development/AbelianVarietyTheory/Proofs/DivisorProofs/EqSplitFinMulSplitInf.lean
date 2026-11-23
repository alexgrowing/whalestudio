import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankWsp
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DefiniteUnitaryRealApproxAndFiniteInfiniteSplit

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TrKer

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

instance finiteDimensional_wsp (lam : InfinitePlace E → DomWeight n) : FiniteDimensional ℂ (Wsp lam) :=
  Module.Finite.of_basis (Basis.piTensorProduct fun v => Module.finBasis ℂ _)

variable (E n) in

def splitFin : UA E n →* finU E n := (GlobalTheory.UnitarySplit.dense_and_split E n).2.2.2.choose

variable (E n) in

def splitInf : UA E n →* infU E n := (GlobalTheory.UnitarySplit.dense_and_split E n).2.2.2.choose_spec.choose

theorem continuous_splitFin : Continuous (splitFin E n) :=
  (GlobalTheory.UnitarySplit.dense_and_split E n).2.2.2.choose_spec.choose_spec.1

theorem eq_splitFin_mul_splitInf (x : UA E n) : x = (splitFin E n x).1 * (splitInf E n x).1 :=
  (GlobalTheory.UnitarySplit.dense_and_split E n).2.2.2.choose_spec.choose_spec.2.2.1 x

theorem splitFin_mul (g : finU E n) (k : infU E n) : splitFin E n (g.1 * k.1) = g :=
  ((GlobalTheory.UnitarySplit.dense_and_split E n).2.2.2.choose_spec.choose_spec.2.2.2 g k).1

theorem splitInf_mul (g : finU E n) (k : infU E n) : splitInf E n (g.1 * k.1) = k :=
  ((GlobalTheory.UnitarySplit.dense_and_split E n).2.2.2.choose_spec.choose_spec.2.2.2 g k).2

theorem splitFin_fin (g : finU E n) : splitFin E n g.1 = g := by
  simpa using splitFin_mul g 1

theorem splitFin_inf (k : infU E n) : splitFin E n k.1 = 1 := by
  simpa using splitFin_mul 1 k

def wInf (lam : InfinitePlace E → DomWeight n) : Representation ℂ (UA E n) (Wsp lam) where
  toFun g := PiTensorProduct.map fun v => GlobalTheory.Branching.sqRep ℂ n (lam v) (cEmb v.embedding g)
  map_one' := by
    simp only [map_one]
    exact PiTensorProduct.map_id
  map_mul' a b := by
    simp only [map_mul]
    exact PiTensorProduct.map_mul _ _

def phiFun (lam : InfinitePlace E → DomWeight n) :
    (finU E n → Module.Dual ℂ (Wsp lam)) →ₗ[ℂ] Wsp lam →ₗ[ℂ] (UA E n → ℂ) :=
  LinearMap.mk₂ ℂ (fun F w g => F (splitFin E n g) (wInf lam g w))
    (fun F F' w => by funext g; simp)
    (fun c F w => by funext g; simp)
    (fun F w w' => by funext g; simp)
    (fun c F w => by funext g; simp)

@[simp] theorem phiFun_apply (lam : InfinitePlace E → DomWeight n) (F : finU E n → Module.Dual ℂ (Wsp lam))
    (w : Wsp lam) (g : UA E n) : phiFun lam F w g = F (splitFin E n g) (wInf lam g w) := rfl

def Phi (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)) :
    vecM S lam K' ⊗[ℂ] Wsp lam →ₗ[ℂ] (UA E n → ℂ) :=
  TensorProduct.lift ((phiFun lam).comp (vecM S lam K').subtype)

@[simp] theorem Phi_tmul (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w))
    (F : vecM S lam K') (w : Wsp lam) : Phi S lam K' (F ⊗ₜ w) = phiFun lam F.1 w := by
  simp [Phi]

theorem cEmb_fin (τ : E →+* ℂ) (k : finU E n) : cEmb τ k.1 = 1 := by
  have hk : cInf k.1 = 1 := MonoidHom.mem_ker.1 k.2
  simp only [cEmb, MonoidHom.comp_apply, hk, map_one]

theorem wInf_fin (lam : InfinitePlace E → DomWeight n) (k : finU E n) : wInf lam k.1 = 1 := by
  have h : ∀ v : InfinitePlace E, cEmb v.embedding k.1 = 1 := fun v => cEmb_fin _ k
  change PiTensorProduct.map (fun v => GlobalTheory.Branching.sqRep ℂ n (lam v) (cEmb v.embedding k.1)) = 1
  simp only [h, map_one]
  exact PiTensorProduct.map_id

theorem splitFin_mul_fin (g : UA E n) (k : finU E n) : splitFin E n (g * k.1) = splitFin E n g * k := by
  rw [map_mul, splitFin_fin]

theorem phiFun_mul_fin (lam : InfinitePlace E → DomWeight n) (F : finU E n → Module.Dual ℂ (Wsp lam)) (w : Wsp lam)
    (g : UA E n) (k : finU E n) :
    phiFun lam F w (g * k.1) = phiFun lam (rightReg ℂ (finU E n) (Module.Dual ℂ (Wsp lam)) k F) w g := by
  rw [phiFun_apply, phiFun_apply, splitFin_mul_fin, map_mul, wInf_fin, mul_one]
  rfl

end GlobalTheory.BCT.TrKer
