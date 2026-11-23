import Formalism.LocalToGlobal.Columns.HeckeInertLemmas
import Formalism.LocalToGlobal.Columns.WmLemmas
import Formalism.LocalToGlobal.Divisibility.LiftLatInst

noncomputable section

namespace Formalism.L2.Col

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Module

section NbFunI

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}
variable (K V : Type) [Field K] [AddCommGroup V] [Module K V]

def nbFunI (P : Ideal (𝓞 E)) (s : List ℕ) : (DecoSet E n ST SG → V) →ₗ[K] (DecoSet E n ST SG → V) where
  toFun ψ d := ∑ d₁ ∈ d.inertNb P s, ψ d₁
  map_add' ψ ψ' := by
    funext d
    simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c ψ := by
    funext d
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]

end NbFunI

section Tr

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem trF_nbFunI {V : Type} [AddCommGroup V] [Module X.K V] (a : GLG X.E n SG) (P : Ideal (𝓞 X.E)) (s : List ℕ)
    (ψ : DecoSet X.E n ST SG → V) :
    trF X n ST SG V a (nbFunI X.K V P s ψ) = nbFunI X.K V P s (trF X n ST SG V a ψ) := by
  funext d
  show ∑ d₁ ∈ (((1 : UF X.E n), a⁻¹) • d).inertNb P s, ψ d₁ =
    ∑ d₁ ∈ d.inertNb P s, ψ (((1 : UF X.E n), a⁻¹) • d₁)
  exact DecoSet.sum_inertNb_smul P s _ d ψ

variable (C : CoefPk X n (DecoSet X.E n ST SG)) (Λ : LevFam X.E X.K n SG)

theorem heckeFamI_formPts_apply (S0 : Set (HeightOneSpectrum (𝓞 X.E))) (y : LevOffI ST SG S0 × List ℕ)
    (φ : (formGSD C Λ).EqFun) :
    ((heckeFamI (Formalism.L2.DIV.formPts C Λ) S0 y φ : (formGSD C Λ).EqFun) : DecoSet X.E n ST SG → C.V) =
      nbFunI X.K C.V y.1.1.asIdeal y.2 (φ : DecoSet X.E n ST SG → C.V) := by
  funext d
  show ((heckeI (Formalism.L2.DIV.formPts C Λ) y.1.1.asIdeal y.2).op φ : DecoSet X.E n ST SG → C.V) d =
    ∑ d₁ ∈ DecoSet.inertNb y.1.1.asIdeal y.2 d, (φ : DecoSet X.E n ST SG → C.V) d₁
  rw [heckeI_op_apply]
  simp [DecoPts.nbI, Formalism.L2.DIV.formPts]

theorem heckeFamI_comm_trRep {A : Type} [Group A] (ι : A →* GLG X.E n SG) (hι : ∀ a w, (Λ w).NormBy (ι a w))
    (S0 : Set (HeightOneSpectrum (𝓞 X.E))) (y : LevOffI ST SG S0 × List ℕ) (a : A) :
    Commute (trRep C Λ ι hι a) (heckeFamI (Formalism.L2.DIV.formPts C Λ) S0 y) := by
  show trRep C Λ ι hι a * heckeFamI (Formalism.L2.DIV.formPts C Λ) S0 y =
    heckeFamI (Formalism.L2.DIV.formPts C Λ) S0 y * trRep C Λ ι hι a
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  rw [Module.End.mul_apply, Module.End.mul_apply]
  show trF X n ST SG C.V (ι a)
      ((heckeFamI (Formalism.L2.DIV.formPts C Λ) S0 y φ : (formGSD C Λ).EqFun) : DecoSet X.E n ST SG → C.V) =
    ((heckeFamI (Formalism.L2.DIV.formPts C Λ) S0 y (trRep C Λ ι hι a φ) : (formGSD C Λ).EqFun) :
      DecoSet X.E n ST SG → C.V)
  rw [heckeFamI_formPts_apply, heckeFamI_formPts_apply, trF_nbFunI]
  rfl

end Tr

end Formalism.L2.Col
