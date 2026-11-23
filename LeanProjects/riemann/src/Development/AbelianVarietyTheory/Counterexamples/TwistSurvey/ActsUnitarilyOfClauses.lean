import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.DefiniteUnitaryAction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupActsUnitarily

noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.DefiniteUnitaryAction
open scoped ComplexOrder

namespace GlobalTheory.UnitaryActionTest

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem actsUnitarily_of_clauses (R : RealDat D A Ks) (hE : R.models_HE) (gE : R.models_gE) (h0 : R.models_ν0)
    (hW : R.models_HW) (gW : R.models_gW) (hν : R.models_νW) (ht : R.fam_tie) (hX : R.models_cX) (hV : R.models_cV) :
    ActsUnitarily R :=
  have h := GlobalTheory.FiniteGroupUnitary.definiteUnitary R ht hX hV
  ⟨GlobalTheory.FiniteGroupUnitary.isUnitaryRep_of_norm _ (GlobalTheory.T.norm_goodRows_finiteGroup_action R hE gE h0),
    fun i σ => GlobalTheory.FiniteGroupUnitary.isUnitaryRep_of_norm _ (GlobalTheory.T.norm_liftForms_finiteGroup_action R hW gW hν i σ),
    fun t σ => h.1 t σ, fun i t σ => h.2 i t σ⟩

theorem unitaryAction : UnitaryAction := fun _ _ _ _ _ _ _ _ _ _ _ R _ h =>
  actsUnitarily_of_clauses R h.models.HE h.models.gE h.models.ν0 h.models.HW h.models.gW h.models.νW h.fam.tie
    h.models.cX h.models.cV

theorem geometric_unitary (R : RealDat D A Ks) (hU : R.LUnif) (hW : R.models_HW) (gW : R.models_gW) (h : ActsUnitarily R)
    (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (g : G) (x y : Fin (R.nW i) → D.what₂.LL) :
    inner ℂ ((R.FW i).j σ ((R.FW i).ρ g x)) ((R.FW i).j σ ((R.FW i).ρ g y)) = inner ℂ ((R.FW i).j σ x) ((R.FW i).j σ y) := by
  have e : ∀ z, (R.FW i).j σ ((R.FW i).ρ g z) =
      σ (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) • R.gW i σ g ((R.FW i).j σ z) := fun z =>
    (hW i σ).1 (by rw [(hU i σ).2.2, map_smul, gW])
  have n : ‖σ (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL)‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one (n := Fintype.card G)
      (by rw [← map_pow, ← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one, map_one])
      Fintype.card_ne_zero
  rw [e, e, inner_smul_left, inner_smul_right, h.formsW, ← mul_assoc, Complex.conj_mul', n]
  simp

def lineDatum : CSD ℚ where
  Cl := Unit
  V := ℚ
  ιV := Unit
  bV := Module.Basis.singleton Unit ℚ
  pair := LinearMap.mk₂'ₛₗ _ _ (fun a b => a * b) (fun _ _ _ => add_mul _ _ _)
    (fun c a b => by simp [mul_assoc]) (fun _ _ _ => mul_add _ _ _) (fun c a b => by simp [mul_left_comm])
  Gam := fun _ => Unit
  ρ := fun _ => 1
  Nab := fun _ => ⊤
  Del := fun _ => ⊤

theorem not_isUnitaryAt_scalars (σ : ℚ →+* ℂ) :
    ¬ IsUnitaryAt lineDatum σ (Representation.ofDistribMulAction ℚ ℚˣ lineDatum.Forms) := by
  intro h
  let f : lineDatum.Forms := ⟨fun _ => (1 : ℚ), fun _ _ => rfl⟩
  have hs : ∀ a, σ (star a) = starRingEnd ℂ (σ a) := fun a => by simp
  have := (isUnitaryAt_iff lineDatum σ hs _).1 h (Units.mk0 2 two_ne_zero) f f
  change ∑ c : Unit, ((Fintype.card Unit : ℕ) : ℚ)⁻¹ * (((2 : ℚ) * 1) * ((2 : ℚ) * 1)) =
    ∑ c : Unit, ((Fintype.card Unit : ℕ) : ℚ)⁻¹ * ((1 : ℚ) * 1) at this
  norm_num at this

end GlobalTheory.UnitaryActionTest
