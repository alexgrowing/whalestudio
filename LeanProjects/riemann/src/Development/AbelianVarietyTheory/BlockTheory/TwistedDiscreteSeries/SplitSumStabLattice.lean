import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsSplitSum (e : AE D) : Prop :=
  IsSplitIdem D e ∨ ∃ P : Finset (Formalism.L2.DIV.Pl D.host.E), IsIdemSum e P

def StabLat (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (g : GA D V) : Prop :=
  ∀ y : Fin V.rank → Formalism.IndefR.Lev.EAf D,
    y ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ↔
      (Formalism.IndefR.Lev.finE V g).val.mulVec y ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ

def pullPt (S T : HSp D) (g : GA D S) (h : GA D T) (t : WO S T) : WO S T :=
  HMul.hMul (HMul.hMul (mt T h⁻¹) (t : Matrix (Fin T.rank) (Fin S.rank) (AE D))) (mt S g)

def LinearLaw (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (e a : AE D) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)) : Prop :=
  ∀ (g : GA D S) (h : GA D T), SuppAt e S g → SuppAt e T h → StabLat S ΛS g → StabLat T ΛT h →
    ∀ x y : (AE D)ˣ, IsDetAt e S g x → IsDetAt e T h y →
      ∀ Φ : WO S T → ℂ, IsSBHalf a (latO S T ΛS ΛT fun _ => True) Φ →
        om (g, h) (Tm Φ) = (((χT x : ℂ))⁻¹ * (χS y : ℂ)) • Tm (fun t => Φ (pullPt S T g h t))

def WeilSplitFormula (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
      (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
      IsSelfDualC S ΛS → IsSelfDualC T ΛT →
      ∀ f₀ : WO S T → ℂ, IsVacO ψ θ S T sS sT ΛS ΛT f₀ →
      ∀ e : AE D, IsSplitSum e →
        (∀ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm →
          LinearLaw S T χS χT om ΛS ΛT e e Tm) ∧
        (∀ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) (cA D e) (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm →
          LinearLaw S T χS χT om ΛS ΛT e (cA D e) Tm)

def WeilSplitFormulaAll : Prop := ∀ D : D7, WeilSplitFormula D

theorem pullPt_eq_actO (S T : HSp D) (g : GA D S) (h : GA D T) (t : WO S T) :
    pullPt S T g h t = actO S T g⁻¹ h⁻¹ t := by
  unfold pullPt actO; rw [inv_inv]

theorem factor_eq (χS χT : (AE D)ˣ →* Circle) (x y : (AE D)ˣ) :
    ((χT x : ℂ))⁻¹ * (χS y : ℂ) = (splitFacO χS χT x y : ℂ) := by
  simp [splitFacO]

theorem mulVec_mem_hatL {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)} (hβ : Formalism.L2.DIV.IsFrame β Λ)
    {k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hk : k ∈ Formalism.L2.DIV.St β) {y : Fin n → E ⊗[F] Formalism.L2.Herm.Af F}
    (hy : y ∈ Formalism.L2.Herm.hatL (F := F) Λ) : k.val.mulVec y ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
  obtain ⟨u, rfl⟩ := hk
  have hy' := (hβ y).1 hy
  refine (hβ _).2 fun i => ?_
  have e0 : β⁻¹ * Formalism.L2.DIV.frGL β u = Formalism.L2.DIV.intGL F E n u * β⁻¹ := by
    show β⁻¹ * (β * Formalism.L2.DIV.intGL F E n u * β⁻¹) = _
    group
  have e1 : (β⁻¹).val.mulVec ((Formalism.L2.DIV.frGL β u).val.mulVec y) =
      (Formalism.L2.DIV.intGL F E n u).val.mulVec ((β⁻¹).val.mulVec y) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, e0]
  rw [e1]
  show ∑ j, (Formalism.L2.DIV.intGL F E n u).val i j * ((β⁻¹).val.mulVec y) j ∈ _
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (u.val i j).2 (hy' j)

theorem mulVec_mem_hatL_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)} (hβ : Formalism.L2.DIV.IsFrame β Λ)
    {k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hk : k ∈ Formalism.L2.DIV.St β) (y : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) :
    y ∈ Formalism.L2.Herm.hatL (F := F) Λ ↔ k.val.mulVec y ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
  refine ⟨mulVec_mem_hatL hβ hk, fun hy => ?_⟩
  have := mulVec_mem_hatL hβ (Subgroup.inv_mem _ hk) hy
  rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at this

theorem stabLat_of_mem_St (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (hβ : Formalism.L2.DIV.IsFrame β Λ) (g : GA D V)
    (hg : Formalism.IndefR.Lev.finE V g ∈ Formalism.L2.DIV.St β) : StabLat V Λ g :=
  fun y => mulVec_mem_hatL_iff hβ hg y

end GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice

end
