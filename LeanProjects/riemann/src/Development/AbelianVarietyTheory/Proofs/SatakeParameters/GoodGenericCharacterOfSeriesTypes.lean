import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodGeneric
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GenericLevelCharacterAlternatingSignConjInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodCharacterPlacewiseCuspidalParabolicProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspIndProdCharOfIsProdCuspChar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GoodGenericSer

open GlobalTheory.GoodGenericInv

theorem goodGenericCharacter_of_seriesTypes : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → ∀ s, A3.fam3.Ok3 s → (∀ k : Fin 2, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; ∃ (C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod (D.host.g k))) (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod (D.host.g k)) C), ∀ f, D.ntypes.eSer k f = Formalism.L2.NT.eSerO O D.R.r f) → GoodGeneric A3.A.X F.P0 F.ψ0 ∧ GoodGeneric A3.A.X F.P0 F.ψ0⁻¹ := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hC s hOk hser
  have hG := hC.base.grp
  have hOk2 : A3.A.fam.Ok s := hOk.ok2
  have hprod : ∀ χ ∈ A3.A.X, GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsProdCuspChar D.what₂.embLL R.Pg D.R.r fun g => χ (R.eG.symm g) :=
    GlobalTheory.T.goodCharacter_placewise_cuspidal_parabolic_product D G Pl0 T A3.A Ks R.toRealDat hG.record hser (fun χ hχ => hOk2.irr χ hχ)
  letI : Fintype F.P0 := Fintype.ofFinite _
  have hsum : ∀ χ ∈ A3.A.X, ∑ h : F.P0, χ (h : G) * (((F.ψ0 h)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) = (Fintype.card F.P0 : D.what₂.LL) :=
    fun χ hχ => by
      letI : Fintype F.lv2.P0 := (inferInstance : Fintype F.P0)
      exact GlobalTheory.RealOneVector.typeSum_base_eq_card D G Pl0 T A3.A Ks R.toRealDat F.lv2 hG.levels hprod χ hχ
  have hone : ∀ χ ∈ A3.A.X, χ 1 ≠ 0 := fun χ hχ h =>
    GlobalTheory.FinGL.LeviChar.irrChar_one_ne_zero
      (GlobalTheory.GoodTypeGeneric.isIrrChar_of_isAbsIrrChar D.what₂.embLL (hOk2.irr χ hχ)) (by rw [h, map_zero])
  have hcard : (Fintype.card F.P0 : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨fun χ hχ => GlobalTheory.GoodTypeGeneric.chiIdem_mul_lvlIdem_ne_zero _ _ (hone χ hχ) (by rw [hsum χ hχ]; exact hcard),
    fun χ hχ => ?_⟩
  obtain ⟨ψ', -, hlev, -⟩ := hG.levels
  have hcls : ∀ g h, χ (g * h * g⁻¹) = χ h := by
    obtain ⟨n, ρ, -, hρ⟩ := hOk2.irr χ hχ
    intro g h
    apply (algebraMap D.what₂.LL (AlgebraicClosure D.what₂.LL)).injective
    rw [← hρ, ← hρ, ρ.char_conj]
  have hmem : ∀ x : G0 R.Pg D.R.r, R.eG.symm x ∈ F.P0 →
      R.eG.symm (alternatingSignDiagonalLevelGroup R.Pg D.R.r * x * (alternatingSignDiagonalLevelGroup R.Pg D.R.r)⁻¹) ∈ F.P0 := by
    intro x hx
    have h1 : x ∈ (P0 R.Pg D.R.r ψ').H := (congrArg LevelP.H hlev) ▸ (show x ∈ (R.toRealDat.levR F.lv2 false).H from hx)
    have h2 := alternatingSignDiagonal_conj_mem_genericLevel ψ' h1
    have h3 : _ ∈ (R.toRealDat.levR F.lv2 false).H := (congrArg LevelP.H hlev).symm ▸ h2
    exact h3
  let t : G := R.eG.symm (alternatingSignDiagonalLevelGroup R.Pg D.R.r)
  have he : ∀ x, t * R.eG.symm x * t⁻¹ = R.eG.symm (alternatingSignDiagonalLevelGroup R.Pg D.R.r * x * (alternatingSignDiagonalLevelGroup R.Pg D.R.r)⁻¹) := by
    intro x; simp only [t, map_mul, map_inv]
  have ht : ∀ h ∈ F.P0, t * h * t⁻¹ ∈ F.P0 := by
    intro h hh
    obtain ⟨x, rfl⟩ := R.eG.symm.surjective h
    rw [he]; exact hmem x hh
  have hψ : ∀ (h : G) (hh : h ∈ F.P0), F.ψ0 ⟨t * h * t⁻¹, ht h hh⟩ = (F.ψ0 ⟨h, hh⟩)⁻¹ := by
    intro h hh
    obtain ⟨x, rfl⟩ := R.eG.symm.surjective h
    have hs : (⟨t * R.eG.symm x * t⁻¹, ht _ hh⟩ : F.P0) = ⟨_, hmem x hh⟩ := Subtype.ext (he x)
    rw [hs]
    apply Units.ext
    apply D.what₂.embLL.injective
    have hx1 : x ∈ (P0 R.Pg D.R.r ψ').H := (congrArg LevelP.H hlev) ▸ (show x ∈ (R.toRealDat.levR F.lv2 false).H from hh)
    have k1 : Units.map D.what₂.embLL.toMonoidHom (F.ψ0 ⟨_, hmem x hh⟩) =
        (Units.map D.what₂.embLL.toMonoidHom (F.ψ0 ⟨_, hh⟩))⁻¹ :=
      calc Units.map D.what₂.embLL.toMonoidHom (F.ψ0 ⟨_, hmem x hh⟩)
          = (R.toRealDat.levR F.lv2 false).chi ⟨alternatingSignDiagonalLevelGroup R.Pg D.R.r * x * (alternatingSignDiagonalLevelGroup R.Pg D.R.r)⁻¹, hmem x hh⟩ := rfl
        _ = (P0 R.Pg D.R.r ψ').chi ⟨alternatingSignDiagonalLevelGroup R.Pg D.R.r * x * (alternatingSignDiagonalLevelGroup R.Pg D.R.r)⁻¹, alternatingSignDiagonal_conj_mem_genericLevel ψ' hx1⟩ :=
            level_character_eq_of_eq hlev _ _ _
        _ = ((P0 R.Pg D.R.r ψ').chi ⟨x, hx1⟩)⁻¹ := genericLevelCharacter_alternatingSign_conj_inv ψ' hx1
        _ = ((R.toRealDat.levR F.lv2 false).chi ⟨x, hh⟩)⁻¹ := by rw [level_character_eq_of_eq hlev x hh hx1]
        _ = (Units.map D.what₂.embLL.toMonoidHom (F.ψ0 ⟨_, hh⟩))⁻¹ := rfl
    have k3 := congrArg Units.val k1
    simpa [Units.coe_map, Units.val_inv_eq_inv_val, map_inv₀] using k3
  refine GlobalTheory.GoodTypeGeneric.chiIdem_mul_lvlIdem_ne_zero _ _ (hone χ hχ) ?_
  rw [typeSum_inv_eq F.P0 F.ψ0 χ hcls t ht hψ, hsum χ hχ]
  exact hcard

end GlobalTheory.GoodGenericSer

end
