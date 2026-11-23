import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.PrimitivePackageFullHecke
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspidalProductMultiplicity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodFamilyGivenCharactersMultiplicityOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodCharacterPlacewiseCuspidalParabolicProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicityLinearCharacterEqCharacterSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatMuPOfRowTest
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspIndProdCharOfIsProdCuspChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReordEqConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePlacesCardAndResidueLe
open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Cx NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem passIn3_of_rows : ∀ (D : D7) [IsTotallyComplex D.what₂.LL] (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (C CH : ℝ), R.WeakCharacterisation F → A3.fam3.Ok3 1 → PrimRows3 R F → (∀ k : Fin 2, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; ∃ (C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod (D.host.g k))) (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod (D.host.g k)) C), ∀ f, D.ntypes.eSer k f = Formalism.L2.NT.eSerO O D.R.r f) → Formalism.MainNotions.PrimeDegreeVariant.LevelRatioBound D → (R.num F C CH).de = 8 * (D.R.f : ℝ) * (D.R.r : ℝ) / ((min (D.host.g 0) (D.host.g 1) : ℕ) : ℝ) → (R.num F C CH).la = Real.log (Fintype.card G) → PassIn3 R F C CH := by
  intro D _ G _ _ Pl0 I0 T A3 Ks _ _ _ R F C CH hC hOk hP hser hadm hde hla
  classical
  have hlev : R.toRealDat.grp_levels F.lv2 := hC.base.grp.levels
  have hrec : R.toRealDat.grp_record := hC.base.grp.record
  have hirr : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hOk.ok2.irr
  have hind := GlobalTheory.T.goodCharacter_placewise_cuspidal_parabolic_product D G Pl0 T A3.A Ks R.toRealDat hrec hser hirr
  letI i0 : Fintype F.P0 := Fintype.ofFinite _
  letI i1 : Fintype F.P1 := Fintype.ofFinite _
  have hone : ∀ χ ∈ A3.A.X, ∑ h : F.P0, χ (h : G) * (((F.ψ0 h)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) = (Fintype.card F.P0 : D.what₂.LL) :=
    @GlobalTheory.RealOneVector.typeSum_base_eq_card D G _ _ Pl0 T A3.A Ks _ _ _ R.toRealDat F.lv2 hlev hind i0
  obtain ⟨S, iS, Ws, iA, iM, iF, τ, hgood, hchars, hm1⟩ :=
    GlobalTheory.T.exists_goodFamily_given_characters_multiplicityOne D.what₂.LL G A3.A.X hirr F.P0 F.ψ0 hone
  obtain ⟨hcard, hres⟩ := GlobalTheory.typePlaces_card_and_residue_le D G Pl0 T A3.A Ks R.toRealDat hrec
  have hcol := @GlobalTheory.ColumnMultSum.columnMult D G _ _ Pl0 T A3.A Ks _ _ _ R.toRealDat F.lv2 hlev hcard hres hadm hirr hind i1
  refine ⟨S, iS, Ws, iA, iM, iF, τ, (GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.nbar R.Pg D.R.k : ℝ), ?_⟩
  refine ⟨GlobalTheory.ratMuP_of_rowTest D G Pl0 I0 T A3 Ks R F hP.rowTest hP.h2P, hgood, hchars, hm1, ?_, ?_, ?_⟩
  · exact_mod_cast GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.nbar_pos R.Pg D.R.k
  · intro s
    obtain ⟨n, hn, hb⟩ := hcol (Formalism.IndefR.TransferLatticeStatement.charOf (τ s)) ((hchars _).2 ⟨s, rfl⟩)
    have hnOf := GlobalTheory.T.multiplicity_linearCharacter_eq_characterSum D.what₂.LL G (Ws s) (τ s) F.P1 F.ψ1
    have heq : Formalism.IndefR.IndefiniteEpsilonOperator.nOf (τ s) ⟨F.P1, F.ψ1⟩ = n := by
      apply Nat.cast_injective (R := D.what₂.LL)
      rw [hnOf]
      exact hn
    rw [heq]
    have hde' : ((faceOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc (R.toCx3 F).zs).Z.num C CH).de = _ := hde
    rw [hde']
    have := abs_le.1 hb
    constructor <;> nlinarith [this.1, this.2]
  · exact hla

end GlobalTheory
