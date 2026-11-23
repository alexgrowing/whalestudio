import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsDeco
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CastGLSymmCastGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryFiniteAdelicPointAsMatrixMemFlagIwahori
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RTupQEqOneIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormLevelPrimesIsSplitSet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvReductionMulFlagTranslationMemRowLevelGroupStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowLevelCharacterTranslationEqFlagCharacterStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivRowStageUnitaryStandardAdelicStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRationalUnitaryEquivRowStageCompatStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemRowLevelOfReductionMemLevelGroupStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.RowStdPres

open Formalism.IndefR.Bridge

section Generic

variable {Xf : Formalism.L2.Col.Fields} {n : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 Xf.E))} (Λ : Formalism.L2.Col.LevFam Xf.E Xf.K n SG)

theorem mem_grp_of_inv_mul (a b : Formalism.L2.Col.GLG Xf.E n SG) (hb : b = 1) (hu : a⁻¹ * b ∈ Λ.grp) : a ∈ Λ.grp := by
  subst hb
  rw [mul_one] at hu
  exact (Subgroup.inv_mem_iff _).1 hu

theorem inv_mul_mem_grp (a b : Formalism.L2.Col.GLG Xf.E n SG) (hb : b = 1) (ha : a ∈ Λ.grp) : a⁻¹ * b ∈ Λ.grp := by
  subst hb
  rw [mul_one]
  exact Λ.grp.inv_mem ha

theorem chr_of_inv_mul (σ : Xf.K →+* ℂ) (a b : Formalism.L2.Col.GLG Xf.E n SG) (hb : b = 1) (ha : a ∈ Λ.grp) (hu : a⁻¹ * b ∈ Λ.grp)
    (z : ℂˣ) (hz : σ ((Λ.chr ⟨_, hu⟩ : Xf.Kˣ) : Xf.K) = (z : ℂ)) :
    σ ((Λ.chr ⟨a, ha⟩ : Xf.Kˣ) : Xf.K) = ((z⁻¹ : ℂˣ) : ℂ) := by
  subst hb
  have e : (⟨a⁻¹ * 1, hu⟩ : Λ.grp) = (⟨a, ha⟩ : Λ.grp)⁻¹ := Subtype.ext (mul_one _)
  rw [e, map_inv, Units.val_inv_eq_inv_val, map_inv₀] at hz
  rw [Units.val_inv_eq_inv_val, ← hz, inv_inv]

variable [NeZero n] (hc : Formalism.BasicNotions.CMData Xf.F Xf.E)

theorem character_trivial_on_reduction_kernel (σ : Xf.K →+* ℂ) (k : colJ hc n ∅ SG Λ.grp) (hk : (k : Formalism.L2.Col.UAd hc n) ∈ principalCongruenceSubgroup hc n ∅ SG) :
    σ ((Λ.chr (Formalism.L2.Col.redH hc n ∅ SG Λ.grp ((colJEquiv hc n ∅ SG Λ.grp).symm k)) : Xf.Kˣ) : Xf.K) = 1 := by
  rw [← colJEquiv_symm_coe, mem_principal_congruence_iff] at hk
  have hr : Formalism.L2.Col.redH hc n ∅ SG Λ.grp ((colJEquiv hc n ∅ SG Λ.grp).symm k) = 1 := Subtype.ext hk
  rw [hr, map_one, Units.val_one, map_one]

theorem formRho_colGl (C : Formalism.L2.Col.CoefPk Xf n (Formalism.L2.Col.DecoSet Xf.E n ∅ SG))
    (γ : Formalism.L2.Col.URat hc n) (k : colJ hc n ∅ SG Λ.grp) (v : C.V) :
    (Formalism.L2.Col.formGSD C Λ).ρ (colGl (Formalism.L2.Col.rf_onDeco C Λ) (γ, k)) v =
      ((Λ.chr (Formalism.L2.Col.redH hc n ∅ SG Λ.grp ((colJEquiv hc n ∅ SG Λ.grp).symm k)) : Xf.Kˣ) : Xf.K) •
        C.rho (Formalism.L2.Col.ratHom hc n γ) v := rfl

end Generic

set_option maxHeartbeats 1000000 in

theorem standard_level_element_hat_eq_one (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r) (t : TupU I U)
    (k : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J) :
    Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_X' X.B.R)
                (eG.symm (rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((k : Bridge.Gf X.toD7.sp.X') : GL _ _)))) = 1 := by
  have h1 : rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((k : Bridge.Gf X.toD7.sp.X') : GL _ _)) = 1 :=
    (RowAct.rTupQ_eq_one_iff X.toD7.sp.X' L.βX (L.datXt t) ⟨k.1, (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J_le k.2⟩).2 k.2
  have h2 : eG.symm (rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((k : Bridge.Gf X.toD7.sp.X') : GL _ _))) = 1 :=
    (congrArg eG.symm h1).trans (map_one eG.symm)
  exact (congrArg (Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_X' X.B.R)) h2).trans (map_one _)

set_option maxHeartbeats 1000000 in

theorem deco_surj (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hI : I.Ok) (hL : LevOf X I U L) (t : TupU I U) :
    Formalism.L2.Col.DecoPtSurj X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) :=
  Formalism.L2.Col.decoPtSurj_of _ _ _ _ (Formalism.L2.Col.unimodGenus_holds _ _) Formalism.L2.DIV.reduction_surjective_bis
    (by classical convert GlobalTheory.Mem.R3.LiftBrg.isSplitSet_sgL X px I U L hI hL t using 1; exact Finset.empty_union _)
    (Finset.disjoint_empty_left _)

set_option maxHeartbeats 1000000 in

theorem lev_iff (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r) (hI : I.Ok) (hL : LevOf X I U L)
    (hG : IsPlacewiseIdentity X (px := px) eG) (t : TupU I U) (h : Bridge.Gf X.toD7.sp.X') :
      h ∈ (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J ↔
        ∃ hz : RowAd.ptE X h ∈ Formalism.L2.Col.J0 X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅,
          Formalism.L2.Col.redG X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ⟨_, hz⟩ ∈
            ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp := by
  constructor
  · intro hh
    have hz := RowDeco.unitaryFiniteAdelicPointAsMatrix_mem_flagIwahori X I hI L hL t ⟨h, (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J_le hh⟩
    exact ⟨hz, mem_grp_of_inv_mul (Xf := X.B.fields) (Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv _ _
      (standard_level_element_hat_eq_one X px I U L eG t ⟨h, hh⟩)
      (GlobalTheory.T.inv_reduction_mul_flagTranslation_mem_rowLevelGroup X px I U L eG hI hL hG t ⟨h, (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J_le hh⟩ hz)⟩
  · rintro ⟨hz, hg⟩
    exact GlobalTheory.T.mem_rowLevel_of_reduction_mem_levelGroup X px I U L hI hL t h hz hg

set_option maxHeartbeats 1000000 in

theorem chi_eq : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r),
    I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG →
    ∀ (t : TupU I U) (k : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J)
      (hz : RowAd.ptE X (k : Bridge.Gf X.toD7.sp.X') ∈ Formalism.L2.Col.J0 X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅)
      (hg : Formalism.L2.Col.redG X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ⟨_, hz⟩ ∈
            ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp),
      X.toD7.what₂.embLL (((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv.chr ⟨_, hg⟩ : X.B.fields.Kˣ) : X.B.fields.K) =
        ((((levEnv X.toD7.sp.X' L.βX (L.datXt t)).χ k)⁻¹ : ℂˣ) : ℂ) := by
  intro X px I U L eG hI hV hL hG t k hz hg
  have hb := standard_level_element_hat_eq_one X px I U L eG t k
  have hu := inv_mul_mem_grp (Xf := X.B.fields) (Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv _ _ hb hg
  have h1 := GlobalTheory.T.rowLevelCharacter_translation_eq_flagCharacter X px I U L eG hI hV hL hG t ⟨k.1, (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J_le k.2⟩ hz hu
  exact chr_of_inv_mul (Xf := X.B.fields) (Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv X.B.embLL _ _ hb hg hu _
    (h1.trans (congrArg Units.val ((levEnv X.toD7.sp.X' L.βX (L.datXt t)).ch_J k)))

set_option maxHeartbeats 1000000 in

theorem lev_eq_map (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r) (hI : I.Ok) (hL : LevOf X I U L)
    (hG : IsPlacewiseIdentity X (px := px) eG) (t : TupU I U)
    (e : Formalism.L2.Col.UAd X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ≃* Bridge.Gf X.toD7.sp.X') (he : ∀ x, RowAd.ptE X (e x) = x.1) :
    (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J =
      (colJ X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1)
        ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp).map e.toMonoidHom := by
  ext h
  rw [lev_iff X px I U L eG hI hL hG t h]
  constructor
  · rintro ⟨hz, hg⟩
    have e1 : RowAd.ptE X h = (e.symm h).1 := by
      have := he (e.symm h)
      rwa [MulEquiv.apply_symm_apply] at this
    refine ⟨e.symm h, ⟨⟨RowAd.ptE X h, hz⟩, hg, Subtype.ext e1⟩, by simp⟩
  · rintro ⟨x, ⟨m, hm, rfl⟩, rfl⟩
    have e1 : RowAd.ptE X (e (Formalism.L2.Col.ToUnitaryAdelic X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ m)) = m.1 := he _
    have hz : RowAd.ptE X (e (Formalism.L2.Col.ToUnitaryAdelic X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ m)) ∈
        Formalism.L2.Col.J0 X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ := by
      rw [e1]; exact m.2
    refine ⟨hz, ?_⟩
    have e2 : (⟨_, hz⟩ : Formalism.L2.Col.J0 X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅) = m := Subtype.ext e1
    exact (congrArg (fun z => Formalism.L2.Col.redG X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) z ∈
      ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp) e2).mpr hm

def levE {G G' : Type} [Group G] [Group G'] (e : G ≃* G') (J : Subgroup G) (J' : Subgroup G') (hJ : J' = J.map e.toMonoidHom) :
    J ≃* J' :=
  (J.equivMapOfInjective e.toMonoidHom e.injective).trans (MulEquiv.subgroupCongr hJ.symm)

theorem levE_coe {G G' : Type} [Group G] [Group G'] (e : G ≃* G') (J : Subgroup G) (J' : Subgroup G')
    (hJ : J' = J.map e.toMonoidHom) (k : J) : ((levE e J J' hJ k : J') : G') = e k := rfl

set_option maxHeartbeats 4000000 in

theorem exists_pres : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → L.βX = 1 → ∀ (cX : CoefA X.toD7.sp.X') (c : VV X.B.fields.K X.B.wts.sgTrue →ₛₗ[X.B.embLL] cX.W), (∀ (γ : GQ X.toD7.sp.X') (γE : GL (Fin X.toD7.sp.X'.rank) X.toD7.host.E) (g : GL (Fin (X.B.R.N X.B.R.m - 1)) X.B.fields.E), Bridge.IsRatMat X.toD7.sp.X' γ γE → MatEq γE g → ∀ v, c (rhoV X.B.fields.emb X.B.wts.sgTrue g v) = cX.coef.ρ γ (c v)) → LinearIndependent ℂ (fun i => c (bVV X.B.fields.K X.B.wts.sgTrue i)) → Submodule.span ℂ (Set.range fun i => c (bVV X.B.fields.K X.B.wts.sgTrue i)) = ⊤ → (∀ x y, inner ℂ (c x) (c y) = X.B.embLL (pairV X.B.fields.emb X.B.wts.sgTrue 1 x y)) → ∀ t, ∃ P : Bridge.ClassPres (Bridge.ratF X.toD7.sp.X') ((famR X I hX U Xg tr).A.MtildeCSD t) X.toD7.what₂.embLL cX.coef.ρ (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J (levEnv X.toD7.sp.X' L.βX (L.datXt t)).χ, (∀ x, P.coef x = c x) ∧ (∀ c', RowAd.decoAd X I t (P.y c') = (Formalism.L2.Col.mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1).outSec.rep c') ∧ ∀ (f : ((famR X I hX U Xg tr).A.MtildeCSD t).Forms) (h : Bridge.Gf X.toD7.sp.X'), P.ext (f : _ → _) h = c ((((Formalism.L2.Col.mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1).res (Formalism.L2.Col.mtildeKOk _ _ _ _ hX)).symm f).1 (RowAd.decoAd X I t h)) := by
  intro X px I hX U Xg tr L eG hI hV hL hG hβ cX c hint hli hspan hpair t
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_equiv_rowStage_unitary_standard_adelic X px I hI
  obtain ⟨eΓ, hι, hrat⟩ := GlobalTheory.T.exists_rational_unitary_equiv_rowStage_compat X px I hI e he
  have hS := deco_surj X px I U L hI hL t
  have hJ := lev_eq_map X px I U L eG hI hL hG t e he
  let χ' : colJ X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1)
        ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp →* ℂˣ :=
    (levEnv X.toD7.sp.X' L.βX (L.datXt t)).χ.comp (levE e _ _ hJ).toMonoidHom
  let coef : (Formalism.L2.Col.mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1).V →ₛₗ[X.B.embLL] cX.W := c
  have hchar : ∀ k : colJ X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp,
      X.B.embLL (((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv.chr
        (Formalism.L2.Col.redH X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp ((colJEquiv X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp).symm k)) : X.B.fields.Kˣ) : X.B.fields.K) =
        (((χ' k)⁻¹ : ℂˣ) : ℂ) := by
    intro k
    have e1 : RowAd.ptE X ((levE e _ _ hJ k : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J) : Bridge.Gf X.toD7.sp.X') =
        ((((colJEquiv X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp).symm k : Formalism.L2.Col.JH X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp) : Formalism.L2.Col.J0 X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅) :
          GL (Fin (X.B.R.N X.B.R.m - 1)) (X.toD7.host.E ⊗[↥X.toD7.host.F] Formalism.L2.Herm.Af ↥X.toD7.host.F)) := by
      rw [levE_coe, he]
      exact congrArg Subtype.val (colJEquiv_symm_coe X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp k).symm
    have hz : RowAd.ptE X ((levE e _ _ hJ k : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J) : Bridge.Gf X.toD7.sp.X') ∈
        Formalism.L2.Col.J0 X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ := by
      rw [e1]; exact (((colJEquiv X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp).symm k : Formalism.L2.Col.JH X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp) : Formalism.L2.Col.J0 X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅).2
    have e2 : (⟨_, hz⟩ : Formalism.L2.Col.J0 X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅) =
        (((colJEquiv X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp).symm k : Formalism.L2.Col.JH X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp) : Formalism.L2.Col.J0 X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅) :=
      Subtype.ext e1
    have hg : Formalism.L2.Col.redG X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ⟨_, hz⟩ ∈ ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp := by
      rw [e2]; exact ((colJEquiv X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp).symm k).2
    have h3 := chi_eq X px I U L eG hI hV hL hG t (levE e _ _ hJ k) hz hg
    have e3 : Formalism.L2.Col.redH X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp ((colJEquiv X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp).symm k) = ⟨_, hg⟩ :=
      Subtype.ext (congrArg (Formalism.L2.Col.redG X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1)) e2.symm)
    rw [e3]
    exact h3
  have hK1 : ∀ k : colJ X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp,
      (k : Formalism.L2.Col.UAd X.toD7.sp.cm (X.B.R.N X.B.R.m - 1)) ∈ principalCongruenceSubgroup X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) → χ' k = 1 := by
    intro k hk
    have h4 := (hchar k).symm.trans (character_trivial_on_reduction_kernel (Xf := X.B.fields) (Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv
      X.toD7.sp.cm X.B.embLL k hk)
    have h5 : (χ' k)⁻¹ = 1 := Units.ext h4
    exact inv_eq_one.mp h5
  have hgl : ∀ (γ : Formalism.L2.Col.URat X.toD7.sp.cm (X.B.R.N X.B.R.m - 1))
      (k : colJ X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1)
        ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp)
      (v : (Formalism.L2.Col.mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1).V),
      coef ((Formalism.L2.Col.mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1).ρ
      (colGl (hc := X.toD7.sp.cm) (Formalism.L2.Col.rf_onDeco (Formalism.L2.Col.rowVal (Pr := X.B.primes px) X.B.wts (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1))
        (Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv) (γ, k)) v) =
      ((χ' k)⁻¹ : ℂˣ) • (cX.coef.ρ.comp eΓ.toMonoidHom) γ (coef v) := by
    intro γ k v
    refine (congrArg coef (formRho_colGl (Xf := X.B.fields) (Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv X.toD7.sp.cm
      (Formalism.L2.Col.rowVal (Pr := X.B.primes px) X.B.wts (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1)) γ k v)).trans ?_
    refine (c.map_smulₛₗ _ _).trans ?_
    obtain ⟨γE, hr, hm⟩ := hrat γ
    have e3 : (Formalism.L2.Col.rowVal (Pr := X.B.primes px) X.B.wts (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1)).rho (Formalism.L2.Col.ratHom X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) γ) v =
        rhoV X.B.fields.emb X.B.wts.sgTrue γ.1 v :=
      congrArg (fun g => rhoV X.B.fields.emb X.B.wts.sgTrue g v) (LiftPres.ufGL_ratHom X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) γ)
    have e4 := (congrArg c e3).trans (hint (eΓ γ) γE γ.1 hr hm v)
    exact congrArg₂ (fun (a : ℂ) (w : cX.W) => a • w) (hchar k) e4
  let P0 := colClassPres (F := ↥X.toD7.host.F) (E := X.toD7.host.E) (hc := X.toD7.sp.cm) (Formalism.L2.Col.rf_onDeco (Formalism.L2.Col.rowVal (Pr := X.B.primes px) X.B.wts (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1))
        (Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv) hS
      (Formalism.L2.Col.mtildeKOk (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1 hX) X.B.embLL
      (cX.coef.ρ.comp eΓ.toMonoidHom) χ' coef hli hspan hpair hK1 hgl
  have hq : ∀ x : Formalism.L2.Col.UAd X.toD7.sp.cm (X.B.R.N X.B.R.m - 1),
      colQ (hc := X.toD7.sp.cm) (Formalism.L2.Col.rf_onDeco (Formalism.L2.Col.rowVal (Pr := X.B.primes px) X.B.wts (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1))
        (Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv) x = RowAd.decoAd X I t (e x) := by
    intro x
    refine (Formalism.L2.Col.decoPt_mk (F := ↥X.toD7.host.F) (E := X.toD7.host.E) X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅
      (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) x).trans ?_
    unfold RowAd.decoAd
    rw [he]
    rfl
  have hχ : ∀ (k : colJ X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1)
        ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp) (hk : e k ∈ (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J),
      (levEnv X.toD7.sp.X' L.βX (L.datXt t)).χ ⟨e k, hk⟩ = χ' k := fun k hk => rfl
  have hρ : ∀ γ, cX.coef.ρ (eΓ γ) = (cX.coef.ρ.comp eΓ.toMonoidHom) γ := fun _ => rfl
  refine ⟨P0.transport e eΓ hι hρ hJ hχ, fun x => rfl, ?_, ?_⟩
  · intro c'
    exact (hq _).symm.trans ((colAdPts (hc := X.toD7.sp.cm) (Formalism.L2.Col.rf_onDeco (Formalism.L2.Col.rowVal (Pr := X.B.primes px) X.B.wts (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1))
        (Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv) hS).q_y c')
  · intro f h
    have h1 := GlobalTheory.Mem.R3.LiftPres.transport_ext P0 e eΓ hι hρ hJ hχ f (e.symm h)
    rw [MulEquiv.apply_symm_apply] at h1
    refine h1.trans ?_
    refine (GlobalTheory.Mem.R3.LiftPres.classPresOf_ext (colAdPts (hc := X.toD7.sp.cm) (Formalism.L2.Col.rf_onDeco (Formalism.L2.Col.rowVal (Pr := X.B.primes px) X.B.wts (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1))
        (Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv) hS) _ _ _ _ coef hli hspan hpair hK1 hgl f
      (e.symm h)).trans ?_
    have h2 : (colAdPts (hc := X.toD7.sp.cm) (Formalism.L2.Col.rf_onDeco (Formalism.L2.Col.rowVal (Pr := X.B.primes px) X.B.wts (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1))
        (Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv) hS).q (e.symm h) = RowAd.decoAd X I t h :=
      (hq _).trans (by rw [MulEquiv.apply_symm_apply])
    rw [h2]
    rfl

end GlobalTheory.Mem.R3.RowStdPres
