import Mathlib
import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.GaloisCuspidalOfInput
import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.ExistsFrameOfSig
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ReductionSecondStep
import Formalism.SizeWindowBrackets.ChainSlopeWindows.TruncatedLatticeHolds
import Formalism.SharpRestriction.GlobalSchurBounds.FlipTwoThree
import Formalism.LocalToGlobal.GlobalTheory.GL4.PMuFrames

open Module NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.MainNotions.flipTwoThree Formalism.L2.Herm Formalism.L2.Geo.Def Formalism.L2.Geo.Def.G1
open Formalism.LFunctionChainParameters.slopeLatticeData (FinPl)

def finPlEquiv (K : Type) [Field K] [NumberField K] : FinPl K ≃ HeightOneSpectrum (𝓞 K) where
  toFun := toH
  invFun w := ⟨w.asIdeal, w.isMaximal⟩
  left_inv _ := rfl
  right_inv _ := rfl

section E

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

private lemma hform_crd_lemma (S : HSpace E) (a b : S.V) :
    Formalism.DivisionValues.hform S.gram (crd S a) (crd S b) = S.hT a b := by
  conv_rhs => rw [← S.frame.sum_equivFun a, ← S.frame.sum_equivFun b]
  simp only [Formalism.DivisionValues.hform, Matrix.toLinearMapₛₗ₂'_apply, map_sum, LinearMap.sum_apply,
    LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, crd, HSpace.gram, RingHom.id_apply,
    Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem mem_dual_crdLat (hc : CMData F E) (S : HSpace E) (L : Submodule (𝓞 E) S.V) (x : S.V) :
    crd S x ∈ Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform S.gram) (crdLat S L) ↔ x ∈ dualSub S L := by
  unfold dualSub
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, Submodule.mem_one, crdLat, Submodule.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, LinearEquiv.coe_coe,
    LinearMap.coe_restrictScalars, hform_crd_lemma, Submodule.mem_mk, AddSubmonoid.mem_mk,
    AddSubsemigroup.mem_mk, Set.mem_setOf_eq, RingHom.mem_range]
  exact Iff.rfl

theorem relIndex_crdLat (hc : CMData F E) (S : HSpace E) (L : Submodule (𝓞 E) S.V) :
    (crdLat S L).toAddSubgroup.relIndex (Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform S.gram) (crdLat S L)).toAddSubgroup =
      L.toAddSubgroup.relIndex (dualSub S L) := by
  let f : S.V →+ (Fin S.rank → E) := (crd S).toAddEquiv.toAddMonoidHom
  have hf : Function.Injective f := (crd S).injective
  have hL : (crdLat S L).toAddSubgroup = L.toAddSubgroup.map f := by
    ext z
    exact Iff.rfl
  have hD : (Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform S.gram) (crdLat S L)).toAddSubgroup =
      (dualSub S L).map f := by
    ext z
    obtain ⟨x, rfl⟩ := (crd S).surjective z
    rw [Submodule.mem_toAddSubgroup, mem_dual_crdLat hc S L x]
    constructor
    · intro h
      exact ⟨x, h, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      exact hf hyx ▸ hy
  rw [hD, hL, ← AddSubgroup.relIndex_comap, AddSubgroup.comap_map_eq_self_of_injective hf]

variable [IsTotallyComplex E]

theorem eLat_mu (hc : CMData F E) (S : HSpace E) (hsig : S.SigOK) (hpos : S.IsPosDef) (hn : 0 < S.rank)
    (L : Submodule (𝓞 E) S.V) (hL : Submodule.IsLattice E L) (q : ℕ) (hq : q ≠ 0) (hLT : LatT S q L) :
    muDef (Pi.basisFun E (Fin S.rank)) (fun v => frameOf (S.gram.map v.embedding)) (crdLat S L) =
      -Real.log q / ((finrank ℚ E : ℝ) * S.rank) := by
  have hM := crdLat_lattice S L hL
  have hY : ∀ v : InfinitePlace E, IsUnit (frameOf (S.gram.map v.embedding)).det ∧
      ((frameOf (S.gram.map v.embedding))⁻¹).conjTranspose * (frameOf (S.gram.map v.embedding))⁻¹ = S.gram.map v.embedding := by
    intro v
    apply frameOf_spec
    apply exists_frame_of_sig _ S.rank
    have h1 := hsig v.embedding
    rwa [hpos v.embedding] at h1
  have hCM : Formalism.DivisionValues.IsCMSub (⊤ : Subfield E) := fun σ a _ => hc.cmUnram.2.1 σ a
  have hRat : Formalism.DivisionValues.IsRatHerm (⊤ : Subfield E) S.gram (fun v => frameOf (S.gram.map v.embedding)) :=
    ⟨fun _ _ => Subfield.mem_top _, hY⟩
  obtain ⟨-, h2⟩ := Formalism.DivisionValues.ratHermLcv_of Formalism.DivisionValues.covolume_via_basis Formalism.DivisionValues.index_change_formula
    Formalism.DivisionValues.semilocal_basis_exists E ⊤ hCM S.rank S.gram _ hRat _ hM
  set M := crdLat S L with hMdef
  set Md := Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform S.gram) M with hMd
  have hle : M ≤ Md := by
    intro z hz
    obtain ⟨x, rfl⟩ := (crd S).surjective z
    exact (mem_dual_crdLat hc S L x).2 (hLT.1 x ((crdLat_mem S L x).1 hz))
  have hidx : M.toAddSubgroup.relIndex Md.toAddSubgroup = q := by
    rw [hMd, hMdef, relIndex_crdLat hc S L]; exact hLT.2
  have hjw : ∀ w : HeightOneSpectrum (𝓞 E), (Formalism.DivisionValues.jw S.gram w M : ℝ) = -(Formalism.HermitianLatticesTheory.locLen w.asIdeal Md M : ℝ) := by
    intro w
    unfold Formalism.DivisionValues.jw Formalism.HermitianLatticesTheory.jIdx Formalism.HermitianLatticesTheory.lidx
    rw [← hMd, inf_eq_left.2 hle]
    have h0 : Formalism.HermitianLatticesTheory.locLen w.asIdeal M M = 0 := by
      unfold Formalism.HermitianLatticesTheory.locLen
      rw [Submodule.comap_subtype_self]
      simp
    rw [h0]
    push_cast
    ring
  obtain ⟨-, -, h3⟩ := Formalism.LFunctionChainParameters.LLcv.index_local_length E (Fin S.rank → E) Md M hle (by rw [hidx]; exact hq)
  rw [hidx] at h3
  have hnE : (0 : ℝ) < (finrank ℚ E : ℝ) := by exact_mod_cast (Module.finrank_pos : 0 < finrank ℚ E)
  have h4 : (∑ᶠ w : HeightOneSpectrum (𝓞 E), Formalism.DivisionValues.lw w * (Formalism.DivisionValues.jw S.gram w M : ℝ)) = -(Real.log q / (finrank ℚ E : ℝ)) := by
    rw [h3, ← finsum_comp_equiv (finPlEquiv E), div_eq_mul_inv, ← mul_neg, finsum_mul]
    refine finsum_congr fun p => ?_
    rw [hjw]
    unfold Formalism.DivisionValues.lw
    show Real.log (Ideal.absNorm p.1 : ℝ) / (finrank ℚ E : ℝ) * -(Formalism.HermitianLatticesTheory.locLen (toH p).asIdeal Md M : ℝ) =
      Real.log (Ideal.absNorm p.1 : ℝ) * (Formalism.HermitianLatticesTheory.locLen (toH p).asIdeal Md M : ℝ) * -(finrank ℚ E : ℝ)⁻¹
    ring
  rw [h4, neg_neg] at h2
  have hrk : rkK M = S.rank := by
    show finrank E (Submodule.span E (M : Set (Fin S.rank → E))) = _
    rw [hM.span_eq_top]
    simp
  have h5 := lcv_eq_mu hn _ (fun v => (hY v).1) M hM.fg hrk
  rw [h2] at h5
  have hr : (0 : ℝ) < (S.rank : ℝ) := by exact_mod_cast hn
  field_simp
  field_simp at h5
  linarith

end E

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
