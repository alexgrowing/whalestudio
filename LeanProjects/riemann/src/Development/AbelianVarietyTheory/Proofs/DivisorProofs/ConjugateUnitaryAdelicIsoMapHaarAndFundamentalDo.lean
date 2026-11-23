import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ConjUTransport

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (UB incM incM_smul mt_gram continuous_conj continuous_conjU)

variable {D : D7}

theorem mem_inv (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (hc : c ≠ 0)
    (h : J = c • V.gram) (x : UB J) :
    (GeneralLinearGroup.map (cA D) (show GL (Fin V.rank) (AE D) from x.1) : GL (Fin V.rank) (AE D)) ∈
      HR (AF D.host.F) D.sp.cm.sig V.gram := by
  have e : ((x.1.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).map (cA D)).map (cA D) =
      (x.1.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) :=
    Matrix.ext fun _ _ => Formalism.L2.Theta.cA_cA _
  have hx : (x.1.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))ᵀ * incM J *
      (x.1.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).map (cA D) = incM J := x.2
  show (((x.1.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).map (cA D)).map (cA D))ᵀ * incM V.gram *
    (x.1.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).map (cA D) = incM V.gram
  rw [e]
  generalize (x.1.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) = X at hx ⊢
  rw [h, incM_smul, Matrix.mul_smul, Matrix.smul_mul] at hx
  have hx' := congrArg (fun y => incA D c⁻¹ • y) hx
  simp only [smul_smul, ← map_mul, inv_mul_cancel₀ hc, map_one, one_smul] at hx'
  exact hx'

def conjUInv (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (hc : c ≠ 0)
    (h : J = c • V.gram) (x : UB J) : GA D V :=
  show HR (AF D.host.F) D.sp.cm.sig V.gram from ⟨_, mem_inv V c hc h x⟩

def conjEquiv (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (hc : c ≠ 0)
    (h : J = c • V.gram) : GA D V ≃* UB J where
  toFun := conjU V c h
  invFun := conjUInv V c hc h
  left_inv g := by
    apply Subtype.ext; apply Units.ext; ext i j; exact Formalism.L2.Theta.cA_cA _
  right_inv x := by
    apply Subtype.ext; apply Units.ext; ext i j; exact Formalism.L2.Theta.cA_cA _
  map_mul' a b := by
    apply Subtype.ext; apply Units.ext
    show (mt V (a * b)).map (cA D) = (mt V a).map (cA D) * (mt V b).map (cA D)
    rw [← Matrix.map_mul]
    simp [Formalism.L2.Theta.mt, map_mul]

theorem continuous_conjUInv (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (hc : c ≠ 0)
    (h : J = c • V.gram) : Continuous (conjUInv V c hc h) := by
  have : IsTopologicalRing (AE D) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact (Units.continuous_val.comp continuous_subtype_val).matrix_map (continuous_conj D)
  · exact (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_map (continuous_conj D)

theorem cA_inclR (a : D.host.E) :
    cA D (inclR (F := D.host.F) (AF D.host.F) a) = inclR (F := D.host.F) (AF D.host.F) (D.sp.cm.sig a) := rfl

theorem rat_fwd (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (h : J = c • V.gram)
    (γ : GA D V) (hγ : γ ∈ GQ V) : conjU V c h γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU D.sp.cm.sig J := by
  obtain ⟨y, -, e⟩ := hγ
  refine ⟨GeneralLinearGroup.map (D.sp.cm.sig : D.host.E →+* D.host.E) y, Units.ext ?_⟩
  have e' : mt V γ = (y : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (F := D.host.F) (AF D.host.F)) :=
    (congrArg Units.val e).symm
  show _ = (mt V γ).map (cA D)
  rw [e']
  ext i j
  exact (cA_inclR _).symm

theorem inclR_injective : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) :=
  Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)

theorem rat_inv (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (hc : c ≠ 0)
    (h : J = c • V.gram) (x : UB J) (hx : x ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU D.sp.cm.sig J) : conjUInv V c hc h x ∈ GQ V := by
  obtain ⟨z, hz⟩ := hx
  have hz' : (x.1.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) =
      (z : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (F := D.host.F) (AF D.host.F)) :=
    (congrArg Units.val hz).symm
  set Z := (z : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (D.sp.cm.sig : D.host.E →+* D.host.E) with hZ
  have hY : (x.1.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).map (cA D) =
      Z.map (inclR (F := D.host.F) (AF D.host.F)) := by
    rw [hz']; ext i j; exact cA_inclR _
  refine ⟨GeneralLinearGroup.map (D.sp.cm.sig : D.host.E →+* D.host.E) z, ?_, Units.ext ?_⟩
  · have hm := mem_inv V c hc h x
    change Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) ((x.1.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).map (cA D)) *
      JR (AF D.host.F) V.gram * (x.1.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).map (cA D) = JR (AF D.host.F) V.gram at hm
    rw [hY] at hm
    have hcT : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (Z.map (inclR (F := D.host.F) (AF D.host.F))) =
        (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Z).map (inclR (F := D.host.F) (AF D.host.F)) := by
      ext i j; exact cA_inclR _
    rw [hcT] at hm
    show Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Z * V.gram * Z = V.gram
    apply Matrix.map_injective inclR_injective
    dsimp only
    rw [Matrix.map_mul, Matrix.map_mul]
    exact hm
  · show Z.map (inclR (F := D.host.F) (AF D.host.F)) = (x.1.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).map (cA D)
    exact hY.symm

def ratEquiv (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (hc : c ≠ 0)
    (h : J = c • V.gram) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU D.sp.cm.sig J ≃ GQ V where
  toFun γ := ⟨conjUInv V c hc h γ.1, rat_inv V c hc h γ.1 γ.2⟩
  invFun γ := ⟨conjU V c h γ.1, rat_fwd V c h γ.1 γ.2⟩
  left_inv γ := Subtype.ext ((conjEquiv V c hc h).right_inv γ.1)
  right_inv γ := Subtype.ext ((conjEquiv V c hc h).left_inv γ.1)

theorem map_isHaar_isFundamentalDomain : ∀ {D : D7} (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E), c ≠ 0 →
    ∀ (h : J = c • V.gram) (ν : Measure (GA D V)) (fd : Set (GA D V)), ν.IsHaarMeasure →
    IsFundamentalDomain (GQ V) fd ν →
    (ν.map (conjU V c h)).IsHaarMeasure ∧
      IsFundamentalDomain (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU D.sp.cm.sig J) (conjU V c h '' fd) (ν.map (conjU V c h)) := by
  intro D V J c hc h ν fd hν hfd
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have : IsTopologicalRing (AE D) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing
  have : BorelSpace (UB J) := ⟨rfl⟩
  let φ := conjEquiv V c hc h
  have c1 : Continuous φ := continuous_conjU V c h
  have c2 : Continuous φ.symm := continuous_conjUInv V c hc h
  have hH : (ν.map φ).IsHaarMeasure := MulEquiv.isHaarMeasure_map ν φ c1 c2
  refine ⟨hH, ?_⟩
  let H : GA D V ≃ₜ UB J := ⟨φ.toEquiv, c1, c2⟩
  let M := H.toMeasurableEquiv
  have hq : Measure.QuasiMeasurePreserving M.symm (ν.map M) ν :=
    (M.measurePreserving_symm ν).quasiMeasurePreserving
  refine hfd.image_of_equiv M.toEquiv hq (ratEquiv V c hc h) fun γ x => ?_
  show φ (φ.symm γ.1 * x) = γ.1 * φ x
  rw [map_mul, MulEquiv.apply_symm_apply]

end GlobalTheory.ConjUTransport
