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

namespace GlobalTheory.HaarConj

variable {D : D7}

theorem isFundamentalDomain_image {G H : Type} [Group G] [Group H] [MeasurableSpace G] [MeasurableSpace H]
    (φ : G ≃* H) (hc : Measurable φ) (hc' : Measurable φ.symm) (Γ : Subgroup G) (Γ' : Subgroup H)
    (hQ : ∀ g, g ∈ Γ ↔ φ g ∈ Γ') (μ : Measure G) (𝓕 : Set G) (h : IsFundamentalDomain Γ 𝓕 μ) :
    IsFundamentalDomain Γ' (φ '' 𝓕) (μ.map φ) := by
  let ψ : G ≃ᵐ H := ⟨φ.toEquiv, hc, hc'⟩
  have hψ : MeasurePreserving ψ μ (μ.map φ) := ⟨ψ.measurable, rfl⟩
  have e : φ '' 𝓕 = φ.symm ⁻¹' 𝓕 := φ.toEquiv.image_eq_preimage_symm 𝓕
  rw [e]
  exact h.preimage_of_equiv (f := φ.symm) (MeasurePreserving.symm ψ hψ).quasiMeasurePreserving
    (e := fun γ => ⟨φ γ, (hQ γ).1 γ.2⟩)
    ⟨fun a b hab => Subtype.ext (φ.injective (congrArg Subtype.val hab)),
      fun b => ⟨⟨φ.symm b, (hQ _).2 (by simp)⟩, Subtype.ext (by simp)⟩⟩
    fun γ y => by
      show φ.symm (φ γ * y) = γ * φ.symm y
      rw [map_mul, φ.symm_apply_apply]

theorem cA_incA (e : D.host.E) : cA D (incA D e) = incA D (D.sp.cm.sig e) := by
  simp [cA, sigR, incA, inclR, Algebra.TensorProduct.map_tmul]

theorem incA_inj : Function.Injective (incA D) :=
  Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (R := 𝓞 D.host.F) (K := D.host.F))

def conjInv (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (hc : c ≠ 0)
    (h : J = c • V.gram) (u : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J) : GA D V :=
  ⟨GeneralLinearGroup.map (cA D) u.1, by
    have hu : u.1.1ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J * u.1.1.map (cA D) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J := u.2
    have e : (u.1.1.map (cA D)).map (cA D) = u.1.1 := Matrix.ext fun _ _ => cA_cA _
    show Formalism.UG.cT (cA D) (u.1.1.map (cA D)) * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM V.gram * u.1.1.map (cA D)
      = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM V.gram
    rw [Formalism.UG.cT, e]
    generalize u.1.1 = M at hu ⊢
    rw [h, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul, Matrix.mul_smul, Matrix.smul_mul] at hu
    have k : incA D c⁻¹ * incA D c = 1 := by rw [← map_mul, inv_mul_cancel₀ hc, map_one]
    have := congrArg (incA D c⁻¹ • ·) hu
    simpa only [smul_smul, k, one_smul] using this⟩

def conjE (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (hc : c ≠ 0)
    (h : J = c • V.gram) : GA D V ≃* GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J where
  toFun := conjU V c h
  invFun := conjInv V c hc h
  left_inv g := Subtype.ext (Units.ext (Matrix.ext fun _ _ => cA_cA _))
  right_inv u := Subtype.ext (Units.ext (Matrix.ext fun _ _ => cA_cA _))
  map_mul' a b := Subtype.ext (by
    show GeneralLinearGroup.map (cA D) (matHom V (a * b)) = GeneralLinearGroup.map (cA D) (matHom V a) *
      GeneralLinearGroup.map (cA D) (matHom V b)
    rw [map_mul, map_mul])

theorem continuous_conjInv (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (hc : c ≠ 0)
    (h : J = c • V.gram) : Continuous (conjInv V c hc h) := by
  have h1 : Continuous (fun u : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J => u.1) := continuous_subtype_val
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact (Units.continuous_val.comp h1).matrix_map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conj D)
  · exact (Units.continuous_coe_inv.comp h1).matrix_map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conj D)

theorem mem_ratU_iff (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (hc : c ≠ 0)
    (h : J = c • V.gram) (g : GA D V) :
    g ∈ GQ V ↔ conjE V c hc h g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU D.sp.cm.sig J := by
  have hg : Formalism.UG.cT (cA D) g.1.1 * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM V.gram * g.1.1 = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM V.gram := g.2
  constructor
  · intro hq
    obtain ⟨x, -, hx⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hq)
    refine Subgroup.mem_subgroupOf.2 ⟨GeneralLinearGroup.map (D.sp.cm.sig : D.host.E →+* D.host.E) x, ?_⟩
    refine Units.ext (Matrix.ext fun i j => ?_)
    have := congrArg (fun y : GL (Fin V.rank) (AE D) => y.1 i j) hx
    show incA D (D.sp.cm.sig (x.1 i j)) = cA D (g.1.1 i j)
    rw [← this, ← cA_incA]
    rfl
  · intro hq
    obtain ⟨w, hw⟩ := Subgroup.mem_subgroupOf.1 hq
    have hw' : ∀ i j, incA D (w.1 i j) = cA D (g.1.1 i j) := fun i j =>
      congrArg (fun y : GL (Fin V.rank) (AE D) => y.1 i j) hw
    have hx : ∀ i j, incA D (D.sp.cm.sig (w.1 i j)) = g.1.1 i j := fun i j => by
      rw [← cA_incA, hw', cA_cA]
    let x := GeneralLinearGroup.map (D.sp.cm.sig : D.host.E →+* D.host.E) w
    have hxm : x.1.map (incA D) = g.1.1 := Matrix.ext fun i j => hx i j
    refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨x, ?_, Units.ext (Matrix.ext fun i j => hx i j)⟩)
    show Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) x.1 * V.gram * x.1 = V.gram
    have key : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) x.1 * V.gram * x.1).map (incA D) =
        V.gram.map (incA D) := by
      rw [Matrix.map_mul, Matrix.map_mul, hxm]
      have e1 : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) x.1).map (incA D) = Formalism.UG.cT (cA D) g.1.1 := by
        rw [← hxm]
        ext i j
        simp only [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply]
        exact (cA_incA _).symm
      rw [e1]
      exact hg
    exact Matrix.ext fun i j => incA_inj (congrFun (congrFun key i) j)

theorem haarConj : ∀ {D : D7} (V : HSp D) (c : D.host.E), c ≠ 0 → ∀ {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (hJ : J = c • V.gram)
    (ν : Measure (GA D V)) (fd : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) fd ν →
    ∃ dom : Set (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J), (ν.map (conjU V c hJ)).IsHaarMeasure ∧
      IsFundamentalDomain (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU D.sp.cm.sig J) dom (ν.map (conjU V c hJ)) := by
  intro D V c hc J hJ ν fd hν hfd
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have : BorelSpace (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J) := ⟨rfl⟩
  have c1 : Continuous (conjE V c hc hJ) := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conjU V c hJ
  have c2 : Continuous (conjE V c hc hJ).symm := continuous_conjInv V c hc hJ
  exact ⟨conjE V c hc hJ '' fd, MulEquiv.isHaarMeasure_map ν (conjE V c hc hJ) c1 c2,
    isFundamentalDomain_image (conjE V c hc hJ) c1.measurable c2.measurable (GQ V) _ (mem_ratU_iff V c hc hJ) ν fd hfd⟩

end GlobalTheory.HaarConj
