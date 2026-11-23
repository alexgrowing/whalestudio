import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsHomOpenPart
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ImmByOfSpans
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjBundleClosureStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsInvertibleMatrixChangeOfSpanEq
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsHomSpecOfLeRingOnStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFunctionFieldOfIsDominantStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DivIffMemNonzeroLocusStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClosedImmersionBaseChangeProjChartStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsLBGenTrivOfRatiosStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericTrivialisationSectionAndPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsClosedImmersionOfCoordinateDivisibilityStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsPullbackOfProjChartStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomogeneousCoordinatesMulVecOfGenericValueStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH
open GlobalTheory.Points
namespace RatModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}
  {Ω' : Type} [Field Ω'] [Algebra o Ω'] {φ : Ω →ₐ[o] Ω'}

theorem ProjChart.closure_eq_top {N : RatModel o Ω'} {q : N.Z ⟶ M.Z} (hq : M.IsHom N φ q) {W : M.Z.Opens}
    (hW : (W : Set M.Z).Nonempty) {J : Type} {t : J → Ω'} (h : M.ProjChart N φ q W t) :
    (∃ j, t j ≠ 0) ∧ Subfield.closure (Set.range φ ∪ {x | ∃ i j, x = t j / t i}) = ⊤ := by
  have hg : q (genericPoint N.Z) ∈ W := by
    have h1 : ⊤ ≤ (N.pt ≫ q) ⁻¹ᵁ W := by
      rw [hq]
      exact le_preimage_comp _ _ (M.top_le_preimage_pt hW) (le_preimage_top _)
    rw [← N.pt_apply (IsLocalRing.closedPoint Ω')]
    exact h1 (x := IsLocalRing.closedPoint Ω') trivial
  obtain ⟨i, hi⟩ := h.1 _ hg
  obtain ⟨U, hU, hD, hR⟩ := h.2 i hi.1
  have hne : (U : Set N.Z).Nonempty := ⟨genericPoint N.Z, hD ▸ ⟨hg, hi⟩⟩
  refine ⟨⟨i, hi.1⟩, top_unique fun x _ => ?_⟩
  have key : ∀ a : Γ(N.Z, U), valF N.pt U a ∈ Subfield.closure (Set.range φ ∪ {x | ∃ i j, x = t j / t i}) := by
    intro a
    have ha : valF N.pt U a ∈ N.ringOn U := (mem_ringOn_iff_exists hne).2 ⟨a, rfl⟩
    rw [hR] at ha
    generalize valF N.pt U a = y at ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with ⟨y, -, rfl⟩ | ⟨j, rfl⟩
      · exact Subfield.subset_closure (Or.inl ⟨y, rfl⟩)
      · exact Subfield.subset_closure (Or.inr ⟨i, j, rfl⟩)
    | algebraMap r => exact Subfield.subset_closure (Or.inl ⟨_, φ.commutes r⟩)
    | add _ _ _ _ h1 h2 => exact add_mem h1 h2
    | mul _ _ _ _ h1 h2 => exact mul_mem h1 h2
  obtain ⟨a, b, -, rfl⟩ := exists_eq_div hU hne x
  exact div_mem (key a) (key b)

theorem IsHom.genericPoint_mem {N : RatModel o Ω'} {q : N.Z ⟶ M.Z} (hq : M.IsHom N φ q) {W : M.Z.Opens}
    (hW : (W : Set M.Z).Nonempty) : q (genericPoint N.Z) ∈ W := by
  have h1 : ⊤ ≤ (N.pt ≫ q) ⁻¹ᵁ W := by
    rw [hq]
    exact le_preimage_comp _ _ (M.top_le_preimage_pt hW) (le_preimage_top _)
  rw [← N.pt_apply (IsLocalRing.closedPoint Ω')]
  exact h1 (x := IsLocalRing.closedPoint Ω') trivial

theorem IsHom.mulVec_div_mem {N : RatModel o Ω'} {q : N.Z ⟶ M.Z} (hq : M.IsHom N φ q) {J : Type} [Fintype J]
    {u : J → Ω'} {i : J} {z : N.Z} (h : N.Div u i z) {m : Matrix J J Ω} (hm : ∀ j k, m j k ∈ M.O (q z)) (j : J) :
    (m.map φ).mulVec u j / u i ∈ N.O z := by
  simp only [Matrix.mulVec, dotProduct, Finset.sum_div, mul_div_assoc, Matrix.map_apply]
  exact Subalgebra.sum_mem _ fun k _ => mul_mem (hq.map_mem_O (hm j k)) (h.2 k)

structure Lat.Frame {J : Type} [Fintype J] (EE : M.Lat J) where
  W : M.Z.Opens
  aff : IsAffineOpen W
  ne : (W : Set M.Z).Nonempty
  B : Matrix J J Ω
  basis : ∀ z ∈ W, EE.E z = Submodule.span (M.O z) (Set.range B)
  c : Matrix J J Γ(M.Z, W)
  c_inv : c.map (valF M.pt W) * B = 1

theorem Lat.exists_frame {J : Type} [Fintype J] (EE : M.Lat J) (hm : ∀ z i, Pi.single i (1 : Ω) ∈ EE.E z)
    (z : M.Z) : ∃ l : EE.Frame, z ∈ l.W := by
  obtain ⟨U, b, hz, hb, h⟩ := EE.loc z
  obtain ⟨W, hW, hzW, hle⟩ := exists_isAffineOpen_mem_and_subset hz
  have hu : IsUnit b.det := hb.isUnit
  obtain ⟨c, hc⟩ := M.exists_matrix_map_valF (U := W) ⟨z, hzW⟩ b⁻¹ fun w hw i j => by
    have := mul_inv_apply_mem_of_span_le (M.O w) (b := 1) (B := b) (c := b⁻¹) (Submodule.span_le.2 (by
      rintro _ ⟨i, rfl⟩
      rw [← h w (hle hw)]
      have e : (1 : Matrix J J Ω) i = Pi.single i 1 := by
        ext j
        simp [Matrix.one_apply, Pi.single_apply, eq_comm]
      rw [e]
      exact hm w i)) (Matrix.mul_nonsing_inv b hu) i j
    rwa [Matrix.one_mul] at this
  refine ⟨⟨W, hW, ⟨z, hzW⟩, b, fun w hw => h w (hle hw), c, ?_⟩, hzW⟩
  rw [← Matrix.nonsing_inv_mul b hu, ← hc]
  congr 1
  ext i j
  exact (M.res_apply W ⟨z, hzW⟩ (c i j)).symm

def Lat.stdFrame {J : Type} [Fintype J] (EE : M.Lat J) {W : M.Z.Opens} (hW : IsAffineOpen W)
    (hne : (W : Set M.Z).Nonempty)
    (h : ∀ z ∈ W, EE.E z = Submodule.span (M.O z) (Set.range fun i => Pi.single i (1 : Ω))) : EE.Frame where
  W := W
  aff := hW
  ne := hne
  B := 1
  basis z hz := by
    rw [h z hz]
    congr 2
    ext i j
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  c := 1
  c_inv := by
    rw [Matrix.mul_one]
    exact Matrix.map_one _ (valR_zero _ _ (M.top_le_preimage_pt hne)) (valR_one _ _ (M.top_le_preimage_pt hne))

namespace Lat.Frame
variable {J : Type} [Fintype J] {EE : M.Lat J}

abbrev co (l : EE.Frame) (φ : Ω →ₐ[o] Ω') (t : J → Ω') : J → Ω' := (l.B.map φ).mulVec t

theorem eq_mulVec (l : EE.Frame) (t : J → Ω') :
    t = ((l.c.map (valF M.pt l.W)).map φ).mulVec (l.co φ t) := by
  rw [Matrix.mulVec_mulVec, ← Matrix.map_mul (f := φ), l.c_inv, Matrix.map_one _ (map_zero φ) (map_one φ),
    Matrix.one_mulVec]

theorem div_mem {N : RatModel o Ω'} {q : N.Z ⟶ M.Z} (hq : M.IsHom N φ q) (l l' : EE.Frame) {t : J → Ω'}
    {i : J} {z : N.Z} (hz : q z ∈ l.W) (hz' : q z ∈ l'.W) (h : N.Div (l.co φ t) i z) (j : J) :
    l'.co φ t j / l.co φ t i ∈ N.O z := by
  have e : l'.co φ t = ((l'.B * l.c.map (valF M.pt l.W)).map φ).mulVec (l.co φ t) := by
    rw [Matrix.map_mul (f := φ), ← Matrix.mulVec_mulVec, ← l.eq_mulVec t]
  rw [e]
  exact hq.mulVec_div_mem h (mul_inv_apply_mem_of_span_le _ ((l'.basis _ hz').symm.trans (l.basis _ hz)).le
    (mul_eq_one_comm.1 l.c_inv)) j

theorem div_mem' {N : RatModel o Ω'} {q : N.Z ⟶ M.Z} (hq : M.IsHom N φ q) (l : EE.Frame) {t : J → Ω'}
    {i : J} {z : N.Z} (hz : q z ∈ l.W) (h : N.Div (l.co φ t) i z) (j : J) :
    t j / l.co φ t i ∈ N.O z := by
  have := hq.mulVec_div_mem h (m := l.c.map (valF M.pt l.W)) (fun j k => valF_mem_O hz _) j
  rwa [← l.eq_mulVec t] at this

end Lat.Frame
end RatModel

theorem nonempty_clos : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → Nonempty (Clos ρ M U₀ EE) := by
  intro hL o Ω _ _ _ _ S ρ M U₀ EE hB
  have := ArithBase.ded (o := o) (Ω := Ω)
  have hne := hB.ov.ne
  obtain ⟨u₀, hu₀⟩ := GlobalTheory.T.exists_hom_spec_of_le_ringOn' o Ω M U₀ S.R hne hB.ov.le
  have himm := ThetaSys.Real.immBy_basis hL o Ω S ρ
  have hH : (LPow ρ.P.A ρ.P.L S.N (baseOver (Sp S.R))).IsLB := LB.isLB_linComb ρ.P.isLB _ _

  have := ρ.P.isAb.smooth
  have := ρ.P.isAb.proper
  have := ρ.P.isAb.geomConnected
  have : GeometricallyIntegral ρ.P.A.hom := grpObj_geometricallyIntegral_of_smooth _ _
  have := M.isLocallyNoetherian
  have := M.sep
  have := M.lft
  have := M.qc
  have : IsIntegral U₀.toScheme := (M.openPart U₀ hne).integral
  have : IsIntegral (pullback ρ.P.A.hom u₀) :=
    GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (pullback.snd ρ.P.A.hom u₀)
  have : IsDominant U₀.ι := by
    have : IsDominant (M.ptOpen U₀ hne ≫ U₀.ι) := by rw [M.ptOpen_ι]; infer_instance
    exact IsDominant.of_comp (M.ptOpen U₀ hne) U₀.ι
  have : IsDominant (pullback.snd ρ.P.A.hom u₀ ≫ U₀.ι) := inferInstance
  obtain ⟨Ω', _, _, φ, pt, hgen, honto, hpt⟩ := GlobalTheory.T.exists_functionField_of_isDominant' o Ω M _ (pullback.snd ρ.P.A.hom u₀ ≫ U₀.ι)
  let N : RatModel o Ω' :=
    { Z := pullback ρ.P.A.hom u₀
      s := (pullback.snd ρ.P.A.hom u₀ ≫ U₀.ι) ≫ M.s
      sep := inferInstance
      lft := inferInstance
      qc := inferInstance
      pt := pt
      pt_s := by
        rw [← Category.assoc, hpt, Category.assoc, M.pt_s, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        congr 2
        exact φ.comp_algebraMap
      gen := hgen
      onto := honto }
  have hN : M.IsHom N φ (pullback.snd ρ.P.A.hom u₀ ≫ U₀.ι) := hpt
  have hsq : IsPullback (snd (baseOver (Sp S.R)) ρ.P.A).left (baseOver (Sp S.R) ⊗ ρ.P.A).hom ρ.P.A.hom (𝟙 _) := by
    have e : (baseOver (Sp S.R) ⊗ ρ.P.A).hom = (fst (baseOver (Sp S.R)) ρ.P.A).left :=
      (Over.w (fst (baseOver (Sp S.R)) ρ.P.A)).symm.trans (Category.comp_id _)
    rw [e]
    exact (IsPullback.of_hasPullback _ ρ.P.A.hom).flip
  let a : N.Z ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left :=
    hsq.lift (pullback.fst ρ.P.A.hom u₀) (pullback.snd ρ.P.A.hom u₀ ≫ u₀)
      (pullback.condition.trans (Category.comp_id _).symm)
  have ha₁ : a ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = pullback.fst ρ.P.A.hom u₀ := hsq.lift_fst _ _ _
  have ha₂ : a ≫ (baseOver (Sp S.R) ⊗ ρ.P.A).hom = pullback.snd ρ.P.A.hom u₀ ≫ u₀ := hsq.lift_snd _ _ _
  have hpb : IsPullback a (pullback.snd ρ.P.A.hom u₀) (baseOver (Sp S.R) ⊗ ρ.P.A).hom u₀ := by
    refine IsPullback.of_right ?_ ha₂ hsq
    rw [ha₁, Category.comp_id]
    exact IsPullback.of_hasPullback _ _
  obtain ⟨t, ht⟩ := CrdCalc.crd_exists hH ρ.s (N.pt ≫ a)
  obtain ⟨hdiv, hval⟩ := GlobalTheory.T.div_iff_mem_nonzeroLocus_and_crd_ratio o Ω' N _ a _ _ ρ.s t hH (by simpa using himm.1) ht
  have hchN := GlobalTheory.T.closedImmersionBaseChange_projChart o Ω M Ω' φ N U₀ _ _ _ u₀ a _ _ _ ρ.s t hpb hN himm ht hdiv
  obtain ⟨W₀, hW₀, hz₀, hle₀⟩ := exists_isAffineOpen_mem_and_subset (U := U₀) hne.some_mem
  obtain ⟨ht0, htop⟩ := (hchN W₀ hle₀ hW₀ ⟨_, hz₀⟩).closure_eq_top hN ⟨_, hz₀⟩

  obtain ⟨P, f, hf, hproj, hP⟩ := GlobalTheory.T.exists_projBundle_closure_alt o Ω M Ω' φ S.J EE t hB.ov.proj ht0 htop
  have hch : ∀ l : EE.Frame, M.ProjChart P φ f l.W (l.co φ t) := fun l => hP l.W l.B l.aff l.ne l.basis
  have hstd : ∀ (W : M.Z.Opens) (hW : IsAffineOpen W) (hWne : (W : Set M.Z).Nonempty) (h : _),
      (EE.stdFrame hW hWne h).co φ t = t := fun W hW hWne h => by
    show ((1 : Matrix S.J S.J Ω).map φ).mulVec t = t
    rw [Matrix.map_one _ (map_zero φ) (map_one φ), Matrix.one_mulVec]
  have hchP : ∀ W : M.Z.Opens, W ≤ U₀ → IsAffineOpen W → (W : Set M.Z).Nonempty → M.ProjChart P φ f W t :=
    fun W hle hW hWne => by
      have := hch (EE.stdFrame hW hWne fun z hz => hB.ee.1 z (hle hz))
      rwa [hstd] at this
  obtain ⟨a₀, ha₀, hcart⟩ := GlobalTheory.T.exists_isPullback_of_projChart' o Ω M Ω' φ N P U₀ _ f S.J t hN hf
    fun W hle hW hWne => ⟨hchN W hle hW hWne, hchP W hle hW hWne⟩

  let I : Type := {k : EE.Frame × S.J // k.1.co φ t k.2 ≠ 0}
  let d : I → Ω' := fun k => k.1.1.co φ t k.1.2
  let U : I → P.Z.Opens := fun k => f ⁻¹ᵁ k.1.1.W ⊓ ⟨_, P.isOpen_setOf_div (k.1.1.co φ t) k.1.2⟩
  have hUcov : ⨆ k, U k = ⊤ := top_unique fun z _ => by
    obtain ⟨l, hl⟩ := EE.exists_frame hB.mem (f z)
    obtain ⟨i, hi⟩ := (hch l).1 z hl
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(l, i), hi.1⟩, hl, hi⟩
  obtain ⟨g, hLB, hG⟩ := GlobalTheory.T.exists_isLB_genTriv_of_ratios' o Ω' P I U d hUcov (fun k => k.2)
    fun k k' z hz => RatModel.Lat.Frame.div_mem hf k.1.1 k'.1.1 hz.1.1 hz.2.1 hz.1.2 k'.1.2
  let O1 : LB P.Z := ⟨I, U, g⟩
  obtain ⟨hsec, hpull⟩ := GlobalTheory.T.genericTrivialisation_section_and_pullback o Ω' P O1 d hG
  choose st hst using fun j => hsec (t j) fun k z hz => RatModel.Lat.Frame.div_mem' hf k.1.1 hz.1 hz.2 j
  have hV : ∀ l : EE.Frame, ((f ⁻¹ᵁ l.W : P.Z.Opens) : Set P.Z).Nonempty := fun l => ⟨_, hf.genericPoint_mem l.ne⟩
  let Q : EE.Frame → RatModel o Ω' := fun l => P.openPart _ (hV l)
  have hQ : ∀ l, P.IsHom (Q l) (AlgHom.id o Ω') (f ⁻¹ᵁ l.W).ι := fun l => P.isHom_openPart _ _
  have hQf : ∀ l, M.IsHom (Q l) φ ((f ⁻¹ᵁ l.W).ι ≫ f) := fun l => by
    have := hf.comp (hQ l)
    rwa [AlgHom.id_comp] at this
  have hGQ : ∀ l, (Q l).GenTriv (O1.pull (f ⁻¹ᵁ l.W).ι) fun k => d (k PUnit.unit) :=
    fun l => hpull Ω' (AlgHom.id o Ω') (Q l) _ (hQ l)
  have hmem : ∀ (l : EE.Frame) (k : (O1.pull (f ⁻¹ᵁ l.W).ι).ι) (z : (f ⁻¹ᵁ l.W).toScheme),
      z ∈ (O1.pull (f ⁻¹ᵁ l.W).ι).U k → (f ⁻¹ᵁ l.W).ι z ∈ U (k PUnit.unit) :=
    fun l k z hz => LB.wchart_le O1 (fun _ => (f ⁻¹ᵁ l.W).ι) k PUnit.unit hz
  have hO : ∀ (l : EE.Frame) (z : (f ⁻¹ᵁ l.W).toScheme), (Q l).O z = P.O ((f ⁻¹ᵁ l.W).ι z) :=
    fun l z => @RatModel.IsHom.O_eq _ _ _ _ _ _ _ _ (hQ l) (inferInstanceAs (IsOpenImmersion (f ⁻¹ᵁ l.W).ι)) z
  have hD : ∀ (l : EE.Frame) (z : (f ⁻¹ᵁ l.W).toScheme) (u : S.J → Ω') (i : S.J),
      (Q l).Div u i z ↔ P.Div u i ((f ⁻¹ᵁ l.W).ι z) := fun l z u i => by
    simp only [RatModel.Div, hO]
  choose σ hσ using fun (l : EE.Frame) (j : S.J) => (GlobalTheory.T.genericTrivialisation_section_and_pullback o Ω' (Q l) _ _ (hGQ l)).1 (l.co φ t j)
    fun k z hz => (hO l z).ge (RatModel.Lat.Frame.div_mem hf _ l (hmem l k z hz).1 z.2 (hmem l k z hz).2 j)
  have : IsProper (f ≫ M.s) := by
    rw [hf.inducedModelMorphism_comp_structureMap]
    exact projProper _ _ _ hproj
  refine ⟨{
    u₀ := u₀
    u₀_pt := hu₀
    P := Over.mk f
    intP := P.integral
    proper := IsProper.of_comp f M.s
    proj := by
      show IsProjOver (f ≫ M.s)
      rw [hf.inducedModelMorphism_comp_structureMap]
      exact hproj
    a₀ := a₀
    cart := hcart
    O1 := O1
    isLB := hLB
    st := st
    crd := ?_
    Λ := EE.Frame
    W := fun l => l.W
    aff := fun l => l.aff
    ne := fun l => l.ne
    cover := top_unique fun z _ => TopologicalSpace.Opens.mem_iSup.2 (EE.exists_frame hB.mem z)
    B := fun l => l.B
    basis := fun l => l.basis
    c := fun l => l.c
    c_inv := fun l => l.c_inv
    σ := σ
    rel := fun l R _ _ x w hw => GlobalTheory.T.homogeneousCoordinates_mulVec_of_genericValue o Ω M Ω' φ P (Q l) _ _ l.W O1 d S.J st (σ l) t (l.co φ t) l.c (hQ l) (hQf l)
      (fun z => z.2) hst (hσ l) (l.eq_mulVec t) R x w hw
    imm := fun l => ?_ }⟩
  · rintro K _ x v ⟨a', ha', hv⟩
    have : IsIso (snd (baseOver (Sp S.R)) ρ.P.A).left := hsq.isIso_fst_of_isIso
    obtain rfl : a' = x ≫ a := by
      rw [← cancel_mono (snd (baseOver (Sp S.R)) ρ.P.A).left, ha', Category.assoc, ha₁]
    have hzU : f (a₀ (x (IsLocalRing.closedPoint K))) ∈ U₀ := by
      rw [← Scheme.Hom.comp_apply, hcart.w, Scheme.Hom.comp_apply]
      exact (pullback.snd ρ.P.A.hom u₀ (x (IsLocalRing.closedPoint K))).2
    obtain ⟨W, hW, hzW, hle⟩ := exists_isAffineOpen_mem_and_subset hzU
    obtain ⟨i, hi⟩ := (hchP W hle hW ⟨_, hzW⟩).1 _ hzW
    obtain ⟨hv0, hvj⟩ := hval K x v i hv (ha₀.div hi)
    let l := EE.stdFrame hW ⟨_, hzW⟩ fun z hz => hB.ee.1 z (hle hz)
    have hl : l.co φ t = t := hstd _ _ _ _
    let k : I := ⟨(l, i), by rw [hl]; exact hi.1⟩
    have hk : a₀ (x (IsLocalRing.closedPoint K)) ∈ U k := ⟨hzW, by
      show P.Div (l.co φ t) i _
      rw [hl]
      exact hi⟩
    have hk' : ⊤ ≤ (x ≫ a₀) ⁻¹ᵁ U k := (le_preimage_iff _ _).2 hk
    refine ⟨k, Units.mk0 (v i) hv0, hk', fun j => ?_⟩
    have e1 : valF P.pt (U k) ((st j).f k) = t j / t i := (hst j k ⟨_, hk⟩).trans (congrArg (t j / · i) hl)
    have e2 := RatModel.val_eq ((top_le_preimage_iff _ _).1 hk') e1
    have e3 := ha₀.val_comp x (IsLocalRing.closedPoint K) (hi.2 j)
    rw [hvj j, mul_comm]
    exact congrArg (v i * ·) (e3.symm.trans e2)
  · refine GlobalTheory.T.isClosedImmersion_of_coordinate_divisibility o Ω' (Q l) _ _ S.J (σ l) (l.co φ t) _ _ (φ.toRingHom.comp (M.res l.W l.ne))
      (LB.isLB_pull hLB _) (hGQ l) (hσ l) (fun k z hz => ?_) ?_ fun i hi => ?_
    · obtain ⟨i, hi⟩ := (hch l).1 ((f ⁻¹ᵁ l.W).ι z) z.2
      exact ⟨i, hi.1, (hO l z).ge (RatModel.Lat.Frame.div_mem hf l _ z.2 (hmem l k z hz).1 hi _)⟩
    · rw [← cancel_mono l.aff.fromSpec]
      have e : ((f ∣_ l.W) ≫ l.aff.isoSpec.hom) ≫ l.aff.fromSpec = (f ⁻¹ᵁ l.W).ι ≫ f := by
        rw [Category.assoc, l.aff.isoSpec_hom_fromSpec, morphismRestrict_ι]
      refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e).trans ((hQf l).trans ?_))
      conv_lhs => rw [← specMap_valMap_fromSpec l.aff M.pt (M.top_le_preimage_pt l.ne)]
      rw [← Spec.map_comp_assoc]
      rfl
    · obtain ⟨V, hVa, hVe, hVr⟩ := (hch l).2 i hi
      have hle : V ≤ f ⁻¹ᵁ l.W := fun z hz => by
        have : z ∈ (V : Set P.Z) := hz
        rw [hVe] at this
        exact this.1
      have hVa' : IsAffineOpen ((f ⁻¹ᵁ l.W).ι ⁻¹ᵁ V) := hVa.preimage_of_isOpenImmersion _ (by simpa using hle)
      refine ⟨(f ⁻¹ᵁ l.W).ι ⁻¹ᵁ V, hVa', ?_, fun x hx => ?_⟩
      · ext z
        show (f ⁻¹ᵁ l.W).ι z ∈ (V : Set P.Z) ↔ (Q l).Div _ i z
        rw [hVe]
        exact ⟨fun h => (hD l z _ i).2 h.2, fun h => ⟨z.2, (hD l z _ i).1 h⟩⟩
      · have hx' : x ∈ P.ringOn V := RatModel.mem_ringOn.2 fun z hz =>
          (hO l ⟨z, hle hz⟩).le (RatModel.mem_ringOn.1 hx ⟨z, hle hz⟩ hz)
        rw [hVr] at hx'
        clear hx
        induction hx' using Algebra.adjoin_induction with
        | mem y hy =>
          rcases hy with ⟨y, hy, rfl⟩ | hy
          · obtain ⟨r, rfl⟩ := (RatModel.mem_ringOn_iff_exists l.ne).1 hy
            exact Subring.subset_closure (Or.inl ⟨r, congrArg φ (M.res_apply _ _ r)⟩)
          · exact Subring.subset_closure (Or.inr hy)
        | algebraMap r =>
          exact Subring.subset_closure (Or.inl ⟨constFn M.s l.W r,
            (congrArg φ ((M.res_apply _ _ _).trans (M.valF_constFn l.ne r))).trans (φ.commutes r)⟩)
        | add _ _ _ _ h1 h2 => exact add_mem h1 h2
        | mul _ _ _ _ h1 h2 => exact mul_mem h1 h2

end GlobalTheory.ZH
end
