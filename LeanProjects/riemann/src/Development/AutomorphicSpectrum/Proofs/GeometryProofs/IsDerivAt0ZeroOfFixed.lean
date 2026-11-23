import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsAbLift
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExponentialFamilyPeriods
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsDerivAt0CompLinMap
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyFamilyUnifIffUnifAt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ExpRowsPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieAlgebraSquaredLengthCompPairingHom
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGrpObjPolarised
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.QuotLoc.DiffL.Pol
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
variable {X : Scheme.{0}}

noncomputable def pullPolL (P : Out.PolAV X) {z : Sp ℂ ⟶ X} {A : Over (Sp ℂ)} [GrpObj A]
    {φ : A.left ⟶ P.A.left} (h : IsGrpPullback A P.A z φ) : Out.PolAV (Sp ℂ) :=
  have hL := pull_isLB P.isLB φ
  have H := pol_pull _ _ P.A A _ φ P.L _ P.isLB hL P.isAb h (PolBaseChange.lbIso_refl hL)
  { A := A, isAb := H.1, g := P.g
    smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim
    L := P.L.pull φ, isLB := hL, rigid := PolBaseChange.rigidified_pull h P.rigid
    sym := PolBaseChange.sym_pull h P.sym, ample := H.2.1 P.ample, ktriv := H.2.2 P.ktriv }

end GlobalTheory.CompanionTheory.Ar.QuotLoc.DiffL.Pol

namespace GlobalTheory.CompanionTheory.Ar.QuotLoc.DiffL

open ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows ReciprocityTheory.ChartRestriction.G.TB.ValAt Formalism.L2.Pj

theorem isDerivAt0_zero_of_fixed {g : ℕ} {Y : Scheme.{0}} {F : (Fin g → ℂ) → (Sp ℂ ⟶ Y)}
    {v : Sp (DualNumber ℂ) ⟶ Y} (h0 : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = F 0)
    (hv : spMap (epsMul (0 : ℂ)) ≫ v = v) : IsDerivAt0 F 0 v := by
  refine ⟨h0, fun U h f => ?_⟩
  rw [map_zero]
  have key : ∀ (v' : Sp (DualNumber ℂ) ⟶ Y) (_ : v' = spMap (epsMul (0 : ℂ)) ≫ v) (h' : ⊤ ≤ v' ⁻¹ᵁ U),
      TrivSqZeroExt.snd (show DualNumber ℂ from
        (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom ((v'.appLE U ⊤ h').hom f)) = 0 := by
    rintro _ rfl h'
    have hs := ReciprocityTheory.ChartRestriction.G.PullbackSections.specMap_comp_appLE (CommRingCat.ofHom (epsMul (0 : ℂ))) v U h' h
    have := ConcreteCategory.congr_hom hs f
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this
    erw [this]
    simp [epsMul]
  exact key v hv.symm h

theorem isHolTo_slice {n g : ℕ} {B : Set (Fin n → ℂ)} {Y : Scheme.{0}}
    {F : (Fin n → ℂ) × (Fin g → ℂ) → (Sp ℂ ⟶ Y)} (h : IsHolTo (B ×ˢ Set.univ) F) {b : Fin n → ℂ} (hb : b ∈ B) :
    IsHolTo Set.univ (fun z : Fin g → ℂ => F (b, z)) := by
  intro U f
  obtain ⟨h1, h2⟩ := h U f
  have hc : Continuous (fun z : Fin g → ℂ => (b, z)) := by fun_prop
  have hmem : ∀ z, z ∈ {z ∈ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ F (b, z) ⁻¹ᵁ U} →
      (b, z) ∈ {bz ∈ B ×ˢ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ F bz ⁻¹ᵁ U} :=
    fun z hz => ⟨⟨hb, trivial⟩, hz.2⟩
  have hset : {z ∈ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ F (b, z) ⁻¹ᵁ U} =
      (fun z => (b, z)) ⁻¹' {bz ∈ B ×ˢ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ F bz ⁻¹ᵁ U} :=
    Set.ext fun z => ⟨hmem z, fun hz => ⟨trivial, hz.2⟩⟩
  refine ⟨hset ▸ h1.preimage hc, fun z hz => ?_⟩
  have hd := (h2 _ (hmem z hz)).differentiableAt (h1.mem_nhds (hmem z hz))
  have hi : DifferentiableAt ℂ (fun z : Fin g → ℂ => (b, z)) z := by fun_prop
  exact (DifferentiableAt.comp z hd hi).differentiableWithinAt

theorem isDerivAt0_pt {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {g n : ℕ}
    {M : LieModel G (𝟙 (Sp R)) (Fin g → R)} {B : Set (Fin n → ℂ)} {ψ : (Fin n → ℂ) → (R →+* ℂ)}
    (e : Flat.FamExp G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B) (Mz : LieModel G (spMap (ψ b)) (Fin g → ℂ))
    (hL : ∀ i, M.Lifts (ψ b) (𝟙 _) (Pi.single i 1) (Mz.pt (Pi.single i 1))) (x : Fin g → ℂ) :
    IsDerivAt0 (fun z => (e.ex b z).left) x (Mz.pt x).left := by
  have h1 : e.ex b 0 = 1 := by
    have := e.add b hb 0 0
    rw [add_zero] at this
    exact mul_eq_left.mp this.symm
  have h0 : (fun z => (e.ex b z).left) 0 = (1 : Over.mk (spMap (ψ b)) ⟶ G).left := congrArg (·.left) h1
  have hbas : ∀ i, IsDerivAt0 (fun z => (e.ex b z).left) (Pi.single i 1) (Mz.pt (Pi.single i 1)).left := fun i => by
    have h := e.diff b hb i
    have h' := hL i
    unfold LieModel.Lifts at h'
    rw [Category.comp_id] at h'
    rwa [← h'] at h
  have hsc : ∀ (c : ℂ) i, IsDerivAt0 (fun z => (e.ex b z).left) (c • Pi.single i 1)
      (Mz.pt (c • Pi.single i 1)).left := fun c i => by
    rw [Mz.smul]
    exact isDerivAt0_smul (hbas i) c
  have hzero : IsDerivAt0 (fun z => (e.ex b z).left) 0 (Mz.pt 0).left := by
    refine isDerivAt0_zero_of_fixed ((Mz.tan 0).trans h0.symm) ?_
    have := Mz.smul 0 0
    rw [zero_smul] at this
    exact this.symm
  have hsum : ∀ s : Finset (Fin g), IsDerivAt0 (fun z => (e.ex b z).left) (∑ i ∈ s, x i • Pi.single i 1)
      (Mz.pt (∑ i ∈ s, x i • Pi.single i 1)).left := fun s => by
    classical
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Mz.add]
      exact UnifCompare.isDerivAt0_mul h0 (hsc _ _) ih
  have hx : ∑ i, x i • (Pi.single i 1 : Fin g → ℂ) = x := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  have := hsum Finset.univ
  rwa [hx] at this

theorem isDiff_unique {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (t : SAB H (Sp ℂ))
    (hP : IsPrincipal t) {A : Over (Sp ℂ)} [GrpObj A] {φ : A.left ⟶ t.G.left} (hφ : IsGrpPullback A t.G (𝟙 _) φ)
    {g' : ℕ} (u : HolUnif A (t.PP.L.pull φ) g') (Hm : Matrix (Fin g') (Fin g') ℂ) (χ : u.Λ → ℂ) (hA : u.IsAH Hm χ)
    {v : epsR ℂ ⟶ A} (hv : IsTangent v) {w w' : Fin g' → ℂ} (h : u.IsDiff w v) (h' : u.IsDiff w' v) : w = w' := by
  obtain ⟨hpr, ham, hk⟩ := hP
  have := t.semi.smooth
  have := t.semi.geomConnected
  have : ConnectedSpace t.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := t.G.hom) (𝟙 _) (𝟙 _) t.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected t.G.hom (eSec t.G (default : PrimeSpectrum ℂ))
  let Q : Out.PolAV (Sp ℂ) :=
    { A := t.G, g := d, smoothDim := hd, L := t.PP.L, isLB := t.PP.isLB, ample := ham, ktriv := hk
      isAb := ⟨inferInstance, inferInstance, hpr, ‹_›⟩
      rigid := ⟨t.PP.rig, t.PP.rigGen⟩
      sym := GlobalTheory.CechPic.sym_of_isSymmetric t.PP t.sym }
  have hφ' : IsGrpPullback A Q.A (𝟙 _) φ := hφ
  obtain ⟨-, -, -, -, t1, -, -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH GlobalTheory.thetaUnifAV_all
    (GlobalTheory.CompanionTheory.Ar.QuotLoc.DiffL.Pol.pullPolL Q hφ') g' u Hm χ hA
  exact (t1 v hv).unique h h'

theorem isDiff_eq_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (g n : ℕ) (M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : Flat.FamExp t.G M B ψ) (b : Fin n → ℂ) (P : AbPart t (spMap (ψ b))) (A : Over (Sp ℂ)) (_ : GrpObj A) (φ : A.left ⟶ P.tB.G.left) (g' : ℕ) (u : HolUnif A (P.tB.PP.L.pull φ) g') (Hm : Matrix (Fin g') (Fin g') ℂ) (χ : u.Λ → ℂ) (ℓ : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), b ∈ B → IsGrpPullback A P.tB.G (𝟙 _) φ → u.IsAH Hm χ → IsPrincipal P.tB → GlobalTheory.CompanionTheory.Ar.QuotLoc.IsAbLift e b P φ u ℓ → ∀ (Mz : LieModel t.G (spMap (ψ b)) (Fin g → ℂ)), (∀ i, M.Lifts (ψ b) (𝟙 _) (Pi.single i 1) (Mz.pt (Pi.single i 1))) → ∀ (x : Fin g → ℂ) (v : epsAt (𝟙 (Sp ℂ)) ⟶ P.tK.G) (v' : epsR ℂ ⟶ A) (w : Fin g' → ℂ), v.left ≫ P.m.φ = (Mz.pt x).left → v'.left ≫ φ = (v ≫ P.τ.q ≫ P.e.hom).left → u.IsDiff w v' → w = ℓ x := by
  intro E _ _ _ H R _ t g n M B ψ e b P A _ φ g' u Hm χ ℓ hb hφ hA hP hl Mz hL x v v' w hv hv' hw
  have Hc := P.m.cart.1
  have hex : ∀ y, ∃ s : 𝟙_ (Over (Sp ℂ)) ⟶ P.tK.G, s.left ≫ P.m.φ = (e.ex b y).left := fun y =>
    ⟨Over.homMk (Hc.lift (e.ex b y).left (𝟙 _) (by simpa using Over.w (e.ex b y))) (Hc.lift_snd _ _ _),
      Hc.lift_fst _ _ _⟩
  choose s hs using hex
  have hd1 := isDerivAt0_pt e hb Mz hL x
  have hFeq : (fun z => (s z).left ≫ P.m.φ) = fun z => (e.ex b z).left := funext hs
  have hd2 : IsDerivAt0 (fun z => (s z).left) x v.left :=
    GlobalTheory.FibreDeriv.isDerivAt0_of_isPullback Hc (fun z => Over.w (s z))
      (by rw [hFeq]; exact isHolTo_slice e.hol hb) (by simpa using Over.w v) (by rw [hFeq, hv]; exact hd1)
  have : IsIso φ := hφ.1.isIso_fst_of_isIso
  have hd3 := isDerivAt0_comp_hom hd2 ((P.τ.q ≫ P.e.hom).left ≫ inv φ)
  have e1 : v.left ≫ (P.τ.q ≫ P.e.hom).left ≫ inv φ = v'.left := by
    rw [← Category.assoc, ← Over.comp_left, ← hv', Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have e2 : (fun z => (s z).left ≫ (P.τ.q ≫ P.e.hom).left ≫ inv φ) = fun z => (u.ex (ℓ z)).left :=
    funext fun z => by
      rw [← Category.assoc, ← Over.comp_left, ← hl z (s z) (hs z), Category.assoc, IsIso.hom_inv_id,
        Category.comp_id]
  rw [e1, e2] at hd3
  have hz : (u.ex (ℓ 0)).left = η[A].left := by
    rw [map_zero]
    exact GlobalTheory.CompanionTheory.Ar.Flat.PerGram.ex_zero_left u
  have htan : IsTangent v' := hd3.1.trans hz
  have hdiff : u.IsDiff (ℓ x) v' := fun U h f => by
    refine (hd3.2 U h f).trans ?_
    have hU : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U := by
      have := tangent_open_preimage_zero hd3 U h
      simpa using this
    have hd : DifferentiableAt ℂ (fun z => valAt' (u.ex z).left U f) (ℓ.toContinuousLinearMap 0) := by
      rw [map_zero]
      exact ((u.hol U f).2 0 hU).differentiableAt ((u.hol U f).1.mem_nhds hU)
    have := fderiv_comp (𝕜 := ℂ) (0 : Fin g → ℂ) hd ℓ.toContinuousLinearMap.differentiableAt
    show fderiv ℂ ((fun z => valAt' (u.ex z).left U f) ∘ ℓ.toContinuousLinearMap) 0 x = _
    rw [this, ContinuousLinearMap.comp_apply, ContinuousLinearMap.fderiv, map_zero]
    rfl
  exact isDiff_unique P.tB hP hφ u Hm χ hA htan hw hdiff

end GlobalTheory.CompanionTheory.Ar.QuotLoc.DiffL
