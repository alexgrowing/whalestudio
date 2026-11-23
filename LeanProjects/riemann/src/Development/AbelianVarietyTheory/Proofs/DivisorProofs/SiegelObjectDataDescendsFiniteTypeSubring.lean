import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInclusionCyclotomicAwayRingFiniteEtale
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LineBundleIsoDescendsToSubringOfFinset
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MorphismDescendsToSubring
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsToFinitelyGeneratedSubring
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsNoethModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrincipalObjectDescendsLargeSubfield
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

namespace GlobalTheory.SiegFg

theorem spMap_subtype_inclusion' {R : Type} [CommRing R] {S₀ R₁ : Subring R} (h : S₀ ≤ R₁) :
    spMap R₁.subtype ≫ spMap (Subring.inclusion h) = spMap S₀.subtype := by
  rw [← Spec.map_comp]
  rfl

theorem smooth_pull {S S' : Scheme.{0}} (f : S' ⟶ S) (B : Over S) (g : ℕ) (hB : SmoothOfRelativeDimension g B.hom) :
    SmoothOfRelativeDimension g ((Over.pullback f).obj B).hom :=
  (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback B.hom f) hB

theorem range_le {n : ℕ} {R : Type} [CommRing R] (β : cycAway n →+* R) (S₀ : Subring R)
    (h₁ : β (zetaAway n) ∈ S₀) (h₂ : ∀ hm : ((n : ℂ))⁻¹ ∈ cycAway n, β ⟨((n : ℂ))⁻¹, hm⟩ ∈ S₀) (x : cycAway n) :
    β x ∈ S₀ := by
  obtain ⟨x, hx⟩ := x
  induction hx using Subring.closure_induction with
  | mem y hy =>
    rcases hy with rfl | hy
    · exact h₁
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact h₂ _
  | zero => exact (congrArg (· ∈ S₀) (map_zero β)).mpr S₀.zero_mem
  | one => exact (congrArg (· ∈ S₀) (map_one β)).mpr S₀.one_mem
  | add y z hy hz ihy ihz =>
    have e : β ⟨y + z, Subring.add_mem _ hy hz⟩ = β ⟨y, hy⟩ + β ⟨z, hz⟩ := by rw [← map_add]; rfl
    rw [e]; exact S₀.add_mem ihy ihz
  | neg y hy ihy =>
    have e : β ⟨-y, Subring.neg_mem _ hy⟩ = -β ⟨y, hy⟩ := by rw [← map_neg]; rfl
    rw [e]; exact S₀.neg_mem ihy
  | mul y z hy hz ihy ihz =>
    have e : β ⟨y * z, Subring.mul_mem _ hy hz⟩ = β ⟨y, hy⟩ * β ⟨z, hz⟩ := by rw [← map_mul]; rfl
    rw [e]; exact S₀.mul_mem ihy ihz

end GlobalTheory.SiegFg

namespace GlobalTheory.SiegFg

theorem siegPre_data_descends_fg : ∀ (g n : ℕ), 3 ≤ n → ∀ (R : Type) [CommRing R] (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)), ∃ (R₁ : Subring R) (β₁ : cycAway n →+* R₁) (A₁ : Over (Sp R₁)) (_ : GrpObj A₁) (P₁ : LB (A₁ ⊗ A₁).left) (lv₁ : Std g n → (𝟙_ (Over (Sp R₁)) ⟶ A₁)), Algebra.FiniteType ℤ R₁ ∧ R₁.subtype.comp β₁ = β ∧ IsAbelianScheme A₁ ∧ SmoothOfRelativeDimension g A₁.hom ∧ P₁.IsLB ∧ IsPullbackTriple c.A c.P (lvOf c) A₁ P₁ lv₁ (spMap R₁.subtype) := by
  intro g n hn R _ β c
  classical
  have h0 : n ≠ 0 := by omega
  haveI : NeZero n := ⟨h0⟩
  have hdim : SmoothOfRelativeDimension g c.A.hom :=
    relDim (ζ := (cycBase h0).ζ) (by omega) (isUnit_natCast h0) c
  have hm : ((n : ℂ))⁻¹ ∈ cycAway n := Subring.subset_closure (by simp)
  obtain ⟨S₀, B, _, φ, hF, hS₀, hB, hBd, hφ⟩ := GlobalTheory.AbelianLimit.abelianScheme_descends_to_fg_subring R g c.A
    {β (zetaAway n), β ⟨((n : ℂ))⁻¹, hm⟩} c.ab hdim
  have hβ : ∀ x, β x ∈ S₀ := range_le β S₀ (hF (by simp)) (fun _ => hF (by simp))
  have : IsCommMonObj B := hB.comm
  have : IsProper B.hom := hB.proper
  have : Smooth B.hom := hB.smooth
  have : QuasiCompact (B ⊗ B).hom := by
    change QuasiCompact (pullback.fst B.hom B.hom ≫ B.hom); infer_instance
  have : QuasiSeparated (B ⊗ B).hom := by
    change QuasiSeparated (pullback.fst B.hom B.hom ≫ B.hom); infer_instance

  obtain ⟨φ₂, hsq⟩ := GlobalTheory.SiegDesc.exists_isSquare hφ.1.w
  obtain ⟨SP, hSP⟩ := GlobalTheory.LBLimit.lb_descends_to_fg_subring R S₀ (c.A ⊗ c.A).left (B ⊗ B).left (c.A ⊗ c.A).hom
    (B ⊗ B).hom φ₂ c.P (GlobalTheory.SiegDesc.isPullback_of_isSquare hφ.1 hsq) c.isLB

  have hw : ∀ a : Std g n, ((lvOf c a).left ≫ φ) ≫ B.hom = spMap S₀.subtype ≫ 𝟙 _ := fun a => by
    have e : (lvOf c a).left ≫ c.A.hom = 𝟙 _ := Over.w (lvOf c a)
    rw [Category.assoc, hφ.1.w, reassoc_of% e, Category.comp_id]
  choose SL hSL using fun a : Std g n => GlobalTheory.morphism_descends_to_subring R S₀ (Sp R) (Sp S₀) B.left (𝟙 _) (𝟙 _)
    B.hom (spMap S₀.subtype) ((lvOf c a).left ≫ φ) IsPullback.of_id_snd (hw a)

  let T : Finset R := SP ∪ Finset.univ.biUnion SL
  let R₁ : Subring R := (Algebra.adjoin S₀ (T : Set R)).toSubring
  have hFT : Algebra.FiniteType ℤ R₁ :=
    GlobalTheory.SpreadGroup.finiteType_of_fg hS₀ (Subalgebra.fg_adjoin_finset T)
  have h : S₀ ≤ R₁ := fun x hx => Subalgebra.algebraMap_mem (Algebra.adjoin S₀ (T : Set R)) (⟨x, hx⟩ : S₀)
  have hT : (T : Set R) ⊆ R₁ := Algebra.subset_adjoin
  have hSPs : (SP : Set R) ⊆ R₁ := fun x hx => hT (by simp [T, Finset.mem_coe.1 hx])
  have hSLs : ∀ a, (SL a : Set R) ⊆ R₁ := fun a x hx => hT (by
    simp only [T, Finset.coe_union, Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true]
    exact Or.inr (Set.mem_iUnion.2 ⟨a, hx⟩))
  have hj : spMap R₁.subtype ≫ spMap (Subring.inclusion h) = spMap S₀.subtype := spMap_subtype_inclusion' h

  let A₁ : Over (Sp R₁) := (Over.pullback (spMap (Subring.inclusion h))).obj B
  have hA₁ : IsAbelianScheme A₁ :=
    { comm := by infer_instance
      smooth := by show Smooth (pullback.snd _ _); infer_instance
      proper := by show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by
        have := hB.geomConnected
        show GeometricallyConnected (pullback.snd _ _); infer_instance }
  have hA₁d : SmoothOfRelativeDimension g A₁.hom := smooth_pull _ B g hBd
  have hpb := Pdiv.PullbackComparison.isGrpPullback (spMap (Subring.inclusion h)) B
  let ψ : c.A.left ⟶ A₁.left := pullback.lift φ (c.A.hom ≫ spMap R₁.subtype)
    (by rw [hφ.1.w, Category.assoc, hj])
  have hψ₁ : ψ ≫ Pdiv.PullbackComparison.pφ (spMap (Subring.inclusion h)) B = φ := pullback.lift_fst _ _ _
  have hψ₂ : ψ ≫ A₁.hom = c.A.hom ≫ spMap R₁.subtype := pullback.lift_snd _ _ _
  have hgp : IsGrpPullback c.A A₁ (spMap R₁.subtype) ψ :=
    IsGrpPullback.cancel hpb (by rw [hψ₁, hj]; exact hφ) hψ₂

  obtain ⟨ψ₂, hsqψ⟩ := GlobalTheory.SiegDesc.exists_isSquare hψ₂
  obtain ⟨P₁, hP₁, hiso⟩ := hSP R₁ h hSPs (A₁ ⊗ A₁).left (A₁ ⊗ A₁).hom
    (Pdiv.PullbackComparison.pφ₂ (spMap (Subring.inclusion h)) B) ψ₂
    (GlobalTheory.SiegDesc.isPullback_of_isSquare hpb.1 (Pdiv.PullbackComparison.isSquare _ B))
    (GlobalTheory.SiegDesc.isSquare_comp hψ₁ hsqψ (Pdiv.PullbackComparison.isSquare _ B) hsq) (GlobalTheory.SiegDesc.isSquare_w hψ₂ hsqψ)

  choose ψa hψa using fun a : Std g n => hSL a R₁ h (hSLs a) (Sp R₁) (𝟙 _) (spMap (Subring.inclusion h))
    (spMap R₁.subtype) IsPullback.of_id_snd hj (by simp)
  let l : Std g n → (Sp R₁ ⟶ A₁.left) := fun a => pullback.lift (ψa a) (𝟙 _)
    (by rw [(hψa a).2, Category.comp_id, Category.id_comp])
  have hl₁ : ∀ a, l a ≫ pullback.fst _ _ = ψa a := fun a => pullback.lift_fst _ _ _
  have hl₂ : ∀ a, l a ≫ A₁.hom = 𝟙 _ := fun a => pullback.lift_snd _ _ _
  let lv₁ : Std g n → (𝟙_ (Over (Sp R₁)) ⟶ A₁) := fun a => Over.homMk (l a) (hl₂ a)
  refine ⟨R₁, β.codRestrict R₁ (fun x => h (hβ x)), A₁, inferInstance, P₁, lv₁, hFT, by ext; rfl, hA₁, hA₁d, hP₁,
    ψ, ψ₂, hgp, hsqψ.1, hsqψ.2, hiso, fun a => ?_⟩
  have e : (lvOf c a).left ≫ c.A.hom = 𝟙 _ := Over.w (lvOf c a)
  apply pullback.hom_ext
  · change (lvOf c a).left ≫ ψ ≫ pullback.fst _ _ = spMap R₁.subtype ≫ l a ≫ pullback.fst _ _
    rw [hl₁]
    exact (congrArg ((lvOf c a).left ≫ ·) hψ₁).trans (hψa a).1.symm
  · change (lvOf c a).left ≫ ψ ≫ A₁.hom = spMap R₁.subtype ≫ l a ≫ A₁.hom
    rw [hψ₂, hl₂, reassoc_of% e, Category.comp_id]

end GlobalTheory.SiegFg
