import Development.EtaleCohomology.EtaleSheaves.LeafCurveCut
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsNeZeroIsStandardSmoothOfRelativeDimension

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.E4.CurveCut.CoverPf

open LateralTheory.E.E4

theorem inf_affine {Ω : Type} [Field Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω) (hc : IsCurve c)
    {U V : C.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) : IsAffineOpen (U ⊓ V) := by
  obtain ⟨_, hP, _⟩ := hc
  have : IsSeparated c := inferInstance
  have : IsSeparated (terminal.from C) := by
    rw [show terminal.from C = c ≫ terminal.from _ from Subsingleton.elim _ _]
    infer_instance
  exact hU.inf hV

theorem inf_nonempty {Ω : Type} [Field Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω) (hc : IsCurve c)
    {U V : C.Opens} (hU : (U : Set C).Nonempty) (hV : (V : Set C).Nonempty) : ((U ⊓ V : C.Opens) : Set C).Nonempty := by
  obtain ⟨hI, _, _⟩ := hc
  have := hI
  simpa using nonempty_preirreducible_inter U.isOpen V.isOpen hU hV

def LeafAffCover : Prop := ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c →
  ∃ U V : C.Opens, U ⊔ V = ⊤ ∧ IsAffineOpen U ∧ IsAffineOpen V ∧ (U : Set C).Nonempty ∧ (V : Set C).Nonempty

def LeafDedOpen : Prop := ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c →
  ∀ W : C.Opens, IsAffineOpen W → (W : Set C).Nonempty →
    ∃ (B : Type) (_ : CommRing B) (_ : IsDedekindDomain B) (_ : Algebra Ω B) (_ : Algebra.FiniteType Ω B),
      Nonempty (W.toScheme ≅ Sp B)

theorem LeafCover_of (hA : LeafAffCover) (hD : LeafDedOpen) : LeafCover := by
  intro Ω _ _ C c hc
  obtain ⟨U, V, hUV, hU, hV, hUn, hVn⟩ := hA Ω c hc
  refine ⟨U, V, hUV, ?_⟩
  intro W hW
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hW
  rcases hW with rfl | rfl | rfl
  · exact hD Ω c hc _ hU hUn
  · exact hD Ω c hc _ hV hVn
  · exact hD Ω c hc _ (inf_affine c hc hU hV) (inf_nonempty c hc hUn hVn)

def LeafDedRing : Prop := ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c →
  ∀ W : C.Opens, IsAffineOpen W → (W : Set C).Nonempty → IsDedekindDomain Γ(C, W)

theorem LeafDedOpen_of (hR : LeafDedRing) : LeafDedOpen := by
  intro Ω _ _ C c hc W hW hWn
  have hD := hR Ω c hc W hW hWn
  obtain ⟨_, _, hS⟩ := hc
  have hL : LocallyOfFiniteType c := inferInstance
  let φ : Ω →+* Γ(C, W) := (c.appLE ⊤ W le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
  letI : Algebra Ω Γ(C, W) := φ.toAlgebra
  have hφ : φ.FiniteType := by
    have h1 : (c.appLE ⊤ W le_top).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType c hL ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ (by simp)
    exact h1.comp (RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv.symm.surjective)
  exact ⟨Γ(C, W), inferInstance, hD, inferInstance, hφ, ⟨hW.isoSpec⟩⟩

def LeafTwoPts : Prop := ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c →
  ∃ p p' : C, p ≠ p' ∧ IsClosed ({p} : Set C) ∧ IsClosed ({p'} : Set C)

def LeafComplAffine : Prop := ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c →
  ∀ (p : C) (hp : IsClosed ({p} : Set C)), IsAffineOpen (⟨{p}ᶜ, hp.isOpen_compl⟩ : C.Opens)

theorem LeafAffCover_of (h2 : LeafTwoPts) (hA : LeafComplAffine) : LeafAffCover := by
  intro Ω _ _ C c hc
  obtain ⟨p, p', hne, hp, hp'⟩ := h2 Ω c hc
  refine ⟨⟨{p}ᶜ, hp.isOpen_compl⟩, ⟨{p'}ᶜ, hp'.isOpen_compl⟩, ?_, hA Ω c hc p hp, hA Ω c hc p' hp', ?_, ?_⟩
  · ext x
    simp only [TopologicalSpace.Opens.coe_sup, TopologicalSpace.Opens.coe_top, Set.mem_union, Set.mem_univ, iff_true]
    by_cases h : x = p
    · right
      subst h
      show x ∈ ({p'}ᶜ : Set C)
      simpa using hne
    · left
      show x ∈ ({p}ᶜ : Set C)
      simpa using h
  · exact ⟨p', by simpa using hne.symm⟩
  · exact ⟨p, by simpa using hne⟩

def LeafDim1 : Prop := ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c →
  ∀ W : C.Opens, IsAffineOpen W → (W : Set C).Nonempty → Ring.DimensionLEOne Γ(C, W)

def LeafNormal : Prop := ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c →
  ∀ W : C.Opens, IsAffineOpen W → (W : Set C).Nonempty → IsIntegrallyClosed Γ(C, W)

theorem leafNormal : LeafNormal := by
  intro Ω _ _ C c hc W hW hWn
  obtain ⟨hI, _, hS⟩ := hc
  have : Nonempty W := hWn.to_subtype
  have hSm : Smooth c := SmoothOfRelativeDimension.smooth 1 c
  let φ : Ω →+* Γ(C, W) := (c.appLE ⊤ W le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
  letI : Algebra Ω Γ(C, W) := φ.toAlgebra
  have hφ : φ.Smooth := by
    have h1 : (c.appLE ⊤ W le_top).hom.Smooth :=
      HasRingHomProperty.appLE @Smooth c hSm ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ (by simp)
    exact RingHom.Smooth.comp (RingHom.Smooth.of_bijective
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv.symm.bijective) h1
  have : Algebra.Smooth Ω Γ(C, W) := hφ
  exact GlobalTheory.isIntegrallyClosed_of_smooth Ω Γ(C, W)

theorem krullDim_eq_one {Ω : Type} [Field Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω) (hc : IsCurve c)
    (W : C.Opens) (hW : IsAffineOpen W) (hWn : (W : Set C).Nonempty) :
    ringKrullDim Γ(C, W) = ((1 : ℕ) : WithBot ℕ∞) := by
  have hI0 : IsIntegral C := hc.1
  have : Nonempty W := hWn.to_subtype
  have : IsDomain Γ(C, W) := inferInstance
  obtain ⟨hI, _, hS⟩ := hc
  have : Nonempty W := hWn.to_subtype
  have hL : LocallyOfFiniteType c := inferInstance
  let e : Ω ≃+* Γ(Sp Ω, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv.symm
  let ψ := (c.appLE ⊤ W le_top).hom
  let φ : Ω →+* Γ(C, W) := ψ.comp (e : Ω →+* Γ(Sp Ω, ⊤))
  letI : Algebra Ω Γ(C, W) := φ.toAlgebra
  have hφ : φ.FiniteType := by
    have h1 : ψ.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType c hL ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ (by simp)
    exact h1.comp (RingHom.FiniteType.of_surjective _ e.surjective)
  have : Algebra.FiniteType Ω Γ(C, W) := hφ
  have hloc : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1) ψ :=
    HasRingHomProperty.appLE (@SmoothOfRelativeDimension 1) c hS ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ (by simp)
  obtain ⟨s, hs, hst⟩ := hloc
  obtain ⟨t, ht, ht0⟩ : ∃ t ∈ s, t ≠ 0 := by
    by_contra h
    push Not at h
    have hle : Ideal.span s ≤ ⊥ := Ideal.span_le.mpr (fun x hx => by simp [h x hx])
    rw [hs] at hle
    exact one_ne_zero (Ideal.mem_bot.mp (hle (Submodule.mem_top : (1 : Γ(C, W)) ∈ ⊤)))
  have h1 : ((algebraMap Γ(C, W) (Localization.Away t)).comp φ).IsStandardSmoothOfRelativeDimension 1 :=
    (hst t ht).comp (RingHom.IsStandardSmoothOfRelativeDimension.equiv e)
  have hs0 : Submonoid.powers t ≤ nonZeroDivisors Γ(C, W) := powers_le_nonZeroDivisors_of_noZeroDivisors ht0
  have : IsDomain (Localization.Away t) := IsLocalization.isDomain_localization hs0
  have hEq : algebraMap Ω (Localization.Away t) = (algebraMap Γ(C, W) (Localization.Away t)).comp φ :=
    IsScalarTower.algebraMap_eq _ _ _
  rw [← hEq] at h1
  have : Algebra.IsStandardSmoothOfRelativeDimension 1 Ω (Localization.Away t) :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := 1)).mp h1
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial 1 Ω (Localization.Away t)
  have h2 := GlobalTheory.AffinePoints.trdeg_eq_of_etale g hg
  have : FaithfulSMul Γ(C, W) (Localization.Away t) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsLocalization.injective _ hs0)
  have : Algebra.IsAlgebraic Γ(C, W) (Localization.Away t) := IsLocalization.isAlgebraic _ (Submonoid.powers t)
  rw [GlobalTheory.trdeg_eq_of_isAlgebraic_top Ω Γ(C, W) (Localization.Away t)] at h2
  exact GlobalTheory.ringKrullDim_eq_of_trdeg_eq Ω Γ(C, W) h2

theorem leafDim1 : LeafDim1 := by
  intro Ω _ _ C c hc W hW hWn
  have h3 := krullDim_eq_one c hc W hW hWn
  have hI0 : IsIntegral C := hc.1
  have : Nonempty W := hWn.to_subtype
  have : IsDomain Γ(C, W) := inferInstance
  have hK : Ring.KrullDimLE 1 Γ(C, W) := Ring.krullDimLE_iff.mpr (by rw [h3])
  exact ⟨fun {P} hne hP => hP.isMaximal_of_ne_bot hne⟩

theorem LeafDedRing_of (hd : LeafDim1) (hn : LeafNormal) : LeafDedRing := by
  intro Ω _ _ C c hc W hW hWn
  have h1 := hd Ω c hc W hW hWn
  have h2 := hn Ω c hc W hW hWn
  obtain ⟨hI, _, hS⟩ := hc
  have : Nonempty W := hWn.to_subtype
  have hL : LocallyOfFiniteType c := inferInstance
  let φ : Ω →+* Γ(C, W) := (c.appLE ⊤ W le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
  letI : Algebra Ω Γ(C, W) := φ.toAlgebra
  have hφ : φ.FiniteType := by
    have h1 : (c.appLE ⊤ W le_top).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType c hL ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ (by simp)
    exact h1.comp (RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv.symm.surjective)
  have : Algebra.FiniteType Ω Γ(C, W) := hφ
  have : IsNoetherianRing Γ(C, W) := Algebra.FiniteType.isNoetherianRing Ω _
  exact { }

theorem LeafCover_of' (hA : LeafAffCover) (hR : LeafDedRing) : LeafCover :=
  LeafCover_of hA (LeafDedOpen_of hR)

theorem LeafCover_of_four (h2 : LeafTwoPts) (hA : LeafComplAffine) (hd : LeafDim1) (hn : LeafNormal) : LeafCover :=
  LeafCover_of' (LeafAffCover_of h2 hA) (LeafDedRing_of hd hn)

theorem LeafCover_of_three (h2 : LeafTwoPts) (hA : LeafComplAffine) (hd : LeafDim1) : LeafCover :=
  LeafCover_of_four h2 hA hd leafNormal

theorem leafTwoPts : LeafTwoPts := by
  intro Ω _ _ C c hc
  have hc' := hc
  obtain ⟨hI, hP, hS⟩ := hc
  have hL : LocallyOfFiniteType c := inferInstance
  have : JacobsonSpace C := LocallyOfFiniteType.jacobsonSpace c
  by_contra hne
  have hsub' : (closedPoints C).Subsingleton := fun p hp p' hp' => by
    by_contra h
    exact hne ⟨p, p', h, hp, hp'⟩
  have hcl : closure (closedPoints C) = Set.univ := closure_closedPoints
  have hsub : Subsingleton C := by
    rcases hsub'.eq_empty_or_singleton with h | ⟨p, h⟩
    · rw [h, closure_empty] at hcl
      exact ⟨fun x _ => by
        have hx : x ∈ (∅ : Set C) := hcl ▸ Set.mem_univ x
        exact absurd hx (Set.notMem_empty x)⟩
    · have hp : IsClosed ({p} : Set C) := by
        have : p ∈ closedPoints C := by rw [h]; rfl
        exact this
      rw [h, hp.closure_eq] at hcl
      exact ⟨fun x y => by
        have hx : x ∈ ({p} : Set C) := hcl ▸ Set.mem_univ x
        have hy : y ∈ ({p} : Set C) := hcl ▸ Set.mem_univ y
        rw [Set.mem_singleton_iff] at hx hy
        rw [hx, hy]⟩
  obtain ⟨x⟩ : Nonempty C := inferInstance
  obtain ⟨_, ⟨W, hW, rfl⟩, hx, -⟩ := C.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have h1 := krullDim_eq_one c hc' W hW ⟨x, hx⟩
  have hsW : Subsingleton W := ⟨fun a b => Subtype.ext (hsub.elim _ _)⟩
  have hsP : Subsingleton (PrimeSpectrum Γ(C, W)) := by
    have := hsW
    exact hW.isoSpec.inv.isOpenEmbedding.injective.subsingleton
  have hK0 : Ring.KrullDimLE 0 Γ(C, W) := Ring.KrullDimLE.mk₀ fun I hI => by
    obtain ⟨M, hM, hIM⟩ := I.exists_le_maximal hI.ne_top
    have h' : (⟨I, hI⟩ : PrimeSpectrum Γ(C, W)) = ⟨M, hM.isPrime⟩ := Subsingleton.elim _ _
    have hIM' : I = M := congrArg PrimeSpectrum.asIdeal h'
    rw [hIM']
    exact hM
  have := (Ring.krullDimLE_iff (n := 0)).mp hK0
  rw [h1] at this
  norm_num at this

theorem LeafCover_of_two (h2 : LeafTwoPts) (hA : LeafComplAffine) : LeafCover :=
  LeafCover_of_three h2 hA leafDim1

theorem LeafCover_of_one (hA : LeafComplAffine) : LeafCover :=
  LeafCover_of_two leafTwoPts hA

end LateralTheory.E.E4.CurveCut.CoverPf
