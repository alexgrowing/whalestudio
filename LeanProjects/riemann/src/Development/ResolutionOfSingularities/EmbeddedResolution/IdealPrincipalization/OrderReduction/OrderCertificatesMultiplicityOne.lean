import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactHypersurface
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheafBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.CertificateOpenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationCertificateMonotone
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationCertificate
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MarkedSchemeWithCenter
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.PrincipalizationCenter
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.TunedMarkedBlowupSeq
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BoundarySeparation
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.CoverTriple
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DescentHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DerivedAndCoverTriples
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.EmptyOrderLocusAfterReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactCoverProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.OrderCertificates
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactHypersurfaceTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem orderCertificate_congr_morphism_ideal_center {k : Type u} [Field k] {W : Scheme.{u}}
    {p p' : W ⟶ Spec (CommRingCat.of k)} {N N' : W.IdealSheafData} {μ : ℕ} {Mem : Set ↥W}
    {Z Z' : W.IdealSheafData} (hp : p = p') (hN : N = N') (hZ : Z = Z')
    (h : OrderCertificate W p N μ Mem Z) : OrderCertificate W p' N' μ Mem Z' := by
  subst hp
  subst hN
  subst hZ
  exact h

private theorem principalizationCertificate_congr_mult {k : Type u} [Field k] {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} {m m' : ℕ} {Mem : Set ↥W}
    {Z : W.IdealSheafData} (hm : m = m') (h : PrincipalizationCertificate W p I m Mem Z) :
    PrincipalizationCertificate W p I m' Mem Z := by
  subst hm
  exact h

private theorem mem_boundarySupport_of_mem_support_of_mem_boundary {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (s : MarkedBlowupSequenceData p I m E) (i : ℕ) (J : (s.obj i).IdealSheafData)
    (hJ : J ∈ s.boundary i) (x : ↥(s.obj i))
    (hx : x ∈ (J.support : Set ↥(s.obj i))) : x ∈ (s.dataAt i).boundarySupport := by
  refine (MarkedSchemeWithCenter.mem_boundarySupport_iff (s.dataAt i) x).2 ⟨J, ?_, hx⟩
  rw [MarkedBlowupSequenceData.dataAt_boundary]
  exact hJ

private theorem get_zero_of_eq_cons {α : Type _} (l : List α) (a : α) (L : List α)
    (hl : l = a :: L) (h0 : 0 < l.length) : l.get ⟨0, h0⟩ = a := by
  subst hl
  rfl

private theorem get_mem_of_eq_cons_of_ne_zero {α : Type _} (l : List α) (a : α) (L : List α)
    (hl : l = a :: L) (idx : Fin l.length) (hidx : (idx : ℕ) ≠ 0) : l.get idx ∈ L := by
  subst hl
  obtain ⟨n, hn⟩ := idx
  cases n with
  | zero => exact absurd rfl hidx
  | succ m =>
      have hm : m < L.length := by simpa using hn
      show L.get ⟨m, hm⟩ ∈ L
      simp

private theorem controlledTransform_eq_ideal_of_eq {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (s : MarkedSequenceOfBlowups p I m E) (I' : X.IdealSheafData) (m' : ℕ)
    (hI : I' = I) (hm : m' = m) (i : ℕ) (hi : i ≤ s.length) :
    (BlowupSequenceData.ofSequenceOfBlowups s.toSequenceOfBlowups).controlledTransform I' m' i = s.ideal i := by
  subst hI
  subst hm
  exact MarkedBlowupSequenceData.ofMarkedSequence_controlledTransform s i hi

private theorem isMaxContactHypersurface_congr {k : Type u} [Field k] {X : Scheme.{u}}
    (p p' : X ⟶ Spec (CommRingCat.of k))
    (hfp : LocallyOfFiniteType p) (hfp' : LocallyOfFiniteType p')
    {A A' H H' : X.IdealSheafData} {μ μ' : ℕ}
    (hp : p = p') (hA : A = A') (hH : H = H') (hμ : μ = μ')
    (hyp : @IsMaxContactHypersurface k _ X p hfp A μ H) :
    @IsMaxContactHypersurface k _ X p' hfp' A' μ' H' := by
  subst hp
  subst hA
  subst hH
  subst hμ
  exact hyp

private theorem balancedTunedSheaf_eq_of_mult_eq_one {k : Type u} [Field k] [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (hfp : LocallyOfFiniteType p)
    (I : X.IdealSheafData) (m : ℕ) (hm : m = 1) :
    @FunctorialResolution.EmbeddedResolution.balancedTunedSheaf k _ _ X p hfp I m = I := by
  subst hm
  exact FunctorialResolution.EmbeddedResolution.balancedTunedSheaf_one k p I

private theorem support_ideal_subset_iteratedStrictTransform (hstar : MaxContactCoverProperties.{u}) (S : MarkedIdealWithBoundary.{u})
    (hv : S.IsAdmissible) [LocallyOfFiniteType S.structMap]
    (hord : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ ((S.mult : ℕ) : ℕ∞)) (hm1 : S.mult = 1)
    (H : S.scheme.IdealSheafData)
    (hH : IsMaxContactHypersurface S.base S.structMap S.ideal S.mult H)
    (u : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary) (t : ℕ) (ht : t ≤ u.length)
    (hfti : LocallyOfFiniteType (u.proj t ≫ S.structMap))
    (hsmt : Smooth (u.proj t ≫ S.structMap))
    (hczs : CharZero S.base) :
    ((u.ideal t).support : Set ↥(u.obj t))
      ⊆ ((u.toBlowupSequenceData.iteratedStrictTransform t H).support : Set ↥(u.obj t)) := by
  have := hfti
  have := hsmt
  have := hczs
  have hadm := isMaxContactHypersurface_iteratedStrictTransform hstar S hv hord H hH u t ht
  have hsub := hadm.orderAtLeastLocus_subset_support (le_of_eq hm1.symm)
  rw [BoundarySeparationByMaxContact.iteratedStrictTransform_eq_toBlowupSequenceData u H t] at hsub
  intro x hx
  apply hsub
  rw [FunctorialResolution.EmbeddedResolution.mem_orderAtLeastLocus_iff]
  have hcoe : ((S.mult : ℕ) : ℕ∞) = 1 := by simp [hm1]
  rw [hcoe]
  exact (FunctorialResolution.EmbeddedResolution.one_le_orderAt_iff_mem_support (u.ideal t) x).2 hx

private theorem orderCertificate_one_of_isSmoothDivisor {k : Type u} [Field k] {W : Scheme.{u}}
    (hin : OpenImmersionStability k) (p : W ⟶ Spec (CommRingCat.of k))
    (N : W.IdealSheafData) (Mem : Set ↥W) (Z : W.IdealSheafData) (Dv : W.IdealSheafData)
    (hDsm : IsSmoothDivisor p Dv)
    (hNsupp : (↑N.support : Set ↥W) ⊆ (↑Dv.support : Set ↥W))
    (hZH : (↑Z.support : Set ↥W) ⊆ (↑Dv.support : Set ↥W))
    (hcase : IsOpen (⇑Dv.subschemeι ⁻¹' (↑Z.support : Set ↥W)) ∨
      ∃ J : Dv.subscheme.IdealSheafData, NonzeroOnComponents J ∧
        (∀ x : ↥Dv.subscheme, Dv.subschemeι x ∉ Mem →
          ∃ V : Dv.subscheme.Opens, x ∈ V ∧
            J.comap V.ι = (N.comap Dv.subschemeι).comap V.ι) ∧
        PrincipalizationCertificate Dv.subscheme (Dv.subschemeι ≫ p) J 1 (⇑Dv.subschemeι ⁻¹' Mem)
          (Z.comap Dv.subschemeι)) :
    OrderCertificate W p N 1 Mem Z := by
  have hoi : IsOpenImmersion (comapSubscheme (⊤ : W.Opens).ι Dv) :=
    hin.isOpenImmersion_comapSubscheme _ _
  have hkey : ∀ x : ↥(Dv.comap (⊤ : W.Opens).ι).subscheme,
      (⊤ : W.Opens).ι ((Dv.comap (⊤ : W.Opens).ι).subschemeι x)
        = Dv.subschemeι ((comapSubscheme (⊤ : W.Opens).ι Dv) x) := by
    intro x
    have hc := comapSubscheme_comp (⊤ : W.Opens).ι Dv
    have h2 := congrArg
      (fun f : (Dv.comap (⊤ : W.Opens).ι).subscheme ⟶ W => f.base x) hc
    simpa using h2.symm
  have hNH' : ∀ y, y ∈ (N.comap (⊤ : W.Opens).ι).support →
      y ∈ (Dv.comap (⊤ : W.Opens).ι).support := by
    intro y hy
    rw [FunctorialResolution.EmbeddedResolution.mem_comap_support_iff_base_mem_support] at hy ⊢
    exact hNsupp hy
  have hZH' : ∀ y, y ∈ (Z.comap (⊤ : W.Opens).ι).support →
      y ∈ (Dv.comap (⊤ : W.Opens).ι).support := by
    intro y hy
    rw [FunctorialResolution.EmbeddedResolution.mem_comap_support_iff_base_mem_support] at hy ⊢
    exact hZH hy
  rcases hcase with hop | ⟨J, hJnz, hJloc, hJcert⟩
  · refine OrderCertificate.descend (fun _ _ => ⊤) (fun _ _ => trivial)
      (fun _ _ => Dv.comap (⊤ : W.Opens).ι)
      (fun _ _ => hin.comap_isSmoothDivisor _ p Dv hDsm)
      (fun _ _ => hNH') (fun _ _ => hZH')
      (fun _ _ => none) ?_ ?_ ?_ ?_
    · intro _ _ _
      have key : IsOpen (⇑(comapSubscheme (⊤ : W.Opens).ι Dv) ⁻¹'
          (⇑Dv.subschemeι ⁻¹' (↑Z.support : Set ↥W))) :=
        ((comapSubscheme (⊤ : W.Opens).ι Dv) ⁻¹ᵁ
          (⟨_, hop⟩ : Dv.subscheme.Opens)).isOpen
      convert key using 1
      ext x
      simp only [Set.mem_preimage]
      rw [← hkey x]
      exact FunctorialResolution.EmbeddedResolution.mem_comap_support_iff_base_mem_support (⊤ : W.Opens).ι Z _
    · intro _ _ _ hJz; exact absurd hJz (by simp)
    · intro _ _ _ hJz; exact absurd hJz (by simp)
    · intro _ _ _ hJz; exact absurd hJz (by simp)
  · refine OrderCertificate.descend (fun _ _ => ⊤) (fun _ _ => trivial)
      (fun _ _ => Dv.comap (⊤ : W.Opens).ι)
      (fun _ _ => hin.comap_isSmoothDivisor _ p Dv hDsm)
      (fun _ _ => hNH') (fun _ _ => hZH')
      (fun _ _ => some (J.comap (comapSubscheme (⊤ : W.Opens).ι Dv))) ?_ ?_ ?_ ?_
    · intro _ _ hcon; exact absurd hcon (by simp)
    · intro _ _ Jz hJz
      obtain rfl : Jz = J.comap (comapSubscheme (⊤ : W.Opens).ι Dv) := by simpa using hJz.symm
      exact hin.comap_nonzeroOnComponents _ J hJnz
    · intro _ _ Jz hJz x hx
      obtain rfl : Jz = J.comap (comapSubscheme (⊤ : W.Opens).ι Dv) := by simpa using hJz.symm
      have hx' : Dv.subschemeι ((comapSubscheme (⊤ : W.Opens).ι Dv) x) ∉ Mem := by
        intro hc
        apply hx
        have hkx := hkey x
        simpa [hkx] using hc
      obtain ⟨V, hV, hVeq⟩ := hJloc _ hx'
      refine ⟨(comapSubscheme (⊤ : W.Opens).ι Dv) ⁻¹ᵁ V, hV, ?_⟩
      have e1 : ((comapSubscheme (⊤ : W.Opens).ι Dv) ⁻¹ᵁ V).ι
            ≫ comapSubscheme (⊤ : W.Opens).ι Dv
          = Scheme.Hom.resLE (comapSubscheme (⊤ : W.Opens).ι Dv) V
              ((comapSubscheme (⊤ : W.Opens).ι Dv) ⁻¹ᵁ V) le_rfl ≫ V.ι :=
        (Scheme.Hom.resLE_comp_ι _ _).symm
      calc (J.comap (comapSubscheme (⊤ : W.Opens).ι Dv)).comap
              ((comapSubscheme (⊤ : W.Opens).ι Dv) ⁻¹ᵁ V).ι
          = J.comap (((comapSubscheme (⊤ : W.Opens).ι Dv) ⁻¹ᵁ V).ι
              ≫ comapSubscheme (⊤ : W.Opens).ι Dv) :=
              (Scheme.IdealSheafData.comap_comp _ _ _).symm
        _ = J.comap (Scheme.Hom.resLE (comapSubscheme (⊤ : W.Opens).ι Dv) V
              ((comapSubscheme (⊤ : W.Opens).ι Dv) ⁻¹ᵁ V) le_rfl ≫ V.ι) := by rw [e1]
        _ = (J.comap V.ι).comap (Scheme.Hom.resLE (comapSubscheme (⊤ : W.Opens).ι Dv) V
              ((comapSubscheme (⊤ : W.Opens).ι Dv) ⁻¹ᵁ V) le_rfl) :=
              Scheme.IdealSheafData.comap_comp _ _ _
        _ = ((N.comap Dv.subschemeι).comap V.ι).comap
              (Scheme.Hom.resLE (comapSubscheme (⊤ : W.Opens).ι Dv) V
                ((comapSubscheme (⊤ : W.Opens).ι Dv) ⁻¹ᵁ V) le_rfl) := by rw [hVeq]
        _ = (N.comap Dv.subschemeι).comap
              (Scheme.Hom.resLE (comapSubscheme (⊤ : W.Opens).ι Dv) V
                ((comapSubscheme (⊤ : W.Opens).ι Dv) ⁻¹ᵁ V) le_rfl ≫ V.ι) :=
              (Scheme.IdealSheafData.comap_comp _ _ _).symm
        _ = (N.comap Dv.subschemeι).comap
              (((comapSubscheme (⊤ : W.Opens).ι Dv) ⁻¹ᵁ V).ι
                ≫ comapSubscheme (⊤ : W.Opens).ι Dv) := by rw [e1]
        _ = ((N.comap Dv.subschemeι).comap (comapSubscheme (⊤ : W.Opens).ι Dv)).comap
              ((comapSubscheme (⊤ : W.Opens).ι Dv) ⁻¹ᵁ V).ι :=
              Scheme.IdealSheafData.comap_comp _ _ _
        _ = (N.comap (comapSubscheme (⊤ : W.Opens).ι Dv ≫ Dv.subschemeι)).comap
              ((comapSubscheme (⊤ : W.Opens).ι Dv) ⁻¹ᵁ V).ι := by
              rw [Scheme.IdealSheafData.comap_comp]
        _ = (N.comap ((Dv.comap (⊤ : W.Opens).ι).subschemeι ≫ (⊤ : W.Opens).ι)).comap
              ((comapSubscheme (⊤ : W.Opens).ι Dv) ⁻¹ᵁ V).ι := by
              rw [comapSubscheme_comp]
        _ = ((N.comap (⊤ : W.Opens).ι).comap (Dv.comap (⊤ : W.Opens).ι).subschemeι).comap
              ((comapSubscheme (⊤ : W.Opens).ι Dv) ⁻¹ᵁ V).ι := by
              rw [Scheme.IdealSheafData.comap_comp]
    · intro _ _ Jz hJz
      obtain rfl : Jz = J.comap (comapSubscheme (⊤ : W.Opens).ι Dv) := by simpa using hJz.symm
      have hpc := PrincipalizationCertificate.comap_of_openImmersionStability hin hJcert
        (comapSubscheme (⊤ : W.Opens).ι Dv)
      have e2 : comapSubscheme (⊤ : W.Opens).ι Dv ≫ (Dv.subschemeι ≫ p)
          = (Dv.comap (⊤ : W.Opens).ι).subschemeι ≫ ((⊤ : W.Opens).ι ≫ p) :=
        comapSubscheme_comp_assoc _ _ _
      have e3 : (⇑(comapSubscheme (⊤ : W.Opens).ι Dv) ⁻¹' (⇑Dv.subschemeι ⁻¹' Mem))
          = ⇑((Dv.comap (⊤ : W.Opens).ι).subschemeι ≫ (⊤ : W.Opens).ι) ⁻¹' Mem := by
        ext x
        simp only [Set.mem_preimage]
        rw [← hkey x]
        simp
      have e4 : (Z.comap Dv.subschemeι).comap (comapSubscheme (⊤ : W.Opens).ι Dv)
          = (Z.comap (⊤ : W.Opens).ι).comap (Dv.comap (⊤ : W.Opens).ι).subschemeι := by
        rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
          comapSubscheme_comp]
      rw [e2, e3, e4] at hpc
      exact hpc

namespace BoundarySeparationByMaxContact

theorem continuationOrderCertificate_of_mult_eq_one (hstar : MaxContactCoverProperties.{u})
    (hopen : ∀ (k : Type u) [Field k], OpenImmersionStability k)
    (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop)
    (hmono : ∀ a b : ℕ, a ≤ b → P b → P a) (A : ℕ → PrincipalizationAssignment.{u})
    (B : PrincipalizationAssignment.{u}) (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B)
    (T : MarkedIdealWithBoundary.{u}) (h : MaxContactFunctoriality.OrderReductionHypotheses P T) (hmult : T.mult = 1) :
    ContinuationOrderCertificate hinv A P T h := by
  intro hft hmk i hi
  have hftI : LocallyOfFiniteType ((separateAllBoundary T h.valid hinv A).proj
      (separateAllBoundary T h.valid hinv A).length ≫
      (MaxContactCoverData.coverTriple T h.valid).structMap) := hft
  have hSV : (MaxContactCoverData.coverTriple T h.valid).IsAdmissible := isAdmissible_coverTriple hstar P T h
  have hSO : ∀ x : ↥(MaxContactCoverData.coverTriple T h.valid).scheme,
      orderAt (MaxContactCoverData.coverTriple T h.valid).ideal x
        ≤ (((MaxContactCoverData.coverTriple T h.valid).mult : ℕ) : ℕ∞) :=
    orderAt_coverTriple_ideal_le_mult hstar P T h
  have hS1 : (MaxContactCoverData.coverTriple T h.valid).mult = 1 := by
    simp [MaxContactCoverData.coverTriple_mult, MaxContactCoverData.tunedMult, hmult, FunctorialResolution.EmbeddedResolution.tuningExponent_one]
  have honeLe : 1 ≤ (MaxContactCoverData.coverTriple T h.valid).mult := le_of_eq hS1.symm
  have hcz : CharZero (MaxContactCoverData.coverTriple T h.valid).base := hSV.charZero
  have hsm0 : Smooth ((separateAllBoundary T h.valid hinv A).proj
      (separateAllBoundary T h.valid hinv A).length ≫
      (MaxContactCoverData.coverTriple T h.valid).structMap) :=
    smooth_projectionToBase_comp hstar (MaxContactCoverData.coverTriple T h.valid) hSV
      (separateAllBoundary T h.valid hinv A) (separateAllBoundary T h.valid hinv A).length le_rfl
  have hAdmCover := isMaxContactHypersurface_coverMaxContactIdeal hstar P T h
  have hAdmT := isMaxContactHypersurface_iteratedStrictTransform hstar
    (MaxContactCoverData.coverTriple T h.valid) hSV hSO (MaxContactCoverData.coverMaxContactIdeal T h.valid)
    hAdmCover (separateAllBoundary T h.valid hinv A) (separateAllBoundary T h.valid hinv A).length le_rfl
  have heqT : MaxContactReduction.iteratedStrictTransform (separateAllBoundary T h.valid hinv A)
      (MaxContactCoverData.coverMaxContactIdeal T h.valid) (separateAllBoundary T h.valid hinv A).length
      = MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid) :=
    (MaxContactReduction.strictTransformAtLength_eq _ _).symm
  have hAdm0 : IsMaxContactHypersurface (MaxContactCoverData.coverTriple T h.valid).base
      ((separateAllBoundary T h.valid hinv A).proj (separateAllBoundary T h.valid hinv A).length ≫
        (MaxContactCoverData.coverTriple T h.valid).structMap)
      ((separateAllBoundary T h.valid hinv A).ideal (separateAllBoundary T h.valid hinv A).length)
      (MaxContactCoverData.coverTriple T h.valid).mult
      (MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid)) :=
    isMaxContactHypersurface_congr
      ((separateAllBoundary T h.valid hinv A).proj (separateAllBoundary T h.valid hinv A).length ≫
        (MaxContactCoverData.coverTriple T h.valid).structMap)
      ((separateAllBoundary T h.valid hinv A).proj (separateAllBoundary T h.valid hinv A).length ≫
        (MaxContactCoverData.coverTriple T h.valid).structMap)
      hftI hftI rfl rfl heqT rfl hAdmT
  obtain ⟨_, hV2, hP2, _, _, _⟩ := exists_cover_eq_separateAllBoundary_append hstar hinv P hmono A B hspec T h
  have hV' : (reduceAlongHypersurfaceTriple T h.valid hinv A hft).IsAdmissible := hV2
  have hP' : P (reduceAlongHypersurfaceTriple T h.valid hinv A hft).krullDimSucc := hP2
  have hftT : LocallyOfFiniteType (reduceAlongHypersurfaceTriple T h.valid hinv A hft).structMap := by
    rw [MaxContactCoverData.derivedTriple_structureMorphism]; exact hft
  have hcz2 : CharZero (reduceAlongHypersurfaceTriple T h.valid hinv A hft).base := hV'.charZero
  have hOB : (reduceAlongHypersurfaceTriple T h.valid hinv A hft).IsOrderBoundedByMult :=
    LowerDimReductionPullback.isOrderBoundedByMult_derivedTriple hstar (MaxContactCoverData.coverTriple T h.valid) hSV honeLe hSO
      (separateAllBoundary T h.valid hinv A) hft
      [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
      (MaxContactCoverData.coverTriple T h.valid).boundary.length hV'
  have hbalanced : (reduceAlongHypersurfaceTriple T h.valid hinv A hft).IsBalanced hftT :=
    LowerDimReductionPullback.isBalanced_derivedTriple hstar (MaxContactCoverData.coverTriple T h.valid) hSV honeLe hSO
      (separateAllBoundary T h.valid hinv A) hft
      [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
      (MaxContactCoverData.coverTriple T h.valid).boundary.length hV'
  have hbd : (reduceAlongHypersurfaceTriple T h.valid hinv A hft).boundary
      = MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
          (MaxContactCoverData.coverMaxContactIdeal T h.valid)
        :: List.drop (MaxContactCoverData.coverTriple T h.valid).boundary.length
            ((separateAllBoundary T h.valid hinv A).boundary
              (separateAllBoundary T h.valid hinv A).length) :=
    MaxContactCoverData.derivedTriple_boundary _ _ _ _ _
  have hjlen : 0 < (reduceAlongHypersurfaceTriple T h.valid hinv A hft).boundary.length := by
    rw [hbd]; simp
  obtain ⟨D, b, hDsm, hD0, hcenter, hbtrue, hDsucc, _hDfin, hJsh⟩ :=
    (hspec 0).shape (reduceAlongHypersurfaceTriple T h.valid hinv A hft) hV' hP' hOB hbalanced hjlen
  have hmu : FunctorialResolution.EmbeddedResolution.tuningExponent (MaxContactCoverData.coverTriple T h.valid).mult
      = (reduceAlongHypersurfaceTriple T h.valid hinv A hft).mult :=
    (MaxContactCoverData.derivedTriple_mult _ _ _ _ _).symm
  have hpeq : ((separateAllBoundary T h.valid hinv A).proj
      (separateAllBoundary T h.valid hinv A).length ≫
      (MaxContactCoverData.coverTriple T h.valid).structMap)
      = (reduceAlongHypersurfaceTriple T h.valid hinv A hft).structMap :=
    (MaxContactCoverData.derivedTriple_structureMorphism _ _ _ _ _).symm
  have htm : FunctorialResolution.EmbeddedResolution.tuningExponent (MaxContactCoverData.coverTriple T h.valid).mult = 1 := by
    rw [hS1]; exact FunctorialResolution.EmbeddedResolution.tuningExponent_one
  have hMultOne : (reduceAlongHypersurfaceTriple T h.valid hinv A hft).mult = 1 := hmu.symm.trans htm
  have hIdeal : (reduceAlongHypersurfaceTriple T h.valid hinv A hft).ideal
      = LowerDimReductionPullback.tunedIdealAtLength (MaxContactCoverData.coverTriple T h.valid)
        (separateAllBoundary T h.valid hinv A) hft :=
    LowerDimReductionPullback.ideal_derivedTriple _ _ hft _ _
  have hIdeal2 : LowerDimReductionPullback.tunedIdealAtLength (MaxContactCoverData.coverTriple T h.valid)
        (separateAllBoundary T h.valid hinv A) hft
      = FunctorialResolution.EmbeddedResolution.balancedTunedSheaf (MaxContactCoverData.coverTriple T h.valid).base
        ((separateAllBoundary T h.valid hinv A).proj (separateAllBoundary T h.valid hinv A).length ≫
          (MaxContactCoverData.coverTriple T h.valid).structMap)
        ((separateAllBoundary T h.valid hinv A).ideal (separateAllBoundary T h.valid hinv A).length)
        (MaxContactCoverData.coverTriple T h.valid).mult :=
    LowerDimReductionPullback.tunedIdealAtLength_eq_balancedTunedSheaf _ _ hft
  have hIdealEq : (reduceAlongHypersurfaceTriple T h.valid hinv A hft).ideal
      = (separateAllBoundary T h.valid hinv A).ideal (separateAllBoundary T h.valid hinv A).length :=
    (hIdeal.trans hIdeal2).trans
      (balancedTunedSheaf_eq_of_mult_eq_one
        ((separateAllBoundary T h.valid hinv A).proj
          (separateAllBoundary T h.valid hinv A).length ≫
          (MaxContactCoverData.coverTriple T h.valid).structMap)
        hftI
        ((separateAllBoundary T h.valid hinv A).ideal (separateAllBoundary T h.valid hinv A).length)
        (MaxContactCoverData.coverTriple T h.valid).mult hS1)
  have hOrderLe : ∀ x : ↥(reduceAlongHypersurfaceTriple T h.valid hinv A hft).scheme,
      orderAt (reduceAlongHypersurfaceTriple T h.valid hinv A hft).ideal x
        ≤ (((reduceAlongHypersurfaceTriple T h.valid hinv A hft).mult : ℕ) : ℕ∞) :=
    (MarkedIdealWithBoundary.isOrderBoundedByMult_iff _).1 hOB
  have hord : ∀ x : ↥((separateAllBoundary T h.valid hinv A).obj
      (separateAllBoundary T h.valid hinv A).length),
      orderAt ((separateAllBoundary T h.valid hinv A).ideal
        (separateAllBoundary T h.valid hinv A).length) x
        ≤ (((MaxContactCoverData.coverTriple T h.valid).mult : ℕ) : ℕ∞) :=
    LowerDimReductionPullback.orderAt_ideal_length_le hstar (MaxContactCoverData.coverTriple T h.valid) hSV hSO
      (separateAllBoundary T h.valid hinv A)
  have key := isMaxContactHypersurface_balancedTunedSheaf hstar (MaxContactCoverData.coverTriple T h.valid).base
    ((separateAllBoundary T h.valid hinv A).proj (separateAllBoundary T h.valid hinv A).length ≫
      (MaxContactCoverData.coverTriple T h.valid).structMap)
    ((separateAllBoundary T h.valid hinv A).ideal (separateAllBoundary T h.valid hinv A).length)
    (MaxContactCoverData.coverTriple T h.valid).mult honeLe hord
    (MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
      (MaxContactCoverData.coverMaxContactIdeal T h.valid)) hAdm0
  have hMaxContactHyp : IsMaxContactHypersurface (reduceAlongHypersurfaceTriple T h.valid hinv A hft).base
      (reduceAlongHypersurfaceTriple T h.valid hinv A hft).structMap
      (reduceAlongHypersurfaceTriple T h.valid hinv A hft).ideal
      (reduceAlongHypersurfaceTriple T h.valid hinv A hft).mult
      (MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid)) :=
    isMaxContactHypersurface_congr
      ((separateAllBoundary T h.valid hinv A).proj (separateAllBoundary T h.valid hinv A).length ≫
        (MaxContactCoverData.coverTriple T h.valid).structMap)
      (reduceAlongHypersurfaceTriple T h.valid hinv A hft).structMap hftI hftT hpeq
      (hIdeal.trans hIdeal2).symm rfl hmu key
  have hNoe : ∀ t, t ≤ (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).length →
      IsLocallyNoetherian ((BlowupSequenceData.ofSequenceOfBlowups
        (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups).obj t) := fun t ht =>
    isLocallyNoetherian_tunedMarkedBlowupSeq_schemeAt hstar (MaxContactCoverData.coverTriple T h.valid) hSV
      (separateAllBoundary T h.valid hinv A) hft
      [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
      (MaxContactCoverData.coverTriple T h.valid).boundary.length hV'
      (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) t ht
  have hb0 : (reduceAlongHypersurfaceTriple T h.valid hinv A hft).boundary.get ⟨0, hjlen⟩
      = MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid) :=
    get_zero_of_eq_cons _ _ _ hbd hjlen
  have hi' : i ≤ (MarkedBlowupSequenceData.ofMarkedSequence
      (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft))).length := by
    rw [MarkedBlowupSequenceData.ofMarkedSequence_length]
    exact le_of_lt hi
  have hK0 : D 0 = (MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
      (MaxContactCoverData.coverMaxContactIdeal T h.valid)).comap
      (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).isoZero.hom :=
    hD0.trans (congrArg (fun J => J.comap
      (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).isoZero.hom) hb0)
  have hKstep : ∀ t < (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).length,
      D (t + 1) = Blowup.strictTransform ((A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).transitionMapSucc t)
          ((A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).center t) (D t)
        ∨ D (t + 1) = (D t).comap
          ((A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).transitionMapSucc t) := by
    intro t htlen
    by_cases hbc : b = true ∧ t = 0
    · obtain ⟨hbt, ht0⟩ := hbc
      subst ht0
      exact Or.inr (hbtrue hbt).2.2
    · exact Or.inl (hDsucc t htlen hbc)
  have hNsub : (↑((A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).ideal i).support :
        Set ↥((A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).schemeAt i))
      ⊆ ↑(D i).support := by
    intro x hx
    have h1 := support_ideal_subset_iteratedStrictTransform hstar (reduceAlongHypersurfaceTriple T h.valid hinv A hft) hV'
      hOrderLe hMultOne
      (MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid)) hMaxContactHyp
      (MarkedBlowupSequenceData.ofMarkedSequence (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft))) i hi'
      (locallyOfFiniteType_projectionToBase_comp hstar (reduceAlongHypersurfaceTriple T h.valid hinv A hft) hV'
        (MarkedBlowupSequenceData.ofMarkedSequence (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft))) i hi')
      (smooth_projectionToBase_comp hstar (reduceAlongHypersurfaceTriple T h.valid hinv A hft) hV'
        (MarkedBlowupSequenceData.ofMarkedSequence (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft))) i hi')
      hcz2 hx
    exact BlowupSequenceData.support_iteratedStrictTransform_subset_support
      (MarkedBlowupSequenceData.ofMarkedSequence (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft))).toBlowupSequenceData
      hNoe
      (MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid)) D hK0 hKstep i hi' h1
  have hctrl : (BlowupSequenceData.ofSequenceOfBlowups
      (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups).controlledTransform
      ((separateAllBoundary T h.valid hinv A).ideal (separateAllBoundary T h.valid hinv A).length)
      (MaxContactCoverData.coverTriple T h.valid).mult i
      = (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).ideal i :=
    controlledTransform_eq_ideal_of_eq (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft))
      ((separateAllBoundary T h.valid hinv A).ideal (separateAllBoundary T h.valid hinv A).length)
      (MaxContactCoverData.coverTriple T h.valid).mult hIdealEq.symm (hS1.trans hMultOne.symm) i (le_of_lt hi)
  have hctrlR : (continuationMarkedData (MaxContactCoverData.coverTriple T h.valid)
        (separateAllBoundary T h.valid hinv A) hft
        [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
          (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
        (MaxContactCoverData.coverTriple T h.valid).boundary.length
        (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) hmk).controlledTransform
      ((separateAllBoundary T h.valid hinv A).ideal (separateAllBoundary T h.valid hinv A).length)
      (MaxContactCoverData.coverTriple T h.valid).mult i
      = (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).ideal i := hctrl
  have hidR : (continuationMarkedData (MaxContactCoverData.coverTriple T h.valid)
      (separateAllBoundary T h.valid hinv A) hft
      [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
      (MaxContactCoverData.coverTriple T h.valid).boundary.length
      (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) hmk).ideal i
      = (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).ideal i :=
    (MarkedBlowupSequenceData.toBlowupSequenceData_controlledTransform_eq
      (continuationMarkedData (MaxContactCoverData.coverTriple T h.valid)
        (separateAllBoundary T h.valid hinv A) hft
        [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
          (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
        (MaxContactCoverData.coverTriple T h.valid).boundary.length
        (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) hmk) i (le_of_lt hi)).symm.trans hctrlR
  have hid : ((continuationMarkedData (MaxContactCoverData.coverTriple T h.valid)
      (separateAllBoundary T h.valid hinv A) hft
      [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
      (MaxContactCoverData.coverTriple T h.valid).boundary.length
      (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) hmk).dataAt i).ideal
      = (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).ideal i :=
    (MarkedBlowupSequenceData.dataAt_ideal
      (continuationMarkedData (MaxContactCoverData.coverTriple T h.valid)
        (separateAllBoundary T h.valid hinv A) hft
        [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
          (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
        (MaxContactCoverData.coverTriple T h.valid).boundary.length
        (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) hmk) i).trans hidR
  have hceR : (continuationMarkedData (MaxContactCoverData.coverTriple T h.valid)
      (separateAllBoundary T h.valid hinv A) hft
      [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
      (MaxContactCoverData.coverTriple T h.valid).boundary.length
      (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) hmk).center i
      = (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).center i :=
    BlowupSequenceData.ofSequenceOfBlowups_center (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups i
  have hce : ((continuationMarkedData (MaxContactCoverData.coverTriple T h.valid)
      (separateAllBoundary T h.valid hinv A) hft
      [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
      (MaxContactCoverData.coverTriple T h.valid).boundary.length
      (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) hmk).dataAt i).center
      = (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).center i :=
    (MarkedBlowupSequenceData.dataAt_center
      (continuationMarkedData (MaxContactCoverData.coverTriple T h.valid)
        (separateAllBoundary T h.valid hinv A) hft
        [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
          (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
        (MaxContactCoverData.coverTriple T h.valid).boundary.length
        (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) hmk) i).trans hceR
  have hprojR : (continuationMarkedData (MaxContactCoverData.coverTriple T h.valid)
      (separateAllBoundary T h.valid hinv A) hft
      [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
      (MaxContactCoverData.coverTriple T h.valid).boundary.length
      (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) hmk).proj i
      = (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).projectionToBase i :=
    BlowupSequenceData.ofSequenceOfBlowups_projectionToBase (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups i
  have hstm : ((continuationMarkedData (MaxContactCoverData.coverTriple T h.valid)
      (separateAllBoundary T h.valid hinv A) hft
      [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
      (MaxContactCoverData.coverTriple T h.valid).boundary.length
      (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) hmk).dataAt i).structMap
      = MarkedSequenceOfBlowups.projectionToSpec (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) i :=
    ((MarkedBlowupSequenceData.dataAt_structMap
      (continuationMarkedData (MaxContactCoverData.coverTriple T h.valid)
        (separateAllBoundary T h.valid hinv A) hft
        [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
          (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
        (MaxContactCoverData.coverTriple T h.valid).boundary.length
        (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) hmk) i).trans
      (congrArg (fun f => f ≫ ((separateAllBoundary T h.valid hinv A).proj
        (separateAllBoundary T h.valid hinv A).length ≫
        (MaxContactCoverData.coverTriple T h.valid).structMap)) hprojR)).trans
      ((congrArg (fun g => (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).projectionToBase i ≫ g)
            hpeq).trans
        (MarkedSequenceOfBlowups.projectionToSpec_eq (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) i).symm)
  have hAb : (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).boundary i
      = (BlowupSequenceData.ofSequenceOfBlowups (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups).boundaryFrom
          (reduceAlongHypersurfaceTriple T h.valid hinv A hft).boundary i :=
    (MarkedBlowupSequenceData.ofMarkedSequence_boundary (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) i
      (le_of_lt hi)).symm
  have hAb2 : (BlowupSequenceData.ofSequenceOfBlowups
        (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups).boundaryFrom
        (reduceAlongHypersurfaceTriple T h.valid hinv A hft).boundary i
      = (BlowupSequenceData.ofSequenceOfBlowups (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups).boundaryFrom
          (MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
            (MaxContactCoverData.coverMaxContactIdeal T h.valid)
            :: List.drop (MaxContactCoverData.coverTriple T h.valid).boundary.length
              ((separateAllBoundary T h.valid hinv A).boundary
                (separateAllBoundary T h.valid hinv A).length)) i :=
    congrArg (fun E => (BlowupSequenceData.ofSequenceOfBlowups
      (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups).boundaryFrom E i) hbd
  have hAb3 : (BlowupSequenceData.ofSequenceOfBlowups
        (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups).boundaryFrom
        (MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
          (MaxContactCoverData.coverMaxContactIdeal T h.valid)
          :: List.drop (MaxContactCoverData.coverTriple T h.valid).boundary.length
            ((separateAllBoundary T h.valid hinv A).boundary
              (separateAllBoundary T h.valid hinv A).length)) i
      = (BlowupSequenceData.ofSequenceOfBlowups
          (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups).iteratedStrictTransform i
          (MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
            (MaxContactCoverData.coverMaxContactIdeal T h.valid))
        :: (BlowupSequenceData.ofSequenceOfBlowups (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups).boundaryFrom
            (List.drop (MaxContactCoverData.coverTriple T h.valid).boundary.length
              ((separateAllBoundary T h.valid hinv A).boundary
                (separateAllBoundary T h.valid hinv A).length)) i :=
    BlowupSequenceData.boundary_cons _ _ _ i
  have hAb4 : (BlowupSequenceData.ofSequenceOfBlowups
        (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups).boundaryFrom
        (List.drop (MaxContactCoverData.coverTriple T h.valid).boundary.length
          ((separateAllBoundary T h.valid hinv A).boundary
            (separateAllBoundary T h.valid hinv A).length)) i
      = List.map ((BlowupSequenceData.ofSequenceOfBlowups
            (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups).iteratedStrictTransform i)
          (List.drop (MaxContactCoverData.coverTriple T h.valid).boundary.length
            ((separateAllBoundary T h.valid hinv A).boundary
              (separateAllBoundary T h.valid hinv A).length))
        ++ (BlowupSequenceData.ofSequenceOfBlowups
            (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups).boundaryFrom [] i :=
    BlowupSequenceData.boundary_eq_map_iteratedStrictTransform_append _ _ i
  have hAfull : (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).boundary i
      = (BlowupSequenceData.ofSequenceOfBlowups
          (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups).iteratedStrictTransform i
          (MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
            (MaxContactCoverData.coverMaxContactIdeal T h.valid))
        :: (List.map ((BlowupSequenceData.ofSequenceOfBlowups
              (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups).iteratedStrictTransform i)
            (List.drop (MaxContactCoverData.coverTriple T h.valid).boundary.length
              ((separateAllBoundary T h.valid hinv A).boundary
                (separateAllBoundary T h.valid hinv A).length))
          ++ (BlowupSequenceData.ofSequenceOfBlowups
              (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups).boundaryFrom [] i) :=
    (hAb.trans hAb2).trans (hAb3.trans (congrArg (fun l =>
      (BlowupSequenceData.ofSequenceOfBlowups (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups).iteratedStrictTransform i
        (MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
          (MaxContactCoverData.coverMaxContactIdeal T h.valid)) :: l) hAb4))
  have hRb : (continuationMarkedData (MaxContactCoverData.coverTriple T h.valid)
      (separateAllBoundary T h.valid hinv A) hft
      [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
      (MaxContactCoverData.coverTriple T h.valid).boundary.length
      (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) hmk).boundary i
      = List.map ((BlowupSequenceData.ofSequenceOfBlowups
            (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups).iteratedStrictTransform i)
          ((separateAllBoundary T h.valid hinv A).boundary
            (separateAllBoundary T h.valid hinv A).length)
        ++ (BlowupSequenceData.ofSequenceOfBlowups
            (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups).boundaryFrom [] i :=
    (MarkedBlowupSequenceData.toBlowupSequenceData_boundary_eq_boundary_of_le
      (continuationMarkedData (MaxContactCoverData.coverTriple T h.valid)
        (separateAllBoundary T h.valid hinv A) hft
        [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
          (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
        (MaxContactCoverData.coverTriple T h.valid).boundary.length
        (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) hmk) i (le_of_lt hi)).symm.trans
      (BlowupSequenceData.boundary_eq_map_iteratedStrictTransform_append
        (BlowupSequenceData.ofSequenceOfBlowups (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups)
        ((separateAllBoundary T h.valid hinv A).boundary
          (separateAllBoundary T h.valid hinv A).length) i)
  have hOther : MarkedSequenceOfBlowups.otherBoundaryLocus
      (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) 0 i
      ⊆ ((continuationMarkedData (MaxContactCoverData.coverTriple T h.valid)
          (separateAllBoundary T h.valid hinv A) hft
          [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
            (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
          (MaxContactCoverData.coverTriple T h.valid).boundary.length
          (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) hmk).dataAt i).boundarySupport := by
    intro x hx
    obtain ⟨idx, hidx, hxs⟩ :=
      (MarkedSequenceOfBlowups.mem_otherBoundaryLocus_iff
        (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) 0 i x).1 hx
    have hmem := get_mem_of_eq_cons_of_ne_zero _ _ _ hAfull idx hidx
    have hmem2 : ((A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).boundary i).get idx
        ∈ (continuationMarkedData (MaxContactCoverData.coverTriple T h.valid)
            (separateAllBoundary T h.valid hinv A) hft
            [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
              (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
            (MaxContactCoverData.coverTriple T h.valid).boundary.length
            (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) hmk).boundary i := by
      rw [hRb]
      rcases List.mem_append.1 hmem with h1 | h2
      · obtain ⟨y, hy, hfy⟩ := List.mem_map.1 h1
        exact List.mem_append.2 (Or.inl (List.mem_map.2 ⟨y, List.mem_of_mem_drop hy, hfy⟩))
      · exact List.mem_append.2 (Or.inr h2)
    exact mem_boundarySupport_of_mem_support_of_mem_boundary _ i _ hmem2 x hxs
  have hmain : OrderCertificate ((A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).schemeAt i)
      (MarkedSequenceOfBlowups.projectionToSpec (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) i)
      ((A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).ideal i) 1
      ((continuationMarkedData (MaxContactCoverData.coverTriple T h.valid)
          (separateAllBoundary T h.valid hinv A) hft
          [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
            (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
          (MaxContactCoverData.coverTriple T h.valid).boundary.length
          (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) hmk).dataAt i).boundarySupport
      ((A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).center i) := by
    refine orderCertificate_one_of_isSmoothDivisor (hopen (reduceAlongHypersurfaceTriple T h.valid hinv A hft).base) _ _ _ _ (D i)
      (hDsm i (le_of_lt hi)) hNsub (hcenter i hi) ?_
    by_cases hbc : b = true ∧ i = 0
    · left
      obtain ⟨hbt, hi0⟩ := hbc
      subst hi0
      exact (hbtrue hbt).2.1
    · right
      obtain ⟨J, hJnz, hJl, hJc⟩ := hJsh i hi hbc
      refine ⟨J, hJnz, ?_, ?_⟩
      · intro x hxm
        exact hJl x (fun hc => hxm (hOther hc))
      · exact principalizationCertificate_mono_of_subset (Set.preimage_mono hOther)
          (principalizationCertificate_congr_mult hMultOne hJc)
  exact orderCertificate_congr_morphism_ideal_center hstm.symm hid.symm hce.symm hmain

theorem orderCertificate_coverMarkedBlowupData_of_mult_eq_one (hstar : MaxContactCoverProperties.{u})
    (hopen : ∀ (k : Type u) [Field k], OpenImmersionStability k)
    (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop)
    (hmono : ∀ a b : ℕ, a ≤ b → P b → P a) (A : ℕ → PrincipalizationAssignment.{u})
    (B : PrincipalizationAssignment.{u}) (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B)
    (T : MarkedIdealWithBoundary.{u}) (h : MaxContactFunctoriality.OrderReductionHypotheses P T) (hmult : T.mult = 1) (t : ℕ)
    (ht : t <
      (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (MaxContactFunctoriality.lowerDimensionalFamily A T)).length) :
    OrderCertificate
      ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv
        (MaxContactFunctoriality.lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.schemeAt t)
      ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv
          (MaxContactFunctoriality.lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.projectionToBase t ≫
        (MaxContactCoverData.coverTriple T h.valid).structMap)
      ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv
        (MaxContactFunctoriality.lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.ideal t) 1
      ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv
        (MaxContactFunctoriality.lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.boundaryLocus t)
      ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv
        (MaxContactFunctoriality.lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.center t) :=
  orderCertificate_coverMarkedBlowupData hstar hinv P hmono A B hspec T h
    (continuationOrderCertificate_of_mult_eq_one hstar hopen hinv P hmono A B hspec T h hmult) hmult t ht

end BoundarySeparationByMaxContact

end FunctorialResolution.EmbeddedResolution

end
