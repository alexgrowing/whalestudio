import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ResKOfResolutionPrincipalisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfIntegralKrullDimEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqOfIsIsoRestrictStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdealSheafAwayFromP
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsIntegralBlowupOfSmooth
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverOfIsPullback

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.ResK ReciprocityTheory.AnForm.R

namespace PositivityTheory.ResPlug

open GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.ResKSide

def ResW : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (M D : ℕ) (X : Scheme.{0}) (i : X ⟶ PSpace K M) (U : X.Opens),
    IsResInput M i U D →
    ∃ (X₁ : Scheme.{0}) (s : X₁ ⟶ X),
      IsProjOver (s ≫ i ≫ PSpace.str K M) ∧ Smooth (s ≫ i ≫ PSpace.str K M) ∧ IsIso (s ∣_ U) ∧
        Dense ((s ⁻¹ᵁ U : X₁.Opens) : Set X₁)

def PrincW : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (d : ℕ) (X : Scheme.{0}) (g : X ⟶ Sp K),
    SmoothOfRelativeDimension d g → IsProjOver g → ∀ U : X.Opens, Dense (U : Set X) →
    ∃ (X' : Scheme.{0}) (s : X' ⟶ X),
      IsProjOver (s ≫ g) ∧ Smooth (s ≫ g) ∧ IsIso (s ∣_ U) ∧ FinalTheorems.Snc (preRed s (U : Set X)ᶜ U.isOpen.isClosed_compl)

theorem resW_of_resolutionCharZero (H : ResolutionCharZero) : ResW := by
  intro K _ _ M D X i U ⟨hi, hred, hdense, hU⟩
  have hproj : IsProjOver (i ≫ PSpace.str K M) := ⟨M, i, hi, rfl⟩
  obtain ⟨X₁, s, -, hproj₁, hsm₁, hiso₁, hsnc₁⟩ := H.projective (i ≫ PSpace.str K M) hproj
  have : Smooth (U.ι ≫ i ≫ PSpace.str K M) := hU.smooth D _
  have hUs : U ≤ (i ≫ PSpace.str K M).smoothLocus := le_smoothLocus _ U
  have : IsIso (s ∣_ U) := isIso_morphismRestrict_of_le s hUs
  refine ⟨X₁, s, hproj₁, hsm₁, this, ?_⟩
  refine dense_preimage s (V := (i ≫ PSpace.str K M).smoothLocus) ?_ hdense
  simpa using dense_compl_of_snc _ hsnc₁

theorem princW_of_principalisationCharZero (H : PrincipalisationCharZero) : PrincW := by
  intro K _ _ d X g hd hp U hU
  have hP : IsProper g := isProper_of_isProjOver hp
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace g
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian g
  have : IsNoetherian X := by first | infer_instance | exact ⟨⟩
  have : NoetherianSpace X := inferInstance
  let I : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩
  have hIs : (I.support : Set X) = (U : Set X)ᶜ := by simp [I]
  have hI : ∀ C ∈ irreducibleComponents X, ¬ C ⊆ (I.support : Set X) :=
    SncBlowup.not_subset_of_dense_compl (by rw [hIs]; simpa using hU)
  obtain ⟨X', s, E', hseq, hsm, -, hsnc, hiso⟩ :=
    H K d X g hd inferInstance inferInstance I ⊥ hI (fun x hx => hx.elim)
  have hproj : IsProjOver (s ≫ g) :=
    (Resolution.IsBlowupSeq.of_smooth hseq.isSmoothBlowupSeq).isProjOver hp
  have hUc : I.support.compl = U := by ext x; simp [hIs]
  rw [hUc] at hiso
  refine ⟨X', s, hproj, hsm, hiso, ?_⟩
  have : (I.comap s).support = ⟨s.base ⁻¹' (U : Set X)ᶜ, U.isOpen.isClosed_compl.preimage s.base.hom.continuous⟩ := by
    apply Closeds.ext
    rw [Scheme.IdealSheafData.support_comap]
    simp [hIs]
  rw [this] at hsnc
  exact hsnc

theorem resK_of_weak (H₁ : ResW) (H₂ : PrincW) : ResKStatement := by
  intro K _ _ M D X i U hin
  obtain ⟨X₁, s, hproj₁, hsm₁, hiso₁, hd₁⟩ := H₁ K M D X i U hin
  obtain ⟨hi, hred, hdense, hU⟩ := hin
  have hD₁ : SmoothOfRelativeDimension D (s ≫ i ≫ PSpace.str K M) :=
    relDim_of_dense _ _ hd₁ (relDim_preimage s _ U hU)
  obtain ⟨X₂, t, hproj₂, hsm₂, hiso₂, hsnc₂⟩ := H₂ K D X₁ (s ≫ i ≫ PSpace.str K M) hD₁ hproj₁ (s ⁻¹ᵁ U) hd₁
  have hiso : IsIso ((t ≫ s) ∣_ U) := by
    rw [morphismRestrict_comp]; exact @IsIso.comp_isIso _ _ _ _ _ _ _ hiso₂ hiso₁
  have hT : IsClosed ((t ≫ s).base ⁻¹' (U : Set X)ᶜ) :=
    U.isOpen.isClosed_compl.preimage (t ≫ s).base.hom.continuous
  have hsncT : FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal ⟨_, hT⟩) := hsnc₂
  have hd₂ : Dense (((t ≫ s) ⁻¹ᵁ U : X₂.Opens) : Set X₂) := by
    exact Dense.mono (fun x hx => by simpa using hx) (dense_compl_of_snc _ hsncT)
  have hproj₂' : IsProjOver (t ≫ s ≫ i ≫ PSpace.str K M) := hproj₂
  have : CompactSpace X₂ := by
    have hP₂ := isProper_of_isProjOver hproj₂'
    exact QuasiCompact.compactSpace_of_compactSpace (t ≫ s ≫ i ≫ PSpace.str K M)
  have hsm : Smooth ((t ≫ s) ≫ i ≫ PSpace.str K M) := by simpa using hsm₂
  obtain ⟨hDim, hC⟩ := GlobalTheory.T.coords_statement K D X₂ ((t ≫ s) ≫ i ≫ PSpace.str K M) ((t ≫ s) ⁻¹ᵁ U) _ hT inferInstance hsm hd₂
    (relDim_preimage (t ≫ s) _ U hU) hsncT
  obtain ⟨r, j, hj, e⟩ := exists_closed_in_prod ((t ≫ s) ≫ i) (by simpa using hproj₂')
  exact ⟨r, X₂, j, t ≫ s, hj, e, hDim, hiso, hd₂, hC⟩

theorem resK_of_resolution_of_principalisation (H₁ : ResolutionCharZero) (H₂ : PrincipalisationCharZero) : ResKStatement :=
  resK_of_weak (resW_of_resolutionCharZero H₁) (princW_of_principalisationCharZero H₂)

theorem isIntegral_of_iso_dense {k : Type} [Field k] {Y Y' : Scheme.{0}} [IsIntegral Y] (s : Y' ⟶ Y) (g : Y ⟶ Sp k)
    [Smooth (s ≫ g)] (U : Y.Opens) (hU : (U : Set Y).Nonempty) [IsIso (s ∣_ U)]
    (hd : Dense ((s ⁻¹ᵁ U : Y'.Opens) : Set Y')) : IsIntegral Y' := by
  have : IsReduced Y' := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isReduced_of_smooth (s ≫ g)
  have : Nonempty U.toScheme := ⟨⟨hU.some, hU.some_mem⟩⟩
  have : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  have : Nonempty (s ⁻¹ᵁ U).toScheme := ⟨(inv (s ∣_ U)) (Nonempty.some inferInstance)⟩
  have : IsIntegral (s ⁻¹ᵁ U).toScheme := isIntegral_of_isOpenImmersion (s ∣_ U)
  have hd' : Dense (Set.range (s ⁻¹ᵁ U).ι) := by simpa using hd
  have h := ((IrreducibleSpace.isIrreducible_univ _).image _ (s ⁻¹ᵁ U).ι.continuous.continuousOn).closure
  rw [Set.image_univ, hd'.closure_eq] at h
  have : IrreducibleSpace Y' := (irreducibleSpace_def _).2 h
  exact isIntegral_of_irreducibleSpace_of_isReduced Y'

theorem isProjOver_comp_closed' {R : Type} [CommRing R] {X X' : Scheme.{0}} (g : X' ⟶ X) [IsClosedImmersion g]
    {f : X ⟶ Sp R} (hf : IsProjOver f) : IsProjOver (g ≫ f) := by
  obtain ⟨M, k, hk, rfl⟩ := hf
  exact ⟨M, g ≫ k, inferInstance, by simp⟩

theorem effCartier_comap_int {G W : Scheme.{0}} [IsIntegral W] (J : G.IdealSheafData) (t : W ⟶ G)
    (hJ : FinalTheorems.EffCartier J) {w₀ : W} (hw : t w₀ ∉ J.support) : FinalTheorems.EffCartier (J.comap t) := by
  intro w
  obtain ⟨U, f, hwU, -, hU⟩ := hJ (t w)
  obtain ⟨_, ⟨A, hA, rfl⟩, hwA, hAU⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open (show w ∈ ((t ⁻¹ᵁ U.1 : W.Opens) : Set W) from hwU) (t ⁻¹ᵁ U.1).isOpen
  have hle : A ≤ t ⁻¹ᵁ U.1 := hAU
  have e := GlobalTheory.Principalise.comapIdealAffine J t U ⟨A, hA⟩ hle
  rw [hU, Ideal.map_span, Set.image_singleton] at e
  have : Nonempty A := ⟨⟨w, hwA⟩⟩
  refine ⟨⟨A, hA⟩, _, hwA, mem_nonZeroDivisors_of_ne_zero fun h0 => ?_, e⟩
  have hd : Dense ((J.comap t).support : Set W)ᶜ :=
    (J.comap t).support.isClosed.isOpen_compl.dense ⟨w₀, fun h => hw ((GlobalTheory.ProjBlowup.mem_support_comap J t w₀).1 h)⟩
  obtain ⟨y, hyA, hy⟩ := hd.inter_open_nonempty _ A.isOpen ⟨w, hwA⟩
  refine hy ((Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨A, hA⟩) hyA).2 ?_)
  rw [e, Scheme.mem_zeroLocus_iff]
  intro a ha
  have ha0 : a = 0 := by
    have := Ideal.mem_span_singleton'.1 ha
    obtain ⟨c, rfl⟩ := this
    rw [h0, mul_zero]
  subst ha0
  simp

theorem isReduced_of_effCartier {G : Scheme.{0}} (J : G.IdealSheafData) (hJ : FinalTheorems.EffCartier J)
    [IsReduced (Scheme.Opens.toScheme J.support.compl)] : IsReduced G := by
  have key : ∀ x : G, ∃ U : G.affineOpens, x ∈ U.1 ∧ _root_.IsReduced Γ(G, U.1) := by
    intro x
    obtain ⟨U, f, hx, hf, hU⟩ := hJ x
    refine ⟨U, hx, ?_⟩
    have hle : G.basicOpen f ≤ J.support.compl := fun y hy hy' => by
      have := (Scheme.IdealSheafData.mem_support_iff_of_mem (G.basicOpen_le f hy)).1 hy'
      rw [Scheme.mem_zeroLocus_iff] at this
      exact this f (by rw [hU]; exact Ideal.subset_span rfl) hy
    have : IsReduced (G.basicOpen f).toScheme := isReduced_of_isOpenImmersion (G.homOfLE hle)
    have h1 : _root_.IsReduced Γ(G, G.basicOpen f) :=
      isReduced_of_injective (G.basicOpen f).topIso.inv.hom (G.basicOpen f).topIso.symm.commRingCatIsoToRingEquiv.injective
    have := U.2.isLocalization_basicOpen f
    exact isReduced_of_injective (algebraMap Γ(G, U.1) Γ(G, G.basicOpen f))
      (IsLocalization.injective _ (M := Submonoid.powers f) (Submonoid.powers_le.2 hf))
  have : ∀ x : G, _root_.IsReduced (G.presheaf.stalk x) := by
    intro x
    obtain ⟨U, hx, hr⟩ := key x
    let := G.presheaf.algebra_section_stalk (⟨x, hx⟩ : U.1)
    have := U.2.isLocalization_stalk ⟨x, hx⟩
    exact isReduced_localizationPreserves (U.2.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl _ hr
  exact isReduced_of_isReduced_stalk G

def PrincNeed : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (d : ℕ) (Y : Scheme.{0}) (f : Y ⟶ Sp k),
    IsIntegral Y → SmoothOfRelativeDimension d f → IsProjOver f →
    ∀ I : Y.IdealSheafData, I ≠ ⊥ →
      ∃ (Y' : Scheme.{0}) (s : Y' ⟶ Y),
        IsIntegral Y' ∧ SmoothOfRelativeDimension d (s ≫ f) ∧ IsProjOver (s ≫ f) ∧
        IsIso (s ∣_ I.support.compl) ∧ FinalTheorems.EffCartier (I.comap s)

def WeakResNeed : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (W : Scheme.{0}) [IsIntegral W] (p : W ⟶ Sp F) (n : ℕ), IsProjOver p →
    topologicalKrullDim W = n →
    ∃ (W' : Scheme.{0}) (s : W' ⟶ W) (U : W.Opens), IsIntegral W' ∧ SmoothOfRelativeDimension n (s ≫ p) ∧
      IsProjOver (s ≫ p) ∧ (U : Set W).Nonempty ∧ IsIso (s ∣_ U)

def GenSmoothDim : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (W : Scheme.{0}) [IsIntegral W] (p : W ⟶ Sp F) (n : ℕ), IsProjOver p →
    topologicalKrullDim W = n → ∃ U : W.Opens, (U : Set W).Nonempty ∧ SmoothOfRelativeDimension n (U.ι ≫ p)

theorem princNeed_of_resW (H : ResW) : PrincNeed := by
  intro k _ _ d Y f hY hd hp I hI
  obtain ⟨y, hy⟩ := GlobalTheory.Principalise.nonempty_compl_support hI
  obtain ⟨G, b, hb, hpG, hiso⟩ := GlobalTheory.ProjBlowup.exists_blowup f hp I
  have hbV : IsIso (b ∣_ I.support.compl) := hiso _ fun _ hx => hx
  have hU : (I.comap b).support.compl = b ⁻¹ᵁ I.support.compl := by
    ext y
    exact not_congr (GlobalTheory.ProjBlowup.mem_support_comap I b y)
  have : IsReduced (Scheme.Opens.toScheme (I.comap b).support.compl) := by
    rw [hU]; exact isReduced_of_isOpenImmersion (b ∣_ I.support.compl ≫ Scheme.Opens.ι _)
  have hG : IsReduced G := isReduced_of_effCartier _ hb.1
  have hdG : Dense ((b ⁻¹ᵁ I.support.compl : G.Opens) : Set G) :=
    hU ▸ GlobalTheory.CompanionTheory.BlowupIntegral.dense_compl_support_of_effCartier _ hb.1
  have hrelU : SmoothOfRelativeDimension d ((b ⁻¹ᵁ I.support.compl).ι ≫ b ≫ f) := relDim_preimage b f _ (by
      have : SmoothOfRelativeDimension (0 + d) (Scheme.Opens.ι I.support.compl ≫ f) := inferInstance
      simpa using this)
  obtain ⟨z, hz⟩ := (b ∣_ I.support.compl).homeomorph.surjective ⟨y, hy⟩
  have : Nonempty G := ⟨z.1⟩
  have hGi : IsIntegral G := GlobalTheory.CompanionTheory.BlowupIntegral.isIntegral_of_blowup I b hb
  obtain ⟨M, i, hi, e⟩ := hpG
  obtain ⟨X, t, hproj, hsm, htiso, htd⟩ := H k M d G i (b ⁻¹ᵁ I.support.compl) ⟨hi, hG, hdG, by
    rw [e]; exact hrelU⟩
  rw [e] at hproj hsm
  have hint : IsIntegral X := isIntegral_of_iso_dense t (b ≫ f) _ ⟨z.1, z.2⟩ htd
  have hrel : SmoothOfRelativeDimension d (t ≫ b ≫ f) := relDim_of_dense _ _ htd (relDim_preimage t _ _ hrelU)
  obtain ⟨w, hw⟩ := htd.nonempty
  refine ⟨X, t ≫ b, hint, by simpa using hrel, by simpa using hproj, ?_, ?_⟩
  · rw [morphismRestrict_comp]; exact @IsIso.comp_isIso _ _ _ _ _ _ _ htiso hbV
  · rw [Scheme.IdealSheafData.comap_comp]
    exact effCartier_comap_int _ t hb.1 (w₀ := w) fun h => hw ((GlobalTheory.ProjBlowup.mem_support_comap I b _).1 h)

theorem isIso_ι_restrict {W : Scheme.{0}} (U : W.Opens) : IsIso (U.ι ∣_ U) := by
  have : Surjective (U.ι ∣_ U) := ⟨fun x => by
    refine ⟨⟨⟨x.1, x.2⟩, x.2⟩, U.ι.isOpenEmbedding.injective ?_⟩
    exact (Scheme.Hom.comp_apply _ _ _).symm.trans ((congrArg (fun f : (U.ι ⁻¹ᵁ U).toScheme ⟶ W => f _) (morphismRestrict_ι U.ι U)).trans rfl)⟩
  exact (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, this⟩

theorem genSmoothDim : GenSmoothDim := by
  intro F _ _ W _ p n hp hdim
  have hP : IsProper p := isProper_of_isProjOver hp
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian p
  have : LocallyOfFinitePresentation p := inferInstance
  have hd : Dense (p.smoothLocus : Set W) := p.dense_smoothLocus_of_perfectField
  have hne : (p.smoothLocus : Set W).Nonempty := hd.nonempty
  refine ⟨p.smoothLocus, hne, ?_⟩
  have : Nonempty p.smoothLocus.toScheme := ⟨⟨hne.some, hne.some_mem⟩⟩
  have : IsIntegral p.smoothLocus.toScheme := isIntegral_of_isOpenImmersion p.smoothLocus.ι
  have hsm : Smooth (p.smoothLocus.ι ≫ p) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    simp
  refine GlobalTheory.T.smoothOfRelativeDimension_of_integral_krullDim_eq F _ _ n hsm ?_
  rw [← hdim]
  exact GlobalTheory.T.topologicalKrullDim_eq_of_isIso_restrict' F W _ p (p.smoothLocus.ι ≫ p) p.smoothLocus.ι inferInstance inferInstance rfl p.smoothLocus hne (isIso_ι_restrict _)

theorem weakResNeed_of_resW (H : ResW) : WeakResNeed := by
  intro F _ _ W _ p n hp hdim
  obtain ⟨U, hU, hUn⟩ := genSmoothDim F W p n hp hdim
  obtain ⟨M, i, hi, rfl⟩ := hp
  obtain ⟨W', s, hproj, hsm, hiso, hd⟩ := H F M n W i U ⟨hi, inferInstance, U.isOpen.dense hU, hUn⟩
  exact ⟨W', s, U, isIntegral_of_iso_dense s (i ≫ PSpace.str F M) U hU hd,
    relDim_of_dense _ _ hd (relDim_preimage s _ U hUn), hproj, hU, hiso⟩

theorem needs_of_weak (H₁ : ResW) (H₂ : PrincW) : ResKStatement ∧ PrincNeed ∧ WeakResNeed :=
  ⟨resK_of_weak H₁ H₂, princNeed_of_resW H₁, weakResNeed_of_resW H₁⟩

theorem resW_of_resK (H : ResKStatement) : ResW := by
  intro K _ _ M D X i U hin
  obtain ⟨r, X', j, f, hj, e, hD, hiso, hd, -⟩ := H K M D X i U hin
  refine ⟨X', f, ?_, hD.smooth D _, hiso, hd⟩
  rw [reassoc_of% e]
  exact isProjOver_comp_closed' j (GlobalTheory.ProjSpace.isProjOver_pullback_str K M r)

theorem needs_of_resK (H : ResKStatement) : ResKStatement ∧ PrincNeed ∧ WeakResNeed :=
  ⟨H, princNeed_of_resW (resW_of_resK H), weakResNeed_of_resW (resW_of_resK H)⟩

end PositivityTheory.ResPlug
