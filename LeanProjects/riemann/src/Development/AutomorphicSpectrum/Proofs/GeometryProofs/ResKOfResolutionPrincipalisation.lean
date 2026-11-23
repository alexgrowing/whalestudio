import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.ConclusionOfSmooth
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NotSubsetOfDenseCompl
import Development.AutomorphicSpectrum.PublishedTheorems.PublishedGlobalResults.PrincipalizationOfPrincipalisation
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsStatementStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.ResK ReciprocityTheory.AnForm.R

namespace GlobalTheory.CompanionTheory.Hypotheses₂.ResKSide

theorem le_smoothLocus {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyOfFinitePresentation f] (U : X.Opens)
    [Smooth (U.ι ≫ f)] : U ≤ f.smoothLocus := by
  intro x hx
  have := (U.ι ≫ f).smoothLocus_eq_top.ge (Set.mem_univ (⟨x, hx⟩ : U))
  rw [← Scheme.Hom.preimage_smoothLocus_eq] at this
  exact this

theorem dense_preimage {X Y : Scheme.{0}} (f : X ⟶ Y) {U V : Y.Opens} [IsIso (f ∣_ V)]
    (hV : Dense ((f ⁻¹ᵁ V : X.Opens) : Set X)) (hU : Dense (U : Set Y)) :
    Dense ((f ⁻¹ᵁ U : X.Opens) : Set X) := by
  rw [dense_iff_inter_open]
  intro O hO hne
  obtain ⟨p, hpO, hpV⟩ := hV.inter_open_nonempty O hO hne
  let O' : Set (f ⁻¹ᵁ V) := (f ⁻¹ᵁ V).ι.base ⁻¹' O
  have hO' : IsOpen O' := hO.preimage (f ⁻¹ᵁ V).ι.base.hom.continuous
  have hopen : IsOpen (V.ι.base '' ((f ∣_ V).base '' O')) :=
    V.ι.isOpenEmbedding.isOpenMap _ ((f ∣_ V).isOpenEmbedding.isOpenMap _ hO')
  have hp' : (⟨p, hpV⟩ : f ⁻¹ᵁ V) ∈ O' := hpO
  obtain ⟨y, ⟨q, ⟨p', hp'O, rfl⟩, rfl⟩, hyU⟩ := hU.inter_open_nonempty _ hopen ⟨_, _, ⟨_, hp', rfl⟩, rfl⟩
  refine ⟨(f ⁻¹ᵁ V).ι p', hp'O, ?_⟩
  show f ((f ⁻¹ᵁ V).ι p') ∈ U
  rw [← Scheme.Hom.comp_apply, ← morphismRestrict_ι, Scheme.Hom.comp_apply]
  exact hyU

theorem relDim_preimage {X Y S : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ S) (U : Y.Opens) [IsIso (f ∣_ U)] {D : ℕ}
    (h : SmoothOfRelativeDimension D (U.ι ≫ g)) : SmoothOfRelativeDimension D ((f ⁻¹ᵁ U).ι ≫ f ≫ g) := by
  have : SmoothOfRelativeDimension (0 + D) ((f ∣_ U) ≫ U.ι ≫ g) := inferInstance
  rw [zero_add] at this
  rw [← morphismRestrict_ι_assoc]
  exact this

theorem relDim_of_dense {Y S : Scheme.{0}} (g : Y ⟶ S) [Smooth g] (W : Y.Opens) (hW : Dense (W : Set Y)) {D : ℕ}
    (h : SmoothOfRelativeDimension D (W.ι ≫ g)) : SmoothOfRelativeDimension D g := by
  choose n W' hW' hd using ReciprocityTheory.ChartRestriction.G.H1.exists_dim g
  have key : ∀ x, n x = D := by
    intro x
    obtain ⟨y, hyW', hyW⟩ := hW.inter_open_nonempty (W' x) (W' x).isOpen ⟨x, hW' x⟩
    have := hd x
    have e₁ : SmoothOfRelativeDimension (0 + n x) ((W' x ⊓ W).ι ≫ g) := by
      rw [← Scheme.homOfLE_ι _ (inf_le_left : W' x ⊓ W ≤ W' x), Category.assoc]; infer_instance
    have e₂ : SmoothOfRelativeDimension (0 + D) ((W' x ⊓ W).ι ≫ g) := by
      rw [← Scheme.homOfLE_ι _ (inf_le_right : W' x ⊓ W ≤ W), Category.assoc]; infer_instance
    simpa using ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ e₁ e₂ ⟨y, hyW', hyW⟩
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension D) := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension D) W'
    (top_le_iff.1 fun x _ => Opens.mem_iSup.2 ⟨x, hW' x⟩) fun x => ?_
  rw [← key x]; exact hd x

theorem isProper_of_isProjOver {K : Type} [Field K] {Y : Scheme.{0}} {h : Y ⟶ Sp K} (hp : IsProjOver h) :
    IsProper h := by
  obtain ⟨N, i, hi, rfl⟩ := hp
  have : IsProper (PSpace.str K N) := isProper_str K N
  infer_instance

end GlobalTheory.CompanionTheory.Hypotheses₂.ResKSide

namespace GlobalTheory.CompanionTheory.Hypotheses₂.ResKSide

theorem resK_of_resolution_principalisation (H₁ : ResolutionCharZero) (H₂ : PrincipalisationCharZero) :
    ResKStatement := by
  intro K _ _ M D X i U ⟨hi, hred, hdense, hU⟩
  have hproj : IsProjOver (i ≫ PSpace.str K M) := ⟨M, i, hi, rfl⟩
  have hP : IsProper (i ≫ PSpace.str K M) := isProper_of_isProjOver hproj
  obtain ⟨X₁, s, hs, hproj₁, hsm₁, hiso₁, hsnc₁⟩ := H₁.projective (i ≫ PSpace.str K M) hproj
  have : Smooth (U.ι ≫ i ≫ PSpace.str K M) := hU.smooth D _
  have hUs : U ≤ (i ≫ PSpace.str K M).smoothLocus := le_smoothLocus _ U
  have : IsIso (s ∣_ U) := isIso_morphismRestrict_of_le s hUs
  have hd₁ : Dense ((s ⁻¹ᵁ U : X₁.Opens) : Set X₁) := by
    refine dense_preimage s (V := (i ≫ PSpace.str K M).smoothLocus) ?_ hdense
    simpa using dense_compl_of_snc _ hsnc₁
  have hP₁ : IsProper (s ≫ i ≫ PSpace.str K M) := isProper_of_isProjOver hproj₁
  have hD₁ : SmoothOfRelativeDimension D (s ≫ i ≫ PSpace.str K M) :=
    relDim_of_dense _ _ hd₁ (relDim_preimage s _ U hU)
  let I : X₁.IdealSheafData := preRed s (U : Set X)ᶜ U.isOpen.isClosed_compl
  have hIs : (I.support : Set X₁) = s.base ⁻¹' (U : Set X)ᶜ := by
    simp [I, preRed]
  have : CompactSpace X₁ := by
    first
    | exact QuasiCompact.compactSpace_of_compactSpace (s ≫ i ≫ PSpace.str K M)
    | exact (quasiCompact_over_affine_iff (s ≫ i ≫ PSpace.str K M)).mp inferInstance
  have : IsLocallyNoetherian X₁ := by
    first
    | exact LocallyOfFiniteType.isLocallyNoetherian (s ≫ i ≫ PSpace.str K M)
    | infer_instance
  have : IsNoetherian X₁ := by first | infer_instance | exact ⟨⟩
  have : NoetherianSpace X₁ := inferInstance
  have hI : ∀ C ∈ irreducibleComponents X₁, ¬ C ⊆ (I.support : Set X₁) := by
    refine SncBlowup.not_subset_of_dense_compl ?_
    rw [hIs]; simpa using hd₁
  obtain ⟨X₂, t, E', hseq, hsm₂, hcart, hsnc₂, hiso₂⟩ :=
    H₂ K D X₁ (s ≫ i ≫ PSpace.str K M) hD₁ inferInstance inferInstance I ⊥ hI (fun x hx => hx.elim)
  have hsupp : ((I.comap t).support : Set X₂) = (t ≫ s).base ⁻¹' (U : Set X)ᶜ := by
    rw [Scheme.IdealSheafData.support_comap]
    simp [hIs] <;> rfl
  have hUc : I.support.compl = s ⁻¹ᵁ U := by
    ext x
    simp [hIs]
  rw [hUc] at hiso₂
  have hiso : IsIso ((t ≫ s) ∣_ U) := by rw [morphismRestrict_comp]; exact @IsIso.comp_isIso _ _ _ _ _ _ _ hiso₂ (isIso_morphismRestrict_of_le s hUs)
  have hT : IsClosed ((t ≫ s).base ⁻¹' (U : Set X)ᶜ) :=
    U.isOpen.isClosed_compl.preimage (t ≫ s).base.hom.continuous
  have hsncT : FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal ⟨_, hT⟩) := by
    have e : (I.comap t).support = ⟨_, hT⟩ := Closeds.ext hsupp
    rwa [e] at hsnc₂
  have hd₂ : Dense (((t ≫ s) ⁻¹ᵁ U : X₂.Opens) : Set X₂) := by
    exact Dense.mono (fun x hx => by simpa using hx) (dense_compl_of_snc _ hsncT)
  have hproj₂ : IsProjOver (t ≫ s ≫ i ≫ PSpace.str K M) :=
    (Resolution.IsBlowupSeq.of_smooth hseq.isSmoothBlowupSeq).isProjOver hproj₁
  have hP₂ := isProper_of_isProjOver hproj₂
  have : CompactSpace X₂ := by
    first
    | exact QuasiCompact.compactSpace_of_compactSpace (t ≫ s ≫ i ≫ PSpace.str K M)
    | exact (quasiCompact_over_affine_iff (t ≫ s ≫ i ≫ PSpace.str K M)).mp inferInstance
  have hsm : Smooth ((t ≫ s) ≫ i ≫ PSpace.str K M) := by simpa using hsm₂
  obtain ⟨hDim, hC⟩ := GlobalTheory.T.coords_statement K D X₂ ((t ≫ s) ≫ i ≫ PSpace.str K M) ((t ≫ s) ⁻¹ᵁ U) _ hT inferInstance hsm hd₂
    (relDim_preimage (t ≫ s) _ U hU) hsncT
  obtain ⟨r, j, hj, e⟩ := exists_closed_in_prod ((t ≫ s) ≫ i) (by simpa using hproj₂)
  exact ⟨r, X₂, j, t ≫ s, hj, e, hDim, hiso, hd₂, hC⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.ResKSide
