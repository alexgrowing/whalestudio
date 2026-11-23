import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Adj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalModelTrivializingBlowup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalModelNonvanishingWeights
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorBundleMapDeterminedGeneric
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionOfIsIsoRestrict

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
open GlobalTheory.VB (IsVB IsSubbundle)
open GlobalTheory.FlagChain (Le)

namespace GlobalTheory.FlagPairCommon

theorem preservesMonomorphisms_pullback {X Y : Scheme.{0}} (j : X ⟶ Y) [IsOpenImmersion j] :
    (Scheme.Modules.pullback j).PreservesMonomorphisms := by
  have : (Scheme.Modules.restrictFunctor j).PreservesMonomorphisms := ⟨fun {F G} φ _ =>
    mono_of_locally_app_injective _ fun W x hx => ⟨W, hx, le_rfl, app_injective_of_mono φ (j ''ᵁ W)⟩⟩
  exact Functor.preservesMonomorphisms.of_iso (Scheme.Modules.restrictFunctorIsoPullback j)

theorem preservesFiniteLimits_pullback {X Y : Scheme.{0}} (j : X ⟶ Y) [IsOpenImmersion j] :
    PreservesFiniteLimits (Scheme.Modules.pullback j) := by
  have := preservesMonomorphisms_pullback j
  have := (Scheme.Modules.pullback j).preservesHomology_of_preservesMonos_and_cokernels
  exact (Scheme.Modules.pullback j).preservesFiniteLimits_of_preservesHomology

theorem effCartier_comap {X Y : Scheme.{0}} [IsIntegral Y] (g : Y ⟶ X) {I : X.IdealSheafData}
    (hI : ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier I) {y : Y} (hy : g y ∉ I.support) :
    ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (I.comap g) := by
  obtain ⟨D, rfl⟩ := EffCartierData.exists_idealSheaf_eq hI
  exact (D.keepsRegular_iff_effCartier g).1 (D.keepsRegular_of_notMem_support g hy)

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem charZero_residueField [CharZero O] (B : Model O) {y : B.X} (hy : y ∈ B.gen) :
    CharZero (B.X.residueField y) := by
  refine charZero_of_injective_ringHom (R := O)
    (f := (B.X.evaluation ⊤ y trivial).hom.comp (algebraMap O Γ(B.X, ⊤))) ?_
  rw [injective_iff_map_eq_zero]
  intro g hg
  by_contra h0
  exact (B.X.evaluation_ne_zero_iff_mem_basicOpen (U := ⊤) y trivial (B.const g)).2
    (B.gen_le_basicOpen h0 hy) hg

theorem exists_effCartier [CharZero O] (B : Model O) (hn : GlobalTheory.IsNormalScheme B.X) (J : B.X.IdealSheafData)
    (hJ : genericPoint B.X ∉ J.support) :
    ∃ (B' : Model O) (f : Model.Hom B' B), f.f (genericPoint B'.X) = genericPoint B.X ∧
      GlobalTheory.IsNormalScheme B'.X ∧ f.relDim = 0 ∧ ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (J.comap f.f) := by
  let U : B.X.Opens := J.support.compl ⊓ B.gen
  have hηU : genericPoint B.X ∈ U := ⟨hJ, B.genericPoint_mem_gen⟩
  obtain ⟨X'', b, hb, hbs, hiso⟩ := GlobalTheory.ProjBlowup.exists_blowup B.str B.isProjOver J
  have hbU : IsIso (b ∣_ U) := hiso U fun x hx => hx.1
  have e₀ : (b ⁻¹ᵁ U).ι ≫ b = b ∣_ U ≫ U.ι := (morphismRestrict_ι b U).symm
  have : IsOpenImmersion ((b ⁻¹ᵁ U).ι ≫ b) := by rw [e₀]; infer_instance
  have : Flat ((b ⁻¹ᵁ U).ι ≫ b ≫ B.str) := by rw [← Category.assoc]; infer_instance
  have hV : GlobalTheory.IsNormalScheme (b ⁻¹ᵁ U).toScheme := .of_isOpenImmersion ((b ⁻¹ᵁ U).ι ≫ b)
  obtain ⟨N, ν, hfin, hN, hpr, hfl, hν, hd⟩ :=
    GlobalTheory.ProjBlowup.exists_normal_model (b ≫ B.str) (b ⁻¹ᵁ U) hbs hV.pred fun x => by
      have hy : ((b ⁻¹ᵁ U).ι ≫ b) x ∈ U := x.2
      have := charZero_residueField B hy.2
      exact charZero_of_injective_ringHom (((b ⁻¹ᵁ U).ι ≫ b).residueFieldMap x).hom.injective
  have hνb : IsIso ((ν ≫ b) ∣_ U) := by
    rw [morphismRestrict_comp]; exact IsIso.comp_isIso' hν hbU
  have : Nonempty U := ⟨⟨_, hηU⟩⟩
  have : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  obtain ⟨c, hpb, hjr⟩ := GlobalTheory.ProjBlowup.exists_section_of_isIso_restrict (ν ≫ b) U
  have hjd : Dense (Set.range c) := hd.mono hjr
  have hirr : IsIrreducible (Set.range c) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image c c.continuous.continuousOn
  have : IrreducibleSpace N := (irreducibleSpace_def N).2 (by simpa [hjd.closure_eq] using hirr.closure)
  have hN' : GlobalTheory.IsNormalScheme N := .of_pred hN
  have : IsReduced N := isReduced_of_isReduced_stalk N
  have : IsIntegral N := isIntegral_of_irreducibleSpace_of_isReduced N
  have : IsOpenImmersion c := MorphismProperty.of_isPullback hpb.flip (inferInstance : IsOpenImmersion U.ι)
  have hc₁ : c ≫ ν ≫ b = U.ι := by simpa using hpb.w
  let B' : Model O := { X := N, str := ν ≫ b ≫ B.str, isProjOver := hpr }
  have hstr : (ν ≫ b) ≫ B.str = B'.str := Category.assoc ..
  have : IsProper (ν ≫ b) := Model.isProper_of_comp_str (Z := B) (Z₁ := B') hstr
  have hcη : c (genericPoint U) = genericPoint N := genericPoint_eq_of_isOpenImmersion c
  have hη : (ν ≫ b) (genericPoint N) = genericPoint B.X := by
    rw [← hcη, ← Scheme.Hom.comp_apply, hc₁]
    exact genericPoint_eq_of_isOpenImmersion U.ι
  have : IsDominant (ν ≫ b) := ⟨(dense_iff_closure_eq.2 (genericPoint_spec B.X)).mono
    (Set.singleton_subset_iff.2 ⟨_, hη⟩)⟩
  have : Surjective (ν ≫ b) :=
    surjective_of_isDominant_of_isClosed_range _ (ν ≫ b).isClosedMap.isClosed_range
  let f : Model.Hom B' B := ⟨ν ≫ b, hstr⟩
  have hdeg : (ν ≫ b).residueDegree (genericPoint N) ≠ 0 := by
    have e := CurveDegreesCompare.residueDegree_comp c (ν ≫ b) (genericPoint U)
    rw [hc₁, CurveDegreesCompare.residueDegree_of_isOpenImmersion, hcη] at e
    exact left_ne_zero_of_mul_eq_one e.symm
  have hdim : B'.relDim ≤ B.relDim := by
    have h := GlobalTheory.ProperCover.dim_le_of_residueDegree_pos (Z' := B'.X) (Z := B.X) (ν ≫ b) hη
      (Nat.pos_of_ne_zero hdeg)
    rw [B'.dim_eq, B.dim_eq] at h
    have h' : B'.relDim + 1 ≤ B.relDim + 1 := by exact_mod_cast h
    omega
  refine ⟨B', f, hη, hN', Nat.sub_eq_zero_of_le hdim, ?_⟩
  change ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (J.comap (ν ≫ b))
  rw [Scheme.IdealSheafData.comap_comp]
  refine effCartier_comap ν hb.1 (y := genericPoint N) fun h => hJ ?_
  rw [← hη]
  exact (ProjBlowup.mem_support_comap J b _).1 h

theorem exists_effCartier₂ [CharZero O] (B : Model O) (hn : GlobalTheory.IsNormalScheme B.X) (J J' : B.X.IdealSheafData)
    (hJ : genericPoint B.X ∉ J.support) (hJ' : genericPoint B.X ∉ J'.support) :
    ∃ (B' : Model O) (f : Model.Hom B' B), GlobalTheory.IsNormalScheme B'.X ∧ f.relDim = 0 ∧
      ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (J.comap f.f) ∧ ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (J'.comap f.f) := by
  obtain ⟨B₁, f₁, h₁, n₁, d₁, c₁⟩ := exists_effCartier B hn J hJ
  obtain ⟨B₂, f₂, h₂, n₂, d₂, c₂⟩ := exists_effCartier B₁ n₁ (J'.comap f₁.f)
    fun h => hJ' (h₁ ▸ (ProjBlowup.mem_support_comap J' f₁.f _).1 h)
  refine ⟨B₂, f₂.comp f₁, n₂, FlagPairExists.relDim_comp f₁ f₂ d₁ d₂, ?_, ?_⟩
  · change ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (J.comap (f₂.f ≫ f₁.f))
    rw [Scheme.IdealSheafData.comap_comp]
    refine effCartier_comap f₂.f c₁ (y := genericPoint B₂.X) fun h => hJ ?_
    rw [← h₁, ← h₂]
    exact (ProjBlowup.mem_support_comap J f₁.f _).1 h
  · change ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (J'.comap (f₂.f ≫ f₁.f))
    rw [Scheme.IdealSheafData.comap_comp]
    exact c₂

theorem kernel_subbundle {X Y : Scheme.{0}} [IsIntegral Y] (ρ : Y ⟶ X) {E L : X.Modules} (a : E ⟶ L) {n : ℕ}
    (hE : IsVB E (n + 1)) (hL : IsVB L 1) [IsFiniteQC (cokernel a)]
    (h : ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier ((annihilatorSheaf (cokernel a)).comap ρ)) :
    IsSubbundle (kernel.ι ((Scheme.Modules.pullback ρ).map a)) ∧
      IsVB (kernel ((Scheme.Modules.pullback ρ).map a)) n :=
  VB.isSubbundle_kernel_of_locally_principal Y _ _ _ n (hE.pullback ρ) (hL.pullback ρ)
    (VB.exists_image_principal_of_effCartier X Y ρ E L a _ hE hL h)

theorem le_kernel {X Y : Scheme.{0}} (ρ : Y ⟶ X) {F G H E : X.Modules} (s : F ⟶ G) (u : H ⟶ G) (t : G ⟶ E)
    {i : F ⟶ E} (hi : s ≫ t = i) [Mono ((Scheme.Modules.pullback ρ).map u)] :
    Le (kernel.ι ((Scheme.Modules.pullback ρ).map (s ≫ cokernel.π u)) ≫ (Scheme.Modules.pullback ρ).map i)
      ((Scheme.Modules.pullback ρ).map (u ≫ t)) := by
  have h₃ : (kernel.ι ((Scheme.Modules.pullback ρ).map (s ≫ cokernel.π u)) ≫
      (Scheme.Modules.pullback ρ).map s) ≫ cokernel.π ((Scheme.Modules.pullback ρ).map u) = 0 := by
    rw [← cancel_mono (cokernelComparison u (Scheme.Modules.pullback ρ)), Category.assoc,
      π_comp_cokernelComparison, Category.assoc, ← Functor.map_comp, kernel.condition, zero_comp]
  refine ⟨Abelian.monoLift _ _ h₃, ?_⟩
  rw [Functor.map_comp _ u, Abelian.monoLift_comp_assoc, Category.assoc, ← Functor.map_comp, hi]

theorem exists_genIso_cokernel {B : Model O} {H G H' G' : B.X.Modules} (u : H ⟶ G) (u' : H' ⟶ G')
    (ψ : B.GenIso H H') (γ : B.GenIso G G') (h : B.genRes.map u ≫ γ.hom = ψ.hom ≫ B.genRes.map u') :
    ∃ l : B.GenIso (cokernel u) (cokernel u'),
      γ.hom ≫ B.genRes.map (cokernel.π u') = B.genRes.map (cokernel.π u) ≫ l.hom :=
  ⟨PreservesCokernel.iso B.genRes u ≪≫ cokernel.mapIso _ _ ψ γ h ≪≫ (PreservesCokernel.iso B.genRes u').symm,
    by simp⟩

theorem exists_genIso_kernel {B : Model O} {F L F' L' : B.X.Modules} (a : F ⟶ L) (a' : F' ⟶ L')
    (γ : B.GenIso F F') (l : B.GenIso L L') (h : γ.hom ≫ B.genRes.map a' = B.genRes.map a ≫ l.hom) :
    ∃ χ : B.GenIso (kernel a) (kernel a'),
      χ.hom ≫ B.genRes.map (kernel.ι a') = B.genRes.map (kernel.ι a) ≫ γ.hom := by
  have := preservesFiniteLimits_pullback B.gen.ι
  exact ⟨PreservesKernel.iso B.genRes a ≪≫ kernel.mapIso _ _ γ l h.symm ≪≫ (PreservesKernel.iso B.genRes a').symm,
    by simp⟩

theorem exists_common_pair : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (E E' : B.X.Modules) (φ : B.GenIso E E') (r : ℕ) (P : GlobalTheory.Vert.Model.FlagPair φ r) (n : ℕ) (hn : n + 1 < r) (H H' : B.X.Modules) (κ : H ⟶ E) (κ' : H' ⟶ E') (ψ : B.GenIso H H'), GlobalTheory.VB.IsSubbundle κ → GlobalTheory.VB.IsSubbundle κ' → GlobalTheory.VB.IsVB H (n + 1) → GlobalTheory.VB.IsVB H' (n + 1) → ψ.hom ≫ B.genRes.map κ' = B.genRes.map κ ≫ φ.hom → GlobalTheory.FlagChain.Le κ (P.fl.ι ⟨n + 2, by omega⟩) → GlobalTheory.FlagChain.Le κ' (P.fl'.ι ⟨n + 2, by omega⟩) → ∃ (B₁ : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B₁ B) (K K' : B₁.X.Modules) (μ : K ⟶ (Scheme.Modules.pullback f.f).obj E) (μ' : K' ⟶ (Scheme.Modules.pullback f.f).obj E') (χ : B₁.GenIso K K'), GlobalTheory.IsNormalScheme B₁.X ∧ f.relDim = 0 ∧ GlobalTheory.VB.IsSubbundle μ ∧ GlobalTheory.VB.IsSubbundle μ' ∧ GlobalTheory.VB.IsVB K n ∧ GlobalTheory.VB.IsVB K' n ∧ χ.hom ≫ B₁.genRes.map μ' = B₁.genRes.map μ ≫ (φ.pull f.comp_str).hom ∧ GlobalTheory.FlagChain.Le μ ((Scheme.Modules.pullback f.f).map (P.fl.ι ⟨n + 1, by omega⟩)) ∧ GlobalTheory.FlagChain.Le μ' ((Scheme.Modules.pullback f.f).map (P.fl'.ι ⟨n + 1, by omega⟩)) ∧ GlobalTheory.FlagChain.Le μ ((Scheme.Modules.pullback f.f).map κ) ∧ GlobalTheory.FlagChain.Le μ' ((Scheme.Modules.pullback f.f).map κ') := by
  intro O _ _ _ p _ _ _ B hB E E' φ r P n hn H H' κ κ' ψ hs hs' hv hv' hψ hle hle'
  obtain ⟨u, rfl⟩ := hle
  obtain ⟨u', rfl⟩ := hle'
  have := hs.mono
  have := hs'.mono
  have : Mono u := mono_of_mono u (P.fl.ι _)
  have : Mono u' := mono_of_mono u' (P.fl'.ι _)
  have hL := FlagChain.isVB_cokernel_one hs (P.fl.isSubbundle _) hv (P.fl.isVB _) P.fl.isVB_self
  have hL' := FlagChain.isVB_cokernel_one hs' (P.fl'.isSubbundle _) hv' (P.fl'.isVB _) P.fl'.isVB_self
  let s : P.fl.F ⟨n + 1, by omega⟩ ⟶ P.fl.F ⟨n + 2, by omega⟩ := P.fl.step ⟨n + 1, hn⟩
  let s' : P.fl'.F ⟨n + 1, by omega⟩ ⟶ P.fl'.F ⟨n + 2, by omega⟩ := P.fl'.step ⟨n + 1, hn⟩
  have hsι : s ≫ P.fl.ι _ = P.fl.ι _ := P.fl.step_ι ⟨n + 1, hn⟩
  have hsι' : s' ≫ P.fl'.ι _ = P.fl'.ι _ := P.fl'.step_ι ⟨n + 1, hn⟩
  have hγ : B.genRes.map s ≫ (P.gen ⟨n + 2, by omega⟩).hom =
      (P.gen ⟨n + 1, by omega⟩).hom ≫ B.genRes.map s' := P.gen_step ⟨n + 1, hn⟩
  have hu : B.genRes.map u ≫ (P.gen ⟨n + 2, by omega⟩).hom = ψ.hom ≫ B.genRes.map u' := by
    rw [← cancel_mono (B.genRes.map (P.fl'.ι ⟨n + 2, by omega⟩)), Category.assoc, Category.assoc, P.gen_ι,
      ← Functor.map_comp, hψ, Functor.map_comp, Category.assoc]
  obtain ⟨l, hl⟩ := exists_genIso_cokernel u u' ψ _ hu
  have ha : (P.gen ⟨n + 1, by omega⟩).hom ≫ B.genRes.map (s' ≫ cokernel.π u') =
      B.genRes.map (s ≫ cokernel.π u) ≫ l.hom := by
    rw [Functor.map_comp, Functor.map_comp, ← reassoc_of% hγ, hl, Category.assoc]
  have hiff : s ≫ cokernel.π u = 0 ↔ s' ≫ cokernel.π u' = 0 := by
    constructor
    · intro h
      refine GlobalTheory.MixedLocalChains.hom_ext_of_genRes O B _ _ 1 _ _ hL' ?_
      rw [← cancel_epi (P.gen ⟨n + 1, by omega⟩).hom, ha, h]
      simp
    · intro h
      refine GlobalTheory.MixedLocalChains.hom_ext_of_genRes O B _ _ 1 _ _ hL ?_
      rw [← cancel_mono l.hom, ← ha, h]
      simp
  by_cases h0 : s ≫ cokernel.π u = 0
  · have h0' := hiff.1 h0
    have h₀ : Le (P.fl.ι ⟨n, by omega⟩) (P.fl.ι ⟨n + 1, by omega⟩) :=
      ⟨P.fl.step ⟨n, by omega⟩, P.fl.step_ι ⟨n, by omega⟩⟩
    have h₀' : Le (P.fl'.ι ⟨n, by omega⟩) (P.fl'.ι ⟨n + 1, by omega⟩) :=
      ⟨P.fl'.step ⟨n, by omega⟩, P.fl'.step_ι ⟨n, by omega⟩⟩
    have h₁ : Le (P.fl.ι ⟨n + 1, by omega⟩) (u ≫ P.fl.ι _) :=
      ⟨Abelian.monoLift u s h0, by rw [Abelian.monoLift_comp_assoc, hsι]⟩
    have h₁' : Le (P.fl'.ι ⟨n + 1, by omega⟩) (u' ≫ P.fl'.ι _) :=
      ⟨Abelian.monoLift u' s' h0', by rw [Abelian.monoLift_comp_assoc, hsι']⟩
    let Q := FlagPairExists.pairPull (Model.Hom.id B).comp_str P
    exact ⟨B, Model.Hom.id B, _, _, Q.fl.ι ⟨n, by omega⟩, Q.fl'.ι ⟨n, by omega⟩, Q.gen _, hB, Nat.sub_self _,
      Q.fl.isSubbundle _, Q.fl'.isSubbundle _, Q.fl.isVB _, Q.fl'.isVB _, Q.gen_ι _, h₀.map _, h₀'.map _,
      (h₀.trans h₁).map _, (h₀'.trans h₁').map _⟩
  have h0' := mt hiff.2 h0
  have hF := P.fl.isVB ⟨n + 1, by omega⟩
  have hF' := P.fl'.isVB ⟨n + 1, by omega⟩
  have := hF.isFiniteQC
  have := hF'.isFiniteQC
  have := hL.isFiniteQC
  have := hL'.isFiniteQC
  obtain ⟨B₁, f, hB₁, hf, c, c'⟩ := exists_effCartier₂ B hB (annihilatorSheaf (cokernel (s ≫ cokernel.π u)))
    (annihilatorSheaf (cokernel (s' ≫ cokernel.π u')))
    (fun h => VB.genericPoint_notMem_support_cokernel_of_ne_zero _ _ _ _ hL h0
      ((coe_support_annihilatorSheaf _).le h))
    (fun h => VB.genericPoint_notMem_support_cokernel_of_ne_zero _ _ _ _ hL' h0'
      ((coe_support_annihilatorSheaf _).le h))
  obtain ⟨k₁, k₂⟩ := kernel_subbundle f.f _ hF hL c
  obtain ⟨k₁', k₂'⟩ := kernel_subbundle f.f _ hF' hL' c'
  obtain ⟨χ, hχ⟩ := exists_genIso_kernel _ _ _ _ (FlagPairExists.pull_comm f.comp_str l _ _ _ ha)
  have : Mono ((Scheme.Modules.pullback f.f).map u) :=
    (SubPull.isSubbundle_pullback _ _ f.f _ _ u _ hv ⟨inferInstance, 1, hL⟩).mono
  have : Mono ((Scheme.Modules.pullback f.f).map u') :=
    (SubPull.isSubbundle_pullback _ _ f.f _ _ u' _ hv' ⟨inferInstance, 1, hL'⟩).mono
  refine ⟨B₁, f, _, _, kernel.ι _ ≫ (Scheme.Modules.pullback f.f).map (P.fl.ι ⟨n + 1, by omega⟩),
    kernel.ι _ ≫ (Scheme.Modules.pullback f.f).map (P.fl'.ι ⟨n + 1, by omega⟩), χ, hB₁, hf,
    FlagChain.isSubbundle_comp k₁ (SubPull.isSubbundle_pullback _ _ f.f _ _ _ _ hF (P.fl.isSubbundle _)),
    FlagChain.isSubbundle_comp k₁' (SubPull.isSubbundle_pullback _ _ f.f _ _ _ _ hF' (P.fl'.isSubbundle _)),
    k₂, k₂', ?_, ⟨_, rfl⟩, ⟨_, rfl⟩, le_kernel f.f s u _ hsι, le_kernel f.f s' u' _ hsι'⟩
  rw [B₁.genRes.map_comp, B₁.genRes.map_comp, reassoc_of% hχ,
    FlagPairExists.pull_comm f.comp_str φ _ _ _ (P.gen_ι _), Category.assoc]

end GlobalTheory.FlagPairCommon
