import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ArthurClozel
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlobalArtinReciprocityHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HilbertClassFieldOfGlobalArtinReciprocity
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHcharPrescribedTrivial
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinExistsHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneRelUnique
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalComponentEigenvectorAtSplitPlaceIsoty
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsQuadraticCharOfSplitTwoGroup
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL GlobalTheory.SmGL

namespace GlobalTheory.AbStep

theorem loc_char : ∀ (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (h : IsPlaceOver A v) (a : Weil h →* (v.adicCompletion F)ˣ), IsLocalArtin h a → ∀ χ : Dec (F := F) A →* ℂˣ, IsOpen (χ.ker : Set (Dec (F := F) A)) → ∃ θ : (v.adicCompletion F)ˣ →* ℂˣ, IsSmoothChar θ ∧ (∃ N : ℕ, 0 < N ∧ θ ^ N = 1) ∧ ∀ σ : Weil h, θ (a σ) = χ (Subgroup.inclusion (Weil_le_Dec h) σ) := by
  intro Ω _ F _ _ _ _ A v h a ha χ hχ
  classical
  let ξ : Weil h →* ℂˣ := χ.comp (Subgroup.inclusion (Weil_le_Dec h))
  have hξ : GlobalTheory.WeilDeligne.IsSmooth ξ := by
    have hc : Continuous (fun σ : Ine (F := F) A =>
        (⟨(σ : G F Ω), Weil_le_Dec h (Ine_le_Weil h σ.2)⟩ : Dec (F := F) A)) :=
      continuous_subtype_val.subtype_mk _
    exact hχ.preimage hc
  obtain ⟨θ, hθs, hθ⟩ := ha.factor ξ hξ
  have hfi : χ.ker.FiniteIndex := GlobalTheory.LocVec.finiteIndex_of_isOpen (Dec (F := F) A)
    (ReciprocityTheory.Gal.isClosed_Dec A).isCompact subset_rfl χ.ker hχ
  refine ⟨θ, hθs, ⟨χ.ker.index, Nat.pos_of_ne_zero hfi.index_ne_zero, ?_⟩, fun σ => ?_⟩
  · refine MonoidHom.ext fun x => ?_
    obtain ⟨σ, rfl⟩ := ha.surj x
    have hm := Subgroup.pow_index_mem χ.ker (Subgroup.inclusion (Weil_le_Dec h) σ)
    rw [MonoidHom.mem_ker, map_pow] at hm
    rw [MonoidHom.pow_apply, MonoidHom.one_apply, ← MonoidHom.comp_apply θ a, ← hθ]
    exact hm
  · exact (DFunLike.congr_fun hθ σ).symm

theorem gal_char : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (art : Ideles F →* Gab F Ω), IsGlobalArtin art → ∀ η : HChar F, (∃ n : ℕ, 0 < n ∧ η.OrderDvd n) → (∀ u : InfinitePlace F, η.locInf u = 1) → ∃ ρ : Gab F Ω →* ℂˣ, IsOpen (ρ.ker : Set (Gab F Ω)) ∧ ∀ x, ρ (art x) = η.1 x := by
  intro F Ω _ _ _ _ art ha η hηf _
  obtain ⟨n, hn, hηn⟩ := hηf
  have hpow : ∀ x, η.1 x ^ n = 1 := fun x => congrArg (fun ξ : HChar F => ξ.1 x) hηn
  have hko : IsOpen (η.1.ker : Set (Ideles F)) := GlobalTheory.HeckeGal.isOpen_ker_of_pow η.1 η.2.1 hn hpow
  have hinf : infConn F ≤ η.1.ker := by
    let ι : (InfiniteAdeleRing F)ˣ →* Ideles F :=
      Units.map (MonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
    have hιc : Continuous ι := Continuous.units_map _ (continuous_id.prodMk continuous_const)
    have hO : IsOpen ((η.1.ker.comap ι : Subgroup _) : Set (InfiniteAdeleRing F)ˣ) := hko.preimage hιc
    rintro _ ⟨y, hy, rfl⟩
    exact (IsClopen.connectedComponent_subset ⟨Subgroup.isClosed_of_isOpen _ hO, hO⟩
      (Subgroup.one_mem _)) hy
  have hker : art.ker ≤ η.1.ker := by
    rw [ha.ker]
    refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ hinf) (η.1.ker.isClosed_of_isOpen hko)
    rintro _ ⟨k, rfl⟩
    exact η.2.2 k
  have hs : Function.Surjective art := ha.quot.surjective
  let e := QuotientGroup.quotientKerEquivOfSurjective art hs
  let ρ : Gab F Ω →* ℂˣ := (QuotientGroup.lift art.ker η.1 hker).comp e.symm.toMonoidHom
  have hρ : ∀ x, ρ (art x) = η.1 x := fun x => by
    have he : e.symm (art x) = (x : Ideles F ⧸ art.ker) := e.symm_apply_eq.2 rfl
    show QuotientGroup.lift art.ker η.1 hker (e.symm (art x)) = _
    rw [he]
    rfl
  refine ⟨ρ, ?_, hρ⟩
  have hk : (ρ.ker : Set (Gab F Ω)) = art '' (η.1.ker : Set (Ideles F)) := by
    ext g
    obtain ⟨x, rfl⟩ := hs g
    constructor
    · intro hg
      exact ⟨x, by rw [SetLike.mem_coe, MonoidHom.mem_ker, ← hρ]; exact hg, rfl⟩
    · rintro ⟨y, hy, e'⟩
      show ρ _ = 1
      rw [← e', hρ]
      exact hy
  rw [hk]
  exact ha.quot.isOpenMap _ hko

end GlobalTheory.AbStep

namespace GlobalTheory.AbStep

theorem one_char (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] [IsAlgClosure F Ω]
    (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (h : IsPlaceOver A v)
    (χ : Dec (F := F) A →* ℂˣ) (hχ : IsOpen (χ.ker : Set (Dec (F := F) A)))
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hT : v ∉ T) :
    ∃ r : G F Ω →* ℂˣ, IsOpen (r.ker : Set (G F Ω)) ∧ (∀ g : Dec (F := F) A, r g = χ g) ∧
      (∀ (j : Ω →+* ℂ) (c : G F Ω), (∀ x, j (c x) = starRingEnd ℂ (j x)) → r c = 1) ∧
      ∀ u ∈ T, ∀ A' : ValuationSubring Ω, IsPlaceOver A' u → ∀ g ∈ Dec (F := F) A', r g = 1 := by
  classical
  obtain ⟨art, ha⟩ := GlobalTheory.globalArtinReciprocity_holds F Ω
  obtain ⟨a, haL⟩ := GlobalTheory.localArtinExists_holds F Ω A v h
  obtain ⟨θ, hθs, hθf, hθ⟩ := loc_char Ω F A v h a haL χ hχ
  have hne : ∀ u ∈ T, u ≠ v := fun u hu e => hT (e ▸ hu)
  obtain ⟨η, hηf, hηi, hηl⟩ := GlobalTheory.DelEps.Twist.exists_hchar_prescribed F (insert v T)
    (Function.update (fun _ => 1) v θ)
    (fun w hw => by
      rcases Finset.mem_insert.1 hw with rfl | hw
      · rw [Function.update_self]; exact hθs
      · rw [Function.update_of_ne (hne w hw)]
        unfold IsSmoothChar
        simp)
    (fun w hw => by
      rcases Finset.mem_insert.1 hw with rfl | hw
      · rw [Function.update_self]; exact hθf
      · rw [Function.update_of_ne (hne w hw)]
        exact ⟨1, one_pos, one_pow _⟩)
  have hηv : η.loc v = θ := by rw [hηl v (Finset.mem_insert_self _ _), Function.update_self]
  have hηT : ∀ u ∈ T, η.loc u = 1 := fun u hu => by
    rw [hηl u (Finset.mem_insert_of_mem hu), Function.update_of_ne (hne u hu)]
  obtain ⟨ρ, hρo, hρ⟩ := gal_char F Ω art ha η hηf hηi
  let r : G F Ω →* ℂˣ := ρ.comp (toAb F Ω)
  have hro : IsOpen (r.ker : Set (G F Ω)) :=
    hρo.preimage (QuotientGroup.isQuotientMap_mk _).continuous
  have hW : ∀ σ : Weil h, r σ = χ (Subgroup.inclusion (Weil_le_Dec h) σ) := fun σ => by
    show ρ (toAb F Ω σ) = _
    rw [← haL.glob art ha σ, hρ, ← hθ σ, ← hηv]
    rfl
  have hD : ∀ g : Dec (F := F) A, r g = χ g := by
    intro g
    obtain ⟨O, hOo, hO⟩ := isOpen_induced_iff.1 hχ
    have h1 : (1 : G F Ω) ∈ O := by
      have : (1 : Dec (F := F) A) ∈ (χ.ker : Set (Dec (F := F) A)) := χ.ker.one_mem
      rw [← hO] at this
      exact this
    obtain ⟨L, hLf, hLs⟩ := (krullTopology_mem_nhds_one_iff F Ω _).1
      ((hro.inter hOo).mem_nhds ⟨r.ker.one_mem, h1⟩)
    obtain ⟨τ, hτ⟩ := GlobalTheory.ConjWD.exists_weil_eq_on (h := h) g.2 L
    have hfix : (τ : G F Ω)⁻¹ * g ∈ L.fixingSubgroup := fun x => by
      show ((τ : G F Ω)⁻¹ * (g : G F Ω)) x = x
      rw [AlgEquiv.mul_apply, ← hτ x x.2]
      show ((τ : G F Ω)⁻¹ * τ) x = x
      simp
    obtain ⟨hr1, hO1⟩ := hLs hfix
    have hk : (Subgroup.inclusion (Weil_le_Dec h) τ)⁻¹ * g ∈ χ.ker := by
      have : (Subgroup.inclusion (Weil_le_Dec h) τ)⁻¹ * g ∈ (Subtype.val ⁻¹' O : Set (Dec (F := F) A)) := hO1
      rw [hO] at this
      exact this
    rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at hk
    have hr1' : r ((τ : G F Ω)⁻¹ * g) = 1 := hr1
    rw [map_mul, map_inv, inv_mul_eq_one] at hr1'
    rw [← hr1', hW τ, hk]
  refine ⟨r, hro, hD, fun j c hc => ?_, fun u hu A' hA' g hg => ?_⟩
  · show ρ (toAb F Ω c) = 1
    rw [← GlobalTheory.HilbertFromArtin.art_sign_eq ha j c hc, hρ]
    exact DFunLike.congr_fun (hηi _) (-1)
  · have hm : toAb F Ω g ∈ (art.comp (localIdele F u)).range.topologicalClosure := by
      rw [ha.dec u A' hA']
      exact ⟨g, hg, rfl⟩
    have hle : (art.comp (localIdele F u)).range ≤ ρ.ker := by
      rintro _ ⟨x, rfl⟩
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hρ]
      exact DFunLike.congr_fun (hηT u hu) x
    exact Subgroup.topologicalClosure_minimal _ hle (ρ.ker.isClosed_of_isOpen hρo) hm

end GlobalTheory.AbStep

namespace GlobalTheory.AbStep

theorem exists_abelian_real_field : ∀ (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] [IsAlgClosure F Ω] [IsTotallyReal F] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (h : IsPlaceOver A v) (V : Subgroup (Dec (F := F) A)), IsOpen (V : Set (Dec (F := F) A)) → commutator (Dec (F := F) A) ≤ V → ∀ T : Finset (HeightOneSpectrum (𝓞 F)), v ∉ T → ∃ F₁ : IntermediateField F Ω, FiniteDimensional F F₁ ∧ IsAbelianGalois F F₁ ∧ (∀ φ : F₁ →+* ℂ, ComplexEmbedding.IsReal φ) ∧ (∀ g : Dec (F := F) A, (g : G F Ω) ∈ F₁.fixingSubgroup ↔ g ∈ V) ∧ ∀ u ∈ T, ∀ A' : ValuationSubring Ω, IsPlaceOver A' u → Dec (F := F) A' ≤ F₁.fixingSubgroup := by
  intro Ω _ F _ _ _ _ _ A v h V hVo hVc T hvT
  haveI : V.Normal := GlobalTheory.normal_of_commutator_le V hVc
  haveI : V.FiniteIndex := GlobalTheory.LocVec.finiteIndex_of_isOpen (Dec (F := F) A) (ReciprocityTheory.Gal.isClosed_Dec A).isCompact subset_rfl V hVo
  letI : CommGroup (Dec (F := F) A ⧸ V) := { (inferInstance : Group (Dec (F := F) A ⧸ V)) with
    mul_comm := fun a b => by
      induction a using QuotientGroup.induction_on with | H a => ?_
      induction b using QuotientGroup.induction_on with | H b => ?_
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      apply hVc
      have := Subgroup.commutator_mem_commutator (Subgroup.mem_top b⁻¹) (Subgroup.mem_top a⁻¹)
      show _ ∈ ⁅(⊤ : Subgroup (Dec (F := F) A)), ⊤⁆
      simpa [commutatorElement_def, mul_assoc] using this }
  have hsep : ∀ q : Dec (F := F) A ⧸ V, ∃ ψ : (Dec (F := F) A ⧸ V) →* ℂˣ, q ≠ 1 → ψ q ≠ 1 := fun q => by
    by_cases hq : q = 1
    · exact ⟨1, fun h => (h hq).elim⟩
    · obtain ⟨ψ, hψ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (Dec (F := F) A ⧸ V) ℂ hq
      exact ⟨ψ, fun _ => hψ⟩
  choose ψ hψ using hsep
  have hopen : ∀ q, IsOpen (((ψ q).comp (QuotientGroup.mk' V)).ker : Set (Dec (F := F) A)) := fun q =>
    Subgroup.isOpen_mono (fun g hg => by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        (QuotientGroup.eq_one_iff g).2 hg, map_one]) hVo
  choose r hro hrD hrc hrT using fun q => one_char Ω F A v h ((ψ q).comp (QuotientGroup.mk' V)) (hopen q) T hvT
  let φ : G F Ω →* (Dec (F := F) A ⧸ V → ℂˣ) := Pi.monoidHom r
  have hφ : ∀ σ, φ σ = 1 ↔ ∀ q, r q σ = 1 := fun σ => funext_iff
  have hker : (φ.ker : Set (G F Ω)) = ⋂ q, (r q).ker := by
    ext σ
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter]
    exact hφ σ
  have ho : IsOpen (φ.ker : Set (G F Ω)) := by
    rw [hker]
    exact isOpen_iInter_of_finite hro
  obtain ⟨L, hLf, hLa, hL⟩ := GlobalTheory.RayFromArtin.exists_field φ ho
  have hmem : ∀ σ : G F Ω, σ ∈ L.fixingSubgroup ↔ ∀ q, r q σ = 1 := fun σ => by
    rw [← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker, hL, hφ]
  refine ⟨L, hLf, hLa, ?_, ?_, ?_⟩
  · intro φ'
    haveI : Algebra.IsAlgebraic L Ω := Algebra.IsAlgebraic.tower_top (K := F) L
    haveI : IsGalois F Ω := {}
    let j : Ω →+* ℂ := ComplexEmbedding.lift Ω φ'
    have hj : j.comp (algebraMap L Ω) = φ' := ComplexEmbedding.lift_comp_algebraMap _ _
    have hreal : ComplexEmbedding.IsReal (j.comp (algebraMap F Ω)) := by
      exact IsTotallyReal.complexEmbedding_isReal _
    obtain ⟨σ, hσ⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := F) j (ComplexEmbedding.conjugate j) (by
      rw [ComplexEmbedding.conjugate_comp, ComplexEmbedding.isReal_iff.1 hreal])
    have hc : ∀ x, j (σ.symm x) = starRingEnd ℂ (j x) := fun x => DFunLike.congr_fun hσ x
    have hfix : σ.symm ∈ L.fixingSubgroup := (hmem _).2 fun q => hrc q j σ.symm hc
    rw [ComplexEmbedding.isReal_iff]
    ext x
    rw [← hj]
    show starRingEnd ℂ (j (x : Ω)) = j (x : Ω)
    rw [← hc]
    exact congrArg j (hfix x)
  · intro g
    rw [hmem]
    constructor
    · intro H
      by_contra hg
      have hq : (QuotientGroup.mk' V g) ≠ 1 := fun e => hg ((QuotientGroup.eq_one_iff g).1 e)
      exact hψ _ hq (by rw [← H (QuotientGroup.mk' V g), hrD]; rfl)
    · intro hg q
      rw [hrD, MonoidHom.comp_apply, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff g).2 hg, map_one]
  · intro u hu A' hA' g hg
    exact (hmem g).2 fun q => hrT q u hu A' hA' g hg

end GlobalTheory.AbStep
