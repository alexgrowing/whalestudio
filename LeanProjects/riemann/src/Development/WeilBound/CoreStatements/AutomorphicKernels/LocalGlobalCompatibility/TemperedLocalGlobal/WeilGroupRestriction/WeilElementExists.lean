import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.WeilGroupRestriction.IwahoriCompatibilityOfChains
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHcharPrescribedTrivial
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinExistsHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HilbertClassFieldOfGlobalArtinReciprocity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilGroupAtPlaceDenseInDecompositionGroupStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.PRep GlobalTheory.SmGL
open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

namespace PositivityTheory.Pf1.CLGD.K

namespace WeilElementExistence

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]

theorem exists_weil_mem {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w)
    (S : Set (Dec (F := F) A)) (hS : IsOpen S) (d : Dec (F := F) A) (hd : d ∈ S) :
    ∃ τ : Weil h, (⟨τ.1, Weil_le_Dec h τ.2⟩ : Dec (F := F) A) ∈ S := by
  obtain ⟨t, ht, hts⟩ := isOpen_induced_iff.mp hS
  have hdt : (d : G F Ω) ∈ t := by
    rw [← hts] at hd
    exact hd
  have hnhds : {x : G F Ω | (d : G F Ω) * x ∈ t} ∈ nhds (1 : G F Ω) := by
    apply (continuous_const_mul (d : G F Ω)).continuousAt.preimage_mem_nhds
    simpa using ht.mem_nhds hdt
  obtain ⟨L, hL, hLs⟩ := (krullTopology_mem_nhds_one_iff F Ω _).mp hnhds
  let pb := Field.powerBasisOfFiniteOfSeparable F L
  obtain ⟨τ, hτW, hτ⟩ := GlobalTheory.T.weilGroupAtPlace_dense_in_decompositionGroup F Ω A w h (d : G F Ω) d.2 (pb.gen : Ω)
  have hfix : (d : G F Ω)⁻¹ * τ ∈ L.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have e : (((d : G F Ω)⁻¹ * τ : G F Ω) : Ω →ₐ[F] Ω).comp L.val = L.val := pb.algHom_ext (by
      show ((d : G F Ω)⁻¹ * τ) (pb.gen : Ω) = pb.gen
      rw [AlgEquiv.mul_apply, hτ]
      show ((d : G F Ω)⁻¹ * (d : G F Ω)) (pb.gen : Ω) = pb.gen
      simp)
    exact congrArg (fun φ : L →ₐ[F] Ω => φ ⟨x, hx⟩) e
  have hτt : τ ∈ t := by
    have := hLs hfix
    simpa using this
  refine ⟨⟨τ, hτW⟩, ?_⟩
  rw [← hts]
  exact hτt

end WeilElementExistence

open WeilElementExistence in
theorem weil_element_exists : K1 := by
  intro F Ω _ _ _ _ _ S _ v A hinj hA χ hχ
  classical
  obtain ⟨art, hart⟩ := GlobalTheory.globalArtinReciprocity_holds F Ω
  have hLA : ∀ s, ∃ a : Weil (hA s) →* ((v s).adicCompletion F)ˣ, IsLocalArtin (hA s) a := fun s =>
    GlobalTheory.localArtinExists_holds F Ω (A s) (v s) (hA s)
  choose a ha using hLA
  have hfin : ∀ s, ∃ N : ℕ, 0 < N ∧ ∀ g, χ s g ^ N = 1 := fun s => by
    have : CompactSpace (Dec (F := F) (A s)) := isCompact_iff_compactSpace.1 (isClosed_Dec (A s)).isCompact
    have : Finite (Dec (F := F) (A s) ⧸ (χ s).ker) := Subgroup.quotient_finite_of_isOpen _ (hχ s)
    refine ⟨(χ s).ker.index, Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite, fun g => ?_⟩
    rw [← map_pow]
    exact MonoidHom.mem_ker.1 ((χ s).ker.pow_index_mem g)
  have hθ : ∀ s, ∃ θ : ((v s).adicCompletion F)ˣ →* ℂˣ, IsSmoothChar θ ∧ (∃ N : ℕ, 0 < N ∧ θ ^ N = 1) ∧
      ∀ σ : Weil (hA s), θ (a s σ) = χ s ⟨σ.1, Weil_le_Dec (hA s) σ.2⟩ := fun s => by
    let ξ : Weil (hA s) →* ℂˣ := (χ s).comp (Subgroup.inclusion (Weil_le_Dec (hA s)))
    have hξ : GlobalTheory.WeilDeligne.IsSmooth ξ := by
      have hc : Continuous (fun σ : Ine (F := F) (A s) =>
          (⟨σ.1, Ine_le_Dec (A s) σ.2⟩ : Dec (F := F) (A s))) :=
        continuous_subtype_val.subtype_mk _
      exact (hχ s).preimage hc
    obtain ⟨θ, hθs, e⟩ := (ha s).factor ξ hξ
    obtain ⟨N, hN, hN1⟩ := hfin s
    refine ⟨θ, hθs, ⟨N, hN, MonoidHom.ext fun x => ?_⟩, fun σ => (DFunLike.congr_fun e σ).symm⟩
    obtain ⟨σ, rfl⟩ := (ha s).surj x
    have e' : θ (a s σ) = ξ σ := (DFunLike.congr_fun e σ).symm
    show θ (a s σ) ^ N = 1
    rw [e']
    exact hN1 (Subgroup.inclusion (Weil_le_Dec (hA s)) σ)
  choose θs hθs using hθ
  have hex : ∀ w : HeightOneSpectrum (𝓞 F), ∃ θ : (w.adicCompletion F)ˣ →* ℂˣ, IsSmoothChar θ ∧
      (∃ N : ℕ, 0 < N ∧ θ ^ N = 1) ∧ ∀ t (e : v t = w), θ = e ▸ θs t := fun w => by
    by_cases hw : ∃ t, v t = w
    · obtain ⟨t, rfl⟩ := hw
      refine ⟨θs t, (hθs t).1, (hθs t).2.1, fun t' e => ?_⟩
      obtain rfl := hinj e
      rfl
    · exact ⟨1, by unfold IsSmoothChar; simp, ⟨1, one_pos, one_pow 1⟩, fun t e => absurd ⟨t, e⟩ hw⟩
  choose θ' hθ'1 hθ'2 hθ'3 using hex
  have hθ'v : ∀ s, θ' (v s) = θs s := fun s => hθ'3 (v s) s rfl
  obtain ⟨η, ⟨n, hn, hηn⟩, hinf, hloc⟩ := GlobalTheory.DelEps.Twist.exists_hchar_prescribed F (Set.finite_range v).toFinset θ'
    (fun w _ => hθ'1 w) (fun w _ => hθ'2 w)
  have hηloc : ∀ s, η.loc (v s) = θs s := fun s => by
    rw [hloc (v s) (by simp), hθ'v s]
  have h1 : ∀ x, η.1 x ^ n = 1 := fun x => congrArg (fun ξ : HChar F => ξ.1 x) hηn
  have hko : IsOpen (η.1.ker : Set (Ideles F)) := GlobalTheory.HeckeGal.isOpen_ker_of_pow η.1 η.2.1 hn h1
  have hkc : IsClosed (η.1.ker : Set (Ideles F)) := Subgroup.isClosed_of_isOpen _ hko
  have hle : art.ker ≤ η.1.ker := by
    rw [hart.ker]
    refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) hkc
    · rintro _ ⟨k, rfl⟩
      exact η.2.2 k
    · rw [GlobalTheory.HeckeGal.infConn, Subgroup.map_le_iff_le_comap]
      intro y hy
      have hinl : Continuous (Units.map (MonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))) :=
        Continuous.units_map _ (continuous_id.prodMk continuous_const)
      have hcl : IsClopen ((Subgroup.comap (Units.map (MonoidHom.inl (InfiniteAdeleRing F)
          (FiniteAdeleRing (𝓞 F) F))) η.1.ker : Subgroup _) : Set (InfiniteAdeleRing F)ˣ) :=
        ⟨hkc.preimage hinl, hko.preimage hinl⟩
      exact hcl.connectedComponent_subset (Subgroup.one_mem _) hy
  let e := QuotientGroup.quotientKerEquivOfSurjective art hart.quot.surjective
  let cη : Gab F Ω →* ℂˣ := (QuotientGroup.lift art.ker η.1 hle).comp e.symm.toMonoidHom
  have hc : ∀ x, cη (art x) = η.1 x := fun x => by
    show QuotientGroup.lift art.ker η.1 hle (e.symm (art x)) = η.1 x
    have : e.symm (art x) = QuotientGroup.mk x := e.symm_apply_eq.mpr rfl
    rw [this]; rfl
  have hcc : Continuous cη := by
    rw [hart.quot.isQuotientMap.continuous_iff]
    have : (cη ∘ art) = η.1 := funext hc
    rw [this]; exact η.2.1
  let ψ : G F Ω →* ℂˣ := cη.comp (GlobalTheory.HeckeGal.toAb F Ω)
  have hψc : Continuous ψ := hcc.comp continuous_quot_mk
  have hψn : ∀ g, ψ g ^ n = 1 := fun g => by
    obtain ⟨x, hx⟩ := hart.quot.surjective (GlobalTheory.HeckeGal.toAb F Ω g)
    show cη _ ^ n = 1
    rw [← hx, hc, h1]
  have hψo : IsOpen (ψ.ker : Set (G F Ω)) := GlobalTheory.HeckeGal.isOpen_ker_of_pow ψ hψc hn hψn
  have hW : ∀ s (σ : Weil (hA s)), ψ σ = χ s ⟨σ.1, Weil_le_Dec (hA s) σ.2⟩ := fun s σ => by
    show cη (GlobalTheory.HeckeGal.toAb F Ω σ) = _
    rw [← (ha s).glob art hart σ, hc, ← (hθs s).2.2 σ, ← hηloc s]
    rfl
  have hD : ∀ s (g : Dec (F := F) (A s)), ψ g = χ s g := fun s g => by
    let K : Subgroup (Dec (F := F) (A s)) := (χ s).ker ⊓ (ψ.comp (Dec (F := F) (A s)).subtype).ker
    have hK : IsOpen (K : Set (Dec (F := F) (A s))) :=
      (hχ s).inter (hψo.preimage continuous_subtype_val)
    obtain ⟨τ, hτ⟩ := exists_weil_mem (hA s) ((fun x => g⁻¹ * x) ⁻¹' (K : Set (Dec (F := F) (A s))))
      (hK.preimage (continuous_const.mul continuous_id)) g (by
        show g⁻¹ * g ∈ K
        rw [inv_mul_cancel]
        exact K.one_mem)
    have hτ' : g⁻¹ * (⟨τ.1, Weil_le_Dec (hA s) τ.2⟩ : Dec (F := F) (A s)) ∈ K := hτ
    obtain ⟨k1, k2⟩ := Subgroup.mem_inf.1 hτ'
    have e1 : χ s g = χ s ⟨τ.1, Weil_le_Dec (hA s) τ.2⟩ :=
      inv_mul_eq_one.1 (by rw [← map_inv, ← map_mul]; exact MonoidHom.mem_ker.1 k1)
    have e2 : (ψ.comp (Dec (F := F) (A s)).subtype) g =
        (ψ.comp (Dec (F := F) (A s)).subtype) ⟨τ.1, Weil_le_Dec (hA s) τ.2⟩ :=
      inv_mul_eq_one.1 (by rw [← map_inv, ← map_mul]; exact MonoidHom.mem_ker.1 k2)
    have e3 : ψ g = ψ τ := e2
    rw [e3, hW s τ, e1]
  refine ⟨ψ, hψo, hD, fun u _ c hcu => ?_⟩
  obtain ⟨j, hj, hju⟩ := hcu
  have e1 := GlobalTheory.HilbertFromArtin.art_sign_eq hart j c hj
  rw [hju] at e1
  show cη (GlobalTheory.HeckeGal.toAb F Ω c) = 1
  rw [← e1, hc]
  exact DFunLike.congr_fun (hinf u) (-1)

end PositivityTheory.Pf1.CLGD.K

end
