import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CrDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsConj

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg UpperTheory.V.Pr UpperTheory.V

open scoped Pointwise in
private theorem conj_ine {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {A B : ValuationSubring Ω} {v : W.Plc k} (hA : IsPlaceOver A v) (hB : IsPlaceOver B v) :
    ∃ g : G k Ω, ∀ τ ∈ Ine (F := k) B, g⁻¹ * τ * g ∈ Ine (F := k) A := by
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hA hB
  have hlift : IsLift (RingEquiv.refl k) σ.toRingEquiv := fun x => σ.commutes x
  have hmem : ∀ x : Ω, σ.toRingEquiv x ∈ B ↔ x ∈ A := by
    intro x
    rw [← hσ]
    exact ValuationSubring.smul_mem_pointwise_smul_iff
  refine ⟨σ, fun τ hτ => ?_⟩
  have h1 := conjGal_mem_Ine hlift hmem hτ
  have heq : conjGal hlift τ = σ⁻¹ * τ * σ := AlgEquiv.ext fun x => rfl
  rw [← heq]
  exact h1

private theorem ine_NS {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    {S : Set (W.Plc k)} {A : ValuationSubring Ω} {v : W.Plc k} (hv : v ∉ S)
    (hA : IsPlaceOver A v) {t : G k Ω} (ht : t ∈ Ine (F := k) A) : toGS Ω S t = 1 := by
  refine (QuotientGroup.eq_one_iff t).2 (Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_))
  simp only [Set.mem_iUnion]
  exact ⟨v, hv, A, hA, ht⟩

private theorem normal_map {l : ℕ} [Fact l.Prime] (F : W.GFrame l) (N : Subgroup F.G₀) (hN : N.Normal)
    (hc : ∀ g ∈ N, F.conj g ∈ N) : (N.map F.η.ker.subtype).Normal := by
  constructor
  rintro _ ⟨m, hm, rfl⟩ γ
  by_cases hγ : F.η γ = 1
  · exact ⟨⟨γ, hγ⟩ * m * (⟨γ, hγ⟩ : F.G₀)⁻¹, hN.conj_mem m hm _, rfl⟩
  · have hγ' : F.η γ = -1 := (Int.units_eq_one_or _).resolve_left hγ
    have h0 : F.η (F.c⁻¹ * γ) = 1 := by
      rw [map_mul, map_inv, F.η_c, hγ']
      simp
    let γ0 : F.G₀ := ⟨F.c⁻¹ * γ, h0⟩
    refine ⟨F.conj (γ0 * m * γ0⁻¹), hc _ (hN.conj_mem m hm γ0), ?_⟩
    show F.c * (F.c⁻¹ * γ * (m : F.Γ) * (F.c⁻¹ * γ)⁻¹) * F.c⁻¹ = γ * (m : F.Γ) * γ⁻¹
    group

theorem UpperTheory.frame_criterion_kernel :
    UpperTheory.V.Pr.CrKer := by
  unfold UpperTheory.V.Pr.CrKer
  intro Ω _ _ _ l _ O _ _ η Ψ σ g₁ B M L _ _ _ _ _ Φ k s x V hS π hπ N hN hNc hNconj hIu hI0
  let N' : Subgroup V.frame.Γ := N.map V.frame.η.ker.subtype
  haveI hN'n : N'.Normal := normal_map V.frame N hN hNconj
  have hG0c : IsClosed (V.frame.η.ker : Set V.frame.Γ) :=
    Subgroup.isClosed_of_isOpen _ V.frame.η_open
  have hN'c : IsClosed (N' : Set V.frame.Γ) := by
    rw [Subgroup.coe_map]
    exact hG0c.isClosedEmbedding_subtypeVal.isClosedMap _ hNc
  let K : Subgroup (G (W.Lp L) Ω) := N'.comap (toGS Ω V.S')
  have hKc : IsClosed (K : Set (G (W.Lp L) Ω)) := hN'c.preimage (continuous_toGS Ω V.S')
  haveI hKn : K.Normal := hN'n.comap _
  let Kup : Subgroup (upl Ω L) := K.map (toUpl Ω L)
  haveI hKupn : Kup.Normal := hKn.map _ toUpl_surj
  have hind : Topology.IsInducing (toUpl Ω L) :=
    (Topology.IsInducing.subtypeVal.of_comp_iff).1 (galEmbTop ℚ (W.Lp L) Ω).1.isInducing
  have hKupc : IsClosed (Kup : Set (upl Ω L)) := by
    obtain ⟨t, ht, hpre⟩ := hind.isClosed_iff.1 hKc
    rw [Subgroup.coe_map, ← hpre, Set.image_preimage_eq t toUpl_surj]
    exact ht
  have hgen : ∀ u : upl Ω L, ∀ B' : ValuationSubring Ω, ¬B'.valuation (l : Ω) < 1 →
      (u : G ℚ Ω) ∈ Ine B' → barChar O Ψ (u : G ℚ Ω) = 1 → u ∈ Kup := by
    intro u B' hl hIne hbar
    obtain ⟨τ, hτ⟩ := toUpl_surj (Ω := Ω) (L := L) u
    refine ⟨τ, ?_, hτ⟩
    have hτI : τ ∈ Ine (F := W.Lp L) B' := by
      rw [← hτ] at hIne
      exact hIne
    by_cases htop : B' = ⊤
    · have hbot := ((places (W.Lp L) Ω l B').2.1 htop).1
      rw [hbot] at hτI
      rw [Subgroup.mem_bot.1 hτI]
      exact K.one_mem
    obtain ⟨v, hv⟩ := (places (W.Lp L) Ω l B').1 htop
    by_cases hvS : v ∈ V.S'
    · have hvS' : v ∈ s.S := hS ▸ hvS
      obtain ⟨h, hh⟩ := conj_ine (s.hA v) hv
      have hτ' := hh τ hτI
      obtain ⟨t, ht⟩ := s.unr (s.A v) v (s.hA v) hτ'
      have htI : t ∈ Ine (F := L) (s.A v) := by
        have h1 : W.resP L Ω t ∈ Ine (F := W.Lp L) (s.A v) := by
          rw [ht]
          exact hτ'
        exact h1
      have hprN : V.pr t ∈ N := by
        rcases hvS' with hlv | hvSt | hv0
        · exfalso
          exact hl ((natCast_place hv l).2 hlv)
        · apply hIu ⟨v, hvSt⟩ (V.pr t) ⟨t, htI, rfl⟩
          rw [hπ t, k.galois_link_projection_coe, k.psi]
          change barChar O Ψ (galEmb ℚ (W.Lp L) Ω (W.resP L Ω t)) = 1
          rw [ht, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv,
            mul_comm ((barChar O Ψ) ((galEmb ℚ (W.Lp L) Ω) h))⁻¹ _, inv_mul_cancel_right]
          have hu : (galEmb ℚ (W.Lp L) Ω) τ = (u : G ℚ Ω) := by
            rw [← hτ]
            rfl
          rw [hu]
          exact hbar
        · apply hI0
          subst hv0
          exact ⟨t, htI, rfl⟩
      have hτ'N : toGS Ω V.S' (h⁻¹ * τ * h) ∈ N' := by
        refine ⟨V.pr t, hprN, ?_⟩
        change toGS Ω V.S' (W.resP L Ω t) = _
        rw [ht]
      have hconj := hN'n.conj_mem _ hτ'N (toGS Ω V.S' h)
      have heq : toGS Ω V.S' h * toGS Ω V.S' (h⁻¹ * τ * h) * (toGS Ω V.S' h)⁻¹ = toGS Ω V.S' τ := by
        simp only [map_mul, map_inv]
        group
      change toGS Ω V.S' τ ∈ N'
      rw [← heq]
      exact hconj
    · change toGS Ω V.S' τ ∈ N'
      rw [ine_NS hvS hv hτI]
      exact N'.one_mem
  have hpker : k.p.ker ≤ Kup := by
    rw [k.p_ker]
    apply Subgroup.topologicalClosure_minimal _ _ hKupc
    apply Subgroup.normalClosure_le_normal
    rintro u ⟨B', hl, hIne, -, hbar⟩
    exact hgen u B' hl hIne hbar
  intro g0 hg0
  obtain ⟨g, rfl⟩ := pr_surj V g0
  have hp0 : k.p0 g = 1 := by
    rw [← hπ g]
    exact hg0
  have hpk : toUpl Ω L (W.resP L Ω g) ∈ k.p.ker := by
    rw [MonoidHom.mem_ker, ← k.galois_link_projection_coe, hp0]
    rfl
  obtain ⟨τ, hτK, hτeq⟩ := hpker hpk
  have hτg : τ = W.resP L Ω g := toUpl_inj hτeq
  obtain ⟨m, hm, hmeq⟩ := hτK
  have hpr : V.pr g = m := by
    apply Subtype.ext
    change toGS Ω V.S' (W.resP L Ω g) = (m : V.frame.Γ)
    rw [← hτg]
    exact hmeq.symm
  rw [hpr]
  exact hm
