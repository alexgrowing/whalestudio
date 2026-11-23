import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.GLinkQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.LevelS
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.InflKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.TameEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.IsClosedOfClosedFiniteIndex
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.PtTail
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.GlobEuler
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.DecZhat
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.QuotProf

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.Fr UpperTheory.V.GC

section SlopeTestRemainingChoices

private theorem hg_rank {k V W : Type} [Field k] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (f : V →ₗ[k] W) [Module.Finite k (LinearMap.ker f)] [Module.Finite k W] (U : Submodule k V) (U' : Submodule k W)
    (h : ∀ x ∈ U, f x ∈ U') :
    Module.Finite k V ∧ finrank k U ≤ finrank k (LinearMap.ker f) + finrank k U' := by
  haveI : Module.Finite k V := by
    haveI := Module.Finite.equiv f.quotKerEquivRange.symm
    exact Module.Finite.of_submodule_quotient (LinearMap.ker f)
  refine ⟨this, ?_⟩
  have e := LinearMap.finrank_range_add_finrank_ker (f.domRestrict U)
  have a : finrank k (LinearMap.range (f.domRestrict U)) ≤ finrank k U' := Submodule.finrank_mono (by
    rintro _ ⟨x, rfl⟩
    exact h x.1 x.2)
  have b : finrank k (LinearMap.ker (f.domRestrict U)) ≤ finrank k (LinearMap.ker f) := by
    rw [← Submodule.finrank_map_subtype_eq]
    refine Submodule.finrank_mono ?_
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  omega

private theorem hg_eqHom {k Γ Γ' M : Type} [Field k] [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ']
    [AddCommGroup M] [Module k M] (ρ : Representation k Γ' M) (t : Γ →* Γ') (ht : Continuous t) (D J : Subgroup Γ)
    [Module.Finite k (eqHom (ρ.comp t) D J)] :
    Module.Finite k (eqHom ρ (D.map t) (J.map t)) ∧
      finrank k (eqHom ρ (D.map t) (J.map t)) ≤ finrank k (eqHom (ρ.comp t) D J) := by
  let u : J → J.map t := fun j => ⟨t j.1, j.1, j.2, rfl⟩
  have hu : Continuous u := (ht.comp continuous_subtype_val).subtype_mk _
  let φ : eqHom ρ (D.map t) (J.map t) →ₗ[k] eqHom (ρ.comp t) D J :=
    { toFun := fun f => ⟨fun j => f.1 (u j), f.2.1.comp_continuous hu, fun a b => by
          rw [← f.2.2.1]
          exact congrArg f.1 (Subtype.ext (map_mul t a.1 b.1)),
        fun d hd j j' h => f.2.2.2 (t d) ⟨d, hd, rfl⟩ (u j) (u j') (by
          change t j'.1 = t d * t j.1 * (t d)⁻¹
          rw [h, map_mul, map_mul, map_inv])⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hφ : Function.Injective φ := by
    intro f g h
    refine Subtype.ext (funext ?_)
    rintro ⟨_, j, hj, rfl⟩
    exact congrFun (congrArg Subtype.val h) ⟨j, hj⟩
  exact ⟨Module.Finite.of_injective φ hφ, LinearMap.finrank_le_finrank_of_injective hφ⟩

private theorem hg_loc {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ)
    [Fact l.Prime] {v : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω} (hA : IsPlaceOver A v)
    (K : Subgroup (G F Ω)) [K.Normal] (hK : IsOpen (K : Set (G F Ω))) (hl : ¬ l ∣ K.index)
    {Γ : Type} [Group Γ] [TopologicalSpace Γ] (π : Dec (F := F) A →* Γ) (hπ : Continuous π)
    (h1 : ∀ g : Dec (F := F) A, g.1 ∈ Ine (F := F) A ⊓ K → π g = 1)
    {k : Type} [Field k] [Finite k] [CharP k l] {M : Type} [AddCommGroup M] [Module k M] [Module.Finite k M]
    [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k Γ M) (hρ : ContAction ρ) (x : H2 ρ) :
    resH2 ρ π hπ x = 0 := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : IsGalois F Ω := {}
  haveI : CompactSpace (Dec (F := F) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
  obtain ⟨φ, -, h2, h3⟩ := decZhat F Ω v A hA
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  haveI : ((Ine (F := F) A ⊓ K).subgroupOf (Dec (F := F) A)).Normal :=
    inferInstanceAs ((Ine (F := F) A).subgroupOf (Dec (F := F) A) ⊓ K.subgroupOf _).Normal
  obtain ⟨b, hb, -, hz⟩ := H2_unramified_inflation l (Dec (F := F) A) k M (ρ.comp π) (hρ.comp (hπ.prodMap continuous_id))
    ((Ine (F := F) A).subgroupOf (Dec (F := F) A)) ((Ine (F := F) A ⊓ K).subgroupOf (Dec (F := F) A)) φ
    (Subgroup.comap_mono inf_le_left)
    (((isClosed_Ine A).inter (K.isClosed_of_isOpen hK)).preimage continuous_subtype_val)
    (by
      rw [Subgroup.relIndex_subgroupOf (Ine_le_Dec _), Subgroup.inf_relIndex_left]
      exact fun h => hl (h.trans (Subgroup.relIndex_dvd_index_of_normal _ _)))
    (fun j hj => by rw [MonoidHom.comp_apply, h1 j hj, map_one]) h2 h3 (restrictCocycles2 ρ π hπ z)
    (fun s t j hj j' hj' => by simp only [restrictCocycles2_apply, map_mul, h1 j hj, h1 j' hj', mul_one])
  change Submodule.Quotient.mk (restrictCocycles2 ρ π hπ z) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  exact (separated_dvr_second_cohomology_mem _ _).2 ⟨b, hb.continuous, funext fun p => (hz p.1 p.2).symm⟩

end SlopeTestRemainingChoices

theorem UpperTheory.V.GC.H2_galois_quotient_eq :
    Hypotheses₂ → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], IsTotallyReal F → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (K : Subgroup (G F Ω)) (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] (π : G F Ω →* Γ) (h : GLink l S K π) (k : Type) [Field k] [Finite k] [CharP k l] (M : Type) [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k Γ M), ContAction ρ →
    ∀ c : InfinitePlace F → G F Ω, (∀ w, IsCCAt w (c w)) → ∀ (A : S → ValuationSubring Ω), (∀ v, IsPlaceOver (A v) v.1) → Module.Finite k (H1 ρ) ∧ Module.Finite k (H2 ρ) ∧
    finrank k (Sha2 ρ (fun v => π.comp (Dec (F := F) (A v)).subtype) fun v => h.cont.comp continuous_subtype_val) + ∑ v, finrank k (H2 (ρ.comp (π.comp (Dec (F := F) (A v)).subtype))) + finrank k (H0 ρ) + finrank ℚ F * finrank k M ≤
      finrank k (H1 ρ) + ∑ w, finrank k (LinearMap.ker (ρ (π (c w)) - 1)) + finrank k (Loc.H0dual (cycF F Ω l k) (ρ.comp π)) := by
  intro P F Ω _ _ _ _ _ l _ hF S K Γ _ _ _ _ _ _ π h k _ _ _ M _ _ _ _ _ ρ hρ c hc A hA
  classical
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : IsGalois F Ω := {}
  haveI := h.normal
  obtain ⟨A', hA', rfl⟩ : ∃ A' : HeightOneSpectrum (𝓞 F) → ValuationSubring Ω, (∀ v, IsPlaceOver (A' v) v) ∧
      A = fun v : S => A' v.1 := by
    refine ⟨fun v => if hv : v ∈ S then A ⟨v, hv⟩ else (exists_isPlaceOver Ω v).choose, fun v => ?_, funext fun v => ?_⟩
    · by_cases hv : v ∈ S
      · simpa only [dif_pos hv] using hA ⟨v, hv⟩
      · simpa only [dif_neg hv] using (exists_isPlaceOver Ω v).choose_spec
    · simp only [dif_pos v.2]
  obtain ⟨S', p, hSS, hp, hps, rfl, hker⟩ := levelS F Ω l S K Γ π h
  haveI hcl := isClosed_NS Ω (S' : Set (HeightOneSpectrum (𝓞 F)))
  haveI : TotallyDisconnectedSpace (GS Ω (S' : Set (HeightOneSpectrum (𝓞 F)))) :=
    (AlgebraTools.totallyDisconnected_quot _ _ hcl).1
  have hS' : ContainsAbove S' l := fun v hv => hSS (h.above v hv)
  have hρ' : ContAction (ρ.comp p) := hρ.comp (hp.prodMap continuous_id)
  have hkill : ∀ q, q ∉ S → ∀ g ∈ Ine (F := F) (A' q) ⊓ K, p (toGS Ω _ g) = 1 := by
    intro q hq g hg
    have : g ∈ (p.comp (toGS Ω _)).ker := by
      rw [h.ker]
      refine Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_)
      simp only [Set.mem_iUnion]
      exact ⟨q, hq, A' q, hA' q, hg⟩
    exact this
  let n : HeightOneSpectrum (𝓞 F) → ℕ := fun v =>
    finrank k (H2 ((ρ.comp p).comp (locHom (S' : Set (HeightOneSpectrum (𝓞 F))) (A' v))))
  have hq : ∀ q : {v // v ∈ S' ∧ v ∉ S},
      Module.Finite k (eqHom (ρ.comp p) ((Dec (F := F) (A' q.1)).map (toGS Ω _)) ((Ine (F := F) (A' q.1) ⊓ K).map (toGS Ω _))) ∧
      finrank k (eqHom (ρ.comp p) ((Dec (F := F) (A' q.1)).map (toGS Ω _)) ((Ine (F := F) (A' q.1) ⊓ K).map (toGS Ω _))) ≤
        n q.1 := by
    intro q
    obtain ⟨a1, a2⟩ := tameEq P.lf P.lt P.le F Ω l q.1 (A' q.1) (hA' _) (fun hv => q.2.2 (h.above _ hv)) K h.isOpen h.idx
      k M ((ρ.comp p).comp (toGS Ω _)) (hρ'.comp ((continuous_toGS Ω _).prodMap continuous_id))
      (fun g hg => by rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hkill _ q.2.2 g hg, map_one])
    obtain ⟨b1, b2⟩ := hg_eqHom (ρ.comp p) (toGS Ω _) (continuous_toGS Ω _) (Dec (F := F) (A' q.1))
      (Ine (F := F) (A' q.1) ⊓ K)
    exact ⟨b1, b2.trans a2.le⟩
  obtain ⟨g1, g2, g3⟩ := globEuler P.gf P.ge F Ω l h.odd hF S' hS' k M (ρ.comp p) hρ' c hc
  have tail := ptTail P.lf P.gf P.pt F Ω l h.odd S' hS' (fun v => A' v.1) (fun v => hA' v.1) k M (ρ.comp p) hρ'
  letI : Fintype {v // v ∈ S' ∧ v ∉ S} := Fintype.subtype (S' \ S) fun _ => Finset.mem_sdiff
  obtain ⟨i1, i2, i3⟩ := inflKer l _ Γ p hp hps k M ρ hρ {v // v ∈ S' ∧ v ∉ S}
    (fun q => (Dec (F := F) (A' q.1)).map (toGS Ω _)) (fun q => (Ine (F := F) (A' q.1) ⊓ K).map (toGS Ω _))
    (hker A' hA') (fun q => (hq q).1) g1
  obtain ⟨r1, r2⟩ := hg_rank (resH2 ρ p hp)
    (Sha2 ρ (fun v : S => (p.comp (toGS Ω _)).comp (Dec (F := F) (A' v.1)).subtype) fun v => h.cont.comp continuous_subtype_val)
    (Sha2 (ρ.comp p) (fun v : S' => locHom (S' : Set (HeightOneSpectrum (𝓞 F))) (A' v.1)) fun v => continuous_locHom _ (A' v.1))
    (by
      intro x hx
      simp only [Sha2, Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
      intro v
      have e : resH2 (ρ.comp p) (locHom (S' : Set (HeightOneSpectrum (𝓞 F))) (A' v.1)) (continuous_locHom _ _) (resH2 ρ p hp x) =
          resH2 ρ ((p.comp (toGS Ω _)).comp (Dec (F := F) (A' v.1)).subtype) (h.cont.comp continuous_subtype_val) x := by
        obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        rfl
      refine e.trans ?_
      by_cases hv : v.1 ∈ S
      · exact hx ⟨v.1, hv⟩
      · exact hg_loc l (hA' v.1) K h.isOpen h.idx _ _ (fun g hg => hkill _ hv g.1 hg) ρ hρ x)
  refine ⟨i1, r1, ?_⟩
  have e0 : H0 (ρ.comp p) = H0 ρ := by
    ext m
    exact ⟨fun hm g => by obtain ⟨g, rfl⟩ := hps g; exact hm g, fun hm g => hm (p g)⟩
  rw [e0] at g3
  have s1 : ∑ v : S', n v.1 = ∑ v : S, n v.1 + ∑ q : {v // v ∈ S' ∧ v ∉ S}, n q.1 := by
    rw [Finset.sum_coe_sort S' n, Finset.sum_coe_sort S n, ← Finset.sum_sdiff hSS, add_comm,
      Finset.sum_subtype (S' \ S) (p := fun v => v ∈ S' ∧ v ∉ S) (fun _ => Finset.mem_sdiff) n]
  have s2 := Finset.sum_le_sum (s := Finset.univ) fun q _ => (hq q).2
  change _ + ∑ v : S', n v.1 = _ at tail
  beta_reduce
  change _ + ∑ v : S, n v.1 + _ + _ ≤ _ + ∑ w, finrank k (LinearMap.ker ((ρ.comp p) (toGS Ω _ (c w)) - 1)) +
    finrank k (Loc.H0dual (cycF F Ω l k) ((ρ.comp p).comp (toGS Ω _)))
  omega
