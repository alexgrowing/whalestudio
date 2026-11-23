import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondSelmerSpanBoundAtAllLevels
import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LimKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LimElt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.FiniteHomOfTopFG
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem exists_tendsto_ultrafilter_of_compact {X : Type} [TopologicalSpace X] [CompactSpace X] (U : Ultrafilter ℕ) (a : ℕ → X) :
    ∃ x, Tendsto a (U : Filter ℕ) (nhds x) := by
  obtain ⟨x, -, hx⟩ := isCompact_univ.ultrafilter_le_nhds (U.map a) (by simp)
  exact ⟨x, by rwa [Ultrafilter.coe_map] at hx⟩

private theorem inv_mul_mem_limKer_of_tendsto_of_eventually_eq {Ph : Type} [Group Ph] [TopologicalSpace Ph] [IsTopologicalGroup Ph]
    {Γ : ℕ → Type} [∀ N, Group (Γ N)] (π : ∀ N, Ph →* Γ N) (U : Ultrafilter ℕ)
    (a b : ℕ → Ph) (x y : Ph) (ha : Tendsto a (U : Filter ℕ) (nhds x))
    (hb : Tendsto b (U : Filter ℕ) (nhds y))
    (hab : ∀ᶠ N in (U : Filter ℕ), π N (a N) = π N (b N)) :
    x⁻¹ * y ∈ limKer (U : Filter ℕ) (fun N => (π N).ker) := by
  rw [mem_limKer]
  intro O
  have hO : ((O.toOpenSubgroup : Subgroup Ph) : Set Ph) ∈ nhds (1 : Ph) :=
    O.toOpenSubgroup.isOpen.mem_nhds O.toOpenSubgroup.one_mem
  have h1 : Tendsto (fun N => x⁻¹ * a N) (U : Filter ℕ) (nhds 1) := by
    simpa using (tendsto_const_nhds (x := x⁻¹)).mul ha
  have h2 : Tendsto (fun N => (b N)⁻¹ * y) (U : Filter ℕ) (nhds 1) := by
    simpa using hb.inv.mul (tendsto_const_nhds (x := y))
  filter_upwards [h1 hO, h2 hO, hab] with N h1N h2N hN
  have e : x⁻¹ * y = (x⁻¹ * a N) * ((a N)⁻¹ * b N) * ((b N)⁻¹ * y) := by group
  rw [e]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right h1N)
    (Subgroup.mem_sup_left ?_)) (Subgroup.mem_sup_right h2N)
  rw [MonoidHom.mem_ker, map_mul, map_inv, hN, inv_mul_cancel]

private theorem exists_eventually_eq_of_eventually_mem_finite {β : Type} (U : Ultrafilter ℕ) (g : ℕ → β) (A : Set β) (hA : A.Finite)
    (hg : ∀ᶠ N in (U : Filter ℕ), g N ∈ A) : ∃ c ∈ A, ∀ᶠ N in (U : Filter ℕ), g N = c := by
  have h : (⋃ c ∈ A, {N | g N = c}) ∈ (U : Filter ℕ) := by
    filter_upwards [hg] with N hN
    exact Set.mem_biUnion hN rfl
  exact (Ultrafilter.finite_biUnion_mem_iff hA).1 h

private theorem continuous_section_quotient_of_ker_le_open {Ph G : Type} [Group Ph] [TopologicalSpace Ph] [IsTopologicalGroup Ph]
    [CompactSpace Ph] [Group G] [TopologicalSpace G] [T2Space G] (π : Ph →* G) (hπ : Continuous π)
    (σ : G → Ph) (hσ : ∀ γ, π (σ γ) = γ) (S : Subgroup Ph) (hS : IsOpen (S : Set Ph))
    (hk : π.ker ≤ S) : Continuous (fun γ => (σ γ : Ph ⧸ S)) := by
  haveI : DiscreteTopology (Ph ⧸ S) := QuotientGroup.discreteTopology hS
  have hmk : Continuous (QuotientGroup.mk : Ph → Ph ⧸ S) := continuous_quot_mk
  have key : ∀ s : Set (Ph ⧸ S), (fun γ => (σ γ : Ph ⧸ S)) ⁻¹' s =
      π '' ((QuotientGroup.mk : Ph → Ph ⧸ S) ⁻¹' s) := by
    intro s
    ext γ
    constructor
    · intro h
      exact ⟨σ γ, h, hσ γ⟩
    · rintro ⟨a, ha, rfl⟩
      have e : (σ (π a) : Ph ⧸ S) = (a : Ph ⧸ S) := by
        rw [QuotientGroup.eq]
        apply hk
        rw [MonoidHom.mem_ker, map_mul, map_inv, hσ, inv_mul_cancel]
      simp only [Set.mem_preimage, e]
      exact ha
  rw [continuous_discrete_rng]
  intro z
  have hc : IsClosed (π '' ((QuotientGroup.mk : Ph → Ph ⧸ S) ⁻¹' {z}ᶜ)) :=
    hπ.isClosedMap _ ((isClosed_discrete ({z}ᶜ : Set (Ph ⧸ S))).preimage hmk)
  rw [← key, Set.preimage_compl] at hc
  exact isClosed_compl_iff.1 hc

private theorem mul_one_sub_add_psi_eq_of_conj {Ph Y : Type} [Group Ph] [TopologicalSpace Ph] [IsTopologicalGroup Ph]
    [CompactSpace Ph] [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y]
    {Γ : ℕ → Type} [∀ N, Group (Γ N)] [∀ N, TopologicalSpace (Γ N)] [∀ N, T2Space (Γ N)]
    (π : ∀ N, Ph →* Γ N) (hπ : ∀ N, Continuous (π N))
    (σ : ∀ N, Γ N → Ph) (hσ : ∀ N γ, π N (σ N γ) = γ)
    (U : Ultrafilter ℕ) (P : Subgroup Y) [P.Normal] (f : ∀ N, Y →* Γ N)
    (hP : TopFG (Y ⧸ P)) (hf : ∀ N, Continuous (f N) ∧ P ≤ (f N).ker)
    (V : OpenNormalSubgroup Ph) :
    ∃ S : Subgroup Ph, IsOpen (S : Set Ph) ∧ ∃ c : Y → Ph ⧸ S, Continuous c ∧
      ∀ᶠ N in (U : Filter ℕ), (π N).ker ⊔ (V.toOpenSubgroup : Subgroup Ph) = S ∧
        ∀ y, ((σ N (f N y) : Ph) : Ph ⧸ S) = c y := by
  set W : Subgroup Ph := (V.toOpenSubgroup : Subgroup Ph) with hW
  have hWo : IsOpen (W : Set Ph) := V.toOpenSubgroup.isOpen
  haveI : Finite (Ph ⧸ W) := Subgroup.quotient_finite_of_isOpen W hWo
  have hmem : ∀ S : Subgroup Ph, W ≤ S → ∀ x : Ph,
      x ∈ S ↔ (x : Ph ⧸ W) ∈ (QuotientGroup.mk : Ph → Ph ⧸ W) '' (S : Set Ph) := by
    intro S hS x
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨s, hs, he⟩
      rw [QuotientGroup.eq] at he
      have e : x = s * (s⁻¹ * x) := by group
      rw [e]
      exact S.mul_mem hs (hS he)
  have hA1 : {S : Subgroup Ph | W ≤ S}.Finite := by
    apply Set.Finite.of_finite_image (f := fun S : Subgroup Ph =>
      (QuotientGroup.mk : Ph → Ph ⧸ W) '' (S : Set Ph)) (Set.toFinite _)
    intro S1 h1 S2 h2 he
    ext x
    rw [hmem S1 h1, hmem S2 h2]
    simp only at he
    rw [he]
  obtain ⟨S, hWS, hS⟩ := exists_eventually_eq_of_eventually_mem_finite U (fun N => (π N).ker ⊔ W) _ hA1
    (Filter.Eventually.of_forall fun N => show W ≤ (π N).ker ⊔ W from le_sup_right)
  have hSo : IsOpen (S : Set Ph) := Subgroup.isOpen_mono hWS hWo
  obtain ⟨N0, hN0⟩ := hS.exists
  haveI hSn : S.Normal := by
    rw [← hN0]
    infer_instance
  haveI : DiscreteTopology (Ph ⧸ S) := QuotientGroup.discreteTopology hSo
  haveI : Finite (Ph ⧸ S) := Subgroup.quotient_finite_of_isOpen S hSo
  have hΦ := (finite_hom_of_topFG (Y ⧸ P) hP).1 (Ph ⧸ S)
  set A2 : Set (Y → Ph ⧸ S) := {φ | Continuous φ ∧
    ∃ θ ∈ {θ : Y ⧸ P →* Ph ⧸ S | IsOpen (θ.ker : Set (Y ⧸ P))},
      φ = fun y : Y => θ (y : Y ⧸ P)} with hA2
  have hA2f : A2.Finite := by
    apply (hΦ.image (fun θ : Y ⧸ P →* Ph ⧸ S => fun y : Y => θ (y : Y ⧸ P))).subset
    rintro φ ⟨-, θ, hθ, rfl⟩
    exact ⟨θ, hθ, rfl⟩
  have hg2 : ∀ᶠ N in (U : Filter ℕ), (fun y => ((σ N (f N y) : Ph) : Ph ⧸ S)) ∈ A2 := by
    filter_upwards [hS] with N hN
    have kle : (π N).ker ≤ S := hN ▸ le_sup_left
    have hcont : Continuous (fun y => ((σ N (f N y) : Ph) : Ph ⧸ S)) :=
      (continuous_section_quotient_of_ker_le_open (π N) (hπ N) (σ N) (hσ N) S hSo kle).comp (hf N).1
    refine ⟨hcont, ?_⟩
    let φY : Y →* Ph ⧸ S := MonoidHom.mk' (fun y => ((σ N (f N y) : Ph) : Ph ⧸ S)) (by
      intro a b
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq]
      apply kle
      simp [MonoidHom.mem_ker, hσ])
    have hPle : P ≤ φY.ker := by
      intro p hp
      rw [MonoidHom.mem_ker]
      show ((σ N (f N p) : Ph) : Ph ⧸ S) = 1
      rw [(hf N).2 hp, QuotientGroup.eq_one_iff]
      apply kle
      simp [MonoidHom.mem_ker, hσ]
    refine ⟨QuotientGroup.lift P φY hPle, ?_, rfl⟩
    have hpre : (QuotientGroup.mk : Y → Y ⧸ P) ⁻¹' ((QuotientGroup.lift P φY hPle).ker : Set (Y ⧸ P))
        = (fun y => ((σ N (f N y) : Ph) : Ph ⧸ S)) ⁻¹' {1} := by
      ext y
      simp [MonoidHom.mem_ker, φY]
    have ho := hcont.isOpen_preimage _ (isOpen_discrete ({1} : Set (Ph ⧸ S)))
    rw [← hpre] at ho
    have ho2 := (QuotientGroup.isOpenMap_coe (N := P)) _ ho
    rwa [Set.image_preimage_eq _ QuotientGroup.mk_surjective] at ho2
  obtain ⟨c, hcA, hc⟩ := exists_eventually_eq_of_eventually_mem_finite U _ A2 hA2f hg2
  refine ⟨S, hSo, c, hcA.1, ?_⟩
  filter_upwards [hS, hc] with N h1 h2
  exact ⟨h1, fun y => congrFun h2 y⟩

theorem UpperTheory.V.Pa.in_lim :
    ∀ (Ph Y : Type) [Group Ph] [TopologicalSpace Ph] [IsTopologicalGroup Ph] [CompactSpace Ph] [TotallyDisconnectedSpace Ph] [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y] [CompactSpace Y] [TotallyDisconnectedSpace Y] (Γ : ℕ → Type) [∀ N, Group (Γ N)] [∀ N, TopologicalSpace (Γ N)] [∀ N, IsTopologicalGroup (Γ N)] [∀ N, CompactSpace (Γ N)] [∀ N, TotallyDisconnectedSpace (Γ N)] (π : ∀ N, Ph →* Γ N) (U : Ultrafilter ℕ) (P : Subgroup Y) [P.Normal] (f : ∀ N, Y →* Γ N), (∀ N, Continuous (π N) ∧ Function.Surjective (π N)) → TopFG (Y ⧸ P) → (∀ N, Continuous (f N) ∧ P ≤ (f N).ker) → ∃ F : Y →* Ph ⧸ limKer (U : Filter ℕ) (fun N => (π N).ker), Continuous F ∧ ∀ V : OpenNormalSubgroup Ph, ∀ᶠ N in (U : Filter ℕ), ∀ y, Close (π N) (QuotientGroup.mk' (limKer (U : Filter ℕ) fun N => (π N).ker)) V.toSubgroup (f N y) (F y) := by
  intro Ph Y _ _ _ _ _ _ _ _ _ _ Γ _ _ _ _ _ π U P _ f hπ hP hf
  haveI : ∀ N, T2Space (Γ N) := fun N => inferInstance
  choose σ hσ using fun N (γ : Γ N) => (hπ N).2 γ
  choose h hh using fun y => exists_tendsto_ultrafilter_of_compact U (fun N => σ N (f N y))
  have hmul : ∀ a b, ((h (a * b) : Ph) : Ph ⧸ limKer (U : Filter ℕ) fun N => (π N).ker) =
      (h a : Ph ⧸ limKer (U : Filter ℕ) fun N => (π N).ker) * (h b) := by
    intro a b
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq]
    refine inv_mul_mem_limKer_of_tendsto_of_eventually_eq π U _ _ _ _ (hh (a * b)) ((hh a).mul (hh b)) ?_
    filter_upwards with N
    simp [hσ, map_mul]
  refine ⟨MonoidHom.mk' (fun y => (h y : Ph ⧸ limKer (U : Filter ℕ) fun N => (π N).ker)) hmul, ?_, ?_⟩
  · apply continuous_of_continuousAt_one
    rw [ContinuousAt, map_one, Filter.tendsto_def]
    intro W hW
    have hmkc : Continuous (QuotientGroup.mk : Ph → Ph ⧸ limKer (U : Filter ℕ) fun N => (π N).ker) :=
      continuous_quot_mk
    have h1 : (QuotientGroup.mk : Ph → Ph ⧸ limKer (U : Filter ℕ) fun N => (π N).ker) ⁻¹' W ∈ nhds (1 : Ph) :=
      hmkc.continuousAt.preimage_mem_nhds (by rw [QuotientGroup.mk_one]; exact hW)
    obtain ⟨t, ht, hto, ht1⟩ := mem_nhds_iff.1 h1
    obtain ⟨V, hV⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hto ht1
    obtain ⟨S, hSo, c, hc, hev⟩ := mul_one_sub_add_psi_eq_of_conj π (fun N => (hπ N).1) σ hσ U P f hP hf V
    haveI : DiscreteTopology (Ph ⧸ S) := QuotientGroup.discreteTopology hSo
    rw [mem_nhds_iff]
    refine ⟨c ⁻¹' {c 1}, ?_, hc.isOpen_preimage _ (isOpen_discrete _), rfl⟩
    intro y hy
    have hin : ∀ᶠ N in (U : Filter ℕ),
        σ N (f N y) ∈ (π N).ker ⊔ (V.toOpenSubgroup : Subgroup Ph) := by
      filter_upwards [hev] with N hN
      obtain ⟨hN, hcN⟩ := hN
      have e1 : ((σ N (f N y) : Ph) : Ph ⧸ S) = ((σ N (f N 1) : Ph) : Ph ⧸ S) := by
        rw [hcN y, hcN 1]
        exact hy
      rw [QuotientGroup.eq] at e1
      have hk1 : σ N (f N 1) ∈ (π N).ker := by simp [MonoidHom.mem_ker, hσ]
      have e2 : σ N (f N y) = σ N (f N 1) * ((σ N (f N 1))⁻¹ * σ N (f N y)) := by group
      rw [e2]
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_left hk1) ?_
      rw [hN]
      simpa using S.inv_mem e1
    have hdec : ∀ N, ∃ v ∈ (V.toOpenSubgroup : Subgroup Ph),
        σ N (f N y) ∈ (π N).ker ⊔ (V.toOpenSubgroup : Subgroup Ph) →
          σ N (f N y) * v⁻¹ ∈ (π N).ker := by
      intro N
      by_cases hm : σ N (f N y) ∈ (π N).ker ⊔ (V.toOpenSubgroup : Subgroup Ph)
      · rw [← SetLike.mem_coe, Subgroup.mul_normal] at hm
        obtain ⟨k, hk, v, hv, hkv⟩ := hm
        refine ⟨v, hv, fun _ => ?_⟩
        rw [← hkv, mul_inv_cancel_right]
        exact hk
      · exact ⟨1, one_mem _, fun h' => absurd h' hm⟩
    choose v hvV hv using hdec
    obtain ⟨w, hw⟩ := exists_tendsto_ultrafilter_of_compact U v
    have hwV : w ∈ (V.toOpenSubgroup : Subgroup Ph) :=
      V.toOpenSubgroup.isClosed.mem_of_tendsto hw (Filter.Eventually.of_forall hvV)
    have hlim := inv_mul_mem_limKer_of_tendsto_of_eventually_eq π U (fun N => σ N (f N y) * (v N)⁻¹) (fun _ => 1) (h y * w⁻¹) 1
      ((hh y).mul hw.inv) tendsto_const_nhds (by
        filter_upwards [hin] with N hN
        rw [map_one]
        exact (MonoidHom.mem_ker).1 (hv N hN))
    have hm' : h y * w⁻¹ ∈ limKer (U : Filter ℕ) (fun N => (π N).ker) := by
      simpa using inv_mem hlim
    have hconj := (limKer_normal (U : Filter ℕ) (fun N => (π N).ker)).conj_mem _ hm' w⁻¹
    have e3 : w⁻¹ * (h y * w⁻¹) * w⁻¹⁻¹ = w⁻¹ * h y := by group
    rw [e3] at hconj
    show ((h y : Ph) : Ph ⧸ limKer (U : Filter ℕ) fun N => (π N).ker) ∈ W
    have e4 : ((h y : Ph) : Ph ⧸ limKer (U : Filter ℕ) fun N => (π N).ker) =
        ((w : Ph) : Ph ⧸ limKer (U : Filter ℕ) fun N => (π N).ker) := by
      rw [QuotientGroup.eq]
      simpa using inv_mem hconj
    rw [e4]
    exact ht (hV hwV)
  · intro V
    obtain ⟨S, hSo, c, hc, hev⟩ := mul_one_sub_add_psi_eq_of_conj π (fun N => (hπ N).1) σ hσ U P f hP hf V
    have hVS : ∀ᶠ N in (U : Filter ℕ), (V.toOpenSubgroup : Subgroup Ph) ≤ S := by
      filter_upwards [hev] with N hN
      rw [← hN.1]
      exact le_sup_right
    have hcy : ∀ y, c y = ((h y : Ph) : Ph ⧸ S) := by
      intro y
      have hO : ((V.toOpenSubgroup : Subgroup Ph) : Set Ph) ∈ nhds (1 : Ph) :=
        V.toOpenSubgroup.isOpen.mem_nhds V.toOpenSubgroup.one_mem
      have ht : Tendsto (fun N => (σ N (f N y))⁻¹ * h y) (U : Filter ℕ) (nhds 1) := by
        simpa using (hh y).inv.mul (tendsto_const_nhds (x := h y))
      obtain ⟨N, ⟨-, hN⟩, hle, hmemN⟩ := (hev.and (hVS.and (ht hO))).exists
      rw [← hN y, QuotientGroup.eq]
      exact hle hmemN
    filter_upwards [hev] with N hN
    obtain ⟨hN, hcN⟩ := hN
    intro y
    have e1 : ((σ N (f N y) : Ph) : Ph ⧸ S) = ((h y : Ph) : Ph ⧸ S) := by rw [hcN y, hcy y]
    rw [QuotientGroup.eq, ← hN, ← SetLike.mem_coe, Subgroup.mul_normal] at e1
    obtain ⟨k, hk, v, hv, hkv⟩ := e1
    refine ⟨σ N (f N y) * k, h y, ?_, rfl, ?_⟩
    · rw [map_mul, hσ, (MonoidHom.mem_ker).1 hk, mul_one]
    · have e : (σ N (f N y) * k)⁻¹ * h y = k⁻¹ * ((σ N (f N y))⁻¹ * h y) := by group
      rw [e, ← hkv, inv_mul_cancel_left]
      exact hv
