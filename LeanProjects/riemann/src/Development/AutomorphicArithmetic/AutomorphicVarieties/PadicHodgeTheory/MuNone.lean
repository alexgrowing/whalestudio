import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IdealValuations.LocRootsY
import GroundTheory.LocalFields.KroneckerWeber
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OpenField
import GroundTheory.LocalFields.LocalArtinCompletion
import GroundTheory.LocalFields.PrincipalUnitsRank
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixingSubgroupEquivBicontinuous

open Formalism.BasicNotions Formalism.BasicNotions.Loc UpperTheory.V.Loc Topology

private theorem mn_sep {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (h : TopologicalAbelianization G) (hh : h ≠ 1) :
    ∃ V : Subgroup (TopologicalAbelianization G), IsOpen (V : Set (TopologicalAbelianization G)) ∧ h ∉ V := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective h
  have hg : g ∉ (commutator G).topologicalClosure := fun hm => hh ((QuotientGroup.eq_one_iff g).2 hm)
  have hS : IsOpen {x : G | x * g ∉ ((commutator G).topologicalClosure : Set G)} :=
    (Subgroup.isClosed_topologicalClosure _).isOpen_compl.preimage (continuous_mul_right g)
  have h1 : (1 : G) ∈ {x : G | x * g ∉ ((commutator G).topologicalClosure : Set G)} := by
    show 1 * g ∉ ((commutator G).topologicalClosure : Set G)
    rw [one_mul]
    exact hg
  obtain ⟨W, hW⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hS h1
  refine ⟨(W : Subgroup G).map (QuotientGroup.mk' _), ?_, ?_⟩
  · rw [Subgroup.coe_map]
    exact QuotientGroup.isOpenMap_coe _ W.isOpen
  · rintro ⟨w, hw, he⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq] at he
    exact hW (inv_mem hw) he

private theorem mn_core {A M : Type} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [CompactSpace A] [T2Space A] [CommGroup M] (r : M →* A) (hr : DenseRange r) {q : ℕ} (hq : q ≠ 0)
    (hM : ∀ x : M, x ^ q = 1 → x = 1)
    (hopen : ∀ n : ℕ, n ≠ 0 → ∃ V : Set A, IsOpen V ∧ 1 ∈ V ∧ ∀ x, r x ∈ V → ∃ z, x = z ^ n)
    (a : A) (ha : a ^ q = 1) (n : ℕ) (hn : n ≠ 0) : ∃ z, a = z ^ n := by
  have hP : IsClosed (Set.range fun z : A => z ^ n) := (isCompact_range (continuous_pow n)).isClosed
  obtain ⟨V, hVo, hV1, hV⟩ := hopen (q * n) (mul_ne_zero hq hn)
  suffices hs : a ∈ closure (Set.range fun z : A => z ^ n) by
    rw [hP.closure_eq] at hs
    obtain ⟨z, hz⟩ := hs
    exact ⟨z, hz.symm⟩
  rw [mem_closure_iff]
  intro o ho hao
  have hW : IsOpen (o ∩ {y : A | y ^ q ∈ V}) := ho.inter (hVo.preimage (continuous_pow q))
  have haW : a ∈ o ∩ {y : A | y ^ q ∈ V} := ⟨hao, by show a ^ q ∈ V; rw [ha]; exact hV1⟩
  obtain ⟨x, hx1, hx2⟩ := hr.exists_mem_open hW ⟨a, haW⟩
  have hx3 : r (x ^ q) ∈ V := by
    rw [map_pow]
    exact hx2
  obtain ⟨z, hz⟩ := hV (x ^ q) hx3
  have hxz : x = z ^ n := by
    have h1 : (x * (z ^ n)⁻¹) ^ q = 1 := by
      rw [mul_pow, inv_pow, ← pow_mul, mul_comm n q, ← hz, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hM _ h1)
  exact ⟨r x, hx1, r z, by rw [hxz, map_pow]⟩

open GroundTheory.LocalField ValuativeRel GroundTheory.LocalField.Abstract in
private theorem mn_field (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [CharZero K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    {q : ℕ} (hq : q ≠ 0) (hM : ∀ x : Kˣ, x ^ q = 1 → x = 1)
    (a : TopologicalAbelianization (Ω ≃ₐ[K] Ω)) (ha : a ^ q = 1) : a = 1 := by
  haveI : IsClosed ((commutator (Ω ≃ₐ[K] Ω)).topologicalClosure : Set (Ω ≃ₐ[K] Ω)) :=
    Subgroup.isClosed_topologicalClosure _
  have hopen : ∀ n : ℕ, n ≠ 0 → ∃ V : Set (TopologicalAbelianization (Ω ≃ₐ[K] Ω)), IsOpen V ∧ 1 ∈ V ∧
      ∀ x, localReciprocityLimit K Ω x ∈ V → ∃ z, x = z ^ n := by
    intro n hn
    haveI : Finite (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) := finite_quotient_range_pow_of_charZero hn
    let H : openFiniteIndex Kˣ := ⟨(powMonoidHom n : Kˣ →* Kˣ).range,
      isOpen_range_pow (Nat.cast_ne_zero.mpr hn), Subgroup.finiteIndex_of_finite_quotient⟩
    haveI := openCompletion.discreteTopology_quotient H
    refine ⟨(fun b => artinCoord K Ω H (topologicalAbelianizationEquiv K Ω b)) ⁻¹' {1}, ?_, ?_, ?_⟩
    · exact (isOpen_discrete _).preimage
        ((continuous_artinCoord H).comp (topologicalAbelianizationEquiv K Ω).continuous)
    · show artinCoord K Ω H (topologicalAbelianizationEquiv K Ω 1) = 1
      rw [map_one, map_one]
    · intro x hx
      have hx' : artinCoord K Ω H (topologicalAbelianizationEquiv K Ω (localReciprocityLimit K Ω x)) = 1 := hx
      rw [← localArtinMap_apply, artinCoord_localArtinMap, QuotientGroup.eq_one_iff] at hx'
      obtain ⟨z, hz⟩ := hx'
      exact ⟨z, hz.symm⟩
  have hall : ∀ n : ℕ, n ≠ 0 → ∃ z, a = z ^ n := fun n hn =>
    mn_core (localReciprocityLimit K Ω) denseRange_localReciprocityLimit hq hM hopen a ha n hn
  by_contra hne
  obtain ⟨V, hVo, haV⟩ := mn_sep a hne
  haveI : Finite (TopologicalAbelianization (Ω ≃ₐ[K] Ω) ⧸ V) := Subgroup.quotient_finite_of_isOpen V hVo
  haveI : V.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨z, hz⟩ := hall V.index Subgroup.FiniteIndex.index_ne_zero
  exact haV (hz ▸ Subgroup.pow_index_mem V z)

private theorem mn_map {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] (f : G →* H) (hf : Continuous f) {g : G}
    (hg : g ∈ (commutator G).topologicalClosure) : f g ∈ (commutator H).topologicalClosure := by
  have hc : commutator G ≤ (commutator H).comap f := by
    rw [← Subgroup.map_le_iff_le_comap, commutator_def, commutator_def, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  have hcl : (commutator G).topologicalClosure ≤ ((commutator H).topologicalClosure).comap f :=
    Subgroup.topologicalClosure_minimal _ (hc.trans (Subgroup.comap_mono (Subgroup.le_topologicalClosure _)))
      ((Subgroup.isClosed_topologicalClosure _).preimage hf)
  exact hcl hg

private theorem mn_cyc {l : ℕ} [Fact l.Prime] (σ : GQ l) {ζ : Om l} (h1 : ζ ^ l = 1) (h2 : ζ ≠ 1)
    (h : σ ζ = ζ) : PadicInt.toZMod ((cyc l l σ : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by
  have hp : l.Prime := Fact.out
  have hprim : IsPrimitiveRoot ζ l := by
    rw [IsPrimitiveRoot.iff_orderOf]
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one h1) with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) h2
    · exact h
  have hs := cyclotomicCharacter.spec (L := Om l) l (n := 1)
    (MulSemiringAction.toRingAut (GQ l) (Om l) σ) ζ (by rw [pow_one]; exact h1)
  have hcyc : (cyc l l σ : ℤ_[l]ˣ) =
      cyclotomicCharacter (Om l) l (MulSemiringAction.toRingAut (GQ l) (Om l) σ) := rfl
  rw [← hcyc] at hs
  set x : ℤ_[l] := ((cyc l l σ : ℤ_[l]ˣ) : ℤ_[l]) with hx
  have hσ : (MulSemiringAction.toRingAut (GQ l) (Om l) σ) ζ = ζ := h
  have hs' : ζ ^ (PadicInt.toZModPow 1 x).val = ζ ^ 1 := by
    calc _ = _ := hs.symm
      _ = ζ := hσ
      _ = ζ ^ 1 := (pow_one ζ).symm
  have hlt : (PadicInt.toZModPow 1 x).val < l :=
    lt_of_lt_of_eq (ZMod.val_lt (PadicInt.toZModPow (p := l) 1 x)) (pow_one l)
  have hk : (PadicInt.toZModPow 1 x).val = 1 := hprim.pow_inj hlt hp.one_lt hs'
  have hk' : PadicInt.toZModPow 1 x = 1 := by
    rw [← ZMod.natCast_zmod_val (PadicInt.toZModPow 1 x), hk, Nat.cast_one]
  have hmem : x - 1 ∈ RingHom.ker (PadicInt.toZModPow (p := l) 1) := by
    rw [RingHom.mem_ker, map_sub, hk', map_one, sub_self]
  rw [PadicInt.ker_toZModPow, pow_one, ← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod,
    RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at hmem
  exact hmem

theorem UpperTheory.V.Loc.muNone :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ), (∃ g : G, PadicInt.toZMod ((cyc l l (φ g) : ℤ_[l]ˣ) : ℤ_[l]) ≠ 1) → ∀ g : G, (QuotientGroup.mk' _ g : TopologicalAbelianization G) ∈ CommGroup.primaryComponent (TopologicalAbelianization G) l → g ∈ (commutator G).topologicalClosure := by
  intro l _ G _ _ _ φ hφ hex g hg
  obtain ⟨g0, hg0⟩ := hex
  have hp : l.Prime := Fact.out
  obtain ⟨K, e, he1, he2, hφe, -⟩ := openField φ hφ
  haveI : FiniteDimensional ℚ_[l] K.1 := K.2
  set L : IntermediateField ℚ_[l] (Om l) := K.1 with hL
  haveI : Algebra.IsAlgebraic L (Om l) := Algebra.IsAlgebraic.tower_top (K := ℚ_[l]) L
  haveI : IsAlgClosure L (Om l) := ⟨inferInstance, inferInstance⟩
  haveI : IsSepClosure L (Om l) := inferInstance
  obtain ⟨vr, ts, hloc, -⟩ := GroundTheory.LocalField.exists_isNonarchimedeanLocalField_valuativeExtension ℚ_[l] L
  let ψ : G →* Gal(Om l/L) := L.fixingSubgroupEquiv.toMonoidHom.comp e.toMonoidHom
  have hψ : Continuous ψ := (GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[l] (Om l) L).1.comp he1
  let ψi : Gal(Om l/L) →* G := e.symm.toMonoidHom.comp L.fixingSubgroupEquiv.symm.toMonoidHom
  have hψi : Continuous ψi := he2.comp (GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[l] (Om l) L).2
  have hψψ : ψi (ψ g) = g :=
    (congrArg e.symm (L.fixingSubgroupEquiv.symm_apply_apply (e g))).trans (e.symm_apply_apply g)
  obtain ⟨n, hn⟩ := hg
  have hgn : g ^ (l ^ n) ∈ (commutator G).topologicalClosure := by
    rw [← map_pow, QuotientGroup.mk'_apply] at hn
    exact (QuotientGroup.eq_one_iff _).1 hn
  have hM : ∀ x : Lˣ, x ^ (l ^ n) = 1 → x = 1 := by
    intro x hx
    by_contra hx1
    obtain ⟨m, hmn, hm⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hx)
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hx1 (orderOf_eq_one_iff.1 (by rw [hm, pow_zero]))
    set y := x ^ (l ^ (m - 1)) with hy
    have hy1 : y ^ l = 1 := by
      rw [hy, ← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0), ← hm, pow_orderOf_eq_one]
    have hy2 : y ≠ 1 := by
      intro h
      have h3 := orderOf_dvd_of_pow_eq_one h
      rw [hm, Nat.pow_dvd_pow_iff_le_right hp.one_lt] at h3
      omega
    have hz1 : (((y : L) : Om l)) ^ l = 1 := by
      have h4 := congrArg (fun u : Lˣ => ((u : L) : Om l)) hy1
      simpa using h4
    have hz2 : (((y : L) : Om l)) ≠ 1 := by
      intro h
      apply hy2
      apply Units.ext
      apply Subtype.ext
      simpa using h
    have hσ : φ g0 ∈ GK K := by
      rw [← hφe]
      exact (e g0).2
    have hfix : (φ g0) ((y : L) : Om l) = ((y : L) : Om l) :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ _ (y : L).2
    exact hg0 (mn_cyc (φ g0) hz1 hz2 hfix)
  have hψn : ψ g ^ (l ^ n) ∈ (commutator Gal(Om l/L)).topologicalClosure := by
    rw [← map_pow]
    exact mn_map ψ hψ hgn
  have ha : QuotientGroup.mk' (commutator Gal(Om l/L)).topologicalClosure (ψ g) = 1 := by
    refine mn_field L (Om l) (pow_ne_zero n hp.ne_zero) hM _ ?_
    rw [← map_pow, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff _).2 hψn
  rw [← hψψ]
  exact mn_map ψi hψi ((QuotientGroup.eq_one_iff _).1 ha)
