import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.UnimodQuot

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem exists_rep (H : HermSpace K V) (f : V →ₗ[K] K) : ∃ y, ∀ x, H.B x y = f x := by
  have h1 : (LinearMap.range H.B.flip).dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_dualCoannihilator] at hx
    exact H.nondeg x fun y => hx _ ⟨y, rfl⟩
  have h2 := Subspace.dualCoannihilator_dualAnnihilator_eq (W := LinearMap.range H.B.flip)
  rw [h1, Submodule.dualAnnihilator_bot] at h2
  have h3 : f ∈ LinearMap.range H.B.flip := h2 ▸ Submodule.mem_top
  obtain ⟨y, hy⟩ := h3
  exact ⟨y, fun x => by rw [← hy]; rfl⟩

theorem mem_of_perp_perp (H : HermSpace K V) (I : Submodule K V) {v : V}
    (hv : ∀ x ∈ perp H I, H.B x v = 0) : v ∈ I := by
  by_contra h
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_dual_map_eq_bot_of_notMem h inferInstance
  obtain ⟨w, hw⟩ := exists_rep H f
  have hwI : w ∈ perp H I := by
    rw [mem_perp_iff]
    intro x hx
    have : f x = 0 := by
      have : f x ∈ I.map f := Submodule.mem_map_of_mem hx
      rwa [hf0, Submodule.mem_bot] at this
    rw [← H.herm, hw, this, star_zero]
  apply hf
  rw [← hw, ← H.herm, hv w hwI, star_zero]

omit [StarRing K] [FiniteDimensional K V] in
theorem mem_one_iff (x : K) : x ∈ (1 : Submodule (𝓞 K) K) ↔ IsIntegral ℤ x := by
  rw [Submodule.mem_one]
  constructor
  · rintro ⟨y, rfl⟩
    exact y.isIntegral_coe
  · intro h
    exact ⟨⟨x, h⟩, rfl⟩

theorem star_mem_one {x : K} (h : x ∈ (1 : Submodule (𝓞 K) K)) : star x ∈ (1 : Submodule (𝓞 K) K) := by
  rw [mem_one_iff] at h ⊢
  exact map_isIntegral_int (starRingEnd K) h

variable [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [StarRing K] [FiniteDimensional K V] in
theorem exists_smul_mem {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) (y : V) :
    ∃ s : nonZeroDivisors (𝓞 K), s • y ∈ L := by
  have hy : y ∈ Submodule.span K (L : Set V) := by rw [hL.span_eq_top]; trivial
  obtain ⟨s, hs⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K (L : Set V) y hy
  rw [Submodule.span_eq] at hs
  exact ⟨s, hs⟩

omit [StarRing K] [FiniteDimensional K V] in
theorem isLocalizedModule_subtype {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) :
    IsLocalizedModule (nonZeroDivisors (𝓞 K)) L.subtype where
  map_units s := by
    have := isLocalizedModule_id (nonZeroDivisors (𝓞 K)) V K
    exact IsLocalizedModule.map_units (S := nonZeroDivisors (𝓞 K)) (LinearMap.id : V →ₗ[𝓞 K] V) s
  surj y := by
    obtain ⟨s, hs⟩ := exists_smul_mem hL y
    exact ⟨(⟨_, hs⟩, s), rfl⟩
  exists_of_eq h := ⟨1, by rw [Subtype.ext h]⟩

omit [StarRing K] [FiniteDimensional K V] in

theorem exists_extension {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) (S : Submodule K V)
    (φ : ↥(L ⊓ rs (𝓞 K) S) →ₗ[𝓞 K] 𝓞 K) :
    ∃ ψ : L →ₗ[𝓞 K] 𝓞 K, ∀ x : ↥(L ⊓ rs (𝓞 K) S), ψ ⟨x, x.2.1⟩ = φ x := by
  let N : Submodule (𝓞 K) L := (rs (𝓞 K) S).comap L.subtype
  have hflat : Module.Flat (𝓞 K) (L ⧸ N) := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    rintro q ⟨a, ha⟩
    obtain ⟨x, rfl⟩ := N.mkQ_surjective q
    have h1 : N.mkQ ((a : 𝓞 K) • x) = 0 := by rw [map_smul]; exact ha
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    have h2 : (algebraMap (𝓞 K) K a) • (x : V) ∈ S := by
      rw [algebraMap_smul]; exact h1
    have h3 : algebraMap (𝓞 K) K a ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors a.2
    exact (S.smul_mem_iff h3).1 h2
  have : Module.FinitePresentation (𝓞 K) (L ⧸ N) := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 K) (L ⧸ N) := Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective
  let ρ : L →ₗ[𝓞 K] V := L.subtype ∘ₗ (LinearMap.id - s ∘ₗ N.mkQ)
  have hρ : ∀ x, ρ x ∈ L ⊓ rs (𝓞 K) S := by
    intro x
    refine ⟨(x - s (N.mkQ x)).2, ?_⟩
    have : x - s (N.mkQ x) ∈ N := by
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub]
      have := LinearMap.congr_fun hs (N.mkQ x)
      rw [LinearMap.comp_apply] at this
      rw [this, LinearMap.id_apply, sub_self]
    exact this
  refine ⟨φ ∘ₗ ρ.codRestrict _ hρ, fun x => ?_⟩
  rw [LinearMap.comp_apply]
  congr 1
  apply Subtype.ext
  have h0 : N.mkQ ⟨x, x.2.1⟩ = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact x.2.2
  show ((⟨x, x.2.1⟩ - s (N.mkQ ⟨x, x.2.1⟩) : L) : V) = x
  rw [h0, map_zero, sub_zero]

theorem exists_lattice_rep (H : HermSpace K V) {L : Submodule (𝓞 K) V} (hU : IsUnimod H L) (S : Submodule K V)
    (φ : ↥(L ⊓ rs (𝓞 K) S) →ₗ[𝓞 K] 𝓞 K) :
    ∃ y ∈ L, ∀ x : ↥(L ⊓ rs (𝓞 K) S), H.B x y = (φ x : K) := by
  have hL := (isLatMod_top_bot_iff L).1 hU.1
  obtain ⟨ψ, hψ⟩ := exists_extension hL S φ
  have := isLocalizedModule_subtype hL
  have hu : ∀ x : nonZeroDivisors (𝓞 K), IsUnit (algebraMap (𝓞 K) (Module.End (𝓞 K) K) x) :=
    fun x => IsLocalizedModule.map_units (S := nonZeroDivisors (𝓞 K)) (Algebra.linearMap (𝓞 K) K) x
  let f : V →ₗ[K] K := LinearMap.extendScalarsOfIsLocalization (nonZeroDivisors (𝓞 K)) K
      (IsLocalizedModule.lift (nonZeroDivisors (𝓞 K)) L.subtype (Algebra.linearMap (𝓞 K) K ∘ₗ ψ) hu)
  have hf : ∀ y : L, f y = algebraMap (𝓞 K) K (ψ y) := fun y =>
    IsLocalizedModule.lift_apply (nonZeroDivisors (𝓞 K)) L.subtype _ hu y
  obtain ⟨y, hy⟩ := exists_rep H f
  refine ⟨y, ?_, fun x => ?_⟩
  · rw [← hU.2, mem_dual_iff]
    refine ⟨by rw [hL.span_eq_top]; trivial, fun x hx => ?_⟩
    rw [← H.herm, hy]
    apply star_mem_one
    rw [hf ⟨x, hx⟩]
    exact Submodule.mem_one.2 ⟨_, rfl⟩
  · rw [hy, ← hψ]
    exact hf ⟨x, x.2.1⟩

theorem isUnimodMod_quot (H : HermSpace K V) {L : Submodule (𝓞 K) V} (hU : IsUnimod H L) {I : Submodule K V}
    (hI : ∀ x ∈ I, ∀ y ∈ I, H.B x y = 0) :
    IsUnimodMod H ((L ⊓ rs (𝓞 K) (perp H I)) ⊔ rs (𝓞 K) I) (perp H I) I := by
  have hL := (isLatMod_top_bot_iff L).1 hU.1
  have hint : ∀ y ∈ L, ∀ x ∈ L, H.B y x ∈ (1 : Submodule (𝓞 K) K) := by
    intro y hy
    rw [← hU.2, mem_dual_iff] at hy
    exact hy.2
  have hIp : I ≤ perp H I := fun x hx => (mem_perp_iff H I x).2 (hI x hx)
  have hsat : ∀ v ∈ perp H I, ∃ c : K, c ≠ 0 ∧ c • v ∈ L ⊓ rs (𝓞 K) (perp H I) := by
    intro v hv
    obtain ⟨s, hs⟩ := exists_smul_mem hL v
    refine ⟨algebraMap (𝓞 K) K s, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2, ?_,
      (perp H I).smul_mem _ hv⟩
    rw [algebraMap_smul]
    exact hs
  have hspan : Submodule.span K (((L ⊓ rs (𝓞 K) (perp H I)) ⊔ rs (𝓞 K) I : Submodule (𝓞 K) V) : Set V)
      = perp H I := by
    apply le_antisymm
    · rw [Submodule.span_le]
      have : (L ⊓ rs (𝓞 K) (perp H I)) ⊔ rs (𝓞 K) I ≤ rs (𝓞 K) (perp H I) := sup_le inf_le_right hIp
      exact this
    · intro v hv
      obtain ⟨c, hc, h⟩ := hsat v hv
      rw [← Submodule.smul_mem_iff _ hc]
      exact Submodule.subset_span (Submodule.mem_sup_left h)
  refine ⟨⟨⟨_, ?_, rfl⟩, hspan⟩, ?_⟩
  · have : IsNoetherian (𝓞 K) L := inferInstance
    have : IsNoetherian (𝓞 K) ↥(L ⊓ rs (𝓞 K) (perp H I)) := isNoetherian_of_le inf_le_left
    rw [← Module.Finite.iff_fg]
    infer_instance
  ext y
  rw [mem_dual_iff, hspan]
  constructor
  · rintro ⟨hy, hyM⟩
    have hx : ∀ x : ↥(L ⊓ rs (𝓞 K) (perp H I)), IsIntegral ℤ (H.B x y) := by
      intro x
      rw [← mem_one_iff, ← H.herm]
      exact star_mem_one (hyM x (Submodule.mem_sup_left x.2))
    let φ : ↥(L ⊓ rs (𝓞 K) (perp H I)) →ₗ[𝓞 K] 𝓞 K :=
      { toFun := fun x => ⟨H.B x y, hx x⟩
        map_add' := fun a b => by
          apply RingOfIntegers.ext
          show H.B ((a : V) + b) y = H.B a y + H.B b y
          simp
        map_smul' := fun a b => by
          apply RingOfIntegers.ext
          show H.B (a • (b : V)) y = algebraMap (𝓞 K) K a * H.B b y
          rw [← algebraMap_smul K a, map_smul]
          rfl }
    obtain ⟨y', hy', h'⟩ := exists_lattice_rep H hU (perp H I) φ
    have hd : y - y' ∈ I := by
      apply mem_of_perp_perp H I
      intro v hv
      obtain ⟨c, hc, h⟩ := hsat v hv
      have h1 : H.B (c • v) y' = H.B (c • v) y := h' ⟨_, h⟩
      rw [map_smul, LinearMap.smul_apply, LinearMap.smul_apply] at h1
      rw [map_sub, smul_right_injective K hc h1, sub_self]
    have hy'p : y' ∈ perp H I := by
      have := (perp H I).sub_mem hy (hIp hd)
      simpa using this
    exact Submodule.mem_sup.2 ⟨y', ⟨hy', hy'p⟩, y - y', hd, by abel⟩
  · intro hy
    obtain ⟨a, ⟨haL, hap⟩, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
    refine ⟨(perp H I).add_mem hap (hIp hb), fun x hx => ?_⟩
    obtain ⟨c, ⟨hcL, hcp⟩, d, hd, rfl⟩ := Submodule.mem_sup.1 hx
    have h1 : H.B a d = 0 := (mem_perp_iff H I a).1 hap d hd
    have h2 : H.B b c = 0 := by rw [← H.herm, (mem_perp_iff H I c).1 hcp b hb, star_zero]
    have h3 : H.B b d = 0 := hI b hb d hd
    simp only [map_add, LinearMap.add_apply, h1, h2, h3, add_zero]
    exact hint a haL c hcL

end GlobalTheory.UnimodQuot
