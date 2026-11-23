import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllFree
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.IntegralFrameAcquisition
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.IntegralFrameAllCompare

open NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.IntegralFrameAcquisition

section Valuations

variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K]

theorem vV_nonneg_iff_le_one (x : K) (hx : x ≠ 0) : 0 ≤ vV V x ↔ valV V x ≤ 1 := by
  rw [← WithZero.log_le_log (valV_ne_zero (V := V) hx) one_ne_zero, WithZero.log_one, vV]
  omega

theorem mem_range_iff (x : K) : x ∈ Set.range (algebraMap V K) ↔ 0 ≤ vV V x := by
  by_cases hx : x = 0
  · subst hx
    exact ⟨fun _ => by simp [vV], fun _ => ⟨0, map_zero _⟩⟩
  rw [vV_nonneg_iff_le_one x hx]
  constructor
  · rintro ⟨v, rfl⟩
    exact HeightOneSpectrum.valuation_le_one _ v
  · exact fun h => IsDiscreteValuationRing.exists_lift_of_le_one (A := V) (K := K) h

theorem vV_pos {v : V} (h0 : v ≠ 0) (h : v ∈ maximalIdeal V) : 0 < vV V (algebraMap V K v) := by
  have h1 : algebraMap V K v ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective V K)).2 h0
  have h2 : valV V (algebraMap V K v) < 1 := (HeightOneSpectrum.valuation_lt_one_iff_mem _ v).2 h
  have := (WithZero.log_lt_log (valV_ne_zero (V := V) h1) one_ne_zero).2 h2
  simp only [WithZero.log_one] at this
  simp only [vV]; omega

theorem vV_zpow (x : K) (n : ℤ) : vV V (x ^ n) = n * vV V x := by
  simp only [vV, map_zpow₀, WithZero.log_zpow, smul_eq_mul]
  ring

theorem vV_of_isUnit {v : V} (h : IsUnit v) : vV V (algebraMap V K v) = 0 := by
  obtain ⟨u, rfl⟩ := h
  have h1 := (mem_range_iff (V := V) (algebraMap V K (u : V))).1 ⟨_, rfl⟩
  have h2 := (mem_range_iff (V := V) (algebraMap V K ((u⁻¹ : Vˣ) : V))).1 ⟨_, rfl⟩
  rw [map_units_inv, ← zpow_neg_one, vV_zpow] at h2
  omega

variable {W L : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L]
  [IsFractionRing W L]

theorem exists_scale (i : K →+* L) (hi : ∀ a : V, i (algebraMap V K a) ∈ Set.range (algebraMap W L)) :
    ∃ r : ℕ, ∀ x : K, vV W (i x) = (r : ℤ) * vV V x := by
  have hnn : ∀ x : K, 0 ≤ vV V x → 0 ≤ vV W (i x) := fun x hx => by
    obtain ⟨a, rfl⟩ := (mem_range_iff x).2 hx
    exact (mem_range_iff _).1 (hi a)
  have hz : ∀ x : K, vV V x = 0 → vV W (i x) = 0 := fun x hx => by
    have h1 := hnn x hx.ge
    have h2 := hnn (x ^ (-1 : ℤ)) (by rw [vV_zpow, hx]; simp)
    rw [map_zpow₀, vV_zpow] at h2
    omega
  obtain ⟨π, hπ⟩ := (IsDiscreteValuationRing.maximalIdeal V).valuation_exists_uniformizer K
  have hπ1 : vV V π = 1 := by simp [vV, valV, hπ]
  have hπ0 : π ≠ 0 := fun h => by simp [h, vV] at hπ1
  have hr := hnn π (by omega)
  refine ⟨(vV W (i π)).toNat, fun x => ?_⟩
  rw [Int.toNat_of_nonneg hr]
  by_cases hx : x = 0
  · simp [hx, vV]
  have h := hz (x * π ^ (-vV V x)) (by rw [vV_mul hx (zpow_ne_zero _ hπ0), vV_zpow, hπ1]; ring)
  rw [map_mul, map_zpow₀, vV_mul ((map_ne_zero i).2 hx) (zpow_ne_zero _ ((map_ne_zero i).2 hπ0)), vV_zpow] at h
  linarith

theorem index_eq {R F : Type} [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F] [IsFractionRing R F]
    {la : HeightOneSpectrum R} {io : F →+* K} {i : K →+* L} {e e' r : ℕ} (ho : OverLa la V io e)
    (ho' : OverLa la W (i.comp io) e') (hi : ∀ x : K, vV W (i x) = (r : ℤ) * vV V x) : e' = r * e := by
  obtain ⟨π, hπ⟩ := la.valuation_exists_uniformizer F
  have hπ1 : vLa la π = 1 := by simp [vLa, hπ]
  have h := ho'.2 π
  rw [RingHom.comp_apply, hi, ho.2, hπ1, mul_one, mul_one] at h
  exact_mod_cast h.symm

theorem finite_of_scale [IsAdicComplete (maximalIdeal V) V] (i : K →+* L) {r : ℕ} (hr : 0 < r)
    (hi : ∀ z, vV W (i z) = (r : ℤ) * vV V z) (h' : Finite (ResidueField W)) : i.Finite := by
  have hint : ∀ a : V, ∃ v : W, algebraMap W L v = i (algebraMap V K a) := fun a =>
    (mem_range_iff _).2 (by rw [hi]; exact mul_nonneg (by positivity) ((mem_range_iff _).1 ⟨a, rfl⟩))
  choose g0 hg0 using hint
  have hinj := IsFractionRing.injective W L
  let g : V →+* W :=
    { toFun := g0
      map_one' := hinj (by simp [hg0])
      map_mul' := fun a b => hinj (by simp [hg0])
      map_zero' := hinj (by simp [hg0])
      map_add' := fun a b => hinj (by simp [hg0]) }
  have hg : ∀ a, algebraMap W L (g a) = i (algebraMap V K a) := hg0
  letI : Algebra V W := g.toAlgebra
  letI : Algebra K L := i.toAlgebra
  letI : Algebra V L := ((algebraMap W L).comp g).toAlgebra
  have : IsScalarTower V W L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower V K L := IsScalarTower.of_algebraMap_eq fun a => hg a
  have hgi : Function.Injective (algebraMap V W) := fun a b hab => by
    apply IsFractionRing.injective V K
    apply i.injective
    rw [← hg, ← hg]
    exact congrArg _ hab
  have : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective _ _).2 hgi
  have hle : (maximalIdeal V).map (algebraMap V W) ≤ maximalIdeal W := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    by_cases h0 : a = 0
    · simp [h0]
    rw [Ideal.mem_comap, mem_maximalIdeal]
    intro hu
    have h1 : vV W (algebraMap W L (g a)) = 0 := vV_of_isUnit hu
    have h3 : (0 : ℤ) < r * vV V (algebraMap V K a) := mul_pos (by exact_mod_cast hr) (vV_pos h0 ha)
    rw [← hi, ← hg, h1] at h3
    exact lt_irrefl _ h3
  have hne : (maximalIdeal V).map (algebraMap V W) ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective hgi]
    exact IsDiscreteValuationRing.not_a_field V
  have htop : (maximalIdeal V).map (algebraMap V W) ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal W).ne_top hle
  have : IsHausdorff ((maximalIdeal V).map (algebraMap V W)) W := IsHausdorff.of_isDomain _ htop
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hϖ
  have : Finite (W ⧸ (maximalIdeal V).map (algebraMap V W)) := by
    rw [hn, ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq]
    have : Finite (W ⧸ maximalIdeal W) := h'
    exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) n
  have : Module.Finite V (W ⧸ (maximalIdeal V).map (algebraMap V W)) := Module.Finite.of_finite
  have : Module.Finite V W := GlobalTheory.FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal V)
  exact Module.Finite.of_isLocalization V W (nonZeroDivisors V)

end Valuations

theorem extension_iff {F : Type} [Field F] [NumberField F] {la : HeightOneSpectrum (𝓞 F)} {T T' : CDVR}
    {io : F →+* T.Fr} {e : ℕ} (ho : OverLa la T.V io e) (hT' : T'.FinRes) (j : T.Fr →+* T'.Fr) (e' : ℕ) :
    (OverLa la T'.V (j.comp io) e' ∧
        ∀ a : T.V, j (algebraMap T.V T.Fr a) ∈ Set.range (algebraMap T'.V T'.Fr)) ↔
      ∃ r : ℕ, e' = r * e ∧ IsFiniteValuedExt T T' j r ∧ OverLa la T'.V (j.comp io) (r * e) := by
  constructor
  · rintro ⟨ho', hj⟩
    obtain ⟨r, hr⟩ := exists_scale j hj
    obtain rfl := index_eq ho ho' hr
    have h0 : 0 < r := Nat.pos_of_mul_pos_right ho'.1
    exact ⟨r, rfl, ⟨finite_of_scale j h0 hr hT', h0, hr⟩, ho'⟩
  · rintro ⟨r, rfl, ⟨-, -, hr⟩, ho'⟩
    refine ⟨ho', fun a => (mem_range_iff _).2 ?_⟩
    rw [hr]
    exact mul_nonneg (by positivity) ((mem_range_iff _).1 ⟨a, rfl⟩)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)

theorem conclusion_iff (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ)
    (ho : OverLa la T.V io e) (y : (letI := io.toAlgebra; FrPt Xo c T.Fr)) :
    (∃ (T' : CDVR) (io' : c.F →+* T'.Fr) (e' : ℕ) (y' : IntFr Xo c T' io'), OverLa la T'.V io' e' ∧ y'.IsAlg ∧
        letI := io.toAlgebra; letI := io'.toAlgebra
        ∃ (φ : T.Fr →ₐ[c.F] T'.Fr) (z : FrPt Xo c T'.Fr) (t : Ix Dw → T'.Frˣ),
          (∀ a : T.V, φ (algebraMap T.V T.Fr a) ∈ Set.range (algebraMap T'.V T'.Fr)) ∧
            FrMap φ y z ∧ FrBor t z y'.1) ↔
      AcquiresIntegralFrame la e y := by
  letI := io.toAlgebra
  constructor
  · rintro ⟨T', io', e', y', ho', ha, φ, z, t, hφ, hz, hb⟩
    letI := io'.toAlgebra
    obtain ⟨j, hj⟩ := φ
    obtain rfl : io' = j.comp io := RingHom.ext fun a => (hj a).symm
    obtain ⟨r, -, hf, ho''⟩ := (extension_iff ho ha j e').1 ⟨ho', hφ⟩
    exact ⟨T', j, r, y', hf, ho'', ha, z, t, hz, hb⟩
  · rintro ⟨T', j, r, y', hf, ho', ha, z, t, hz, hb⟩
    exact ⟨T', j.comp io, r * e, y', ho', ha, algHomOver io j, z, t,
      ((extension_iff ho ha j (r * e)).2 ⟨r, rfl, hf, ho'⟩).2, hz, hb⟩

theorem intAll_iff : Formalism.L2.PjFree.IntAll Xo c ↔ AllAcquireIntegralFrame Xo c :=
  forall_congr' fun la => forall_congr' fun T => forall_congr' fun io => forall_congr' fun e =>
    forall_congr' fun ho => forall_congr' fun _ => forall_congr' fun y => conclusion_iff Xo c la T io e ho y

end GlobalTheory.IntegralFrameAllCompare
