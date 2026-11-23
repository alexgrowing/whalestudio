import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS)
open Formalism.L2.Pj

namespace GlobalTheory.LocalDepthCompare

section Places

variable {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
  [IsFractionRing V K']

theorem valV_le_one (v : V) : valV V (algebraMap V K' v) ≤ 1 :=
  HeightOneSpectrum.valuation_le_one _ v

theorem valV_lt_one_iff (v : V) : valV V (algebraMap V K' v) < 1 ↔ v ∈ maximalIdeal V :=
  HeightOneSpectrum.valuation_lt_one_iff_mem _ v

theorem valV_eq_one {v : V} (h : v ∉ maximalIdeal V) : valV V (algebraMap V K' v) = 1 :=
  le_antisymm (valV_le_one v) (not_lt.1 fun h' => h ((valV_lt_one_iff v).1 h'))

theorem vV_pos {v : V} (h0 : v ≠ 0) (h : v ∈ maximalIdeal V) : 0 < vV V (algebraMap V K' v) := by
  have h1 : algebraMap V K' v ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective V K')).2 h0
  have := (WithZero.log_lt_log (valV_ne_zero (V := V) h1) one_ne_zero).2 ((valV_lt_one_iff v).2 h)
  simp only [WithZero.log_one] at this
  simp only [vV]; omega

theorem not_charZero_iff : ¬ CharZero (ResidueField V) ↔ ∃ n : ℕ, n ≠ 0 ∧ (n : V) ∈ maximalIdeal V := by
  constructor
  · intro h
    by_contra hn
    refine h (charZero_of_inj_zero fun n h0 => ?_)
    by_contra hn0
    exact hn ⟨n, hn0, by rw [← residue_eq_zero_iff, map_natCast, h0]⟩
  · rintro ⟨n, hn, hm⟩ _
    rw [← residue_eq_zero_iff, map_natCast] at hm
    exact hn (by exact_mod_cast hm)

variable {K : Type} [Field K] [NumberField K]

theorem not_charZero_of_overLa {la : HeightOneSpectrum (𝓞 K)} {io : K →+* K'} {e : ℕ}
    (ho : OverLa la V io e) : ¬ CharZero (ResidueField V) := by
  rw [not_charZero_iff]
  have hn : Ideal.absNorm la.asIdeal ≠ 0 := fun h => la.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  refine ⟨_, hn, ?_⟩
  have hmem := Ideal.absNorm_mem la.asIdeal
  generalize Ideal.absNorm la.asIdeal = n at hn hmem
  by_contra hV
  have hK : ((n : ℕ) : K) ≠ 0 := by exact_mod_cast hn
  have h1 : valV V ((n : ℕ) : K') = 1 := by
    rw [← map_natCast (algebraMap V K') n]
    exact valV_eq_one hV
  have h2 : la.valuation K ((n : ℕ) : K) < 1 := by
    rw [← map_natCast (algebraMap (𝓞 K) K) n, HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact hmem
  have h3 : WithZero.log (la.valuation K ((n : ℕ) : K)) < 0 := by
    have := (WithZero.log_lt_log ((la.valuation K).ne_zero_iff.2 hK) one_ne_zero).2 h2
    simpa using this
  have h4 := ho.2 ((n : ℕ) : K)
  rw [map_natCast, vV, h1, vLa, WithZero.log_one] at h4
  have he : (0 : ℤ) < e := by exact_mod_cast ho.1
  nlinarith [mul_pos he (neg_pos.2 h3)]

theorem exists_overLa_of_not_charZero (io : K →+* K') (hT : ¬ CharZero (ResidueField V)) :
    ∃ (la : HeightOneSpectrum (𝓞 K)) (e : ℕ), OverLa la V io e := by
  have hint : ∀ a : 𝓞 K, ∃ v : V, algebraMap V K' v = io a := fun a =>
    IsIntegrallyClosed.algebraMap_eq_of_integral (R := V) (K := K')
      (IsIntegral.map_of_comp_eq (Int.castRingHom V) io (RingHom.ext_int _ _) a.isIntegral_coe)
  choose g0 hg0 using hint
  have hinj := IsFractionRing.injective V K'
  let g : 𝓞 K →+* V :=
    { toFun := g0
      map_one' := hinj (by simp [hg0])
      map_mul' := fun a b => hinj (by simp [hg0])
      map_zero' := hinj (by simp [hg0])
      map_add' := fun a b => hinj (by simp [hg0]) }
  have hg : ∀ a, algebraMap V K' (g a) = io (algebraMap (𝓞 K) K a) := hg0
  have hne : (maximalIdeal V).comap g ≠ ⊥ := by
    obtain ⟨n, hn, hm⟩ := not_charZero_iff.1 hT
    intro h
    have h1 : ((n : ℕ) : 𝓞 K) ∈ (maximalIdeal V).comap g := by
      rw [Ideal.mem_comap, map_natCast]; exact hm
    rw [h, Ideal.mem_bot] at h1
    exact hn (by exact_mod_cast h1)
  let la : HeightOneSpectrum (𝓞 K) := ⟨(maximalIdeal V).comap g, Ideal.comap_isPrime _ _, hne⟩
  have hun : ∀ a : 𝓞 K, a ∉ la.asIdeal → valV V (io (algebraMap (𝓞 K) K a)) = 1 := fun a ha => by
    rw [← hg]
    exact valV_eq_one ha
  have hone : ∀ x : K, la.valuation K x = 1 → valV V (io x) = 1 := fun x hx => by
    obtain ⟨n, d, h⟩ := la.exists_primeCompl_mul_eq_of_integer x hx.le
    have hd : la.valuation K (algebraMap (𝓞 K) K d) = 1 := (la.valuation_eq_one_iff_notMem).2 d.2
    have hn : la.valuation K (algebraMap (𝓞 K) K n) = 1 := by rw [← h, map_mul, hx, hd, one_mul]
    have h2 := hun n ((la.valuation_eq_one_iff_notMem).1 hn)
    rwa [← h, map_mul, map_mul, hun d d.2, mul_one] at h2
  obtain ⟨π, hπ⟩ := la.intValuation_exists_uniformizer
  have hπK : la.valuation K (algebraMap (𝓞 K) K π) = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap, hπ]
  have hπ0 : algebraMap (𝓞 K) K π ≠ 0 := fun h => by
    simp [h] at hπK; exact WithZero.exp_ne_zero hπK.symm
  have hπm : π ∈ la.asIdeal := by
    rw [← la.valuation_lt_one_iff_mem (K := K), hπK, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have hpos : 0 < vV V (io (algebraMap (𝓞 K) K π)) := by
    rw [← hg]
    refine vV_pos (fun h => ?_) hπm
    have := hg π
    rw [h, map_zero] at this
    exact (map_ne_zero io).2 hπ0 this.symm
  refine ⟨la, (vV V (io (algebraMap (𝓞 K) K π))).toNat, by omega, fun a => ?_⟩
  rw [Int.toNat_of_nonneg hpos.le]
  by_cases ha : a = 0
  · simp [ha, vV, vLa]
  have hva : la.valuation K a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  have h1 := hone (a * (algebraMap (𝓞 K) K π) ^ (-vLa la a)) (by
    rw [map_mul, map_zpow₀, hπK, ← WithZero.exp_zsmul, ← WithZero.exp_log hva, ← WithZero.exp_add]
    simp [vLa])
  have h2 := congrArg WithZero.log h1
  rw [map_mul, map_mul, map_zpow₀, map_zpow₀, WithZero.log_mul (valV_ne_zero ((map_ne_zero io).2 ha))
    (zpow_ne_zero _ (valV_ne_zero ((map_ne_zero io).2 hπ0))), WithZero.log_zpow,
    WithZero.log_one] at h2
  simp only [vV, smul_eq_mul] at h2 ⊢
  linarith

end Places

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]

section Local

variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

variable {la : HeightOneSpectrum (𝓞 c.F)} {e : ℕ}

end Local

variable (Xo c)

def IndepOn (p : CDVR → Prop) (k : ℕ) : Prop :=
  ∀ (T : CDVR), p T → ∀ (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C C' : IntChart T io y) (e : ℕ)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), nuLocC C e k a n = nuLocC C' e k a n

end GlobalTheory.LocalDepthCompare
