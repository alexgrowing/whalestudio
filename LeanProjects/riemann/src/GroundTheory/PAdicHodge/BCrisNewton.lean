import Mathlib
import GroundTheory.PAdicHodge.BCrisNewtonFrac
import GroundTheory.PAdicHodge.BCrisRegular
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

section Abstract

theorem exists_eq_div_of_mem_closure_range {R F : Type*} [CommRing R] [Field F] (f : R →+* F)
    {x : F} (hx : x ∈ Subfield.closure (Set.range f)) : ∃ u v : R, x = f u / f v := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Subfield.mem_closure_iff.1 hx
  have hle : Subring.closure (Set.range f) ≤ f.range :=
    Subring.closure_le.2 (by rintro _ ⟨w, rfl⟩; exact ⟨w, rfl⟩)
  obtain ⟨u, rfl⟩ := hle hy
  obtain ⟨v, rfl⟩ := hle hz
  exact ⟨u, v, rfl⟩

theorem exists_mul_eq_of_away_away {A B F : Type*} [CommRing A] [CommRing B] [CommRing F] {r : A}
    {t : Localization.Away r} (ι : A →+* B) (ιP : Localization.Away r →+* B)
    (hP : ∀ a, ιP (algebraMap A _ a) = ι a) (φ : B →+* F) (ιB : Localization.Away t →+* F)
    (hB : ∀ x, ιB (algebraMap _ _ x) = φ (ιP x)) (u : Localization.Away t) :
    ∃ (w : A) (n m : ℕ), ιB u * φ (ιP t ^ n * ι r ^ m) = φ (ι w) := by
  obtain ⟨x, n, hx⟩ := ACris.exists_mul_pow_eq_of_away (φ.comp ιP) ιB hB u
  obtain ⟨w, m, hw⟩ := ACris.exists_mul_pow_eq_of_away ι ιP hP x
  refine ⟨w, n, m, ?_⟩
  rw [RingHom.comp_apply, RingHom.comp_apply] at hx
  rw [map_mul, map_pow, ← mul_assoc, hx, ← map_mul, hw]

theorem mul_eq_mul_of_eqs {F : Type*} [CommRing F] {Y U V Wu Wv Su Sv : F} (h1 : Y * V = U)
    (hu : U * Su = Wu) (hv : V * Sv = Wv) : Wu * Sv = Y * (Wv * Su) := by
  rw [← hu, ← hv, ← h1]
  ring

end Abstract

namespace ACris

open _root_.WittVector Polynomial

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "𝔹dR" => BDeRham (normInteger ℂ_[p]) p

variable {ε : PreTilt (normInteger ℂ_[p]) p} (hε : PreTilt.untilt ε = 1)
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[p]) p) p).symm ε) ≠ 1)

def fracBCris : Subfield 𝔹dR := Subfield.closure (Set.range (iotaB hε hζ))

theorem iotaB_mem_fracBCris (x : BCris hε) : iotaB hε hζ x ∈ fracBCris hε hζ :=
  Subfield.subset_closure ⟨x, rfl⟩

theorem natCast_p_ne_zero_bdR : (p : 𝔹) ≠ 0 := by
  rw [← map_natCast (algebraMap ℚ_[p] 𝔹) p]
  exact fun h => (Nat.cast_ne_zero.2 hp.out.ne_zero : (p : ℚ_[p]) ≠ 0)
    ((algebraMap ℚ_[p] 𝔹).injective (by rw [h, map_zero]))

set_option maxHeartbeats 1600000 in

theorem exists_iotaB_mul_eq (u : BCris hε) : ∃ w s : ACris ℂ_[p] p, s ≠ 0 ∧
    iotaB hε hζ u * algebraMap 𝔹 𝔹dR (iota ℂ_[p] p s) = algebraMap 𝔹 𝔹dR (iota ℂ_[p] p w) := by
  obtain ⟨w, n, m, h⟩ := exists_mul_eq_of_away_away (iota ℂ_[p] p) (iotaPlus ℂ_[p] p)
    (fun a => iotaPlus_algebraMap a) (algebraMap 𝔹 𝔹dR) (iotaB hε hζ) (fun x => iotaB_algebraMap hε hζ x) u
  have e : iotaPlus ℂ_[p] p (algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) (periodT hε)) ^ n *
      iota ℂ_[p] p (p : ACris ℂ_[p] p) ^ m = iota ℂ_[p] p (periodT hε ^ n * (p : ACris ℂ_[p] p) ^ m) := by
    rw [iotaPlus_algebraMap, map_mul, map_pow, map_pow]
  rw [e] at h
  refine ⟨w, periodT hε ^ n * (p : ACris ℂ_[p] p) ^ m, fun h0 => ?_, h⟩
  have := congrArg (iota ℂ_[p] p) h0
  rw [map_mul, map_pow, map_pow, iota_periodT, map_natCast, map_zero] at this
  exact mul_ne_zero (pow_ne_zero _ (fontaineT_ne_zero hε hζ)) (pow_ne_zero _ natCast_p_ne_zero_bdR) this

set_option maxHeartbeats 1600000 in

theorem isACrisFraction_of_mem_fracBCris {y : PadicAlgCl p}
    (hy : algClToBdRField p y ∈ fracBCris hε hζ) : IsACrisFraction y := by
  by_cases hy0 : y = 0
  · rw [hy0]; exact ⟨0, 1, one_ne_zero_aCris, by rw [map_zero, map_zero, zero_mul]⟩
  obtain ⟨u, v, huv⟩ := exists_eq_div_of_mem_closure_range (iotaB hε hζ) hy
  have hinj : Function.Injective (algebraMap 𝔹 𝔹dR) := IsFractionRing.injective 𝔹 𝔹dR
  have e : algebraMap 𝔹 𝔹dR (algClToBdR p y) = algClToBdRField p y := rfl
  have hyne : algClToBdRField p y ≠ 0 := fun h0 =>
    hy0 (injective_algClToBdR p (hinj (by rw [e, h0, map_zero, map_zero])))
  have hv : iotaB hε hζ v ≠ 0 := fun h0 => hyne (by rw [huv, h0, div_zero])
  have h1 : algClToBdRField p y * iotaB hε hζ v = iotaB hε hζ u := by
    rw [huv, div_mul_cancel₀ _ hv]
  obtain ⟨wu, su, hsu, hu⟩ := exists_iotaB_mul_eq hε hζ u
  obtain ⟨wv, sv, hsv, hv'⟩ := exists_iotaB_mul_eq hε hζ v
  have hwv : wv ≠ 0 := by
    intro h0
    rw [h0, map_zero, map_zero] at hv'
    exact mul_ne_zero hv ((map_ne_zero_iff _ hinj).2 (iota_ne_zero hsv)) hv'
  refine ⟨wu * sv, wv * su, mul_ne_zero_aCris hwv hsu, hinj ?_⟩
  rw [map_mul, map_mul, map_mul, map_mul, map_mul, e]
  exact mul_eq_mul_of_eqs h1 hu hv'

theorem mem_unramifiedClosure_of_mem_fracBCris {y : PadicAlgCl p}
    (hy : algClToBdRField p y ∈ fracBCris hε hζ) : y ∈ unramifiedClosure p :=
  (isACrisFraction_of_mem_fracBCris hε hζ hy).mem_unramifiedClosure

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

set_option maxHeartbeats 1600000 in

theorem fracBCris_fixed [FiniteDimensional ℚ_[p] K] {x : 𝔹dR} (hx : x ∈ fracBCris hε hζ)
    (hfix : ∀ σ : Gal(PadicAlgCl p/K), σ • x = x) :
    ∃ k ∈ maxUnramified p K, x = algClToBdRField p k := by
  obtain ⟨k, hk⟩ := bDeRham_fixed K x hfix
  have e : x = algClToBdRField p (k : PadicAlgCl p) := hk.symm
  refine ⟨k, ⟨k.2, ?_⟩, e⟩
  exact mem_unramifiedClosure_of_mem_fracBCris hε hζ (e ▸ hx)

set_option maxHeartbeats 1600000 in

theorem mem_fracBCris_of_mem_maxUnramified {k : PadicAlgCl p} (hk : k ∈ maxUnramified p K) :
    algClToBdRField p k ∈ fracBCris hε hζ ∧
      ∀ σ : Gal(PadicAlgCl p/K), σ • algClToBdRField p k = algClToBdRField p k := by
  obtain ⟨x, -, hx⟩ := exists_bCris_fixed hε hζ hk
  refine ⟨?_, fun σ => gal_smul_algebraMap_intermediateField_bDeRham σ (⟨k, hk.1⟩ : K)⟩
  have e : algClToBdRField p k = iotaB hε hζ x := hx.symm
  rw [e]
  exact iotaB_mem_fracBCris hε hζ x

theorem fixed_fracBCris_eq [FiniteDimensional ℚ_[p] K] :
    {x : 𝔹dR | x ∈ fracBCris hε hζ ∧ ∀ σ : Gal(PadicAlgCl p/K), σ • x = x} =
      algClToBdRField p '' (maxUnramified p K : Set (PadicAlgCl p)) := by
  ext x
  constructor
  · rintro ⟨hx, hfix⟩
    obtain ⟨k, hk, rfl⟩ := fracBCris_fixed hε hζ hx hfix
    exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact mem_fracBCris_of_mem_maxUnramified hε hζ hk

end ACris

end GroundTheory.PAdicHodge
