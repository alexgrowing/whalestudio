import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NatCastMemPlaceAt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNormEqOfMemClosure
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRamificationOverPlaceOfCdvrReadingInCp
open NumberField IsDedekindDomain Formalism.L2.Pj GlobalTheory.GeoTie

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.KurApprox
open Polynomial
variable {p : ℕ} [Fact p.Prime]

section Val

variable {K : Type} [Field K] [NumberField K] (ψ : K →+* ℂ_[p])

theorem valuation_eq_exp {x : K} (hx : x ≠ 0) :
    (placeAt ψ).valuation K x = WithZero.exp (-vLa (placeAt ψ) x) := by
  rw [vLa, neg_neg, WithZero.exp_log (((placeAt ψ).valuation K).ne_zero_iff.2 hx)]

theorem exists_uniformizer : ∃ π : K, π ≠ 0 ∧ vLa (placeAt ψ) π = 1 ∧ ‖ψ π‖ < 1 := by
  set P := placeAt ψ
  obtain ⟨π, hπ⟩ := P.intValuation_exists_uniformizer
  have hπ1 : P.intValuation π < 1 := by
    rw [hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hπn : ‖ψ (π : K)‖ < 1 := (mem_placeAt ψ π).1 ((P.intValuation_lt_one_iff_mem π).1 hπ1)
  have hνπ : P.valuation K (π : K) = WithZero.exp (-1) := by
    rw [← hπ]; exact HeightOneSpectrum.valuation_of_algebraMap P π
  have hπ0 : (π : K) ≠ 0 := by
    intro h
    rw [h, map_zero] at hνπ
    exact WithZero.exp_ne_zero hνπ.symm
  refine ⟨π, hπ0, ?_, hπn⟩
  simp [vLa, P, hνπ]

theorem norm_eq_zpow {π : K} (hπ0 : π ≠ 0) (hπ : vLa (placeAt ψ) π = 1) {x : K} (hx : x ≠ 0) :
    ‖ψ x‖ = ‖ψ π‖ ^ vLa (placeAt ψ) x := by
  set P := placeAt ψ
  set n := vLa P x
  set b := x * π ^ (-n) with hb
  have hb0 : b ≠ 0 := mul_ne_zero hx (zpow_ne_zero _ hπ0)
  have hνb : P.valuation K b = 1 := by
    rw [hb, map_mul, map_zpow₀, valuation_eq_exp ψ hx, valuation_eq_exp ψ hπ0, hπ, ← WithZero.exp_zsmul,
      ← WithZero.exp_add]
    simp only [smul_eq_mul, mul_neg, mul_one, neg_neg, n]
    rw [show -vLa (placeAt ψ) x + vLa P x = 0 from neg_add_cancel _, WithZero.exp_zero]
  have h1 : ‖ψ b‖ ≤ 1 := GlobalTheory.ReadingOver.norm_le_one_of_valuation_le_one ψ hνb.le
  have h2 : ‖ψ b⁻¹‖ ≤ 1 := GlobalTheory.ReadingOver.norm_le_one_of_valuation_le_one ψ (by rw [map_inv₀, hνb, inv_one])
  have hpos : 0 < ‖ψ b‖ := norm_pos_iff.2 ((map_ne_zero ψ).2 hb0)
  have hb1 : ‖ψ b‖ = 1 := by
    rw [map_inv₀, norm_inv] at h2
    exact le_antisymm h1 ((inv_le_one₀ hpos).1 h2)
  have hxb : x = b * π ^ n := by
    rw [hb, mul_assoc, ← zpow_add₀ hπ0, neg_add_cancel, zpow_zero, mul_one]
  rw [hxb, map_mul, norm_mul, hb1, one_mul, map_zpow₀, norm_zpow]

end Val

section Unram

variable {F F' : Type} [Field F] [NumberField F] [Field F'] [NumberField F'] [Algebra F F']

theorem vLa_eq_of_mem_kurC (φ : F →+* ℂ_[p]) (φ' : F' →+* ℂ_[p]) (hcomp : ∀ a, φ' (algebraMap F F' a) = φ a)
    (hk : ∀ x, φ' x ∈ kurC φ) (a : F) : vLa (placeAt φ') (algebraMap F F' a) = vLa (placeAt φ) a := by
  by_cases ha : a = 0
  · subst ha; simp [vLa]
  obtain ⟨π, hπ0, hπ, hπn⟩ := exists_uniformizer φ
  obtain ⟨π', hπ0', hπ', hπn'⟩ := exists_uniformizer φ'
  set c := ‖φ π‖ with hc
  set c' := ‖φ' π'‖ with hc'
  have hc0 : 0 < c := norm_pos_iff.2 ((map_ne_zero φ).2 hπ0)
  have hc0' : 0 < c' := norm_pos_iff.2 ((map_ne_zero φ').2 hπ0')
  obtain ⟨b, hb⟩ := GlobalTheory.KurValue.exists_norm_eq φ (hk π')
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero, norm_zero] at hb
    exact hc0'.ne' hb
  have e1 : c' = c ^ vLa (placeAt φ) b := by rw [hc', hb, norm_eq_zpow φ hπ0 hπ hb0]
  have hι0 : algebraMap F F' π ≠ 0 := (_root_.map_ne_zero _).2 hπ0
  have e2 : c = c' ^ vLa (placeAt φ') (algebraMap F F' π) := by
    rw [hc, ← hcomp, norm_eq_zpow φ' hπ0' hπ' hι0]
  have hinj := zpow_right_injective₀ hc0 hπn.ne
  have hmk : vLa (placeAt φ) b * vLa (placeAt φ') (algebraMap F F' π) = 1 := by
    apply hinj
    change c ^ (_ * _) = c ^ (1 : ℤ)
    rw [zpow_mul, ← e1, ← e2, zpow_one]
  have hm : vLa (placeAt φ) b = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hmk with h | h
    · exact h.1
    · exfalso
      rw [h.1, zpow_neg_one] at e1
      have : 1 < c⁻¹ := (one_lt_inv₀ hc0).2 hπn
      linarith
  rw [hm, zpow_one] at e1
  have hιa : algebraMap F F' a ≠ 0 := (_root_.map_ne_zero _).2 ha
  have e3 := norm_eq_zpow φ' hπ0' hπ' hιa
  rw [hcomp, norm_eq_zpow φ hπ0 hπ ha, ← hc, ← hc', e1] at e3
  exact (hinj e3).symm

end Unram

section Approx

variable {F : Type} [Field F] (φ : F →+* ℂ_[p])

def adjRoots (N : ℕ) : IntermediateField F (PAt φ) :=
  IntermediateField.adjoin F {x : PAt φ | x ^ N = 1}

theorem finite_roots {N : ℕ} (hN : 0 < N) : {x : PAt φ | x ^ N = 1}.Finite := by
  classical
  refine ((nthRoots N (1 : PAt φ)).toFinset.finite_toSet).subset fun x hx => ?_
  simpa [Polynomial.mem_nthRoots hN] using hx

theorem finiteDimensional_adjRoots {N : ℕ} (hN : 0 < N) : FiniteDimensional F (adjRoots φ N) := by
  haveI := (finite_roots φ hN).to_subtype
  refine IntermediateField.finiteDimensional_adjoin fun x hx => ?_
  have h : x ^ N = 1 := hx
  exact IsIntegral.of_pow hN (by rw [h]; exact isIntegral_one)

theorem numberField_adjRoots [NumberField F] {N : ℕ} (hN : 0 < N) : NumberField (adjRoots φ N) := by
  haveI := finiteDimensional_adjRoots φ hN
  haveI : FiniteDimensional ℚ (adjRoots φ N) := Module.Finite.trans F (adjRoots φ N)
  constructor

theorem adjRoots_mono {N M : ℕ} (h : N ∣ M) : adjRoots φ N ≤ adjRoots φ M := by
  obtain ⟨k, rfl⟩ := h
  refine IntermediateField.adjoin.mono _ _ _ fun x hx => ?_
  have hx' : x ^ N = 1 := hx
  show x ^ (N * k) = 1
  rw [pow_mul, hx', one_pow]

theorem adjRoots_le_kurC {N : ℕ} (hN : 0 < N) (hpN : ¬ p ∣ N) (z : PAt φ) (hz : z ∈ adjRoots φ N) :
    toCp φ z ∈ kurC φ := by
  let Kt : IntermediateField F (PAt φ) :=
    (show Subfield (PAt φ) from kurC φ).toIntermediateField fun a => mem_kurC φ a
  have hle : adjRoots φ N ≤ Kt := by
    refine IntermediateField.adjoin_le_iff.2 fun x hx => ?_
    have hx' : x ^ N = 1 := hx
    exact root_mem_kurC (p := p) φ hpN hx'
  exact hle hz

def kurAlg : Subfield ℂ_[p] where
  carrier := {z | ∃ N : ℕ, 0 < N ∧ ¬ p ∣ N ∧ (show PAt φ from z) ∈ adjRoots φ N}
  mul_mem' := by
    rintro x y ⟨N, hN, hpN, hx⟩ ⟨M, hM, hpM, hy⟩
    refine ⟨N * M, Nat.mul_pos hN hM, fun h => ?_, ?_⟩
    · rcases (Nat.Prime.dvd_mul (Fact.out : p.Prime)).1 h with h | h
      exacts [hpN h, hpM h]
    · exact mul_mem (adjRoots_mono φ (dvd_mul_right N M) hx) (adjRoots_mono φ (dvd_mul_left M N) hy)
  one_mem' := ⟨1, one_pos, (Fact.out : p.Prime).not_dvd_one, one_mem _⟩
  add_mem' := by
    rintro x y ⟨N, hN, hpN, hx⟩ ⟨M, hM, hpM, hy⟩
    refine ⟨N * M, Nat.mul_pos hN hM, fun h => ?_, ?_⟩
    · rcases (Nat.Prime.dvd_mul (Fact.out : p.Prime)).1 h with h | h
      exacts [hpN h, hpM h]
    · exact add_mem (adjRoots_mono φ (dvd_mul_right N M) hx) (adjRoots_mono φ (dvd_mul_left M N) hy)
  zero_mem' := ⟨1, one_pos, (Fact.out : p.Prime).not_dvd_one, zero_mem _⟩
  neg_mem' := by
    rintro x ⟨N, hN, hpN, hx⟩
    exact ⟨N, hN, hpN, neg_mem hx⟩
  inv_mem' := by
    rintro x ⟨N, hN, hpN, hx⟩
    exact ⟨N, hN, hpN, inv_mem hx⟩

theorem kurC_le : kurC φ ≤ (kurAlg φ).topologicalClosure := by
  refine Subfield.topologicalClosure_minimal _ (sup_le ?_ ?_) (Subfield.isClosed_topologicalClosure _)
  · rintro _ ⟨a, rfl⟩
    exact Subfield.le_topologicalClosure _ ⟨1, one_pos, (Fact.out : p.Prime).not_dvd_one,
      IntermediateField.algebraMap_mem _ a⟩
  · refine Subfield.topologicalClosure_minimal _ ?_ (Subfield.isClosed_topologicalClosure _)
    refine (Subfield.closure_le.2 ?_).trans (Subfield.le_topologicalClosure _)
    rintro ζ ⟨n, hn, hpn, hζ⟩
    exact ⟨n, hn, hpn, IntermediateField.subset_adjoin _ _ hζ⟩

end Approx

end GlobalTheory.KurApprox

namespace GlobalTheory.KurApprox

theorem kur_approx : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (φ : F →+* ℂ_[p]) (n : ℕ)
    (y : Fin n → ℂ_[p]), (∀ s, y s ∈ kurC φ) → ∀ ε : ℝ, 0 < ε →
    ∃ (F' : Type) (_ : Field F') (_ : NumberField F') (_ : Algebra F F') (φ' : F' →+* ℂ_[p]),
      (∀ a, φ' (algebraMap F F' a) = φ a) ∧ (∀ a : F, vLa (placeAt φ') (algebraMap F F' a) = vLa (placeAt φ) a) ∧
      ∃ a' : Fin n → F', ∀ s, ‖y s - φ' (a' s)‖ < ε := by
  intro p _ F _ _ φ n y hy ε hε
  have h1 : ∀ s, ∃ z : ℂ_[p], ∃ N : ℕ, 0 < N ∧ ¬ p ∣ N ∧ (show PAt φ from z) ∈ adjRoots φ N ∧ ‖y s - z‖ < ε := by
    intro s
    have hs : y s ∈ closure ((kurAlg φ : Subfield ℂ_[p]) : Set ℂ_[p]) := kurC_le φ (hy s)
    obtain ⟨z, ⟨N, hN, hpN, hz⟩, hd⟩ := Metric.mem_closure_iff.1 hs ε hε
    exact ⟨z, N, hN, hpN, hz, by rwa [dist_eq_norm] at hd⟩
  choose z N hN hpN hz hd using h1
  set M := ∏ s, N s with hM
  have hM0 : 0 < M := Finset.prod_pos fun s _ => hN s
  have hpM : ¬ p ∣ M := by
    intro h
    obtain ⟨s, _, hs⟩ := ((Fact.out : p.Prime).prime.dvd_finsetProd_iff _).1 h
    exact hpN s hs
  let K := adjRoots φ M
  haveI : NumberField K := numberField_adjRoots φ hM0
  let φ' : K →+* ℂ_[p] := (toCp φ).comp (algebraMap K (PAt φ))
  have hcomp : ∀ a, φ' (algebraMap F K a) = φ a := fun a => rfl
  have hk : ∀ x : K, φ' x ∈ kurC φ := fun x => adjRoots_le_kurC φ hM0 hpM x x.2
  have hzM : ∀ s, (show PAt φ from z s) ∈ K := fun s =>
    adjRoots_mono φ (Finset.dvd_prod_of_mem N (Finset.mem_univ s)) (hz s)
  exact ⟨K, inferInstance, inferInstance, inferInstance, φ', hcomp, vLa_eq_of_mem_kurC φ φ' hcomp hk,
    fun s => ⟨z s, hzM s⟩, fun s => hd s⟩

end GlobalTheory.KurApprox
