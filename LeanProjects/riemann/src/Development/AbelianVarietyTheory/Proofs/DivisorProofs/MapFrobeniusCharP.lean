import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArtinSchreierSystemIntegralStatement
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.LemY

theorem map_frobenius_charP (p : ℕ) [Fact p.Prime] {S K : Type} [CommRing S] [CommRing K] [CharP S p] [CharP K p]
    (f : S →+* K) (x : WittVector p S) :
    WittVector.map f (WittVector.frobenius x) = WittVector.frobenius (WittVector.map f x) := by
  ext n
  simp [WittVector.coeff_frobenius_charP, WittVector.map_coeff, map_pow]

theorem map_mulVec_witt (p : ℕ) [Fact p.Prime] {S K : Type} [CommRing S] [CommRing K] (f : S →+* K) (d : ℕ)
    (U : Matrix (Fin d) (Fin d) (WittVector p S)) (B : Fin d → WittVector p S) (i : Fin d) :
    WittVector.map f ((U *ᵥ B) i) = (U.map (WittVector.map f) *ᵥ (fun j => WittVector.map f (B j))) i := by
  rw [RingHom.map_mulVec]; rfl

theorem step : ∀ (p : ℕ) [Fact p.Prime] (S K : Type) [CommRing S] [IsDomain S] [ValuationRing S] [CharP S p] [PerfectRing S p] [Field K] [Algebra S K] [IsFractionRing S K] [CharP K p] [PerfectRing K p] (d : ℕ) (U : Matrix (Fin d) (Fin d) (WittVector p S)) (Z : Fin d → WittVector p S) (Y : Fin d → WittVector p K), (∀ i, WittVector.frobenius (Y i) = (U.map (WittVector.map (algebraMap S K)) *ᵥ Y) i + WittVector.map (algebraMap S K) (Z i)) → ∃ (B Z₁ : Fin d → WittVector p S) (Y₁ : Fin d → WittVector p K), (∀ i, Y i = WittVector.map (algebraMap S K) (B i) + (p : WittVector p K) * Y₁ i) ∧ ∀ i, WittVector.frobenius (Y₁ i) = (U.map (WittVector.map (algebraMap S K)) *ᵥ Y₁) i + WittVector.map (algebraMap S K) (Z₁ i) := by
  intro p _ S K _ _ _ _ _ _ _ _ _ _ d U Z Y hY
  set f : S →+* K := algebraMap S K with hf
  set F : WittVector p S →+* WittVector p K := WittVector.map f with hF

  have h0 : ∀ i, (Y i).coeff 0 ^ p = ((U.map WittVector.constantCoeff).map f *ᵥ fun j => (Y j).coeff 0) i
      + f ((Z i).coeff 0) := by
    intro i
    have := congrArg (fun w => w.coeff 0) (hY i)
    rw [WittVector.coeff_frobenius_charP] at this
    rw [this]
    have e1 := RingHom.map_mulVec (WittVector.constantCoeff (p := p) (R := K)) (U.map F) Y i
    change WittVector.constantCoeff ((U.map F *ᵥ Y) i + F (Z i)) = _
    rw [map_add, e1]
    simp [Matrix.map_map, Function.comp_def, WittVector.constantCoeff_apply, hF, WittVector.map_coeff]
  have hb : ∀ i, ∃ c, f c = (Y i).coeff 0 := fun i =>
    RingHom.mem_range.mp (GlobalTheory.T.artin_schreier_system_integral p S K d (U.map WittVector.constantCoeff) (fun i => (Z i).coeff 0)
      (fun i => (Y i).coeff 0) h0 i)
  choose b hbY using hb
  set B : Fin d → WittVector p S := fun i => WittVector.teichmuller p (b i) with hB
  have hdiff : ∀ i, ∃ c, Y i - F (B i) = (p : WittVector p K) * c := by
    intro i
    have hm : Y i - F (B i) ∈ Ideal.span {(p : WittVector p K)} := by
      rw [WittVector.mem_span_p_iff_coeff_zero_eq_zero, ← WittVector.constantCoeff_apply, map_sub,
        WittVector.constantCoeff_apply, WittVector.constantCoeff_apply, hB, hF, WittVector.map_teichmuller,
        WittVector.teichmuller_coeff_zero, hbY, sub_self]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hm
    exact ⟨c, by rw [← hc, mul_comm]⟩
  choose Y₁ hY₁ using hdiff
  have hYfun : Y = (fun j => F (B j)) + (p : WittVector p K) • Y₁ := by
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination hY₁ j
  set Wv : Fin d → WittVector p S := fun i => (U *ᵥ B) i + Z i - WittVector.frobenius (B i) with hWv
  have hWimg : ∀ i, F (Wv i) = (p : WittVector p K) * (WittVector.frobenius (Y₁ i) - (U.map F *ᵥ Y₁) i) := by
    intro i
    have h := hY i
    have e2 : (U.map F *ᵥ Y) i = (U.map F *ᵥ fun j => F (B j)) i + (p : WittVector p K) * (U.map F *ᵥ Y₁) i := by
      rw [hYfun, Matrix.mulVec_add, Matrix.mulVec_smul]
      rfl
    have e3 : Y i = F (B i) + (p : WittVector p K) * Y₁ i := by linear_combination hY₁ i
    rw [e2, e3, map_add, map_mul, map_natCast] at h
    have e4 : F (Wv i) = (U.map F *ᵥ fun j => F (B j)) i + F (Z i) - WittVector.frobenius (F (B i)) := by
      rw [hWv]
      simp only
      rw [map_sub, map_add, map_mulVec_witt, hF, map_frobenius_charP]
    rw [e4]
    linear_combination (-1 : WittVector p K) * h
  have hW0 : ∀ i, (Wv i).coeff 0 = 0 := by
    intro i
    apply IsFractionRing.injective S K
    rw [map_zero]
    have h1 : F (Wv i) ∈ Ideal.span {(p : WittVector p K)} :=
      Ideal.mem_span_singleton'.mpr ⟨_, by rw [hWimg i, mul_comm]⟩
    rw [WittVector.mem_span_p_iff_coeff_zero_eq_zero, hF, WittVector.map_coeff] at h1
    exact h1
  have hZ : ∀ i, ∃ c, c * (p : WittVector p S) = Wv i := fun i =>
    Ideal.mem_span_singleton'.mp ((WittVector.mem_span_p_iff_coeff_zero_eq_zero _).mpr (hW0 i))
  choose Z₁ hZ₁ using hZ
  refine ⟨B, Z₁, Y₁, fun i => by linear_combination hY₁ i, fun i => ?_⟩
  have hp : (p : WittVector p K) ≠ 0 := WittVector.p_nonzero p K
  apply mul_left_cancel₀ hp
  have := hWimg i
  rw [← hZ₁ i, map_mul, map_natCast] at this
  linear_combination -this

end GlobalTheory.LemY
