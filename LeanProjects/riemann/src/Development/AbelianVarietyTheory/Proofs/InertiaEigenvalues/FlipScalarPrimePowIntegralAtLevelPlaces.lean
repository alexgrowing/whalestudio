import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFlipDet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharInvCentralFlipIdeleEqProdLocalComponentsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharInfinityEqCoeffMulHalfNormPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFieldElementLocalComponentsLevelNumberStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralFlipScalarMemCoefficientFieldStatement
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries

theorem exists_pow_mul_mem_of_mem_fieldRange (z : ℂ) (l : ℕ) (hl : l.Prime) : ∃ c : ℕ, ∀ (k : Type) [Field k] [NumberField k]
    (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k)) (O : Subring ℂ), ((l : ℕ) : 𝓞 k) ∈ la.asIdeal → ValRing σ la O →
    z ∈ σ.fieldRange → (l : ℂ) ^ c * z ∈ O := by
  classical
  by_cases h : ∃ m : ℕ, m ≠ 0 ∧ IsIntegral ℤ ((m : ℂ) * z)
  · obtain ⟨m, hm0, hint⟩ := h
    obtain ⟨c, m', hm', hmeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 l hl.ne_one
    refine ⟨c, fun k _ _ σ la O hla hO hz => ?_⟩
    obtain ⟨y, rfl⟩ := hz
    have hti : IsIntegral ℤ ((m : k) * y) := by
      rw [← isIntegral_algHom_iff σ.toIntAlgHom σ.injective]
      simpa using hint
    have hm'0 : (m' : k) ≠ 0 := by
      rintro h0
      rw [Nat.cast_eq_zero] at h0
      subst h0
      simp at hmeq
      exact hm0 hmeq
    have hcop : IsCoprime (m' : ℤ) (l : ℤ) :=
      Nat.isCoprime_iff_coprime.2 (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hl).2 hm'))
    have hnot : ((m' : ℕ) : 𝓞 k) ∉ la.asIdeal := by
      intro hmem
      obtain ⟨s, t, hst⟩ := hcop
      apply la.isPrime.ne_top
      rw [Ideal.eq_top_iff_one]
      have : ((s : 𝓞 k) * ((m' : ℕ) : 𝓞 k) + (t : 𝓞 k) * ((l : ℕ) : 𝓞 k)) = 1 := by
        have := congrArg (Int.cast : ℤ → 𝓞 k) hst
        push_cast at this
        exact this
      rw [← this]
      exact la.asIdeal.add_mem (la.asIdeal.mul_mem_left _ hmem) (la.asIdeal.mul_mem_left _ hla)
    have hv1 : la.valuation k (m' : k) = 1 := by
      have e : ((m' : ℕ) : k) = algebraMap (𝓞 k) k ((m' : ℕ) : 𝓞 k) := (map_natCast _ _).symm
      rw [e, HeightOneSpectrum.valuation_of_algebraMap]
      exact HeightOneSpectrum.intValuation_eq_one_iff.2 hnot
    have hvt : la.valuation k ((m : k) * y) ≤ 1 := by
      have := HeightOneSpectrum.valuation_le_one (K := k) la (⟨(m : k) * y, hti⟩ : 𝓞 k)
      exact this
    have heq : ((l : k) ^ c * y) = ((m : k) * y) / (m' : k) := by
      rw [hmeq]; push_cast; field_simp
    have hmem := hO ((l : k) ^ c * y) (by rw [heq, map_div₀, hv1, div_one]; exact hvt)
    simpa using hmem
  · refine ⟨0, fun k _ _ σ la O hla hO hz => ?_⟩
    exfalso
    obtain ⟨y, rfl⟩ := hz
    have hy : IsAlgebraic ℤ y := (IsFractionRing.isAlgebraic_iff ℤ ℚ k).2 (Algebra.IsAlgebraic.isAlgebraic y)
    obtain ⟨m, hm0, hmi⟩ := hy.exists_integral_multiple
    apply h
    refine ⟨m.natAbs, by simpa using hm0, ?_⟩
    have h2 : IsIntegral ℤ (σ (m • y)) := hmi.map σ.toIntAlgHom
    rcases Int.natAbs_eq m with hm | hm
    · rw [hm] at h2; simpa [zsmul_eq_mul] using h2
    · rw [hm] at h2
      have h3 := h2.neg
      simpa [zsmul_eq_mul, neg_mul] using h3

theorem flipScal_pow_mem : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → Odd W.rank → ∀ (χ : Formalism.L2.Host.HChar D.host.E) (M₀ l : ℕ), ChiData χW χ M₀ → l.Prime → M₀ ≠ 0 → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)), ∃ c : ℕ, ∀ (eT : AE D) (x : (AE D)ˣ), IsIdemSum eT T → (∀ PP ∈ T, ((M₀ : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → IsFlipDet V eT M₀ x → ∀ (k : Type) [Field k] [NumberField k] (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k)) (O : Subring ℂ), ((l : ℕ) : 𝓞 k) ∈ la.asIdeal → ValRing σ la O → ConjIn D σ → χ.ValuesIn (-1 / 2) σ → Odd M₀ → Nat.Coprime M₀ (GlobalTheory.Tow.badN D) → (l : ℂ) ^ c * flipScal χW V W T M₀ x ∈ O := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hVP hW χ M₀ l hχ hl hM T
  have hM' : ((M₀ : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast hM
  set u : D.host.Eˣ := Units.mk0 _ hM' with hu
  set z : ℂ := (∏ PP ∈ T, ((χ.locK PP u : ℂˣ) : ℂ) ^ V.rank) *
    ((Real.sqrt (flipIdx V W T M₀ : ℝ) : ℝ) : ℂ)⁻¹ with hz
  obtain ⟨c, hc⟩ := exists_pow_mul_mem_of_mem_fieldRange z l hl
  refine ⟨c, fun eT x hT hTM hx k _ _ σ la O hla hO hconj hval _ _ => ?_⟩
  have hfl : flipScal χW V W T M₀ x = z := by
    unfold flipScal
    rw [GlobalTheory.T.char_inv_centralFlipIdele_eq_prod_local_components D V χW χ M₀ u T eT x hχ.1 rfl hT hx]
  rw [hfl]
  refine hc k σ la O hla hO ?_
  obtain ⟨a, hai, hA1, hA2⟩ := GlobalTheory.T.exists_field_element_local_components_level_number D.host.E χ M₀ u rfl T
  have hinf := GlobalTheory.T.heckeChar_infinity_eq_coeff_mul_halfNorm_pow D ψ θ V W χV χW om ΛV ΛW sW f₀ hVP χ hχ.1 k σ hconj a
  have := GlobalTheory.T.centralFlipScalar_mem_coefficientField D.host.E χ M₀ V.rank W.rank u a T k σ hW rfl hai hTM (fun v hv => hχ.2.1 v hv) hval hinf hA1 hA2
  simpa [hz, flipIdx] using this

end GlobalTheory.LevelSeries

end
