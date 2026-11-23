import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCSpan
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCMinima
import Formalism.SharpRestriction.Divisibility.WeightFamilies
import Formalism.SharpRestriction.Divisibility.WeightAlgebra

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

namespace ConjugateMinimaInstance

open NumberField Formalism.MainNotions.ModuliIntegralCharts Formalism.BasicNotions

theorem scalar_frame_w_zero_exists (D : D7) : ∃ w₀ : 𝓞 D.host.E, (w₀ : D.host.E) + D.host.conj w₀ = 1 := by
  have hd : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  have hcc : (((D.host.gal D.host.conj).1.2 : ℤˣ) : ℤ) = -1 := by
    have hg : D.host.gal D.host.conj = Formalism.HC.Frame.cc _ := by
      simp [Formalism.HC.HostRaw.conj]
    rw [hg]
    simp only [Formalism.HC.Frame.cc] <;> decide
  have hc : D.host.conj D.host.sqd = -D.host.sqd := by
    rw [D.host.gal_sqd, hcc]
    simp
  obtain ⟨m, hm⟩ : ∃ m : ℕ, D.host.d = 4 * m + 3 := ⟨D.host.d / 4, by omega⟩
  have hs : D.host.sqd ^ 2 = -(4 * (m : D.host.E) + 3) := by
    have h0 := D.host.sqd_sq
    rw [hm] at h0
    push_cast at h0
    exact h0
  have hint : IsIntegral ℤ ((1 + D.host.sqd) / 2) := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C ((m : ℤ) + 1), by monicity!, ?_⟩
    rw [← Polynomial.aeval_def]
    simp only [map_add, map_sub, map_pow, map_one, map_natCast, Polynomial.aeval_X, Polynomial.aeval_C,
      algebraMap_int_eq, eq_intCast, Int.cast_add, Int.cast_natCast, Int.cast_one]
    linear_combination (1 / 4 : D.host.E) * hs
  refine ⟨⟨(1 + D.host.sqd) / 2, hint⟩, ?_⟩
  show (1 + D.host.sqd) / 2 + D.host.conj ((1 + D.host.sqd) / 2) = 1
  rw [map_div₀, map_add, map_one, hc, map_ofNat]
  ring

theorem conj_int (D : D7) (c : 𝓞 D.host.E) : ∃ c' : 𝓞 D.host.E, (c' : D.host.E) = D.host.conj c :=
  ⟨⟨D.host.conj c, c.isIntegral_coe.map (((D.host.conj : D.host.E ≃ₐ[ℚ] D.host.E) : D.host.E →ₐ[ℚ] D.host.E).restrictScalars ℤ)⟩, rfl⟩

theorem conj_ne (D : D7) : ∃ z : D.host.E, D.host.conj z ≠ z := by
  by_contra h
  push_neg at h
  have h1 : D.host.conj = 1 := AlgEquiv.ext h
  have h2 : Formalism.HC.Frame.cc D.R.toFrame = 1 := by
    have := congrArg D.host.gal h1
    simpa [Formalism.HC.HostRaw.conj] using this
  have h3 := congrArg Prod.fst h2
  simp only [Formalism.HC.Frame.cc, Prod.fst_one] at h3
  revert h3
  decide

private theorem bil_expand_lemma {Y ι : Type} [AddCommGroup Y] [Fintype ι] (f : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ)
    (b : Module.Basis ι ℤ Y) (a : Y) :
    f a a = ∑ i, ∑ k, ((b.repr a i : ℤ) : ℝ) * ((b.repr a k : ℤ) : ℝ) * f (b i) (b k) := by
  conv_lhs => rw [← b.sum_repr a]
  simp only [map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply, zsmul_eq_mul,
    Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

private theorem quad_nonneg_lemma {Y : Type} [AddCommGroup Y] (f : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ)
    (hpd : ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℤ Y),
      ∀ c : ι → ℝ, c ≠ 0 → 0 < ∑ i, ∑ k, c i * c k * f (b i) (b k)) (a : Y) : 0 ≤ f a a := by
  obtain ⟨ι, hι, b, hb⟩ := hpd
  by_cases ha : a = 0
  · simp [ha]
  · have hc : (fun i => ((b.repr a i : ℤ) : ℝ)) ≠ 0 := by
      intro h0
      apply ha
      apply b.repr.injective
      ext i
      have := congrFun h0 i
      simpa using this
    have hpos := hb _ hc
    have hexp := bil_expand_lemma f b a
    linarith

theorem phiCSpan_loc (D : D7) : ∃ w₀ : 𝓞 D.host.E, (w₀ : D.host.E) + D.host.conj w₀ = 1 ∧
    ∀ {r j p : ℕ} (L : Loc D r j p) {Z : L.Mdl} (y : L.Pt Z) (k : ℕ) (x : Fin k → L.Ylat y),
      (∀ u : L.Ylat y, ∃ n : ℕ, 0 < n ∧ n • u ∈ Submodule.span (𝓞 D.host.E) (Set.range x)) →
      L.phiCy y ≤ ∑ b, L.be y (w₀ • x b) (x b) := by
  obtain ⟨w₀, hw⟩ := scalar_frame_w_zero_exists D
  refine ⟨w₀, hw, ?_⟩
  intro r j p L Z y k x hx
  have hnn : ∀ a : L.Ylat y, 0 ≤ L.be y a a := fun a => quad_nonneg_lemma (L.be y) (L.be_posDef y) a
  have h := phiCSpan_holds
  unfold PhiCSpanStatement at h
  exact h D.host.E (fun z => D.host.conj z) (conj_int D) (L.Ylat y) w₀ hw
    ⟨L.be y, L.be_symm y, L.be_bal y⟩ hnn k x hx

theorem phiCMinima_loc (D : D7) {r j p : ℕ} (L : Loc D r j p) {Z : L.Mdl} (y : L.Pt Z) :
    ∃ v : Fin (Module.finrank ℤ (L.Ylat y)) → L.Ylat y, LinearIndependent ℤ v ∧
      ∀ i, L.be y (v i) (v i) / 2 ≤
        (|(NumberField.discr D.host.E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ D.host.E)) /
            (2 * Module.finrank ℚ D.host.E) * (Module.finrank ℤ (L.Ylat y) : ℝ) ^ 2 * L.phiCy y := by
  obtain ⟨w₀, hw⟩ := scalar_frame_w_zero_exists D
  obtain ⟨ι, hι, b, -⟩ := L.be_posDef y
  exact phiCMinima_holds D.host.E (fun z => D.host.conj z) (fun φ z => WeightFamilies.emb_conj D φ z) (conj_ne D) w₀ hw
    (L.Ylat y) (L.beS y) ⟨ι, hι, b, L.gram_posDef y b⟩

theorem phiC_rec_eq {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P j) (hj : j < D.R.m)
    (la : IsDedekindDomain.HeightOneSpectrum (𝓞 B.KO)) (y : X.Pt la) :
    X.phiC la y = (eWL B.KO la : ℝ) * (P.loc X.dat (WeightAlgebra.resCh la)).phiCy (X.pt66 la y) := by
  simp [WeightAlgebra.PJ.phiC, hj]

theorem phiCMinima_rec {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P j) (hj : j < D.R.m)
    (la : IsDedekindDomain.HeightOneSpectrum (𝓞 B.KO)) (y : X.Pt la) :
    ∃ v : Fin (Module.finrank ℤ ((P.loc X.dat (WeightAlgebra.resCh la)).Ylat (X.pt66 la y))) →
        (P.loc X.dat (WeightAlgebra.resCh la)).Ylat (X.pt66 la y), LinearIndependent ℤ v ∧
      ∀ i, (eWL B.KO la : ℝ) * ((P.loc X.dat (WeightAlgebra.resCh la)).be (X.pt66 la y) (v i) (v i) / 2) ≤
        (|(NumberField.discr D.host.E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ D.host.E)) /
            (2 * Module.finrank ℚ D.host.E) *
          (Module.finrank ℤ ((P.loc X.dat (WeightAlgebra.resCh la)).Ylat (X.pt66 la y)) : ℝ) ^ 2 * X.phiC la y := by
  obtain ⟨v, hv, hb⟩ := phiCMinima_loc D (P.loc X.dat (WeightAlgebra.resCh la)) (X.pt66 la y)
  refine ⟨v, hv, fun i => ?_⟩
  rw [phiC_rec_eq X hj la y]
  have he : (0 : ℝ) ≤ (eWL B.KO la : ℝ) := by positivity
  have := mul_le_mul_of_nonneg_left (hb i) he
  calc (eWL B.KO la : ℝ) * ((P.loc X.dat (WeightAlgebra.resCh la)).be (X.pt66 la y) (v i) (v i) / 2)
      ≤ (eWL B.KO la : ℝ) * ((|(NumberField.discr D.host.E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ D.host.E)) /
            (2 * Module.finrank ℚ D.host.E) *
          (Module.finrank ℤ ((P.loc X.dat (WeightAlgebra.resCh la)).Ylat (X.pt66 la y)) : ℝ) ^ 2 *
            (P.loc X.dat (WeightAlgebra.resCh la)).phiCy (X.pt66 la y)) := this
    _ = _ := by ring

end ConjugateMinimaInstance

end Formalism.MainNotions.ModuliIntegralCharts.H1
