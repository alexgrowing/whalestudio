import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.CellDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfComps

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open IsDedekindDomain NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SmallRatCell

open RestrictedProduct InfinitePlace.Completion

variable {F : Type} [Field F] [NumberField F]

theorem exists_nat_mem (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ v ∈ S, ((N : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  have hpos : 0 < ∏ v ∈ S, Ideal.absNorm v.asIdeal :=
    Finset.prod_pos fun v _ => Nat.pos_of_ne_zero (by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
  refine ⟨2 * ∏ v ∈ S, Ideal.absNorm v.asIdeal, by omega, fun v hv => ?_⟩
  obtain ⟨c, hc⟩ : Ideal.absNorm v.asIdeal ∣ 2 * ∏ v ∈ S, Ideal.absNorm v.asIdeal :=
    (Finset.dvd_prod_of_mem _ hv).mul_left 2
  rw [hc]
  push_cast
  exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)

def tau (N k : ℕ) : ℚ := (N : ℚ) ^ k / (1 + ((N : ℚ) ^ k) ^ 2)

theorem tau_pos {N : ℕ} (hN : 2 ≤ N) (k : ℕ) : 0 < tau N k := by
  have : (0 : ℚ) < N := by exact_mod_cast (by omega : 0 < N)
  unfold tau
  positivity

theorem tendsto_tau_fin (v : HeightOneSpectrum (𝓞 F)) {N : ℕ} (hN : ((N : ℕ) : 𝓞 F) ∈ v.asIdeal) :
    Tendsto (fun k => algebraMap F (v.adicCompletion F) ((tau N k : ℚ) : F)) atTop (𝓝 0) := by
  have hv : Valued.v (N : v.adicCompletion F) < 1 := by
    have e : (N : v.adicCompletion F) = algebraMap (𝓞 F) (v.adicCompletion F) (N : 𝓞 F) :=
      (map_natCast _ N).symm
    rw [e]
    have h1 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (N : 𝓞 F)
    have h2 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v (N : 𝓞 F)).2 hN
    exact h1 ▸ h2
  have ht := Valued.tendsto_zero_pow_of_v_lt_one hv
  have h2 : Tendsto (fun k : ℕ => 1 + ((N : v.adicCompletion F) ^ k) ^ 2) atTop (𝓝 1) := by
    simpa using (ht.pow 2).const_add 1
  have h3 := ht.div h2 one_ne_zero
  rw [zero_div] at h3
  refine h3.congr fun k => ?_
  simp [tau, map_div₀, map_add, map_pow, map_natCast]

theorem tendsto_tau_inf (w : InfinitePlace F) {N : ℕ} (hN : 2 ≤ N) :
    Tendsto (fun k => algebraMap F w.Completion ((tau N k : ℚ) : F)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hnorm : ∀ k, ‖algebraMap F w.Completion ((tau N k : ℚ) : F)‖ = (tau N k : ℝ) := fun k => by
    rw [← (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _)]
    have h := map_ratCast ((extensionEmbedding w).comp (algebraMap F w.Completion)) (tau N k)
    rw [RingHom.comp_apply] at h
    rw [h, Complex.norm_ratCast, abs_of_pos (by exact_mod_cast tau_pos hN k)]
  simp only [hnorm]
  have hb : ∀ k, (tau N k : ℝ) ≤ (1 / 2 : ℝ) ^ k := fun k => by
    have h2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have hx : (2 : ℝ) ^ k ≤ (N : ℝ) ^ k := pow_le_pow_left₀ (by norm_num) h2 k
    have hp : (0 : ℝ) < 2 ^ k := by positivity
    have hxp : (0 : ℝ) < (N : ℝ) ^ k := by linarith
    simp only [tau]
    push_cast
    rw [one_div, inv_pow, div_le_iff₀ (by positivity)]
    have : (2 : ℝ) ^ k * (N : ℝ) ^ k ≤ 1 + ((N : ℝ) ^ k) ^ 2 := by nlinarith
    rw [← div_eq_inv_mul, le_div_iff₀ hp]
    linarith
  refine squeeze_zero (fun k => by exact_mod_cast (tau_pos hN k).le) hb ?_
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

open Classical in

def finS (S : Finset (HeightOneSpectrum (𝓞 F))) (q : F) :
    Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]_[𝓟 ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ)] :=
  ⟨fun v => if v ∈ S then algebraMap F (v.adicCompletion F) q else 0, by
    rw [Filter.eventually_principal]
    intro v hv
    have hv' : v ∉ S := by simpa using hv
    simp only [if_neg hv']
    exact zero_mem _⟩

theorem cofinite_le (S : Finset (HeightOneSpectrum (𝓞 F))) :
    (cofinite : Filter (HeightOneSpectrum (𝓞 F))) ≤ 𝓟 ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ) := by
  rw [le_principal_iff, mem_cofinite, compl_compl]
  exact S.finite_toSet

def sAd (S : Finset (HeightOneSpectrum (𝓞 F))) (q : F) : AF F :=
  (fun w => algebraMap F w.Completion q,
    RestrictedProduct.inclusion _ _ (cofinite_le S) (finS S q))

theorem tendsto_sAd (S : Finset (HeightOneSpectrum (𝓞 F))) (q : ℕ → F)
    (hi : ∀ w : InfinitePlace F, Tendsto (fun k => algebraMap F w.Completion (q k)) atTop (𝓝 0))
    (hf : ∀ v ∈ S, Tendsto (fun k => algebraMap F (v.adicCompletion F) (q k)) atTop (𝓝 0)) :
    Tendsto (fun k => sAd S (q k)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun k => finS S (q k)) atTop (𝓝 0) := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.isInducing.tendsto_nhds_iff, tendsto_pi_nhds]
    intro v
    by_cases hv : v ∈ S
    · refine (hf v hv).congr fun k => ?_
      exact (if_pos hv).symm
    · refine tendsto_const_nhds.congr fun k => ?_
      show (0 : v.adicCompletion F) = _
      exact (if_neg hv).symm
  have h2 := ((RestrictedProduct.continuous_inclusion (cofinite_le S)).tendsto 0).comp h1
  refine Tendsto.prodMk_nhds (tendsto_pi_nhds.2 hi) h2

theorem one_tmul_algebraMap {A E : Type} [CommRing A] [Algebra F A] [Field E] [Algebra F E] (q : F) :
    (1 : A) ⊗ₜ[F] algebraMap F E q = algebraMap F A q ⊗ₜ[F] (1 : E) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
    TensorProduct.smul_tmul']

theorem ring_hom_mul_sub_eq_zero {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (x e y : A) (c : B)
    (hc : f e = c) (h : f x * c = f y) : f (x * e - y) = 0 := by
  rw [map_sub, map_mul, hc, h, sub_self]

open Classical in

theorem tensor_key {E : Type} [Field E] [Algebra F E] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (e : AF F ⊗[F] E) (hi : ∀ w, compInf F E w e = 1)
    (hf : ∀ v, compFin F E v e = if v ∈ S then 1 else 0) (q : F) :
    ((1 : AF F) ⊗ₜ[F] algebraMap F E q) * e = sAd S q ⊗ₜ[F] (1 : E) := by
  rw [← sub_eq_zero]
  refine GlobalTheory.CompanionTheory.AdeleComp.tensor_eq_zero _ (fun w => ?_) (fun v => ?_)
  · refine ring_hom_mul_sub_eq_zero (compInf F E w) _ _ _ _ (hi w) ?_
    rw [mul_one]
    exact one_tmul_algebraMap (A := w.Completion) _
  · refine ring_hom_mul_sub_eq_zero (compFin F E v) _ _ _ _ (hf v) ?_
    by_cases hv : v ∈ S
    · rw [if_pos hv, mul_one]
      have h : evFin F v (sAd S q) = algebraMap F (v.adicCompletion F) q := if_pos hv
      show (1 : v.adicCompletion F) ⊗ₜ[F] _ = evFin F v (sAd S q) ⊗ₜ[F] (1 : E)
      rw [h]
      exact one_tmul_algebraMap _
    · rw [if_neg hv, mul_zero]
      have h : evFin F v (sAd S q) = 0 := if_neg hv
      show 0 = evFin F v (sAd S q) ⊗ₜ[F] (1 : E)
      rw [h, TensorProduct.zero_tmul]

theorem incA_mul_idem (D : D7) (S : Finset (Pl D)) (e : AE D) (he : IsIdem S e) (q : ℚ) :
    incA D ((q : ℚ) : D.host.E) * e = sAd S ((q : ℚ) : D.host.F) • (1 : AE D) := by
  have hq : ((q : ℚ) : D.host.E) = algebraMap D.host.F D.host.E ((q : ℚ) : D.host.F) :=
    (map_ratCast (algebraMap D.host.F D.host.E) q).symm
  have hs : sAd S ((q : ℚ) : D.host.F) • (1 : AE D) =
      sAd S ((q : ℚ) : D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) := by
    show _ • ((1 : AF D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)) = _
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hs, hq]
  exact tensor_key S e he.1 he.2 _

theorem smallRat : PositivityTheory.Rg.Rsw.L.IdemEx → PositivityTheory.Rg.Rsw.Cell.SmallRat := by
  intro _ D S e he V hV M
  obtain ⟨N, hN, hmem⟩ := exists_nat_mem S
  have ht : Tendsto (fun k => sAd S ((tau N k : ℚ) : D.host.F)) atTop (𝓝 0) :=
    tendsto_sAd S _ (fun w => tendsto_tau_inf w hN) (fun v hv => tendsto_tau_fin v (hmem v hv))
  have hz : Tendsto (fun k => incA D ((tau N k : ℚ) : D.host.E) * e) atTop (𝓝 0) := by
    have h := ht.smul_const (1 : AE D)
    rw [zero_smul] at h
    exact h.congr fun k => (incA_mul_idem D S e he _).symm
  have hall : ∀ᶠ k in atTop, ∀ j : Fin M,
      ((j.1 + 1 : ℕ) : AE D) * (incA D ((tau N k : ℚ) : D.host.E) * e) ∈ V := by
    rw [Filter.eventually_all]
    intro j
    have h := hz.const_mul ((j.1 + 1 : ℕ) : AE D)
    rw [mul_zero] at h
    exact h hV
  obtain ⟨k, hk⟩ := hall.exists
  refine ⟨fun j => ((j.1 + 1 : ℕ) : ℚ) * tau N k, fun i j hij => ?_, fun j => ?_⟩
  · have h := mul_right_cancel₀ (tau_pos hN k).ne' hij
    have h2 : i.1 + 1 = j.1 + 1 := by exact_mod_cast h
    exact Fin.ext (by omega)
  · have h := hk j
    have e1 : incA D (((((j.1 + 1 : ℕ) : ℚ) * tau N k : ℚ)) : D.host.E) =
        ((j.1 + 1 : ℕ) : AE D) * incA D ((tau N k : ℚ) : D.host.E) := by
      rw [Rat.cast_mul, map_mul, Rat.cast_natCast, map_natCast]
    show incA D (((((j.1 + 1 : ℕ) : ℚ) * tau N k : ℚ)) : D.host.E) * e ∈ V
    rw [e1, mul_assoc]
    exact h

end GlobalTheory.CompanionTheory.SmallRatCell

end
