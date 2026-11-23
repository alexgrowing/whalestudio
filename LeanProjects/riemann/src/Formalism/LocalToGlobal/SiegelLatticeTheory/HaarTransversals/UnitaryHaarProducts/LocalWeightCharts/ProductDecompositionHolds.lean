import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.HaarWN
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.SubgroupHypothesisHolds

noncomputable section

open MeasureTheory Matrix Topology
open scoped ENNReal NNReal Pointwise

namespace WlocSk.HM

open Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

def jinv (g : Mx k r) : Mx k r := Hpk k r * gᴴ * Hpk k r

lemma jinv_mul {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : jinv g * g = 1 := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  unfold jinv
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
    _ = Hpk k r * Hpk k r := by rw [hg']
    _ = 1 := Formalism.QuantumDeterminants.GBasic.Hpk_sq k r

lemma mul_jinv {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : g * jinv g = 1 := mul_eq_one_comm.mp (jinv_mul hg)

lemma jinv_eq {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : g⁻¹ = jinv g := Matrix.inv_eq_left_inv (jinv_mul hg)

lemma jinv_cont : Continuous (fun g : Mx k r => jinv g) :=
  (continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const

lemma lmul_meas (a : Mx k r) : Measurable (lmulM (k := k) (r := r) a) := by
  have hc : Continuous (lmulM (k := k) (r := r) a) := by
    unfold Formalism.QuantumDeterminants.lmulM
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Matrix.mul_apply, Matrix.of_apply]
    exact continuous_finset_sum _ fun l _ => by fun_prop
  exact hc.measurable

lemma mulP_meas : Measurable (mulP : Mt k r × Mt k r → Mt k r) := by
  have hc : Continuous (mulP : Mt k r × Mt k r → Mt k r) := by
    unfold WlocSk.mulP
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Matrix.mul_apply, Matrix.of_apply]
    exact continuous_finset_sum _ fun l _ => by fun_prop
  exact hc.measurable

theorem s_closed (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hT : 0 < Tz k r z) :
    IsClosed (Sset k r z : Set (Mx k r)) := by
  have hE : IsClosedEmbedding (Grp.val : Grp (UH (Hpk k r) : Set (Mx k r)) uh_clsub → Mx k r) := Grp.emb
  let A : Set (Grp (UH (Hpk k r) : Set (Mx k r)) uh_clsub) := Grp.val ⁻¹' (UWset k r z : Set (Mx k r))
  let B : Set (Grp (UH (Hpk k r) : Set (Mx k r)) uh_clsub) := Grp.val ⁻¹' (Nset k r : Set (Mx k r))
  have hA : IsCompact A := hE.isCompact_preimage (compactW z hz hT)
  have hB : IsClosed B := n_closed.preimage hE.continuous
  have hAB : IsClosed (A * B) := hB.mul_left_of_isCompact hA
  have himg : Grp.val '' (A * B) = (Sset k r z : Set (Mx k r)) := by
    ext s
    constructor
    · rintro ⟨x, ⟨a, ha, b, hb, rfl⟩, rfl⟩
      exact ⟨a.val, ha, b.val, hb, rfl⟩
    · rintro ⟨h, hh, m, hm, rfl⟩
      exact ⟨Grp.mk h hh.1 * Grp.mk m hm.1, ⟨Grp.mk h hh.1, hh, Grp.mk m hm.1, hm, rfl⟩, rfl⟩
  rw [← himg]
  exact hE.isClosedMap _ hAB

theorem s_clsub (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hconj : ∀ h ∈ UWset k r z, ∀ m ∈ Nset k r, h⁻¹ * m * h ∈ Nset k r) :
    ClSub (Sset k r z : Set (Mx k r)) := by
  have hW := uw_clsub (k := k) (r := r) z
  have hN := n_clsub (k := k) (r := r)
  refine ⟨⟨1, hW.one_mem, 1, hN.one_mem, (Matrix.mul_one 1).symm⟩, ?_, ?_, ?_, s_closed z hz hT⟩
  · rintro _ ⟨h, hh, m, hm, rfl⟩ _ ⟨h', hh', m', hm', rfl⟩
    refine ⟨h * h', hW.mul_mem _ hh _ hh', h'⁻¹ * m * h' * m', hN.mul_mem _ (hconj h' hh' m hm) _ hm', ?_⟩
    have e : h' * h'⁻¹ = 1 := Matrix.mul_nonsing_inv h' (hW.unit h' hh')
    calc h * m * (h' * m') = h * (h' * h'⁻¹) * m * h' * m' := by
          rw [e]; simp only [Matrix.mul_assoc, Matrix.mul_one]
      _ = h * h' * (h'⁻¹ * m * h' * m') := by simp only [Matrix.mul_assoc]
  · rintro _ ⟨h, hh, m, hm, rfl⟩
    have hi := hW.inv_mem h hh
    have hu := hW.unit h hh
    refine ⟨h⁻¹, hi, h * m⁻¹ * h⁻¹, ?_, ?_⟩
    · have := hconj h⁻¹ hi m⁻¹ (hN.inv_mem m hm)
      rwa [Matrix.nonsing_inv_nonsing_inv h hu] at this
    · rw [Matrix.mul_inv_rev]
      calc m⁻¹ * h⁻¹ = (h⁻¹ * h) * m⁻¹ * h⁻¹ := by rw [Matrix.nonsing_inv_mul h hu, Matrix.one_mul]
        _ = h⁻¹ * (h * m⁻¹ * h⁻¹) := by simp only [Matrix.mul_assoc]
  · rintro _ ⟨h, hh, m, hm, rfl⟩
    rw [Matrix.det_mul]
    exact (hW.unit h hh).mul (hN.unit m hm)

theorem prod_haar (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hconj : ∀ h ∈ UWset k r z, ∀ m ∈ Nset k r, h⁻¹ * m * h ∈ Nset k r)
    (μW μN : Measure (Mt k r)) (hW : IsHaarOn (UWset k r z) μW) (hN : IsHaarOn (Nset k r) μN)
    [IsFiniteMeasure μW] (hNc : ∀ K : Set (Mt k r), IsCompact K → μN K < ⊤) :
    IsHaarOn (Sset k r z) ((μW.prod μN).map mulP) := by
  obtain ⟨hσW, hW0, hWc, hWl⟩ := hW
  obtain ⟨hσN, hN0, hNcc, hNl⟩ := hN
  have hSc := s_clsub z hz hT hconj
  have hm := mulP_meas (k := k) (r := r)
  have aeW : ∀ᵐ p ∂(μW.prod μN), (Matrix.of p.1 : Mx k r) ∈ UWset k r z := by
    rw [ae_iff]
    have : {p : Mt k r × Mt k r | ¬ (Matrix.of p.1 : Mx k r) ∈ UWset k r z} =
        {x : Mt k r | Matrix.of x ∉ UWset k r z} ×ˢ Set.univ := by
      ext p; exact ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩
    rw [this, Measure.prod_prod, hWc, zero_mul]
  have aeN : ∀ᵐ p ∂(μW.prod μN), (Matrix.of p.2 : Mx k r) ∈ Nset k r := by
    rw [ae_iff]
    have : {p : Mt k r × Mt k r | ¬ (Matrix.of p.2 : Mx k r) ∈ Nset k r} =
        Set.univ ×ˢ {x : Mt k r | Matrix.of x ∉ Nset k r} := by
      ext p; exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
    rw [this, Measure.prod_prod, hNcc, mul_zero]

  have hUWc : @IsCompact (Mt k r) _ (UWset k r z) := compactW z hz hT
  have hfc : ∀ K : Set (Mt k r), IsCompact K → ((μW.prod μN).map mulP) K < ⊤ := by
    intro K hK
    let f : Mt k r × Mt k r → Mt k r := fun q => (jinv (Matrix.of q.1) * Matrix.of q.2 : Mx k r)
    have hf : Continuous f := (jinv_cont.comp continuous_fst).matrix_mul continuous_snd
    have hK' : IsCompact (f '' ((UWset k r z : Set (Mt k r)) ×ˢ K)) := (hUWc.prod hK).image hf
    have hsub : (mulP ⁻¹' K : Set (Mt k r × Mt k r)) ≤ᵐ[μW.prod μN]
        (Set.univ ×ˢ (f '' ((UWset k r z : Set (Mt k r)) ×ˢ K))) := by
      filter_upwards [aeW] with p h1 hp
      refine ⟨trivial, ⟨(p.1, mulP p), ⟨h1, hp⟩, ?_⟩⟩
      show jinv (Matrix.of p.1) * (Matrix.of p.1 * Matrix.of p.2) = Matrix.of p.2
      rw [← Matrix.mul_assoc, jinv_mul h1.1, Matrix.one_mul]
    rw [Measure.map_apply hm hK.isClosed.measurableSet]
    refine lt_of_le_of_lt (measure_mono_ae hsub) ?_
    rw [Measure.prod_prod]
    exact ENNReal.mul_lt_top (measure_lt_top μW _) (hNc _ hK')

  have hρ0 : (μW.prod μN).map mulP ≠ 0 := by
    intro h0
    have h1 := congrArg (fun ν : Measure (Mt k r) => ν Set.univ) h0
    simp only [Measure.map_apply hm MeasurableSet.univ, Measure.coe_zero, Pi.zero_apply] at h1
    rw [Set.preimage_univ, ← Set.univ_prod_univ, Measure.prod_prod, mul_eq_zero] at h1
    rcases h1 with h | h
    · exact hW0 (Measure.measure_univ_eq_zero.mp h)
    · exact hN0 (Measure.measure_univ_eq_zero.mp h)

  have hSm : MeasurableSet {x : Mt k r | Matrix.of x ∉ Sset k r z} :=
    (show @IsClosed (Mt k r) _ (Sset k r z) from hSc.closed).measurableSet.compl
  have hconc : ((μW.prod μN).map mulP) {x : Mt k r | Matrix.of x ∉ Sset k r z} = 0 := by
    rw [Measure.map_apply hm hSm]
    have hae : ∀ᵐ p ∂(μW.prod μN), ¬ (p ∈ mulP ⁻¹' {x : Mt k r | Matrix.of x ∉ Sset k r z}) := by
      filter_upwards [aeW, aeN] with p h1 h2
      intro hp
      exact hp ⟨Matrix.of p.1, h1, Matrix.of p.2, h2, rfl⟩
    exact measure_mono_null (fun p hp => not_not_intro hp) (ae_iff.mp hae)

  have leftW : ∀ h₀ ∈ UWset k r z, ((μW.prod μN).map mulP).map (lmulM h₀) = (μW.prod μN).map mulP := by
    intro h₀ hh₀
    rw [Measure.map_map (lmul_meas h₀) hm]
    have e : (lmulM h₀ ∘ mulP : Mt k r × Mt k r → Mt k r) = mulP ∘ Prod.map (lmulM h₀) id := by
      funext p
      exact (Matrix.mul_assoc h₀ (Matrix.of p.1) (Matrix.of p.2)).symm
    rw [e, ← Measure.map_map hm ((lmul_meas h₀).prodMap measurable_id),
      ← Measure.map_prod_map _ _ (lmul_meas h₀) measurable_id, hWl h₀ hh₀, Measure.map_id]

  have leftN : ∀ m₀ ∈ Nset k r, ((μW.prod μN).map mulP).map (lmulM m₀) = (μW.prod μN).map mulP := by
    intro m₀ hm₀
    rw [Measure.map_map (lmul_meas m₀) hm]
    let g : Mt k r → Mt k r → Mt k r := fun h m => lmulM (jinv (Matrix.of h) * m₀ * Matrix.of h) m
    have hgm : Measurable (Function.uncurry g) := by
      have : Continuous (Function.uncurry g) := by
        show Continuous fun q : Mt k r × Mt k r =>
          ((jinv (Matrix.of q.1) * m₀ * Matrix.of q.1) * Matrix.of q.2 : Mx k r)
        exact (((jinv_cont.comp continuous_fst).matrix_mul continuous_const).matrix_mul
          continuous_fst).matrix_mul continuous_snd
      exact this.measurable
    have hg : ∀ᵐ h ∂μW, μN.map (g h) = μN := by
      rw [ae_iff]
      refine measure_mono_null (fun h hh => ?_) hWc
      intro hin
      apply hh
      have hc : jinv (Matrix.of h) * m₀ * Matrix.of h ∈ Nset k r := by
        rw [← jinv_eq hin.1]; exact hconj _ hin _ hm₀
      exact hNl _ hc
    have hT := MeasurePreserving.skew_product (MeasurePreserving.id μW) hgm hg
    have hae : (lmulM m₀ ∘ mulP : Mt k r × Mt k r → Mt k r) =ᵐ[μW.prod μN]
        mulP ∘ (fun p : Mt k r × Mt k r => (id p.1, g p.1 p.2)) := by
      filter_upwards [aeW] with p h1
      show m₀ * (Matrix.of p.1 * Matrix.of p.2) =
        Matrix.of p.1 * ((jinv (Matrix.of p.1) * m₀ * Matrix.of p.1) * Matrix.of p.2)
      have e := mul_jinv h1.1
      calc m₀ * (Matrix.of p.1 * Matrix.of p.2)
          = (Matrix.of p.1 * jinv (Matrix.of p.1)) * m₀ * Matrix.of p.1 * Matrix.of p.2 := by
            rw [e, Matrix.one_mul, Matrix.mul_assoc]
        _ = Matrix.of p.1 * ((jinv (Matrix.of p.1) * m₀ * Matrix.of p.1) * Matrix.of p.2) := by
            simp only [Matrix.mul_assoc]
    rw [Measure.map_congr hae, ← Measure.map_map hm hT.measurable, hT.map_eq]
  refine ⟨sigma_of_compact _ hfc, hρ0, hconc, ?_⟩
  rintro _ ⟨h₀, hh₀, m₀, hm₀, rfl⟩
  have e : (lmulM (h₀ * m₀) : Mt k r → Mt k r) = lmulM h₀ ∘ lmulM m₀ := by
    funext x; exact Matrix.mul_assoc h₀ m₀ (Matrix.of x)
  rw [e, ← Measure.map_map (lmul_meas h₀) (lmul_meas m₀), leftN m₀ hm₀, leftW h₀ hh₀]

theorem sprod_main (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hconj : ∀ h ∈ UWset k r z, ∀ m ∈ Nset k r, h⁻¹ * m * h ∈ Nset k r)
    (μW μN μS : Measure (Mt k r)) (hW : IsHaarOn (UWset k r z) μW) (hN : IsHaarOn (Nset k r) μN)
    [IsFiniteMeasure μW] (hNc : ∀ K : Set (Mt k r), IsCompact K → μN K < ⊤) (hS : IsHaarOn (Sset k r z) μS) :
    ∃ cS : ℝ≥0∞, cS ≠ 0 ∧ cS ≠ ⊤ ∧ (μW.prod μN).map mulP = cS • μS := by
  have hSc := s_clsub z hz hT hconj
  obtain ⟨c1, h10, h1t, e1⟩ := haar_unique _ hSc _ (prod_haar z hz hT hconj μW μN hW hN hNc)
  obtain ⟨c2, h20, h2t, e2⟩ := haar_unique _ hSc _ hS
  refine ⟨c1 / c2, (ENNReal.div_pos_iff.mpr ⟨h10, h2t⟩).ne', ENNReal.div_ne_top h1t h20, ?_⟩
  rw [e1, e2, smul_smul, ENNReal.div_mul_cancel h20 h2t]

end WlocSk.HM

namespace WlocSk

theorem sProd_of (hG : SGrp) : SProd := by
  intro k r z c u v b H _ _ _ σ Vp _ _ _ π w μG μS ν μW μN hyp
  obtain ⟨hset, -, -, -, -, hS, -, hW, hN, hWf, hNc⟩ := hyp
  obtain ⟨-, -, hz, hT, -⟩ := hset
  have hconj := (hG k r z c hz hT).2.2.2.2
  exact HM.sprod_main z hz hT (fun h hh m hm => (hconj h hh m hm).1) μW μN μS hW hN hNc hS

theorem product_decomposition_holds : SProd := sProd_of subgroup_hypothesis_holds

end WlocSk
