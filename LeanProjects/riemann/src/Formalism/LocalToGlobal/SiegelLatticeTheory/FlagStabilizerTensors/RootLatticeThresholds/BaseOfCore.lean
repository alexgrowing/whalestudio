import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants
open scoped ENNReal

namespace Formalism.L2.SG.Pf.BaseOf

variable {k r : ℕ}

theorem trG_closedEmb {n : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool) {Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ}
    {Qi : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ} (h2 : Q * Qi = 1) :
    Topology.IsClosedEmbedding (fun γ : Formalism.REAL.UJ ε => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG Q Qi γ) : Mt k r)) := by
  subst hn
  have h1 : Qi * Q = 1 := mul_eq_one_comm.mp h2
  obtain ⟨hemb, -⟩ := Formalism.REAL.isClosedEmbeddingMatrix (2 * r + k + 1) ε
  let L : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ ≃ₜ Mt k r :=
    { toFun := fun M => Matrix.of.symm (Qi * M * Q)
      invFun := fun M => Q * Matrix.of M * Qi
      left_inv := fun M => by
        show Q * Matrix.of (Matrix.of.symm (Qi * M * Q)) * Qi = M
        rw [Equiv.apply_symm_apply, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul,
          Matrix.mul_assoc, h2, Matrix.mul_one]
      right_inv := fun M => by
        show Matrix.of.symm (Qi * (Q * Matrix.of M * Qi) * Q) = M
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]
        rfl
      continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
      continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const }
  exact L.isClosedEmbedding.comp hemb

private theorem isUnit_det_of_mem_UH_Hpk {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) : IsUnit g.det := by
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  have hd := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul] at hd
  have hH : (Hpk k r).det ≠ 0 := (Formalism.FourierDecayAlt.P.B2x2.hpk_unit k r).ne_zero
  rw [isUnit_iff_ne_zero]
  intro h0
  rw [h0, mul_zero] at hd
  exact hH hd.symm

private theorem measurable_inv_apply (i j : Fin (2 * r + k + 1)) :
    Measurable fun x : Mt k r => (Matrix.of x)⁻¹ i j := by
  have e : (fun x : Mt k r => (Matrix.of x)⁻¹ i j) =
      fun x => (Matrix.of x).det⁻¹ * (Matrix.of x).adjugate i j := by
    funext x
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [e]
  have hc : Continuous fun x : Mt k r =>
      (Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := continuous_id
  exact hc.matrix_det.measurable.inv.mul (hc.matrix_adjugate.matrix_elem i j).measurable

theorem muS_swap {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    {μW : Measure (Mt k r)} (hW : Formalism.MainNotions.S.IsHaarOn (UWset k r z) μW) {μN : Measure (Mt k r)}
    (hNB : Formalism.FourierDecayAlt.B.IsHaarOn (Nset k r) μN) :
    (μN.prod μW).map (fun p => (Matrix.of.symm (Matrix.of p.1 * Matrix.of p.2) : Mt k r)) = Formalism.MainNotions.S.muS μW μN := by
  haveI : SigmaFinite μW := hW.1
  haveI : IsFiniteMeasureOnCompacts μN := ⟨fun K hK => hNB.finite_compact K hK⟩
  haveI : SigmaFinite μN := inferInstance
  have hconj := Formalism.FourierDecayAlt.P.b2_conjInvRaw_proof k r z μN hz hT hNB
  have hco : ∀ i j, Measurable fun p : Mt k r × Mt k r => p.1 i j :=
    fun i j => (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_fst)
  have hco2 : ∀ i j, Measurable fun p : Mt k r × Mt k r => p.2 i j :=
    fun i j => (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_snd)
  have hmul12 : Measurable fun p : Mt k r × Mt k r => (Matrix.of.symm (Matrix.of p.1 * Matrix.of p.2) : Mt k r) := by
    refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.of_symm_apply]
    exact Finset.measurable_sum _ fun l _ => (hco i l).mul (hco2 l j)
  have hmul21 : Measurable fun p : Mt k r × Mt k r => (Matrix.of.symm (Matrix.of p.2 * Matrix.of p.1) : Mt k r) := by
    refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.of_symm_apply]
    exact Finset.measurable_sum _ fun l _ => (hco2 i l).mul (hco l j)
  have hcm : Measurable (Function.uncurry fun (h n : Mt k r) => conjM (Matrix.of h) n) := by
    refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
    simp only [Function.uncurry, conjM, Matrix.mul_apply, Matrix.of_apply]
    exact Finset.measurable_sum _ fun l _ =>
      (Finset.measurable_sum _ fun m _ => (hco i m).mul (hco2 m l)).mul ((measurable_inv_apply l j).comp measurable_fst)
  have haeW : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r z := ae_iff.mpr hW.2.2.1
  have hsk : MeasurePreserving (fun p : Mt k r × Mt k r => (p.1, conjM (Matrix.of p.1) p.2))
      (μW.prod μN) (μW.prod μN) :=
    (MeasurePreserving.id μW).skew_product hcm (haeW.mono fun x hx => hconj _ hx)
  have hae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z := by
    rw [ae_iff]
    refine measure_mono_null (show {p : Mt k r × Mt k r | ¬ (Matrix.of p.1 ∈ UWset k r z)} ⊆
        {x : Mt k r | Matrix.of x ∉ UWset k r z} ×ˢ (Set.univ : Set (Mt k r)) from
      fun p hp => ⟨hp, Set.mem_univ _⟩) ?_
    rw [Measure.prod_prod, hW.2.2.1, zero_mul]
  calc (μN.prod μW).map (fun p => (Matrix.of.symm (Matrix.of p.1 * Matrix.of p.2) : Mt k r))
      = ((μW.prod μN).map Prod.swap).map (fun p => (Matrix.of.symm (Matrix.of p.1 * Matrix.of p.2) : Mt k r)) := by
        rw [Measure.prod_swap]
    _ = (μW.prod μN).map (fun p => (Matrix.of.symm (Matrix.of p.2 * Matrix.of p.1) : Mt k r)) := by
        rw [Measure.map_map hmul12 measurable_swap]
        rfl
    _ = ((μW.prod μN).map (fun p : Mt k r × Mt k r => (p.1, conjM (Matrix.of p.1) p.2))).map
          (fun p => (Matrix.of.symm (Matrix.of p.2 * Matrix.of p.1) : Mt k r)) := by
        rw [hsk.map_eq]
    _ = (μW.prod μN).map (fun p : Mt k r × Mt k r =>
          (Matrix.of.symm (Matrix.of (conjM (Matrix.of p.1) p.2) * Matrix.of p.1) : Mt k r)) := by
        rw [Measure.map_map hmul21 hsk.measurable]
        rfl
    _ = Formalism.MainNotions.S.muS μW μN := by
        unfold Formalism.MainNotions.S.muS
        refine Measure.map_congr (hae.mono fun p hp => ?_)
        have hu := isUnit_det_of_mem_UH_Hpk hp.1
        funext i j
        show ((Matrix.of p.1 * Matrix.of p.2 * (Matrix.of p.1)⁻¹) * Matrix.of p.1) i j =
          (Matrix.of p.1 * Matrix.of p.2) i j
        rw [Matrix.mul_assoc _ _ (Matrix.of p.1), Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]

theorem muS_loc {n : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool) {Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ}
    {Qi : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ} (h1 : Qi * Q = 1) (h2 : Q * Qi = 1)
    (hg : Qᴴ * Formalism.REAL.Jm ε * Q = Hpk k r) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    {μW : Measure (Mt k r)} (hW : Formalism.MainNotions.S.IsHaarOn (UWset k r z) μW) (hW1 : μW Set.univ = 1)
    {μN : Measure (Mt k r)} (hNB : Formalism.FourierDecayAlt.B.IsHaarOn (Nset k r) μN) :
    ∃ μS : Measure (Formalism.REAL.UJ ε),
      Formalism.L2.SG.RealObj.IsHaarLoc {γ | Formalism.L2.SG.RealObj.trG Q Qi γ ∈ Sset k r z} μS ∧
      μS.map (fun γ => Matrix.of.symm (Formalism.L2.SG.RealObj.trG Q Qi γ)) =
        (μN.prod μW).map (fun p => Matrix.of.symm (Matrix.of p.1 * Matrix.of p.2)) := by
  have hSμ := Formalism.L2.SG.Pf.Choice.isHaarOn_muS_gen hz hT hW hW1 hNB
  rw [muS_swap hz hT hW hNB]
  subst hn
  have h1' : Qi * Q = 1 := mul_eq_one_comm.mp h2
  obtain ⟨T, hTdef⟩ : ∃ T : Formalism.REAL.UJ ε → Mt k r,
      T = fun γ => Matrix.of.symm (Formalism.L2.SG.RealObj.trG Q Qi γ) := ⟨_, rfl⟩
  have hemb : MeasurableEmbedding T := by
    rw [hTdef]
    exact (trG_closedEmb rfl ε h2).measurableEmbedding
  have hJ : Qiᴴ * Hpk k r * Qi = Formalism.REAL.Jm ε := by
    rw [← hg]
    calc Qiᴴ * (Qᴴ * Formalism.REAL.Jm ε * Q) * Qi = (Q * Qi)ᴴ * Formalism.REAL.Jm ε * (Q * Qi) := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [h2, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hUHrange : ∀ M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, M ∈ UH (Hpk k r) →
      ∃ γ : Formalism.REAL.UJ ε, Formalism.L2.SG.RealObj.trG Q Qi γ = M := by
    intro M hM
    have hMd := isUnit_det_of_mem_UH_Hpk hM
    have hQd : IsUnit (Q.det * Qi.det) := by
      rw [← Matrix.det_mul, h2, Matrix.det_one]
      exact isUnit_one
    have hu : IsUnit (Q * M * Qi) := by
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul, Matrix.det_mul]
      have e : Q.det * M.det * Qi.det = (Q.det * Qi.det) * M.det := by ring
      rw [e]
      exact hQd.mul hMd
    have hmem : hu.unit ∈ Formalism.REAL.UJ ε := by
      show Formalism.REAL.inUJ ε ((hu.unit : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))
      rw [IsUnit.unit_spec]
      unfold Formalism.REAL.inUJ
      have hM' : Mᴴ * Hpk k r * M = Hpk k r := hM
      calc (Q * M * Qi)ᴴ * Formalism.REAL.Jm ε * (Q * M * Qi)
          = Qiᴴ * (Mᴴ * (Qᴴ * Formalism.REAL.Jm ε * Q) * M) * Qi := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = Formalism.REAL.Jm ε := by rw [hg, hM', hJ]
    refine ⟨⟨hu.unit, hmem⟩, ?_⟩
    show Qi * ((hu.unit : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) * Q = M
    rw [IsUnit.unit_spec]
    simp only [Matrix.mul_assoc]
    rw [h1', Matrix.mul_one, ← Matrix.mul_assoc, h1', Matrix.one_mul]
  have hrange : ∀ᵐ x ∂(Formalism.MainNotions.S.muS μW μN), x ∈ Set.range T := by
    have h0 : ∀ᵐ x ∂(Formalism.MainNotions.S.muS μW μN), Matrix.of x ∈ Sset k r z := ae_iff.mpr hSμ.2.2.1
    refine h0.mono fun x hx => ?_
    obtain ⟨h, hh, m, hm, hx'⟩ := hx
    have hUH : Matrix.of x ∈ UH (Hpk k r) := by
      rw [hx']
      show (h * m)ᴴ * Hpk k r * (h * m) = Hpk k r
      have hh' : hᴴ * Hpk k r * h = Hpk k r := hh.1
      have hm' : mᴴ * Hpk k r * m = Hpk k r := hm.1
      calc (h * m)ᴴ * Hpk k r * (h * m) = mᴴ * (hᴴ * Hpk k r * h) * m := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = Hpk k r := by rw [hh', hm']
    obtain ⟨γ, hγ⟩ := hUHrange _ hUH
    exact ⟨γ, by rw [hTdef]; exact hγ⟩
  have hmap : (Measure.comap T (Formalism.MainNotions.S.muS μW μN)).map T = Formalism.MainNotions.S.muS μW μN := by
    rw [hemb.map_comap, Measure.restrict_eq_self_of_ae_mem hrange]
  have hmulT : ∀ s x : Formalism.REAL.UJ ε,
      T (s * x) = lmulM (Formalism.L2.SG.RealObj.trG Q Qi s) (T x) := by
    intro s x
    rw [hTdef]
    show (Qi * (((s * x : Formalism.REAL.UJ ε) : (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ˣ) :
        Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) * Q) =
      (Qi * ((s : (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ˣ) :
        Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) * Q) *
      (Qi * ((x : (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ˣ) :
        Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) * Q)
    rw [Subgroup.coe_mul, Units.val_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q Qi, h2, Matrix.one_mul]
  have hTm : Measurable T := hemb.measurable
  refine ⟨Measure.comap T (Formalism.MainNotions.S.muS μW μN), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact SigmaFinite.of_map _ hTm.aemeasurable (by rw [hmap]; exact hSμ.1)
  · intro h0
    apply hSμ.2.1
    rw [← hmap, h0, Measure.map_zero]
  · rw [hemb.comap_apply]
    refine measure_mono_null ?_ hSμ.2.2.1
    rintro _ ⟨γ, hγ, rfl⟩
    rw [hTdef]
    exact hγ
  · intro s hs
    have hLm : Measurable (lmulM (Formalism.L2.SG.RealObj.trG Q Qi s) : Mt k r → Mt k r) := by
      refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
      simp only [lmulM, Matrix.mul_apply, Matrix.of_apply]
      exact Finset.measurable_sum _ fun l _ => measurable_const.mul ((measurable_pi_apply j).comp (measurable_pi_apply l))
    have hsm : Measurable fun x : Formalism.REAL.UJ ε => s * x := measurable_const_mul s
    have e1 : ((Measure.comap T (Formalism.MainNotions.S.muS μW μN)).map (fun x => s * x)).map T =
        (Measure.comap T (Formalism.MainNotions.S.muS μW μN)).map T := by
      rw [Measure.map_map hTm hsm]
      have hc : T ∘ (fun x => s * x) = lmulM (Formalism.L2.SG.RealObj.trG Q Qi s) ∘ T := funext (hmulT s)
      rw [hc, ← Measure.map_map hLm hTm, hmap, hSμ.2.2.2 _ hs]
    calc (Measure.comap T (Formalism.MainNotions.S.muS μW μN)).map (fun x => s * x)
        = Measure.comap T (((Measure.comap T (Formalism.MainNotions.S.muS μW μN)).map (fun x => s * x)).map T) :=
          (hemb.comap_map _).symm
      _ = Measure.comap T ((Measure.comap T (Formalism.MainNotions.S.muS μW μN)).map T) := by rw [e1]
      _ = Measure.comap T (Formalism.MainNotions.S.muS μW μN) := hemb.comap_map _
  · subst hTdef
    exact hmap

theorem haarG_B {n : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool) {Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ}
    {Qi : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ} (h2 : Q * Qi = 1) (hg : Qᴴ * Formalism.REAL.Jm ε * Q = Hpk k r) :
    Formalism.FourierDecayAlt.B.IsHaarOn (Formalism.FourierDecayAlt.B.GV k r)
      ((Formalism.REAL.muG ε).map (fun γ => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG Q Qi γ) : Mt k r))) := by
  have hSK := Formalism.L2.SG.Pf.Choice.haar_tr hn ε Q Qi h2 hg
  have hce := trG_closedEmb hn ε h2
  obtain ⟨hz, hT1⟩ := Formalism.FourierDecayAlt.P.base_vector_exists k r
  have hT0 : 0 < Tz k r (bvec (wI k r (Fin.last k))) := by rw [hT1]; exact one_pos
  have hright := (quotient_measure_unitary_group k r _ hz hT0).2.2.2.1 _ hSK
  obtain ⟨hsf, hne, hcon, hleft⟩ := hSK
  refine ⟨hcon, hleft, hright, fun K hK => ?_, hne⟩
  rw [Measure.map_apply hce.measurable hK.isClosed.measurableSet]
  exact (hce.isCompact_preimage hK).measure_lt_top

theorem sec_exists (hk : 1 ≤ k) (z z' : Fin (2 * r + k + 1) → ℂ) (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    (hf : ∃ g, Formalism.MainNotions.S.IsFrameW k r z g) (hf' : ∃ g, Formalism.MainNotions.S.IsFrameW k r z' g) :
    ∃ μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, IsSection k r z z' μsec := by
  obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 := ⟨k - 1, by omega⟩
  exact Formalism.MainNotions.S.Inh.big_cell_section_exists k0 r z z' hT hT' hf hf'

open Formalism.BasicNotions in
theorem k_pos (D : D7) : 1 ≤ D.R.k := by
  have h := D.R.m_add_three_le_k
  omega

end Formalism.L2.SG.Pf.BaseOf
