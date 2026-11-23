import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnGeomCut
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.GramSchmidtFramesLocal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.LocBCore
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.XiHermitianCofactorDet
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.HmSelfRe

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom

open Formalism.QuantumDeterminants PI.UnitaryGroupMassFormula.GsFr
open scoped Matrix

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace S1

variable {k r : ℕ}

lemma smooth_hermitian_rank_two {s : Set (B.Mat k r)} {p q : B.Mat k r → Fin (2 * r + k + 1) → ℂ}
    (hp : Sm p s) (hq : Sm q s) : Sm (fun x => Rk k r (p x) (q x)) s := by
  unfold Sm Rk at *
  refine contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j => ?_
  simp only [Matrix.vecMulVec_apply, Matrix.vecMul, dotProduct, Pi.star_apply]
  have hs : ∀ l, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => star (q x l)) s := fun l => by
    have h := Complex.conjCLE.contDiff.comp_contDiffOn (contDiffOn_pi.mp hq l)
    simpa [Function.comp_def] using h
  exact (contDiffOn_pi.mp hp i).mul (ContDiffOn.sum fun l _ => (hs l).mul contDiffOn_const)

lemma s_unitH {s : Set (B.Mat k r)} {v : B.Mat k r → Fin (2 * r + k + 1) → ℂ} (hv : Sm v s)
    (hp : ∀ x ∈ s, 0 < (Formalism.QuantumDeterminants.herm (Hpk k r) (v x) (v x)).re) : Sm (fun x => unitH k r (v x)) s := by
  unfold Sm unitH Formalism.QuantumDeterminants.herm at *
  have hvi : ∀ i, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => v x i) s := fun i => contDiffOn_pi.mp hv i
  have hsi : ∀ i, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => star (v x i)) s := fun i => by
    have h := Complex.conjCLE.contDiff.comp_contDiffOn (hvi i)
    simpa [Function.comp_def] using h
  have hh : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => star (v x) ⬝ᵥ Hpk k r *ᵥ v x) s := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
    exact ContDiffOn.sum fun i _ => (hsi i).mul (ContDiffOn.sum fun j _ => contDiffOn_const.mul (hvi j))
  have hre : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (star (v x) ⬝ᵥ Hpk k r *ᵥ v x).re) s := by
    have h := Complex.reCLM.contDiff.comp_contDiffOn hh
    simpa [Function.comp_def] using h
  have hsq := hre.sqrt fun x hx => (hp x hx).ne'
  have hinv := hsq.inv fun x hx => (Real.sqrt_pos.mpr (hp x hx)).ne'
  have hc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => (((Real.sqrt (star (v x) ⬝ᵥ Hpk k r *ᵥ v x).re)⁻¹ : ℝ) : ℂ)) s := by
    have h := Complex.ofRealCLM.contDiff.comp_contDiffOn hinv
    simpa [Function.comp_def] using h
  exact hc.smul hv

end S1

open S1 in
theorem geometry_smoothness_holds : GeomSmooth := by
  intro k r z z' _hk hz hz'
  let fd : B.Mat k r → ℂ := fun g => (Zhat k r z z' g).det
  let f1 : B.Mat k r → ℝ := fun g =>
    (Formalism.QuantumDeterminants.herm (Hpk k r) (omW k r z z' g) (omW k r z z' g)).re
  let f2 : B.Mat k r → ℝ := fun g =>
    (Formalism.QuantumDeterminants.herm (Hpk k r) (omS k r z z' g) (omS k r z z' g)).re
  have hid : Sm (fun g : B.Mat k r => g) Set.univ := contDiffOn_id
  have cd : Continuous fd := (contDiffOn_univ.1 (s_det (s_Zhat z z' hid))).continuous
  have c1 : Continuous f1 :=
    (contDiffOn_univ.1 (s_re (s_herm _ (s_omW z z' hid) (s_omW z z' hid)))).continuous
  have c2 : Continuous f2 :=
    (contDiffOn_univ.1 (s_re (s_herm _ (s_omS (s := Set.univ) z z') (s_omS z z')))).continuous
  let U : Set (B.Mat k r) := (fd ⁻¹' {0}ᶜ ∩ {g | 0 < f1 g}) ∩ {g | 0 < f2 g}
  have hU : IsOpen U :=
    ((isOpen_compl_singleton.preimage cd).inter (isOpen_lt continuous_const c1)).inter
      (isOpen_lt continuous_const c2)
  have hmem : ∀ g ∈ posG k r z z', g ∈ U := by
    intro g hg
    obtain ⟨hgV, hG⟩ := hg
    refine ⟨⟨det_ne_of_G hz hz' hG, ?_⟩, ?_⟩
    · have hm : omW k r z z' g ∈ Wsp k r z := prW_mem hz _
      exact posV hz hm.1 hm.2 (omW_ne hz hz' hgV hG)
    · have hm : omS k r z z' g ∈ Wsp k r z' := prW_mem hz' _
      have hω : omS k r z z' g ≠ 0 := by rw [← omS_eq z z' hgV]; exact omW'_ne hz hz' hgV hG
      exact posV hz' hm.1 hm.2 hω
  have sU : Sm (fun g : B.Mat k r => g) U := contDiffOn_id
  have hd0 : ∀ g ∈ U, (Zhat k r z z' g).det ≠ 0 := fun g hg => hg.1.1
  have hnu : Sm (fun g => nuG z z' g) U := s_unitH (s_omW z z' sU) fun g hg => hg.1.2
  have hnuS : Sm (fun g => unitH k r (omS k r z z' g)) U := s_unitH (s_omS z z') fun g hg => hg.2
  have hdi : Sm (fun g => -((Zhat k r z z' g).det)⁻¹) U := ((s_det (s_Zhat z z' sU)).inv hd0).neg
  have hL : Sm (fun g => Lm k r z z' g) U := by
    unfold Lm
    exact contDiffOn_const.add (ContDiffOn.sum fun c _ => ContDiffOn.sum fun a _ =>
      s_msmul (hdi.mul (s_adj (s_Zhat z z' sU) c a)) (s_mmul contDiffOn_const sU))
  have hP : Sm (fun g => Phi k r z z' g) U := by
    unfold Phi
    exact s_mmul (s_mmul contDiffOn_const sU) hL
  have hio : Sm (fun g => Phi k r z z' g *
      (Pm k r z' - Rk k r (unitH k r (omS k r z z' g)) (unitH k r (omS k r z z' g)) * Pm k r z')) U :=
    s_mmul hP (contDiffOn_const.sub (s_mmul (smooth_hermitian_rank_two hnuS hnuS) contDiffOn_const))
  refine ⟨fun g₀ hg₀ => ⟨U, fun g => nuG z z' g, hU, hmem g₀ hg₀, hnu, fun g _ _ => rfl⟩,
    fun g₀ hg₀ => ⟨U, fun g => unitH k r (omS k r z z' g), hU, hmem g₀ hg₀, hnuS, fun g _ hgV => ?_⟩,
    fun g₀ hg₀ => ⟨U, _, hU, hmem g₀ hg₀, hio, fun g _ hgV => ?_⟩⟩
  · show unitH k r (omW' k r z z' g) = _
    rw [omS_eq z z' hgV]
  · show Phi k r z z' g * (Pm k r z' - Rk k r (unitH k r (omW' k r z z' g)) (unitH k r (omW' k r z z' g)) *
      Pm k r z') = _
    rw [omS_eq z z' hgV]

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom
