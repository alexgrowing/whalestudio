import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.AeProductMemUnipotentAndNilradical
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.RepresentationUnitary

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace WlocSk.PtD

open WlocSk Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.CayleySignature

theorem representation_continuous : PiCont := by
  intro k r z u Vp _ _ π hz hT hπ ξ
  obtain ⟨g, hg, hπU⟩ := hπ
  obtain ⟨hgU, hgfix, hgz⟩ := hg
  obtain ⟨-, -, ⟨-, -, hcont⟩, -⟩ := hπU
  have hgi := WlocSk.UnitaryRepLocal.uh_inv hgU
  have hfixg : ∀ a ∈ UWset k r z, ∀ l, ¬ WlocSk.UnitaryRepLocal.inB k r l →
      a *ᵥ (g *ᵥ bvec l) = g *ᵥ bvec l := by
    intro a ha l hl
    unfold WlocSk.UnitaryRepLocal.inB at hl
    by_cases h1 : l.val < r
    · have hl' : l = eI k r ⟨l.val, h1⟩ := Fin.ext rfl
      rw [hl', (hgfix ⟨l.val, h1⟩).1, (ha.2.1 ⟨l.val, h1⟩).1]
    · by_cases h2 : r + k < l.val
      · have hl' : l = esI k r ⟨2 * r + k - l.val, by omega⟩ := by apply Fin.ext; simp [esI]; omega
        rw [hl', (hgfix _).2, (ha.2.1 _).2]
      · have hl' : l = wI k r (Fin.last k) := by apply Fin.ext; simp [wI]; omega
        have hs : ((Real.sqrt (Tz k r z) : ℝ) : ℂ) ≠ 0 := by
          have := Real.sqrt_pos.mpr hT; exact_mod_cast this.ne'
        obtain ⟨t, ht⟩ : ∃ t : ℂ, t = ((Real.sqrt (Tz k r z) : ℝ) : ℂ) := ⟨_, rfl⟩
        rw [← ht] at hgz hs
        have hgw : g *ᵥ bvec (wI k r (Fin.last k)) = t⁻¹ • z := by
          calc g *ᵥ bvec (wI k r (Fin.last k)) = t⁻¹ • (t • g *ᵥ bvec (wI k r (Fin.last k))) := by
                rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
            _ = t⁻¹ • z := by rw [← Matrix.mulVec_smul, hgz]
        rw [hl', hgw, Matrix.mulVec_smul, ha.2.2]
  have hstruct : ∀ a ∈ UWset k r z, WlocSk.UnitaryRepLocal.ub (g⁻¹ * a * g) ∈ UJset (allPos k) ∧
      a = g * blockW k r (WlocSk.UnitaryRepLocal.ub (g⁻¹ * a * g)) * g⁻¹ := by
    intro a ha
    have hc : g⁻¹ * a * g ∈ UH (Hpk k r) :=
      WlocSk.UnitaryRepLocal.uh_mul (WlocSk.UnitaryRepLocal.uh_mul hgi.2.2 ha.1) hgU
    have hb : g⁻¹ * a * g = blockW k r (WlocSk.UnitaryRepLocal.ub (g⁻¹ * a * g)) := by
      refine WlocSk.UnitaryRepLocal.eq_blockW hc fun l hl => ?_
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hfixg a ha l hl, Matrix.mulVec_mulVec,
        hgi.2.1, Matrix.one_mulVec]
    refine ⟨WlocSk.UnitaryRepLocal.ub_unitary hc hb, ?_⟩
    rw [← hb]
    calc a = (g * g⁻¹) * a * (g * g⁻¹) := by rw [hgi.1, Matrix.one_mul, Matrix.mul_one]
      _ = g * (g⁻¹ * a * g) * g⁻¹ := by simp only [Matrix.mul_assoc]
  have hmul : Continuous fun a : Mat k r => g⁻¹ * a * g :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have hubc : Continuous fun a : Mat k r => WlocSk.UnitaryRepLocal.ub (g⁻¹ * a * g) := by
    unfold WlocSk.UnitaryRepLocal.ub
    exact continuous_pi fun m => continuous_pi fun m' =>
      (continuous_apply _).comp ((continuous_apply _).comp hmul)
  refine ((hcont ξ).comp hubc.continuousOn (fun a ha => (hstruct a ha).1)).congr (fun a ha => ?_)
  show π a ξ = π (g * blockW k r (WlocSk.UnitaryRepLocal.ub (g⁻¹ * a * g)) * g⁻¹) ξ
  rw [← (hstruct a ha).2]

theorem wave_packet_integrable (hSG : SigmaG) (hD : Decay) (hRG : ReprodG) (hS : SGrp) (hPi : PiUnit)
    (hNI : NIntDecay) (hU : UWComp) : AInt :=
  aInt_of hSG hD hRG hS hPi hNI hU representation_continuous

theorem wave_packet_continuous (hSG : SigmaG) (hD : Decay) (hRG : ReprodG) (hS : SGrp) (hPi : PiUnit)
    (hNI : NIntDecay) (hU : UWComp) : ACont :=
  aCont_of hSG hD hRG hS hPi hNI hU representation_continuous

end WlocSk.PtD
