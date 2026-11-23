import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.PCDesc
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.OrbitDerivatives.EtaleClosedPointLiftsSimpleRootsMonic
import Development.WeilBound.HeckeVectors.SmoothVectors.SobolevApproximation.SobApproxHolds
import Formalism.LocalToGlobal.IndefiniteReal.SmExpSmulContDiff

open Matrix Topology
open scoped ComplexOrder

noncomputable section

namespace CompanionTheory.D.gk.HC

open Formalism.BasicNotions.TH (GrpData URep GKMod)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section UJ

variable {n : ℕ} (ε : Fin n → Bool)

theorem ujInvC {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.MainNotions.S.UJset ε) :
    (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) * g = 1 := by
  have hg' : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', Formalism.REAL.Jm_mul_self]

theorem isMatGroupC : PI.IsMatGroup (Formalism.MainNotions.S.UJset ε) := by
  refine ⟨?_, ?_, fun a ha b hb => ?_, fun a ha => ?_⟩
  · exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
  · show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε * 1 = Formalism.REAL.Jm ε; simp
  · have ha' : aᴴ * Formalism.REAL.Jm ε * a = Formalism.REAL.Jm ε := ha
    have hb' : bᴴ * Formalism.REAL.Jm ε * b = Formalism.REAL.Jm ε := hb
    show (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = Formalism.REAL.Jm ε
    calc (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = bᴴ * (aᴴ * Formalism.REAL.Jm ε * a) * b := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [ha', hb']
  · have h1 := ujInvC ε ha
    have h2 : a * a⁻¹ = 1 := by rw [Matrix.inv_eq_left_inv h1]; exact mul_eq_one_comm.1 h1
    refine ⟨?_, h2⟩
    have ha' : aᴴ * Formalism.REAL.Jm ε * a = Formalism.REAL.Jm ε := ha
    show (a⁻¹)ᴴ * Formalism.REAL.Jm ε * a⁻¹ = Formalism.REAL.Jm ε
    calc (a⁻¹)ᴴ * Formalism.REAL.Jm ε * a⁻¹ = (a⁻¹)ᴴ * (aᴴ * Formalism.REAL.Jm ε * a) * a⁻¹ := by rw [ha']
      _ = (a * a⁻¹)ᴴ * Formalism.REAL.Jm ε * (a * a⁻¹) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h2, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

def thetaC : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => Formalism.REAL.Jm ε * xᴴ * Formalism.REAL.Jm ε
      map_add' := fun a b => by rw [conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c a => by
        rw [conjTranspose_smul, star_trivial, Matrix.mul_smul, Matrix.smul_mul]; rfl }

theorem thetaC_eq {x : Matrix (Fin n) (Fin n) ℂ} (hx : x ∈ Formalism.MainNotions.S.UJset ε) : thetaC ε x = x⁻¹ :=
  (Matrix.inv_eq_left_inv (ujInvC ε hx)).symm

variable {ε} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem repOnC (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) : CompanionTheory.D.Upq.Sm.RepOn (Formalism.MainNotions.S.UJset ε) σ :=
  ⟨(isMatGroupC ε).2.1, (isMatGroupC ε).2.2.1, hσ.1.1, hσ.1.2⟩

theorem smoothVec_of_isSmC {w : H} (hw : CompanionTheory.D.Upq.Sm.IsSm (Formalism.MainNotions.S.UJset ε) σ w) :
    Formalism.L2.Theta.SmoothVec (Formalism.IndefR.Tow.SobPf.lieG (Formalism.REAL.Jm ε)) σ w := by
  intro m Xs hX
  have hc := Formalism.IndefR.PeterssonHilbertSpace.sm_prod_exp_contDiff m Xs
  have hmem : ∀ t : Fin m → ℝ, (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod ∈ Formalism.MainNotions.S.UJset ε :=
    fun t => Formalism.IndefR.PeterssonHilbertSpace.sm_prod_exp_mem _ m Xs (fun i => hX i) t
  rw [contDiff_iff_contDiffAt]
  intro t0
  obtain ⟨U, F, hU, h0, hF, hEq⟩ := hw _ (hmem t0)
  have hev : (fun t : Fin m → ℝ => σ ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod) w)
      =ᶠ[𝓝 t0] fun t => F ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod) := by
    filter_upwards [hc.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds h0)] with t ht
    exact hEq _ ht (hmem t)
  exact ((hF.contDiffAt (hU.mem_nhds h0)).comp t0 hc.contDiffAt).congr_of_eventuallyEq hev

theorem kfinDense_UJC (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) : Dense {v : H | Formalism.MainNotions.S.IsKFin ε σ v} := by
  have hsm := CompanionTheory.D.gk.FinalFormK.dense_sm' (isMatGroupC ε) (thetaC ε) (fun x hx => thetaC_eq ε hx) (repOnC hσ) hσ.2.2
  have hG : Formalism.IndefR.Tow.SobPf.IsGRep (Formalism.REAL.Jm ε) σ := ⟨hσ.1.1, hσ.1.2, hσ.2.1, hσ.2.2⟩
  have hC : Formalism.IndefR.Datum.IsCartanInv (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε) := by
    have hJ : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
      ext i j; simp only [Formalism.REAL.Jm, diagonal_conjTranspose, diagonal_apply]; split_ifs <;> simp_all
    refine ⟨Formalism.REAL.Jm_mul_self ε, ?_, ?_⟩
    · rw [hJ, Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one]
    · rw [Formalism.REAL.Jm_mul_self]; exact Matrix.PosDef.one
  rw [Metric.dense_iff]
  intro h δ hδ
  obtain ⟨w, hw, hwh⟩ := Metric.dense_iff.1 hsm h (δ / 2) (half_pos hδ)
  obtain ⟨v, -, hvK, hvw⟩ := CompanionTheory.D.gk.HC.sobApprox_holds (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε) σ hC hG w
    (smoothVec_of_isSmC hwh) [[]] (by simp) (δ / 2) (half_pos hδ)
  refine ⟨v, ?_, ?_⟩
  · have h1 := hvw [] (by simp)
    simp only [Formalism.IndefR.Tow.SobPf.dL, List.foldr_nil] at h1
    rw [Metric.mem_ball] at hw ⊢
    calc dist v h ≤ dist v w + dist w h := dist_triangle _ _ _
      _ < δ / 2 + δ / 2 := add_lt_add (by rw [dist_eq_norm]; exact h1) hw
      _ = δ := add_halves δ
  · obtain ⟨W, hW, hvW, hst⟩ := hvK
    refine ⟨W, hW, hvW, fun g hg x hx => hst g ⟨?_, hg.2⟩ x hx⟩
    show gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε
    rw [Matrix.mul_assoc, ← hg.2, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose,
      (Matrix.mem_unitaryGroup_iff').1 hg.1, Matrix.one_mul]

end UJ

end CompanionTheory.D.gk.HC
