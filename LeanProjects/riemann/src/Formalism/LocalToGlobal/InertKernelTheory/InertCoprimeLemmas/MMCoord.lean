import Formalism.LocalToGlobal.InertKernelTheory.DefsMMCoord
import Formalism.LocalToGlobal.InertKernelTheory.DefsMM
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.PowerSeriesEmbedding
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntTens
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2

noncomputable section

namespace Formalism.L2.KerInert

namespace MMCoord

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

def inclCL (D : D7) : (D.what₂.Tau → ℂ) →L[ℂ] VC D 1 1 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v τ _ _ => v τ, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

theorem inclCL_apply (v : D.what₂.Tau → ℂ) : inclCL D v = fun τ _ _ => v τ := rfl

theorem translate_theta_coordinates (B : Base D cc δ) (s₁ v : D.what₂.Tau → ℂ) :
    U D B.tor (fun τ _ _ => s₁ τ) (B.thZero 1 1) (fun τ _ _ => v τ) =
      Formalism.L2.Th1.H.opU (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau)) s₁ B.thMM v := by
  have hA : Formalism.MainNotions.TaylorLogMetric.area (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ) = Formalism.L2.Th1.F.area B.L := B.areaOK
  have hT : B.tor.abelian₂ = Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ := rfl
  simp only [U, Formalism.MainNotions.TaylorLogMetric.Hf, Base.thZero, tensPow, Formalism.L2.Th1.H.opU, Formalism.L2.Th1.H.matH, LinearMap.mk₂'ₛₗ_apply, hOne,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.univ_unique, Finset.sum_singleton,
    Finset.prod_singleton, hT, hA]
  congr 1
  have e1 : ∀ w : D.what₂.Tau → ℂ, ∑ x, w x * ((Formalism.L2.Th1.F.area B.L : ℝ) : ℂ)⁻¹ * (starRingEnd ℂ) (s₁ x) =
      (∑ x, w x * (starRingEnd ℂ) (s₁ x)) / ((Formalism.L2.Th1.F.area B.L : ℝ) : ℂ) := fun w => by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [e1, e1]

theorem u_incl (B : Base D cc δ) (s : VC D 1 1) (v : D.what₂.Tau → ℂ) :
    U D B.tor s (B.thZero 1 1) (inclCL D v) =
      Formalism.L2.Th1.H.opU (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau)) (fun τ => s τ 0 0) B.thMM v := by
  have hs : s = fun τ _ _ => s τ 0 0 := by
    funext τ i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  have h := translate_theta_coordinates B (fun τ => s τ 0 0) v
  rw [← hs] at h
  exact h

def projM (D : D7) : Matrix D.what₂.Tau (D.what₂.Tau × Fin 1 × Fin 1) ℂ :=
  Matrix.of fun τ k => if k = (τ, 0, 0) then 1 else 0

theorem projM_mulVec (w : D.what₂.Tau × Fin 1 × Fin 1 → ℂ) : (projM D).mulVec w = fun τ => w (τ, 0, 0) := by
  funext τ
  simp [projM, Matrix.mulVec, dotProduct, ite_mul, Finset.sum_ite_eq']

theorem flat_eq (w : D.what₂.Tau × Fin 1 × Fin 1 → ℂ) :
    Formalism.L2.AlgTh.flat D.what₂.Tau 1 1 w = inclCL D ((projM D).mulVec w) := by
  rw [projM_mulVec, inclCL_apply]
  funext τ i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  rfl

theorem linSubst_projM (T : MvPowerSeries D.what₂.Tau ℂ) :
    Formalism.L2.Th1.H.linSubst (projM D) T =
      MvPowerSeries.subst (fun τ : D.what₂.Tau =>
        (MvPowerSeries.X (τ, 0, 0) : MvPowerSeries (D.what₂.Tau × Fin 1 × Fin 1) ℂ)) T := by
  unfold Formalism.L2.Th1.H.linSubst
  congr 1
  funext τ
  simp [projM, apply_ite MvPowerSeries.C, ite_mul, Finset.sum_ite_eq']

theorem map_subst_liftT {p : ℕ} [Fact p.Prime] (h : ℂ →+* ℂ_[p]) (T : MvPowerSeries D.what₂.Tau ℂ) :
    MvPowerSeries.map h (MvPowerSeries.subst (fun τ : D.what₂.Tau =>
        (MvPowerSeries.X (τ, 0, 0) : MvPowerSeries (D.what₂.Tau × Fin 1 × Fin 1) ℂ)) T) =
      liftT D (MvPowerSeries.map h T) := by
  have ha : MvPowerSeries.HasSubst (fun τ : D.what₂.Tau =>
      (MvPowerSeries.X (τ, 0, 0) : MvPowerSeries (D.what₂.Tau × Fin 1 × Fin 1) ℂ)) :=
    MvPowerSeries.HasSubst.X_comp (fun τ : D.what₂.Tau => ((τ, 0, 0) : D.what₂.Tau × Fin 1 × Fin 1))
  rw [MvPowerSeries.map_subst ha]
  unfold liftT
  congr 1
  funext τ
  simp [MvPowerSeries.map_X]

end MMCoord

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical MMCoord

theorem coordinates_one_theta_algebraic : CoordTieA := by
  intro D cc δ B _ _ p _ lam ι hι s
  refine ⟨fun hG => ?_, fun hs => ?_⟩
  · have hgG : Formalism.L2.Th1.H.opU (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau)) (fun τ => s τ 0 0) B.thMM =
        fun v => U D B.tor s (B.thZero 1 1) (inclCL D v) := funext fun v => (u_incl B s v).symm
    have hg0 : AnalyticAt ℂ
        (Formalism.L2.Th1.H.opU (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau)) (fun τ => s τ 0 0) B.thMM) 0 := by
      rw [hgG]
      exact (hG.1 _ trivial).comp ((inclCL D).analyticAt 0)
    have hfun : (fun z => U D B.tor s (B.thZero 1 1) (Formalism.L2.AlgTh.flat D.what₂.Tau 1 1 z)) =
        fun w => Formalism.L2.Th1.H.opU (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau)) (fun τ => s τ 0 0) B.thMM
          ((projM D).mulVec w) := by
      funext w
      rw [flat_eq, hgG]
    rw [power_series_embedding D 1 1 p lam ι hι _ hG.2, IntTens.taylorSer_eq_taylorMv _ hG.1, hfun,
      Formalism.L2.Th1.H.taylorMvComp _ _ (projM D) _ hg0, linSubst_projM]
    exact map_subst_liftT ι.toRingHom _
  · obtain ⟨n, hn, hcop, hmem⟩ := hs
    have h0 := B.lat0OK 1 1
    unfold Base.Lat0OK at h0
    rw [h0] at hmem
    refine ⟨n, hn, fun hd => ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mp hcop.symm) hd, ?_⟩
    have h00 : (fun τ => (n • s) τ 0 0) ∈ B.lamM := hmem 0 0
    convert h00 using 1
    funext τ
    simp [nsmul_eq_mul]

theorem coordTie_of (h : CoordTieA) (hz : AlgZero) : CoordTie := by
  intro D cc δ B hcc hδ p _ hp hin lam ι hι s hs
  obtain ⟨h1, h2⟩ := h D cc δ B hcc hδ p lam ι hι s
  exact ⟨h1 (hz D cc δ B hcc hδ p hp hin 1 1 s hs), h2 hs⟩

theorem coordTie_of_algZero (hz : AlgZero) : CoordTie := coordTie_of coordinates_one_theta_algebraic hz

end Formalism.L2.KerInert
