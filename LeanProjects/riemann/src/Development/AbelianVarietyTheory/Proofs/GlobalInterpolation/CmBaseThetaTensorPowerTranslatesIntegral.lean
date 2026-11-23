import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.StdOK
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmThetaBaseVectorTranslatesIntegralStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeJetsAreBoundedMomentsProdAndSumStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeJetsAreBoundedMomentsPullbackStatement

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.MomN

theorem contDiff_opU_of_analytic {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (H : Formalism.L2.Th1.H.Sesq V) (x : V) {F : V → ℂ} (hF : AnalyticOnNhd ℂ F Set.univ) :
    ContDiff ℂ ⊤ (Formalism.L2.Th1.H.opU H x F) := by
  have h1 : ContDiff ℂ ⊤ F := contDiffOn_univ.1 (hF.contDiffOn uniqueDiffOn_univ)
  let f : V →ₗ[ℂ] ℂ :=
    { toFun := fun z => H z x
      map_add' := fun a b => by simp
      map_smul' := fun c a => by simp }
  have hl : ContDiff ℂ ⊤ (fun z => H z x) := (LinearMap.toContinuousLinearMap f).contDiff
  have h2 : ContDiff ℂ ⊤ (fun z => F (z + x)) := h1.comp (contDiff_id.add contDiff_const)
  have h3 : ContDiff ℂ ⊤ (fun z => Complex.exp (-(Real.pi : ℂ) * H z x - (Real.pi : ℂ) * H x x / 2)) :=
    ((contDiff_const.mul hl).sub contDiff_const).cexp
  exact h2.mul h3

theorem latInt_U_thZero : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]) (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]), Per D.host.d ι δ₀ θ Ω → ∀ (N N' : ℕ) (s : VC D N N'), TorsPrime D q (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) s → LatInt ι (Ω / ι δ₀) (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (U D B.tor s (B.thZero N N')) := by
  intro D cc δ B hcc hδ q _ hq2 hsplit hcop ι δ₀ θ Ω hP N N' s hs
  have hS := B.stdOK hcc hδ
  have han : AnalyticOnNhd ℂ B.thMM Set.univ := (B.thMM_spec hS).1.1
  have hLat : La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') = powLat B.lamM N N' := B.lat0OK N N'
  have hA : area (lamOf D cc δ) = Formalism.L2.Th1.F.area B.L := B.areaOK
  set G : Fin N' → Fin N → (D.what₂.Tau → ℂ) → ℂ := fun i j =>
    Formalism.L2.Th1.H.opU (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau)) (fun τ => s τ i j) B.thMM with hG
  have hU : U D B.tor s (B.thZero N N') = fun z => ∏ i, ∏ j, G i j (entry D.what₂.Tau N N' i j z) := by
    funext z
    rw [U_eq]
    show Formalism.L2.Th1.H.opU (formV (area (lamOf D cc δ)) D.what₂.Tau N N') s (tensPow B.thMM N N') z = _
    rw [hA, opU_tensPow]
    rfl
  have hGc : ∀ i j, ContDiff ℂ ⊤ (G i j) := fun i j => contDiff_opU_of_analytic _ _ han
  have hEc : ∀ i j, ContDiff ℂ ⊤ (fun z : VC D N N' => G i j (entry D.what₂.Tau N N' i j z)) :=
    fun i j => (hGc i j).comp (entry D.what₂.Tau N N' i j).contDiff
  obtain ⟨n, -, hnq, hns⟩ := hs
  rw [hLat] at hns
  have hF : ∀ i j, LatInt ι (Ω / ι δ₀) (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))
      (fun z => G i j (entry D.what₂.Tau N N' i j z)) := by
    intro i j
    have hm : LatInt ι (Ω / ι δ₀) B.lamM (G i j) := by
      refine GlobalTheory.T.cmTheta_baseVector_translates_integral D cc δ B hcc hδ q hq2 hsplit hcop ι δ₀ θ Ω hP (fun τ => s τ i j) n hnq ?_
      have := hns i j
      convert this using 1
      funext τ
      simp [nsmul_eq_mul]
    refine GlobalTheory.T.latticeJetsAreBoundedMoments_pullback q ι (D.what₂.Tau → ℂ) (VC D N N') (Ω / ι δ₀) B.lamM
      (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (entry D.what₂.Tau N N' i j) (G i j) (hGc i j) ?_ hm
    intro x hx
    rw [hLat] at hx
    exact ⟨1, Nat.coprime_one_left q, by rw [one_smul]; exact hx i j⟩
  rw [hU]
  refine (GlobalTheory.T.latticeJetsAreBoundedMoments_prod_and_sum q ι (VC D N N') (Ω / ι δ₀) (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))).1 (Fin N')
    (fun i z => ∏ j, G i j (entry D.what₂.Tau N N' i j z)) (fun i => ?_) (fun i => ?_)
  · exact contDiff_prod fun j _ => hEc i j
  · exact (GlobalTheory.T.latticeJetsAreBoundedMoments_prod_and_sum q ι (VC D N N') (Ω / ι δ₀) (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))).1 (Fin N)
      (fun j z => G i j (entry D.what₂.Tau N N' i j z)) (hEc i) (hF i)

end GlobalTheory.MomN
