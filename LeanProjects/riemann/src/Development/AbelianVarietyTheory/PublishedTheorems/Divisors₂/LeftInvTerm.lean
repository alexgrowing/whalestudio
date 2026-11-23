import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilSiegelFormula
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.FirstClauseRankZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HypsSatisfiable
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ShiftedAdditiveCharacterArchimedeanParameters
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SiegelSchwartz.Model

open GlobalTheory.StdUnn

variable {D : D7} {n : ℕ}

theorem hyps_hold (D : D7) (n : ℕ) (V : HSp D) :
    ∃ (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D) (μ : Measure (Mx D V.rank n))
      (𝓕 : Set (Mx D V.rank n)) (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (ν : Measure (GA D V))
      (Φ : schwartzA θ V.rank n), IsCharAF D.host.F ψ ∧ IsHeckeChar D χ ∧ ResEta D χ V.rank ∧ IsInfFam θ ∧
        IsCovolOne (ratMx D V.rank n) μ 𝓕 ∧ IsWeilSch ψ χ θ V μ ω ∧ ν.IsHaarMeasure ∧ Φ.1 0 ≠ 0 := by
  obtain ⟨ν, ψ, χ, omh, -, -, -, hν, hω, -, -, -⟩ :=
    GlobalTheory.SiegelFormula.Model.data_exist GlobalTheory.weilRepresentationUnitaryPair V V
  obtain ⟨θ, hθ⟩ := hω.std.2.1
  have hxi : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  obtain ⟨lam, hlam, hψ, -⟩ := shift_char_realPar D ψ hω.std θ hθ D.host.xi0 ⟨hxi, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg D⟩
  have hl : lam ≠ 0 := fun h => by
    rw [h, map_zero] at hlam
    exact div_ne_zero (neg_ne_zero.2 hxi) hxi hlam.symm
  obtain ⟨μ, 𝓕, hμ⟩ := GlobalTheory.MixModel.exists_isCovolOne D V.rank n
  obtain ⟨ω, hW⟩ := Inhab.weil_exists D n V ψ hω.std lam hl χ hω.hecT hω.resT θ hθ μ 𝓕 hμ
  have hc : ∀ τ, ∃ s, IsCartanInv (gramAt D V τ) s := fun τ =>
    GlobalTheory.Mem.ThetaNonzero.exists_isCartanInv (GlobalTheory.SmoothForms.RealPts.gramAt_herm V τ)
      (GlobalTheory.SmoothForms.RealPts.gramAt_unit V τ)
  choose s hs using hc
  obtain ⟨U, h1, h2, h3⟩ := Inhab.hyps_satisfiable.2.2.2.2 D V.rank n
  obtain ⟨Φ, -, -, hΦ⟩ := Inhab.hyps_satisfiable.2.2.2.1 D n V θ (fun _ => 1) (fun _ => one_ne_zero) s hs U h1 h2 h3
  exact ⟨_, χ, θ, μ, 𝓕, ω, ν, Φ, hψ, hω.hecT, hω.resT, hθ, hμ, hW, hν, hΦ⟩

theorem range_met (D : D7) : (∃ V : HSp D, 2 * 1 < V.rank ∧ Formalism.MainNotions.SchurIrreducible.wittIdx V = 0) ∧
    ∃ V : HSp D, 2 * 1 < V.rank ∧ 0 < Formalism.MainNotions.SchurIrreducible.wittIdx V :=
  ⟨⟨GlobalTheory.SiegelFormula.Model.pos D 3, show 2 * 1 < 3 by decide, GlobalTheory.SiegelFormula.Model.wittIdx_pos 3⟩,
    ⟨dblSp (GlobalTheory.SiegelFormula.Model.pos D 2), show 2 * 1 < 2 + 2 by decide, by
      rw [GlobalTheory.SiegelFormula.Model.wittIdx_dblSp]; exact show 0 < 2 by decide⟩⟩

theorem leftInv_term {V : HSp D} {ψ χ θ μ} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hχ : IsHeckeChar D χ)
    (hω : IsWeilSch ψ χ θ V μ ω) (Φ : schwartzA θ V.rank n) : LeftInv (P D n ⊓ GF D n) fun γ => (ω γ Φ).1 0 := by
  intro γ hγ g
  obtain ⟨hp, hr⟩ := Subgroup.mem_inf.1 hγ
  obtain ⟨a, ha⟩ := LeftInvSect.exists_blkA hp
  obtain ⟨u, hu⟩ := LeftInvSect.det_rat hr a ha
  have h1 : absA D (Matrix.GeneralLinearGroup.det a) = 1 := by
    rw [hu]; exact absE_inclR u
  have h2 : χ (Matrix.GeneralLinearGroup.det a) = 1 := by
    rw [hu]; exact hχ.2 u
  obtain ⟨m, v, b, e, hm, hv⟩ := LeftInvSect.exists_levi_unip hp a ha
  have e' : ω (γ * g) Φ = ω m (ω v (ω g Φ)) := by
    rw [e, map_mul, map_mul]; rfl
  have z1 : ∀ a : Mx D n n, ((0 : Mx D V.rank n) ⬝ a : Mx D V.rank n) = 0 := fun a => Matrix.zero_mul a
  have z2 : StdUnn.inner V (0 : Mx D V.rank n) 0 = 0 := by rw [StdUnn.inner, adj_zero, Matrix.zero_mul]
  show (ω (γ * g) Φ).1 0 = (ω g Φ).1 0
  rw [e', hω.levi m _ hm, h1, h2, z1, hω.unip v b hv, z2]
  simp [halfTr, npow]

theorem term_one {V : HSp D} {ψ χ θ μ} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hχ : IsHeckeChar D χ)
    (hω : IsWeilSch ψ χ θ V μ ω) (Φ : schwartzA θ V.rank n) :
    Eis.term (P D n) (GF D n) (fun γ => (ω γ Φ).1 0) 1 (mk _ 1) = Φ.1 0 := by
  rw [Eis.term_mk (leftInv_term hχ hω Φ)]
  simp

theorem leftInv_sum (V : HSp D) (φ : Mx D V.rank n → ℂ) : LeftInv (GQ V) fun h =>
    ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, φ (GlobalTheory.SiegelFormula.invPt V h ξ) := by
  intro γ hγ h
  obtain ⟨δ, -, hδ⟩ : ∃ δ : GL (Fin V.rank) D.host.E, _ ∧ Formalism.UG.bc (incA D) δ = Formalism.L2.Theta.matHom V γ⁻¹ := inv_mem hγ
  let e : Matrix (Fin V.rank) (Fin n) D.host.E ≃ Matrix (Fin V.rank) (Fin n) D.host.E :=
    ⟨fun ξ => δ.1 * ξ, fun ξ => δ⁻¹.1 * ξ, fun ξ => by simp, fun ξ => by simp⟩
  have h1 : Formalism.L2.Theta.mt V γ⁻¹ = δ.1.map (incA D) := (congrArg Units.val hδ).symm
  have h2 : Formalism.L2.Theta.mt V (γ * h)⁻¹ = Formalism.L2.Theta.mt V h⁻¹ * Formalism.L2.Theta.mt V γ⁻¹ := by rw [mul_inv_rev]; rfl
  refine (tsum_congr fun ξ => ?_).trans (e.tsum_eq fun ξ => φ (GlobalTheory.SiegelFormula.invPt V h ξ))
  simp only [GlobalTheory.SiegelFormula.invPt, e, Equiv.coe_fn_mk, h2, h1, Matrix.mul_assoc, Matrix.map_mul]

theorem inner_mt (V : HSp D) (h : GA D V) (x y : Mx D V.rank n) :
    StdUnn.inner V (Formalism.L2.Theta.mt V h ⬝ x) (Formalism.L2.Theta.mt V h ⬝ y) = StdUnn.inner V x y := by
  unfold StdUnn.inner
  rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA V), ← Matrix.mul_assoc (adj (Formalism.L2.Theta.mt V h)), mt_unitary]

theorem vol_ne (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] :
    autMeasure V ν Set.univ ≠ 0 ∧ autMeasure V ν Set.univ ≠ ⊤ := ⟨NeZero.ne _, measure_ne_top _ _⟩

theorem rhs_eq {V : HSp D} {θ} (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (ν : Measure (GA D V))
    (Φ : schwartzA θ V.rank n) : (⨍ q, AutomorphicL2Unitary.descend (GQ V) (fun h => ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
        Φ.1 (GlobalTheory.SiegelFormula.invPt V h ξ)) q ∂autMeasure V ν) = thetaInt ω ν Φ 1 := by
  unfold thetaInt theta
  rw [map_one]
  rfl

theorem at_point (H : GlobalTheory.Published.WeilSiegelFormula) {V : HSp D} (hn : 1 ≤ n) (hm : 2 * n < V.rank) {ψ χ θ μ 𝓕}
    (hψ : IsCharAF D.host.F ψ) (hχ : IsHeckeChar D χ) (hr : ResEta D χ V.rank) (hθ : IsInfFam θ)
    (hμ : IsCovolOne (ratMx D V.rank n) μ 𝓕) {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)}
    (hω : IsWeilSch ψ χ θ V μ ω) (ν : Measure (GA D V)) (hν : ν.IsHaarMeasure) (Φ : schwartzA θ V.rank n) (g : G D n) :
    Eis.cosetSum (P D n) (GF D n) (fun γ => (ω γ Φ).1 0) g = thetaInt ω ν Φ g := by
  have h := H D n V hn hm ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω ν hν (ω g Φ)
  refine Eq.trans ?_ h
  simp only [Eis.cosetSum, Eis.term, mul_one, map_mul, Module.End.mul_apply]

end GlobalTheory.SiegelSchwartz.Model

end
