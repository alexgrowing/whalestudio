import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinCovariance
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSumInvariantWeylInvolution
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousHalfTr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockMatrixInjective

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.EisCovar PositivityTheory.GramSchwartzFunctions.EC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTw

variable {D : D7} {n ρ p : ℕ} {hn : ρ + p = n}

theorem adj_B (b₀ : HermE D ρ) : adj (b₀.1.map (incA D)) = b₀.1.map (incA D) := by
  have h : b₀.1ᴴ = b₀.1 := b₀.2
  have := rat_conjTranspose (D := D) b₀.1
  rw [h] at this
  exact this.symm

theorem pr_def (b₀ : HermE D ρ) (u v : Mx D ρ p) : pr b₀ u v = adj u ⬝ (b₀.1.map (incA D) ⬝ v) := rfl

theorem pr_add_left (b₀ : HermE D ρ) (u u' v : Mx D ρ p) : pr b₀ (u + u') v = pr b₀ u v + pr b₀ u' v := by
  simp only [pr_def, adj_add, Matrix.add_mul]

theorem pr_add_right (b₀ : HermE D ρ) (u v v' : Mx D ρ p) : pr b₀ u (v + v') = pr b₀ u v + pr b₀ u v' := by
  simp only [pr_def, Matrix.mul_add]

theorem pr_neg_left (b₀ : HermE D ρ) (u v : Mx D ρ p) : pr b₀ (-u) v = -pr b₀ u v := by
  simp only [pr_def, adj_neg, Matrix.neg_mul]

theorem pr_neg_right (b₀ : HermE D ρ) (u v : Mx D ρ p) : pr b₀ u (-v) = -pr b₀ u v := by
  simp only [pr_def, Matrix.mul_neg]

theorem adj_pr (b₀ : HermE D ρ) (u v : Mx D ρ p) : adj (pr b₀ u v) = pr b₀ v u := by
  simp only [pr_def, adj_mul, adj_adj, adj_B, Matrix.mul_assoc]

theorem trace_pr_swap (b₀ : HermE D ρ) (u v : Mx D ρ p) :
    Matrix.trace (pr b₀ v u) = cA D (Matrix.trace (pr b₀ u v)) := by
  rw [← trace_adj, adj_pr]

theorem trA_pr_comm (b₀ : HermE D ρ) (u v : Mx D ρ p) :
    trA (Matrix.trace (pr b₀ v u)) = trA (Matrix.trace (pr b₀ u v)) := by
  rw [trace_pr_swap, trA, GlobalTheory.DualPairCheck.trace_cA]

theorem trace_mul_pr (b₀ : HermE D ρ) (b : Mx D p p) (u v : Mx D ρ p) :
    Matrix.trace (pr b₀ u (v ⬝ b)) = Matrix.trace (b ⬝ pr b₀ u v) := by
  have : pr b₀ u (v ⬝ b) = pr b₀ u v ⬝ b := by simp only [pr_def, Matrix.mul_assoc]
  rw [this, Matrix.trace_mul_comm]

theorem trace_swap_pr (b₀ : HermE D ρ) {b : Mx D p p} (hb : adj b = b) (u v : Mx D ρ p) :
    Matrix.trace (b ⬝ pr b₀ v u) = cA D (Matrix.trace (b ⬝ pr b₀ u v)) := by
  rw [← trace_adj, adj_mul, hb, adj_pr, Matrix.trace_mul_comm]

theorem halfTr_add'' (a c : AE D) : halfTr (a + c) = halfTr a + halfTr c := by
  simp only [halfTr, trA, map_add, mul_add]

theorem halfTr_neg'' (a : AE D) : halfTr (-a) = -halfTr a := by
  simp only [halfTr, trA, map_neg, mul_neg]

theorem quad_shift_pr (b₀ : HermE D ρ) {b : Mx D p p} (hb : adj b = b) (u v : Mx D ρ p) :
    halfTr (Matrix.trace (b ⬝ pr b₀ (u + v) (u + v))) =
      halfTr (Matrix.trace (b ⬝ pr b₀ u u)) + trA (Matrix.trace (pr b₀ u (v ⬝ b))) +
        halfTr (Matrix.trace (pr b₀ v (v ⬝ b))) := by
  rw [pr_add_left, pr_add_right, pr_add_right, Matrix.mul_add, Matrix.mul_add, Matrix.mul_add, Matrix.trace_add,
    Matrix.trace_add, Matrix.trace_add, halfTr_add'', halfTr_add'', halfTr_add'', trace_swap_pr b₀ hb u v,
    trace_mul_pr, trace_mul_pr, ← Unip.halfTr_add_cA (Matrix.trace (b ⬝ pr b₀ u v))]
  abel

theorem psi_halfTr_rat {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (e : D.host.E) :
    ψ (halfTr (incA D e)) = 1 := by
  rw [GlobalTheory.CompanionTheory.HermPoisson.halfTr_incA']
  exact hψ.2.2.1 _

theorem chz_add (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (z : hermA D ρ) (w : Mx D ρ ρ) (h : z.1 + w ∈ hermA D ρ) :
    chz ψ b₀ ⟨z.1 + w, h⟩ = chz ψ b₀ z * ψ (halfTr (Matrix.trace (b₀.1.map (incA D) ⬝ w))) := by
  simp only [chz]
  rw [Matrix.mul_add, Matrix.trace_add, halfTr_add'', AddChar.map_add_eq_mul]

theorem trace_rat {k : ℕ} (N : Matrix (Fin k) (Fin k) D.host.E) :
    Matrix.trace (rat N : Mx D k k) = incA D (Matrix.trace N) := by
  simp only [Matrix.trace, Matrix.diag, rat, Matrix.map_apply]
  exact (map_sum (incA D) _ _).symm

theorem character_phase_identity {A : Type} [AddCommGroup A] (ψ : AddChar A ℂ) (a c q u : A) (hq : ψ q = 1) :
    ψ (a - c) * ψ (q + c + u) = ψ u * ψ a := by
  rw [← AddChar.map_add_eq_mul, show a - c + (q + c + u) = q + (u + a) by abel, AddChar.map_add_eq_mul, hq, one_mul,
    AddChar.map_add_eq_mul]

theorem trA_pr_sub (b₀ : HermE D ρ) (x w X : Mx D ρ p) :
    trA (Matrix.trace (pr b₀ (x - w) X)) = trA (Matrix.trace (pr b₀ x X)) - trA (Matrix.trace (pr b₀ X w)) := by
  rw [sub_eq_add_neg, pr_add_left, pr_neg_left, Matrix.trace_add, Matrix.trace_neg, Weyl.trA_add, Weyl.trA_neg,
    sub_eq_add_neg, trA_pr_comm b₀ X w]

theorem term_unip {ψ : AddChar (AF D.host.F) ℂ} {b₀ : HermE D ρ}
    {χ : (AE D)ˣ →* Circle} {θ : InfFam D} {μ : Measure (Mx D ρ p)} {Ω : G D p → Mx D ρ p → ℂ}
    (hΩ : IsTh ψ χ θ b₀ μ Ω) (g : G D p) {b : Mx D p p} (hb : adj b = b)
    (hg : mat g = blk4 1 b 0 1) (h : G D p) (x y X : Mx D ρ p)
    (hq : ψ (halfTr (Matrix.trace (b ⬝ pr b₀ X X))) = 1) :
    ψ (trA (Matrix.trace (pr b₀ (x - y ⬝ b) X))) * Ω (g * h) (X + y) =
      ψ (halfTr (Matrix.trace (pr b₀ y (y ⬝ b)))) * (ψ (trA (Matrix.trace (pr b₀ x X))) * Ω h (X + y)) := by
  rw [hΩ.unip g b hg h, quad_shift_pr b₀ hb, trA_pr_sub, ← mul_assoc, character_phase_identity ψ _ _ _ _ hq, mul_assoc]

theorem rat_quad (b₀ : HermE D ρ) (b : Matrix (Fin p) (Fin p) D.host.E) (ξ : Matrix (Fin ρ) (Fin p) D.host.E) :
    Matrix.trace (rat b ⬝ pr b₀ (rat ξ) (rat ξ) : Mx D p p) = incA D (Matrix.trace (b * (ξᴴ * (b₀.1 * ξ)))) := by
  have e : rat b ⬝ pr b₀ (rat ξ) (rat ξ) = (rat (b * (ξᴴ * (b₀.1 * ξ))) : Mx D p p) := by
    rw [rat_mul, rat_mul, rat_mul, rat_conjTranspose]
    rfl
  rw [e, trace_rat]

theorem th_unip {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {b₀ : HermE D ρ}
    {χ : (AE D)ˣ →* Circle} {θ : InfFam D} {μ : Measure (Mx D ρ p)} {Ω : G D p → Mx D ρ p → ℂ}
    (hΩ : IsTh ψ χ θ b₀ μ Ω) (g : G D p) (b : Matrix (Fin p) (Fin p) D.host.E) (hb : adj (rat b : Mx D p p) = rat b)
    (hg : mat g = blk4 1 (rat b) 0 1) (h : G D p) (z : hermA D ρ) (x y : Mx D ρ p) :
    th ψ b₀ (Ω h) z x y = th ψ b₀ (Ω (g * h)) (zU z y (rat b) hb) (x - y ⬝ rat b) y := by
  set u := halfTr (Matrix.trace (pr b₀ y (y ⬝ rat b))) with hu
  have hz : chz ψ b₀ (zU z y (rat b) hb) = chz ψ b₀ z * ψ (-u) := by
    have e : (zU z y (rat b) hb : hermA D ρ) = ⟨z.1 + -(y ⬝ (rat b ⬝ adj y)), by
      have := (zU z y (rat b) hb).2
      simpa [zU, sub_eq_add_neg] using this⟩ := Subtype.ext (sub_eq_add_neg _ _)
    have e2 : Matrix.trace (b₀.1.map (incA D) ⬝ (y ⬝ (rat b ⬝ adj y))) = Matrix.trace (pr b₀ y (y ⬝ rat b)) := by
      rw [pr_def, ← Matrix.mul_assoc y, ← Matrix.mul_assoc (b₀.1.map (incA D)) (y ⬝ rat b) (adj y), Matrix.trace_mul_comm]
    rw [e, chz_add, Matrix.mul_neg, Matrix.trace_neg, halfTr_neg'', e2]
  have ht : ∀ ξ : Matrix (Fin ρ) (Fin p) D.host.E,
      ψ (trA (Matrix.trace (pr b₀ (x - y ⬝ rat b) (ξ.map (incA D))))) * Ω (g * h) (ξ.map (incA D) + y) =
        ψ u * (ψ (trA (Matrix.trace (pr b₀ x (ξ.map (incA D))))) * Ω h (ξ.map (incA D) + y)) := by
    intro ξ
    refine term_unip hΩ g hb hg h x y _ ?_
    have := rat_quad b₀ b ξ
    rw [show ξ.map (incA D) = rat ξ from rfl, this]
    exact psi_halfTr_rat hψ _
  simp only [th, ht, tsum_mul_left, hz]
  have e1 : ψ (-u) * ψ u = 1 := by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  linear_combination (-(chz ψ b₀ z * ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, ψ (trA (Matrix.trace (pr b₀ x (ξ.map (incA D))))) * Ω h (ξ.map (incA D) + y))) * e1

def Pp (b₀ : HermE D ρ) (u v : Mx D ρ p) : AF D.host.F := trA (Matrix.trace (pr b₀ u v))

theorem Pp_comm (b₀ : HermE D ρ) (u v : Mx D ρ p) : Pp b₀ u v = Pp b₀ v u := (trA_pr_comm b₀ v u)

theorem Pp_add_left (b₀ : HermE D ρ) (u u' v : Mx D ρ p) : Pp b₀ (u + u') v = Pp b₀ u v + Pp b₀ u' v := by
  simp only [Pp, pr_add_left, Matrix.trace_add, Weyl.trA_add]

theorem Pp_add_right (b₀ : HermE D ρ) (u v v' : Mx D ρ p) : Pp b₀ u (v + v') = Pp b₀ u v + Pp b₀ u v' := by
  simp only [Pp, pr_add_right, Matrix.trace_add, Weyl.trA_add]

theorem Pp_neg_left (b₀ : HermE D ρ) (u v : Mx D ρ p) : Pp b₀ (-u) v = -Pp b₀ u v := by
  simp only [Pp, pr_neg_left, Matrix.trace_neg, Weyl.trA_neg]

theorem phase_weyl {A : Type} [AddCommGroup A] (ψ : AddChar A ℂ) (a b c : A) :
    ψ a * ψ b = ψ (-c) * ψ (a + b + c) := by
  rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, show -c + (a + b + c) = a + b by abel]

theorem pairing_eq (b₀ : HermE D ρ) (ψ : AddChar (AF D.host.F) ℂ) (u v : Mx D ρ p) :
    GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing b₀.1 ψ u v = ψ (Pp b₀ u v) := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing, GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.gramQ, GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.mmul, Pp, pr_def]
  rw [Matrix.mul_assoc]
  rfl

theorem continuous_psi_Pp {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ) (x : Mx D ρ p) :
    Continuous fun u : Mx D ρ p => ψ (Pp b₀ x u) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have ht : Continuous (trA (D := D)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
  exact hψ.1.comp (ht.comp (continuous_const.matrix_mul (continuous_const.matrix_mul continuous_id)).matrix_trace)

theorem poisson_step {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {b₀ : HermE D ρ} (hb : b₀.1.det ≠ 0)
    {χ : (AE D)ˣ →* Circle} {θ : InfFam D} (hθ : IsInfFam θ) (m : Meas D ρ p) {Ω : G D p → Mx D ρ p → ℂ}
    (hΩ : IsTh ψ χ θ b₀ m.μ Ω) (g : G D p) (hg : mat g = blk4 0 1 (-1) 0) (h : G D p) (x y : Mx D ρ p) :
    ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, ψ (Pp b₀ x (ξ.map (incA D))) * Ω h (ξ.map (incA D) + y) =
      ψ (-Pp b₀ x y) * ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E,
        ψ (Pp b₀ (-y) (ξ.map (incA D))) * Ω (g * h) (ξ.map (incA D) + x) := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := lattice_Mx D ρ p
  haveI : BorelSpace (Mx D ρ p) := ⟨rfl⟩
  have hT : IsHermND (D.sp.cm.sig) b₀.1 := ⟨fun i j => congrFun (congrFun b₀.2 i) j, hb⟩
  obtain ⟨h1, h2⟩ := GlobalTheory.T.rationalAdelicMatrices_self_annihilator D ρ p b₀.1 hT ψ hψ
  have hs := ThetaPoisson.pairing_symm (n := p) hT ψ
  have hμ := m.hμ
  haveI := hμ.1
  have hn1 : ∀ a, ‖ψ a‖ = 1 := hψ.2.1
  let f : Mx D ρ p → ℂ := fun u => Ω h (u + y) * ψ (Pp b₀ x u)
  have hfc : Continuous f :=
    (hΩ.cont.comp (continuous_const.prodMk (continuous_id.add continuous_const))).mul (continuous_psi_Pp hψ b₀ x)
  have hval : ∀ γ : Mx D ρ p, ∫ u, f u * GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing b₀.1 ψ u γ ∂m.μ =
      ψ (-Pp b₀ (γ + x) y) * Ω (g * h) (γ + x) := by
    intro γ
    rw [hΩ.weyl g hg h (γ + x),
      ← integral_add_right_eq_self (μ := m.μ) (fun t => Ω h t * ψ (trA (Matrix.trace (pr b₀ (γ + x) t)))) y,
      ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    have e : Pp b₀ (γ + x) (u + y) = Pp b₀ x u + Pp b₀ u γ + Pp b₀ (γ + x) y := by
      rw [Pp_add_right, Pp_add_left b₀ γ x u, Pp_comm b₀ γ u]
      abel
    have e2 := phase_weyl ψ (Pp b₀ x u) (Pp b₀ u γ) (Pp b₀ (γ + x) y)
    rw [← e] at e2
    show Ω h (u + y) * ψ (Pp b₀ x u) * GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing b₀.1 ψ u γ =
      ψ (-Pp b₀ (γ + x) y) * (Ω h (u + y) * ψ (Pp b₀ (γ + x) (u + y)))
    rw [pairing_eq]
    linear_combination (Ω h (u + y)) * e2
  have key := ThetaPoisson.poisson_translates (ratMx D ρ p) K hK hKc (GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing (n := p) b₀.1 ψ)
    (fun w => ?_) hs (fun a a' w => ?_) (fun a w => ?_) h1 h2 m.μ m.𝓕 hμ.2.1 hμ.2.2 (f := f) hfc ?_ ?_
  · simp only [hval] at key
    rw [ThetaPoisson.tsum_ratMx f,
      ThetaPoisson.tsum_ratMx (fun γ => ψ (-Pp b₀ (γ + x) y) * Ω (g * h) (γ + x))] at key
    calc ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, ψ (Pp b₀ x (ξ.map (incA D))) * Ω h (ξ.map (incA D) + y)
        = ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, f (ξ.map (incA D)) := tsum_congr fun ξ => mul_comm _ _
      _ = _ := key
      _ = _ := by
        rw [← tsum_mul_left]
        refine tsum_congr fun ξ => ?_
        have e : -Pp b₀ (ξ.map (incA D) + x) y = -Pp b₀ x y + Pp b₀ (-y) (ξ.map (incA D)) := by
          rw [Pp_add_left, Pp_neg_left, Pp_comm b₀ y]
          abel
        rw [e, AddChar.map_add_eq_mul, mul_assoc]
  · simp only [hs _ w, pairing_eq]
    exact continuous_psi_Pp hψ b₀ w
  · rw [pairing_eq, pairing_eq, pairing_eq, Pp_add_left, AddChar.map_add_eq_mul]
  · rw [pairing_eq]
    exact hn1 _
  · intro Q hQ
    have hcy : Continuous fun u : Mx D ρ p => u + y := continuous_id.add continuous_const
    obtain ⟨b, hb1, hb2⟩ := ThetaPoisson.translates_bound hθ ⟨Ω h, hΩ.mem h⟩ ((· + y) '' Q) (hQ.image hcy)
    refine ⟨b, hb1, fun u hu ξ => ?_⟩
    have h3 := hb2 (u + y) ⟨u, hu, rfl⟩ ξ
    simp only [f]
    rw [norm_mul, hn1, mul_one, add_assoc]
    exact h3
  · obtain ⟨b, hb1, hb2⟩ := ThetaPoisson.translates_bound hθ ⟨Ω (g * h), hΩ.mem _⟩ {x} isCompact_singleton
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun γ => ?_) hb1
    rw [hval, norm_mul, hn1, one_mul]
    exact hb2 x rfl γ

theorem chz_zW (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (z : hermA D ρ) (x y : Mx D ρ p) :
    chz ψ b₀ (zW z x y) = chz ψ b₀ z * ψ (-Pp b₀ x y) := by
  have e : (zW z x y : hermA D ρ) = ⟨z.1 + -(x ⬝ adj y + y ⬝ adj x), by
      have := (zW z x y).2
      have e' : z.1 + -(x ⬝ adj y + y ⬝ adj x) = (zW z x y).1 := by simp only [zW]; abel
      rw [e']
      exact this⟩ := Subtype.ext (by simp only [zW]; abel)
  have e1 : Matrix.trace (b₀.1.map (incA D) ⬝ (y ⬝ adj x)) = Matrix.trace (pr b₀ x y) := by
    rw [pr_def, ← Matrix.mul_assoc (b₀.1.map (incA D)) y (adj x), Matrix.trace_mul_comm]
  have e2 : Matrix.trace (b₀.1.map (incA D) ⬝ (x ⬝ adj y)) = cA D (Matrix.trace (pr b₀ x y)) := by
    rw [← trace_pr_swap, pr_def, ← Matrix.mul_assoc (b₀.1.map (incA D)) x (adj y), Matrix.trace_mul_comm]
  rw [e, chz_add, Matrix.mul_neg, Matrix.mul_add, Matrix.trace_neg, Matrix.trace_add, e1, e2, halfTr_neg'', halfTr_add'',
    add_comm (halfTr (cA D _)), Unip.halfTr_add_cA]
  rfl

theorem th_weyl {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {b₀ : HermE D ρ} (hb : b₀.1.det ≠ 0)
    {χ : (AE D)ˣ →* Circle} {θ : InfFam D} (hθ : IsInfFam θ) (m : Meas D ρ p) {Ω : G D p → Mx D ρ p → ℂ}
    (hΩ : IsTh ψ χ θ b₀ m.μ Ω) (g : G D p) (hg : mat g = blk4 0 1 (-1) 0) (h : G D p) (z : hermA D ρ) (x y : Mx D ρ p) :
    th ψ b₀ (Ω h) z x y = th ψ b₀ (Ω (g * h)) (zW z x y) (-y) x := by
  have key := poisson_step hψ hb hθ m hΩ g hg h x y
  show chz ψ b₀ z * ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, ψ (Pp b₀ x (ξ.map (incA D))) * Ω h (ξ.map (incA D) + y) =
    chz ψ b₀ (zW z x y) * ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E,
      ψ (Pp b₀ (-y) (ξ.map (incA D))) * Ω (g * h) (ξ.map (incA D) + x)
  rw [key, chz_zW, mul_assoc]

def glR (a : Matrix (Fin p) (Fin p) D.host.E) (ha : IsUnit a.det) : GL (Fin p) (AE D) :=
  ⟨rat a, rat a⁻¹, by rw [← rat_mul, Matrix.mul_nonsing_inv _ ha, rat_one],
    by rw [← rat_mul, Matrix.nonsing_inv_mul _ ha, rat_one]⟩

theorem det_glR (a : Matrix (Fin p) (Fin p) D.host.E) (ha : IsUnit a.det) :
    ((Matrix.GeneralLinearGroup.det (glR a ha) : (AE D)ˣ) : AE D) = incA D (ha.unit : D.host.Eˣ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, IsUnit.unit_spec]
  exact ((incA D).map_det a).symm

theorem chi_rat {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (v : (AE D)ˣ) (u : D.host.Eˣ)
    (hv : (v : AE D) = incA D u) : χ v = 1 := by
  rw [← hχ.2 u]
  exact congrArg χ (Units.ext hv)

theorem absA_rat (v : (AE D)ˣ) (u : D.host.Eˣ) (hv : (v : AE D) = incA D u) : absA D v = 1 := by
  rw [← absE_inclR (F := D.host.F) u]
  exact congrArg _ (Units.ext hv)

theorem trace_pr_levi (b₀ : HermE D ρ) (x X : Mx D ρ p) (a : Mx D p p) :
    Matrix.trace (pr b₀ (x ⬝ adj a) X) = Matrix.trace (pr b₀ x (X ⬝ a)) := by
  simp only [pr_def, adj_mul, adj_adj]
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem th_levi {ψ : AddChar (AF D.host.F) ℂ} {b₀ : HermE D ρ}
    {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) {θ : InfFam D} {μ : Measure (Mx D ρ p)} {Ω : G D p → Mx D ρ p → ℂ}
    (hΩ : IsTh ψ χ θ b₀ μ Ω) (g : G D p) (a : Matrix (Fin p) (Fin p) D.host.E) (ha : IsUnit a.det)
    (hg : mat g = blk4 (glR a ha).1 0 0 (adj ((glR a ha)⁻¹).1)) (h : G D p) (z : hermA D ρ) (x y : Mx D ρ p) :
    th ψ b₀ (Ω h) z x y = th ψ b₀ (Ω (g * h)) z (x ⬝ adj (glR a ha).1) (y ⬝ ((glR a ha)⁻¹).1) := by
  have h1 : (((glR a ha)⁻¹).1 : Mx D p p) ⬝ (glR a ha).1 = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  let e : Matrix (Fin ρ) (Fin p) D.host.E ≃ Matrix (Fin ρ) (Fin p) D.host.E :=
    { toFun := fun ξ => ξ * a
      invFun := fun ξ => ξ * a⁻¹
      left_inv := fun ξ => by simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ha, Matrix.mul_one]
      right_inv := fun ξ => by simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ha, Matrix.mul_one] }
  have hc : (χ (Matrix.GeneralLinearGroup.det (glR a ha)) : ℂ) = 1 := by
    rw [chi_rat hχ _ ha.unit (det_glR a ha)]
    simp
  have hA : absA D (Matrix.GeneralLinearGroup.det (glR a ha)) = 1 := by
    exact absA_rat _ ha.unit (det_glR a ha)
  simp only [th]
  congr 1
  rw [← e.tsum_eq]
  refine tsum_congr fun ξ => ?_
  rw [hΩ.levi g (glR a ha) hg h, hc, hA, trace_pr_levi]
  have e1 : ((ξ.map (incA D) + y ⬝ ((glR a ha)⁻¹).1) ⬝ (glR a ha).1 : Mx D ρ p) = (e ξ).map (incA D) + y := by
    rw [Matrix.add_mul, Matrix.mul_assoc, h1, Matrix.mul_one]
    congr 1
    exact (rat_mul ξ a).symm
  have e2 : (ξ.map (incA D) ⬝ (glR a ha).1 : Mx D ρ p) = (e ξ).map (incA D) := (rat_mul ξ a).symm
  rw [e1, e2]
  simp [npow]

def St (M : Maps D hn) (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (Ω : G D p → Mx D ρ p → ℂ) (γ : G D p) : Prop :=
  ∀ (h : G D p) (z : hermA D ρ) (x y : Mx D ρ p), ∃ (z' : hermA D ρ) (x' y' : Mx D ρ p),
    M.emb γ * (M.nzx z x * M.sh y) = M.nzx z' x' * M.sh y' * M.emb γ ∧
    th ψ b₀ (Ω h) z x y = th ψ b₀ (Ω (γ * h)) z' x' y'

theorem St_mul {M : Maps D hn} {ψ : AddChar (AF D.host.F) ℂ} {b₀ : HermE D ρ} {Ω : G D p → Mx D ρ p → ℂ} {γ₁ γ₂ : G D p}
    (h₁ : St M ψ b₀ Ω γ₁) (h₂ : St M ψ b₀ Ω γ₂) : St M ψ b₀ Ω (γ₁ * γ₂) := by
  intro h z x y
  obtain ⟨z2, x2, y2, e2, t2⟩ := h₂ h z x y
  obtain ⟨z3, x3, y3, e3, t3⟩ := h₁ (γ₂ * h) z2 x2 y2
  refine ⟨z3, x3, y3, ?_, ?_⟩
  · rw [map_mul, mul_assoc, e2, ← mul_assoc, e3, mul_assoc]
  · rw [t2, t3, mul_assoc]

theorem ratGen (D : D7) (p : ℕ) (S : G D p → Prop) (hmul : ∀ g h, S g → S h → S (g * h))
    (hm : ∀ (g : G D p) (a : Matrix (Fin p) (Fin p) D.host.E) (ha : IsUnit a.det),
      mat g = blk4 (glR a ha).1 0 0 (adj ((glR a ha)⁻¹).1) → S g)
    (hn : ∀ (g : G D p) (b : Matrix (Fin p) (Fin p) D.host.E), adj (rat b : Mx D p p) = rat b →
      mat g = blk4 1 (rat b) 0 1 → S g)
    (hw : ∀ g : G D p, mat g = blk4 0 1 (-1) 0 → S g) : ∀ γ ∈ GF D p, S γ := by
  intro γ hγ
  have hF : FieldGen D.host.E (D.sp.cm.sig : D.host.E →+* D.host.E) p :=
    FieldGenPf.fieldGen_of_bruhat GlobalTheory.CompanionTheory.BruhatCell.bruhat D.host.E _ (fun x => star_star x) two_ne_zero p
  obtain ⟨h1, h2, -⟩ := GlobalTheory.CompanionTheory.RatPtsUnn.ratPtsUnn D p
  obtain ⟨g, hgu, hgU, hg⟩ := h1 γ hγ
  let T : Matrix (Fin (p + p)) (Fin (p + p)) D.host.E → Prop := fun N =>
    IsUnit N.det ∧ IsUnitary (D.sp.cm.sig : D.host.E →+* D.host.E) (EC.Jm D.host.E p) N ∧
      ∀ γ' : G D p, mat γ' = N.map (incA D) → S γ'
  have hprod : ∀ M₁ M₂, T M₁ → T M₂ → T (M₁ * M₂) := by
    rintro M₁ M₂ ⟨u₁, U₁, s₁⟩ ⟨u₂, U₂, s₂⟩
    refine ⟨by rw [Matrix.det_mul]; exact u₁.mul u₂, Transfer.isUnitary_mul U₁ U₂, fun γ' e => ?_⟩
    obtain ⟨γ₁, -, e₁⟩ := h2 M₁ u₁ U₁
    obtain ⟨γ₂, -, e₂⟩ := h2 M₂ u₂ U₂
    have e' : γ' = γ₁ * γ₂ := mat_injective' (by rw [e, mat_mul', e₁, e₂, Matrix.map_mul])
    rw [e']
    exact hmul _ _ (s₁ _ e₁) (s₂ _ e₂)
  have hmA : ∀ a : Matrix (Fin p) (Fin p) D.host.E, IsUnit a.det →
      T (mA (D.sp.cm.sig : D.host.E →+* D.host.E) a) := fun a ha =>
    ⟨Transfer.mA_isUnit_det _ ha, Transfer.mA_isUnitary Transfer.sig_sig ha, fun γ' e =>
      hm γ' a ha (e.trans (Transfer.map_mA a))⟩
  have hnB : ∀ b : Matrix (Fin p) (Fin p) D.host.E, cT (D.sp.cm.sig : D.host.E →+* D.host.E) b = b → T (nB b) := by
    intro b hb
    refine ⟨Transfer.nB_isUnit_det b, Transfer.nB_isUnitary hb, fun γ' e => hn γ' b ?_ (e.trans (Transfer.map_nB b))⟩
    rw [← rat_conjTranspose]
    exact congrArg rat hb
  have hJ : T (EC.Jm D.host.E p) :=
    ⟨Transfer.Jm_isUnit_det, Transfer.Jm_isUnitary _, fun γ' e => hw γ' (e.trans Transfer.map_Jm)⟩
  exact (hF T hprod hmA hnB hJ g hgu hgU).2.2 γ hg

theorem thTwist : ThTwist := by
  intro D n ρ p hn M m ψ hψ b₀ hb χ hχ θ hθ Ω hΩ γ hγ z x y z' x' y' e
  have hS : St M ψ b₀ Ω γ := by
    refine ratGen D p (St M ψ b₀ Ω) (fun _ _ => St_mul) ?_ ?_ ?_ γ hγ
    · intro g a ha hg h z x y
      exact ⟨z, _, _, gl_levi M g (glR a ha) hg z x y, th_levi hχ hΩ g a ha hg h z x y⟩
    · intro g b hb' hg h z x y
      exact ⟨_, _, y, gl_unip M g (rat b) hb' hg z x y, th_unip hψ hΩ g b hb' hg h z x y⟩
    · intro g hg h z x y
      exact ⟨_, _, _, gl_weyl M g hg z x y, th_weyl hψ hb hθ m hΩ g hg h z x y⟩
  obtain ⟨z2, x2, y2, e2, t2⟩ := hS 1 z x y
  have e3 : M.nzx z' x' * M.sh y' = M.nzx z2 x2 * M.sh y2 := mul_right_cancel (e.symm.trans e2)
  obtain ⟨rfl, rfl, rfl⟩ := nzx_sh_inj M e3
  rw [t2, mul_one]

end GlobalTheory.CompanionTheory.ThTw
