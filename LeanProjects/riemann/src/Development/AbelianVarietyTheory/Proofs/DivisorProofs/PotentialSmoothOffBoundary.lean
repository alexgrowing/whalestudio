import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricSmoothOffBoundary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenMetricFlagCompactification
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.AnForm.M
open GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam
open scoped ContDiff

namespace GlobalTheory.HodgeChgSmooth

theorem smoothOn_lnRatio {F : Type} [Field F] [NumberField F] {Y : Var F} {σ : F →+* ℂ} {Δ : Y.Dv}
    {m m' : Y.Met σ Δ} {S : Set (Y.pts σ)} (h : m.SmoothOn S) (h' : m'.SmoothOn S) :
    (Y.an σ).SmoothOn S (lnRatio (C := cxSt F) m m') := by
  refine AnRead.smoothOn_of_cover (T := fun g : Y.Fnˣ => Var.eqnSet σ Δ g) (fun g => Var.isOpen_eqnSet Δ g)
    (fun y _ => ⟨_, Var.mem_eqnSet Δ y⟩) fun g => ?_
  refine AnRead.SmoothOn.congr (f := fun y => (m'.wt g y - m.wt g y) / 2)
    (fun i => (((h'.2 g) i).sub ((h.2 g) i)).div_const 2) fun y hy => ?_
  have hg : Δ.GeneratesAt (under y) ((g⁻¹ : Y.Fnˣ) : Y.Fn) := by
    rw [Units.val_inv_eq_inv_val]
    exact CartierDiv.isEqn_iff_generatesAt_inv.1 hy.2
  have hp : ∀ {n : Y.Met σ Δ}, y ∈ n.posSet → PosAt (C := cxSt F) n y := fun hy' => by
    have h₁ : y ∈ Var.eqnSet σ Δ (eqn Δ (under y)) := Base.isEqn_eqn _ _
    exact ((Var.Met.mem_posSet_iff h₁).1 hy').trans_eq (Var.pn_frame h₁).symm
  rw [lnRatio_eq hg (hp (h.1 hy.1)) (hp (h'.1 hy.1))]
  show Real.log (Y.pn σ Δ m (Y.cx σ ((g⁻¹ : Y.Fnˣ) : Y.Fn)) y) / 2 -
      Real.log (Y.pn σ Δ m' (Y.cx σ ((g⁻¹ : Y.Fnˣ) : Y.Fn)) y) / 2 = (-Real.log (m'.h g y) - -Real.log (m.h g y)) / 2
  rw [Var.pn_frame hy.2, Var.pn_frame hy.2]
  ring

theorem smoothOn_of_manIs {F : Type} [Field F] [NumberField F] {Y : Var F} {e : ℕ} {M : Man e} (I : ManIs M Y)
    (he : Y.dim = e) (a : Fin (M.n + 1)) {S : Set (Y.pts (I.ε a))} (hS : IsOpen S) {g : Y.pts (I.ε a) → ℝ}
    (hg : (Y.an (I.ε a)).SmoothOn S g) {f : M.X a → ℝ} (hfg : ∀ z, I.pt a z ∈ S → f z = g (I.pt a z)) :
    (M.A a).SmoothOn {z | I.pt a z ∈ S} f := by
  subst he
  intro j
  obtain ⟨c, hc⟩ := I.alg a j
  have h1 := (c.contDiffOn_finChart_iff _ S g).2 (hg.chart hS c)
  rw [hc]
  have hset : ((I.pt a).transOpenPartialHomeomorph c.finChart).target ∩
      ((I.pt a).transOpenPartialHomeomorph c.finChart).symm ⁻¹' {z | I.pt a z ∈ S} =
      c.finChart.target ∩ c.finChart.symm ⁻¹' S := by
    ext v
    simp [Homeomorph.transOpenPartialHomeomorph_target, Homeomorph.transOpenPartialHomeomorph_symm_apply]
  rw [hset]
  refine h1.congr fun v hv => ?_
  have hv' : I.pt a ((I.pt a).symm (c.finChart.symm v)) ∈ S := by simpa using hv.2
  simp only [Function.comp_apply, Homeomorph.transOpenPartialHomeomorph_symm_apply]
  rw [hfg _ hv', Homeomorph.apply_symm_apply]

end GlobalTheory.HodgeChgSmooth

open GlobalTheory.Mean4 GlobalTheory.Mean4O in

theorem GlobalTheory.HodgeChgSmooth.smoothOn_ph : Hypotheses2 → HypothesesH → OnObj fun _ O _ T _ _ =>
    ∀ c u σ, ((T.M c).A σ).SmoothOn ((T.M c).Z σ)ᶜ ((T.F c).ph u σ) := by
  intro _ _ D O hO _ A T H h c u a
  obtain ⟨x, P, hc⟩ := hO
  let I := h.man c
  let S : Set (Pts (O.var c) (I.ε a)) := {y | ¬ LiesIn ((O.Φ.C c).down y) (genBd O.s.T.Z)}
  have hT := isOpen_not_liesIn (p := genStr O.s.T.Z) (σ := embOf O.κ.e (I.ε a)) (genBd O.s.T.Z)
  have hm : ∀ n, IsOpen S ∧ (O.met.hm c none (I.ε a) n).SmoothOn S := fun n => by
    rw [hc.hm_eq]
    exact FlagCpt.smoothOn_met_of_eigMet _ _ _ _ _ _ _ _ _ _ _ (O.Φ.C c) (I.ε a) (x.hodge _) _ hT
      (ToroidalCompactificationData.hodge_smoothOn _ _ _ _ _ _ _ x _) n
  have h0 : ∀ n, (O.met.h0 c (I.ε a) n).SmoothOn S := fun n => by
    rw [hc.h0_eq]
    have := (FlagCpt.smoothOn_met_of_eigMet _ _ _ _ _ _ _ _ _ _ _ (O.Φ.C c) (I.ε a) (x.eigMet _) Set.univ isOpen_univ
      (x.smoothOn_eigMet _) n).2
    exact ⟨fun _ _ => this.1 trivial, fun g => (this.2 g).mono fun y hy => ⟨trivial, hy.2⟩⟩
  have hS : IsOpen S := (hm 0).1
  have hg : ((O.var c).an (I.ε a)).SmoothOn S (O.chg c none u (I.ε a)) := by
    intro i
    refine (ContDiffOn.sum (s := Finset.univ) fun r _ => (contDiffOn_const (c := u r.1 r.2)).mul
      (GlobalTheory.HodgeChgSmooth.smoothOn_lnRatio (hm (O.ex r)).2 (h0 (O.ex r)) i)).congr fun v _ => ?_
    simp [Setup.chg]
  have hZ : ((T.M c).Z a)ᶜ = {z | I.pt a z ∈ S} := by
    ext z
    exact not_congr ((h.an c).Z a z)
  rw [hZ]
  refine GlobalTheory.HodgeChgSmooth.smoothOn_of_manIs I ?_ a hS hg fun z hz => (h.an c).ph u a z ?_
  · exact O.dim_eq c
  · rw [(h.an c).Z a z]
    exact hz
