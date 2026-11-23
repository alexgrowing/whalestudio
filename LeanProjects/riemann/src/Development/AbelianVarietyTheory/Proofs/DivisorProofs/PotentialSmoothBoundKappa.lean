import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InSOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialSmoothOffBoundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralCutoffLogDecay
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPotentialPositiveOnComponents
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open CategoryTheory AlgebraicGeometry ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory GlobalTheory.ShFam GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.FlagPoly

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PshTrans

theorem contDiffAt_e_of_finChart {F : Type} [Field F] [NumberField F] {Y : Var F} {σ : F →+* ℂ}
    (c : AlgChart Y.str σ Y.dim) {f : Pts Y σ → ℝ} {y : Pts Y σ}
    (hf : ContDiffAt ℝ 2 (f ∘ c.finChart.symm) (c.finChart y)) :
    ContDiffAt ℝ 2 (f ∘ c.e.symm) (c.e y) := by
  have e1 : (FinChart.toV Y.dim).symm (c.e y) = c.finChart y := by
    rw [← AlgChart.toV_finChart]
    exact (FinChart.toV Y.dim).symm_apply_apply _
  rw [← e1] at hf
  have h2 := hf.comp (c.e y) (FinChart.toV Y.dim).symm.contDiff.contDiffAt
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
  simp only [Function.comp_apply, AlgChart.finChart_symm_apply, ContinuousLinearEquiv.apply_symm_apply]

theorem isPsh_of_levi_algChart : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} {e : ℕ} {M : Man e} (I : ManIs M Y),
    Y.dim = e → ∀ (a : Fin (M.n + 1)) {ι : Type} [Fintype ι] {Δ : ι → Y.Dv}
    (m : ∀ i σ, (cxSt F).Met Y σ (Δ i)), (∀ i, Y.mSmooth (I.ε a) (Δ i) (m i (I.ε a))) →
    ∀ (t : ι → ℝ) {P : M.Pot}, I.FormOf m t P → IsPotential (M.A a) (P a) →
    ∀ (g : Pts Y (I.ε a) → ℝ), (Y.an (I.ε a)).SmoothOn Set.univ g → ∀ (κ : ℝ),
    (∀ (c : AlgChart Y.str (I.ε a) Y.dim), ∀ y ∈ c.e.source, ∀ x, (I.pt a).symm y ∈ (M.Om a).U x → ∀ ξ,
      0 ≤ ∑ i, t i * (Real.pi / 2 * curvMet (m i (I.ε a)) c y ξ) + c.levi g y ξ +
        κ * c.levi (fun z => (M.Om a).φ x ((I.pt a).symm z)) y ξ) →
    IsPsh (M.A a) (P a + LocPot.ofFun (fun z => g (I.pt a z)) + (M.Om a).rsmul κ) := by
  intro F _ _ Y e M I he a ι _ Δ m hm t P hP hPp g hg κ hL
  have hGs : (M.A a).Smooth (fun z => g (I.pt a z)) := by
    have h1 := GlobalTheory.HodgeChgSmooth.smoothOn_of_manIs I he a isOpen_univ hg (f := fun z => g (I.pt a z))
      (fun _ _ => rfl)
    simpa [FinHolAtlas.Smooth] using h1
  have hO : IsPotential (M.A a) (M.Om a) := (M.bd a).2.2.1
  subst he
  intro x j y hy w
  obtain ⟨hyt, ⟨⟨hPx, -⟩, hOx⟩⟩ := hy
  obtain ⟨cj, hcj⟩ := I.alg a j
  obtain ⟨p, hp⟩ : ∃ p, I.pt a (((M.A a).chart j).symm y) = p := ⟨_, rfl⟩
  have hzs : ((M.A a).chart j).symm y ∈ ((M.A a).chart j).source := ((M.A a).chart j).map_target hyt
  have hsp : (I.pt a).symm p = ((M.A a).chart j).symm y := by rw [← hp]; simp
  have hyeq : y = (M.A a).chart j ((I.pt a).symm p) := by rw [hsp, ((M.A a).chart j).right_inv hyt]
  subst hyeq
  clear hp
  have hj : (I.pt a).symm p ∈ ((M.A a).chart j).source := by rw [hsp]; exact hzs
  have hvz : ((M.A a).chart j).symm ((M.A a).chart j ((I.pt a).symm p)) = (I.pt a).symm p :=
    ((M.A a).chart j).left_inv hj
  rw [hvz] at hPx hOx
  have hyj : p ∈ cj.e.source := by
    rw [hcj] at hj
    simpa [Homeomorph.transOpenPartialHomeomorph_source] using hj
  have hvc : (M.A a).chart j ((I.pt a).symm p) = cj.finChart p := by
    rw [hcj]
    simp

  obtain ⟨Q, hQ, hlev⟩ := hP a
  have hPs := potSmoothAt (M.A a) (P a) hPp x j ⟨hyt, by rw [Set.mem_preimage, hvz]; exact hPx⟩
  have hGc := GlobalTheory.ShellMass.smoothOn_contDiffAt isOpen_univ hGs j hyt trivial
  have hOs := potSmoothAt (M.A a) (M.Om a) hO x j ⟨hyt, by rw [Set.mem_preimage, hvz]; exact hOx⟩
  have hsplit : levi ((P a + LocPot.ofFun (fun z => g (I.pt a z)) + (M.Om a).rsmul κ).φ x ∘ ((M.A a).chart j).symm) ((M.A a).chart j ((I.pt a).symm p)) w =
      (levi ((P a).φ x ∘ ((M.A a).chart j).symm) ((M.A a).chart j ((I.pt a).symm p)) w +
        1 * levi ((fun z => g (I.pt a z)) ∘ ((M.A a).chart j).symm) ((M.A a).chart j ((I.pt a).symm p)) w) +
        κ * levi ((M.Om a).φ x ∘ ((M.A a).chart j).symm) ((M.A a).chart j ((I.pt a).symm p)) w := by
    rw [← levi_add_smul 1 hPs hGc w, ← levi_add_smul κ (hPs.add (contDiffAt_const.mul hGc)) hOs w]
    congr 1
    funext u
    simp only [Function.comp_apply, one_mul]
    rfl
  have eP : levi ((P a).φ x ∘ ((M.A a).chart j).symm) ((M.A a).chart j ((I.pt a).symm p)) w =
      ∑ i, t i * (Real.pi / 2 * curvMet (m i (I.ε a)) cj p w) := by
    rw [GlobalTheory.ShellMass.levi_base hPp x j hyt (by rw [hvz]; exact hPx) w, hlev j _ hyt w]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [← GlobalTheory.ShellMass.levi_base (hQ i).2 ((I.pt a).symm p) j hyt (by rw [hvz]; exact (Q i).mem_U _) w]
    have key := GlobalTheory.AmplePos.levi_isPot_eq_curvMet (hm i) (I.pt a) (hQ i).1 cj ((I.pt a).symm p)
      (by simpa using hyj) w
    simp only [Homeomorph.apply_symm_apply] at key
    rw [hvc, ← key, hcj]
  have hsm : (Y.an (I.ε a)).SmoothOn Set.univ g := hg
  have hG' : ContDiffAt ℝ 2 (g ∘ cj.e.symm) (cj.e p) := hsm.contDiffAt_two isOpen_univ hyj trivial
  have eG : levi ((fun z => g (I.pt a z)) ∘ ((M.A a).chart j).symm) ((M.A a).chart j ((I.pt a).symm p)) w = cj.levi g p w := by
    rw [hvc, AlgChart.levi, cj.leviV_re_eq hG' w, hcj]
    congr 1
    funext u
    simp [Homeomorph.transOpenPartialHomeomorph_symm_apply]
  have hOf : ContDiffAt ℝ 2 ((fun z => (M.Om a).φ x ((I.pt a).symm z)) ∘ cj.finChart.symm) (cj.finChart p) := by
    have h1 := hOs
    rw [hvc, hcj] at h1
    simpa [Function.comp_def, Homeomorph.transOpenPartialHomeomorph_symm_apply] using h1
  have hO' := contDiffAt_e_of_finChart cj hOf
  have eO : levi ((M.Om a).φ x ∘ ((M.A a).chart j).symm) ((M.A a).chart j ((I.pt a).symm p)) w =
      cj.levi (fun z => (M.Om a).φ x ((I.pt a).symm z)) p w := by
    rw [hvc, AlgChart.levi, cj.leviV_re_eq hO' w, hcj]
    congr 1
  have hfin := hL cj p hyj x hOx w
  rw [hsplit, eP, eG, eO, one_mul]
  exact hfin

end GlobalTheory.PshTrans
