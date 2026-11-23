import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsStokesStep
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedB
import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ADensStC
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M Filter Topology

namespace StokesStep

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isOpen_multicone : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  simp only [Set.ofPred_forall, Set.ofPred_exists]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem ptsIntegral_congr_g (P : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    {g g' : ((Σ k, ι k) → ℂ) → ℝ} (hg : ∀ z ∈ mcPts P, g z = g' z) :
    ptsIntegral P φ g = ptsIntegral P φ g' := by
  classical
  unfold ptsIntegral ptsIntegralAt
  split_ifs with hΨ
  · congr 1
    funext y
    refine finsum_congr fun w => finsum_congr fun _ => ?_
    unfold sheetDensity
    split_ifs with hγ
    · rw [hg _ hγ.choose_spec.2.self_of_nhds.2.1]
    · rfl
  · rfl

theorem isConeTangent_lift {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) (x : R.X)
    (j : Fin R.A.n) {y : Fin e → ℂ}
    (hy : y ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) (w : Fin e → ℂ) :
    IsConeTangent (Int.castRingHom ℂ) P (R.lift x ((R.A.chart j).symm y))
      (fderiv ℂ (fun y' => R.lift x ((R.A.chart j).symm y')) y w) := by
  set τ : (Fin e → ℂ) → (Σ k, ι k) → ℂ := fun y' => R.lift x ((R.A.chart j).symm y') with hτdef
  have hO : IsOpen ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) :=
    (R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x)
  have hτ : AnalyticAt ℂ τ y := analyticAt_pi_iff.mpr fun p => R.holo x p j y hy
  intro f hf
  set F := map (Int.castRingHom ℂ) f
  have h0 : (fun y' => eval (τ y') F) =ᶠ[𝓝 y] fun _ => (0 : ℂ) := by
    filter_upwards [hO.mem_nhds hy] with y' hy'
    exact (R.mem x _ hy'.2).2 f hf
  have hD := (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_hasFDerivAt_eval F (τ y)).comp y hτ.differentiableAt.hasFDerivAt
  have hD0 : HasFDerivAt (fun y' => eval (τ y') F) (0 : (Fin e → ℂ) →L[ℂ] ℂ) y :=
    (hasFDerivAt_const (0 : ℂ) y).congr_of_eventuallyEq h0
  have h1 := congrArg (fun L => L w) (hD.unique hD0)
  simpa [smul_eq_mul, mul_comm] using h1

theorem isPsh_potOf {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) {A : HermLine ι}
    (hA : IsSemipositiveH P A) : IsPsh R.A (potOf R A) := by
  intro x j y hy w
  have hy' : y ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x := hy
  set τ : (Fin e → ℂ) → (Σ k, ι k) → ℂ := fun y' => R.lift x ((R.A.chart j).symm y') with hτdef
  have hτ : AnalyticAt ℂ τ y := analyticAt_pi_iff.mpr fun p => R.holo x p j y hy'
  have hz : τ y ∈ mcPts P := R.mem x _ hy'.2
  have hS : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} ∈ 𝓝 (τ y) :=
    isOpen_multicone.mem_nhds hz.1
  have hφ : ContDiffAt ℝ 2 (fun z => Real.log (A.h z)) (τ y) :=
    ((hA.1.contDiffAt hS).of_le (WithTop.coe_le_coe.mpr le_top)).log (A.pos _ hz.1).ne'
  have hc : (potOf R A).φ x ∘ (R.A.chart j).symm = (fun z => Real.log (A.h z)) ∘ τ := rfl
  rw [hc, ReciprocityTheory.AnForm.levi_comp w hτ hφ]
  exact hA.2 _ hz _ (isConeTangent_lift R x j hy' w)

end StokesStep

open StokesStep in

theorem StokesStep.proof (hE : ResExistsStatement) : StokesStep.Statement := by
  intro K _ ι _ P n i A A' hP ha hA hA' hi
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨J, ⟨R⟩⟩ := exists_anLogRes hE hP
  set C := A'.tensor A.inv with hCdef
  have hC0 : C.a = 0 := by simp [C, HermLine.tensor, HermLine.inv, ha]
  have hCs : IsSmoothHerm C := hA'.1.mul (isSmoothHerm_inv hA.1)
  have hlogC : ∀ z, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      Real.log (C.h z) = Real.log (A'.h z) - Real.log (A.h z) := by
    intro z hz
    show Real.log (A'.h z * (A.h z)⁻¹) = _
    rw [Real.log_mul (A'.pos z hz).ne' (inv_ne_zero (A.pos z hz).ne'), Real.log_inv]
    ring
  let L : ℕ → Fin (m + 1) → HermLine ι := fun l j => if j.val < l then A' else A
  have hpot : ∀ l, stokesMixPot A A' (m + 1) l = pot (L l) := by
    intro l
    funext j z
    simp only [stokesMixPot, pot, L]
    split_ifs <;> rfl
  have hLsp : ∀ l j, IsSemipositiveH P (L l j) := fun l j => by
    simp only [L]
    split_ifs
    exacts [hA', hA]
  have hL : ∀ l j, IsSmoothHerm (L l j) := fun l j => (hLsp l j).1
  have hs := isSectionOn_inv_one hP.2.1.1 hC0
  set v : R.X → ℝ := fun x => Real.log (C.h (R.lift x x)) with hvdef
  have key : ∀ l, ptsIntegral P (stokesMixPot A A' (m + 1) l)
      (fun z => Real.log (A'.h z) - Real.log (A.h z)) = mInt R.A (fun j => potOf R (L l j)) v := by
    intro l
    rw [ptsIntegral_congr_g P _ (g' := logNorm C.inv 1) fun z hz => by
      rw [logNorm_inv_one, hlogC z hz.1], hpot,
      ptsIntegral_eq_mInt' hE resBridge R hP (hL l) (isSmoothHerm_inv hCs) hs]
    congr 1
    funext x
    exact logNorm_inv_one C _
  rw [key, key]

  set σ : Equiv.Perm (Fin (m + 1)) := Equiv.swap 0 ⟨i, hi⟩ with hσ
  rw [← mIntSymm R.A (fun j => potOf R (L (i + 1) j)) σ v,
    ← mIntSymm R.A (fun j => potOf R (L i j)) σ v]
  set T : Fin m → LocPot R.X := fun k => potOf R (L i (σ k.succ)) with hT
  have hne : ∀ j : Fin (m + 1), j ≠ ⟨i, hi⟩ → L (i + 1) j = L i j := by
    intro j hj
    have hj' : j.val ≠ i := fun h => hj (Fin.ext h)
    simp only [L]
    by_cases h : j.val < i
    · rw [if_pos (by omega), if_pos h]
    · rw [if_neg (by omega), if_neg h]
  have hσs : ∀ k : Fin m, σ k.succ ≠ ⟨i, hi⟩ := by
    intro k hk
    rw [hσ, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right] at hk
    exact Fin.succ_ne_zero k hk
  have e1 : (fun j => potOf R (L (i + 1) j)) ∘ σ = Fin.cons (potOf R A') T := by
    funext k
    refine Fin.cases ?_ (fun k => ?_) k
    · simp [σ, L]
    · simp only [Function.comp_apply, Fin.cons_succ, T]
      rw [hne _ (hσs k)]
  have e0 : (fun j => potOf R (L i j)) ∘ σ = Fin.cons (potOf R A) T := by
    funext k
    refine Fin.cases ?_ (fun k => ?_) k
    · simp [σ, L]
    · simp only [Function.comp_apply, Fin.cons_succ, T]
  rw [e1, e0]

  have hv : R.A.Smooth v := smooth_diag R hCs hC0
  have hgerm : mInt R.A (Fin.cons (potOf R A') T) v =
      mInt R.A (Fin.cons (potOf R A + LocPot.ofFun v) T) v := by
    refine ReciprocityTheory.ChartRestriction.G.Geo.mInt_congr R.A (locDens_cons_congr R.A T fun j y hy => ?_) fun _ => rfl
    set x0 := (R.A.chart j).symm y
    filter_upwards [((R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x0)).mem_nhds
      ⟨hy, R.mem_U x0⟩] with y' hy'
    have hmc := (R.mem x0 _ hy'.2).1
    show Real.log (A'.h (R.lift x0 _)) = Real.log (A.h (R.lift x0 _)) + v _
    rw [hvdef]
    simp only
    rw [← h_eq_of_sameOrbit hC0 (R.compat x0 _ _ ⟨hy'.2, R.mem_U _⟩), hlogC _ hmc]
    ring
  have hpA : IsPotential R.A (potOf R A) := isPotential_potOf R hA.1
  have hpv : IsPotential R.A (LocPot.ofFun v) := isPotential_ofFun R.A v hv
  have hTp : ∀ k, IsPotential R.A (T k) := fun k => isPotential_potOf R (hL i _)
  have hTpsh : ∀ k, IsPsh R.A (T k) := fun k => isPsh_potOf R (hLsp i _)
  have hcons : ∀ Q, IsPotential R.A Q → ∀ k, IsPotential R.A ((Fin.cons Q T : Fin (m + 1) → LocPot R.X) k) :=
    fun Q hQ k => by
      refine Fin.cases ?_ (fun k => ?_) k
      · simpa using hQ
      · simpa using hTp k
  have hvc : Continuous v := PLC.continuous_of_smooth R.A hv
  have hadd := mIntAdd R.A (potOf R A) (LocPot.ofFun v) T hpA hpv hTp v
    (mIntegrableCont R.A _ (hcons _ hpA) v hvc) (mIntegrableCont R.A _ (hcons _ hpv) v hvc)
  have hneg := byPartsNonpos R.A v hv T hTp hTpsh
  rw [hgerm, hadd]
  linarith

end GroundTheory.Heights₂.Heights.LowerBoundFree
