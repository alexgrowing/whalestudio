import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.PullRep

def plU {X Y : Scheme.{0}} (f : Y ⟶ X) {U : X.Opens} {W : Y.Opens} (h : W ≤ f ⁻¹ᵁ U) :
    Γ(X, U)ˣ →* Γ(Y, W)ˣ := (res h).comp (pullU f U)

theorem res_plU {X Y : Scheme.{0}} (f : Y ⟶ X) {U : X.Opens} {W V : Y.Opens} (h : W ≤ f ⁻¹ᵁ U)
    (l : V ≤ W) (x : Γ(X, U)ˣ) : res l (plU f h x) = plU f (l.trans h) x :=
  Units.ext (resG_appLE f h l (x : Γ(X, U)))

theorem plU_res {X Y : Scheme.{0}} (f : Y ⟶ X) {U U' : X.Opens} {W : Y.Opens} (l : U' ≤ U)
    (h : W ≤ f ⁻¹ᵁ U') (x : Γ(X, U)ˣ) : plU f h (res l x) = plU f (h.trans (f.preimage_mono l)) x :=
  Units.ext (appLE_resG f l h (x : Γ(X, U)))

theorem plU_plU {X Y Z : Scheme.{0}} (g : Z ⟶ Y) (f : Y ⟶ X) {U : X.Opens} {V : Y.Opens} {W : Z.Opens}
    (h : V ≤ f ⁻¹ᵁ U) (h' : W ≤ g ⁻¹ᵁ V) (x : Γ(X, U)ˣ) :
    plU g h' (plU f h x) = plU (g ≫ f) (h'.trans (g.preimage_mono h)) x :=
  Units.ext (appLE_appLE g f h h' (x : Γ(X, U)))

theorem lbPull_g {X Y : Scheme.{0}} (B : LB X) (f : Y ⟶ X) (i j : PUnit → B.ι) :
    (B.pull f).g i j = plU f (le_inf (inf_le_left.trans (LB.wchart_le B (fun _ => f) i PUnit.unit))
      (inf_le_right.trans (LB.wchart_le B (fun _ => f) j PUnit.unit)) :
        (B.pull f).U i ⊓ (B.pull f).U j ≤ f ⁻¹ᵁ (B.U (i PUnit.unit) ⊓ B.U (j PUnit.unit)))
      (B.g (i PUnit.unit) (j PUnit.unit)) := by
  show ∏ k : PUnit, (plU f _ (B.g (i k) (j k))) ^ ((fun _ => (1 : ℤ)) k) = _
  rw [Fintype.prod_unique]
  exact zpow_one _

variable {n' m : ℕ} {n : Fin (m + 1) → ℕ}

abbrev qq (n' m : ℕ) (n : Fin (m + 1) → ℕ) : MP ℤ (m + 1) (consN n' n) ⟶ MP ℤ m n := qpSnd n' m n

theorem qq_str (n' m : ℕ) (n : Fin (m + 1) → ℕ) : qq n' m n ≫ mpStr ℤ m n = mpStr ℤ (m + 1) (consN n' n) :=
  qpSnd_str n' m n

def tl (c : ∀ k, Bk (consN n' n) k) : ∀ k, Bk n k := fun k => c k.succ

theorem mchart_le_pull (c : ∀ k, Bk (consN n' n) k) :
    mchart c ≤ qq n' m n ⁻¹ᵁ mchart (tl c) :=
  fun _ hx => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx k.succ

theorem pullDeg_zero (a : Fin (m + 1) → ℤ) : pullDeg (Fin.succ : Fin (m + 1) → Fin (m + 2)) a 0 = 0 := by
  unfold pullDeg
  rw [Function.extend_apply']
  · rfl
  · rintro ⟨k, hk⟩
    exact Fin.succ_ne_zero k hk

theorem pullDeg_succ (a : Fin (m + 1) → ℤ) (k : Fin (m + 1)) :
    pullDeg (Fin.succ : Fin (m + 1) → Fin (m + 2)) a k.succ = a k :=
  (Fin.succ_injective _).extend_apply _ _ _

theorem blockUnit_succ {k : Fin (m + 1)} (i j : Bk n k) {W : (MP ℤ (m + 1) (consN n' n)).Opens}
    {W₀ : (MP ℤ m n).Opens} (h : W ≤ prB (consN n' n) k.succ ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j))
    (H : W ≤ qq n' m n ⁻¹ᵁ W₀) (h₀ : W₀ ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j)) :
    blockUnit (n := consN n' n) (k := k.succ) i j h = plU (qq n' m n) H (blockUnit i j h₀) :=
  (plU_plU (qq n' m n) (prB n k) h₀ H _).symm

theorem prod_blockUnit (c c' : ∀ k, Bk (consN n' n) k) {W : (MP ℤ (m + 1) (consN n' n)).Opens}
    {V : (MP ℤ m n).Opens} (HV : W ≤ qq n' m n ⁻¹ᵁ V) (hW : W ≤ mchart c ⊓ mchart c')
    (hV : V ≤ mchart (tl c) ⊓ mchart (tl c')) (a : Fin (m + 1) → ℤ) :
    ∏ k, blockUnit (c k) (c' k) (fun _ hx => ⟨mchart_le c k (hW hx).1, mchart_le c' k (hW hx).2⟩ :
        W ≤ prB (consN n' n) k ⁻¹ᵁ (chart ℤ (consN n' n k) (c k) ⊓ chart ℤ (consN n' n k) (c' k))) ^
          pullDeg (Fin.succ : Fin (m + 1) → Fin (m + 2)) a k =
      plU (qq n' m n) HV (∏ k, blockUnit (tl c k) (tl c' k)
        (fun _ hx => ⟨mchart_le (tl c) k (hV hx).1, mchart_le (tl c') k (hV hx).2⟩ :
          V ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (tl c k) ⊓ chart ℤ (n k) (tl c' k))) ^ a k) := by
  rw [map_prod, Fin.prod_univ_succ, pullDeg_zero, zpow_zero, one_mul]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow, pullDeg_succ]
  exact congrArg (· ^ a k) (blockUnit_succ _ _ _ HV _)

theorem prod_norm_pull (z : (Σ k, Bk (consN n' n) k) → ℂ) (c : ∀ k, Bk (consN n' n) k) (a : Fin (m + 1) → ℤ) :
    ∏ k, ‖z ⟨k, c k⟩‖ ^ pullDeg (Fin.succ : Fin (m + 1) → Fin (m + 2)) a k =
      ∏ k, ‖z (sv n' n ⟨k, tl c k⟩)‖ ^ a k := by
  rw [Fin.prod_univ_succ, pullDeg_zero, zpow_zero, one_mul]
  simp only [pullDeg_succ]
  rfl

theorem isUnder_map {y' : CxPts (mpStr ℤ (m + 1) (consN n' n)) σ₀} {z' : (Σ k, Bk (consN n' n) k) → ℂ}
    (h : IsUnder y' z') :
    IsUnder (Points.PtsOver.map (qq n' m n) (qq_str n' m n) _ y') (fun p => z' (sv n' n p)) := by
  intro k i
  refine ⟨(h k.succ i).1, fun j hy => ?_⟩
  have e := (h k.succ i).2 j hy
  calc CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n k i) (pullRatio (prB n k) _ i le_rfl j)
        (Points.PtsOver.map (qq n' m n) (qq_str n' m n) _ y')
      = CxPts.ev (mpStr ℤ (m + 1) (consN n' n)) σ₀ (qq n' m n ⁻¹ᵁ blockChart n k i)
          ((qq n' m n).app _ (pullRatio (prB n k) _ i le_rfl j)) y' :=
        (ev_app (qq n' m n) (qq_str n' m n) _ _ y').symm
    _ = CxPts.ev (mpStr ℤ (m + 1) (consN n' n)) σ₀ (qq n' m n ⁻¹ᵁ blockChart n k i)
          (pullRatio (qq n' m n ≫ prB n k) _ i le_rfl j) y' := by
        rw [Scheme.Hom.app_eq_appLE, appLE_pullRatio]
    _ = _ := e

theorem ev_plU {y' : CxPts (mpStr ℤ (m + 1) (consN n' n)) σ₀} {U : (MP ℤ m n).Opens}
    {W : (MP ℤ (m + 1) (consN n' n)).Opens} (H : W ≤ qq n' m n ⁻¹ᵁ U)
    (hy : y' ∈ ptsIn (mpStr ℤ (m + 1) (consN n' n)) σ₀ W) (x : Γ(MP ℤ m n, U)ˣ) :
    CxPts.ev (mpStr ℤ (m + 1) (consN n' n)) σ₀ W (plU (qq n' m n) H x : Γ(MP ℤ (m + 1) (consN n' n), W)) y' =
      CxPts.ev (mpStr ℤ m n) σ₀ U (x : Γ(MP ℤ m n, U)) (Points.PtsOver.map (qq n' m n) (qq_str n' m n) _ y') :=
  (ev_res H hy _).trans (ev_app (qq n' m n) (qq_str n' m n) U _ y')

end GlobalTheory.CompanionTheory.MPDict.PullRep

namespace GlobalTheory.CompanionTheory.MPDict

open GlobalTheory.CompanionTheory.MPDict.PullRep

theorem isHermRep_pull (n' m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n)) (A : Geo.HermLine (Bk n))
    (hM : IsHermRep M A) :
    IsHermRep (m := m + 1) (n := consN n' n) (M.pull (qpSnd n' m n) (qpSnd_str n' m n)) (pullLine n' A) := by
  show IsHermRep (M.pull (qq n' m n) (qq_str n' m n)) (pullLine n' A)
  obtain ⟨u, h1, h2, h3⟩ := hM
  have Hu : ∀ (i : PUnit → M.B.ι) (c : ∀ k, Bk (consN n' n) k),
      (M.pull (qq n' m n) (qq_str n' m n)).B.U i ⊓ mchart c ≤
        qq n' m n ⁻¹ᵁ (M.B.U (i PUnit.unit) ⊓ mchart (tl c)) := fun i c x hx =>
    ⟨LB.wchart_le M.B (fun _ => qq n' m n) i PUnit.unit hx.1, mchart_le_pull c hx.2⟩
  refine ⟨fun i c => plU (qq n' m n) (Hu i c) (u (i PUnit.unit) (tl c)), ?_, ?_, ?_⟩
  · intro i j c
    have HV : (M.pull (qq n' m n) (qq_str n' m n)).B.U i ⊓
        (M.pull (qq n' m n) (qq_str n' m n)).B.U j ⊓ mchart c ≤
          qq n' m n ⁻¹ᵁ (M.B.U (i PUnit.unit) ⊓ M.B.U (j PUnit.unit) ⊓ mchart (tl c)) := fun x hx =>
      ⟨⟨LB.wchart_le M.B (fun _ => qq n' m n) i PUnit.unit hx.1.1,
        LB.wchart_le M.B (fun _ => qq n' m n) j PUnit.unit hx.1.2⟩, mchart_le_pull c hx.2⟩
    have e := congrArg (plU (qq n' m n) HV) (h1 (i PUnit.unit) (j PUnit.unit) (tl c))
    rw [map_mul, plU_res, plU_res, plU_res] at e
    exact (res_plU _ _ _ _).trans (e.trans (congrArg₂ (· * ·)
      ((congrArg (Semi.res _) (lbPull_g M.B (qq n' m n) i j)).trans (res_plU _ _ _ _)).symm
      (res_plU _ _ _ _).symm))
  · intro i c c'
    have HV : (M.pull (qq n' m n) (qq_str n' m n)).B.U i ⊓
        (mchart c ⊓ mchart c') ≤ qq n' m n ⁻¹ᵁ (M.B.U (i PUnit.unit) ⊓ (mchart (tl c) ⊓ mchart (tl c'))) :=
      fun x hx => ⟨LB.wchart_le M.B (fun _ => qq n' m n) i PUnit.unit hx.1, mchart_le_pull c hx.2.1,
        mchart_le_pull c' hx.2.2⟩
    have e := congrArg (plU (qq n' m n) HV) (h2 (i PUnit.unit) (tl c) (tl c'))
    rw [map_mul, plU_res, plU_res] at e
    rw [res_plU, res_plU]
    refine e.trans (congrArg₂ (· * ·) rfl ?_)
    exact (prod_blockUnit c c' HV (fun _ hx => hx.2) (fun _ hx => hx.2) A.a).symm
  · intro i c y z hz hy
    have hy0 : Points.PtsOver.map (qq n' m n) (qq_str n' m n) _ y ∈
        ptsIn (mpStr ℤ m n) σ₀ (M.B.U (i PUnit.unit) ⊓ mchart (tl c)) :=
      Points.le_preimage_comp y.1 (qq n' m n) (Hu i c) hy
    have e := h3 (i PUnit.unit) (tl c) _ _ (isUnder_map hz) hy0
    have ev_e := ev_plU (Hu i c) hy (u (i PUnit.unit) (tl c))
    have φ_e := (M.φ σ₀).pull_φ (qq n' m n) (qq_str n' m n) i y
    show A.h (fun p => z (sv n' n p)) = _
    rw [e]
    refine congrArg₂ (· * ·) (congrArg₂ (· * ·) (prod_norm_pull z c A.a).symm ?_) ?_
    · exact congrArg (‖·‖) ev_e.symm
    · exact congrArg (fun t => Real.exp (t / 2)) φ_e.symm

end GlobalTheory.CompanionTheory.MPDict
