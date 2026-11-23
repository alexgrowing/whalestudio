import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.A3oneOfFactSplitOfCountCont
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedA
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.PowRep

open GlobalTheory.CuspDim.IsoPow
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet (powLine powLine_a constLine)

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem h_powLine {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (A : Geo.HermLine ι) (r : ℕ)
    (z : (Σ k, ι k) → ℂ) : (powLine A r).h z = A.h z ^ r := by
  induction r with
  | zero => simp [powLine, constLine]
  | succ r ih => simp [powLine, Geo.HermLine.tensor, ih, pow_succ]

theorem frame_pow {Z : Scheme.{0}} (B : LB Z) (r : ℕ) (V : Z.Opens) (u : ∀ i, Γ(Z, B.U i ⊓ V)ˣ)
    (h : ∀ i j, Semi.res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          B.U i ⊓ B.U j ⊓ V ≤ B.U j ⊓ V) (u j) =
        Semi.res (inf_le_left : B.U i ⊓ B.U j ⊓ V ≤ B.U i ⊓ B.U j) (B.g i j) *
          Semi.res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            B.U i ⊓ B.U j ⊓ V ≤ B.U i ⊓ V) (u i))
    (j j' : PUnit.{1} → B.ι) :
    Semi.res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        (lbPow B r).U j ⊓ (lbPow B r).U j' ⊓ V ≤ (lbPow B r).U j' ⊓ V)
        (Semi.res (inf_le_inf_right V (pow_le r j')) (u (j' PUnit.unit)) ^ r) =
      Semi.res (inf_le_left : (lbPow B r).U j ⊓ (lbPow B r).U j' ⊓ V ≤ (lbPow B r).U j ⊓ (lbPow B r).U j')
          ((lbPow B r).g j j') *
        Semi.res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          (lbPow B r).U j ⊓ (lbPow B r).U j' ⊓ V ≤ (lbPow B r).U j ⊓ V)
          (Semi.res (inf_le_inf_right V (pow_le r j)) (u (j PUnit.unit)) ^ r) := by
  have hW : (lbPow B r).U j ⊓ (lbPow B r).U j' ⊓ V ≤
      B.U (j PUnit.unit) ⊓ B.U (j' PUnit.unit) ⊓ V :=
    inf_le_inf_right V (inf_le_inf (pow_le r j) (pow_le r j'))
  have e := congrArg (fun t => Semi.res hW t ^ r) (h (j PUnit.unit) (j' PUnit.unit))
  simp only [map_mul, mul_pow, GlobalTheory.CuspDim.IsoPow.res_res] at e
  rw [res_pow_g]
  simp only [map_pow, GlobalTheory.CuspDim.IsoPow.res_res]
  exact e

theorem res_blockUnit {k : Fin (m + 1)} (i j : Bk n k) {W W' : (MP ℤ m n).Opens}
    (h : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j)) (h' : W' ≤ W) :
    Semi.res h' (blockUnit i j h) = blockUnit i j (h'.trans h) :=
  GlobalTheory.CuspDim.IsoPow.res_res _ _ _

theorem ev_res_pow {p : (MP ℤ m n) ⟶ Sp ℤ} {W U : (MP ℤ m n).Opens} (h : W ≤ U) (v : Γ(MP ℤ m n, U)ˣ) (r : ℕ)
    {y : CxPts p σ₀} (hy : y ∈ ptsIn p σ₀ W) :
    CxPts.ev p σ₀ W ((Semi.res h v ^ r : Γ(MP ℤ m n, W)ˣ) : Γ(MP ℤ m n, W)) y =
      CxPts.ev p σ₀ U (v : Γ(MP ℤ m n, U)) y ^ r := by
  rw [Units.val_pow_eq_pow_val, CxPts.ev_eq hy, map_pow, ← CxPts.ev_eq hy]
  exact congrArg (· ^ r) (CxPts.ev_res h hy _)

theorem chart_pow {B : LB (MP ℤ m n)} (A : Geo.HermLine (Bk n)) (r : ℕ) (j : PUnit.{1} → B.ι) (c c' : ∀ k, Bk n k)
    (v : Γ(MP ℤ m n, B.U (j PUnit.unit) ⊓ mchart c)ˣ) (v' : Γ(MP ℤ m n, B.U (j PUnit.unit) ⊓ mchart c')ˣ)
    (h : Semi.res (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
          B.U (j PUnit.unit) ⊓ (mchart c ⊓ mchart c') ≤ B.U (j PUnit.unit) ⊓ mchart c) v =
        Semi.res (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
          B.U (j PUnit.unit) ⊓ (mchart c ⊓ mchart c') ≤ B.U (j PUnit.unit) ⊓ mchart c') v' *
        ∏ k, blockUnit (c k) (c' k) (fun _ hx =>
          ⟨mchart_le c k hx.2.1, mchart_le c' k hx.2.2⟩ :
            B.U (j PUnit.unit) ⊓ (mchart c ⊓ mchart c') ≤
              prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k))) ^ A.a k) :
    Semi.res (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
        (lbPow B r).U j ⊓ (mchart c ⊓ mchart c') ≤ (lbPow B r).U j ⊓ mchart c)
        (Semi.res (inf_le_inf_right _ (pow_le r j)) v ^ r) =
      Semi.res (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
        (lbPow B r).U j ⊓ (mchart c ⊓ mchart c') ≤ (lbPow B r).U j ⊓ mchart c')
        (Semi.res (inf_le_inf_right _ (pow_le r j)) v' ^ r) *
      ∏ k, blockUnit (c k) (c' k) (fun _ hx =>
        ⟨mchart_le c k hx.2.1, mchart_le c' k hx.2.2⟩ :
          (lbPow B r).U j ⊓ (mchart c ⊓ mchart c') ≤
            prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k))) ^ (powLine A r).a k := by
  have hW : (lbPow B r).U j ⊓ (mchart c ⊓ mchart c') ≤ B.U (j PUnit.unit) ⊓ (mchart c ⊓ mchart c') :=
    inf_le_inf_right _ (pow_le r j)
  have e := congrArg (fun t => Semi.res hW t ^ r) h
  simp only [map_mul, mul_pow, map_prod, map_zpow, res_blockUnit, GlobalTheory.CuspDim.IsoPow.res_res] at e
  simp only [map_pow, GlobalTheory.CuspDim.IsoPow.res_res]
  refine e.trans (congrArg _ ?_)
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [powLine_a, mul_comm, zpow_mul, zpow_natCast]
  exact congrArg (fun t => (t ^ A.a k) ^ r) (res_blockUnit _ _ _ _)

theorem isHermRep_pow (m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n)) (A : Geo.HermLine (Bk n)) (r : ℕ)
    (hM : IsHermRep M A) : IsHermRep (M.pow r) (powLine A r) := by
  obtain ⟨u, h₁, h₂, h₃⟩ := hM
  refine ⟨fun (j : PUnit.{1} → M.B.ι) c =>
    Semi.res (inf_le_inf_right _ (pow_le (B := M.B) r j)) (u (j PUnit.unit) c) ^ r, ?_, ?_, ?_⟩
  · intro j j' c
    exact frame_pow M.B r (mchart c) (fun i => u i c) (fun i j => h₁ i j c) j j'
  · intro j c c'
    exact chart_pow A r j c c' _ _ (h₂ (j PUnit.unit) c c')
  · intro (j : PUnit.{1} → M.B.ι) c y z hz hy
    have hy' : y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U (j PUnit.unit) ⊓ mchart c) :=
      CxPts.ptsIn_mono (inf_le_inf_right _ (pow_le (B := M.B) r j)) hy
    have e := h₃ (j PUnit.unit) c y z hz hy'
    have eφ : ((M.pow r).φ σ₀).φ j y = r * (M.φ σ₀).φ (j PUnit.unit) y := by
      exact ((M.φ σ₀).zpow_φ r j y).trans (by simp)
    have ev := ev_res_pow (p := mpStr ℤ m n) (inf_le_inf_right (mchart c) (pow_le (B := M.B) r j))
      (u (j PUnit.unit) c) r hy
    beta_reduce
    rw [h_powLine, e, eφ, show CxPts.ev (mpStr ℤ m n) σ₀ ((M.pow r).B.U j ⊓ mchart c) _ y = _ from ev, norm_pow, mul_pow, mul_pow, ← Finset.prod_pow,
      ← Real.exp_nat_mul, mul_div_assoc]
    congr 2
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [powLine_a, mul_comm, zpow_mul, zpow_natCast]

end GlobalTheory.CompanionTheory.MPDict.PowRep
