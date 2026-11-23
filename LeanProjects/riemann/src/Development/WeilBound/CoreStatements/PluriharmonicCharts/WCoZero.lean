import Mathlib
import Development.WeilBound.CoreStatements.PluriharmonicCharts.PullDegSome
import Development.WeilBound.CoreStatements.PluriharmonicCharts.XCWArith
import Development.WeilBound.CoreStatements.PluriharmonicCharts.XCWLine
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section
namespace PositivityTheory.Xgp.c_algsq

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

variable {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem wCo_zero (M : FlagModel y Ψ N j) {p : Ψ × Fin N} {k₀ : K} (hk : M.blk p = some k₀) (ca cb : Fin N)
    (m : ι k₀) : M.wCo p k₀ ca cb 0 ⟨none, m⟩ = M.wCo p k₀ ca cb 0 ⟨some k₀, m⟩ := by
  simp only [FlagModel.wCo, Matrix.single_zero, add_zero, mul_one]
  rw [M.y_step p k₀ hk m, map_sum]
  exact Finset.sum_congr rfl fun I _ => by rw [map_mul, CPts.minorIJ_map]

def mkAlg (M : FlagModel y Ψ N j) {d : ℕ} {τ : Ψ} {a b : Fin N} {k₀ : K} {ca cb : Fin N} (hb : (b : ℕ) = a + 1)
    (hab : (b : ℕ) < j ∨ j ≤ (a : ℕ)) (hk : M.blk (τ, a) = some k₀) (hca : (ca : ℕ) = lastCol N j a)
    (hcb : (cb : ℕ) = ca + 1) (hy : IsArithVar (mCoordIdeal y) (d + 2)) (xi2 : K → ℤ) (hxi : xi2 k₀ = -2)
    (g h : MRing fun o : Option K => ι (o.getD k₀)) (dg dh : Option K → ℕ) (hg : IsMultiHomog g dg)
    (hh : IsMultiHomog h dh) (hgn : g ∉ mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X))
    (hhn : h ∉ mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X))
    (hdeg : ∀ o : Option K, (dg o : ℤ) - dh o = o.elim 1 fun k => -xi2 k - (if M.blk (τ, a) = some k then 1 else 0))
    (hdiv : divCycle (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) g =
      divCycle (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) h +
        Finsupp.single (mCoordIdeal (M.wCo (τ, a) k₀ ca cb 0)) 1) :
    AlgSq (mCoordIdeal y) d k₀ xi2 where
  arithY := hy
  xi_two_base_eq_neg_two := hxi
  KW := Option K
  ιW := fun o => ι (o.getD k₀)
  PW := mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)
  arithW := (t_c_w_arith K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hab hk hca hcb hy).1
  κ := ![some, κ₁ k₀]
  v := ![v₀ k₀, v₁ k₀]
  block := Fin.forall_fin_two.2 ⟨Pts.isBlockMap_v₀ k₀, isBlockMap_v₁ k₀⟩
  image := Fin.forall_fin_two.2 ⟨(t_c_w_arith K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hab hk hca hcb hy).2.2.2.1,
    (t_c_w_arith K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hab hk hca hcb hy).2.2.2.2 (v₁ k₀) (fun _ h => v₁_ne h)
      (v₁_self k₀)⟩
  same p hp := (v₁_ne hp).symm
  new := by
    rintro ⟨k, hk'⟩
    have : some k = κ₁ k₀ k₀ := hk'
    rw [κ₁_self] at this
    cases this
  all k' := by
    cases k' with
    | none => exact Or.inr (κ₁_self k₀).symm
    | some k => exact Or.inl ⟨k, rfl⟩
  fibre_line := t_c_w_line K ι Φ y Ψ N j M τ a b k₀ ca cb hb hab hk hca hcb
  Δ := mCoordIdeal (M.wCo (τ, a) k₀ ca cb 0)
  arithΔ := (t_c_w_arith K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hab hk hca hcb hy).2.1
  PW_le := (t_c_w_arith K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hab hk hca hcb hy).2.2.1
  diag i i' := by
    show mConeMap _ (X (v₀ k₀ ⟨k₀, i⟩) * X (v₁ k₀ ⟨k₀, i'⟩) - X (v₀ k₀ ⟨k₀, i'⟩) * X (v₁ k₀ ⟨k₀, i⟩)) = 0
    rw [v₁_self, v₁_self]
    simp only [mConeMap, map_sub, map_mul, aeval_X, v₀, wCo_zero M hk]
    ring
  g := g
  h := h
  dg := dg
  dh := dh
  g_deg := hg
  h_deg := hh
  g_nmem := hgn
  h_nmem := hhn
  deg_eq o := by
    show _ = -(pullDeg some xi2 o + pullDeg (κ₁ k₀) xi2 o)
    rw [hdeg, pullDeg_some, pullDeg_κ₁]
    cases o with
    | none => simp [hxi]
    | some k =>
      simp only [Option.elim, hk, Option.some.injEq]
      by_cases e : k = k₀
      · subst e; simp [hxi]
      · rw [if_neg e, if_neg (Ne.symm e)]; ring
  div_eq := hdiv

end PositivityTheory.Xgp.c_algsq
