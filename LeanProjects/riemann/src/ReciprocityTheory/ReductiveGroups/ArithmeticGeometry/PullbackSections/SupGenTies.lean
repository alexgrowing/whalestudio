import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaValC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ModelLat

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

def SupAtUnitSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T), GamAt T → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j),
    SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → LastPos (T.Q.Dw j) (wtA w) →
    ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ f ∈ T.C j w,
      0 < supN (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f) →
      ∃ (k : (T.U j σ).Comp) (xf : ((T.U j σ).X k).dom),
        (∀ τ' i', ‖dmin ((T.U j σ).X k).Gm xf.1 τ' i'‖ = 1) ∧ ((T.U j σ).X k).IsOrtho xf.1 ∧
        supN (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f) ≤
          2 * ‖toC (evR (T.Q.Xo j) T.Q.c f ((T.U j σ).un k xf))‖ ∧
        0 < ((T.U j σ).X k).firstMinimumSq xf.1 ∧ Real.log (1 / ((T.U j σ).X k).firstMinimumSq xf.1) ≤ 44 * large₂.sc.L

def TorusFrameSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ →
    ∀ (k : (T.U j σ).Comp) (xf : ((T.U j σ).X k).dom), ((T.U j σ).X k).IsOrtho xf.1 →
    ∃ (W : UnfAt (T.U j σ) k xf) (Wu : UnitAt W) (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt ((T.U j σ).X k) xf.1)
      (L : (Fin W.g → ℂ) →ₗ[ℂ] ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim),
      TorusPins W Wu A L ∧ A.T.l2 1 A.s = 1 ∧ (∀ i, ‖L (Pi.single i 1)‖ ≤ 1) ∧
      Fintype.card (ReciprocityTheory.ChartRestriction.G.I2.Idx A.T.dim) ≤ D.R.f * D.R.r

def RepSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (x : (T.Q.Dw j).La),
    ∃ x2 : (T.Q.Dw j).La,
      x2 ∈ (Ideal.span {(2 : 𝓞 D.host.E)} *
          (T.Q.l.Mb.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) ^ 2) •
            (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw j).La) ∧
      x2 - x ∈ T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw j).La)

def LieFacSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j),
    SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L →
      Real.log (lieFac (T.Q.Dw j) (xiR D) (wtA w)) ≤ 2 * large₂.sc.L * absA w

def DegSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j)
    (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F), P ∈ harmA T.Q.c (wtA w) w.n → (P.totalDegree : ℝ) ≤ absA w

def CuspTieSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j),
    LastPos (T.Q.Dw j) (wtA w) →
    ∀ (x : Fin w.n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F), P ∈ harmA T.Q.c (wtA w) w.n →
    ∀ f : T.R j, IsThRule (T.Q.Xo j) T.Q.c (T.nab j) x P f → f ∈ T.C j w

def DimPosSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j), 1 ≤ D.R.f ∧ 1 ≤ D.R.r ∧ 1 ≤ T.Q.l.M

def Lam1RowSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T), GamAt T → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j),
    SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → LastPos (T.Q.Dw j) (wtA w) →
    ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ f ∈ T.C j w, ∀ (k : (T.U j σ).Comp),
    ∀ z0 ∈ ((T.U j σ).X k).dom,
      (∀ x ∈ ((T.U j σ).X k).dom,
        ((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) x ≤
          2 * ((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) z0) →
      0 < ((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) z0 →
      0 < ((T.U j σ).X k).firstMinimumSq z0 ∧ Real.log (1 / ((T.U j σ).X k).firstMinimumSq z0) ≤ 44 * large₂.sc.L

structure XExt {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) where
  k0 : ℝ
  minWeight_pos : 0 < k0
  k0_le : k0 ≤ 2
  ξ0_abs : ∀ τ : X.Ψ, ‖τ.1 X.ξ0‖ = k0 / 2
  EF_int : ∀ x ∈ X.Λ, ∀ y ∈ X.Λ, ∃ k : ℤ, EFf X.ξ0 X.Gm x y = k
  EF_perf : ∀ φ : X.Λ →+ ℤ, ∃ x ∈ X.Λ, ∀ y : X.Λ, (φ y : ℚ) = EFf X.ξ0 X.Gm x y
  L' : Submodule (𝓞 E) (Fin r → E)
  L'_fg : L'.FG
  L'_int : ∀ x ∈ L', ∀ y ∈ L', IsIntegral ℤ (herm X.Gm x y)
  L'_dual : ∀ x, (∀ y ∈ L', IsIntegral ℤ (herm X.Gm x y)) → x ∈ L'
  NA : ℕ
  NC : ℕ
  NA_pos : 0 < NA
  NC_pos : 0 < NC
  NA_sub : ∀ x ∈ X.Λ, (NA : E) • x ∈ L'
  NC_sub : ∀ x ∈ L', (NC : E) • x ∈ X.Λ
  g : ℕ
  g_pos : 0 < g
  cong : ∀ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ →
    (∀ x ∈ X.Λ, ∃ y ∈ X.Λ, Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) x - x = (g : E) • y) → γ ∈ X.Γ

def XExt.toX {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} (e : XExt X) :
    DataX E r :=
  ⟨X, e.k0, e.minWeight_pos, e.k0_le, e.ξ0_abs, e.EF_int, e.EF_perf, e.L', e.L'_fg, e.L'_int, e.L'_dual, e.NA, e.NC,
    e.NA_pos, e.NC_pos, e.NA_sub, e.NC_sub, e.g, e.g_pos, e.cong⟩

def ModelDataXSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T), GamAt T → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j),
    SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n →
    ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ k : (T.U j σ).Comp,
    ∃ (e : XExt ((T.U j σ).X k)) (M wg : ℝ), 0 < M ∧ Real.log M ≤ 23 * large₂.sc.L ∧ 0 < wg ∧
      (∑ τ, ((T.U j σ).X k).spread (laU (T.U j σ) (wtA w) w.n k) τ) ≤ wg ∧
      (∀ v ∈ e.L', herm ((T.U j σ).X k).Gm v v = 0 → ∀ b : D.host.E, cc b = b → IsIntegral ℤ b →
        ∃ γ ∈ ((T.U j σ).X k).Γ, ((T.U j σ).X k).χ (laU (T.U j σ) (wtA w) w.n k) γ = 1 ∧
          ∀ τ : ((T.U j σ).X k).Ψ, (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 =
            ((T.U j σ).X k).flowMat v τ ((M : ℂ) * τ.1 b)) ∧
      Real.log ((fdeg D.host.E : ℝ) * wg + 2) ≤ 9 * large₂.sc.L ∧
      (∃ B : ℝ, Real.log B ≤ 3 * large₂.sc.L ∧ ∀ v ∈ ((T.U j σ).X k).Λ, v ≠ 0 →
        ∃ a : D.host.E, a ≠ 0 ∧ a • v ∈ e.L' ∧ ∀ τ : D.host.E →+* ℂ, ‖τ a‖ ≤ B) ∧
      Real.log (1 / e.k0) ≤ 3 * large₂.sc.L

def TorusMatchSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ →
    ∀ (k : (T.U j σ).Comp) (xf : ((T.U j σ).X k).dom), ((T.U j σ).X k).IsOrtho xf.1 →
    ∃ (W : UnfAt (T.U j σ) k xf) (Wu : UnitAt W) (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt ((T.U j σ).X k) xf.1)
      (L : (Fin W.g → ℂ) ≃ₗ[ℂ] ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim), TorusPins W Wu A L.toLinearMap

def UnitHmSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ →
    ∀ (k : (T.U j σ).Comp) (xf : ((T.U j σ).X k).dom), ((T.U j σ).X k).IsOrtho xf.1 →
    ∀ (W : UnfAt (T.U j σ) k xf) (Wu : UnitAt W) (i : Fin W.g),
      (hermForm Wu.Hm (Pi.single i 1) (Pi.single i 1)).re ≤ 1

end ReciprocityTheory.ChartRestriction.G.PullbackSections
