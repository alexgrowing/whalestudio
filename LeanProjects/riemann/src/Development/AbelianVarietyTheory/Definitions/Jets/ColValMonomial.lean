import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsWeightBasisFiltration
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCHyp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExpF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.ThmASt

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS FB ev Dof)
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.FamGerm

structure Pt1 (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (F : Type) [Field F] [Algebra (FractionRing V) F] where
  ϖ : V
  hϖ : Irreducible ϖ
  complete : IsAdicComplete (maximalIdeal V) V
  t : SAB H (Sp V)
  P : PELUnif (maximalIdeal V) t
  tors : P.TorsionIso
  Q : P.D.toPre.X → ℤ
  hQ : QForm.IsQ P.D.toPre ϖ Q
  v : AddValuation F (WithTop ℚ)
  hv : ValOver ϖ F v
  d : ℕ
  x : JetSer.Fam t.G (Fin d)
  hx : Chart.IsUnivChart t.G d x
  j : P.U.LG.L.ι
  hj : ⊤ ≤ η[t.G].left ⁻¹ᵁ P.U.LG.L.U j
  u : letI := H.starRing; ∀ a : 𝓞 E, LB.Gen (LB.LinComb P.U.LG.L (rosatiφ t.G (t.act.act a) (t.act.act (star a))) rosatiε)
  hu : letI := H.starRing; ∀ a, JetSer.IsNormRos P.U.LG.L _ _ (u a)
  B : letI := H.starRing; FB V d (𝓞 E)
  hB : letI := H.starRing; JetSer.IsFBOf P.U.LG P.U.cubG t.act u x j B
  ρ : LB.Gen (LB.LinComb P.U.LG.L (JetSer.primφ (t.act.act H.w0)) JetSer.primε)
  hρ : ρ.IsGen
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {F : Type} [Field F] [Algebra (FractionRing V) F] (y : Pt1 E H V F)

def Pt1.Germ (q : ℕ) (s : Fam y.P.D.toPre F q) (f : PS F 1 y.d) : Prop :=
  ∃ (l : ℕ) (c : Fin l → F) (σ : Fin l → H0 y.P.U.LG.L q) (fi : Fin l → ∀ α, y.P.D.toPre.SecB q α) (g : Fin l → PS V 1 y.d) (r : PS V 1 y.d),
    (∀ i e, y.P.U.ExpandsAt e q (σ i) (fi i)) ∧
    (∀ α, GeneratorPullback.SecLin y.P.D.toPre.P.L (DegPre.famφ y.P.D.toPre F α) (DegPre.famε q) (s.s α) (y.P.D.toPre.famφB α) (DegPre.famε q)
      (fun i => fi i α) (DegPre.prB y.P.D.toPre F).left (fun i => scal (fst (TF (R := V) F) y.P.D.toPre.P.A).left (c i))) ∧
    JetSer.IsSer1 y.x _ (y.ρ.s (fun _ => y.j)).val r ∧
    (∀ i, ∃ S, JetSer.IsSer1 y.x _ ((σ i).f (fun _ => y.j)) S ∧ g i * r ^ q = S) ∧
    f = ∑ i, MvPowerSeries.C (c i) * MvPowerSeries.map (TWO.algVF (V := V) (F := F)) (g i)

def Pt1.Red (r : ℕ) (b : Module.Basis (Fin r) ℤ y.P.D.toPre.X) (Cc M₀ : ℝ) : Prop :=
  0 ≤ Cc ∧ 0 ≤ M₀ ∧ (∀ i, (y.Q (b i) : ℝ) ≤ Cc) ∧ ∀ i z, |(QForm.bOf y.P.D.toPre y.Q (b i) z : ℝ)| ≤ M₀ * y.Q z

def Pt1.Transl (q : ℕ) (c : 𝓞 E) (s h : Fam y.P.D.toPre F q) : Prop :=
  ∃ (p : QkPt y.P.D.toPre F q) (x : TFK (R := V) F ⟶ y.P.A.A)
    (w : LB.Gen (LB.LinComb y.P.D.toPre.P.L (DegPre.lineφ y.P.D.toPre F p.g.b) (DegPre.lineε q))) (ζ : F) (t' : Fam y.P.D.toPre F q),
    y.P.ToA F q p x ∧ (letI := H.starRing; x ≫ y.P.oA.act c = 1) ∧ w.IsGen ∧ ζ ≠ 0 ∧ FinOrd y.P.D F q p w ζ ∧
      PhiRel y.P.D.toPre F q p w s t' ∧ Fam.IsSmul y.P.D.toPre F ζ t' h

def Pt1.CharAt (a : 𝓞 E) (p : ℕ) {Λ : Type} (e : Λ → Fin y.d → TWO.Ov y.v) (yy : Λ → TWO.Ov y.v) : Prop :=
  letI := H.starRing
  ∃ (κ : (TFK (R := V) F ⟶ y.P.A.A) → Fˣ) (Z : Over (Spec (CommRingCat.of (TWO.Ov y.v)))) (jZ : Z.left ⟶ y.t.G.left) (k : Γ(Z.left, ⊤)),
    (∀ z z', z ≫ y.P.oA.act a = 1 → z' ≫ y.P.oA.act a = 1 → κ (z * z') = κ z * κ z') ∧
    IsFinite Z.hom ∧ Flat Z.hom ∧ IsReduced (Pdiv.specO (TWO.Ov y.v) F ⊗ Z).left ∧
    jZ ≫ y.t.G.hom = Z.hom ≫ Spec.map (CommRingCat.ofHom (TWO.fO y.v y.hϖ y.hv)) ∧
    jZ ≫ (y.t.act.act a).left = jZ ≫ (1 : y.t.G ⟶ y.t.G).left ∧
    (∀ (c : Pdiv.specO (TWO.Ov y.v) F ⟶ Z) (z : TFK (R := V) F ⟶ y.P.A.A),
      (z ≫ y.P.U.gen.inv).left ≫ pullback.fst y.t.G.hom (jK V) = c.left ≫ jZ → JetSer.fnVal c.left ⊤ k = (κ z : F)) ∧
    ∀ l, ∃ (w : Pdiv.specO (TWO.Ov y.v) (DualNumber (TWO.Ov y.v ⧸ Ideal.span {(p : TWO.Ov y.v)})) ⟶ Z)
      (φ : Chart.JetR V (Fin y.d) 1 →+* DualNumber (TWO.Ov y.v ⧸ Ideal.span {(p : TWO.Ov y.v)})),
      (∀ i, φ (Chart.zR 1 i) = TrivSqZeroExt.inr (Ideal.Quotient.mk _ (e l i))) ∧
      w.left ≫ jZ = Spec.map (CommRingCat.ofHom φ) ≫ (y.x 1).left ∧
      JetSer.fnVal w.left ⊤ k = 1 + TrivSqZeroExt.inr (Ideal.Quotient.mk _ (yy l))

def Pt1.colVal [Algebra V F] [CharZero F] (h : PS F 2 y.d) (q : ℕ) {Λ : Type} [Fintype Λ] (e : Λ → Fin y.d → F) {n : ℕ}
    (P : MvPolynomial (Λ × Fin n) F) (f : Fin n → PS F 1 y.d) : F :=
  letI := H.starRing
  ∑ mo ∈ P.support, P.coeff mo * ∏ b, y.B.nabVal F h H.w0 q (f b) e (MvPolynomial.monomial (colM mo b) 1)

def minorsP (k : Type) [CommRing k] {T : Type} [Fintype T] [DecidableEq T] {r : T → ℕ} {n : ℕ} (col : ∀ τ, Fin (r τ) → Fin n)
    (m : ∀ τ, Fin (r τ) → ℕ) : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k :=
  ∏ τ, ∏ s : Fin (r τ), (Matrix.of fun a i : Fin (s.val + 1) => (MvPolynomial.X ((⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)), col τ (Fin.castLE s.isLt i)) : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k)).det ^ m τ s

def GermExSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : Pt1 E H V F), letI := H.starRing; ∀ q : ℕ, 1 ≤ q → ∃ gm : Fam y.P.D.toPre F q →ₗ[F] PS F 1 y.d, ∀ s f, y.Germ q s f ↔ f = gm s

def GermValSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : Pt1 E H V F), letI := H.starRing; ∀ q : ℕ, 1 ≤ q → ∀ (s : Fam y.P.D.toPre F q) (f : PS F 1 y.d), y.Germ q s f → (∀ r : ℚ, (∀ χ, VGe y.P.D F y.v q χ (s.s χ) r) → ∀ mo, ((r : ℚ) : WithTop ℚ) ≤ y.v (MvPowerSeries.coeff mo f)) ∧ ∀ (χ : y.P.D.toPre.X) (x : F) (r r' : ℚ), Val0 y.P.D F q χ (s.s χ) x → y.v x = (r : ℚ) → r < r' → (∀ β, β ≠ χ → VGe y.P.D F y.v q β (s.s β) r') → y.v (MvPowerSeries.constantCoeff f) = (r : ℚ)

def JetsSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : Pt1 E H V F), letI := H.starRing; ∀ (r : ℕ) (b : Module.Basis (Fin r) ℤ y.P.D.toPre.X) (Cc M₀ : ℝ), y.Red r b Cc M₀ → ∀ q n : ℕ, 4 * n + 4 ≤ q → (n : ℝ) * M₀ < q → ∃ gm : ℚ, 0 ≤ gm ∧ (gm : ℝ) ≤ (n : ℝ) ^ 2 * Cc / q ∧ ∀ g : PS F 1 y.d, (∀ mo, 0 ≤ y.v (MvPowerSeries.coeff mo g)) → ∃ (s : Fam y.P.D.toPre F q) (f : PS F 1 y.d), NuGe y.P.D y.Q F y.v q s (-gm) ∧ y.Germ q s f ∧ (∀ mo, 0 ≤ y.v (MvPowerSeries.coeff mo f)) ∧ ∀ mo : Fin 1 × Fin y.d →₀ ℕ, mo.degree ≤ n → MvPowerSeries.coeff mo f = MvPowerSeries.coeff mo g

def PullGermSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : Pt1 E H V F), letI := H.starRing; ∀ (a : 𝓞 E) (N k : ℕ), 1 ≤ N → 4 ≤ k → a * star a = (N : 𝓞 E) → ∀ h : PS F 2 y.d, y.B.IsCanonGauge F h → ∃ (w : PS V 1 y.d) (κ : Vˣ), FB.toK F w = FB.expS F (ev (n := 1) ![y.B.actK F a] (y.B.hL F h H.w0) - (N : F) • y.B.hL F h H.w0) ∧ ∀ (s : Fam y.P.D.toPre F k) (s' : Fam y.P.D.toPre F (k * N)) (f : PS F 1 y.d), PullAl y.P.D F y.P.oD a k N s s' → y.Germ k s f → y.Germ (k * N) s' (MvPowerSeries.C (algebraMap V F κ) * (ev (n := 1) ![y.B.actK F a] f * FB.toK F w ^ k))

def EigGermSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : Pt1 E H V F), letI := H.starRing; ∀ (a : 𝓞 E) (p k : ℕ), p.Prime → 4 ≤ k → a * star a = (p : 𝓞 E) → ∀ (Λ : Type) (e : Λ → Fin y.d → TWO.Ov y.v) (yy : Λ → TWO.Ov y.v) (α : Λ → TWO.Ov y.v), (∀ l, α l ∈ Ideal.span {(p : TWO.Ov y.v)}) → (∀ l, (dAct F y.B a).mulVec (fun i => (e l i : F)) = (α l : F) • fun i => (e l i : F)) → y.CharAt a p e yy → ∀ (Dw : Datum H) (_I : TateIso Dw F (TFK (R := V) F ⟶ y.P.A.A) (fun a g => g ≫ y.P.oA.act a) (fun n g g' c => WeilIs y.P.A.A y.P.A.L n g g' (unitOn c))), Nat.Coprime p k → (∃ u u' : 𝓞 E, u * a + u' * star a = 1) → ∃ (pt : QkPt y.P.D.toPre F (k * p)) (x : TFK (R := V) F ⟶ y.P.A.A), y.P.ToA F (k * p) pt x ∧ x ≫ y.P.oA.act (star a) = 1 ∧ ∀ (w : LB.Gen (LB.LinComb y.P.D.toPre.P.L (DegPre.lineφ y.P.D.toPre F pt.g.b) (DegPre.lineε (k * p)))), w.IsGen → ∀ (s : Fam y.P.D.toPre F k) (s' t' : Fam y.P.D.toPre F (k * p)) (c : F), PullAl y.P.D F y.P.oD a k p s s' → PhiRel y.P.D.toPre F (k * p) pt w s' t' → (∀ χ, VGe y.P.D F y.v (k * p) χ ((c • t').s χ) 0) → ∀ (h : PS F 2 y.d) (ω : PS V 1 y.d), y.B.IsCanonGauge F h → FB.toK F ω = FB.expS F (ev (n := 1) ![y.B.actK F a] (y.B.hL F h H.w0) - (p : F) • y.B.hL F h H.w0) → ∀ f : PS F 1 y.d, y.Germ (k * p) (c • t') (f * FB.toK F ω ^ k) → ∀ l mo, y.v (p : F) ≤ y.v (MvPowerSeries.coeff mo (Dof (y.B.FK F) (fun i => (e l i : F)) f - MvPowerSeries.C (yy l : F) * f))

def CharExSt : Prop := ∀ (p : ℕ) [Fact p.Prime], Pdiv.ThmAGtStC p → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : Pt1 E H V F), letI := H.starRing; IsAdicComplete (Ideal.span {(p : TWO.Ov y.v)}) (TWO.Ov y.v) → ¬ IsUnit (p : TWO.Ov y.v) → ∀ a : 𝓞 E, a * star a = (p : 𝓞 E) → (∃ u u' : 𝓞 E, u * a + u' * star a = 1) → ∀ (T : Type) [Fintype T] [DecidableEq T] (rk : T → ℕ) (τ : T → 𝓞 E →+* TWO.Ov y.v) (e : (Σ t, Fin (rk t)) → Fin y.d → TWO.Ov y.v), (∀ (c : 𝓞 E) l, (dAct F y.B c).mulVec (fun i => (e l i : F)) = (τ l.1 c : F) • fun i => (e l i : F)) → (∀ t, τ t a ∈ Ideal.span {(p : TWO.Ov y.v)}) → (∀ t, ∃ lam : Fin (rk t) → Fin y.d → TWO.Ov y.v, ∀ i i', ∑ s, lam i s * e ⟨t, i'⟩ s = if i = i' then 1 else 0) → (∃ ε : T → 𝓞 E, ∀ t t', τ t' (ε t) - (if t = t' then 1 else 0) ∈ Ideal.span {(p : TWO.Ov y.v)}) → ∀ c : TWO.Ov y.v, (p - 1) • y.v (c : F) = y.v (p : F) → ∀ (n : ℕ) (col : ∀ t, Fin (rk t) → Fin n), (∀ t, Function.Injective (col t)) → ∃ yy : (Σ t, Fin (rk t)) × Fin n → TWO.Ov y.v, (∀ b, y.CharAt a p e (fun l => yy (l, b))) ∧ ∀ t (s : Fin (rk t)), y.v (((Matrix.of fun a i : Fin (s.val + 1) => yy (⟨t, Fin.castLE s.isLt a⟩, col t (Fin.castLE s.isLt i))).det : TWO.Ov y.v) : F) ≤ (s.val + 1) • y.v (c : F)

def RSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : Pt1 E H V F), letI := H.starRing; ∀ (Dw : Datum H) (_I : TateIso Dw F (TFK (R := V) F ⟶ y.P.A.A) (fun a g => g ≫ y.P.oA.act a) (fun n g g' c => WeilIs y.P.A.A y.P.A.L n g g' (unitOn c))), ∀ (r : ℕ) (b : Module.Basis (Fin r) ℤ y.P.D.toPre.X) (Cc M₀ : ℝ), y.Red r b Cc M₀ → ∀ (α : 𝓞 E) (N n D : ℕ), α * star α = (N : 𝓞 E) → (∃ u u' : 𝓞 E, u * α + u' * star α = 1) → IsUnit ((N : ℕ) : V) → 4 * D + 4 ≤ N → (D : ℝ) * M₀ < N → ∀ (θα : Fam y.P.D.toPre F (1 * N)), (∀ s, NuGe y.P.D y.Q F y.v (1 * N) s 0 → ∃ (m : ℕ) (t : Fin m → Fam y.P.D.toPre F (1 * N)) (c : Fin m → F), (∀ i, y.Transl (1 * N) (star α) θα (t i)) ∧ (∀ i, 0 ≤ y.v (c i)) ∧ s = ∑ i, c i • t i) → ∀ (h : PS F 2 y.d) (Λ : Type) [Fintype Λ] (e : Λ → Fin y.d → F) (I : Type) [Fintype I] [Nonempty I] (Pi : I → MvPolynomial (Λ × Fin n) F) (c : I → F), (∀ i, 0 ≤ y.v (c i)) → (∑ i, c i • Pi i).totalDegree ≤ D → ∀ (g : Fin n → PS F 1 y.d), (∀ b mo, 0 ≤ y.v (MvPowerSeries.coeff mo (g b))) → ∀ gm : ℚ, y.v (y.colVal h (1 * N) e (∑ i, c i • Pi i) g) = (gm : ℚ) → ∃ (i : I) (t : Fin n → Fam y.P.D.toPre F (1 * N)) (f : Fin n → PS F 1 y.d) (gm' : ℚ), (∀ b, y.Transl (1 * N) (star α) θα (t b) ∧ y.Germ (1 * N) (t b) (f b)) ∧ y.v (y.colVal h (1 * N) e (Pi i) f) = (gm' : ℚ) ∧ (gm' : ℝ) ≤ gm + (D : ℝ) ^ 2 * Cc / N

def LemmaBSt : Prop := ∀ (p : ℕ) [Fact p.Prime], Pdiv.ThmAGtStC p → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : Pt1 E H V F), letI := H.starRing; IsAdicComplete (Ideal.span {(p : TWO.Ov y.v)}) (TWO.Ov y.v) → ¬ IsUnit (p : TWO.Ov y.v) → ∀ (Dw : Datum H) (_I : TateIso Dw F (TFK (R := V) F ⟶ y.P.A.A) (fun a g => g ≫ y.P.oA.act a) (fun n g g' c => WeilIs y.P.A.A y.P.A.L n g g' (unitOn c))), ∀ (r : ℕ) (b : Module.Basis (Fin r) ℤ y.P.D.toPre.X) (Cc M₀ : ℝ), y.Red r b Cc M₀ → ∀ (a : 𝓞 E) (k : ℕ), a * star a = (p : 𝓞 E) → (∃ u u' : 𝓞 E, u * a + u' * star a = 1) → Nat.Coprime p k → ∀ (T : Type) [Fintype T] [DecidableEq T] (rk : T → ℕ) (τ : T → 𝓞 E →+* TWO.Ov y.v) (e : (Σ t, Fin (rk t)) → Fin y.d → TWO.Ov y.v), (∀ (c : 𝓞 E) l, (dAct F y.B c).mulVec (fun i => (e l i : F)) = (τ l.1 c : F) • fun i => (e l i : F)) → ∀ (isV : T → Prop) [DecidablePred isV], (∀ t, isV t → τ t a ∈ Ideal.span {(p : TWO.Ov y.v)}) → (∀ t, ¬ isV t → IsUnit (τ t a)) → (∃ lam : (Σ t, Fin (rk t)) → Fin y.d → TWO.Ov y.v, ∀ l l', ∑ s, lam l s * e l' s = if l = l' then 1 else 0) → (∃ ε : T → 𝓞 E, ∀ t t', τ t' (ε t) - (if t = t' then 1 else 0) ∈ Ideal.span {(p : TWO.Ov y.v)}) → ∀ (n : ℕ) (S : Finset (Fin n)) (col : ∀ t, Fin (rk t) → Fin n) (m : ∀ t, Fin (rk t) → ℕ), (∀ t, Function.Injective (col t)) → (∀ t i, col t i ∈ S ↔ isV t) → ∀ D : ℕ, D = ∑ t, ∑ s : Fin (rk t), m t s * (s.val + 1) → D < p - 1 → 4 * D + 4 ≤ k → (D : ℝ) * M₀ < k → ∀ h : PS F 2 y.d, y.B.IsCanonGauge F h → ∀ ep : ℚ, y.v (p : F) = (ep : ℚ) → ∃ (s : Fin n → Fam y.P.D.toPre F k) (s' t : Fin n → Fam y.P.D.toPre F (k * p)) (f : Fin n → PS F 1 y.d) (gm : ℚ), (∀ b, NuGe y.P.D y.Q F y.v (k) (s b) 0 ∧ PullAl y.P.D F y.P.oD a k p (s b) (s' b) ∧ y.Transl (k * p) (star a) (s' b) (t b) ∧ y.Germ (k * p) (t b) (f b)) ∧ y.v (y.colVal h (k * p) (fun l i => (e l i : F)) (minorsP F col m) f) = (gm : ℚ) ∧ (gm : ℝ) ≤ (D : ℝ) * ep / (p - 1) + S.card * r * Cc / (4 * k) + (D : ℝ) ^ 2 * Cc / k

def CorSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : Pt1 E H V F), letI := H.starRing; ∀ (a a' : 𝓞 E) (N N' n : ℕ), 1 ≤ N → 1 ≤ N' → Nat.Coprime N N' → a * star a = (N : 𝓞 E) → a' * star a' = (N' : 𝓞 E) → ∀ (θ' : Fam y.P.D.toPre F (1 * N')) (θ₂ : Fam y.P.D.toPre F (1 * N' * N)), θ' ≠ 0 → PullAl y.P.D F y.P.oD a (1 * N') N θ' θ₂ → (∀ s, NuGe y.P.D y.Q F y.v (1 * N') s 0 → ∃ (m : ℕ) (t : Fin m → Fam y.P.D.toPre F (1 * N')) (c : Fin m → F), (∀ i, y.Transl (1 * N') (star a') θ' (t i)) ∧ (∀ i, 0 ≤ y.v (c i)) ∧ s = ∑ i, c i • t i) → ∀ (h : PS F 2 y.d) (Λ : Type) [Fintype Λ] (e : Λ → Fin y.d → F) (I : Type) [Fintype I] [Nonempty I] (Pi : I → MvPolynomial (Λ × Fin n) F) (c : I → F), (∀ i, 0 ≤ y.v (c i)) → ∀ (s : Fin n → Fam y.P.D.toPre F (1 * N')) (s' t : Fin n → Fam y.P.D.toPre F (1 * N' * N)) (f : Fin n → PS F 1 y.d), (∀ b, NuGe y.P.D y.Q F y.v (1 * N') (s b) 0 ∧ PullAl y.P.D F y.P.oD a (1 * N') N (s b) (s' b) ∧ y.Transl (1 * N' * N) (star a) (s' b) (t b) ∧ y.Germ (1 * N' * N) (t b) (f b)) → ∀ gm : ℚ, y.v (y.colVal h (1 * N' * N) e (∑ i, c i • Pi i) f) = (gm : ℚ) → ∃ (i : I) (t₂ : Fin n → Fam y.P.D.toPre F (1 * N' * N)) (f₂ : Fin n → PS F 1 y.d), (∀ b, y.Transl (1 * N' * N) (star (a' * a)) θ₂ (t₂ b) ∧ y.Germ (1 * N' * N) (t₂ b) (f₂ b)) ∧ y.v (y.colVal h (1 * N' * N) e (Pi i) f₂) ≤ (gm : ℚ)

def PtExSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (F : Type) [Field F] [Algebra (FractionRing V) F] (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t), P.TorsionIso → ∀ (ϖ : V), Irreducible ϖ → ∀ v : AddValuation F (WithTop ℚ), ValOver ϖ F v → ∃ y : Pt1 E H V F, y.t = t ∧ HEq y.P P ∧ y.v = v ∧ y.ϖ = ϖ

section Basic₂

theorem Pt1.germ_zero (q : ℕ) {r : PS V 1 y.d} (hr : JetSer.IsSer1 y.x _ (y.ρ.s (fun _ => y.j)).val r) :
    y.Germ q 0 0 := by
  refine ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, Fin.elim0, r, fun i => i.elim0, fun α j₁ j₂ _ => ?_, hr,
    fun i => i.elim0, by simp⟩
  rw [Finset.univ_eq_empty, Finset.sum_empty]
  exact map_zero _

theorem Pt1.Red.mono {y : Pt1 E H V F} {r : ℕ} {b : Module.Basis (Fin r) ℤ y.P.D.toPre.X} {Cc Cc' M₀ : ℝ}
    (h : y.Red r b Cc M₀) (hC : Cc ≤ Cc') : y.Red r b Cc' M₀ :=
  ⟨h.1.trans hC, h.2.1, fun i => (h.2.2.1 i).trans hC, h.2.2.2⟩

theorem Pt1.Transl.mul {y : Pt1 E H V F} {q : ℕ} {c : 𝓞 E} {s h : Fam y.P.D.toPre F q} (ht : y.Transl q c s h)
    (c' : 𝓞 E) : y.Transl q (c' * c) s h := by
  let _ := H.starRing
  obtain ⟨p, x, w, ζ, t', h₁, h₂, h₃⟩ := ht
  refine ⟨p, x, w, ζ, t', h₁, ?_, h₃⟩
  have := y.P.oA.hom c'
  rw [y.P.oA.map_mul, ← Category.assoc, h₂, MonObj.one_comp]

section ColVal
variable [Algebra V F] [CharZero F] (h : PS F 2 y.d) (q : ℕ) {Λ : Type} [Fintype Λ] (e : Λ → Fin y.d → F) {n : ℕ}

theorem Pt1.colVal_monomial (mo : Λ × Fin n →₀ ℕ) (c : F) (f : Fin n → PS F 1 y.d) :
    y.colVal h q e (MvPolynomial.monomial mo c) f =
      c * ∏ b, (letI := H.starRing; y.B.nabVal F h H.w0 q (f b) e (MvPolynomial.monomial (colM mo b) 1)) := by
  classical
  unfold Pt1.colVal
  by_cases hc : c = 0
  · simp [hc]
  · rw [MvPolynomial.support_monomial, if_neg hc, Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl]

theorem Pt1.colVal_zero (f : Fin n → PS F 1 y.d) : y.colVal h q e (0 : MvPolynomial (Λ × Fin n) F) f = 0 := by
  simp [Pt1.colVal]

theorem Pt1.colVal_add (P P' : MvPolynomial (Λ × Fin n) F) (f : Fin n → PS F 1 y.d) :
    y.colVal h q e (P + P') f = y.colVal h q e P f + y.colVal h q e P' f := by
  classical
  unfold Pt1.colVal
  have key : ∀ R : MvPolynomial (Λ × Fin n) F, R.support ⊆ P.support ∪ P'.support → ∀ g : (Λ × Fin n →₀ ℕ) → F,
      ∑ mo ∈ R.support, R.coeff mo * g mo = ∑ mo ∈ P.support ∪ P'.support, R.coeff mo * g mo := fun R hR g =>
    Finset.sum_subset hR fun mo _ hm => by rw [MvPolynomial.notMem_support_iff.1 hm, zero_mul]
  rw [key _ MvPolynomial.support_add, key P Finset.subset_union_left, key P' Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun mo _ => by rw [MvPolynomial.coeff_add, add_mul]

theorem Pt1.colVal_smul (c : F) (P : MvPolynomial (Λ × Fin n) F) (f : Fin n → PS F 1 y.d) :
    y.colVal h q e (c • P) f = c * y.colVal h q e P f := by
  classical
  unfold Pt1.colVal
  rw [Finset.mul_sum, Finset.sum_subset (MvPolynomial.support_smul (a := c) (f := P))
    fun mo _ hm => by rw [MvPolynomial.notMem_support_iff.1 hm, zero_mul]]
  exact Finset.sum_congr rfl fun mo _ => by rw [MvPolynomial.coeff_smul, smul_eq_mul, _root_.mul_assoc]

theorem Pt1.colVal_sum {I : Type} (S : Finset I) (c : I → F) (P : I → MvPolynomial (Λ × Fin n) F)
    (f : Fin n → PS F 1 y.d) : y.colVal h q e (∑ i ∈ S, c i • P i) f = ∑ i ∈ S, c i * y.colVal h q e (P i) f := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [Pt1.colVal]
  | insert i S hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, y.colVal_add, y.colVal_smul, ih]

end ColVal

theorem minorMonomial_zero (k : Type) [CommRing k] {T : Type} [Fintype T] [DecidableEq T] {r : T → ℕ} {n : ℕ}
    (col : ∀ τ, Fin (r τ) → Fin n) : minorsP k col (fun _ _ => 0) = 1 := by
  simp [minorsP]

example (k : Type) [CommRing k] {n : ℕ} (b : Fin n) (m : ℕ) :
    minorsP k (T := Unit) (r := fun _ => 1) (fun _ _ => b) (fun _ _ => m) = MvPolynomial.X (⟨(), 0⟩, b) ^ m := by
  simp [minorsP]

example (k : Type) [CommRing k] :
    minorsP k (T := Unit) (r := fun _ => 2) (n := 2) (fun _ i => i) (fun _ s => s.val) =
      MvPolynomial.X (⟨(), 0⟩, 0) * MvPolynomial.X (⟨(), 1⟩, 1) -
        MvPolynomial.X (⟨(), 0⟩, 1) * MvPolynomial.X (⟨(), 1⟩, 0) := by
  simp [minorsP, Fin.prod_univ_two, Matrix.det_fin_two]

end Basic₂

end GlobalTheory.FamGerm
