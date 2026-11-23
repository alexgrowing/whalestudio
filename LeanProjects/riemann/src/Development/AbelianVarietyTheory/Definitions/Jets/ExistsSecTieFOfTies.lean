import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.H1algStatement
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.CombBound4Of
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.IsMixedOver

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.PullbackSections (endT IsNormEnd IsMixedOver)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.PtTie

section Cast
variable {X Y : Scheme.{0}}

def isoCast {L L' : LB X} (h : L = L') {M : LB Y} (f : Y ⟶ X) (w : LB.Iso M (L.pull f)) : LB.Iso M (L'.pull f) := h ▸ w
end Cast

section End
variable {X : Scheme.{0}} (A : Over X) [GrpObj A] [IsCommMonObj A] (L : RigLB A)

abbrev endOver (T : Over X) (φ : A ⟶ A) : T ⊗ A ⟶ T ⊗ A := endT A T φ

def IsNormPull (φ : A ⟶ A) (a b : ℤ) {T : Over X} (s : LB.Sec (LPow A L.L b T)) (s' : LB.Sec (LPow A L.L a T)) : Prop :=
  ∃ (α₀ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, φ.left] ![a, -b]))
    (α : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(snd T A).left, (snd T A ≫ φ).left] ![a, -b])),
    α₀.IsGen ∧ IsNormEnd A L φ a b α₀ ∧
    LB.Gen.Corr L.L _ _ _ _ α (LB.pullGen L.L _ _ α₀ (snd T A).left) ∧
    IsTwistPull A L.L (endT A T φ) (snd T A ≫ φ) (lift_snd _ _) a b α s s'

def IsSymAct (N : ℕ) {T : Over X} (b : T ⟶ A) (s s' : LB.Sec (LPow A L.L (N : ℤ) T)) : Prop :=
  b ^ N = 1 ∧ ∃ U : ThetaGrp A L.L (N : ℤ) T, SymLift A L.L (N : ℤ) N b U ∧ IsActOf A L.L (N : ℤ) U s s'

def IsTransPull (φ : A ⟶ A) (N : ℕ) {T : Over X} (s : LB.Sec (LPow A L.L 1 T)) (b : T ⟶ A)
    (hh : LB.Sec (LPow A L.L (N : ℤ) T)) : Prop :=
  ∃ h₁ : LB.Sec (LPow A L.L (N : ℤ) T), IsNormPull A L φ (N : ℤ) 1 s h₁ ∧ IsSymAct A L N b h₁ hh

theorem IsSymAct.pow_eq_one {N : ℕ} {T : Over X} {b : T ⟶ A} {s s' : LB.Sec (LPow A L.L (N : ℤ) T)}
    (h : IsSymAct A L N b s s') : b ^ N = 1 := h.1

theorem IsTransPull.pow_eq_one {φ : A ⟶ A} {N : ℕ} {T : Over X} {s : LB.Sec (LPow A L.L 1 T)} {b : T ⟶ A}
    {hh : LB.Sec (LPow A L.L (N : ℤ) T)} (h : IsTransPull A L φ N s b hh) : b ^ N = 1 := h.choose_spec.2.1
end End

section Comparison₂
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr} {y : letI := io.toAlgebra; FrPt Xo c T.Fr}
  (I : IntData Xo c T io y) (P : PELUnif (maximalIdeal T.V) I.G)
  (F : Type) [Field F] [Algebra T.Fr F] (xF : Sp F ⟶ Xo.X)

def PtTieF (x : TFK (R := T.V) F ⟶ P.A.A) (b : ptO Xo xF ⟶ Xo.univ.t.G) : Prop :=
  ∃ r : Sp F ⟶ I.t'.G.left, r ≫ I.t'.G.hom = spMap (algebraMap T.Fr F) ∧ r ≫ I.m1.φ = b.left ∧
    r ≫ I.m2.φ = (x ≫ P.U.gen.inv).left ≫ pullback.fst I.G.G.hom (jK T.V)

def SecTieF (q : ℕ) (σ : P.U.toUnifPre.SecGF F q)
    (hh : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (q : ℤ) (ptO Xo xF))) : Prop :=
  xF = spMap (algebraMap T.Fr F) ≫ (letI := io.toAlgebra; y.x) ∧
  ∀ (Z : Scheme.{0}) (r : Z ⟶ I.t'.G.left) (zG : Z ⟶ (UnifPre.GF (R := T.V) (G := I.G.G) F).left)
    (zU : Z ⟶ (ptO Xo xF ⊗ Xo.univ.t.G).left),
    zG ≫ UnifPre.gFK (R := T.V) (G := I.G.G) F = r ≫ I.m2.φ →
    zU ≫ (snd (ptO Xo xF) Xo.univ.t.G).left = r ≫ I.m1.φ →
    zG ≫ (fst (TFK (R := T.V) F) ((Over.pullback (jK T.V)).obj I.G.G)).left = zU ≫ (fst (ptO Xo xF) Xo.univ.t.G).left →
    zU ≫ (fst (ptO Xo xF) Xo.univ.t.G).left ≫ spMap (algebraMap T.Fr F) = r ≫ I.t'.G.hom →
    ∀ (z : Z) (J₁ : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι) (J₂ : (Z ⟶ I.G.G.left) → P.U.LG.L.ι) (j' : I.t'.PP.L.ι),
      Good Xo.univ.t.PP.L z J₁ → Good P.U.LG.L z J₂ → r z ∈ I.t'.PP.L.U j' →
      sval σ zG z J₂ * ((gv I.w1 r z (fun _ => J₁ (r ≫ I.m1.φ)) j').val) ^ q =
        sval hh zU z J₁ *
          ((gv (isoCast (congrArg RigLB.L P.bundle).symm I.m2.φ I.w2) r z (fun _ => J₂ (r ≫ I.m2.φ)) j').val) ^ q
variable {I P F xF}

theorem PtTieF.base {x : TFK (R := T.V) F ⟶ P.A.A} {b : ptO Xo xF ⟶ Xo.univ.t.G} (h : PtTieF I P F xF x b) :
    xF = spMap (algebraMap T.Fr F) ≫ (letI := io.toAlgebra; y.x) := by
  letI := io.toAlgebra
  obtain ⟨r, h1, h2, -⟩ := h
  have hw : I.m1.φ ≫ Xo.univ.t.G.hom = I.t'.G.hom ≫ y.x := I.m1.cart.1.w
  have hb : b.left ≫ Xo.univ.t.G.hom = xF := Over.w b
  rw [← hb, ← h2, Category.assoc, hw, ← Category.assoc, h1]

theorem SecTieF.base {q : ℕ} {σ : P.U.toUnifPre.SecGF F q}
    {hh : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (q : ℤ) (ptO Xo xF))} (h : SecTieF I P F xF q σ hh) :
    xF = spMap (algebraMap T.Fr F) ≫ (letI := io.toAlgebra; y.x) := h.1

variable (I P)

end Comparison₂

section Num
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}

def nrm (Dw : Datum H) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (α : 𝓞 E) : c.F :=
  ∏ τ : E →+* ℂ, embK c τ α ^ (∑ i : Fin (Dw.mult τ), a (τ, i))

def SplitsIn (E : Type) [Field E] [NumberField E] (g : ℕ) : Prop :=
  (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).card = Module.finrank ℚ E ∧
    (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).Nodup

def ShortBasis {X : Type} [AddCommGroup X] (Q : X → ℤ) (r : ℕ) (Φ M0 : ℝ) : Prop :=
  0 ≤ Φ ∧ ∃ b : Module.Basis (Fin r) ℤ X, (∀ j, (Q (b j) : ℝ) ≤ Φ) ∧
    ∀ j z, |((Q (b j + z) - Q (b j) - Q z : ℤ) : ℝ)| ≤ M0 * Q z

theorem nrm_zero (Dw : Datum H) (c : Coeff l) (α : 𝓞 E) : nrm Dw c 0 α = 1 := by simp [nrm]
end Num

section Run
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons IsDedekindDomain

def rr0 (D : D7) : ℝ :=
  (|(NumberField.discr D.host.E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ D.host.E)) / (2 * Module.finrank ℚ D.host.E)

def RunNum (D : D7) {j : ℕ} (w : WeightFamilies.Wt D j) (c : ℝ) : Prop :=
  w.LastPos ∧ 2 * D.R.f * D.R.r ≤ w.n ∧ (∀ i, 4 * WeightAlgebra.DF w + 4 ≤ D.host.g i) ∧ 0 ≤ c ∧
    (j < D.R.m → ∀ i, (WeightAlgebra.DF w : ℝ) * (2 * Real.sqrt (2 * D.R.f * D.R.m)) < (D.host.g i : ℝ) ∧
      rr0 D * ((2 * D.R.f * D.R.m : ℝ) ^ 4 * w.n + 2 * (2 * D.R.f * D.R.m : ℝ) ^ 3) * (WeightAlgebra.DF w : ℝ) ^ 2 / (D.host.g i : ℝ) ≤ c)

theorem runNum_cc (D : D7) (L : SizeData₂ D) {j : ℕ} (w : WeightFamilies.Wt D j) (C2 A2 CR : ℝ) (h1 : w.LastPos)
    (h2 : D.R.f * D.R.r * (D.R.r + 1) ≤ w.n) (h3 : ∀ i, 4 * WeightAlgebra.DF w + 4 ≤ D.host.g i)
    (h4 : rr0 D ≤ WeightFamilies.RRv D CR)
    (h5 : (2 * D.R.f * D.R.m : ℝ) ^ 4 * w.n + 2 * (2 * D.R.f * D.R.m : ℝ) ^ 3 ≤ WeightFamilies.PPv D L C2 A2)
    (h6 : ∀ i, (WeightAlgebra.DF w : ℝ) * (2 * Real.sqrt (2 * D.R.f * D.R.m)) < (D.host.g i : ℝ)) :
    RunNum D w (WeightAlgebra.cc D L C2 A2 CR w) := by
  have r0 : 0 ≤ rr0 D := by unfold rr0; positivity
  have p0 : (0 : ℝ) ≤ (2 * D.R.f * D.R.m : ℝ) ^ 4 * w.n + 2 * (2 * D.R.f * D.R.m : ℝ) ^ 3 := by positivity
  have hR := r0.trans h4
  have hP := p0.trans h5
  refine ⟨h1, ?_, h3, by unfold WeightAlgebra.cc; positivity, fun _ i => ⟨h6 i, ?_⟩⟩
  · refine le_trans ?_ h2
    rcases Nat.eq_zero_or_pos D.R.r with h | h
    · simp [h]
    · nlinarith [Nat.mul_le_mul_left (D.R.f * D.R.r) (show 2 ≤ D.R.r + 1 by omega)]
  · have hq : WeightAlgebra.qq D ≤ D.host.g i := by
      fin_cases i
      exacts [min_le_left _ _, min_le_right _ _]
    have hq0 : 0 < WeightAlgebra.qq D := lt_min (by have := h3 0; omega) (by have := h3 1; omega)
    unfold WeightAlgebra.cc
    gcongr
variable {D : D7}

def Oriented (T : Top D) (EX : ErrX D) : Prop := ∀ i, T.Q.l.Mb ≤ Ideal.span {piBarO EX i}

def nuWt (T : Top D) {j : ℕ} (w : WeightFamilies.Wt D j) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) : ℝ :=
  letI := T.Q.H.starRing
  (nuW (T.Q.Xo j) T.Q.c la T.Q.l.M (wtA w) w.n).toReal / (ramOverZ la : ℝ)

def sWt (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) {j : ℕ} (w : WeightFamilies.Wt D j) : 𝓞 B.KO :=
  nnW B hinj EX w * (pPow D (c2 D w) (cHalf w) (cHalf w) : 𝓞 B.KO)

end Run
end GlobalTheory.PtTie
