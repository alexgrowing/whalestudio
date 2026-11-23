import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds

def degEmb (g N : ℕ) : ℕ := N ^ g * g.factorial

def coordConst (g : ℕ) : ℝ := (g : ℝ) * (3 / 2 : ℝ) ^ g * (2 : ℝ) ^ ((g : ℝ) / 2 - 1)

def LowerBounds (g N N' : ℕ) : Prop :=
  1 + 2 * (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2) < (N : ℝ) ∧
    2 * (degEmb g N : ℝ) * coordConst g * (N : ℝ) < (N' : ℝ)

example : LowerBounds 2 ((3 ^ 2) ^ 2) (3 ^ 11 * (3 ^ 2) ^ 2) := by
  unfold LowerBounds coordConst degEmb
  norm_num [Nat.factorial]

example : ¬ LowerBounds 2 ((3 ^ 2) ^ 2) (3 ^ 10 * (3 ^ 2) ^ 2) := by
  unfold LowerBounds coordConst degEmb
  norm_num [Nat.factorial]

section Operators

variable {B : Scheme.{0}} (P : Out.PolAV B) (rig : LB.Gen (P.L.pull (eSec P.A)))

def IsMulPull (k : ℕ) (a : ℤ) {T : Over B} (θ : LB.Sec (Out.LPow P.A P.L 1 T)) (s : LB.Sec (Out.LPow P.A P.L a T)) : Prop :=
  ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ k).left] ![a, -1]),
    α.IsGen ∧
    LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ α (Out.ptSecT P.A 1).left)
      (LB.mulGen P.L _ _ _ _ (Out.rigT P.A P.L rig T a) (LB.invGen P.L _ _ (Out.rigT P.A P.L rig T 1))) ∧
    Out.IsTwistPull P.A P.L (Out.mulT P.A T k) (snd T P.A ^ k) (lift_snd _ _) a 1 α θ s

def IsHeis (k : ℕ) {T : Over B} (x : T ⟶ P.A) (s s' : LB.Sec (Out.LPow P.A P.L (k : ℤ) T)) : Prop :=
  x ^ k = 1 ∧ ∃ U : Out.ThetaGrp P.A P.L (k : ℤ) T,
    Out.SymLift P.A P.L (k : ℤ) k x U ∧ Out.IsActOf P.A P.L (k : ℤ) U s s'

def IsValueZero (a : ℤ) {T : Over B} (s : LB.Sec (Out.LPow P.A P.L a T)) (v : Γ(T.left, ⊤)) : Prop :=
  ∃ τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => (1 : T ⟶ P.A).left) (fun _ => a)),
    τ.IsGen ∧ LB.Gen.Corr P.L _ _ _ _ τ (Out.rigT P.A P.L rig T a) ∧ Out.IsValueAt P.A P.L a s 1 τ v

def IsThetaConst (k : ℕ) {T : Over B} (θ : LB.Sec (Out.LPow P.A P.L 1 T)) (x : T ⟶ P.A) (v : Γ(T.left, ⊤)) : Prop :=
  ∃ s s' : LB.Sec (Out.LPow P.A P.L ((k ^ 2 : ℕ) : ℤ) T),
    IsMulPull P rig k _ θ s ∧ IsHeis P (k ^ 2) x s s' ∧ IsValueZero P rig _ s' v

end Operators

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

abbrev Base (S : ThetaSys o Ω) : Over (Sp S.R) := Out.baseOver (Sp S.R)

def fn (S : ThetaSys o Ω) : S.R →+* Γ((Base S).left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of S.R)).inv.hom

def cst (S : ThetaSys o Ω) : o →+* Γ((Base S).left, ⊤) := (fn S).comp (algebraMap o S.R)

theorem level_ne_zero (S : ThetaSys o Ω) : (S.r * S.N) ^ 2 ≠ 0 := by
  have h1 := S.r_pos
  have h2 := S.N_ge
  exact pow_ne_zero _ (Nat.mul_ne_zero (by omega) (by omega))

def zetaUnit (S : ThetaSys o Ω) : Γ(Sp S.R, ⊤)ˣ :=
  unitOn (Units.map (algebraMap o S.R).toMonoidHom (S.prim.isUnit (level_ne_zero S)).unit)

def idx {g g' : ℕ} (h : g' = g) (i : Fin (2 * g')) : Fin g ⊕ Fin g :=
  finSumFinEquiv.symm (Fin.cast (by rw [h, two_mul]) i)

def cstSpan (S : ThetaSys o Ω) {M : Type} [AddCommGroup M] [Module Γ((Base S).left, ⊤) M] (X : Set M) : AddSubgroup M :=
  AddSubgroup.closure {v | ∃ c : o, ∃ x ∈ X, v = cst S c • x}

def torPt (S : ThetaSys o Ω) {P : Out.PolAV (Sp S.R)} (h : P.g = S.g)
    (lev : Out.Level P ((S.r * S.N) ^ 2) (zetaUnit S)) (a : S.Gam) : Base S ⟶ P.A :=
  Out.linComb lev.pt (fun i => (a (idx h i)).val) ^ (S.r * S.N)

structure Realisation (S : ThetaSys o Ω) where
  n : ℕ
  k : ℕ
  j : ℕ
  prime : n.Prime
  odd : Odd n
  two_le : 2 ≤ k
  N_eq : S.N = (n ^ k) ^ 2
  r_eq : S.r = n ^ j
  bounds : LowerBounds S.g S.N (S.r * S.N)

  P : Out.PolAV (Sp S.R)
  dim : P.g = S.g
  rig : LB.Gen (P.L.pull (eSec P.A))
  rig_gen : rig.IsGen

  w : P.A ⟶ P.A
  w_hom : IsMonHom w
  selfPaired : LBIso P.L (cubeLB P.A ![𝟙 P.A, w] P.L)

  lev : Out.Level P ((S.r * S.N) ^ 2) (zetaUnit S)

  θ : LB.Sec (Out.LPow P.A P.L 1 (Base S))
  θ_gen : Out.IsGenSec P.A P.L 1 θ

  th_eq : ∀ a : S.Gam, ∃ (x' : Base S ⟶ P.A) (v : Γ((Base S).left, ⊤)) (e : ℕ),
    x' ^ (S.r * S.N) = torPt S dim lev a ∧ IsThetaConst P rig (S.r * S.N) θ x' v ∧
      fn S ⟨S.th a, S.th_mem a⟩ = cst S S.ζ ^ e * v

  s₁ : LB.Sec (Out.LPow P.A P.L (S.N : ℤ) (Base S))
  s₁_eq : IsMulPull P rig (n ^ k) (S.N : ℤ) θ s₁

  b : S.J → LB.Sec (Out.LPow P.A P.L (S.N : ℤ) (Base S))
  b_indep : ∀ c : S.J → o, ∑ i, cst S (c i) • Out.SecM.ofSec P.A (b i) = 0 → c = 0
  b_span : cstSpan S (Set.range fun i => Out.SecM.ofSec P.A (b i)) =
    cstSpan S {v | ∃ x s, IsHeis P S.N x s₁ s ∧ v = Out.SecM.ofSec P.A s}

  ρ_eq : ∀ (a : S.Gam) (i : S.J), ∃ s, IsHeis P S.N (torPt S dim lev a ^ S.r) (b i) s ∧
    Out.SecM.ofSec P.A s = ∑ i', cst S (S.ρ a i' i) • Out.SecM.ofSec P.A (b i')

  ev_eq : ∀ a : S.Gam, ∃ e : LB.Gen (LB.LinComb P.L (Y := (Base S).left) (K := Fin 1)
      (fun _ => (torPt S dim lev a).left) (fun _ => 1)),
    Out.IsTorsFrame P rig (S.r * S.N) (torPt S dim lev a) e ∧
      ∀ i, Out.IsValueAt P.A P.L (S.N : ℤ) (b i) (torPt S dim lev a)
        (Out.powFrame P.A P.L (torPt S dim lev a) e (S.N : ℤ)) (fn S ⟨S.ev a i, S.ev_mem a i⟩)

abbrev Realisation.tor {S : ThetaSys o Ω} (Z : Realisation S) (a : S.Gam) : Base S ⟶ Z.P.A := torPt S Z.dim Z.lev a

section Tests

variable {p : ℕ} [Fact p.Prime]

abbrev intRing (K : IntermediateField ℚ_[p] (PadicAlgCl p)) : ValuationSubring K :=
  (OO p).comap (algebraMap K (PadicAlgCl p))

theorem intRing_injective (K : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    Function.Injective ((algebraMap K (PadicAlgCl p)).comp (intRing K).subtype) :=
  (algebraMap K (PadicAlgCl p)).injective.comp Subtype.val_injective

instance fracAlgebra (K : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    Algebra (FractionRing (intRing K)) (PadicAlgCl p) :=
  (IsFractionRing.lift (A := intRing K) (K := FractionRing (intRing K)) (intRing_injective K)).toAlgebra

example (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (x : intRing K) :
    algebraMap (FractionRing (intRing K)) (PadicAlgCl p) (algebraMap (intRing K) _ x) = ((x : K) : PadicAlgCl p) :=
  IsFractionRing.lift_algebraMap (intRing_injective K) x

def PsiNorm {K : IntermediateField ℚ_[p] (PadicAlgCl p)} (D : Out.DegPre (intRing K)) (χ : D.X) (t : ℝ) : Prop :=
  ∀ i : D.P.L.ι, ⊤ ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U i →
    ‖algebraMap (FractionRing (intRing K)) (PadicAlgCl p)
      (valF (𝟙 (Sp (FractionRing (intRing K)))) _ ((D.psi χ).s fun _ => i).val)‖ = t

structure UnifTest {S : ThetaSys o Ω} (Z : Realisation S) (p : ℕ) [Fact p.Prime] (y : S.R →+* PadicAlgCl p) where
  base_int : ∀ a : o, ‖y (algebraMap o S.R a)‖ ≤ 1
  K : IntermediateField ℚ_[p] (PadicAlgCl p)
  finite : FiniteDimensional ℚ_[p] K
  yK : S.R →+* FractionRing (intRing K)
  yK_eq : ∀ a, algebraMap (FractionRing (intRing K)) (PadicAlgCl p) (yK a) = y a

  A : Out.PolAV (Sp (FractionRing (intRing K)))
  φ : A.A.left ⟶ Z.P.A.left
  cart : IsGrpPullback A.A Z.P.A (spMap yK) φ
  pol : LBIso A.L (Z.P.L.pull φ)

  G : Over (Sp (intRing K))
  [grp : GrpObj G]
  [comm : IsCommMonObj G]
  qc : QuasiCompact G.hom
  split : ∃ E : SplitExt (Sp (IsLocalRing.ResidueField (intRing K))),
    E.IsGt ((Over.pullback (spMap (IsLocalRing.residue (intRing K)))).obj G)

  D : Out.DegData (intRing K) (IsLocalRing.maximalIdeal (intRing K))
  U : Out.Unif (IsLocalRing.maximalIdeal (intRing K)) D A G

  pt : S.Gam → (Out.TFK (R := intRing K) (PadicAlgCl p) ⟶ A.A)
  pt_eq : ∀ a, (pt a).left ≫ φ = spMap y ≫ (Z.tor a).left

  lab : S.Gam → Out.QkPt D.toPre (PadicAlgCl p) (S.r * S.N)
  lab_eq : ∀ a, Out.QkToAkU U.toUnifPre (PadicAlgCl p) (S.r * S.N) (lab a) (pt a)

attribute [instance] UnifTest.grp UnifTest.comm

def UnifTest.Matches {S : ThetaSys o Ω} {Z : Realisation S} {y : S.R →+* PadicAlgCl p} (t : UnifTest Z p y)
    (τ : S.Test p y) : Prop :=
  ∃ e : τ.X ≃+ t.D.toPre.X,
    (∀ χ, PsiNorm t.D.toPre (e χ) (Real.exp (-(τ.q χ)))) ∧
    ∀ a, τ.yy a = QuotientAddGroup.mk (e.symm (t.lab a).y)

end Tests

def Realisation.HasUnifTests {S : ThetaSys o Ω} (Z : Realisation S) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (y : S.R →+* PadicAlgCl p), (∀ a : o, ‖y (algebraMap o S.R a)‖ ≤ 1) →
    ∃ (t : UnifTest Z p y) (τ : S.Test p y), t.Matches τ

example {S : ThetaSys o Ω} (Z : Realisation S) (h : Z.HasUnifTests) : S.HasTests :=
  fun p _ y hy => let ⟨_, τ, _⟩ := h p y hy; ⟨τ⟩

end GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds
end
