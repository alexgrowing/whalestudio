import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ZH
open ReciprocityTheory.ChartRestriction.G.Out Classical

def HypS {B : Scheme.{0}} (G : Over B) [GrpObj G] [IsCommMonObj G] (L : LB G.left) : Prop :=
  ∃ w wd : G ⟶ G, IsMonHom w ∧ IsMonHom wd ∧ w * wd = 𝟙 G ∧ LBIso L (cubeLB G ![𝟙 G, w] L) ∧
    LBIso (cubeLB G ![fst G G ≫ w, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ wd] L)

abbrev fn {R : Type} [CommRing R] (a : R) : Γ((baseOver (Sp R)).left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

structure ThetaSys.Real (S : ThetaSys o Ω) where
  P : PolAV (Sp S.R)
  g_eq : P.g = S.g
  hypS : HypS P.A P.L
  n : ℕ
  n_prime : n.Prime
  n_odd : Odd n
  k : ℕ
  two_le : 2 ≤ k
  N_eq : S.N = (n ^ k) ^ 2
  r_eq : ∃ j, 1 ≤ j ∧ S.r = n ^ j
  card : Fintype.card S.J = S.N ^ S.g
  pt : S.Gam → (baseOver (Sp S.R) ⟶ P.A)
  pt_add : ∀ a b, pt (a + b) = pt a * pt b
  pt_bij : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp S.R) (z : Over.mk x ⟶ P.A), z ^ (S.r * S.N) = 1 →
    ∃! a, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp S.R)) ≫ pt a = z
  weil : ∀ a b (c : (S.R)ˣ), (c : S.R) = algebraMap o S.R (S.ζ ^ (S.r * S.N * (eStd S.g _ a b).val)) →
    WeilIs P.A P.L (S.r * S.N : ℕ) (pt a) (pt b) (unitOn c)
  rig : LB.Gen (P.L.pull (eSec P.A))
  rig_gen : rig.IsGen
  th₁ : LB.Sec (LPow P.A P.L 1 (baseOver (Sp S.R)))
  th₁_basis : IsSecBasis _ (fun _ : Fin 1 => th₁)
  fr : ∀ a, LB.Gen (LB.LinComb P.L (Y := (baseOver (Sp S.R)).left) (K := Fin 1) (fun _ => (pt a).left) (fun _ => 1))
  fr_tors : ∀ a, IsTorsFrame P rig (S.r * S.N) (pt a) (fr a)
  th_val : ∀ a, IsValueAt P.A P.L 1 th₁ (pt a) (fr a) (fn (⟨S.th a, S.th_mem a⟩ : S.R))
  s : S.J → LB.Sec (LPow P.A P.L S.N (baseOver (Sp S.R)))
  s_basis : ∀ σ : LB.Sec (LPow P.A P.L S.N (baseOver (Sp S.R))), ∃! c : S.J → Γ((baseOver (Sp S.R)).left, ⊤),
    ∀ j, σ.f j = ∑ i, liftFun P.A _ (c i) * (s i).f j
  ev_val : ∀ i, IsEvT P S.N pt (fun a => powFrame P.A P.L (pt a) (fr a) S.N) (s i) (fun a => fn (⟨S.ev a i, S.ev_mem a i⟩ : S.R))
  i₀ : S.J
  α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd (baseOver (Sp S.R)) P.A).left, (snd (baseOver (Sp S.R)) P.A ^ (n ^ k)).left] ![(S.N : ℤ), -1])
  α_gen : α.IsGen
  α_norm : LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ α (ptSecT P.A 1).left)
    (LB.mulGen P.L _ _ _ _ (rigT P.A P.L rig (baseOver (Sp S.R)) S.N) (rigT P.A P.L rig (baseOver (Sp S.R)) (-1)))
  s_zero : IsTwistPull P.A P.L (mulT P.A _ (n ^ k)) (snd _ P.A ^ (n ^ k)) (lift_snd _ _) S.N 1 α th₁ (s i₀)
  U : S.Gam → ThetaGrp P.A P.L S.N (baseOver (Sp S.R))
  U_sym : ∀ a, SymLift P.A P.L S.N S.N (pt (S.r • a)) (U a)
  U_act : ∀ a i σ, IsActOf P.A P.L S.N (U a) (s i) σ →
    ∀ j, σ.f j = ∑ l, liftFun P.A _ (fn (algebraMap o S.R (S.ρ a l i))) * (s l).f j
  orbit : ∀ i, ∃ a, ∃ e : ℕ, ∀ l, S.ρ a l i₀ = if l = i then S.ζ ^ e else 0

structure ThetaSys.Real.UTest {S : ThetaSys o Ω} (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) where
  V : Type
  [ring : CommRing V]
  [dom : IsDomain V]
  [dvr : IsDiscreteValuationRing V]
  complete : IsAdicComplete (IsLocalRing.maximalIdeal V) V
  [alg : Algebra (FractionRing V) (PadicAlgCl p)]
  norm_le : ∀ x : FractionRing V, ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))
  yK : S.R →+* FractionRing V
  fac : (algebraMap (FractionRing V) (PadicAlgCl p)).comp yK = y₀
  A : PolAV (Sp (FractionRing V))
  φ : A.A.left ⟶ ρ.P.A.left
  cart : IsGrpPullback A.A ρ.P.A (spMap yK) φ
  lb : LBIso A.L (ρ.P.L.pull φ)
  G : Over (Sp V)
  [grp : GrpObj G]
  [comm : IsCommMonObj G]
  semi : IsSemiAbelian G
  D : DegData V (IsLocalRing.maximalIdeal V)
  U : Unif (IsLocalRing.maximalIdeal V) D A G
attribute [instance] ThetaSys.Real.UTest.ring ThetaSys.Real.UTest.dom ThetaSys.Real.UTest.dvr ThetaSys.Real.UTest.alg
  ThetaSys.Real.UTest.grp ThetaSys.Real.UTest.comm
namespace ThetaSys.Real.UTest
variable {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀)

def PsiNorm (χ : u.D.toPre.X) (r : ℝ) : Prop :=
  ∀ j : PUnit → u.D.toPre.P.L.ι, ⊤ ≤ (u.D.toPre.c χ).left ⁻¹ᵁ u.D.toPre.P.L.U (j PUnit.unit) →
    ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (valF (𝟙 (Sp (FractionRing u.V))) _ ((u.D.toPre.psi χ).s j).val)‖ = r

def Integral (a : S.Gam) : Prop := ∃ (h : Sp u.V ⟶ u.G.left) (x : Sp (FractionRing u.V) ⟶ pullback u.G.hom (jK u.V)),
  h ≫ u.G.hom = 𝟙 _ ∧ x ≫ pullback.fst _ _ = jK u.V ≫ h ∧ x ≫ pullback.snd _ _ = 𝟙 _ ∧
  x ≫ u.U.gen.hom.left ≫ u.φ = spMap u.yK ≫ (ρ.pt a).left

structure Lab where
  q : QuadraticMap ℤ u.D.toPre.X ℝ
  pos : Filter.Tendsto q Filter.cofinite Filter.atTop
  q_eq : ∀ χ, u.PsiNorm χ (Real.exp (-q χ))
  yy : S.Gam →+ u.D.toPre.X ⧸ (nsmulAddMonoidHom (S.r * S.N) : u.D.toPre.X →+ u.D.toPre.X).range
  yy_onto : Function.Surjective yy
  yy_eq : ∀ (a : S.Gam) (pk : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A),
    QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) pk x → x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left →
    yy a = QuotientAddGroup.mk pk.y
  ker_iff : ∀ a, a ∈ yy.ker ↔ u.Integral a
  isoFree : S.IsoFree (S.perp yy.ker)
  wt : u.D.toPre.X →+ (S.perp yy.ker →+ ZMod S.N)
  wt_eq : ∀ (x : S.Gam) (α : u.D.toPre.X), yy x = QuotientAddGroup.mk α → ∀ t : S.perp yy.ker,
    wt α t = ZMod.castHom (dvd_mul_left S.N S.r) (ZMod S.N) (eStd S.g _ t x)

def Lab.Match {u : ρ.UTest p y₀} (l : u.Lab) (τ : S.Test p y₀) : Prop :=
  ∃ e : τ.X ≃+ u.D.toPre.X, (∀ α, τ.q α = l.q (e α)) ∧
    ∀ a α, τ.yy a = QuotientAddGroup.mk α ↔ l.yy a = QuotientAddGroup.mk (e α)
end ThetaSys.Real.UTest

def ThetaSys.Big (S : ThetaSys o Ω) : Prop :=
  1 + 2 * (S.g : ℝ) * (2 : ℝ) ^ ((S.g : ℝ) / 2) < S.N ∧
  2 * ((S.N ^ S.g * S.g.factorial : ℕ) : ℝ) * ((S.g : ℝ) * (3 / 2 : ℝ) ^ S.g * (2 : ℝ) ^ ((S.g : ℝ) / 2 - 1)) * S.N < (S.r * S.N : ℕ) ∧
  6 * (S.N ^ S.g * S.g.factorial) < S.r * S.N

def ThetaSys.delta (S : ThetaSys o Ω) {p : ℕ} [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) : ℝ :=
  ⨆ x, ‖y₀ ⟨S.th x, S.th_mem x⟩‖
end GlobalTheory.ZH
end
