import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowDat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def perp (D : Datum H) (Z : Submodule (𝓞 E) D.La) : Submodule (𝓞 E) D.La where
  carrier := {x | ∀ z ∈ Z, D.EF x z = 0}
  zero_mem' := by intro z _; simp
  add_mem' := by
    intro x y hx hy z hz
    show D.EF (x + y) z = 0
    rw [map_add, LinearMap.add_apply, hx z hz, hy z hz, add_zero]
  smul_mem' := by
    intro a x hx z hz
    show D.EF (a • x) z = 0
    rw [D.adj]
    exact hx _ (Z.smul_mem _ hz)

def IsIsoSat (D : Datum H) (Z : Submodule (𝓞 E) D.La) : Prop :=
  Z ≤ perp D Z ∧ ∀ (n : ℕ) (x : D.La), n ≠ 0 → n • x ∈ Z → x ∈ Z

def IsLower (D D' : Datum H) (Z : Submodule (𝓞 E) D.La) (f : perp D Z →ₗ[𝓞 E] D'.La) : Prop :=
  Function.Surjective f ∧ (∀ x, f x = 0 ↔ (x : D.La) ∈ Z) ∧ ∀ x y, D'.EF (f x) (f y) = D.EF x y

def lowLevel (l : Level H) : Level H :=
  { l with A := l.M', A_pos := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos }

theorem ka_le (l : Level H) (c : Coeff l) : KA (lowLevel l) ≤ c.F := by
  unfold KA
  rw [IntermediateField.adjoin_le_iff]
  intro x hx
  rcases hx with rfl | hx
  · exact c.le (IntermediateField.subset_adjoin _ _ (by simp))
  · rw [Set.mem_singleton_iff] at hx; subst hx; exact c.zeta_mem

end GlobalTheory.LowDat

namespace GlobalTheory.LowDat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

def lowS (C : UChart.Fam Xo c R) : Sp R ⟶ Sp (KA (lowLevel l)) :=
  spMap (C.b.comp (IntermediateField.inclusion (ka_le l c)).toRingHom)

def toF (C : UChart.Fam Xo c R) (F : Type) [Field F] [Algebra (FractionRing R) F] : c.F →+* F :=
  (algebraMap (FractionRing R) F).comp ((algebraMap R (FractionRing R)).comp C.b)

def XFLevel (C : UChart.Fam Xo c R) (tK : SAB H (Sp (FractionRing R))) (m1 : SABMap tK C.t (jK R))
    (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _)) (F : Type) [Field F] [Algebra (FractionRing R) F]
    (I : letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F) : Prop :=
  ((I.ζ l.M' : Fˣ) : F) = toF C F ⟨zeta l.M', c.zeta_mem⟩ ∧
  ∀ (k : ℕ) (a : Dw.La) (σ : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G),
    ((k = l.A ∧ σ = Xo.univ.etaA a) ∨
      (k = l.M ∧ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La) ∧ σ = Xo.univ.eta a)) →
    ∀ x : TFK (R := R) F ⟶ C.P.A.A, C.P.ToA F k (I.ev k a) x →
      ∃ g : Sp F ⟶ tK.G.left, g ≫ m1.φ = x.left ≫ C.P.U.gen.inv.left ≫ pullback.fst C.t.G.hom (jK R) ∧
        g ≫ m2.φ = jFK (R := R) F ≫ C.y ≫ pullback.fst _ _ ≫ σ.left

def FiltGraded (C : UChart.Fam Xo c R) (Z : Submodule (𝓞 E) Dw.La) (F : Type) [Field F] [Algebra (FractionRing R) F]
    (I : letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F) : Prop :=
  ∀ n, 0 < n → ∀ a, (∃ q : QkPt C.P.D.toPre F n, QkPt.Equiv C.P.D.toPre F (I.ev n a) q ∧ q.y = 0) ↔
    ∃ b ∈ perp Dw Z, ∃ e, a = b + n • e

abbrev LowTate (C : UChart.Fam Xo c R) (D' : Datum H) (o' : Obj D' (lowLevel l) (baseKA (lowLevel l)) (lowS C))
    (F : Type) [Field F] [Algebra (FractionRing R) F] :=
  TateIso D' F (Over.mk (jFK (R := R) F ≫ jK R) ⟶ o'.t.G) (fun a g => g ≫ o'.t.act.act a)
    (fun n g g' z => Out.WeilIs o'.t.G o'.t.PP.L n g g' (unitOn z))

def LowGraded (C : UChart.Fam Xo c R) (Z : Submodule (𝓞 E) Dw.La) (D' : Datum H) (f : perp Dw Z →ₗ[𝓞 E] D'.La)
    (o' : Obj D' (lowLevel l) (baseKA (lowLevel l)) (lowS C)) (φB : o'.t.G.left ⟶ C.P.D.toPre.P.A.left)
    (F : Type) [Field F] [Algebra (FractionRing R) F]
    (I : letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F) (I' : LowTate C D' o' F) : Prop :=
  (∀ n, I'.ζ n = I.ζ n) ∧
  (∀ w, toUnit _ ≫ o'.etaA w = I'.ev (lowLevel l).A w) ∧
  (∀ w ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D'.La), toUnit _ ≫ o'.eta w = I'.ev l.M w) ∧
  ∀ n, 0 < n → ∀ a : perp Dw Z, ∃ q : QkPt C.P.D.toPre F n,
    QkPt.Equiv C.P.D.toPre F (I.ev n a) q ∧ q.y = 0 ∧ q.g.b.left = (I'.ev n (f a)).left ≫ φB

end GlobalTheory.LowDat
