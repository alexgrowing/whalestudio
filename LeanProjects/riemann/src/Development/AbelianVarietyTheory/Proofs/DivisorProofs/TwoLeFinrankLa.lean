import Development.AbelianVarietyTheory.Definitions.Divisors.ToRepFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor

variable {S : Scheme.{0}}

def SiegKerBy {h M : ℕ} {B : Type} [CommRing B] {ζ : B} {s : S ⟶ Sp B} (c : SiegPre h M ζ s) (d : ℕ) : Prop :=
  Out.RelAmple c.A c.diag ∧
    ∀ (T : Over S) (x : T ⟶ c.A),
      (∃ t : (c.P.pull (lift (snd c.A T ≫ x) (fst c.A T)).left).Gen, t.IsGen) → x ^ d = 1

def IsSympLev {A : Over S} [GrpObj A] (P : LB (G2 A).left) (h M : ℕ) {B : Type} [CommRing B] (ζ : B)
    (t₁ : S ⟶ Sp B) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)) : Prop :=
  (∀ a b, lev (a + b) = lev a * lev b) ∧ (∀ a, lev a ^ M = 1) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : B →+* k) (z : kˣ), x ≫ t₁ = spMap β →
      (z : k) = β ζ →
      (∀ a, (toUnit (Over.mk x) ≫ lev a = 1 ↔ ∃ b, a = M • b)) ∧
      (∀ g : Over.mk x ⟶ A, g ^ M = 1 → ∃ a, toUnit _ ≫ lev a = g) ∧
      ∀ a b, Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) M (toUnit (Over.mk x) ≫ lev a) (toUnit _ ≫ lev b)
        (unitOn (z ^ (2 * omegaStd a b)))

theorem SiegPre.isSympLev {h M : ℕ} {B : Type} [CommRing B] {ζ : B} {s : S ⟶ Sp B} (c : SiegPre h M ζ s) :
    IsSympLev c.P h M ζ s c.lev :=
  ⟨c.lev_add, c.lev_tors, c.geom⟩

def SDRep (h M d : ℕ) : Prop :=
  ∃ (X : Scheme.{0}) (s : X ⟶ Sp (cycAway M)) (u : SiegPre h M (zetaAway M) s),
    SiegKerBy u d ∧ IsUnit ((d : ℕ) : Γ(X, ⊤)) ∧ IsQProjOver s ∧
    ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t),
      IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∃! f : S ⟶ X, f ≫ s = t ∧ SiegPB c u f

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

def HasLevelStructureOfLevel (b : Base D R) (N h M : ℕ) : Prop :=
  ∃ (X : Scheme.{0}) (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
    (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over X) ⟶ u.A)),
    IsSympLev u.P h M (zetaAway M) s₁ lev ∧ IsQProjOver s ∧
    ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (t₁ : S ⟶ Sp (cycAway M)) (o : Obj b N t)
      (l : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ o.A)), IsSympLev o.P h M (zetaAway M) t₁ l →
      ∃! f : S ⟶ X, f ≫ s = t ∧ f ≫ s₁ = t₁ ∧ ∃ m : ObjMap o u f, ∀ a, (l a).left ≫ m.φ = f ≫ (lev a).left

theorem Datum.two_le_finrank_La {p : ℕ} [Fact p.Prime] (D : Datum p) : 2 ≤ Module.finrank ℤ D.La := by
  haveI := D.freeLa
  haveI := D.finLa
  have hF : 0 < Module.finrank ℚ D.F := Module.finrank_pos
  have hpos : 0 < Module.finrank ℤ D.La := by
    rw [D.rankLa]
    exact Nat.mul_pos (Nat.mul_pos D.m_pos D.n_pos) hF
  by_contra hlt
  have h1 : Module.finrank ℤ D.La = 1 := by omega
  let bs := Module.finBasisOfFinrankEq ℤ D.La h1
  have hzero : ∀ x y : D.La, D.EF x y = 0 := by
    intro x y
    have hx : x = bs.repr x 0 • bs 0 := by
      conv_lhs => rw [← bs.sum_repr x]
      simp
    have hy : y = bs.repr y 0 • bs 0 := by
      conv_lhs => rw [← bs.sum_repr y]
      simp
    rw [hx, hy, LinearMap.map_smul, LinearMap.map_smul, LinearMap.smul_apply, D.alt, smul_zero, smul_zero]
  have hsub : ∀ x : D.La, x = 0 := by
    intro x
    apply D.nondeg
    ext y
    simp [hzero]
  have : Module.finrank ℤ D.La = 0 := by
    haveI : Subsingleton D.La := ⟨fun a b => by rw [hsub a, hsub b]⟩
    exact Module.finrank_zero_of_subsingleton
  omega

end GlobalTheory.UPel.HT
