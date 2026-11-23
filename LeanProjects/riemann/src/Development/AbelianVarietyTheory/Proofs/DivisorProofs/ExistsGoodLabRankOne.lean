import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ThetaTowerRecognition
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionMapsCompatibleInLevel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.Recog

variable {R : Type} [CommRing R] [IsDomain R]

structure GoodLab (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F]
    (f : ∀ k : ℕ, QkPt D F k → (TFK (R := R) F ⟶ A.A)) : Prop where
  pow : ∀ k, 1 ≤ k → ∀ p, f k p ^ k = 1
  onto : ∀ k, 1 ≤ k → ∀ x : TFK (R := R) F ⟶ A.A, x ^ k = 1 → ∃ p, f k p = x
  eqv : ∀ k, 1 ≤ k → ∀ p p', f k p = f k p' ↔ QkPt.Equiv D F p p'
  add : ∀ k, 1 ≤ k → ∀ p p' p'', QkAdd p p' p'' → f k p'' = f k p * f k p'
  weil : ∀ k, 1 ≤ k → ∀ p p' (z : Fˣ), WeilQkIs D F k p p' z → WeilIs A.A A.L k (f k p) (f k p') (unitOn z)
  level : ∀ k m N, 1 ≤ k → 1 ≤ m → N = k * m → ∀ (p : QkPt D F k) (q : QkPt D F N), q.y = m • p.y → q.g = p.g →
    f N q = f k p

def Lies {W : Type} [CommRing W] [IsDomain W] (φ : R →+* W) {D : DegPre R} {D' : DegPre W} (hD : IsPullDeg φ D D')
    {F F' : Type} [Field F] [Field F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F']
    [Algebra (FractionRing W) F'] (em : F →+* F') {k : ℕ} (p : QkPt D F k) (p' : QkPt D' F' k) : Prop :=
  ∃ p₁ : QkPt D F' k, QkExt em p p₁ ∧ p'.y = hD.xe.symm p₁.y ∧ IsPullGtF φ hD F' p₁.g p'.g

theorem exists_goodLab [CharZero R] {I : Ideal R} (hR : AdmBase R I) {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (U : Unif I D A G) (F : Type) [Field F]
    [IsAlgClosed F] [Algebra (FractionRing R) F] :
    ∃ f, GoodLab D.toPre A F f ∧ ∀ k, 1 ≤ k → ∀ p x, QkToAkU U.toUnifPre F k p x ↔ x = f k p := by
  have H : ∀ k : ℕ, ∃ f : QkPt D.toPre F k → (TFK (R := R) F ⟶ A.A), 1 ≤ k →
      GlobalTheory.UT.Tors U.toUnifPre F k f ∧ ∀ p, f p ^ k = 1 := fun k => by
    by_cases hk : 1 ≤ k
    · obtain ⟨f, hf⟩ := GlobalTheory.TorsionIso.torsion_clause R _ hR D A G hG U F k hk
      exact ⟨f, fun _ => hf⟩
    · exact ⟨fun _ => 1, fun h => absurd h hk⟩
  choose f hf using H
  refine ⟨f, ⟨fun k hk => (hf k hk).2, fun k hk => (hf k hk).1.2.1, fun k hk => (hf k hk).1.2.2.1,
    fun k hk => (hf k hk).1.2.2.2.1, fun k hk p p' z => ((hf k hk).1.2.2.2.2 p p' z).1, ?_⟩, fun k hk => (hf k hk).1.1⟩
  intro k m N hk hm hN p q hy hg
  have hN1 : 1 ≤ N := hN ▸ Nat.mul_pos hk hm
  exact (((hf N hN1).1.1 q _).1 (((GlobalTheory.LevelCompat.qkToAkU_level GlobalTheory.firstFiveLaws R _ hR D A G hG U F k m N hk hm hN p q
    (f k p)).1 hy hg).1 (((hf k hk).1.1 p _).2 rfl))).symm

end GlobalTheory.Mum.Recog
