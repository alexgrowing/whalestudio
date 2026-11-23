import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

structure Pre (b : Base D R) (s : S ⟶ Sp R) where
  A : Over S
  [grp : GrpObj A]
  [comm : IsCommMonObj A]
  ab : IsAbelianScheme A
  act : OActN D.O A
  P : LB (G2 A).left
  isLB : P.IsLB
  rig₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen
  rig₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen
  symm : LBIso P (P.pull (lift (snd A A) (fst A A)).left)
  ample : Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left)
  kerP : ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over S) (x : T ⟶ A),
    (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ e = 1
  rosati : ∀ c : D.O, LBIso (P.pull (lift (fst A A ≫ act.act c) (snd A A)).left)
    (P.pull (lift (fst A A) (snd A A ≫ act.act (D.star c).unop)).left)

attribute [instance] Pre.grp Pre.comm

def Pre.LieAt {b : Base D R} {s : S ⟶ Sp R} (o : Pre b s) {R' : Type} [CommRing R'] (x : Sp R' ⟶ S)
    (β : R →+* R') : Prop :=
  (∀ (R2 : Type) [CommRing R2] (g2 : R' →+* R2), ∀ v : epsPtR (spMap g2 ≫ x) ⟶ o.A,
    IsTanScal o.act (spMap g2 ≫ x) (algebraMap (𝓞 D.F) D.O D.ω) (g2 (β b.ρ)) v →
      ∃ w : Fin D.a → (epsPtR (spMap g2 ≫ x) ⟶ o.A),
        (∀ i, ∀ c : 𝓞 D.F, IsTanScal o.act (spMap g2 ≫ x) (algebraMap (𝓞 D.F) D.O c) (g2 (β (b.t i c))) (w i)) ∧
        v = (List.ofFn w).prod) ∧
  ∀ (k : Type) [Field k] [IsAlgClosed k] (g2 : R' →+* k), ∀ i,
    LieMult (o.act.toF D) (spMap g2 ≫ x) ((g2.comp β).comp (b.t i)) D.m

end GlobalTheory.UPel.HT
