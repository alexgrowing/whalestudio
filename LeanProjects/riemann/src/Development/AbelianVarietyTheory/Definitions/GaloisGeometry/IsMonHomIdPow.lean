import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsHeckeMapLevRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ForgetIsHeckeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPosOfCoprime

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory GlobalTheory.AV GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo

namespace GlobalTheory.DrinLev.HT.MulModel

open GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R}

theorem comp_pow' {S : Scheme.{0}} {X Y M : Over S} [MonObj M] (f : X ⟶ Y) (g : Y ⟶ M) (n : ℕ) :
    f ≫ g ^ n = (f ≫ g) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

theorem pow_comp' {S : Scheme.{0}} {G G' Z : Over S} [MonObj G] [MonObj G'] (φ : G ⟶ G')
    [IsMonHom φ] (x : Z ⟶ G) (n : ℕ) : (x ^ n) ≫ φ = (x ≫ φ) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.one_comp]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]

theorem isMonHom_id_pow {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ) :
    IsMonHom (𝟙 A ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact inferInstanceAs (IsMonHom (toUnit A ≫ η[A]))
  | succ n ih =>
    rw [pow_succ]
    exact inferInstanceAs (IsMonHom (lift (𝟙 A ^ n) (𝟙 A) ≫ μ[A]))

variable {G : HTGroup p} (L : Link D G)

theorem isIsogWit_mul {S : Scheme.{0}} {s : S ⟶ Sp R} {N : ℕ} (o : Obj b N s) (c : ℕ) (hc : c.Coprime p) :
    IsIsogWit L 1 o o (𝟙 o.A ^ c) (𝟙 o.A ^ c) c (c * c) := by
  haveI := isMonHom_id_pow o.A c
  refine ⟨inferInstance, inferInstance, fun a => ?_, fun a => ?_, ?_, ?_, hc, Nat.Coprime.mul hc hc,
    fun k _ _ t β ht => ?_⟩
  · haveI := o.act.hom a
    rw [comp_pow', pow_comp', Category.comp_id, Category.id_comp]
  · haveI := o.act.hom a
    rw [comp_pow', pow_comp', Category.comp_id, Category.id_comp]
  · rw [comp_pow', Category.comp_id, ← pow_mul]
  · rw [comp_pow', Category.comp_id, ← pow_mul]
  obtain ⟨I, hI⟩ := o.geom k t β ht
  refine ⟨I, I, hI, hI, fun n hn hnp x y => ?_⟩
  have e1 : ((c : ℕ) : ℤ) • L.actG 1 (inAf D x) = ((1 : ℕ) : ℤ) • L.actG 1 (inAf D (c • x)) := by
    simp only [map_one, Module.End.one_apply, Nat.cast_one, one_smul, natCast_zsmul]
    change c • ForgetHecke.inAfHom D x = ForgetHecke.inAfHom D (c • x)
    rw [map_nsmul]
  show I.ev n x ≫ 𝟙 o.A ^ c = I.ev n y ↔ ∃ v ∈ LaHat D, ((c : ℕ) : ℤ) • L.actG 1 (inAf D x) = inAf D y + n • v
  rw [e1, ForgetHecke.acts_one_iff L n hn hnp (c • x) y, comp_pow', Category.comp_id, ← TateIsoO.ev_nsmul,
    ← I.ker n hn hnp (c • x - y)]
  have hx : I.ev n (c • x) = I.ev n (c • x - y) * I.ev n y := by rw [← I.add, sub_add_cancel]
  rw [hx, mul_eq_right]

theorem isHeckeWit_mul {N : ℕ} (M : Model b N) (c : ℕ) (hc : c.Coprime p) :
    IsHeckeWit L 1 M M (𝟙 M.X) M.univ (𝟙 _ ^ c) (𝟙 _ ^ c) c (c * c) (GlobalTheory.UPel.HT.EtLev.LevForget.idMap M.univ) :=
  ⟨Category.id_comp _, isIsogWit_mul L M.univ c hc⟩

end GlobalTheory.DrinLev.HT.MulModel
