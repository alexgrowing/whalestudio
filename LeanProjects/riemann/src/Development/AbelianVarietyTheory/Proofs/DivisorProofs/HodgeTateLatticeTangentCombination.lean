import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentFlagVec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDlogUniqueModuloP

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ShFam.Pad MonObj
open Formalism.MainNotions.DIV.Cons (intO)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv actR)
open GlobalTheory.LieMet (tanOf isTan_tv tan_ext isComb_iff)
open GlobalTheory.LocM.Frm (bcTan)
open GlobalTheory.DlogEx (red dlog red_left)

namespace GlobalTheory.HTStable

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {O : Type} [CommRing O] {x : Sp O ⟶ X}

theorem comp_pow_eq_one {T : Over X} (φ : t.G ⟶ t.G) [IsMonHom φ] {q : ℕ} {g : T ⟶ t.G} (hg : g ^ q = 1) :
    (g ≫ φ) ^ q = 1 := by
  have h : ∀ k : ℕ, (g ≫ φ) ^ k = (g ^ k) ≫ φ := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero, MonObj.one_comp]
    | succ k ih => rw [pow_succ, pow_succ, ih, MonObj.mul_comp]
  rw [h, hg, MonObj.one_comp]

def actChar {q : ℕ} (c : TorsChar t x q) (a : 𝓞 E) : TorsChar t x q where
  χ B _ _ _ g := c.χ B (g ≫ t.act.act a)
  mul B _ _ _ g g' hg hg' := by
    haveI := t.act.hom a
    rw [MonObj.mul_comp]
    exact c.mul B _ _ (comp_pow_eq_one _ hg) (comp_pow_eq_one _ hg')
  nat B B' _ _ _ _ _ _ φ g g' hg e := by
    haveI := t.act.hom a
    refine c.nat B B' φ _ _ (comp_pow_eq_one _ hg) ?_
    rw [Over.comp_left, Over.comp_left, e, Category.assoc]

theorem dlogDvd_sum {p m : ℕ} (v : TanM x t.G) (hv : DlogDvd t x p m (tv v).left) {n : ℕ} (a : Fin n → 𝓞 E)
    (c : Fin n → O) : DlogDvd t x p m (tv (∑ j, c j • actR t.act (a j) v)).left := by
  intro k χ g hg
  have hq : ((p ^ k : ℕ) : O ⧸ Ideal.span {(p : O) ^ k}) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(p : O) ^ k})), Ideal.Quotient.eq_zero_iff_mem, Nat.cast_pow]
    exact Ideal.mem_span_singleton_self _
  have h3 : g = red _ (∑ j, c j • actR t.act (a j) v) := Over.OverMorphism.ext (by rw [hg]; rfl)
  rw [h3]
  show dlog _ hq χ _ ∈ _
  rw [map_sum]
  refine Ideal.sum_mem _ fun j _ => ?_
  rw [map_smul, Algebra.smul_def]
  refine Ideal.mul_mem_left _ _ ?_
  have h := hv k (actChar χ (a j)) (red _ v) rfl
  have e : red (O ⧸ Ideal.span {(p : O) ^ k}) (actR t.act (a j) v) = red _ v ≫ t.act.act (a j) :=
    (Category.assoc _ _ _).symm
  show (χ.χ (DualNumber (O ⧸ Ideal.span {(p : O) ^ k})) (red (O ⧸ Ideal.span {(p : O) ^ k}) (actR t.act (a j) v)) : DualNumber (O ⧸ Ideal.span {(p : O) ^ k})).snd ∈ _
  rw [e]
  exact h

theorem latHT_comb_act : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (p : ℕ) (x : Sp C ⟶ X) (w : Sp (DualNumber C) ⟶ t.G.left), IsTanAtG t x w → w ∈ latHT t p x → ∀ (n : ℕ) (a : Fin n → 𝓞 E) (c : Fin n → C), (∀ j, ‖c j‖ ≤ 1) → ∀ W : Sp (DualNumber C) ⟶ t.G.left, IsCombAtG t x (fun j => w ≫ (t.act.act (a j)).left) c W → W ∈ latHT t p x := by
  intro E _ _ _ H X t C _ _ p x w hw hl n a c hc W hW
  obtain ⟨xO, hx, m, vO, hvO, hbc, hd⟩ := hl
  let cO : Fin n → ↥(intO C) := fun j => ⟨c j, hc j⟩
  let V : TanM xO t.G := ∑ j, cO j • actR t.act (a j) (tanOf hvO)
  refine ⟨xO, hx, m, (tv V).left, isTan_tv V, ?_, dlogDvd_sum (tanOf hvO) hd a cO⟩
  have hu := (isComb_iff (fun j => actR t.act (a j) (tanOf hw)) c (∑ j, c j • actR t.act (a j) (tanOf hw))).2 rfl
  have hWe : (tv (∑ j, c j • actR t.act (a j) (tanOf hw))).left = W :=
    ((isCombAtG_iff t x (fun j => tv (actR t.act (a j) (tanOf hw))) c _).1 hu).symm.trans
      ((isCombAtG_iff t x (fun j => tv (actR t.act (a j) (tanOf hw))) c _).1 hW)
  have h1 : bcTan (intO C).subtype hx (tanOf hvO) = ((p : C) ^ m) • tanOf hw := tan_ext hbc
  have h2 : ∀ j, bcTan (intO C).subtype hx (actR t.act (a j) (tanOf hvO)) =
      actR t.act (a j) (bcTan (intO C).subtype hx (tanOf hvO)) := fun j => tan_ext (Category.assoc _ _ _).symm
  have h3 : bcTan (intO C).subtype hx V = ((p : C) ^ m) • ∑ j, c j • actR t.act (a j) (tanOf hw) := by
    simp only [V, map_sum, map_smulₛₗ, h2, h1, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact smul_comm (c j) ((p : C) ^ m) _
  rw [← hWe]
  exact congrArg (fun z => (tv z).left) h3

end GlobalTheory.HTStable
