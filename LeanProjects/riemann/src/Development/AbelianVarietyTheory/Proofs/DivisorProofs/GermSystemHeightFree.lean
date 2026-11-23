import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {S : Scheme.{0}} {N : ℕ}
  {s : S ⟶ Sp R}

theorem act_zero_eq_one_wvs (o : Obj b N s) : o.act.act 0 = 1 := by
  have h := o.act.add 0 0
  rw [add_zero] at h
  exact mul_eq_left.mp h.symm

def ptModuleWvs (o : Obj b N s) (T : Over S) : Module (𝓞 D.F) (Additive (T ⟶ o.A)) where
  smul a g := Additive.ofMul (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O a))
  one_smul g := by
    show Additive.ofMul (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O 1)) = g
    rw [map_one, o.act.one, Category.comp_id]; rfl
  mul_smul a c g := by
    show Additive.ofMul (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O (a * c))) =
      Additive.ofMul ((g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)) ≫ o.act.act (algebraMap (𝓞 D.F) D.O a))
    rw [map_mul, o.act.mul, Category.assoc]
  smul_zero a := by
    haveI := o.act.hom (algebraMap (𝓞 D.F) D.O a)
    show Additive.ofMul ((1 : T ⟶ o.A) ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)) = Additive.ofMul 1
    rw [one_comp]
  smul_add a g h := by
    haveI := o.act.hom (algebraMap (𝓞 D.F) D.O a)
    show Additive.ofMul ((g.toMul * h.toMul) ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)) =
      Additive.ofMul ((g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)) * (h.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)))
    rw [mul_comp]
  add_smul a c g := by
    show Additive.ofMul (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O (a + c))) =
      Additive.ofMul ((g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)) * (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)))
    rw [map_add, o.act.add, comp_mul]
  zero_smul g := by
    show Additive.ofMul (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O 0)) = Additive.ofMul 1
    rw [map_zero, act_zero_eq_one_wvs, comp_one]

attribute [local instance] ptModuleWvs

theorem smul_toMul_wvs (o : Obj b N s) (T : Over S) (a : 𝓞 D.F) (g : Additive (T ⟶ o.A)) :
    (a • g).toMul = g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O a) := rfl

def kerWSubWvs (o o' : Obj b N s) (ψ : o.A ⟶ o'.A) [IsMonHom ψ]
    (hl : ∀ a : 𝓞 D.F, o.act.act (algebraMap (𝓞 D.F) D.O a) ≫ ψ = ψ ≫ o'.act.act (algebraMap (𝓞 D.F) D.O a))
    (w : Ideal (𝓞 D.F)) (T : Over S) : Submodule (𝓞 D.F) (Additive (T ⟶ o.A)) where
  carrier := {g | g.toMul ≫ ψ = 1 ∧ KilledBy o w g.toMul}
  zero_mem' := by
    refine ⟨one_comp ψ, fun a _ => ?_⟩
    haveI := o.act.hom (algebraMap (𝓞 D.F) D.O a)
    exact one_comp _
  add_mem' {g h} hg hh := by
    refine ⟨?_, fun a ha => ?_⟩
    · show (g.toMul * h.toMul) ≫ ψ = 1
      rw [mul_comp, hg.1, hh.1, _root_.mul_one]
    · haveI := o.act.hom (algebraMap (𝓞 D.F) D.O a)
      show (g.toMul * h.toMul) ≫ _ = 1
      rw [mul_comp, hg.2 a ha, hh.2 a ha, _root_.mul_one]
  smul_mem' c g hg := by
    refine ⟨?_, fun a ha => ?_⟩
    · show (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)) ≫ ψ = 1
      haveI := o'.act.hom (algebraMap (𝓞 D.F) D.O c)
      rw [Category.assoc, hl, ← Category.assoc, hg.1, one_comp]
    · show (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)) ≫ o.act.act (algebraMap (𝓞 D.F) D.O a) = 1
      haveI := o.act.hom (algebraMap (𝓞 D.F) D.O c)
      rw [Category.assoc, ← o.act.mul, ← map_mul, mul_comm, map_mul, o.act.mul, ← Category.assoc, hg.2 a ha,
        one_comp]

theorem card_kerW_eq_pow : ∀ {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R}
    {S : Scheme.{0}} {N : ℕ} {s : S ⟶ Sp R} (o o' : Obj b N s) (ψ : o.A ⟶ o'.A), IsMonHom ψ →
    (∀ a : 𝓞 D.F, o.act.act (algebraMap (𝓞 D.F) D.O a) ≫ ψ = ψ ≫ o'.act.act (algebraMap (𝓞 D.F) D.O a)) →
    ∀ (w : Ideal (𝓞 D.F)), w.IsMaximal → ∀ {k : Type} [Field k] (y : Sp k ⟶ S),
    Finite {g : Over.mk y ⟶ o.A // g ≫ ψ = 1 ∧ KilledBy o w g} →
    ∃ j' : ℕ, Nat.card {g : Over.mk y ⟶ o.A // g ≫ ψ = 1 ∧ KilledBy o w g} = Ideal.absNorm w ^ j' := by
  intro p _ D R _ b S N s o o' ψ hψ hl w hw k _ y hfin
  haveI := hψ
  let K := kerWSubWvs o o' ψ hl w (Over.mk y)
  let e : K ≃ {g : Over.mk y ⟶ o.A // g ≫ ψ = 1 ∧ KilledBy o w g} :=
    { toFun := fun x => ⟨x.1.toMul, x.2⟩
      invFun := fun g => ⟨Additive.ofMul g.1, g.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  haveI : Finite K := Finite.of_equiv _ e.symm
  have htor : Module.IsTorsionBySet (𝓞 D.F) K (w : Set (𝓞 D.F)) := by
    intro x a
    apply Subtype.ext
    show Additive.ofMul (x.1.toMul ≫ o.act.act (algebraMap _ _ a.1)) = Additive.ofMul 1
    rw [x.2.2 a.1 a.2]
  letI := Ideal.Quotient.field w
  letI : Module (𝓞 D.F ⧸ w) K := htor.module
  have hne : w ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hw (NumberField.RingOfIntegers.not_isField D.F)
  haveI : Finite (𝓞 D.F ⧸ w) := Ideal.finiteQuotientOfFreeOfNeBot w hne
  letI := Fintype.ofFinite (𝓞 D.F ⧸ w)
  letI := Fintype.ofFinite K
  refine ⟨Module.finrank (𝓞 D.F ⧸ w) K, ?_⟩
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := 𝓞 D.F ⧸ w),
    Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

end GlobalTheory.UPel.HT.ES
