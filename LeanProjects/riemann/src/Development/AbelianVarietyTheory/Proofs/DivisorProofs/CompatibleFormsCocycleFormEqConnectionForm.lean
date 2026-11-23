import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormsMapOfDividedPowerDerivationStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.ConnCocycle

attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler

theorem divPowerCompatDeRhamRelIdeal_zero_dividedPowers (R B : Type) [CommRing R] [CommRing B] [Algebra R B] : rel R (dp0 B) = ⊥ := by
  refine le_bot_iff.1 (Ideal.span_le.2 ?_)
  rintro _ ⟨n, a, ha, rfl⟩
  rw [Ideal.mem_bot.1 ha]
  simp [dpow_eval_zero]

theorem cocyc {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} (k : (KK (dp0 R) s).Z1)
    {T T' : Thick (dp0 R) s} (φ : T ⟶ T') :
    k.1.2 T' = km1 (SemiHom.of_algHom φ.φ) φ.dp (k.1.2 T) + kd0 R T'.δ (k.1.1 T T' φ) := by
  have h := congrArg (fun c ↦ c.2.1 T T' φ) (AddMonoidHom.mem_ker.1 k.2)
  change k.1.2 T' - _ - _ = 0 at h
  rw [sub_sub, sub_eq_zero] at h
  exact h

section
variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B]

def sndK : (diagExt R B).C →+ K1 R (dp0 B) :=
  AddMonoidHom.mk' (fun c ↦ Submodule.Quotient.mk (TrivSqZeroExt.snd c)) fun a b ↦ by
    rw [TrivSqZeroExt.snd_add, Submodule.Quotient.mk_add]

theorem sndK_apply (c : (diagExt R B).C) : sndK R B c = Submodule.Quotient.mk (TrivSqZeroExt.snd c) := rfl

theorem sndK_mul (x y : (diagExt R B).C) :
    sndK R B (x * y) = (diagExt R B).π x • sndK R B y + (diagExt R B).π y • sndK R B x := by
  show Submodule.Quotient.mk (x * y).snd = x.fst • Submodule.Quotient.mk (p := N1 R (dp0 B)) y.snd +
    y.fst • Submodule.Quotient.mk (p := N1 R (dp0 B)) x.snd
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add]
  congr 1

theorem sndK_alg (r : R) : sndK R B (algebraMap R (diagExt R B).C r) = 0 := by
  rw [sndK_apply, TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.snd_inl, Submodule.Quotient.mk_zero]

theorem sndK_dpow (n : ℕ) (a : (diagExt R B).C) (ha : a ∈ RingHom.ker ((diagExt R B).π : (diagExt R B).C →+* B)) :
    sndK R B ((divided₂ (diagExt R B).sq).dpow (n + 1) a) =
      (diagExt R B).π ((divided₂ (diagExt R B).sq).dpow n a) • sndK R B a := by
  rcases n with _ | m
  · rw [(divided₂ (diagExt R B).sq).dpow_one ha, (divided₂ (diagExt R B).sq).dpow_zero ha, map_one, one_smul]
  · have h0 : (diagExt R B).π ((divided₂ (diagExt R B).sq).dpow (m + 1) a) = 0 :=
      (divided₂ (diagExt R B).sq).dpow_mem (Nat.succ_ne_zero m) ha
    rw [squareZeroDividedPowers_dpow _ (by omega), map_zero, h0, zero_smul]

end

section
variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]

theorem deRhamAlgebraMap_sends_sectionOneForm (ρ : DR R (diagExt R B).C →+ DR R B) (hmul : ∀ x y, ρ (x * y) = ρ x * ρ y)
    (halg : ∀ c, ρ (algebraMap _ (DR R (diagExt R B).C) c) = algebraMap B (DR R B) ((diagExt R B).π c))
    (hD : ∀ c, ρ (ι1 (D R (diagExt R B).C c)) = ι1 (TrivSqZeroExt.snd c))
    (α : B →ₐ[R] (diagExt R B).C) (hα : ∀ b, (diagExt R B).π (α b) = b)
    (g : Ω[B⁄R] →+ Ω[B⁄R]) (hg : ∀ b c : B, g (b • D R B c) = b • TrivSqZeroExt.snd (α c))
    (κ : Ω[B⁄R]) : ρ (ι1 ((SemiHom.of_algHom α).m1 κ)) = ι1 (g κ) := by
  induction κ using ind1 with
  | h b c =>
    rw [SemiHom.oneFormMap_smul_semilinear, SemiHom.m1_D, map_smul, Algebra.smul_def, hmul, halg, hD, hg, map_smul,
      Algebra.smul_def]
    congr 2
    exact hα b
  | h0 => simp
  | ha x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add, map_add]

end

theorem form_eq_connForm : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (k : (KK (dp0 R) s).Z1)
    (f : Z1 (O (dp0 R) s)), k.1.1 = f.1 → ∀ (B : Type) [CommRing B] [Algebra R B] (x : Sp B ⟶ X)
    (hx : x ≫ s = spMap (algebraMap R B)),
    k.1.2 (Thick.triv B x hx) = Submodule.Quotient.mk (connForm f x hx) := by
  intro R _ X s k f hk B _ _ x hx
  obtain ⟨ρ, hadd, hmul, halg, hD, hrel, -, -⟩ := GlobalTheory.T.exists_formsMap_of_dividedPowerDerivation R B ⊥ (dp0 B) (diagExt R B).C
    (RingHom.ker ((diagExt R B).π : (diagExt R B).C →+* B)) (divided₂ (diagExt R B).sq) (diagExt R B).π
    (sndK R B) (sndK_mul R B) (sndK_alg R B) (sndK_dpow R B)
  have h0 := divPowerCompatDeRhamRelIdeal_zero_dividedPowers R B
  simp only [h0, Ideal.mem_bot, sub_sub, sub_eq_zero] at hadd hmul halg hD hrel
  let ρh : DR R (diagExt R B).C →+ DR R B := AddMonoidHom.mk' ρ hadd
  have hD' : ∀ c, ρh (ι1 (D R (diagExt R B).C c)) = ι1 (TrivSqZeroExt.snd c) := fun c ↦ hD c _ rfl
  let a := (diagExt R B).secHom hx (diagExt R B).i fun _ ↦ rfl
  let a' := (diagExt R B).secHom hx (diagSec R B) (fst_derSec _)
  have c1 := cocyc k a
  have c2 := cocyc k a'
  rw [hk] at c1 c2
  obtain ⟨κ, hκ⟩ := Submodule.Quotient.mk_surjective _ (k.1.2 (Thick.triv B x hx))
  obtain ⟨θ, hθ⟩ := Submodule.Quotient.mk_surjective _ (k.1.2 ((diagExt R B).thick x hx))
  rw [← hκ, ← hθ, divPowerCompatOneFormMap_mk, divPowerCompatFunctionDifferential_apply, ← Submodule.Quotient.mk_add, Submodule.Quotient.eq] at c1 c2
  have e1 : ρh (ι1 (θ - ((SemiHom.of_algHom a.φ).m1 κ + D R _ (f.1 _ _ a)))) = 0 := hrel _ c1
  have e2 : ρh (ι1 (θ - ((SemiHom.of_algHom a'.φ).m1 κ + D R _ (f.1 _ _ a')))) = 0 := hrel _ c2
  have r1 := deRhamAlgebraMap_sends_sectionOneForm ρh hmul halg hD' a.φ (fun _ ↦ rfl) 0 (fun b c ↦ by
    show (0 : Ω[B⁄R]) = b • TrivSqZeroExt.snd (TrivSqZeroExt.inl c : TrivSqZeroExt B Ω[B⁄R])
    rw [TrivSqZeroExt.snd_inl, smul_zero])
  have r2 := deRhamAlgebraMap_sends_sectionOneForm ρh hmul halg hD' a'.φ (fst_derSec _) (AddMonoidHom.id _) (fun b c ↦ by
    show b • D R B c = b • TrivSqZeroExt.snd (diagSec R B c)
    rw [snd_derSec])
  simp only [map_sub, map_add, r1, r2, hD', AddMonoidHom.zero_apply, AddMonoidHom.id_apply, map_zero,
    zero_add] at e1 e2
  rw [← hκ, Submodule.Quotient.eq]
  change ι1 _ ∈ rel R (dp0 B)
  rw [h0, Ideal.mem_bot, map_sub, sub_eq_zero]
  simp only [connForm, TrivSqZeroExt.snd_sub, map_sub]
  change ι1 κ = ι1 (TrivSqZeroExt.snd (f.1 _ _ a)) - ι1 (TrivSqZeroExt.snd (f.1 _ _ a'))
  linear_combination (norm := abel1) e1 - e2

end GlobalTheory.ConnCocycle
