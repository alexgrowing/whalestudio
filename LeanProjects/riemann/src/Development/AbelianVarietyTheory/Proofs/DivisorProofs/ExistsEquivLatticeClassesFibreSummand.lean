import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TraceDualDifferent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepNeZero
open NumberField
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.LatFibre

open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.SlopeTestRemainingChoices.EisFibre

variable {F : Type} [Field F] [NumberField F]

theorem unit_eq_one_of_mul {ε : (𝓞 F)ˣ} {b : F} (hb : b ≠ 0) (h : ((ε : 𝓞 F) : F) * b = b) : ε = 1 := by
  have h1 : ((ε : 𝓞 F) : F) = 1 := mul_right_cancel₀ hb (by rw [h, one_mul])
  apply Units.ext
  apply RingOfIntegers.coe_injective
  simp [h1]

def pairOf {𝔞 𝔟 : Frac F} (x : Σ _β : NzCls 𝔟, (latM 𝔞 : Set F)) : LatPair 𝔞 𝔟 :=
  ⟨((x.2 : F), rep x.1), x.2.2, rep_mem x.1, fun h => rep_ne_zero x.1 (congrArg Prod.snd h)⟩

theorem out_mk {𝔞 𝔟 : Frac F} (p : LatPair 𝔞 𝔟) :
    ∃ ε : (𝓞 F)ˣ, (Quotient.mk (latRel 𝔞 𝔟) p).out.1.1 = ((ε : 𝓞 F) : F) * p.1.1 ∧
      (Quotient.mk (latRel 𝔞 𝔟) p).out.1.2 = ((ε : 𝓞 F) : F) * p.1.2 :=
  Quotient.exact (Quotient.out_eq (Quotient.mk (latRel 𝔞 𝔟) p)).symm

private lemma ringOfIntegers_unit_coe_ne_zero (ε : (𝓞 F)ˣ) : ((ε : 𝓞 F) : F) ≠ 0 :=
  right_ne_zero_of_mul_eq_one (unit_inv_mul ε)

theorem out_mk_ne {𝔞 𝔟 : Frac F} (x : Σ _β : NzCls 𝔟, (latM 𝔞 : Set F)) :
    (Quotient.mk (latRel 𝔞 𝔟) (pairOf x)).out.1.2 ≠ 0 := by
  obtain ⟨ε, -, h2⟩ := out_mk (pairOf x)
  rw [h2]
  exact mul_ne_zero (ringOfIntegers_unit_coe_ne_zero ε) (rep_ne_zero x.1)

def fibreMap (𝔞 𝔟 : Frac F) (x : Σ _β : NzCls 𝔟, (latM 𝔞 : Set F)) :
    {c : Quotient (latRel 𝔞 𝔟) // c.out.1.2 ≠ 0} :=
  ⟨Quotient.mk _ (pairOf x), out_mk_ne x⟩

theorem fibreMap_injective (𝔞 𝔟 : Frac F) : Function.Injective (fibreMap 𝔞 𝔟) := by
  rintro ⟨β, a⟩ ⟨β', a'⟩ h
  have h' : Quotient.mk (latRel 𝔞 𝔟) (pairOf ⟨β, a⟩) = Quotient.mk (latRel 𝔞 𝔟) (pairOf ⟨β', a'⟩) :=
    congrArg Subtype.val h
  obtain ⟨ε, h1, h2⟩ := Quotient.exact h'
  have hβ : β = β' :=
    (Quotient.out_eq (s := unitRel 𝔟) β).symm.trans
      ((Quotient.sound (s := unitRel 𝔟) (a := Quotient.out (s := unitRel 𝔟) β)
        (b := Quotient.out (s := unitRel 𝔟) β') ⟨ε, h2⟩).trans (Quotient.out_eq (s := unitRel 𝔟) β'))
  subst hβ
  have hε : ε = 1 := unit_eq_one_of_mul (rep_ne_zero β) h2.symm
  subst hε
  have haa : a = a' := Subtype.ext (by simpa [pairOf] using h1.symm)
  subst haa
  rfl

theorem fibreMap_surjective (𝔞 𝔟 : Frac F) : Function.Surjective (fibreMap 𝔞 𝔟) := by
  rintro ⟨c, hc⟩
  let b : NzElt 𝔟 := ⟨c.out.1.2, c.out.2.2.1, hc⟩
  obtain ⟨ε, hε⟩ : ∃ ε : (𝓞 F)ˣ,
      rep (Quotient.mk (unitRel 𝔟) b : NzCls 𝔟) = ((ε : 𝓞 F) : F) * c.out.1.2 :=
    Quotient.exact (Quotient.out_eq (Quotient.mk (unitRel 𝔟) b)).symm
  have ha : ((ε : 𝓞 F) : F) * c.out.1.1 ∈ latM 𝔞 := by
    have hs := (latM 𝔞 : Submodule (𝓞 F) F).smul_mem (ε : 𝓞 F) c.out.2.1
    rwa [Algebra.smul_def] at hs
  refine ⟨⟨(Quotient.mk (unitRel 𝔟) b : NzCls 𝔟), ⟨_, ha⟩⟩, ?_⟩
  apply Subtype.ext
  show Quotient.mk (latRel 𝔞 𝔟) (pairOf _) = c
  conv_rhs => rw [← Quotient.out_eq c]
  exact (Quotient.sound (s := latRel 𝔞 𝔟) (a := c.out) ⟨ε, rfl, hε⟩).symm

theorem exists_equiv : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F),
    ∃ e : (Σ _β : GlobalTheory.SlopeTestRemainingChoices.EisFibre.NzCls 𝔟, (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞 : Set F)) ≃
      {c : Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟) // c.out.1.2 ≠ 0},
      ∀ (k : ℕ), Even k → ∀ (σ : ℂ) (z : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) (x : Σ _β : GlobalTheory.SlopeTestRemainingChoices.EisFibre.NzCls 𝔟, (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞 : Set F)),
        GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 k σ z (e x).1 = GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisTerm k σ z ((x.2 : F), GlobalTheory.SlopeTestRemainingChoices.EisFibre.rep x.1) := by
  intro F _ _ _ 𝔞 𝔟
  refine ⟨Equiv.ofBijective (fibreMap 𝔞 𝔟) ⟨fibreMap_injective 𝔞 𝔟, fibreMap_surjective 𝔞 𝔟⟩, ?_⟩
  intro k hk σ z x
  exact eisClass_mk 𝔞 𝔟 hk σ z (pairOf x)

end GlobalTheory.LatFibre
