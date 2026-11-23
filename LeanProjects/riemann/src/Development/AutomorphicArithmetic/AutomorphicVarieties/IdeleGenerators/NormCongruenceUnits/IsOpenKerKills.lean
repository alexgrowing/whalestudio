import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.NormCongruenceUnits.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.NormOneOfFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ShapeFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ResFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.DenseRangeUnitsR
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.IsAlgOfPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.AlgCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.UpQuad
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.GaloisRepRankTwoRealOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.SelfTwGal
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.InfinitesimalCharacterPullback.HasInfCharPullSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.FrobDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.IneFixRoots

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published
open scoped Matrix

namespace UpperTheory.V.Sd

section CongLemmas

variable {l : ℕ} [Fact l.Prime]

private theorem cong_trans {a b c : (Qbar l)ˣ} (h : Cong a b) (h' : Cong b c) : Cong a c := by
  unfold Cong at *
  have := IsUltrametricDist.norm_add_le_max ((a : Qbar l) - b) ((b : Qbar l) - c)
  rw [sub_add_sub_cancel] at this
  exact this.trans_lt (max_lt h h')

private theorem cong_norm {a b : (Qbar l)ˣ} (h : Cong a b) (hb : ‖(b : Qbar l)‖ = 1) : ‖(a : Qbar l)‖ = 1 := by
  unfold Cong at h
  have := IsUltrametricDist.norm_eq_of_add_norm_lt_max (x := (a : Qbar l)) (y := -(b : Qbar l))
    (by rw [← sub_eq_add_neg, norm_neg, hb]; exact h.trans_le (le_max_right _ _))
  rw [this, norm_neg, hb]

private theorem cong_mul_right {a b : (Qbar l)ˣ} (h : Cong a b) (c : (Qbar l)ˣ) (hc : ‖(c : Qbar l)‖ = 1) :
    Cong (a * c) (b * c) := by
  unfold Cong at *
  rw [Units.val_mul, Units.val_mul, ← sub_mul, norm_mul, hc, mul_one]
  exact h

private theorem cong_mul {a b c d : (Qbar l)ˣ} (h : Cong a b) (h' : Cong c d) (hb : ‖(b : Qbar l)‖ = 1)
    (hd : ‖(d : Qbar l)‖ = 1) : Cong (a * c) (b * d) := by
  refine cong_trans (cong_mul_right h c (cong_norm h' hd)) ?_
  rw [mul_comm b c, mul_comm b d]
  exact cong_mul_right h' b hb

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]

private theorem cyc_val (s : G F Ω) :
    ((cycBar F Ω l s : (Qbar l)ˣ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) ((cycZ F Ω l s : ℤ_[l]) : ℚ_[l]) := rfl

end CongLemmas

section Gal

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

end Gal

section Shape

variable {l : ℕ} [Fact l.Prime] {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

private theorem cont_units {Γ R : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Monoid R]
    [TopologicalSpace R] (f : Γ →* Rˣ) (h : Continuous fun s => (f s : R)) : Continuous f := by
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  simp only [← map_inv]
  exact h.comp continuous_inv

private theorem cyc_ine [IsAlgClosure F Ω] {A : ValuationSubring Ω} (hA : ¬ A.valuation (l : Ω) < 1) {s : G F Ω}
    (hs : s ∈ Ine (F := F) A) : cycBar F Ω l s = 1 := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  have h' : ((cycZ F Ω l s : ℤ_[l]ˣ) : ℤ_[l]) = ((1 : ℕ) : ℤ_[l]) := by
    refine PadicInt.ext_of_toZModPow.mp fun n => ?_
    have hln : ¬ A.valuation (((l ^ n : ℕ) : Ω)) < 1 := by
      have h2 : A.valuation (l : Ω) = 1 :=
        le_antisymm ((A.valuation_le_one_iff _).mpr (natCast_mem A l)) (not_lt.mp hA)
      rw [Nat.cast_pow, Valuation.map_pow, h2, one_pow]
      exact lt_irrefl 1
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
    have hN0 : l ^ n ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
    set c := PadicInt.toZModPow n ((cycZ F Ω l s : ℤ_[l]ˣ) : ℤ_[l]) with hc
    have hσζ : s ζ = ζ ^ c.val := cyclotomicCharacter.spec (L := Ω) l
      (MulSemiringAction.toRingAut (Ω ≃ₐ[F] Ω) Ω s) ζ hζ.pow_eq_one
    have hlt := hs.2 ζ (ReciprocityTheory.Gal.valuation_eq_one_of_pow_eq_one A hN0 hζ.pow_eq_one).le
    rw [hσζ] at hlt
    have heq : ζ ^ c.val = ζ := by
      refine ReciprocityTheory.Gal.eq_of_pow_eq_one A hln ?_ hζ.pow_eq_one hlt
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    have heq' : (hζ.isUnit hN0).unit ^ c.val = (hζ.isUnit hN0).unit ^ 1 :=
      Units.ext (by simpa using heq)
    have hu : IsPrimitiveRoot (hζ.isUnit hN0).unit (l ^ n) :=
      IsPrimitiveRoot.coe_units_iff.mp (by simpa using hζ)
    rw [pow_eq_pow_iff_modEq, ← hu.eq_orderOf] at heq'
    rw [map_natCast, ← ZMod.natCast_zmod_val c]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr heq'
  apply Units.ext
  rw [cyc_val, h']; simp

private theorem ordAt_tw {n : ℕ} {r : G F Ω →* GL (Fin n) (Qbar l)} {m : Fin n → ℤ} {ψ : Fin n → G F Ω →* (Qbar l)ˣ}
    {A : ValuationSubring Ω} (h : OrdAt r m ψ A) (δ : G F Ω →* (Qbar l)ˣ) (hn : ∀ s, ‖(δ s : Qbar l)‖ = 1) (a : ℤ)
    (hδ : ∀ s ∈ Ine (F := F) A, δ s = cycBar F Ω l s ^ a) :
    OrdAt (tw r δ) (fun i => m i + a) (fun i => ψ i * δ) A := by
  obtain ⟨κ, h1, h2, h3⟩ := h
  refine ⟨_, (shapeFacts l _ n r δ).2.2.1 _ κ h1, fun i s hs => ?_, fun i s => cong_mul_right (h3 i s) _ (hn _)⟩
  rw [zpow_add, ← h2 i s hs, ← hδ s hs]; rfl

end Shape

section Up

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

end Up

end UpperTheory.V.Sd
