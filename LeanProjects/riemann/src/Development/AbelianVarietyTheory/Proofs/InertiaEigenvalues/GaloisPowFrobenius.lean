import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.FrobAction

open GlobalTheory.BKReal

theorem galois_pow_frobenius : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (g : GQ l),
    ∃ m : ZMod a, ∀ x : Om l, x ^ l ^ a = x → g x = x ^ l ^ m.val := by
  intro l hl a _ g
  obtain ⟨z, ω, hω, hz, -⟩ := exists_gen l a
  have h1 := one_lt_pow_l l a
  have hmem : ∀ y : Fq l a, Per.σF g (Fq.val l a y) ∈ resSub l a := fun y => by
    rw [mem_resSub, ← map_pow, ← map_pow, Fq.pow_card]
  let φ : Fq l a →+* Fq l a := ((Per.σF g).comp (Fq.val l a)).codRestrict (resSub l a) hmem
  have hφ : ∀ y, Fq.val l a (φ y) = Per.σF g (Fq.val l a y) := fun _ => rfl
  letI : Algebra (ZMod l) (Fq l a) := ZMod.algebra _ _
  haveI : Fintype (Fq l a) := Fintype.ofFinite _
  let ψ : Fq l a →ₐ[ZMod l] Fq l a :=
    { φ with
      commutes' := fun r => by
        haveI : NeZero l := ⟨hl.out.ne_zero⟩
        obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective r
        simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
          MonoidHom.coe_coe, map_natCast] }
  have hb : Function.Bijective ψ := Finite.injective_iff_bijective.1 ψ.toRingHom.injective
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod l) (Fq l a)).2
    (AlgEquiv.ofBijective ψ hb)
  have hfr : ∀ (k : ℕ) (y : Fq l a), (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod l) (Fq l a) ^ k) y =
      y ^ l ^ k := fun k y => by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, FiniteField.frobeniusAlgEquivOfAlgebraic_apply, ZMod.card,
        ← pow_mul, ← pow_succ]
  have hφz : φ z = z ^ l ^ (n : ℕ) := by
    have := congrArg (fun e : Fq l a ≃ₐ[ZMod l] Fq l a => e z) hn
    simp only [hfr] at this
    exact this.symm
  have hrank : Module.finrank (ZMod l) (Fq l a) = a := by
    have h2 := Module.card_eq_pow_finrank (K := ZMod l) (V := Fq l a)
    rw [ZMod.card, ← Nat.card_eq_fintype_card, card_Fq] at h2
    exact (Nat.pow_right_injective hl.out.two_le h2).symm

  have key : ∀ y : OCb l, ((PreTilt.untilt (Per.σF g y) : Per.OC l) : ℂ_[l]) =
      Per.σC g ((PreTilt.untilt y : Per.OC l) : ℂ_[l]) := fun y => by
    rw [GlobalTheory.RingBasics.untilt_σF]
    exact GlobalTheory.RingIface.sigO_coe l g _
  have hu := GlobalTheory.MemLoc.IsTiltOf.untilt_eq hz
  have hgω : g ω = ω ^ l ^ (n : ℕ) := by
    apply (algebraMap (Om l) ℂ_[l]).injective
    have h3 := key (Fq.val l a z)
    rw [← hφ, hφz, map_pow, map_pow, SubmonoidClass.coe_pow, hu, GlobalTheory.RingBasics.σC_coe] at h3
    rw [map_pow]
    exact h3.symm
  refine ⟨((n : ℕ) : ZMod a), fun x hx => ?_⟩
  have hval : (((n : ℕ) : ZMod a)).val = n := ZMod.val_natCast_of_lt (lt_of_lt_of_eq n.2 hrank)
  rw [hval]
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [map_zero, zero_pow (pow_pos hl.out.pos _).ne']
  · have h4 : x ^ (l ^ a - 1) = 1 := mul_right_cancel₀ hx0 (by rw [← pow_succ, Nat.sub_add_cancel h1.le, hx, one_mul])
    haveI : NeZero (l ^ a - 1) := ⟨by omega⟩
    obtain ⟨k, -, rfl⟩ := hω.eq_pow_of_pow_eq_one h4
    rw [map_pow, hgω, ← pow_mul, ← pow_mul, mul_comm]

end GlobalTheory.FrobAction

example : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (g : GQ l), ∃ m : ZMod a, ∀ x : Om l, x ^ l ^ a = x → g x = x ^ l ^ m.val :=
  GlobalTheory.FrobAction.galois_pow_frobenius
