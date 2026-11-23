import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.QInertHolds

noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Formalism.UG
open PI.VolStabSW PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

def QProd : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → ¬ (IE (E := E) v).IsPrime →
    ∃ e : QE (E := E) v ≃+* (𝓞 F ⧸ v.asIdeal) × (𝓞 F ⧸ v.asIdeal),
      ∀ c, e (algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) c) = (c, c)

theorem sq_mem (h : IsCMExt F E σ) (x : QE (E := E) v) (hx : sigQ σ v x = x) :
    ∃ c, algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) c = x * x := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hs : Ideal.Quotient.mk (IE (E := E) v) (sigO σ y) = Ideal.Quotient.mk _ y := by
    rw [← sigQ_mk]; exact hx
  have hss : sigO σ (sigO σ y) = y := RingOfIntegers.ext (by simp only [sigO_coe]; exact sig_sig σ h _)
  obtain ⟨b, hb⟩ := fix_int σ h (y * sigO σ y) (by rw [map_mul, hss, mul_comm])
  refine ⟨Ideal.Quotient.mk _ b, ?_⟩
  rw [Ideal.Quotient.algebraMap_quotient_map_quotient, hb, map_mul, hs]

theorem idem_cases {k : Type} [Field k] {a : k} (ha : a * a = a) : a = 0 ∨ a = 1 := by
  have : a * (a - 1) = 0 := by rw [mul_sub, ha, mul_one, sub_self]
  rcases mul_eq_zero.1 this with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.1 h)

theorem qSplit_of (hP : QProd σ J ψ v) : QSplit σ J ψ v := by
  intro hstd hun hp
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  obtain ⟨e, he⟩ := hP hstd hun hp
  refine ⟨e, ?_⟩
  set z : QE (E := E) v := e.symm (1, 0) with hz
  have hez : e z = (1, 0) := by rw [hz, RingEquiv.apply_symm_apply]
  have hinv : ∀ x, sigQ σ v (sigQ σ v x) = x := sigQ_sigQ σ v hstd.1
  have hw : e (sigQ σ v z) = (0, 1) := by
    have hzz : z * z = z := e.injective (by rw [map_mul, hez]; simp)
    have hid : e (sigQ σ v z) * e (sigQ σ v z) = e (sigQ σ v z) := by rw [← map_mul, ← map_mul, hzz]
    have h1 := idem_cases ((Prod.fst_mul _ _).symm.trans (congrArg Prod.fst hid))
    have h2 := idem_cases ((Prod.snd_mul _ _).symm.trans (congrArg Prod.snd hid))
    have h10 : ((1, 0) : (𝓞 F ⧸ v.asIdeal) × (𝓞 F ⧸ v.asIdeal)).1 ≠ ((1, 0) : (𝓞 F ⧸ v.asIdeal) × (𝓞 F ⧸ v.asIdeal)).2 :=
      one_ne_zero
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exfalso
      have h0 : sigQ σ v z = 0 := (map_eq_zero_iff e e.injective).1 (Prod.ext h1 h2)
      have : e z = 0 := by rw [← hinv z, h0, map_zero, map_zero]
      rw [hez] at this
      exact one_ne_zero (congrArg Prod.fst this)
    · exact Prod.ext h1 h2
    · exfalso
      have hf : sigQ σ v z = z := e.injective (by rw [hez]; exact Prod.ext h1 h2)
      obtain ⟨c, hc⟩ := sq_mem σ v hstd.1 z hf
      rw [hzz] at hc
      have := he c
      rw [hc, hez] at this
      apply h10
      rw [this]
    · exfalso
      have h0 : sigQ σ v z = 1 := e.injective (by rw [map_one]; exact Prod.ext h1 h2)
      have : e z = 1 := by rw [← hinv z, h0, map_one, map_one]
      rw [hez] at this
      exact zero_ne_one (congrArg Prod.snd this)
  intro x
  have hx : x = algebraMap _ (QE (E := E) v) (e x).1 * z + algebraMap _ (QE (E := E) v) (e x).2 * (1 - z) := by
    apply e.injective
    rw [map_add, map_mul, map_mul, he, he, map_sub, map_one, hez]
    ext <;> simp
  have key : e (sigQ σ v x) = ((e x).2, (e x).1) := by
    conv_lhs => rw [hx]
    rw [map_add, map_mul, map_mul, sigQ_alg, sigQ_alg, map_sub, map_one, map_add, map_mul, map_mul, he, he,
      map_sub, map_one, hw]
    ext <;> simp
  rw [key]
  rfl

end PI.OmLocU.Red
