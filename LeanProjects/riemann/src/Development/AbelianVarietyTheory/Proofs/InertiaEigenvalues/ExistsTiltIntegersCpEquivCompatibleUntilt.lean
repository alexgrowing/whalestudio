import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
import GroundTheory.PAdicHodge.TiltValuation
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

open GroundTheory.PAdicHodge

variable (l : ℕ) [Fact l.Prime]

theorem oc_eq_normInteger : (𝓞_ℂ_[l]).toSubring = normInteger ℂ_[l] := by
  ext x
  rw [mem_normInteger, ← GlobalTheory.RingBasics.mem_OC]
  rfl

noncomputable def ocEquiv : OC l ≃+* normInteger ℂ_[l] := RingEquiv.subringCongr (oc_eq_normInteger l)

theorem coe_ocEquiv (x : OC l) : ((ocEquiv l x : normInteger ℂ_[l]) : ℂ_[l]) = (x : ℂ_[l]) := rfl

theorem span_map_ocEquiv :
    Ideal.span {(l : normInteger ℂ_[l])} = (Ideal.span {(l : OC l)}).map ((ocEquiv l : OC l →+* normInteger ℂ_[l])) := by
  rw [Ideal.map_span, Set.image_singleton]; simp

noncomputable def modEquiv : ModP (OC l) l ≃+* ModP (normInteger ℂ_[l]) l :=
  Ideal.quotientEquiv _ _ (ocEquiv l) (span_map_ocEquiv l)

noncomputable def flTo : Fl l →+* PreTilt (normInteger ℂ_[l]) l :=
  Perfection.map l (modEquiv l : ModP (OC l) l →+* ModP (normInteger ℂ_[l]) l)

noncomputable def flFrom : PreTilt (normInteger ℂ_[l]) l →+* Fl l :=
  Perfection.map l ((modEquiv l).symm : ModP (normInteger ℂ_[l]) l →+* ModP (OC l) l)

theorem coeff_flTo (x : Fl l) (n : ℕ) :
    Perfection.coeff _ l n (flTo l x) = modEquiv l (Perfection.coeff _ l n x) := rfl

theorem coeff_flFrom (x : PreTilt (normInteger ℂ_[l]) l) (n : ℕ) :
    Perfection.coeff _ l n (flFrom l x) = (modEquiv l).symm (Perfection.coeff _ l n x) := rfl

noncomputable def flEquiv : Fl l ≃+* PreTilt (normInteger ℂ_[l]) l :=
  RingEquiv.ofRingHom (flTo l) (flFrom l)
    (RingHom.ext fun x => Perfection.ext fun n => by
      change Perfection.coeff _ l n (flTo l (flFrom l x)) = Perfection.coeff _ l n x
      rw [coeff_flTo, coeff_flFrom, RingEquiv.apply_symm_apply])
    (RingHom.ext fun x => Perfection.ext fun n => by
      change Perfection.coeff _ l n (flFrom l (flTo l x)) = Perfection.coeff _ l n x
      rw [coeff_flFrom, coeff_flTo, RingEquiv.symm_apply_apply])

theorem flEquiv_apply (x : Fl l) : flEquiv l x = flTo l x := rfl

theorem untilt_flTo (x : Fl l) : (flTo l x).untilt = ocEquiv l x.untilt := by
  refine Perfection.teichmuller_spec (I := Ideal.span {(l : normInteger ℂ_[l])}) fun n => ?_
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (Perfection.coeff _ l n x)
  refine ⟨ocEquiv l y, ?_, ?_⟩
  · rw [coeff_flTo, ← hy]
    rfl
  · have := (Perfection.teichmuller_sModEq hy).symm
    rw [SModEq.sub_mem, GlobalTheory.RingBasics.mem_span_pow_OC] at this
    have hl : ((l : normInteger ℂ_[l]) : ℂ_[l]) = (l : ℂ_[l]) := by simp
    rw [SModEq.sub_mem, mem_span_singleton_pow_iff, ← map_pow, ← map_sub, coe_ocEquiv, hl]
    exact this

theorem exists_flEquiv_untilt : ∀ (l : ℕ) [Fact l.Prime], ∃ e : Fl l ≃+* PreTilt (GroundTheory.PAdicHodge.normInteger ℂ_[l]) l,
    ∀ x : Fl l, ((PreTilt.untilt (e x) : GroundTheory.PAdicHodge.normInteger ℂ_[l]) : ℂ_[l]) = sh x := by
  intro l _
  refine ⟨flEquiv l, fun x => ?_⟩
  rw [flEquiv_apply, untilt_flTo, coe_ocEquiv]
  rfl

end GlobalTheory.PSer
