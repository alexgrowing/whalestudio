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

namespace GlobalTheory.BKGal.PrismTwist

variable {l : ℕ} [hl : Fact l.Prime] (a : ℕ) [NeZero a] {e : ℕ} [NeZero e] (ϖ : GlobalTheory.BKReal.PiSys l e)

theorem ev_injective : Function.Injective (ϖ.ev a) := by
  let Q := OCb l ⧸ Ideal.span {ϖ.flat}
  have hn : ¬ IsUnit ϖ.flat := fun h => ϖ.not_isUnit_teich (h.map (WittVector.teichmuller l))
  have : Nontrivial Q := Ideal.Quotient.nontrivial_iff.2 (by rwa [Ne, Ideal.span_singleton_eq_top])
  have : CharP Q l := (CharP.charP_iff_prime_eq_zero hl.out).2 (by
    rw [← map_natCast (Ideal.Quotient.mk _), CharP.cast_eq_zero, map_zero])
  let r : Ainf l →+* WittVector l Q := WittVector.map (Ideal.Quotient.mk _)
  have hr : Function.Injective (r.comp (wA l a).toRingHom) := fun x y h => WittVector.ext fun n =>
    ((Ideal.Quotient.mk (Ideal.span {ϖ.flat})).comp (Fq.val l a)).injective
      (congrArg (WittVector.coeff · n) h)
  have hR : r ϖ.teich = 0 := by
    change WittVector.map (Ideal.Quotient.mk _) (WittVector.teichmuller l ϖ.flat) = 0
    rw [WittVector.map_teichmuller, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _),
      WittVector.teichmuller_zero]
  have ht : ϖ.teich ≠ 0 := fun h => by
    have := congrArg (fun w : Ainf l => w.coeff 0) h
    simp only [PiSys.teich, WittVector.teichmuller_coeff_zero, WittVector.zero_coeff] at this
    exact ϖ.flat_ne_zero this
  have key : ∀ n (x : (Wq l a)⟦X⟧), ϖ.ev a x = 0 → coeff n x = 0 := by
    have h0 : ∀ x : (Wq l a)⟦X⟧, ϖ.ev a x = 0 → constantCoeff x = 0 := fun x hx => by
      rw [x.eq_X_mul_shift_add_const, map_add, map_mul, PiSys.ev_X, PiSys.ev_C] at hx
      have h1 := congrArg r hx
      rw [map_add, map_mul, hR, zero_mul, zero_add, map_zero] at h1
      exact hr (h1.trans (map_zero _).symm)
    intro n
    induction n with
    | zero => exact fun x hx => by simpa using h0 x hx
    | succ n ih =>
      intro x hx
      have h1 := h0 x hx
      rw [x.eq_X_mul_shift_add_const, h1, map_zero, add_zero, map_mul, PiSys.ev_X] at hx
      have h2 := ih _ ((mul_eq_zero.1 hx).resolve_left ht)
      rw [coeff_mk] at h2
      exact h2
  refine (injective_iff_map_eq_zero _).2 fun x hx => PowerSeries.ext fun n => ?_
  rw [key n x hx, map_zero]

theorem σA_frobenius (g : GQ l) (x : Ainf l) :
    Per.σA g (WittVector.frobenius x) = WittVector.frobenius (Per.σA g x) := by
  rw [WittVector.frobenius_eq_map_frobenius]
  refine WittVector.ext fun n => ?_
  rw [GlobalTheory.RingIface.sigA_coeff, WittVector.map_coeff, WittVector.map_coeff, GlobalTheory.RingIface.sigA_coeff,
    frobenius_def, frobenius_def, map_pow]

end GlobalTheory.BKGal.PrismTwist

theorem GlobalTheory.BKGal.PrismTwist.hom_restrict : ∀ {l : ℕ} [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (g : GQ l) (σ : ↥(OL (ϖ.field a)) →+* ↥(OL (ϖ.field a))), (∀ x, (((σ x : ↥(ϖ.field a).1) : Om l)) = g ((x : ↥(ϖ.field a).1) : Om l)) → ∀ (ψ : (Wq l a)⟦X⟧ →+* (Wq l a)⟦X⟧), (∀ x, ϖ.ev a (ψ x) = Per.σA g (ϖ.ev a x)) → ∃ H : Hom (ϖ.prism a) ((ϖ.prism a).restrict σ), ∀ x, H.f x = ψ x := by
  intro l _ a e _ _ ϖ g σ hσ ψ hψ
  have hfrob : ∀ x, ψ (frobS l a x) = frobS l a (ψ x) := fun x =>
    GlobalTheory.BKGal.PrismTwist.ev_injective a ϖ (by
      rw [hψ, PiSys.ev_frobS, PiSys.ev_frobS, hψ, GlobalTheory.BKGal.PrismTwist.σA_frobenius])
  refine ⟨{ f := ψ
            f_δ := (deltaS l a).map_δ_of_map_φ (deltaS l a)
              (fun x hx => (mul_eq_zero.1 hx).resolve_left (l_ne_zero l a)) ψ hfrob
            f_I := fun (x : (Wq l a)⟦X⟧) hx => ?_
            f_str := fun r (x : (Wq l a)⟦X⟧) h => ?_ }, fun _ => rfl⟩
  · have hx' := Ideal.mem_span_singleton.1 hx
    refine Ideal.mem_span_singleton.2 ((ϖ.theta_ev_eq_zero_iff a (ψ x)).1 ?_)
    rw [hψ, GlobalTheory.RingBasics.θ_σA, (ϖ.theta_ev_eq_zero_iff a x).2 hx', map_zero]
  · apply ϖ.quotToOC_injective a
    change ϖ.quotToOC a (Ideal.Quotient.mk _ (ψ x)) = ϖ.quotToOC a (ϖ.strMap a (σ r))
    have h' : Ideal.Quotient.mk (Ideal.span {eis l a e}) x = ϖ.strMap a r := h
    rw [PiSys.quotToOC_mk, PiSys.quotToOC_strMap, hψ, GlobalTheory.RingBasics.θ_σA, ← PiSys.quotToOC_mk, h',
      PiSys.quotToOC_strMap]
    refine Subtype.ext ?_
    rw [GlobalTheory.RingIface.sigO_coe]
    change Per.σC g (((r : ↥(ϖ.field a).1) : Om l) : ℂ_[l]) = (((σ r : ↥(ϖ.field a).1) : Om l) : ℂ_[l])
    rw [hσ]
    exact GlobalTheory.RingBasics.σC_coe g _
