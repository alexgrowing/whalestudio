import Mathlib
import GroundTheory.PAdicHodge.FWCyclotomicNorm
import GroundTheory.PAdicHodge.FontaineWintenberger
import GroundTheory.PAdicHodge.PerfectoidCriterion
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

variable (p : ℕ) [Fact p.Prime]

def cyclInf : IntermediateField ℚ_[p] (PadicAlgCl p) := ⨆ n, cycl p n

theorem mem_cyclInf_iff {x : PadicAlgCl p} : x ∈ cyclInf p ↔ ∃ n, x ∈ cycl p n := by
  have hdir : Directed (· ≤ ·) (cycl p) := (cycl_mono (p := p)).directed_le
  rw [← SetLike.mem_coe, cyclInf, IntermediateField.coe_iSup_of_directed hdir, Set.mem_iUnion]
  rfl

def cyclComplete : Subfield ℂ_[p] :=
  ((cyclInf p).toSubfield.map (algebraMap (PadicAlgCl p) ℂ_[p])).topologicalClosure

theorem coe_mem_cyclComplete {n : ℕ} {x : PadicAlgCl p} (hx : x ∈ cycl p n) :
    (x : ℂ_[p]) ∈ cyclComplete p :=
  Subfield.le_topologicalClosure _ ⟨x, (mem_cyclInf_iff p).2 ⟨n, hx⟩, rfl⟩

theorem isClosed_cyclComplete : IsClosed (cyclComplete p : Set ℂ_[p]) :=
  Subfield.isClosed_topologicalClosure _

instance : CompleteSpace (cyclComplete p) := (isClosed_cyclComplete p).completeSpace_coe

theorem norm_natCast_cyclComplete : ‖(p : cyclComplete p)‖ = (p : ℝ)⁻¹ := by
  change ‖((p : cyclComplete p) : ℂ_[p])‖ = _
  rw [show ((p : cyclComplete p) : ℂ_[p]) = ((p : PadicAlgCl p) : ℂ_[p]) by simp,
    PadicComplex.norm_extends, norm_natCast_prime]

instance : NontriviallyNormedField (cyclComplete p) where
  non_trivial := ⟨(p : cyclComplete p)⁻¹, by
    rw [norm_inv, norm_natCast_cyclComplete, inv_inv]; exact one_lt_p_real⟩

instance isPerfectoidField_cyclComplete : IsPerfectoidField (cyclComplete p) p where
  complete := inferInstance
  norm_natCast_lt_one := by
    rw [norm_natCast_cyclComplete]; exact inv_lt_one_of_one_lt₀ one_lt_p_real
  exists_norm_mem_Ioo r hr := by
    obtain ⟨n, x, hx, h1, h2⟩ := exists_mem_cycl_norm_mem_Ioo (p := p) hr
    have hn : ‖(⟨(x : ℂ_[p]), coe_mem_cyclComplete p hx⟩ : cyclComplete p)‖ = ‖x‖ :=
      PadicComplex.norm_extends p x
    exact ⟨⟨x, coe_mem_cyclComplete p hx⟩, hn ▸ h1, hn ▸ h2⟩
  surjective_pow := by
    refine IsPerfectoidField.surjective_pow_of_norm p fun x hx1 => ?_
    have hx1' : ‖(x : ℂ_[p])‖ ≤ 1 := hx1
    have hpinv : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast (Fact.out : p.Prime).pos)
    obtain ⟨b, ⟨u, hu, rfl⟩, hb⟩ := Metric.mem_closure_iff.1 x.2 _ hpinv
    obtain ⟨n, hun⟩ := (mem_cyclInf_iff p).1 hu
    have hdist : ‖(x : ℂ_[p]) - algebraMap (PadicAlgCl p) ℂ_[p] u‖ < (p : ℝ)⁻¹ := by
      rw [← dist_eq_norm]; exact hb
    have hu1 : ‖u‖ ≤ 1 := by
      rw [← PadicComplex.norm_extends p u]
      have h := IsUltrametricDist.norm_add_le_max (x : ℂ_[p])
        (algebraMap (PadicAlgCl p) ℂ_[p] u - x)
      rw [add_sub_cancel] at h
      refine h.trans (max_le hx1' ?_)
      rw [norm_sub_rev]
      exact hdist.le.trans (inv_lt_one_of_one_lt₀ one_lt_p_real).le
    obtain ⟨v, hv, hv1, hvu⟩ := exists_pow_approx_cycl hun hu1
    refine ⟨⟨(v : ℂ_[p]), coe_mem_cyclComplete p hv⟩, ?_, ?_⟩
    · exact (PadicComplex.norm_extends p v).trans_le hv1
    · rw [norm_natCast_cyclComplete]
      change ‖(x : ℂ_[p]) - algebraMap (PadicAlgCl p) ℂ_[p] v ^ p‖ ≤ _
      have hsplit : (x : ℂ_[p]) - algebraMap (PadicAlgCl p) ℂ_[p] v ^ p =
          ((x : ℂ_[p]) - algebraMap (PadicAlgCl p) ℂ_[p] u) +
            algebraMap (PadicAlgCl p) ℂ_[p] (u - v ^ p) := by
        rw [map_sub, map_pow]; ring
      rw [hsplit]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hdist.le ?_)
      rw [← PadicComplex.coe_eq, PadicComplex.norm_extends, ← norm_natCast_prime]
      exact hvu

instance : CharZero (cyclComplete p) :=
  (RingHom.charZero_iff (cyclComplete p).subtype.injective).2 inferInstance

instance : NormedAlgebra (cyclComplete p) ℂ_[p] where
  norm_smul_le k x := by rw [Algebra.smul_def, norm_mul]; rfl

local notation "K∞" => cyclComplete p
local notation "K∞♭" => Tilt (cyclComplete p) NormedField.valuation (normInteger (cyclComplete p))
  normInteger_integers p

def absoluteGaloisGroupCyclTiltEquiv : Field.absoluteGaloisGroup K∞ ≃ₜ* Field.absoluteGaloisGroup K∞♭ :=
  absoluteGaloisGroupTiltEquiv K∞ p

def cyclGaloisTiltEquiv :
    (algebraicClosure K∞ ℂ_[p] ≃ₐ[K∞] algebraicClosure K∞ ℂ_[p]) ≃ₜ*
      (algebraicClosure K∞♭ (Tilt ℂ_[p] NormedField.valuation (normInteger ℂ_[p]) normInteger_integers p) ≃ₐ[K∞♭]
        algebraicClosure K∞♭ (Tilt ℂ_[p] NormedField.valuation (normInteger ℂ_[p]) normInteger_integers p)) :=
  galoisTiltEquiv K∞ ℂ_[p] p

theorem cyclGaloisTiltEquiv_fixes_iff (L : IntermediateField K∞ ℂ_[p]) [FiniteDimensional K∞ L]
    (σ : algebraicClosure K∞ ℂ_[p] ≃ₐ[K∞] algebraicClosure K∞ ℂ_[p]) :
    (∀ y : algebraicClosure K∞♭ (Tilt ℂ_[p] NormedField.valuation (normInteger ℂ_[p])
        normInteger_integers p),
        (y : Tilt ℂ_[p] NormedField.valuation (normInteger ℂ_[p]) normInteger_integers p) ∈
          tiltIntermediateField p L → cyclGaloisTiltEquiv p σ y = y) ↔
      (∀ x : algebraicClosure K∞ ℂ_[p], (x : ℂ_[p]) ∈ L → σ x = x) :=
  galoisTiltEquiv_fixes_iff L σ

end GroundTheory.PAdicHodge
