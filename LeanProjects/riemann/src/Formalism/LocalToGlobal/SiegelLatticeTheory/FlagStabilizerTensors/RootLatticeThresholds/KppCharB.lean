import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppCharA
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PsiCondAll

noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.KppChar

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.RowDictPf Formalism.L2.SG.Pf.AllRowsRedKerA
  Formalism.L2.SG.Pf.AllRowsRedKer Formalism.L2.SG.Pf.KppRedW Formalism.L2.SG.Pf.RedBasicsPf

variable {D : D7} (X : HidaSetting D)

theorem g_pos : 0 < X.B.g := by
  rw [X.g_eq]; exact Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos

theorem divN_add (a b : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) :
    divN X.B.I X.B.g (a + b) = divN X.B.I X.B.g a + divN X.B.I X.B.g b := by
  unfold divN; ring

theorem divN_g (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) :
    divN X.B.I X.B.g ((X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * c) = c := by
  unfold divN
  have hg : ((X.B.g : ℕ) : X.B.I.F) ≠ 0 := Nat.cast_ne_zero.2 (g_pos X).ne'
  rw [← mul_assoc, ← map_natCast (algebraMap X.B.I.F (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)), ← map_mul,
    inv_mul_cancel₀ hg, map_one, one_mul]

theorem psi_modg (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) {d : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hd : d ∈ IntAf X.B.I.F X.B.I.E) :
    X.psiEf (divN X.B.I X.B.g (c + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * d)) = X.psiEf (divN X.B.I X.B.g c) := by
  rw [divN_add, X.psiEf_add, divN_g, X.psiEf_int d hd, mul_one]

theorem divN_incl (y : X.B.I.E) : divN X.B.I X.B.g (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) y) =
    Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (((X.B.g : ℕ) : X.B.I.E)⁻¹ * y) := by
  unfold divN
  rw [Algebra.TensorProduct.algebraMap_apply, map_mul]
  congr 1
  show algebraMap X.B.I.F X.B.I.E ((X.B.g : X.B.I.F)⁻¹) ⊗ₜ[X.B.I.F] (1 : Af X.B.I.F) =
    Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (((X.B.g : ℕ) : X.B.I.E)⁻¹)
  rw [map_inv₀, map_natCast]
  rfl

theorem psiEinf_star (y : X.B.I.E) : psiEinf X.B.I (star y) = psiEinf X.B.I y := by
  unfold psiEinf
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [X.B.I.cm.cmUnram.2.1 (X.B.I.φ v) y]
  congr 2
  simp only [starRingEnd_apply, star_star]
  ring

theorem psi_incl_star (y : X.B.I.E) :
    X.psiEf (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (star y)) =
      X.psiEf (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) y) := by
  have h1 := X.psiEf_rat (star y)
  have h2 := X.psiEf_rat y
  rw [psiEinf_star] at h1
  have hne : psiEinf X.B.I y ≠ 0 := by intro h; rw [h, mul_zero] at h2; exact zero_ne_one h2
  exact mul_right_cancel₀ hne (h1.trans h2.symm)

theorem psi_sig (ε : 𝓞 X.B.I.E) (m : ℕ) :
    X.psiEf (divN X.B.I X.B.g (iE X.B.I (sigO X.B.I ε) * (m : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))) =
      X.psiEf (divN X.B.I X.B.g (iE X.B.I ε * (m : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))) := by
  have e : ∀ a : 𝓞 X.B.I.E, iE X.B.I a * (m : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) =
      Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) ((a : X.B.I.E) * m) := by
    intro a; rw [map_mul, map_natCast]
  rw [e, e, divN_incl, divN_incl, sigO_coe]
  have : ((X.B.g : ℕ) : X.B.I.E)⁻¹ * (star (ε : X.B.I.E) * m) = star (((X.B.g : ℕ) : X.B.I.E)⁻¹ * ((ε : X.B.I.E) * m)) := by
    rw [star_mul, star_mul, star_inv₀, star_natCast, star_natCast]; ring
  rw [this, psi_incl_star]

variable {kv : Σ k : Fin 2, D.nd.PlG k}

theorem g_split_mul {k k' : Fin 2} (hk : k' ≠ k) :
    ((D.host.g k : ℕ) : 𝓞 X.B.I.E) * ((D.host.g k' : ℕ) : 𝓞 X.B.I.E) = ((X.B.g : ℕ) : 𝓞 X.B.I.E) := by
  rw [g_eq_cast]
  fin_cases k <;> fin_cases k'
  · exact absurd rfl hk
  · rfl
  · exact mul_comm _ _
  · exact absurd rfl hk

theorem other_ne (k : Fin 2) : (1 - k) ≠ k := by fin_cases k <;> decide

theorem psi_period {ε : 𝓞 X.B.I.E} (hε : ε ∈ Ideal.span {((D.host.g (1 - kv.1) : ℕ) : 𝓞 X.B.I.E)}) (m q : ℕ) :
    X.psiEf (divN X.B.I X.B.g (iE X.B.I ε * ((m + D.host.g kv.1 * q : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))) =
      X.psiEf (divN X.B.I X.B.g (iE X.B.I ε * (m : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))) := by
  obtain ⟨δ, hδ⟩ := Ideal.mem_span_singleton'.1 hε
  have e : iE X.B.I ε * ((m + D.host.g kv.1 * q : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) =
      iE X.B.I ε * (m : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (iE X.B.I δ * q) := by
    have hg : ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) =
        iE X.B.I (((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.E) * ((D.host.g (1 - kv.1) : ℕ) : 𝓞 X.B.I.E)) := by
      rw [g_split_mul X (other_ne kv.1)]; simp [iE]
    rw [hg, ← hδ]
    simp only [iE, map_mul, map_natCast, Nat.cast_add, Nat.cast_mul]
    ring
  rw [e, psi_modg X _ (mul_mem (iE_int X.B.I δ) (natCast_mem _ q))]

def psiK (ε : 𝓞 X.B.I.E) (hε : ε ∈ Ideal.span {((D.host.g (1 - kv.1) : ℕ) : 𝓞 X.B.I.E)}) :
    AddChar (ZMod (D.host.g kv.1)) ℂ where
  toFun t := X.psiEf (divN X.B.I X.B.g (iE X.B.I ε * ((t.val : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)))
  map_zero_eq_one' := by
    simp only [ZMod.val_zero, Nat.cast_zero, mul_zero]
    unfold divN; rw [mul_zero]; exact X.psiEf_int 0 (zero_mem _)
  map_add_eq_mul' a b := by
    have : NeZero (D.host.g kv.1) := ⟨(D.host.g_prime kv.1).ne_zero⟩
    have hval : a.val + b.val = (a + b).val + D.host.g kv.1 * ((a.val + b.val) / D.host.g kv.1) := by
      rw [ZMod.val_add]; exact (Nat.mod_add_div _ _).symm
    rw [← psi_period X hε (a + b).val ((a.val + b.val) / D.host.g kv.1), ← hval, Nat.cast_add, mul_add, divN_add,
      X.psiEf_add]

theorem psiK_apply (ε : 𝓞 X.B.I.E) (hε : ε ∈ Ideal.span {((D.host.g (1 - kv.1) : ℕ) : 𝓞 X.B.I.E)})
    (t : ZMod (D.host.g kv.1)) :
    psiK X ε hε t = X.psiEf (divN X.B.I X.B.g (iE X.B.I ε * ((t.val : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))) := rfl

end Formalism.L2.SG.Pf.KppChar
