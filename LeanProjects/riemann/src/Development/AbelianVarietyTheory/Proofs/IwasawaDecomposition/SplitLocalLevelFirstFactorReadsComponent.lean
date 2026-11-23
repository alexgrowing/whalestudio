import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiamondElementIntegralSupportLastRow
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdFirst

theorem qPi_eq_phi_of_adAt : ∀ {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {Q : Finset (Pl E)} {Θ : LevQFam E K n Q} (q : QLoc hc n Q Θ) (P : Q), conjPrime₂ P.1 ≠ P.1 → ∀ (a : AfE F E) (e : E), adAt F P.1 a = algebraMap E _ e → qPi q P a = q.phi P e := by
  intro F E K _ _ _ _ _ _ _ hc n _ Q Θ q P hP a e he
  have hw : P.1.under (𝓞 F) = qv F P.1 := HeightOneSpectrum.ext rfl
  set ψ := GlobalTheory.Mem.Dil.psi (qv F P.1) P.1 hw with hψ
  set sp := q.sp P with hsp

  have hu' : ψ (sp.symm (0, 1)) = 0 := by
    obtain ⟨r, hr, hr'⟩ := exists_mem_notMem (Ne.symm hP)
    have hcr : cO E r ∉ P.1.asIdeal := fun h => hr' ((mem_conjP _ _).2 h)
    obtain ⟨hne, hinv⟩ := qdf_phi_unit q P hcr
    set w := Formalism.UG.inclE (F := F) ((qv F P.1).adicCompletion F) (r : E) with hwdef
    have hws : w = Formalism.UG.sigR hc.sig _ (Formalism.UG.inclE (F := F) ((qv F P.1).adicCompletion F) ((cO E r : 𝓞 E) : E)) := by
      rw [hwdef]
      show _ = Formalism.UG.inclE (F := F) _ (star (star ((r : 𝓞 E) : E)))
      rw [star_star]
    have hw2 : (sp w).2 = q.phi P ((cO E r : 𝓞 E) : E) := by
      rw [hws, hsp, q.sp_sig]
      rfl
    set z := sp.symm (0, ((sp w).2)⁻¹) with hz
    have hzint : z ∈ Formalism.BasicNotions.intV E (qv F P.1) := by
      refine (q.sp_int P z).2 ⟨?_, ?_⟩
      · rw [hz, ← hsp, sp.apply_symm_apply]; exact zero_mem _
      · rw [hz, ← hsp, sp.apply_symm_apply]; show ((sp w).2)⁻¹ ∈ _; rw [hw2]; exact hinv
    have hwz : w * z = sp.symm (0, 1) := by
      apply sp.injective
      rw [map_mul, hz, sp.apply_symm_apply, sp.apply_symm_apply]
      refine Prod.ext (mul_zero _) ?_
      show (sp w).2 * ((sp w).2)⁻¹ = 1
      rw [hw2]
      exact mul_inv_cancel₀ hne
    have hidem : ψ (sp.symm (0, 1)) * ψ (sp.symm (0, 1)) = ψ (sp.symm (0, 1)) := by
      rw [← map_mul, ← map_mul sp.symm]
      simp
    rcases mul_eq_zero.1 (show ψ (sp.symm (0, 1)) * (ψ (sp.symm (0, 1)) - 1) = 0 by rw [mul_sub, hidem, mul_one, sub_self]) with h | h
    · exact h
    · exfalso
      have h1 : ψ (sp.symm (0, 1)) = 1 := sub_eq_zero.1 h
      rw [← hwz, map_mul] at h1
      have hv1 : Valued.v (ψ w) < 1 := by
        rw [hψ, hwdef, GlobalTheory.Mem.Dil.psi_inclE]
        exact GlobalTheory.Mem.Dil.val_lt_one hr
      have hv2 : Valued.v (ψ z) ≤ 1 := (GlobalTheory.Mem.Dil.mem_intV_iff (qv F P.1) z).1 hzint P.1 hw
      have h3 := congrArg Valued.v h1
      rw [map_mul, map_one] at h3
      exact absurd h3 (ne_of_lt (lt_of_le_of_lt (mul_le_of_le_one_right' hv2) hv1))
  have hu : ψ (sp.symm (1, 0)) = 1 := by
    have e1 : sp.symm (1, 0) + sp.symm (0, 1) = 1 := by
      rw [← map_add]; simp
    have e2 := congrArg ψ e1
    rw [map_add, hu', add_zero, map_one] at e2
    exact e2

  set x := prV (E := E) (qv F P.1) a - Formalism.UG.inclE (F := F) ((qv F P.1).adicCompletion F) e with hx
  have hψx : ψ x = 0 := by
    rw [hx, map_sub, hψ, GlobalTheory.Mem.Dil.psi_prV, GlobalTheory.Mem.Dil.psi_inclE, he, sub_self]
  have hx1 : (sp x).1 = 0 := by
    by_contra ht
    have hxy : x * sp.symm (((sp x).1)⁻¹, 0) = sp.symm (1, 0) := by
      apply sp.injective
      rw [map_mul, sp.apply_symm_apply, sp.apply_symm_apply]
      exact Prod.ext (mul_inv_cancel₀ ht) (mul_zero _)
    have h2 := congrArg ψ hxy
    rw [map_mul, hψx, zero_mul, hu] at h2
    exact zero_ne_one h2
  have e3 : qPi q P a - q.phi P e = (sp x).1 := by
    rw [hx, map_sub]
    rfl
  exact sub_eq_zero.1 (e3.trans hx1)

end GlobalTheory.Mem.Col2.AdFirst
