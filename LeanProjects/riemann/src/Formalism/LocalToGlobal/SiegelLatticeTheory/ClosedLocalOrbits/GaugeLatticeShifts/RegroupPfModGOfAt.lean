import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfTermCar

noncomputable section

open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf.RegroupPf

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem reduction_mod_g_holds : ModGOfAtC := by
  intro D X g1 Λ hΛ v hv
  obtain ⟨c, hcop, hcv⟩ := hv
  have hg0 : X.B.g ≠ 0 := by
    rw [X.g_eq]; exact Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  have hgE : (X.B.g : X.B.I.E) ≠ 0 := Nat.cast_ne_zero.mpr hg0
  set q : X.B.I.E := ((X.B.g : X.B.I.E))⁻¹ with hqdef
  set ι : X.B.I.E →+* X.B.I.E ⊗[X.B.I.F] Af X.B.I.F := Formalism.UG.inclE (F := X.B.I.F) (E := X.B.I.E) (Af X.B.I.F) with hι
  have hq : ι q * (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) = 1 := by
    rw [← map_natCast ι, ← map_mul, hqdef, inv_mul_cancel₀ hgE, map_one]
  have key : ∀ z ∈ mL X.B.I X.B.g, ι q • z ∈ X.B.I.Lf := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      rw [smul_smul, hq, one_smul]; exact hx
    | zero => rw [smul_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
    | smul t a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ t ha
  set w : (VS D).V := (X.ιE (q * c)) • v with hwdef
  have hwΛ : w ∈ Λ := by
    rw [hΛ, hwdef, Formalism.L2.SG.NormCut.crd_smul' X, Formalism.L2.SG.NormCut.incl_smul' X, mulVec_smul,
      RingEquiv.symm_apply_apply, map_mul, map_natCast, mul_smul]
    exact key _ hcv
  intro P hgP
  have hcP : ((c : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro hc
    have h1 : IsCoprime ((c : ℤ)) ((X.B.g : ℤ)) := Nat.isCoprime_iff_coprime.mpr hcop
    obtain ⟨a, b, hab⟩ := h1.map (Int.castRingHom (𝓞 D.host.E))
    have hg' : (((X.B.g : ℕ) : ℤ) : 𝓞 D.host.E) ∈ P.asIdeal := by
      rw [Int.cast_natCast, X.g_eq]; exact hgP
    have hc' : (((c : ℕ) : ℤ) : 𝓞 D.host.E) ∈ P.asIdeal := by rw [Int.cast_natCast]; exact hc
    have h1P : (1 : 𝓞 D.host.E) ∈ P.asIdeal := by
      rw [← hab]
      exact P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ hc') (P.asIdeal.mul_mem_left _ hg')
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1P)
  have hcv' : ((c : ℕ) : 𝓞 D.host.E) • v = ((gS D : ℕ) : 𝓞 D.host.E) • w := by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, hwdef, ← Nat.cast_smul_eq_nsmul D.host.E,
      ← Nat.cast_smul_eq_nsmul D.host.E, smul_smul]
    congr 1
    rw [← map_natCast X.ιE (gS D), ← map_mul, ← mul_assoc, hqdef, show gS D = X.B.g from X.g_eq.symm,
      mul_inv_cancel₀ hgE, one_mul, map_natCast]
  exact ⟨_, hcP, by rw [hcv']; exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hwΛ⟩

end Formalism.L2.SG.Pf.RegroupPf
