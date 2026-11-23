import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAttachedHodge
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmEmbeddingProperties
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqIffConjPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalIdeleSndSelf

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.TripleLocal GlobalTheory.TypeLeaf

namespace GlobalTheory.EtaSelfDual

theorem ordF_unif {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) : ordF w (unif w) = 1 := by
  have h := unif_spec w
  have h1 : Valued.v ((atFin w (unif w) : (w.adicCompletion K)ˣ) : w.adicCompletion K) = w.valuation K (unif w : K) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (unif w : K)
  have h0 : w.valuation K (unif w : K) ≠ 0 := (Valuation.ne_zero_iff _).2 (unif w).ne_zero
  unfold IsUnifAt at h
  rw [h1, ← WithZero.exp_log h0, WithZero.exp_inj] at h
  unfold ordF
  omega

theorem ordF_conj {R : Ranks} (H : Formalism.BasicNotions.Host R) {w w' : HeightOneSpectrum (𝓞 H.E)} (h : IsConjPl H w w') (k : H.Eˣ) :
    ordF w' (Units.map (MonoidHomClass.toMonoidHom H.conj) k) = ordF w k := by
  have hc := (GlobalTheory.Mem.Chr.conjPl_main.2.1 R H w w').1 h (k : H.E)
  unfold ordF
  congr 2

theorem val_mul_val {R : Ranks} (H : Formalism.BasicNotions.Host R) (χ : HChar H.E) (hχ : IsEtaT H χ)
    {w w' : HeightOneSpectrum (𝓞 H.E)} (h : IsConjPl H w w') : χ.val w * χ.val w' = 1 := by
  classical
  obtain ⟨c, hc, hcm, ho, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  have hC : GlobalTheory.Mem.Chr.ConjPl H.conj.toRingEquiv w w' := (GlobalTheory.Mem.Chr.conjPl_main.2.1 R H w w').1 h
  have hC' : GlobalTheory.Mem.Chr.ConjPl c.toRingEquiv w w' := fun x => by
    have := hC x
    simpa [hc] using this
  set v := w.under (𝓞 H.F) with hv
  have hmem : ∀ P, P ∈ aboveF (L := H.E) H.F v ↔ P = w ∨ P = w' := by
    intro P
    rw [aboveF, Set.Finite.mem_toFinset, Set.mem_setOf_eq, GlobalTheory.Mem.Chr.under_eq_iff_conjPl c hcm.rank hcm.ne]
    constructor
    · rintro (h1 | h1)
      · exact Or.inl h1
      · exact Or.inr ((GlobalTheory.Mem.Chr.existsUnique_conjPl c.toRingEquiv w).unique h1 hC')
    · rintro (h1 | h1)
      · exact Or.inl h1
      · exact Or.inr (h1 ▸ hC')
  have hab : aboveF (L := H.E) H.F v = insert w {w'} := by
    ext P
    rw [hmem P, Finset.mem_insert, Finset.mem_singleton]
  have hloc : ∀ P ∈ aboveF (L := H.E) H.F v, χ.locK P (upF H.F (unif v)) = χ.val P := fun P hP => by
    have hPv : P.under (𝓞 H.F) = v := by
      rw [aboveF, Set.Finite.mem_toFinset] at hP
      exact hP
    rw [GlobalTheory.HeckeProduct.locK_unr χ (hχ.unr P), ho, hPv, ordF_unif, zpow_one]
  have hwm : w ∈ aboveF (L := H.E) H.F v := (hmem w).2 (Or.inl rfl)
  have hwm' : w' ∈ aboveF (L := H.E) H.F v := (hmem w').2 (Or.inr rfl)
  have hr := hχ.res.1 v (unif v)
  simp only [HChar.resFin, MonoidHom.finset_prod_apply, MonoidHom.comp_apply] at hr
  by_cases hw : w = w'
  · subst hw
    rw [hab, Finset.insert_eq_of_mem (Finset.mem_singleton_self _), Finset.prod_singleton, etaFin, hab,
      Finset.insert_eq_of_mem (Finset.mem_singleton_self _), if_pos (Finset.card_singleton _), ordF_unif, zpow_one, hloc w hwm] at hr
    rw [hr]
    simp
  · rw [hab, Finset.prod_insert (by simpa using hw), Finset.prod_singleton, etaFin, hab,
      if_neg (by rw [Finset.card_insert_of_notMem (by simpa using hw), Finset.card_singleton]; omega),
      hloc w hwm, hloc w' hwm'] at hr
    exact hr

theorem isCSD_of_isEtaT : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (χ : HChar H.E), IsEtaT H χ → IsCSD H χ := by
  intro R H χ hχ
  refine ⟨fun w w' h k => ?_, fun k => ?_⟩
  · rw [GlobalTheory.HeckeProduct.locK_unr χ (hχ.unr w'), GlobalTheory.HeckeProduct.locK_unr χ (hχ.unr w), ordF_conj H h,
      eq_inv_of_mul_eq_one_left (val_mul_val H χ hχ h), inv_zpow, inv_inv]
  · refine eq_inv_of_mul_eq_one_left (Units.ext ?_)
    rw [Units.val_mul, Units.val_one, hχ.inf, hχ.inf, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun g _ => ?_
    have hz : embPsi H g (k : H.E) ≠ 0 := (_root_.map_ne_zero _).2 k.ne_zero
    have e1 : embPsi H g ((Units.map (MonoidHomClass.toMonoidHom H.conj) k : H.Eˣ) : H.E) =
        starRingEnd ℂ (embPsi H g (k : H.E)) := H.conjE_apply _ _
    rw [e1, Complex.norm_conj, zpow_one, zpow_one, div_mul_div_comm, Complex.conj_mul', ← Complex.ofReal_pow,
      ← Complex.ofReal_mul, ← sq, div_self]
    exact Complex.ofReal_ne_zero.2 (pow_ne_zero _ (norm_ne_zero_iff.2 hz))

end GlobalTheory.EtaSelfDual
