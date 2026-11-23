import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CentralEig2
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

namespace UpperTheory.Gal.CertificateRingHomMap

private theorem rat_eq_one_of_ZU (s : ℚˣ) (hpos : 0 < (s : ℚ))
    (h : Units.map (algebraMap ℚ AfQ).toMonoidHom s ∈ ZU) : s = 1 := by
  have hv : ∀ v : Plc ℚ, HeightOneSpectrum.valuation ℚ v (s : ℚ) = 1 := fun v => by
    have h1 : Valued.v ((algebraMap ℚ AfQ (s : ℚ)) v) = 1 := h v
    rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h1
    exact h1
  have hi : ∀ x : ℚ, (∀ v : Plc ℚ, HeightOneSpectrum.valuation ℚ v x ≤ 1) → ∃ m : ℤ, (m : ℚ) = x := fun x hx => by
    obtain ⟨a, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one ℚ x hx
    have h2 : IsIntegral ℤ (algebraMap (𝓞 ℚ) ℚ a) := a.2
    obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
    exact ⟨m, by simpa using hm⟩
  obtain ⟨m, hm⟩ := hi s (fun v => (hv v).le)
  obtain ⟨m', hm'⟩ := hi (s : ℚ)⁻¹ (fun v => by rw [map_inv₀, hv v, inv_one])
  have hmm : m * m' = 1 := by
    have h3 : (m : ℚ) * m' = 1 := by rw [hm, hm']; exact mul_inv_cancel₀ s.ne_zero
    exact_mod_cast h3
  have hm1 : m = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hmm with h4 | h4
    · exact h4
    · subst h4
      rw [← hm] at hpos
      norm_num at hpos
  ext
  rw [← hm, hm1]
  simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem coord_emb (v : InfinitePlace E) (x : E) :
    coord v.embedding (pInf E (algebraMap E (Ad E) x)) = v.embedding x := by
  have h : ∀ w : InfinitePlace E, pInf E (algebraMap E (Ad E) x) w = w.embedding x := fun w => pInf_algebraMap _ _
  unfold coord
  simp [h]

private theorem val_rat (W : Wt E n) (j : ℤ) (f : algForms W) (γ : Gam0 E n) (h1 : γ.1.2 = 1) :
    ∃ a : finU E n, ofU a = rat γ ∧
      ∀ u : finU E n, algForms.val f (a.1 * u.1) = xi0 W j γ (algForms.val f u.1) := by
  have hy : (γ.1.1.val.map (GlobalTheory.SplitPts.conjE E).toRingHom)ᵀ * γ.1.1.val = 1 := by
    have h : (γ.1.1.val.map (GlobalTheory.SplitPts.conjE E).toRingHom)ᵀ * γ.1.1.val =
      algebraMap ℚ E γ.1.2 • (1 : Matrix (Fin n) (Fin n) E) := γ.2.1
    rw [h, h1]
    simp
  have hY : ratGL E n γ.1.1 ∈ UA E n := by
    change Formalism.UG.cT (conjAd E) (γ.1.1.val.map (algebraMap E (Ad E))) * 1 * γ.1.1.val.map (algebraMap E (Ad E)) = 1
    rw [GlobalTheory.DefU.ClassFin.cT_map (algebraMap E (Ad E)) (IsCMField.complexConj E).toRingEquiv.toRingHom (conjAd E)
      (fun y => (conjAd_algebraMap y).symm), mul_one, ← Matrix.map_mul]
    have h2 : Formalism.UG.cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ.1.1.val * γ.1.1.val = 1 := hy
    rw [h2]
    simp
  let Y : UA E n := ⟨ratGL E n γ.1.1, hY⟩
  have hYr : Y ∈ ratU E n := Subgroup.mem_subgroupOf.2 ⟨γ.1.1, rfl⟩
  let a := GlobalTheory.UnitarySplit.finPart Y
  let b := GlobalTheory.UnitarySplit.infPart Y
  have hab : Y = a.1 * b.1 := GlobalTheory.UnitarySplit.finPart_mul_infPart Y
  refine ⟨a, ?_, fun u => ?_⟩
  · refine Subtype.ext (Prod.ext ?_ ?_)
    · exact pFin_finGL _
    · show (1 : AfQˣ) = Units.map (algebraMap ℚ AfQ).toMonoidHom γ.1.2
      rw [h1, map_one]
  · have e : a.1 * u.1 = Y * (u.1 * ((b⁻¹ : infU E n) : UA E n)) := by
      have hc := GlobalTheory.DefU.fin_mul_inf u.2 b.2
      rw [hab, Subgroup.coe_inv, mul_assoc, ← mul_assoc b.1, ← hc, mul_assoc u.1, mul_inv_cancel, mul_one]
    have hc : cAll b.1 = embAll E n γ.1.1 := by
      funext v
      show cEmb v.embedding b.1 = GeneralLinearGroup.map v.embedding γ.1.1
      refine Units.ext (Matrix.ext fun i k => ?_)
      have h3 : (cEmb v.embedding b.1).val i k = coord v.embedding ((cInf b.1).val i k) := rfl
      rw [h3, GlobalTheory.UnitarySplit.cInf_infPart]
      exact coord_emb v _
    rw [e, algForms.val_left f hYr, algForms.val_right, inv_inv]
    have h4 : xi0 W j γ = Representation.dual
        ((Formalism.L2.DIV.rhoK (K := ℂ) (ι := InfinitePlace E) W).comp (embAll E n)) γ.1.1 := by
      have h6 : xi0 W j γ = (((γ.1.2 : ℚ) : ℂ) ^ j) • Representation.dual
          ((Formalism.L2.DIV.rhoK (K := ℂ) (ι := InfinitePlace E) W).comp (embAll E n)) γ.1.1 := rfl
      rw [h6, h1]
      simp
    rw [h4, Representation.dual_apply, Representation.dual_apply]
    have h5 : W.rep b⁻¹ = ((Formalism.L2.DIV.rhoK (K := ℂ) (ι := InfinitePlace E) W).comp (embAll E n)) γ.1.1⁻¹ := by
      have h7 : cAll (b⁻¹ : infU E n).1 = embAll E n γ.1.1⁻¹ := by
        rw [Subgroup.coe_inv, map_inv, hc, map_inv]
      show Formalism.L2.DIV.rhoK (K := ℂ) (ι := InfinitePlace E) W (cAll (b⁻¹ : infU E n).1) =
        Formalism.L2.DIV.rhoK (K := ℂ) (ι := InfinitePlace E) W (embAll E n γ.1.1⁻¹)
      rw [h7]
    rw [h5]

theorem pKerFormU_of :
    UpperTheory.Gal.CertificateRingHomMap.OfUBij → UpperTheory.Gal.CertificateRingHomMap.KerFormU := by
  intro hB E _ _ _ n W j f hf K hK hfix
  obtain ⟨hinj, hsurj⟩ := hB E n
  let φ : GUf E n → Module.Dual ℂ W.Sp := fun g => if h : ∃ u, ofU u = g then algForms.val f h.choose.1 else 0
  have hφ : ∀ u : finU E n, φ (ofU u) = algForms.val f u.1 := fun u => by
    have h : ∃ u', ofU u' = ofU u := ⟨u, rfl⟩
    show (if h : ∃ u', ofU u' = ofU u then algForms.val f h.choose.1 else 0) = _
    rw [dif_pos h, hinj h.choose_spec]
  have hone : ∀ γ : Gam0 E n, sim (rat γ) ∈ ZU → γ.1.2 = 1 := fun γ h => rat_eq_one_of_ZU γ.1.2 γ.2.2 h
  refine ⟨φ, ⟨?_, ?_, ?_⟩, hφ, ?_⟩
  · intro γ k hk he
    have h1 := hone γ (he ▸ hK k hk)
    rw [← he]
    show Units.map (algebraMap ℚ AfQ).toMonoidHom γ.1.2 = 1
    rw [h1, map_one]
  · intro γ u hγ hu
    obtain ⟨u₀, rfl⟩ := hsurj u hu
    obtain ⟨a, ha, hau⟩ := val_rat W j f γ (hone γ (hγ ▸ ZU.one_mem))
    rw [← ha, ← map_mul, hφ, hφ]
    exact hau u₀
  · intro k hk u hk1 hu
    obtain ⟨u₀, rfl⟩ := hsurj u hu
    obtain ⟨u', rfl⟩ := hsurj k hk1
    rw [← map_mul, hφ, hφ]
    show algForms.val f (u₀.1 * u'.1) = _
    rw [← algForms.val_algRep, hfix u' hk]
  · have hex : ∃ g, algForms.val f g ≠ 0 := by
      by_contra hc
      push_neg at hc
      refine hf (Subtype.ext (LinearMap.ext fun v => funext fun g => ?_))
      exact LinearMap.congr_fun (hc g) v
    obtain ⟨g, hg⟩ := hex
    refine ⟨ofU (GlobalTheory.UnitarySplit.finPart g), sim_ofU _, ?_⟩
    rw [hφ]
    intro h0
    apply hg
    have h1 := algForms.val_right f (GlobalTheory.UnitarySplit.finPart g).1 (GlobalTheory.UnitarySplit.infPart g)
    rw [← GlobalTheory.UnitarySplit.finPart_mul_infPart g] at h1
    rw [h1, h0, map_zero]

end UpperTheory.Gal.CertificateRingHomMap
