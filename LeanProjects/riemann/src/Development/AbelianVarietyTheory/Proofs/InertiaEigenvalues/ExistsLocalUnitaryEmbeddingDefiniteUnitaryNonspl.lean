import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSatAtConstOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivLocProdTriv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivOfISupRange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG

namespace GlobalTheory.UnitaryBC.NonSplit

variable {E : Type} [Field E] [NumberField E]

theorem matrix_ext_pLoc {n : ℕ} {A B : Matrix (Fin n) (Fin n) (Af E)}
    (H : ∀ u : HeightOneSpectrum (𝓞 E), A.map (pLoc E u) = B.map (pLoc E u)) : A = B :=
  Matrix.ext fun i j => FiniteAdeleRing.ext E fun u => congrFun₂ (H u) i j

theorem continuous_finGL' (n : ℕ) : Continuous (finGL E n) :=
  Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map
    (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))))

theorem eq_conjSrc_self (c : E ≃+* E) (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E)
    (hs : ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (c x)) (hv : ∀ x, Valued.v (s x) = Valued.v x) :
    w = conjSrc c w := by
  refine eq_conjSrc fun k => ?_
  have h1 : Valued.v (algebraMap E (w.adicCompletion E) k) = w.valuation E k :=
    w.valuedAdicCompletion_eq_valuation' k
  have h2 : Valued.v (algebraMap E (w.adicCompletion E) (c k)) = w.valuation E (c k) :=
    w.valuedAdicCompletion_eq_valuation' _
  rw [← h1, ← h2, ← hs, hv]

theorem cT_locGL_mul (c : E ≃+* E) {n : ℕ} (w : HeightOneSpectrum (𝓞 E))
    (s : w.adicCompletion E →+* w.adicCompletion E) (hs : ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (c x))
    (hv : ∀ x, Valued.v (s x) = Valued.v x) (g : GL (Fin n) (w.adicCompletion E)) (hg : cT s g.val * g.val = 1) :
    cT (conjFin c) (locGL E n w g).val * (locGL E n w g).val = 1 := by
  refine matrix_ext_pLoc fun u => ?_
  rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  by_cases hu : u = w
  · subst hu
    have e1 : (locGL E n u g).val.map (pLoc E u) = g.val := congrArg Units.val (pLoc_locGL u g)
    have e2 : (cT (conjFin c) (locGL E n u g).val).map (pLoc E u) = cT s g.val := by
      ext1 i j
      change pLoc E u (conjFin c ((locGL E n u g).val j i)) = s (g.val j i)
      rw [← e1]
      exact pLoc_conjFin_eq c u s hs hv _
    rw [e1, e2, hg]
  · have hne : conjSrc c u ≠ w := fun e =>
      hu (conjSrc_injective c (e.trans (eq_conjSrc_self c w s hs hv)))
    have e1 : (locGL E n w g).val.map (pLoc E u) = 1 := congrArg Units.val (pLoc_locGL_of_ne hu g)
    have e3 : (locGL E n w g).val.map (pLoc E (conjSrc c u)) = 1 := congrArg Units.val (pLoc_locGL_of_ne hne g)
    have e2 : (cT (conjFin c) (locGL E n w g).val).map (pLoc E u) = 1 := by
      ext1 i j
      change conjLoc c u (((locGL E n w g).val.map (pLoc E (conjSrc c u))) j i) = _
      rw [e3]
      by_cases hij : i = j
      · subst hij; simp
      · simp [Matrix.one_apply, hij, Ne.symm hij]
    rw [e1, e2, Matrix.mul_one]

variable [IsCMField E]

theorem finGL_locGL_mem_UA {n : ℕ} (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E)
    (hs : ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x))
    (hv : ∀ x, Valued.v (s x) = Valued.v x) (g : GL (Fin n) (w.adicCompletion E)) (hg : cT s g.val * g.val = 1) :
    finGL E n (locGL E n w g) ∈ UA E n := by
  change cT (conjAd E) (finGL E n (locGL E n w g)).val * 1 * (finGL E n (locGL E n w g)).val = 1
  rw [Matrix.mul_one]
  have h1 : (finGL E n (locGL E n w g)).val.map (pInf E) = 1 := congrArg Units.val (pInf_finGL (locGL E n w g))
  have h2 : (finGL E n (locGL E n w g)).val.map (pFin E) = (locGL E n w g).val :=
    congrArg Units.val (pFin_finGL (locGL E n w g))
  have h3 : (cT (conjAd E) (finGL E n (locGL E n w g)).val).map (pInf E) = 1 := by
    ext1 i j
    change (infEq E).symm ((infEq E) (starRingEnd (Cinf E) (pInf E ((finGL E n (locGL E n w g)).val j i)))) = _
    rw [RingEquiv.symm_apply_apply]
    change starRingEnd (Cinf E) (((finGL E n (locGL E n w g)).val.map (pInf E)) j i) = _
    rw [h1]
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply, hij, Ne.symm hij]
  have h4 : (cT (conjAd E) (finGL E n (locGL E n w g)).val).map (pFin E) =
      cT (conjFin (IsCMField.complexConj E).toRingEquiv) (locGL E n w g).val := by
    ext1 i j
    change conjFin _ (((finGL E n (locGL E n w g)).val.map (pFin E)) j i) = _
    rw [h2]
    rfl
  have h5 := cT_locGL_mul (IsCMField.complexConj E).toRingEquiv w s hs hv g hg
  have h6 : (cT (conjAd E) (finGL E n (locGL E n w g)).val * (finGL E n (locGL E n w g)).val).map (pInf E) =
      (1 : Matrix (Fin n) (Fin n) (Ad E)).map (pInf E) := by
    rw [Matrix.map_mul, h3, h1, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
  have h7 : (cT (conjAd E) (finGL E n (locGL E n w g)).val * (finGL E n (locGL E n w g)).val).map (pFin E) =
      (1 : Matrix (Fin n) (Fin n) (Ad E)).map (pFin E) := by
    rw [Matrix.map_mul, h4, h2, h5, Matrix.map_one _ (map_zero _) (map_one _)]
  ext1 i j
  exact ad_ext (congrFun₂ h6 i j) (congrFun₂ h7 i j)

end GlobalTheory.UnitaryBC.NonSplit

open GlobalTheory.UnitaryBC.NonSplit in

theorem GlobalTheory.UnitaryBC.exists_locUnitary_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E),
    (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) →
    (∀ x, Valued.v (s x) = Valued.v x) → ¬ IsSplitAt w →
    ∃ ι : Formalism.UG.UJ s (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) →* UA E n, Continuous ι ∧
      (∀ g, ι g ∈ locU n w ∧ cLoc w (ι g) = g.1) ∧ (∀ x ∈ locU n w, cLoc w x = 1 → x = 1) ∧
      ∀ x g, cLoc w x = 1 → x * ι g = ι g * x := by
  intro E _ _ _ n w s hs hv hns
  have hU : ∀ g : Formalism.UG.UJ s (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)),
      finGL E n (locGL E n w g.1) ∈ UA E n := fun g => by
    refine finGL_locGL_mem_UA w s hs hv g.1 ?_
    have h : cT s g.1.val * 1 * g.1.val = 1 := g.2
    rwa [Matrix.mul_one] at h
  refine ⟨((finGL E n).comp ((locGL E n w).comp (Formalism.UG.UJ s 1).subtype)).codRestrict (UA E n) hU,
    Continuous.subtype_mk (((continuous_finGL' n).comp (CuspSub.continuous_locGL w)).comp continuous_subtype_val) _,
    fun g => ⟨Subgroup.mem_inf.2 ⟨MonoidHom.mem_ker.2 ?_, Subgroup.mem_iInf.2 fun u =>
      Subgroup.mem_iInf.2 fun hu => MonoidHom.mem_ker.2 ?_⟩, ?_⟩, fun x hx h1 => ?_, fun x g h1 => ?_⟩
  · change GeneralLinearGroup.map (pInf E) (finGL E n (locGL E n w g.1)) = 1
    exact pInf_finGL _
  · change GeneralLinearGroup.map (pLoc E u) (GeneralLinearGroup.map (pFin E) (finGL E n (locGL E n w g.1))) = 1
    rw [pFin_finGL]
    exact pLoc_locGL_of_ne (fun e => hu (by rw [e])) _
  · change GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) (finGL E n (locGL E n w g.1))) = g.1
    rw [pFin_finGL, pLoc_locGL]
  · obtain ⟨hxf, hxi⟩ := Subgroup.mem_inf.1 hx
    have hinf : GeneralLinearGroup.map (pInf E) x.1 = 1 := MonoidHom.mem_ker.1 hxf
    have hloc : ∀ u, GeneralLinearGroup.map (pLoc E u) (GeneralLinearGroup.map (pFin E) x.1) = 1 := fun u => by
      by_cases hu : u = w
      · subst hu; exact h1
      · have hu' : u.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E)) :=
          fun e => hns ⟨u, hu, e⟩
        exact MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hxi u) hu')
    refine Subtype.ext (ga_ext (hinf.trans (map_one _).symm) ?_)
    change _ = GeneralLinearGroup.map (pFin E) 1
    rw [map_one]
    exact LocUniq.gl_ext fun u => by rw [hloc u, map_one]
  · have hk : GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) x.1) = 1 := h1
    apply Subtype.ext
    change x.1 * finGL E n (locGL E n w g.1) = finGL E n (locGL E n w g.1) * x.1
    obtain ⟨y, k, hx, hk'⟩ : ∃ y k, x.1 = infGL E n y * finGL E n k ∧ GeneralLinearGroup.map (pLoc E w) k = 1 :=
      ⟨_, _, (infGL_mul_finGL x.1).symm, hk⟩
    rw [hx, mul_assoc, ← map_mul, LocUniq.comm_locGL w hk' g.1, map_mul, ← mul_assoc, infGL_comm, mul_assoc]

end
