import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU GlobalTheory.Mem.Chr

namespace GlobalTheory.DefU.Inert

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem conjPl_self (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E)
    (hs : ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x))
    (hv : ∀ x, Valued.v (s x) = Valued.v x) : ConjPl (IsCMField.complexConj E).toRingEquiv w w := fun k => by
  have h1 : Valued.v (algebraMap E (w.adicCompletion E) k) = w.valuation E k :=
    w.valuedAdicCompletion_eq_valuation' k
  have h2 : Valued.v (algebraMap E (w.adicCompletion E) (IsCMField.complexConj E k)) =
      w.valuation E (IsCMField.complexConj E k) := w.valuedAdicCompletion_eq_valuation' _
  have h3 := hv (algebraMap E (w.adicCompletion E) k)
  rw [hs, h1, h2] at h3
  exact h3

theorem eq_of_under_eq {w u : HeightOneSpectrum (𝓞 E)} (hw : ConjPl (IsCMField.complexConj E).toRingEquiv w w)
    (hu : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))) : u = w := by
  rcases (under_eq_iff_conjPl (IsCMField.complexConj E) (Algebra.IsQuadraticExtension.finrank_eq_two _ _)
    (IsCMField.complexConj_ne_one E) w u).1 hu with h | h
  · exact h
  · exact (existsUnique_conjPl _ w).unique h hw

theorem continuous_finGL : Continuous (finGL E n) :=
  Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map
    (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))))

theorem continuous_cLoc (w : HeightOneSpectrum (𝓞 E)) : Continuous (cLoc (n := n) w) :=
  (Continuous.units_map _ (continuous_id.matrix_map
    ((RestrictedProduct.continuous_eval w).comp continuous_snd))).comp continuous_subtype_val

theorem mat_ext {A B : Matrix (Fin n) (Fin n) (Ad E)} (h1 : A.map (pInf E) = B.map (pInf E))
    (h2 : ∀ v, A.map ((pLoc E v).comp (pFin E)) = B.map ((pLoc E v).comp (pFin E))) : A = B := by
  ext i j
  refine ad_ext (congrFun (congrFun h1 i) j) (FiniteAdeleRing.ext _ fun v => ?_)
  exact congrFun (congrFun (h2 v) i) j

theorem map_finGL (v : HeightOneSpectrum (𝓞 E)) (k : GL (Fin n) (Af E)) :
    GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (finGL E n k) = GeneralLinearGroup.map (pLoc E v) k :=
  Units.ext (congrArg (fun g : GL (Fin n) (v.adicCompletion E) => (g : Matrix (Fin n) (Fin n) (v.adicCompletion E)))
    (congrArg (GeneralLinearGroup.map (pLoc E v)) (pFin_finGL k)))

theorem pInf_conjAd (x : Ad E) : pInf E (conjAd E x) = star (pInf E x) :=
  (infEq E).symm_apply_apply _

theorem finGL_mem (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E)
    (hs : ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x))
    (hv : ∀ x, Valued.v (s x) = Valued.v x) (g : GL (Fin n) (w.adicCompletion E))
    (hg : g ∈ UJ s (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E))) :
    finGL E n (locGL E n w g) ∈ UA E n := by
  have hg' : cT s g.val * g.val = 1 := by
    have h : cT s g.val * 1 * g.val = 1 := hg
    rwa [Matrix.mul_one] at h
  have hw := conjPl_self w s hs hv
  change cT (conjAd E) (finGL E n (locGL E n w g)).val * 1 * (finGL E n (locGL E n w g)).val = 1
  rw [Matrix.mul_one]
  generalize hh : finGL E n (locGL E n w g) = h
  have hI : h.val.map (pInf E) = 1 := by
    rw [← hh]
    exact congrArg Units.val (pInf_finGL (locGL E n w g))
  have hL : ∀ v, h.val.map ((pLoc E v).comp (pFin E)) =
      (GeneralLinearGroup.map (pLoc E v) (locGL E n w g)).val := fun v => by
    rw [← hh]
    exact congrArg Units.val (map_finGL v (locGL E n w g))
  refine mat_ext ?_ fun v => ?_
  · have hc : (cT (conjAd E) h.val).map (pInf E) = 1 := by
      refine Matrix.ext fun i j => ?_
      have h1 : pInf E (h.val j i) = (1 : Matrix (Fin n) (Fin n) (Cinf E)) j i := congrFun (congrFun hI j) i
      change pInf E (conjAd E (h.val j i)) = _
      rw [pInf_conjAd, h1]
      by_cases e : i = j
      · subst e; simp
      · simp [Matrix.one_apply, e, Ne.symm e]
    rw [Matrix.map_mul, hc, hI, Matrix.mul_one, Matrix.map_one _ (map_zero _) (map_one _)]
  · rcases eq_or_ne v w with rfl | hvw
    · have h0 := hL v
      rw [pLoc_locGL] at h0
      have hc : (cT (conjAd E) h.val).map ((pLoc E v).comp (pFin E)) = cT s g.val := by
        refine Matrix.ext fun i j => ?_
        have h1 : pLoc E v (pFin E (h.val j i)) = g.val j i := congrFun (congrFun h0 j) i
        change pLoc E v (conjFin (IsCMField.complexConj E).toRingEquiv (pFin E (h.val j i))) = s (g.val j i)
        rw [pLoc_conjFin_eq _ v s hs hv, h1]
      rw [Matrix.map_mul, hc, h0, hg', Matrix.map_one _ (map_zero _) (map_one _)]
    · have h0 := hL v
      rw [pLoc_locGL_of_ne hvw] at h0
      have hne : conjSrc (IsCMField.complexConj E).toRingEquiv v ≠ w := fun e =>
        hvw ((existsUnique_conjPl _ w).unique (e ▸ conjPl_conjSrc _ v) hw)
      have h2 := hL (conjSrc (IsCMField.complexConj E).toRingEquiv v)
      rw [pLoc_locGL_of_ne hne] at h2
      have hc : (cT (conjAd E) h.val).map ((pLoc E v).comp (pFin E)) = 1 := by
        refine Matrix.ext fun i j => ?_
        have h1 : pLoc E (conjSrc (IsCMField.complexConj E).toRingEquiv v) (pFin E (h.val j i)) =
            (1 : Matrix (Fin n) (Fin n) _) j i := congrFun (congrFun h2 j) i
        change pLoc E v (conjFin (IsCMField.complexConj E).toRingEquiv (pFin E (h.val j i))) = _
        rw [pLoc_conjFin, h1]
        by_cases e : i = j
        · subst e; simp
        · simp [Matrix.one_apply, e, Ne.symm e]
      have h0' : h.val.map ((pLoc E v).comp (pFin E)) = 1 := h0
      rw [Matrix.map_mul, hc, h0', Matrix.mul_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem finGL_mem_locU {w : HeightOneSpectrum (𝓞 E)} (hw : ConjPl (IsCMField.complexConj E).toRingEquiv w w)
    (g : GL (Fin n) (w.adicCompletion E)) (hU : finGL E n (locGL E n w g) ∈ UA E n) :
    (⟨_, hU⟩ : UA E n) ∈ locU n w := by
  refine Subgroup.mem_inf.2 ⟨pInf_finGL _, ?_⟩
  simp only [Subgroup.mem_iInf]
  intro u hu
  have hne : u ≠ w := fun e => hu (by rw [e])
  exact (map_finGL u _).trans (pLoc_locGL_of_ne hne g)

theorem finGL_cLoc {w : HeightOneSpectrum (𝓞 E)} (hw : ConjPl (IsCMField.complexConj E).toRingEquiv w w)
    (x : locU n w) : finGL E n (locGL E n w (cLoc w (x : UA E n))) = (x : UA E n).1 := by
  have hx := Subgroup.mem_inf.1 x.2
  have hx2 := hx.2
  simp only [Subgroup.mem_iInf] at hx2
  refine Units.ext (mat_ext ?_ fun v => ?_)
  · have h1 : GeneralLinearGroup.map (pInf E) (x : UA E n).1 = 1 := hx.1
    have h2 := pInf_finGL (locGL E n w (cLoc w (x : UA E n)))
    exact congrArg Units.val (h2.trans h1.symm)
  · have h1 : GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (finGL E n (locGL E n w (cLoc w (x : UA E n)))) =
        GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (x : UA E n).1 := by
      refine (map_finGL v _).trans ?_
      rcases eq_or_ne v w with rfl | hvw
      · exact pLoc_locGL v _
      · rw [pLoc_locGL_of_ne hvw]
        have := hx2 v fun e => hvw (eq_of_under_eq hw e)
        exact (MonoidHom.mem_ker.1 this).symm
    exact congrArg Units.val h1

theorem locU_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E))
    (s : w.adicCompletion E →+* w.adicCompletion E),
    (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) →
    (∀ x, Valued.v (s x) = Valued.v x) →
    ∃ e : locU n w ≃ₜ* UJ s (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)),
      ∀ x : locU n w, (e x : GL (Fin n) (w.adicCompletion E)) = cLoc w (x : UA E n) := by
  intro E _ _ _ n w s hs hv
  have hw := conjPl_self w s hs hv
  have hf : ∀ x : locU n w, cLoc w (x : UA E n) ∈ UJ s (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := fun x => by
    change cT s _ * 1 * _ = 1
    rw [Matrix.mul_one]
    exact cT_cLoc w s hs hv _
  refine ⟨{ toFun := fun x => ⟨cLoc w (x : UA E n), hf x⟩
            invFun := fun g => ⟨⟨finGL E n (locGL E n w g.1), finGL_mem w s hs hv g.1 g.2⟩,
              finGL_mem_locU hw g.1 _⟩
            left_inv := fun x => Subtype.ext (Subtype.ext (finGL_cLoc hw x))
            right_inv := fun g => Subtype.ext ?_
            map_mul' := fun x y => Subtype.ext (map_mul (cLoc w) (x : UA E n) y)
            continuous_toFun := Continuous.subtype_mk ((continuous_cLoc w).comp continuous_subtype_val) _
            continuous_invFun := Continuous.subtype_mk (Continuous.subtype_mk
              (continuous_finGL.comp ((CuspSub.continuous_locGL w).comp continuous_subtype_val)) _) _ }, fun _ => rfl⟩
  exact (map_finGL w _).trans (pLoc_locGL w _)

end GlobalTheory.DefU.Inert

end
