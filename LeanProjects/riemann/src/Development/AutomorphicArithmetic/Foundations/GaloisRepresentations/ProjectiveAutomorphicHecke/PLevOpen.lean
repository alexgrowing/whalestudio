import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CentralEig2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenKGLInvEntries
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

private theorem isOpen_intA (F : Type) [Field F] [NumberField F] :
    IsOpen {a : FiniteAdeleRing (𝓞 F) F | ∀ v, Valued.v (a v) ≤ 1} :=
  RestrictedProduct.isOpen_forall_mem
    (A := fun v : HeightOneSpectrum (𝓞 F) => ((v.adicCompletionIntegers F : ValuationSubring _) : Set (v.adicCompletion F)))
    (fun v => Valued.isOpen_valuationSubring _)

private theorem continuous_sim {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} :
    Continuous (sim : GUf E n → AfQˣ) := continuous_snd.comp continuous_subtype_val

private theorem continuous_mat {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} :
    Continuous (mat : GUf E n → GL (Fin n) (Af E)) := continuous_fst.comp continuous_subtype_val

private theorem continuous_comp {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (w : Plc E) :
    Continuous (comp w : GUf E n → GL (Fin n) (w.adicCompletion E)) :=
  (Continuous.units_map _ (continuous_id.matrix_map (RestrictedProduct.continuous_eval w))).comp continuous_mat

theorem UpperTheory.Gal.CertificateRingHomMap.pLevOpen_of :
    UpperTheory.Gal.CertificateRingHomMap.LevOpen := by
  intro E _ _ _ n S Kw hK
  have hI : IsOpen {a : Af E | ∀ v, Valued.v (a v) ≤ 1} := isOpen_intA E
  have hJ : IsOpen {a : AfQ | ∀ v, Valued.v (a v) ≤ 1} := isOpen_intA ℚ
  let A : Set (GUf E n) :=
    ((((fun k => ((sim k : AfQˣ) : AfQ)) ⁻¹' {a : AfQ | ∀ v, Valued.v (a v) ≤ 1}) ∩
      ((fun k => (((sim k)⁻¹ : AfQˣ) : AfQ)) ⁻¹' {a : AfQ | ∀ v, Valued.v (a v) ≤ 1})) ∩
    ((⋂ i, ⋂ j, (fun k => (mat k).val i j) ⁻¹' {a : Af E | ∀ v, Valued.v (a v) ≤ 1}) ∩
      (⋂ i, ⋂ j, (fun k => ((mat k)⁻¹).val i j) ⁻¹' {a : Af E | ∀ v, Valued.v (a v) ≤ 1}))) ∩
    ⋂ w ∈ S, comp w ⁻¹' (Kw w : Set (GLw n w))
  have hAo : IsOpen A := by
    refine ((IsOpen.inter ?_ ?_).inter (IsOpen.inter ?_ ?_)).inter ?_
    · exact hJ.preimage (Units.continuous_val.comp continuous_sim)
    · exact hJ.preimage (Units.continuous_val.comp continuous_sim.inv)
    · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        hI.preimage ((Units.continuous_val.comp continuous_mat).matrix_elem i j)
    · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        hI.preimage ((Units.continuous_val.comp continuous_mat.inv).matrix_elem i j)
    · exact isOpen_biInter_finset fun w hw => (hK w hw).preimage (continuous_comp w)
  have hone : ∀ (i j : Fin n) (v : Plc E), Valued.v (((1 : Matrix (Fin n) (Fin n) (Af E)) i j) v) ≤ 1 := by
    intro i j v
    by_cases h : i = j
    · subst h
      rw [Matrix.one_apply_eq]
      change Valued.v (1 : v.adicCompletion E) ≤ 1
      rw [map_one]
    · rw [Matrix.one_apply_ne h]
      change Valued.v (0 : v.adicCompletion E) ≤ 1
      rw [map_zero]
      exact zero_le'
  have hQ : ∀ v : Plc ℚ, Valued.v ((1 : AfQ) v) ≤ 1 := fun v => by
    change Valued.v (1 : v.adicCompletion ℚ) ≤ 1
    rw [map_one]
  have h1 : (1 : GUf E n) ∈ A := by
    refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
    · simpa using hQ
    · simpa using hQ
    · simp only [Set.mem_iInter, Set.mem_preimage, map_one]
      exact fun i j => hone i j
    · simp only [Set.mem_iInter, Set.mem_preimage, map_one, inv_one]
      exact fun i j => hone i j
    · simp only [Set.mem_iInter, Set.mem_preimage, map_one]
      exact fun w _ => (Kw w).one_mem
  have hsub : A ⊆ (lev S Kw : Set (GUf E n)) := by
    rintro k ⟨⟨⟨hs, hs'⟩, hm, hm'⟩, hc⟩
    simp only [Set.mem_iInter, Set.mem_preimage] at hm hm' hc
    refine mem_lev.2 ⟨fun v => ?_, fun w hw => hc w hw, fun w _ _ => ?_⟩
    · have h : Valued.v (((sim k : AfQˣ) : AfQ) v * (((sim k)⁻¹ : AfQˣ) : AfQ) v) = 1 := by
        change Valued.v ((((sim k : AfQˣ) : AfQ) * (((sim k)⁻¹ : AfQˣ) : AfQ)) v) = 1
        rw [Units.mul_inv]
        exact map_one _
      rw [map_mul] at h
      refine le_antisymm (hs v) ?_
      calc (1 : _) = _ := h.symm
        _ ≤ Valued.v (((sim k : AfQˣ) : AfQ) v) * 1 := mul_le_mul' le_rfl (hs' v)
        _ = _ := mul_one _
    · rw [GlobalTheory.HenQ.Basic.mem_KGL_iff]
      refine ⟨fun i j => hm i j w, fun i j => ?_⟩
      have : (comp w k)⁻¹ = GeneralLinearGroup.map (pLoc E w) (mat k)⁻¹ := (map_inv _ _).symm
      rw [this]
      exact hm' i j w
  exact Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (hAo.mem_nhds h1) hsub)
