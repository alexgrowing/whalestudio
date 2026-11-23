import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShortHarmonicFamilyLinear
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShortHarmonicFamilyUnimodularStatement

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.StdHarm

open MvPolynomial

variable {E : Type} [Field E] [NumberField E]

theorem mem_std {n : ℕ} (v : Fin n → E) : v ∈ stdLat E n ↔ ∀ j, IsIntegral ℤ (v j) := by
  simp only [stdLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
  refine forall_congr' fun j => ⟨?_, fun h => ⟨⟨v j, h⟩, rfl⟩⟩
  rintro ⟨y, hy⟩
  rw [← hy]
  exact y.isIntegral_coe

theorem single_mem_std {n : ℕ} (j : Fin n) : (Pi.single j 1 : Fin n → E) ∈ stdLat E n := by
  rw [mem_std]
  intro k
  by_cases h : k = j
  · subst h; simpa using isIntegral_one
  · simpa [h] using isIntegral_zero

theorem std_fg (n : ℕ) : (stdLat E n).FG :=
  Submodule.fg_pi fun _ => by
    rw [Submodule.one_eq_span]
    exact Submodule.fg_span_singleton _

variable [IsCMField E]

theorem std_unimod (n : ℕ) : (⟨stdLat E n⟩ : GenLat E n).Unimod := by
  have hc (x : E) (hx : IsIntegral ℤ x) : IsIntegral ℤ (IsCMField.complexConj E x) :=
    hx.map_of_comp_eq (RingHom.id ℤ) (IsCMField.complexConj E : E →+* E) (RingHom.ext_int _ _)
  intro v
  constructor
  · intro hv w hw
    have h : IsIntegral ℤ (∑ j, IsCMField.complexConj E (v j) * w j) :=
      IsIntegral.sum _ fun j _ => (hc _ ((mem_std v).1 hv j)).mul ((mem_std w).1 hw j)
    exact ⟨⟨_, h⟩, rfl⟩
  · intro h
    refine (mem_std v).2 fun j => ?_
    obtain ⟨y, hy⟩ := h _ (single_mem_std j)
    have h1 : IsCMField.complexConj E (v j) = algebraMap (𝓞 E) E y := by
      rw [hy]
      simp [Pi.single_apply]
    have h2 := hc _ y.isIntegral_coe
    rwa [← h1, IsCMField.complexConj_apply_apply] at h2

variable {H : Host E} {Dw : Datum H} {l : Level H} (c : Coeff l)

theorem symO_std (n : ℕ) : Formalism.L2.Pj.symO (Dw := Dw) c (⟨stdLat E n⟩ : GenLat E n) =
    (MvPolynomial.map (σ := LtN Dw n) (algebraMap (integralClosure ℤ c.F) c.F)).range := by
  apply le_antisymm
  · refine Subring.closure_le.2 ?_
    rintro f (⟨o, rfl⟩ | ⟨σ, i, b, hb, rfl⟩)
    · exact ⟨C o, by simp⟩
    · refine Subring.sum_mem _ fun j _ => Subring.mul_mem _ ?_ ⟨X _, map_X _ _⟩
      have h : IsIntegral ℤ (embF c σ (b j)) :=
        ((mem_std b).1 hb j).map_of_comp_eq (RingHom.id ℤ) (embF c σ) (RingHom.ext_int _ _)
      exact ⟨C ⟨_, h⟩, map_C _ _⟩
  · rintro _ ⟨Q, rfl⟩
    induction Q using MvPolynomial.induction_on with
    | C o => exact Subring.subset_closure (Or.inl ⟨o, by rw [map_C]; rfl⟩)
    | add p q hp hq => rw [map_add]; exact Subring.add_mem _ hp hq
    | mul_X p s hp =>
      rw [map_mul, map_X]
      refine Subring.mul_mem _ hp (Subring.subset_closure (Or.inr ?_))
      obtain ⟨σ, i, j⟩ := s
      refine ⟨σ, i, Pi.single j 1, single_mem_std j, ?_⟩
      rw [letB, Finset.sum_eq_single j]
      · simp
      · intro k _ hk
        simp [hk]
      · simp

theorem harmL_std (n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) :
    harmL (Dw := Dw) c (⟨stdLat E n⟩ : GenLat E n) a = harmA c a n := by
  ext P
  refine and_congr_right fun _ => ?_
  rw [symO_std]
  constructor
  · rintro ⟨Q, rfl⟩ m
    rw [coeff_map]
    exact (coeff m Q).2
  · intro h
    refine mem_range_map_iff_coeffs_subset.2 fun x hx => ?_
    obtain ⟨m, -, rfl⟩ := mem_coeffs_iff.1 hx
    exact ⟨⟨_, h m⟩, rfl⟩

theorem harmA_mem_span_short : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (n : ℕ), (∀ a : (E →+* ℂ) × ℕ → ℕ, harmL (Dw := Dw) c (⟨stdLat E n⟩ : GenLat E n) a = harmA c a n) ∧ (Dw.p + Dw.q ≤ n → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (L : ℝ), 2 ≤ L → Real.log (FD.rdE E) ≤ 2 * L → Real.log (FD.fdeg E) ≤ 2 * L → Real.log (1 + DF Dw a) ≤ 2 * L → Real.log n ≤ L → ∀ P ∈ harmA (Dw := Dw) c a n, P ∈ Submodule.span c.F {Q : MvPolynomial (LtN Dw n) c.F | Q ∈ harmA c a n ∧ ∀ σ' : c.F →+* ℂ, Real.log (∑ m ∈ Q.support, ‖σ' (Q.coeff m)‖) ≤ 140 * (Dw.p + Dw.q : ℕ) * L * DF Dw a}) := by
  intro E _ _ _ H Dw l c n
  refine ⟨harmL_std c n, fun hn a L hL h1 h2 h3 h4 P hP => ?_⟩
  obtain ⟨S, hS, hspan, -⟩ := GlobalTheory.T.exists_short_harmonic_family_unimodular E H Dw l c n ⟨stdLat E n⟩ (std_unimod n) (std_fg n)
    hn a L hL h1 h2 h3 h4
  refine Submodule.span_mono (fun Q hQ => ?_) (hspan P hP.1)
  exact ⟨harmL_std c n a ▸ (hS Q hQ).1, (hS Q hQ).2⟩

end GlobalTheory.StdHarm
