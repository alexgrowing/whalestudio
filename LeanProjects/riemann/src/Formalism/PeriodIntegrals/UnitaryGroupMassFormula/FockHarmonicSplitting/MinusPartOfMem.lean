import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockHarmonicSplitting.FockCore
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockHarmonicSplitting.ConjTransposeOneKronecker
import Formalism.PeriodIntegrals.FockDegreeTwoParts

noncomputable section

open MvPolynomial Matrix FockH1Action

namespace PI.FHS

section Parts

variable {σ : Type*}

lemma plusPart_of_mem {A : Module.End ℂ (MvPolynomial σ ℂ)} {d : ℕ} {P : MvPolynomial σ ℂ}
    (hP : P ∈ homog σ d) : plusPart A P = homogeneousComponent (d + 2) (A P) := by
  unfold plusPart
  rw [finsum_eq_single _ d]
  · rw [homogeneousComponent_of_mem hP, if_pos rfl]
  · intro e he
    rw [homogeneousComponent_of_mem hP, if_neg he, map_zero, map_zero]

lemma minusPart_of_mem {A : Module.End ℂ (MvPolynomial σ ℂ)} {d : ℕ} {Q : MvPolynomial σ ℂ}
    (hQ : Q ∈ homog σ (d + 2)) : minusPart A Q = homogeneousComponent d (A Q) := by
  unfold minusPart
  rw [finsum_eq_single _ d]
  · rw [homogeneousComponent_of_mem hQ, if_pos rfl]
  · intro e he
    rw [homogeneousComponent_of_mem hQ, if_neg (by omega), map_zero, map_zero]

end Parts

variable {p q r s : ℕ}

lemma kill {a b : ℕ} (A : Mat a b →ₗ[ℂ] Module.End ℂ (Pol p q r s))
    (hA : ∀ Z : Mat a b, IsPC Z → ∀ P Q, fockInner (A Z P) Q = - fockInner P (A Zᴴ Q))
    {d : ℕ} {z : Pol p q r s} (hz : z ∈ homog (Ix p q × Ix r s) (d + 2))
    (horth : ∀ Z : Mat a b, IsPC Z → ∀ g ∈ homog (Ix p q × Ix r s) d,
      fockInner (plusPart (A Z) g) z = 0)
    (Z : Mat a b) (hZ : IsPC Z) : minusPart (A Z) z = 0 := by
  have hm : minusPart (A Z) z = homogeneousComponent d (A Z z) := minusPart_of_mem hz
  have hmem : minusPart (A Z) z ∈ homog (Ix p q × Ix r s) d := by
    rw [hm]
    exact homogeneousComponent_mem d _
  apply fockInner_self_eq_zero
  calc fockInner (minusPart (A Z) z) (minusPart (A Z) z)
      = fockInner (homogeneousComponent d (A Z z)) (minusPart (A Z) z) := by rw [← hm]
    _ = fockInner (A Z z) (minusPart (A Z) z) := fockInner_hc_left _ _ hmem
    _ = - fockInner z (A Zᴴ (minusPart (A Z) z)) := hA Z hZ _ _
    _ = - fockInner z (homogeneousComponent (d + 2) (A Zᴴ (minusPart (A Z) z))) := by
        rw [fockInner_hc_right _ _ hz]
    _ = - fockInner z (plusPart (A Zᴴ) (minusPart (A Z) z)) := by rw [plusPart_of_mem hmem]
    _ = 0 := by rw [← fockInner_conj, horth Zᴴ (isPC_ct hZ) _ hmem, map_zero, neg_zero]

theorem harmSplit : PI.FockDegreeTwoParts.HarmSplit := by
  intro p q r s u1 u2 _ d
  have hRle : Submodule.span ℂ (raised p q r s u1 u2 d) ≤ homog (Ix p q × Ix r s) (d + 2) := by
    rw [Submodule.span_le]
    rintro R ⟨Q, hQ, h | h⟩
    · obtain ⟨_, Z, _, rfl⟩ := h
      rw [SetLike.mem_coe, plusPart_of_mem hQ]
      exact homogeneousComponent_mem _ _
    · obtain ⟨_, Z, _, rfl⟩ := h
      rw [SetLike.mem_coe, plusPart_of_mem hQ]
      exact homogeneousComponent_mem _ _
  apply le_antisymm
  · intro f hf
    obtain ⟨y, hy, horth⟩ := exists_orth (Submodule.span ℂ (raised p q r s u1 u2 d)) (d + 2) hRle f
    have hfy : f - y ∈ homog (Ix p q × Ix r s) (d + 2) := Submodule.sub_mem _ hf (hRle hy)
    have hlow : f - y ∈ lowKer p q r s u1 u2 := by
      refine ⟨fun hu Z hZ => ?_, fun hu Z hZ => ?_⟩
      · refine kill (fockAct1 p q r s) (fun Z hZ P Q => fockAct1_adj hZ P Q) hfy (fun Z' hZ' g hg => ?_) Z hZ
        exact horth _ (Submodule.subset_span ⟨g, hg, Or.inl ⟨hu, Z', hZ', rfl⟩⟩)
      · refine kill (fockAct2 p q r s) (fun Z hZ P Q => fockAct2_adj hZ P Q) hfy (fun Z' hZ' g hg => ?_) Z hZ
        exact horth _ (Submodule.subset_span ⟨g, hg, Or.inr ⟨hu, Z', hZ', rfl⟩⟩)
    have hsplit : f = (f - y) + y := by abel
    rw [hsplit]
    exact Submodule.add_mem_sup ⟨hfy, Submodule.subset_span hlow⟩ hy
  · exact sup_le inf_le_left hRle

end PI.FHS
