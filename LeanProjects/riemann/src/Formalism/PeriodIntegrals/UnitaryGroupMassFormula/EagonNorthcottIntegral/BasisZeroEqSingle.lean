import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EagonNorthcottIntegral.YHom
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EagonNorthcottIntegral.DivisionPartitionTotal

noncomputable section

namespace PI.EagonNorthcottZ

open MvPolynomial

private def mon {D : ℕ} (α : Fin D → ℕ) : Fin D ⊕ Fin D →₀ ℕ := ∑ i, Finsupp.single (Sum.inr i) (α i)

private def yp {D : ℕ} (α : Fin D → ℕ) : P D := ∏ i, ys i ^ α i

private lemma mon_inr {D : ℕ} (α : Fin D → ℕ) (i : Fin D) : mon α (Sum.inr i) = α i := by
  classical
  simp [mon, Finsupp.finsetSum_apply, Finsupp.single_apply]

private lemma mon_inl {D : ℕ} (α : Fin D → ℕ) (i : Fin D) : mon α (Sum.inl i) = 0 := by
  classical
  simp [mon, Finsupp.finsetSum_apply]

private lemma yp_eq {D : ℕ} (α : Fin D → ℕ) : yp α = monomial (mon α) (1 : ℤ) := by
  rw [yp, mon, monomial_sum_one]
  simp [ys, X_pow_eq_monomial]

private lemma noX_iff {D : ℕ} (f : P D) : NoX f ↔ ∃ g, rename Sum.inr g = f := Iff.rfl

private lemma nox_zero {D : ℕ} : NoX (0 : P D) := (noX_iff _).2 ⟨0, map_zero _⟩

private lemma nox_add {D : ℕ} {f g : P D} (hf : NoX f) (hg : NoX g) : NoX (f + g) := by
  obtain ⟨u, rfl⟩ := (noX_iff _).1 hf
  obtain ⟨v, rfl⟩ := (noX_iff _).1 hg
  exact (noX_iff _).2 ⟨u + v, map_add _ _ _⟩

private lemma nox_smul {D : ℕ} (c : ℤ) {f : P D} (hf : NoX f) : NoX (c • f) := by
  obtain ⟨u, rfl⟩ := (noX_iff _).1 hf
  exact (noX_iff _).2 ⟨c • u, map_smul _ _ _⟩

private lemma noX_coeff {D : ℕ} {f : P D} (hf : NoX f) {m : Fin D ⊕ Fin D →₀ ℕ} (hm : m ∈ f.support)
    (i : Fin D) : m (Sum.inl i) = 0 := by
  classical
  by_contra h
  obtain ⟨g, rfl⟩ := (noX_iff _).1 hf
  have h1 : Sum.inl i ∈ (rename Sum.inr g).vars := (mem_vars_iff_mem_support _).2 ⟨m, hm, Finsupp.mem_support_iff.2 h⟩
  have h2 := vars_rename Sum.inr g h1
  simp at h2

private lemma yhom_zero {D a : ℕ} : YHom (D := D) a 0 := by
  intro m hm
  simp at hm

private lemma yhom_add {D a : ℕ} {f g : P D} (hf : YHom a f) (hg : YHom a g) : YHom a (f + g) := by
  classical
  intro m hm
  rcases Finset.mem_union.1 (support_add hm) with h | h
  exacts [hf m h, hg m h]

private lemma yhom_smul {D a : ℕ} (c : ℤ) {f : P D} (hf : YHom a f) : YHom a (c • f) :=
  fun m hm => hf m (support_smul hm)

private lemma memA {D a : ℕ} {f : P D} (h1 : NoX f) (h2 : YHom a f) :
    f ∈ Submodule.span ℤ (yp '' {α : Fin D → ℕ | ∑ i, α i = a}) := by
  classical
  rw [f.as_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  have hmon : m = mon (fun i => m (Sum.inr i)) := by
    ext v
    rcases v with i | i
    · rw [mon_inl, noX_coeff h1 hm i]
    · rw [mon_inr]
  have hmem : monomial m (1 : ℤ) ∈ yp '' {α : Fin D → ℕ | ∑ i, α i = a} :=
    ⟨fun i => m (Sum.inr i), h2 m hm, by rw [yp_eq, ← hmon]⟩
  have : monomial m (coeff m f) = coeff m f • monomial m (1 : ℤ) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

private lemma K_zero {D : ℕ} (t : Fin D → P D) : K t 0 = 0 := by
  funext J
  simp [K]

private lemma K_add {D : ℕ} (t : Fin D → P D) (ω η : W D) : K t (ω + η) = K t ω + K t η := by
  funext J
  simp [K, mul_add, Finset.sum_add_distrib]

private lemma K_smul {D : ℕ} (t : Fin D → P D) (c : ℤ) (ω : W D) : K t (c • ω) = c • K t ω := by
  funext J
  simp only [K, Pi.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm]

private lemma isZL_iff {D a j : ℕ} (ω : W D) : IsZL a j ω ↔
    (((∀ J, J.card ≠ j → ω J = 0) ∧ ∀ J, YHom a (ω J)) ∧ K ys ω = 0) ∧ ∀ J, NoX (ω J) := Iff.rfl

private def ZL (D a j : ℕ) : Submodule ℤ (W D) where
  carrier := {ω | IsZL a j ω}
  zero_mem' := (isZL_iff _).2 ⟨⟨⟨fun _ _ => rfl, fun _ => yhom_zero⟩, K_zero _⟩, fun _ => nox_zero⟩
  add_mem' := by
    intro ω η hω hη
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := (isZL_iff _).1 hω
    obtain ⟨⟨⟨g1, g2⟩, g3⟩, g4⟩ := (isZL_iff _).1 hη
    refine (isZL_iff _).2 ⟨⟨⟨fun J hJ => ?_, fun J => yhom_add (h2 J) (g2 J)⟩, ?_⟩,
      fun J => nox_add (h4 J) (g4 J)⟩
    · simp [h1 J hJ, g1 J hJ]
    · rw [K_add, h3, g3, add_zero]
  smul_mem' := by
    intro c ω hω
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := (isZL_iff _).1 hω
    refine (isZL_iff _).2 ⟨⟨⟨fun J hJ => ?_, fun J => yhom_smul c (h2 J)⟩, ?_⟩,
      fun J => nox_smul c (h4 J)⟩
    · simp [h1 J hJ]
    · rw [K_smul, h3, smul_zero]

private def G (D a : ℕ) : Set (W D) :=
  Set.range fun p : Finset (Fin D) × {α // α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin D)) a} =>
    (Pi.single p.1 (yp p.2.1) : W D)

private lemma memB {D a : ℕ} {ω : W D} (h : ∀ J, NoX (ω J) ∧ YHom a (ω J)) :
    ω ∈ Submodule.span ℤ (G D a) := by
  classical
  rw [← Finset.univ_sum_single ω]
  refine Submodule.sum_mem _ fun J _ => ?_
  have h3 := Submodule.mem_map_of_mem (f := LinearMap.single ℤ (fun _ : Finset (Fin D) => P D) J)
    (memA (h J).1 (h J).2)
  rw [← Submodule.span_image] at h3
  refine Submodule.span_mono ?_ h3
  rintro _ ⟨_, ⟨α, hα, rfl⟩, rfl⟩
  exact ⟨(J, ⟨α, by simpa [Finset.mem_piAntidiag] using hα⟩), by simp⟩

end PI.EagonNorthcottZ
