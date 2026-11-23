import Formalism.PeriodIntegrals.HermitianGenusExtension.SemilocalHermitianLattices.MassSt
import Formalism.HermitianLattices.HermitianLatticesProofs.MassBasic
import Formalism.HermitianLattices.HermitianLatticesProofs.LocDual

open NumberField Module

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L3

def stdForm (K : Type) [Field K] [StarRing K] (n : ℕ) :
    (Fin n → K) →ₗ⋆[K] (Fin n → K) →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K) (fun x y => ∑ i, star (x i) * y i)
    (fun x x' y => by simp [add_mul, Finset.sum_add_distrib])
    (fun c x y => by simp [Finset.mul_sum, mul_assoc, starRingEnd_apply])
    (fun x y y' => by simp [mul_add, Finset.sum_add_distrib])
    (fun c x y => by simp [Finset.mul_sum, mul_left_comm])

def stdLat (K : Type) [Field K] (n : ℕ) : Submodule (𝓞 K) (Fin n → K) :=
  Submodule.span (𝓞 K) (Set.range fun i : Fin n => (Pi.single i 1 : Fin n → K))

theorem stdForm_apply (K : Type) [Field K] [StarRing K] (n : ℕ) (x y : Fin n → K) :
    stdForm K n x y = ∑ i, star (x i) * y i := rfl

theorem stdForm_isSymm (K : Type) [Field K] [StarRing K] (n : ℕ) : (stdForm K n).IsSymm := by
  refine ⟨fun x y => ?_⟩
  simp [stdForm_apply, mul_comm, starRingEnd_apply]

theorem stdLat_isOrtho (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ) :
    Formalism.HermitianLatticesTheory.IsOrthoLattice (stdForm K n) (stdLat K n) n := by
  refine ⟨fun i => Pi.single i 1, ?_, ?_, rfl, ?_⟩
  · have := (Pi.basisFun K (Fin n)).linearIndependent
    rwa [show ⇑(Pi.basisFun K (Fin n)) = fun i => (Pi.single i 1 : Fin n → K) from
      funext fun i => Pi.basisFun_apply K (Fin n) i] at this
  · have := (Pi.basisFun K (Fin n)).span_eq
    rwa [show ⇑(Pi.basisFun K (Fin n)) = fun i => (Pi.single i 1 : Fin n → K) from
      funext fun i => Pi.basisFun_apply K (Fin n) i] at this
  · intro i j
    rw [stdForm_apply]
    by_cases hij : i = j
    · subst hij
      simp [Pi.single_apply]
    · simp [Pi.single_apply, hij, Ne.symm hij]

section Ortho

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

namespace StandardSymmetricSums

theorem form_sum {h : V →ₗ⋆[K] V →ₗ[K] K} {n : ℕ} {e : Fin n → V}
    (he : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) (c d : Fin n → K) :
    h (∑ i, c i • e i) (∑ j, d j • e j) = ∑ i, star (c i) * d i := by
  simp [map_sum, LinearMap.sum_apply, he, mul_comm, starRingEnd_apply]

theorem form_left {h : V →ₗ⋆[K] V →ₗ[K] K} {n : ℕ} {e : Fin n → V}
    (he : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) (i : Fin n) (d : Fin n → K) :
    h (e i) (∑ j, d j • e j) = d i := by
  simp [map_sum, he]

theorem star_int (r : 𝓞 K) : ∃ t : 𝓞 K, algebraMap (𝓞 K) K t = star (algebraMap (𝓞 K) K r) :=
  ⟨RingOfIntegers.mapRingHom (starRingEnd K) r, rfl⟩

theorem exists_coord {n : ℕ} {e : Fin n → V} (hsp : Submodule.span K (Set.range e) = ⊤) (x : V) :
    ∃ c : Fin n → K, ∑ i, c i • e i = x :=
  (Submodule.mem_span_range_iff_exists_fun K).1 (hsp ▸ Submodule.mem_top)

theorem mem_lat_iff {n : ℕ} {e : Fin n → V} (x : V) :
    x ∈ Submodule.span (𝓞 K) (Set.range e) ↔
      ∃ c : Fin n → 𝓞 K, ∑ i, algebraMap (𝓞 K) K (c i) • e i = x := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  simp only [algebraMap_smul]

end StandardSymmetricSums

open StandardSymmetricSums

theorem finiteDimensional_of_ortho {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {n : ℕ}
    (hL : Formalism.HermitianLatticesTheory.IsOrthoLattice h L n) : FiniteDimensional K V := by
  obtain ⟨e, hli, hsp, -, -⟩ := hL
  exact (Basis.mk hli hsp.ge).finiteDimensional_of_finite

theorem finrank_of_ortho {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {n : ℕ}
    (hL : Formalism.HermitianLatticesTheory.IsOrthoLattice h L n) : finrank K V = n := by
  obtain ⟨e, hli, hsp, -, -⟩ := hL
  simpa using finrank_eq_card_basis (Basis.mk hli hsp.ge)

theorem isLattice_of_ortho {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {n : ℕ}
    (hL : Formalism.HermitianLatticesTheory.IsOrthoLattice h L n) : Submodule.IsLattice K L := by
  obtain ⟨e, hli, hsp, rfl, -⟩ := hL
  refine ⟨Submodule.fg_span (Set.finite_range e), ?_⟩
  rw [Submodule.span_span_of_tower, hsp]

theorem isTotPosDef_of_ortho (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) {L : Submodule (𝓞 K) V} {n : ℕ} (hL : Formalism.HermitianLatticesTheory.IsOrthoLattice h L n) :
    IsTotPosDef h := by
  obtain ⟨e, hli, hsp, -, he⟩ := hL
  intro x hx φ
  obtain ⟨c, rfl⟩ := exists_coord hsp x
  rw [form_sum he, map_sum, Complex.re_sum]
  have hc : ∃ i, c i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx (by simp [hcon])
  obtain ⟨i, hi⟩ := hc
  have hterm : ∀ j, (φ (star (c j) * c j)).re = Complex.normSq (φ (c j)) := by
    intro j
    rw [map_mul, hK.2.1, Complex.normSq_eq_conj_mul_self.symm, Complex.ofReal_re]
  simp only [hterm]
  refine Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ _, ?_⟩
  exact Complex.normSq_pos.2 (by simpa using hi)

theorem trace_pos_of_ortho (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) {L : Submodule (𝓞 K) V} {n : ℕ} (hL : Formalism.HermitianLatticesTheory.IsOrthoLattice h L n) :
    ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x) := by
  intro x hx
  have hp := isTotPosDef_of_ortho hK hs hL x hx
  have ht := trace_eq_sum_embeddings (K := ℚ) (L := K) ℂ (x := h x x)
  have hre := congrArg Complex.re ht
  rw [Complex.re_sum] at hre
  have hpos : 0 < ∑ σ : K →ₐ[ℚ] ℂ, (σ (h x x)).re :=
    Finset.sum_pos (fun σ _ => hp σ.toRingHom)
      ⟨(Classical.arbitrary (K →+* ℂ)).toRatAlgHom, Finset.mem_univ _⟩
  rw [← hre] at hpos
  have : (algebraMap ℚ ℂ (Algebra.trace ℚ K (h x x))).re = ((Algebra.trace ℚ K (h x x) : ℚ) : ℝ) := by
    simp
  rw [this] at hpos
  exact_mod_cast hpos

theorem isIntegralLat_of_ortho {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {n : ℕ}
    (hL : Formalism.HermitianLatticesTheory.IsOrthoLattice h L n) : Formalism.HermitianLatticesTheory.IsIntegralLat h L := by
  obtain ⟨e, hli, hsp, rfl, he⟩ := hL
  intro x hx y hy
  obtain ⟨c, rfl⟩ := (mem_lat_iff x).1 hx
  obtain ⟨d, rfl⟩ := (mem_lat_iff y).1 hy
  rw [form_sum he]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨t, ht⟩ := star_int (c i)
  rw [← ht, ← map_mul]
  exact Submodule.mem_one.2 ⟨_, rfl⟩

theorem isUnimodular_of_ortho {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {n : ℕ}
    (hL : Formalism.HermitianLatticesTheory.IsOrthoLattice h L n) : Formalism.HermitianLatticesTheory.IsUnimodular h L := by
  have hint := isIntegralLat_of_ortho hL
  obtain ⟨e, hli, hsp, rfl, he⟩ := hL
  apply le_antisymm
  · intro x hx
    obtain ⟨c, rfl⟩ := exists_coord hsp x
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.coe_restrictScalars] at hx
    have hc : ∀ i, ∃ r : 𝓞 K, algebraMap (𝓞 K) K r = c i := by
      intro i
      have := hx (e i) (Submodule.subset_span ⟨i, rfl⟩)
      rw [form_left he] at this
      exact Submodule.mem_one.1 this
    choose r hr using hc
    exact (mem_lat_iff _).2 ⟨r, by simp only [hr]⟩
  · intro x hx
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.coe_restrictScalars]
    exact fun y hy => hint y hy x hx

theorem isUnimodularAt_of_ortho (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) {L : Submodule (𝓞 K) V} {n : ℕ} (hL : Formalism.HermitianLatticesTheory.IsOrthoLattice h L n) :
    ∀ p : Ideal (𝓞 K), p.IsMaximal → Formalism.HermitianLatticesTheory.IsUnimodularAt h p L :=
  ((Formalism.HermitianLatticesTheory.locDual (𝓞 K) K V h hs (fun r => (star_int r).imp fun _ ht => ht) L
    (isLattice_of_ortho hL).fg).2).1 (isUnimodular_of_ortho hL)

theorem mass_pos_of_ortho (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) {L : Submodule (𝓞 K) V} {n : ℕ} (hL : Formalism.HermitianLatticesTheory.IsOrthoLattice h L n) :
    0 < Formalism.HermitianLatticesTheory.mass h L := by
  have := finiteDimensional_of_ortho hL
  exact (Formalism.HermitianLatticesTheory.massBasic K V h hs (trace_pos_of_ortho hK hs hL) L (isLattice_of_ortho hL)).2.2

end Ortho

end ReciprocityTheory.ChartRestriction.L3
