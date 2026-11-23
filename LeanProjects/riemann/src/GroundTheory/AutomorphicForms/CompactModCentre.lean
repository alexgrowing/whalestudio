import Mathlib
import GroundTheory.AutomorphicForms.SchurOrthogonality

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

namespace SchurOrthogonality

open MeasureTheory Topology Set Function ComplexConjugate Module

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ G V} {σ : Representation ℂ G W}

theorem span_orbit_eq_top [π.IsIrreducible] {v : V} (hv : v ≠ 0) :
    Submodule.span ℂ (range fun g => π g v) = ⊤ := by
  set S := Submodule.span ℂ (range fun g => π g v)
  have hS : ∀ g, ∀ ⦃x⦄, x ∈ S → π g x ∈ S := by
    intro g x hx
    have : S ≤ S.comap (π g) := Submodule.span_le.2 (by
      rintro _ ⟨h, rfl⟩
      exact Submodule.subset_span ⟨g * h, by simp [Module.End.mul_apply]⟩)
    exact this hx
  rcases IsSimpleOrder.eq_bot_or_eq_top (⟨S, hS⟩ : Subrepresentation π) with h | h
  · exfalso
    apply hv
    have : v ∈ (⟨S, hS⟩ : Subrepresentation π).toSubmodule := Submodule.subset_span ⟨1, by simp⟩
    rw [h] at this
    exact (Submodule.mem_bot ℂ).1 this
  · exact congrArg Subrepresentation.toSubmodule h

theorem mem_smoothVectors_dual_of_finiteDimensional [FiniteDimensional ℂ V] (hπs : IsSmooth π)
    (φ : Module.Dual ℂ V) : φ ∈ smoothVectors (Representation.dual π) := by
  let b := Module.finBasis ℂ V
  have hopen : IsOpen ((⨅ i, stabilizerOf π (b i) : Subgroup G) : Set G) := by
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun i => hπs (b i)
  refine Subgroup.isOpen_mono (fun h hh => ?_) hopen
  rw [mem_stabilizerOf]
  have hh' : ∀ i, π h⁻¹ (b i) = b i := by
    intro i
    have : π h (b i) = b i := mem_stabilizerOf.1 (Subgroup.mem_iInf.1 hh i)
    conv_lhs => rw [← this]
    exact rep_inv_apply_apply π h (b i)
  have hid : π h⁻¹ = LinearMap.id := b.ext fun i => by rw [hh', LinearMap.id_apply]
  ext x
  rw [dual_apply_apply, hid, LinearMap.id_apply]

variable [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {Z : Subgroup G} [Z.Normal]

theorem finiteDimensional_of_compactSpace [CompactSpace (G ⧸ Z)] (hπs : IsSmooth π)
    [π.IsIrreducible] (hZ : ∀ z ∈ Z, ∃ c : ℂ, ∀ v, π z v = c • v) : FiniteDimensional ℂ V := by
  obtain ⟨v, hv⟩ := exists_ne_zero_of_isIrreducible (ρ := π)
  obtain ⟨K, -, hKo, hvK⟩ := (isSmooth_iff_forall_exists π).1 hπs v
  let U : G → Set (G ⧸ Z) := fun g => QuotientGroup.mk '' ((fun k => g * k) '' (K : Set G))
  have hUo : ∀ g, IsOpen (U g) := fun g =>
    QuotientGroup.isOpenMap_coe _ (isOpenMap_mul_left g _ hKo)
  have hcover : (univ : Set (G ⧸ Z)) ⊆ ⋃ g, U g := by
    intro q _
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    exact mem_iUnion.2 ⟨g, g, ⟨1, K.one_mem, mul_one g⟩, rfl⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hUo hcover
  set S := Submodule.span ℂ (range fun g : t => π (g : G) v)
  have hmem : ∀ g, π g v ∈ S := by
    intro g
    obtain ⟨i, hi, hgi⟩ := mem_iUnion₂.1 (ht (mem_univ (g : G ⧸ Z)))
    obtain ⟨_, ⟨k, hk, rfl⟩, hkg⟩ := hgi
    have hz : (i * k)⁻¹ * g ∈ Z := QuotientGroup.eq.1 hkg
    obtain ⟨c, hc⟩ := hZ _ hz
    have hg : g = i * k * ((i * k)⁻¹ * g) := by group
    have hkv : π k v = v := mem_fixedVectors.1 hvK k hk
    rw [hg, map_mul, Module.End.mul_apply, hc, map_smul, map_mul, Module.End.mul_apply, hkv]
    exact S.smul_mem c (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩)
  have htop : (⊤ : Submodule ℂ V) ≤ S := by
    rw [← span_orbit_eq_top (π := π) hv, Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact hmem g
  have hfg : S.FG := Submodule.fg_span (finite_range _)
  exact Module.finite_def.2 (top_le_iff.1 htop ▸ hfg)

theorem isAdmissible_of_finiteDimensional [FiniteDimensional ℂ V] (hπs : IsSmooth π) :
    IsAdmissible π :=
  ⟨hπs, fun _ _ _ => inferInstance⟩

variable [MeasurableSpace (G ⧸ Z)] [BorelSpace (G ⧸ Z)] {ν : Measure (G ⧸ Z)}

theorem isSquareIntegrable_of_compactSpace [CompactSpace (G ⧸ Z)] [IsFiniteMeasure ν]
    (hπs : IsSmooth π) (h1 : ∀ z ∈ Z, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ v, π z v = c • v) :
    IsSquareIntegrable Z ν π := by
  refine ⟨h1, fun v φ => ?_⟩
  have hc : Continuous fun q : G ⧸ Z => ‖(φ : Module.Dual ℂ V) (π q.out v)‖ :=
    continuous_apply_out (F := fun g => ‖(φ : Module.Dual ℂ V) (π g v)‖)
      (norm_coeff_mul_mem h1 v _) (continuous_dual_orbit (hπs v) _).norm
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  exact MemLp.of_bound hc.aestronglyMeasurable C (ae_of_all _ fun q => hC q (mem_univ q))

section Characters

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def character (π : Representation ℂ G V) (g : G) : ℂ :=
  LinearMap.trace ℂ V (π g)

theorem character_eq_sum {ι : Type*} [Fintype ι] (π : Representation ℂ G V) (b : Module.Basis ι ℂ V)
    (g : G) : character π g = ∑ i, b.coord i (π g (b i)) := by
  classical
  rw [character, LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
  simp [LinearMap.toMatrix_apply, Basis.coord_apply]

theorem character_eq_of_equiv {π : Representation ℂ G V} {σ : Representation ℂ G W}
    (E : π.Equiv σ) (g : G) : character σ g = character π g := by
  rw [character, character, ← Representation.Equiv.conj_apply_self g E]
  exact LinearMap.trace_conj' _ _

end Characters

section Orthogonality

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [SecondCountableTopology G]
  {Z : Subgroup G} [Z.Normal] [MeasurableSpace (G ⧸ Z)] [BorelSpace (G ⧸ Z)]
  {ν : Measure (G ⧸ Z)} [ν.IsHaarMeasure] [ν.IsMulRightInvariant] [CompactSpace (G ⧸ Z)]
  {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ G V} {σ : Representation ℂ G W}

theorem sum_pairing_basis [FiniteDimensional ℂ V] (hπ2 : IsSquareIntegrable Z ν π)
    (hπs : IsSmooth π) (v : V) (ψ : smoothVectors (Representation.dual π)) :
    ∑ j, pairing Z ν π π v ((Module.finBasis ℂ V).coord j) ((Module.finBasis ℂ V) j) ψ =
      (ν.real univ : ℂ) * (ψ : Module.Dual ℂ V) v := by
  have := isInvInvariant_of_isMulRightInvariant Z ν
  set b := Module.finBasis ℂ V
  let c : Fin (Module.finrank ℂ V) → smoothVectors (Representation.dual π) := fun j =>
    ⟨b.coord j, mem_smoothVectors_dual_of_finiteDimensional hπs _⟩
  unfold pairing
  have hI : ∀ j ∈ Finset.univ, Integrable
      (fun q : G ⧸ Z => coeffProd π π v (b.coord j) (b j) ψ q.out) ν := fun j _ =>
    integrable_coeffProd hπ2 hπ2 (sameCentralCharacter_self hπ2) hπs hπs v (c j) (b j) ψ
  rw [← integral_finsetSum _ hI]
  have hpt : ∀ q : G ⧸ Z, ∑ j, coeffProd π π v (b.coord j) (b j) ψ q.out =
      (ψ : Module.Dual ℂ V) v := by
    intro q
    simp only [coeffProd]
    have : ∑ j, b.coord j (π q.out v) * (ψ : Module.Dual ℂ V) (π q.out⁻¹ (b j)) =
        (ψ : Module.Dual ℂ V) (π q.out⁻¹ (∑ j, b.coord j (π q.out v) • b j)) := by
      simp only [map_sum, map_smul, smul_eq_mul]
    rw [this]
    simp only [Basis.coord_apply, Basis.sum_repr, rep_inv_apply_apply]
  simp only [hpt, integral_const, Complex.real_smul]

theorem formalDegree_eq (hπs : IsSmooth π) [π.IsIrreducible]
    (h1 : ∀ z ∈ Z, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ v, π z v = c • v) :
    formalDegree ν π = Module.finrank ℂ V / ν.real univ := by
  have hfd : FiniteDimensional ℂ V := finiteDimensional_of_compactSpace hπs fun z hz => by
    obtain ⟨c, -, hc⟩ := h1 z hz
    exact ⟨c, hc⟩
  have hπ : IsAdmissible π := isAdmissible_of_finiteDimensional hπs
  have hπ2 : IsSquareIntegrable Z ν π := isSquareIntegrable_of_compactSpace hπs h1
  obtain ⟨v₀, ψ₀, h₀⟩ := exists_dual_apply_eq_one hπs
  have hsum := sum_pairing_basis hπ2 hπs v₀ ψ₀
  set b := Module.finBasis ℂ V
  let c : Fin (Module.finrank ℂ V) → smoothVectors (Representation.dual π) := fun j =>
    ⟨b.coord j, mem_smoothVectors_dual_of_finiteDimensional hπs _⟩
  have hterm : ∀ j, pairing Z ν π π v₀ (b.coord j) (b j) ψ₀ = (formalDegree ν π : ℂ)⁻¹ := by
    intro j
    have : pairing Z ν π π v₀ (b.coord j) (b j) ψ₀ = _ :=
      integral_eq_formalDegree hπ hπ2 v₀ (c j) (b j) ψ₀
    rw [this, h₀]
    simp [c, Basis.coord_apply, Basis.repr_self]
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, h₀,
    mul_one] at hsum
  have hd := formalDegree_pos (ν := ν) hπ hπ2
  have hvol : 0 < ν.real univ := by
    exact ENNReal.toReal_pos (isOpen_univ.measure_pos ν univ_nonempty).ne' (measure_ne_top ν univ)
  have hd' : (formalDegree ν π : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have key : (Module.finrank ℂ V : ℂ) = ν.real univ * formalDegree ν π := by
    rw [← hsum, mul_assoc, inv_mul_cancel₀ hd', mul_one]
  have key' : (Module.finrank ℂ V : ℝ) = ν.real univ * formalDegree ν π := by exact_mod_cast key
  rw [key', mul_div_cancel_left₀ _ hvol.ne']

open Classical in

theorem integral_character_mul_inv (hπs : IsSmooth π) (hσs : IsSmooth σ) [π.IsIrreducible]
    [σ.IsIrreducible] (h1 : ∀ z ∈ Z, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ v, π z v = c • v)
    (hc : SameCentralCharacter Z π σ) :
    ∫ q : G ⧸ Z, character π q.out * character σ q.out⁻¹ ∂ν =
      if Nonempty (π.Equiv σ) then (ν.real univ : ℂ) else 0 := by
  have := isInvInvariant_of_isMulRightInvariant Z ν
  obtain ⟨v₀, hv₀⟩ := exists_ne_zero_of_isIrreducible (ρ := π)
  have h1σ : ∀ z ∈ Z, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ w, σ z w = c • w := by
    intro z hz
    obtain ⟨c, hcπ, hcσ⟩ := hc z hz
    obtain ⟨c', hc'1, hc'⟩ := h1 z hz
    have : c = c' := by
      have h := (hcπ v₀).symm.trans (hc' v₀)
      have h2 : (c - c') • v₀ = 0 := by rw [sub_smul, h, sub_self]
      rcases smul_eq_zero.1 h2 with h3 | h3
      · exact sub_eq_zero.1 h3
      · exact absurd h3 hv₀
    exact ⟨c, this ▸ hc'1, hcσ⟩
  have : FiniteDimensional ℂ V := finiteDimensional_of_compactSpace hπs fun z hz => by
    obtain ⟨c, -, hc⟩ := h1 z hz
    exact ⟨c, hc⟩
  have : FiniteDimensional ℂ W := finiteDimensional_of_compactSpace hσs fun z hz => by
    obtain ⟨c, -, hc⟩ := h1σ z hz
    exact ⟨c, hc⟩
  have hπ : IsAdmissible π := isAdmissible_of_finiteDimensional hπs
  have hσ : IsAdmissible σ := isAdmissible_of_finiteDimensional hσs
  have hπ2 : IsSquareIntegrable Z ν π := isSquareIntegrable_of_compactSpace hπs h1
  have hσ2 : IsSquareIntegrable Z ν σ := isSquareIntegrable_of_compactSpace hσs h1σ
  set b := Module.finBasis ℂ V
  set b' := Module.finBasis ℂ W
  let c : Fin (Module.finrank ℂ V) → smoothVectors (Representation.dual π) := fun j =>
    ⟨b.coord j, mem_smoothVectors_dual_of_finiteDimensional hπs _⟩
  let c' : Fin (Module.finrank ℂ W) → smoothVectors (Representation.dual σ) := fun j =>
    ⟨b'.coord j, mem_smoothVectors_dual_of_finiteDimensional hσs _⟩
  split_ifs with hiso
  · obtain ⟨E⟩ := hiso
    have hself : ∫ q : G ⧸ Z, character π q.out * character π q.out⁻¹ ∂ν = ν.real univ := by
      have hexp : ∀ q : G ⧸ Z, character π q.out * character π q.out⁻¹ =
          ∑ i, ∑ j, coeffProd π π (b i) (b.coord i) (b j) (b.coord j) q.out := by
        intro q
        rw [character_eq_sum π b, character_eq_sum π b, Finset.sum_mul_sum]
        rfl
      have hI : ∀ i j, Integrable
          (fun q : G ⧸ Z => coeffProd π π (b i) (b.coord i) (b j) (b.coord j) q.out) ν :=
        fun i j => integrable_coeffProd hπ2 hπ2 (sameCentralCharacter_self hπ2) hπs hπs (b i) (c i)
          (b j) (c j)
      have hsplit : ∀ i, ∫ q : G ⧸ Z, ∑ j, coeffProd π π (b i) (b.coord i) (b j) (b.coord j) q.out ∂ν
          = ∑ j, ∫ q : G ⧸ Z, coeffProd π π (b i) (b.coord i) (b j) (b.coord j) q.out ∂ν :=
        fun i => integral_finsetSum _ fun j _ => hI i j
      simp only [hexp]
      rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hI i j]
      have hij : ∀ i j, ∫ q : G ⧸ Z, coeffProd π π (b i) (b.coord i) (b j) (b.coord j) q.out ∂ν =
          (formalDegree ν π : ℂ)⁻¹ * (if i = j then 1 else 0) := by
        intro i j
        have := integral_eq_formalDegree hπ hπ2 (b i) (c i) (b j) (c j)
        simp only [c, Basis.coord_apply, Basis.repr_self] at this
        rw [show (∫ q : G ⧸ Z, coeffProd π π (b i) (b.coord i) (b j) (b.coord j) q.out ∂ν) =
          ∫ q : G ⧸ Z, (b.coord i) (π q.out (b i)) * (b.coord j) (π q.out⁻¹ (b j)) ∂ν from rfl]
        simp only [Basis.coord_apply]
        rw [this]
        congr 1
        by_cases h : i = j
        · subst h
          simp
        · simp [h, Ne.symm h]
      simp only [hsplit, hij, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
        if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [formalDegree_eq (ν := ν) hπs h1]
      have hvol : 0 < ν.real univ := by
        exact ENNReal.toReal_pos (isOpen_univ.measure_pos ν univ_nonempty).ne'
          (measure_ne_top ν univ)
      have hn : (Module.finrank ℂ V : ℂ) ≠ 0 := by
        exact_mod_cast (Module.finrank_pos_iff_exists_ne_zero.2 ⟨v₀, hv₀⟩).ne'
      push_cast
      field_simp
    simpa only [character_eq_of_equiv E] using hself
  · have hne : IsEmpty (π.Equiv σ) := not_nonempty_iff.1 hiso
    have hexp : ∀ q : G ⧸ Z, character π q.out * character σ q.out⁻¹ =
        ∑ i, ∑ j, coeffProd π σ (b i) (b.coord i) (b' j) (b'.coord j) q.out := by
      intro q
      rw [character_eq_sum π b, character_eq_sum σ b', Finset.sum_mul_sum]
      rfl
    have hI : ∀ i j, Integrable
        (fun q : G ⧸ Z => coeffProd π σ (b i) (b.coord i) (b' j) (b'.coord j) q.out) ν :=
      fun i j => integrable_coeffProd hπ2 hσ2 hc hπs hσs (b i) (c i) (b' j) (c' j)
    simp only [hexp]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hI i j]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => hI i j]
    exact Finset.sum_eq_zero fun j _ =>
      integral_eq_zero_of_isEmpty_equiv hπ hσ hπ2 hσ2 hc hne (b i) (c i) (b' j) (c' j)

end Orthogonality

end SchurOrthogonality

end GroundTheory.Automorphic
