import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open Module IsLocalRing LinearMap Submodule

noncomputable section

namespace LengthDecomp

open Classical

variable {B : Type*} [CommRing B]

theorem length_localizedModule_eq_of_isLocalizedModule (p : Ideal B) [p.IsPrime]
    {X Y : Type*} [AddCommGroup X] [Module B X] [AddCommGroup Y] [Module B Y]
    [Module (Localization.AtPrime p) Y] [IsScalarTower B (Localization.AtPrime p) Y]
    (g : X →ₗ[B] Y) [IsLocalizedModule p.primeCompl g] :
    length (Localization.AtPrime p) (LocalizedModule p.primeCompl X) =
      length (Localization.AtPrime p) Y :=
  ((IsLocalizedModule.iso p.primeCompl g).extendScalarsOfIsLocalization p.primeCompl
    (Localization.AtPrime p)).length_eq

theorem length_localizedModule_quotient (n m : MaximalSpectrum B) :
    length (Localization.AtPrime n.asIdeal) (LocalizedModule n.asIdeal.primeCompl (B ⧸ m.asIdeal)) =
      if n = m then 1 else 0 := by
  have hn := n.isMaximal
  have hm := m.isMaximal
  split_ifs with h
  · subst h
    rw [length_localizedModule_eq_of_isLocalizedModule n.asIdeal
      (n.asIdeal.toLocalizedQuotient' (Localization.AtPrime n.asIdeal) n.asIdeal.primeCompl
        (Algebra.linearMap B (Localization.AtPrime n.asIdeal)))]
    have hmax : n.asIdeal.localized' (Localization.AtPrime n.asIdeal) n.asIdeal.primeCompl
        (Algebra.linearMap B (Localization.AtPrime n.asIdeal)) =
          maximalIdeal (Localization.AtPrime n.asIdeal) := by
      rw [Submodule.localized'_eq_span, ← Localization.AtPrime.map_eq_maximalIdeal]
      rfl
    rw [hmax]
    have : IsSimpleModule (Localization.AtPrime n.asIdeal)
        (Localization.AtPrime n.asIdeal ⧸ maximalIdeal (Localization.AtPrime n.asIdeal)) :=
      isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp inferInstance)
    exact Module.length_eq_one _ _
  · rw [Module.length_eq_zero_iff, LocalizedModule.subsingleton_iff]
    obtain ⟨s, hsm, hsn⟩ : ∃ s ∈ m.asIdeal, s ∉ n.asIdeal := by
      by_contra! hc
      exact h (MaximalSpectrum.ext (hm.eq_of_le hn.ne_top hc).symm)
    intro x
    refine ⟨s, hsn, ?_⟩
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr hsm,
      zero_mul]

variable {R : Type*} [CommRing R] [Algebra R B]
variable {N : Type*} [AddCommGroup N] [Module B N] [Module R N] [IsScalarTower R B N]

theorem step {p q : Submodule B N} (h : p ⋖ q) :
    ∃ m : MaximalSpectrum B, length R q = length R p + length R (B ⧸ m.asIdeal) ∧
      ∀ n : MaximalSpectrum B,
        length (Localization.AtPrime n.asIdeal) (LocalizedModule n.asIdeal.primeCompl q) =
          length (Localization.AtPrime n.asIdeal) (LocalizedModule n.asIdeal.primeCompl p) +
            if n = m then 1 else 0 := by
  let f : p →ₗ[B] q := inclusion h.le
  have key : IsSimpleModule B (q ⧸ range f) := by
    rwa [range_inclusion, ← covBy_iff_quot_is_simple h.le]
  obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp key
  let g : q →ₗ[B] B ⧸ m := e.toLinearMap.comp (range f).mkQ
  have hf : Function.Injective f := inclusion_injective _
  have hg : Function.Surjective g := e.surjective.comp (range f).mkQ_surjective
  have hfg : Function.Exact f g := exact_iff.mpr ((e.ker_comp _).trans (range f).ker_mkQ)
  refine ⟨⟨m, hm⟩, length_eq_add_of_exact (f.restrictScalars R) (g.restrictScalars R) hf hg hfg,
    fun n => ?_⟩
  rw [← length_localizedModule_quotient n ⟨m, hm⟩]
  exact length_eq_add_of_exact
    ((IsLocalizedModule.map n.asIdeal.primeCompl (LocalizedModule.mkLinearMap _ p)
      (LocalizedModule.mkLinearMap _ q) f).extendScalarsOfIsLocalization n.asIdeal.primeCompl
        (Localization.AtPrime n.asIdeal))
    ((IsLocalizedModule.map n.asIdeal.primeCompl (LocalizedModule.mkLinearMap _ q)
      (LocalizedModule.mkLinearMap _ (B ⧸ m)) g).extendScalarsOfIsLocalization
        n.asIdeal.primeCompl (Localization.AtPrime n.asIdeal))
    (IsLocalizedModule.map_injective _ _ _ f hf) (IsLocalizedModule.map_surjective _ _ _ g hg)
    (LocalizedModule.map_exact _ f g hfg)

theorem length_eq_sum [Fintype (MaximalSpectrum B)] (hN : IsFiniteLength B N) :
    length R N = ∑ n : MaximalSpectrum B,
      length (Localization.AtPrime n.asIdeal) (LocalizedModule n.asIdeal.primeCompl N) *
        length R (B ⧸ n.asIdeal) := by
  obtain ⟨s, hs_bot, hs_top⟩ := isFiniteLength_iff_exists_compositionSeries.mp hN
  have H : ∀ k, length R (s k) = ∑ n : MaximalSpectrum B,
      length (Localization.AtPrime n.asIdeal) (LocalizedModule n.asIdeal.primeCompl (s k)) *
        length R (B ⧸ n.asIdeal) := by
    intro k
    induction k using Fin.induction with
    | zero =>
      rw [← RelSeries.head, hs_bot]
      simp [Module.length_eq_zero]
    | succ i hi =>
      obtain ⟨m, h1, h2⟩ := step (R := R) (s.step i)
      rw [h1, hi]
      simp_rw [h2, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have := H (Fin.last _)
  rw [← RelSeries.last, hs_top] at this
  rw [← ((Submodule.topEquiv (R := B) (M := N)).restrictScalars R).length_eq, this]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [length_localizedModule_eq_of_isLocalizedModule n.asIdeal
    ((LocalizedModule.mkLinearMap n.asIdeal.primeCompl N).comp
      (Submodule.topEquiv (R := B) (M := N)).toLinearMap)]

theorem finite_maximalSpectrum [IsLocalRing R] [Module.Finite R B] :
    Finite (MaximalSpectrum B) := by
  have hfin := Algebra.QuasiFinite.finite_primesOver (R := R) (S := B) (maximalIdeal R)
  have := hfin.to_subtype
  refine Finite.of_injective (β := (maximalIdeal R).primesOver B)
    (fun n => ⟨n.asIdeal, n.isMaximal.isPrime, ⟨(IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) n.asIdeal)).symm⟩⟩) ?_
  intro n n' hnn'
  exact MaximalSpectrum.ext (congrArg Subtype.val hnn')

end LengthDecomp

theorem LengthDecomp.proof : LengthDecomp.Statement := by
  intro R B _ _ _ _ _ _ b hfin
  have := LengthDecomp.finite_maximalSpectrum (R := R) (B := B)
  let _ : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
  have hB : IsFiniteLength B (B ⧸ Ideal.span {b}) := by
    rw [length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian] at hfin
    rw [isFiniteLength_iff_isNoetherian_isArtinian]
    exact hfin.imp (isNoetherian_of_tower R) (isArtinian_of_tower R)
  rw [LengthDecomp.length_eq_sum (R := R) hB, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun n _ => ?_
  congr 1
  have hspan : (Ideal.span {b}).localized' (Localization.AtPrime n.asIdeal) n.asIdeal.primeCompl
      (Algebra.linearMap B (Localization.AtPrime n.asIdeal)) =
        Ideal.span {algebraMap B (Localization.AtPrime n.asIdeal) b} := by
    rw [Ideal.span, Submodule.localized'_span, Set.image_singleton]
    rfl
  rw [Ring.ord, LengthDecomp.length_localizedModule_eq_of_isLocalizedModule n.asIdeal
    ((Ideal.span {b}).toLocalizedQuotient' (Localization.AtPrime n.asIdeal) n.asIdeal.primeCompl
      (Algebra.linearMap B (Localization.AtPrime n.asIdeal))), hspan]

end

end GroundTheory.Heights₂.Heights.Vertical
