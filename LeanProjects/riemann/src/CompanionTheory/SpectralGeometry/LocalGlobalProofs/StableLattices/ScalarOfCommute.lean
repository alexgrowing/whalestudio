import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.SimpleDistinctness.ScalarCharacterOfL2Embedding
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.HarishChandraModulesIndefiniteUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFiniteModuleIrreducibleOfIrreducibleUnitaryRep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactTypeInCompactStableSubmodule
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFiniteIdem
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

noncomputable section

open Polynomial

namespace GlobalTheory.CompanionTheory.RgStart

open Formalism.REAL (GlRel KHighest IsWeight qdet)
open CompanionTheory.D.LK (IsKMod)
open CompanionTheory.RgExh

theorem monic_eval_capP : ∀ (n : ℕ) (p : ℂ[X]), p.Monic → p.natDegree = n →
    ∃ χ : Fin n → ℂ, ∀ Y : ℂ, p.eval Y = Formalism.QuantumDeterminants.capP χ Y
  | 0, p, hm, hd => ⟨Fin.elim0, fun Y => by
      rw [eq_one_of_monic_natDegree_zero hm hd]
      simp [Formalism.QuantumDeterminants.capP]⟩
  | n + 1, p, hm, hd => by
      have hdeg : p.degree ≠ 0 := by
        rw [degree_eq_natDegree hm.ne_zero, hd]
        exact_mod_cast Nat.succ_ne_zero n
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_root p hdeg
      have hq : (X - C z) * (p /ₘ (X - C z)) = p := mul_divByMonic_eq_iff_isRoot.2 hz
      have hqm : (p /ₘ (X - C z)).Monic := (monic_X_sub_C z).of_mul_monic_left (hq.symm ▸ hm)
      have hqd : (p /ₘ (X - C z)).natDegree = n := by
        have := (monic_X_sub_C z).natDegree_mul hqm
        rw [hq, hd, natDegree_X_sub_C] at this
        omega
      obtain ⟨χ, hχ⟩ := monic_eval_capP n _ hqm hqd
      refine ⟨Fin.cons (-z) χ, fun Y => ?_⟩
      rw [← hq, eval_mul, hχ]
      simp [Formalism.QuantumDeterminants.capP, Fin.prod_univ_succ, sub_eq_add_neg]

theorem exists_char {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (h : ∀ u, ∃ c : ℂ, qdet E u = c • (1 : Module.End ℂ V)) :
    ∃ χ : Fin n → ℂ, ∀ Y : ℂ,
      qdet E (Y + ((n : ℂ) - 1) / 2) = Formalism.QuantumDeterminants.capP χ Y • (1 : Module.End ℂ V) := by
  obtain ⟨c, h1, h2, h3, -⟩ := GlobalTheory.CentreFin.exists_coef E (-(((n : ℂ) - 1) / 2))
    (B := (⊥ : Subalgebra ℂ (Module.End ℂ V))) (fun u => by
      obtain ⟨c, hc⟩ := h u
      exact Algebra.mem_bot.2 ⟨c, by rw [hc, Algebra.algebraMap_eq_smul_one]⟩)
  have hd : ∀ j, ∃ d : ℂ, j ≤ n → c j = d • (1 : Module.End ℂ V) := fun j => by
    by_cases hj : j ≤ n
    · obtain ⟨d, hd⟩ := Algebra.mem_bot.1 (h2 j hj)
      exact ⟨d, fun _ => by rw [← hd, Algebra.algebraMap_eq_smul_one]⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose d hd using hd
  let q : ℂ[X] := ∑ j ∈ Finset.range n, C (d j) * X ^ j
  have hq : q.degree < n := by
    rw [degree_lt_iff_coeff_zero]
    intro m hm
    simp only [q, finset_sum_coeff, coeff_C_mul, coeff_X_pow]
    refine Finset.sum_eq_zero fun j hj => ?_
    have : m ≠ j := by have := Finset.mem_range.1 hj; omega
    simp [this]
  have hdg : (X ^ n + q).degree = (n : WithBot ℕ) := by
    rw [degree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), degree_X_pow]
  obtain ⟨χ, hχ⟩ := monic_eval_capP n (X ^ n + q) (monic_X_pow_add hq)
    (natDegree_eq_of_degree_eq_some hdg)
  refine ⟨χ, fun Y => ?_⟩
  have e := h3 Y
  rw [sub_neg_eq_add] at e
  have e2 : ∀ j ∈ Finset.range n, Y ^ j • c j = (d j * Y ^ j) • (1 : Module.End ℂ V) := fun j hj => by
    rw [hd j (Finset.mem_range.1 hj).le, smul_smul, mul_comm]
  rw [e, Finset.sum_range_succ, h1, Finset.sum_congr rfl e2, ← hχ]
  simp only [q, eval_add, eval_pow, eval_X, eval_finset_sum, eval_mul, eval_C, add_smul, Finset.sum_smul]
  rw [add_comm]

section Rep

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

theorem exists_emb (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ) (hK : IsKMod ε σ D E) :
    ∃ ι : D →ₗ[ℂ] ReciprocityTheory.ChartRestriction.DS.smD ε σ, Function.Injective ι ∧
      (∀ x, ι x ∈ CompanionTheory.D.gk.HC.KF ε σ) ∧
      ∀ a b x, ReciprocityTheory.ChartRestriction.DS.smE ε σ a b (ι x) = ι (E a b x) := by
  have hle : D ≤ ReciprocityTheory.ChartRestriction.DS.smD ε σ := fun v hv =>
    (CompanionTheory.D.gk.HC.K_finite_smooth_vectors n ε H σ hσ hirr).1 v ((hK.mem v).1 hv)
  exact ⟨Submodule.inclusion hle, Submodule.inclusion_injective hle, fun x => (hK.mem x).1 x.2,
    fun a b x => Subtype.ext (GlobalTheory.KFinIrr.smE_eq hσ hK x (hle x.2) a b)⟩

theorem exists_kType [Nontrivial H] (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) :
    ∃ (μ : Fin n → ℝ) (S : Submodule ℂ H), Formalism.MainNotions.S.IsKTypeOf ε σ μ S := by
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  obtain ⟨v, hkv, hv⟩ := (GlobalTheory.HcPort.kfinDense_UJC hσ).exists_mem_open Metric.isOpen_ball
    ⟨x, Metric.mem_ball_self hpos⟩
  have hv0 : v ≠ 0 := by
    rintro rfl
    simp [Metric.mem_ball, dist_eq_norm] at hv
  obtain ⟨S, hS, hvS, hst⟩ := hkv
  have hSb : S ≠ ⊥ := fun h => hv0 (by simpa [h] using hvS)
  obtain ⟨μ, S', -, hS'⟩ := GlobalTheory.KTypeExists.exists_kType n ε H σ hσ S hS hst hSb
  exact ⟨μ, S', hS'⟩

theorem scalar_of_commute [Nontrivial H] (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ) (hK : IsKMod ε σ D E)
    (T : Module.End ℂ D) (hT : ∀ a b, T * E a b = E a b * T) :
    ∃ c : ℂ, T = c • (1 : Module.End ℂ D) := by
  have hTa : ∀ a b x, T (E a b x) = E a b (T x) := fun a b x => LinearMap.congr_fun (hT a b) x
  obtain ⟨μ, S₀, hS₀⟩ := exists_kType hσ
  obtain ⟨v, hv0, -, hv⟩ := hK.hw μ S₀ hS₀
  obtain ⟨ι, hι, hKF, hc⟩ := exists_emb hσ hirr hK
  let P : Submodule ℂ (ReciprocityTheory.ChartRestriction.DS.smD ε σ) := Submodule.span ℂ
    {w | w ∈ CompanionTheory.D.gk.HC.KF ε σ ∧ ReciprocityTheory.ChartRestriction.DS.IsKHWVec ε (ReciprocityTheory.ChartRestriction.DS.smE ε σ) μ w}
  haveI hP : FiniteDimensional ℂ P := CompanionTheory.D.gk.HC.uAdm n ε H σ hσ hirr μ
  let S : Submodule ℂ D := Submodule.span ℂ {x | KHighest ε E μ x}
  have hSP : ∀ x ∈ S, ι x ∈ P := fun x hx => by
    have : S ≤ P.comap ι := Submodule.span_le.2 fun y hy => Submodule.subset_span
      ⟨hKF y, fun a => by rw [hc, hy.1 a, map_smul],
        fun a b hab he => by rw [hc, hy.2 a b hab he, map_zero]⟩
    exact this hx
  haveI : FiniteDimensional ℂ S :=
    FiniteDimensional.of_injective (ι.restrict hSP) fun x y h =>
      Subtype.ext (hι (congrArg Subtype.val h))
  have hTS : ∀ x ∈ S, T x ∈ S := fun x hx => by
    have : S ≤ S.comap T := Submodule.span_le.2 fun y hy => Submodule.subset_span
      ⟨fun a => by rw [← hTa, hy.1 a, map_smul],
        fun a b hab he => by rw [← hTa, hy.2 a b hab he, map_zero]⟩
    exact this hx
  haveI : Nontrivial S := Submodule.nontrivial_iff_ne_bot.2 fun h => hv0 (by
    have : v ∈ S := Submodule.subset_span hv
    simpa [h] using this)
  obtain ⟨c, hcE⟩ := Module.End.exists_eigenvalue (T.restrict hTS)
  obtain ⟨w, hw⟩ := hcE.exists_hasEigenvector
  have hwe : T (w : D) = c • (w : D) := congrArg Subtype.val hw.apply_eq_smul
  have hw0 : (w : D) ≠ 0 := fun h => hw.2 (Subtype.ext h)
  let N : Submodule ℂ D := LinearMap.ker (T - c • (1 : Module.End ℂ D))
  have hN : ∀ x, x ∈ N ↔ T x = c • x := fun x => by
    simp [N, sub_eq_zero]
  rcases GlobalTheory.KFinIrr.kMod_irred n ε H σ D E inferInstance hσ hirr hK N (fun a b x hx => by
      rw [hN] at hx ⊢
      rw [hTa, hx, map_smul]) with h | h
  · exact absurd (by simpa [h] using (hN w).2 hwe) hw0
  · refine ⟨c, LinearMap.ext fun x => ?_⟩
    have : x ∈ N := h ▸ Submodule.mem_top
    simpa using (hN x).1 this

theorem intWt (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ) (hK : IsKMod ε σ D E) :
    IntWt ⟨D, E, hK.gl⟩ := by
  intro μ x hx0 hx a
  obtain ⟨ι, hι, hKF, hc⟩ := exists_emb hσ hirr hK
  by_contra hno
  have hne : ∀ m : ℤ, (m : ℂ) ≠ (μ a : ℂ) := fun m hm => hno ⟨m, by exact_mod_cast hm.symm⟩
  let T : Module.End ℂ (ReciprocityTheory.ChartRestriction.DS.smD ε σ) := ReciprocityTheory.ChartRestriction.DS.smE ε σ a a
  have h1 : ι x ∈ T.eigenspace (μ a : ℂ) := by
    rw [Module.End.mem_eigenspace_iff]
    change ReciprocityTheory.ChartRestriction.DS.smE ε σ a a (ι x) = _
    rw [hc]
    have : E a a x = (μ a : ℂ) • x := hx a
    rw [this, map_smul]
  have h2 : ι x ∈ ⨆ j, ⨆ (_ : j ≠ (μ a : ℂ)), T.eigenspace j := by
    have hle : Submodule.span ℂ {w : ReciprocityTheory.ChartRestriction.DS.smD ε σ | w ∈ CompanionTheory.D.gk.HC.KF ε σ ∧
        ∃ ν : Fin n → ℤ, ∀ b, ReciprocityTheory.ChartRestriction.DS.smE ε σ b b w = (ν b : ℂ) • w} ≤
        ⨆ j, ⨆ (_ : j ≠ (μ a : ℂ)), T.eigenspace j := by
      refine Submodule.span_le.2 ?_
      rintro w ⟨-, ν, hν⟩
      have hw : w ∈ T.eigenspace (ν a : ℂ) := by
        rw [Module.End.mem_eigenspace_iff]
        exact hν a
      exact (le_iSup₂_of_le (f := fun j (_ : j ≠ (μ a : ℂ)) => T.eigenspace j) (ν a : ℂ) (hne _) le_rfl) hw
    exact hle (CompanionTheory.D.gk.HC.integral_weights n ε H σ hσ hirr _ (hKF x))
  have hz : ι x = 0 := by
    have := (Module.End.eigenspaces_iSupIndep T (μ a : ℂ))
    exact (Submodule.disjoint_def.1 this) _ h1 h2
  exact hx0 (hι (by rw [hz, map_zero]))

end Rep

theorem startMod : CompanionTheory.RgExh.Fin.StartMod := by
  intro n ε H _ _ _ σ hσ hirr hH D E hK
  obtain ⟨μ, S₀, hS₀⟩ := exists_kType hσ
  obtain ⟨v, hv0, -, -⟩ := hK.hw μ S₀ hS₀
  haveI : Nontrivial D := ⟨⟨v, 0, hv0⟩⟩
  refine ⟨⟨inferInstanceAs (Nontrivial D), GlobalTheory.KFinIrr.kMod_irred n ε H σ D E inferInstance hσ hirr hK⟩, ?_,
    intWt hσ hirr hK⟩
  exact exists_char E fun u => scalar_of_commute hσ hirr hK _ fun a b =>
    Formalism.REAL.qDetCentral _ n E hK.gl u a b

end GlobalTheory.CompanionTheory.RgStart
