import Development.WeilBound.ThetaLifts.EigenvalueEndgame.CuspidalAverages.KeyThree
import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.PsiUnrOfNotLe
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDictAd
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.LmOfLinBar
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDictSec

noncomputable section

set_option linter.style.haveILetI false

namespace PositivityTheory.ThKEnd.Cusp

open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.KCo Matrix
open PositivityTheory.Mix (psiUnr_of_not_le)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section

variable {κ : Type} [Fintype κ] {v : Pl F}

def vacW (v : Pl F) : Submodule (v.adicCompletionIntegers F) ((κ → Fv F v) × (κ → Fv F v)) where
  carrier := {y | (∀ i, y.1 i ∈ v.adicCompletionIntegers F) ∧ ∀ i, y.2 i ∈ v.adicCompletionIntegers F}
  add_mem' ha hb := ⟨fun i => add_mem (ha.1 i) (hb.1 i), fun i => add_mem (ha.2 i) (hb.2 i)⟩
  zero_mem' := ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩
  smul_mem' c _ h := ⟨fun i => mul_mem c.2 (h.1 i), fun i => mul_mem c.2 (h.2 i)⟩

theorem vac_locW (z : (κ → AF F) × (κ → AF F)) : ∀ᶠ v in cofinite, locW v z ∈ vacW v :=
  (eventually_all.2 fun i => (z.1 i).2.2).and (eventually_all.2 fun i => (z.2 i).2.2)

theorem vac_schr {ψ : AddChar (AF F) ℂ} (hψ : PsiUnr ψ v) (h2 : (2 : Fv F v)⁻¹ ∈ v.adicCompletionIntegers F) {y} (hy : y ∈ vacW (κ := κ) v) :
    schr (psiV ψ v) y (Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) =
      Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
  funext x
  by_cases hx : ∀ i, x i ∈ v.adicCompletionIntegers F
  · have h : psiV ψ v (x ⬝ᵥ y.2 + ⅟(2 : Fv F v) * (y.1 ⬝ᵥ y.2)) = 1 := by
      have := (hψ _).2 (show x ⬝ᵥ y.2 + ⅟(2 : Fv F v) * (y.1 ⬝ᵥ y.2) ∈ v.adicCompletionIntegers F from
        add_mem (sum_mem fun i _ => mul_mem (hx i) (hy.2 i))
          (mul_mem (by rwa [invOf_eq_inv]) (sum_mem fun i _ => mul_mem (hy.1 i) (hy.2 i)))) 1 (one_mem _)
      rwa [mul_one] at this
    rw [schr, h, one_mul, Set.indicator_of_mem (show x ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hx),
      Set.indicator_of_mem (show x + y.1 ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from
        fun i => add_mem (hx i) (hy.1 i))]
    rfl
  · rw [schr, Set.indicator_of_notMem (show x ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hx),
      Set.indicator_of_notMem (show x + y.1 ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from fun h => hx fun i => by
        simpa using sub_mem (h i) (hy.1 i)), mul_zero]

theorem vac_eq {ψ : AddChar (AF F) ℂ} (hψ : PsiUnr ψ v) {Φ : (κ → Fv F v) → ℂ} (h : ∀ y ∈ vacW v, schr (psiV ψ v) y Φ = Φ) :
    Φ = Φ 0 • Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
  classical
  funext x
  by_cases hx : ∀ i, x i ∈ v.adicCompletionIntegers F
  · have := congrFun (h (x, 0) ⟨hx, fun _ => zero_mem _⟩) 0
    rw [Pi.smul_apply, Set.indicator_of_mem (show x ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hx)]
    simpa [schr] using this
  · rw [Pi.smul_apply, Set.indicator_of_notMem (show x ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hx), smul_zero]
    obtain ⟨i, hi⟩ := not_forall.1 hx
    obtain ⟨y, hy, hne⟩ : ∃ y ∈ v.adicCompletionIntegers F, psiLoc ψ v (x i * y) ≠ 1 := by
      by_contra hc
      push Not at hc
      exact hi ((hψ _).1 hc)
    have := congrFun (h (0, Pi.single i y) ⟨fun _ => zero_mem _, fun j => by
      by_cases e : j = i
      · subst e; simpa using hy
      · simp [Pi.single_eq_of_ne e]⟩) x
    simp only [schr, dotProduct_single, Pi.zero_apply, zero_mul, mul_zero, add_zero] at this
    exact (mul_left_eq_self₀.1 this).resolve_left hne

end

theorem vac_int_F (x : F) : ∀ᶠ v : Pl F in cofinite, algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F := by
  have h : ∀ᶠ v : Pl F in cofinite, evFin F v (algebraMap F (AF F) x) ∈ v.adicCompletionIntegers F := (algebraMap F (AF F) x).2.2
  filter_upwards [h] with v hv
  rwa [AlgHom.commutes] at hv

theorem vac_int_Z {E K : Type} [Field E] [Field K] (O : ValuationSubring K) (t : E →+* K) {x : E} (h : IsIntegral ℤ x) : t x ∈ O := by
  have h1 : IsIntegral ℤ (t x) := h.map t.toIntAlgHom
  have h2 : IsIntegral O (t x) := h1.tower_top
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := O) (K := K)).1 h2
  rw [← hy]
  exact y.2

theorem vac_int_E (x : E) : ∀ᶠ v : Pl F in cofinite, ∀ t : E →ₐ[F] Fv F v, t x ∈ v.adicCompletionIntegers F := by
  have ha : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨N, hN, hi⟩ := ha.exists_integral_multiple
  filter_upwards [vac_int_F (F := F) (N : F)⁻¹] with v hv t
  have h1 : t (N • x) ∈ v.adicCompletionIntegers F := vac_int_Z _ (t : E →+* Fv F v) hi
  have e : t x = algebraMap F (Fv F v) (N : F)⁻¹ * t (N • x) := by
    rw [← t.commutes, ← map_mul, zsmul_eq_mul, map_inv₀, map_intCast, inv_mul_cancel_left₀ (Int.cast_ne_zero.2 hN)]
  rw [e]
  exact mul_mem hv h1

theorem vac_val {v : Pl F} (y : Fv F v) : ValuativeRel.valuation (Fv F v) y ≤ 1 ↔ y ∈ v.adicCompletionIntegers F := by
  haveI : (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  rw [(ValuativeRel.isEquiv (ValuativeRel.valuation (Fv F v))
    (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ)))).le_one_iff_le_one]
  exact Iff.rfl

theorem vac_one {n d : ℕ} {v : Pl F} (Y : Matrix (Fin n) (Fin d) (Fv F v)) :
    Set.indicator {x : Fin n × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} (1 : (Fin n × Fin d → Fv F v) → ℂ) (ofM Y) =
      oneO (Fv F v) n d Y := by
  by_cases hY : ∀ a b, ValuativeRel.valuation (Fv F v) (Y a b) ≤ 1
  · exact (Set.indicator_of_mem (show ofM Y ∈ {x : Fin n × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from
      fun p => (vac_val _).1 (hY p.1 p.2)) _).trans (Set.indicator_of_mem
        (show Y ∈ {Y : Matrix (Fin n) (Fin d) (Fv F v) | ∀ a b, ValuativeRel.valuation (Fv F v) (Y a b) ≤ 1} from hY)
        (1 : Matrix (Fin n) (Fin d) (Fv F v) → ℂ)).symm
  · exact (Set.indicator_of_notMem (show ofM Y ∉ {x : Fin n × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from
      fun e => hY fun a b => (vac_val _).2 (e (a, b))) _).trans (Set.indicator_of_notMem
        (show Y ∉ {Y : Matrix (Fin n) (Fin d) (Fv F v) | ∀ a b, ValuativeRel.valuation (Fv F v) (Y a b) ≤ 1} from hY)
        (1 : Matrix (Fin n) (Fin d) (Fv F v) → ℂ)).symm

theorem vac_sum {κ ι : Type} [Fintype κ] [Fintype ι] {v : Pl F} (c : ι → Fv F v) (z : ι → (κ → AF F) × (κ → AF F))
    (hc : ∀ i, c i ∈ v.adicCompletionIntegers F) (hz : ∀ i, locW v (z i) ∈ vacW v) : locW v (∑ i, sgl v (c i) • z i) ∈ vacW v := by
  refine Finset.sum_induction _ (fun t => locW v t ∈ vacW v) (fun a b ha hb => locW_add a b ▸ add_mem ha hb) ?_ fun i _ => ?_
  · have h0 : evFin F v 0 ∈ v.adicCompletionIntegers F := by rw [map_zero]; exact zero_mem _
    exact ⟨fun _ => h0, fun _ => h0⟩
  · rw [locW_smul, ev_sgl]
    exact ⟨fun j => mul_mem (hc i) ((hz i).1 j), fun j => mul_mem (hc i) ((hz i).2 j)⟩

theorem vacBar : VacBar := by
  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB hX hW hM
  classical
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have dX : IsUnit X.J.det :=
    GlobalTheory.CompanionTheory.Ar.RT.isUnit_det_of_cartan (F := F) X.J (B.emb w).1 1 (X.θ w) (by rw [one_smul]; exact hX.cartan w)
  have dW : IsUnit W.J.det := GlobalTheory.CompanionTheory.Ar.RT.isUnit_det_of_cartan (F := F) W.J (B.emb w).1 Complex.I (W.θ w) (hW.cartan w)
  obtain ⟨δ, hδ⟩ : ∃ δ : E, δ - σ δ ≠ 0 := by
    by_contra e
    push Not at e
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    haveI := hB.cm.2.1
    refine IsTotallyComplex.complexEmbedding_not_isReal τ (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => ?_))
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact (hB.cm.2.2.2 τ x).symm.trans (congrArg τ (sub_eq_zero.1 (e x)).symm)
  have hd : ∀ᶠ v : Pl F in cofinite, ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal :=
    (Ideal.finite_factors differentIdeal_ne_bot).subset fun v hv => Ideal.dvd_iff_le.2 (not_not.1 hv)
  let U : E → Fin n × Fin d → Matrix (Fin n) (Fin d) (AE F E) := fun x p => single p.1 p.2 (inclR (F := F) (AF F) x)
  filter_upwards [hd, vac_int_F (F := F) 2⁻¹, hM.std, vac_int_E (F := F) δ, vac_int_E (F := F) (δ - σ δ)⁻¹,
    eventually_all.2 fun i => eventually_all.2 fun j => vac_int_E (F := F) (X.J⁻¹ i j),
    eventually_all.2 fun i => eventually_all.2 fun j => vac_int_E (F := F) (W.J⁻¹ i j),
    eventually_all.2 fun p => vac_locW (M.co.e (U 1 p)), eventually_all.2 fun p => vac_locW (M.co.e (U δ p))]
    with v e1 e2 e3 e4 e5 e6 e7 e8 e9 t ι hι
  obtain ⟨⟨sec, h⟩, -⟩ := section_statement F E σ hB.cm v t
  have uu : ∀ {m : ℕ} {J : Matrix (Fin m) (Fin m) E}, IsUnit J.det → IsUnit ((incM F J).map (piW t)) := fun {m J} hJ => by
    rw [incM_map h]
    exact ((Matrix.isUnit_iff_isUnit_det J).2 hJ).map (t : E →+* Fv F v).mapMatrix
  have hG : Grams σ t (incM F X.J) (incM F W.J) := by
    refine ⟨uu dX, uu dW, 1, one_mul _, Matrix.ext fun i j => ?_, Matrix.ext fun i j => ?_⟩
    · rw [incM_map' h, incM_map h, one_smul, hX.herm]; rfl
    · rw [incM_map' h, incM_map h, neg_smul, one_smul, hW.skew, map_neg]; rfl
  have lm := lm_of_linBar adjoint_statement hB.std h hG hι
  have hu : PsiUnr B.ψ v := psiUnr_of_not_le hB.std v e1
  rw [map_inv₀, map_ofNat] at e2
  have key : ∀ P Q : Matrix (Fin n) (Fin d) (Fv F v), (∀ i j, P i j ∈ v.adicCompletionIntegers F) →
      (∀ i j, Q i j ∈ v.adicCompletionIntegers F) →
      ∃ u, u.map (piW t) = P ∧ u.map (piW (t.comp σ)) = Q ∧ locW v (M.co.e u) ∈ vacW v := fun P Q hP hQ => by
    let b : Fin n × Fin d → Fv F v := fun p => (P p.1 p.2 - Q p.1 p.2) * t (δ - σ δ)⁻¹
    let a : Fin n × Fin d → Fv F v := fun p => P p.1 p.2 - b p * t δ
    have hb : ∀ p, b p ∈ v.adicCompletionIntegers F := fun p => mul_mem (sub_mem (hP _ _) (hQ _ _)) (e5 t)
    have ha : ∀ p, a p ∈ v.adicCompletionIntegers F := fun p => sub_mem (hP _ _) (mul_mem (hb p) (e4 t))
    have hu : ∀ i j, (∑ p, sgl v (a p) • U 1 p + ∑ p, sgl v (b p) • U δ p) i j =
        sgl v (a (i, j)) • inclR (F := F) (AF F) (1 : E) + sgl v (b (i, j)) • inclR (F := F) (AF F) δ := fun i j => by
      have k : ∀ (c : Fin n × Fin d → AF F) (x : E), (∑ p, c p • U x p) i j = c (i, j) • inclR (F := F) (AF F) x := fun c x => by
        rw [Matrix.sum_apply, Finset.sum_eq_single (i, j)]
        · simp [U]
        · rintro ⟨i', j'⟩ _ hne
          have : U x (i', j') i j = 0 := single_apply_of_ne _ _ _ _ _ fun e => hne (Prod.ext e.1 e.2)
          rw [Matrix.smul_apply, this, smul_zero]
        · simp
      rw [Matrix.add_apply, k, k]
    have ht : t δ - t (σ δ) ≠ 0 := by rw [← map_sub]; exact (map_ne_zero t).2 hδ
    refine ⟨∑ p, sgl v (a p) • U 1 p + ∑ p, sgl v (b p) • U δ p, Matrix.ext fun i j => ?_, Matrix.ext fun i j => ?_, ?_⟩
    · rw [map_apply, hu, map_add, (h.smul _ _).1, (h.smul _ _).1, (h.inc _).1, (h.inc _).1, ev_sgl, ev_sgl, map_one]
      simp only [a]
      ring
    · rw [map_apply, hu, map_add, (h.smul _ _).2, (h.smul _ _).2, (h.inc _).2, (h.inc _).2, ev_sgl, ev_sgl, map_one, map_one]
      simp only [a, b, map_inv₀, map_sub]
      field_simp
      ring
    · rw [map_add, locW_add, map_sum, map_sum]
      simp only [map_smul]
      exact add_mem (vac_sum _ _ ha e8) (vac_sum _ _ hb e9)
  have hfix := vac_eq hu (Φ := (LinearMap.funLeft ℂ ℂ (ofH (Fv F v) (Fin n) (Fin d)).symm ∘ₗ ι) (M.vac v)) fun y hy => by
    obtain ⟨u, h1, h2, h3⟩ := key (-toM y.2) (-((X.J⁻¹).map t * toM y.1 * ((W.J⁻¹).map t)ᵀ)) (fun i j => neg_mem (hy.2 (i, j)))
      fun i j => neg_mem (sum_mem fun a _ => mul_mem (sum_mem fun b _ => mul_mem (e6 _ _ t) (hy.1 (b, a))) (e7 _ _ t))
    have iX : X.J.map t * (X.J⁻¹).map t = 1 := by
      rw [← Matrix.map_mul (f := t), mul_nonsing_inv _ dX, Matrix.map_one _ (map_zero _) (map_one _)]
    have iW : W.J.map t * (W.J⁻¹).map t = 1 := by
      rw [← Matrix.map_mul (f := t), mul_nonsing_inv _ dW, Matrix.map_one _ (map_zero _) (map_one _)]
    have hc : coord σ t (incM F X.J) (incM F W.J) u = y := by
      rw [coord, h1, h2, incM_map h, incM_map h, Matrix.mul_neg, Matrix.neg_mul, neg_neg, neg_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        iX, Matrix.one_mul, Matrix.mul_assoc, ← transpose_mul, iW, transpose_one, Matrix.mul_one]
      rfl
    rw [← hc, ← lm.Heisenberg₂ u _ (hM.vac v).1, e3, vac_schr hu e2 h3]
  refine ⟨(LinearMap.funLeft ℂ ℂ (ofH (Fv F v) (Fin n) (Fin d)).symm ∘ₗ ι) (M.vac v) 0, funext fun Y => ?_⟩
  exact (congrFun hfix (ofM Y)).trans (congrArg
    (fun z : ℂ => (LinearMap.funLeft ℂ ℂ (ofH (Fv F v) (Fin n) (Fin d)).symm ∘ₗ ι) (M.vac v) 0 • z) (vac_one Y))

end PositivityTheory.ThKEnd.Cusp

end
