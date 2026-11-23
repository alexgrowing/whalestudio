import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocFacOfNeg
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactUnitaryIntegralPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import GroundTheory.GlobalFields.IdeleGroups.ClassGroup
import GroundTheory.GlobalFields.TateThesis.AdeleIdealMeasure
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

noncomputable section
namespace GlobalTheory.BumpOrbit
open GlobalTheory.RSTheta

section Local
variable {K : Type} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [ContinuousInv₀ K] [T2Space K]

theorem continuousAt_rowGL {a : ℕ} (ℓ : Fin a) :
    ContinuousAt (rowGL ℓ : (Fin a → K) → GL (Fin a) K) (Pi.single ℓ 1) := by
  have hO : {y : Fin a → K | y ℓ ≠ 0} ∈ nhds (Pi.single ℓ (1:K)) :=
    (isOpen_ne_fun (continuous_apply ℓ) continuous_const).mem_nhds (by simp)
  have hv : (fun y => rowMat ℓ y) =ᶠ[nhds (Pi.single ℓ (1:K))]
      fun y => ((rowGL ℓ y : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) :=
    Filter.eventually_of_mem hO fun y hy => (val_rowGL (isUnit_iff_ne_zero.2 hy)).symm
  have hc : Continuous fun y : Fin a → K => rowMat ℓ y := continuous_const.matrix_updateRow ℓ continuous_id
  have hinv : ContinuousAt (fun y : Fin a → K => (rowMat ℓ y)⁻¹) (Pi.single ℓ 1) := by
    refine ContinuousAt.comp (f := fun y => rowMat ℓ y) (g := Inv.inv) ?_ hc.continuousAt
    refine continuousAt_matrix_inv _ ?_
    rw [det_rowMat, Ring.inverse_eq_inv']
    simpa using continuousAt_inv₀ (one_ne_zero (α := K))
  have hv' : (fun y => MulOpposite.op (rowMat ℓ y)⁻¹) =ᶠ[nhds (Pi.single ℓ (1:K))]
      fun y => MulOpposite.op (((rowGL ℓ y)⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) :=
    hv.mono fun y hy => by simp only [Matrix.coe_units_inv, ← hy]
  rw [Units.isEmbedding_embedProduct.isInducing.continuousAt_iff]
  exact (hc.continuousAt.congr hv).prodMk ((MulOpposite.continuous_op.continuousAt.comp hinv).congr hv')

end Local

theorem exists_exp_lt {c : WithZero (Multiplicative ℤ)} (hc : c ≠ 0) :
    ∃ N : ℕ, WithZero.exp (-(N:ℤ)) < c := by
  obtain ⟨k, rfl⟩ : ∃ k, c = WithZero.exp k := ⟨_, (WithZero.exp_log hc).symm⟩
  refine ⟨(-k + 1).toNat, ?_⟩
  rw [WithZero.exp_lt_exp]
  omega

variable {E : Type} [Field E] [NumberField E]

theorem exists_nat_of_mem_nhds {a : ℕ} (ℓ : Fin a) (w : HeightOneSpectrum (𝓞 E))
    {V : Set (Fin a → w.adicCompletion E)} (hV : V ∈ nhds (Pi.single ℓ 1)) :
    ∃ N : ℕ, ∀ y : Fin a → w.adicCompletion E,
      (∀ j, Valued.v (y j - (Pi.single ℓ 1 : Fin a → w.adicCompletion E) j) ≤ WithZero.exp (-(N:ℤ))) → y ∈ V := by
  rw [nhds_pi, Filter.mem_pi] at hV
  obtain ⟨I, -, t, ht, hsub⟩ := hV
  have h1 : ∀ j, ∃ N : ℕ, ∀ z : w.adicCompletion E,
      Valued.v (z - (Pi.single ℓ 1 : Fin a → w.adicCompletion E) j) ≤ WithZero.exp (-(N:ℤ)) → z ∈ t j := by
    intro j
    obtain ⟨γ, hγ⟩ := Valued.mem_nhds.1 (ht j)
    have hc : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ (0 : WithZero (Multiplicative ℤ)) := by simp
    obtain ⟨N, hN⟩ := exists_exp_lt hc
    refine ⟨N, fun z hz => hγ ?_⟩
    simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
    exact lt_of_le_of_lt hz hN
  choose N hN using h1
  refine ⟨Finset.univ.sup N, fun y hy => hsub fun j _ => hN j _ ((hy j).trans ?_)⟩
  rw [WithZero.exp_le_exp, neg_le_neg_iff, Nat.cast_le]
  exact Finset.le_sup (Finset.mem_univ j)

variable {E : Type} [Field E] [NumberField E]

theorem map_list_prod_locGL {a : ℕ} (g : ∀ w : HeightOneSpectrum (𝓞 E), GL (Fin a) (w.adicCompletion E))
    (l : List (HeightOneSpectrum (𝓞 E))) (hl : l.Nodup) (w : HeightOneSpectrum (𝓞 E)) :
    GeneralLinearGroup.map (pLoc E w) (l.map fun v => locGL E a v (g v)).prod = if w ∈ l then g w else 1 := by
  induction l with
  | nil => simp
  | cons v l ih =>
    rw [List.map_cons, List.prod_cons, map_mul, ih (List.nodup_cons.1 hl).2]
    by_cases h : w = v
    · subst h
      rw [pLoc_locGL, if_neg (List.nodup_cons.1 hl).1, if_pos List.mem_cons_self, mul_one]
    · rw [pLoc_locGL_of_ne h, one_mul]
      simp [h]

theorem pLoc_single {a : ℕ} (ℓ j : Fin a) (w : HeightOneSpectrum (𝓞 E)) :
    pLoc E w ((Pi.single ℓ 1 : Fin a → Af E) j) = (Pi.single ℓ 1 : Fin a → w.adicCompletion E) j := by
  by_cases h : j = ℓ
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem exists_nat_rowGL_mem {a : ℕ} (ℓ : Fin a) {U : Subgroup (GL (Fin a) (Af E))}
    (hU : IsOpen (U : Set (GL (Fin a) (Af E)))) (w : HeightOneSpectrum (𝓞 E)) :
    ∃ N : ℕ, ∀ y : Fin a → w.adicCompletion E,
      (∀ j, Valued.v (y j - (Pi.single ℓ 1 : Fin a → w.adicCompletion E) j) ≤ WithZero.exp (-(N:ℤ))) →
      locGL E a w (rowGL ℓ y) ∈ U ∧ rowGL ℓ y ∈ KGL w a := by
  apply exists_nat_of_mem_nhds
  have ho : IsOpen ((locGL E a w) ⁻¹' (U : Set (GL (Fin a) (Af E))) ∩
      (KGL w a : Set (GL (Fin a) (w.adicCompletion E)))) :=
    (hU.preimage (GlobalTheory.CuspRep.CuspSub.continuous_locGL w)).inter
      (GlobalTheory.LFun.IntPtsUnitary.isOpen_GLint _ (Valued.isOpen_integer (w.adicCompletion E)))
  exact (continuousAt_rowGL ℓ).preimage_mem_nhds
    (ho.mem_nhds (by simp only [rowGL_single, Set.mem_inter_iff, Set.mem_preimage, map_one, SetLike.mem_coe,
      one_mem, and_self]))

theorem pLoc_apply (w : HeightOneSpectrum (𝓞 E)) (x : Af E) : pLoc E w x = x w := rfl

theorem val_sub_single_le {a : ℕ} (ℓ : Fin a) {J : (FractionalIdeal (𝓞 E)⁰ E)ˣ} {y : Fin a → Af E}
    (hy : y - Pi.single ℓ 1 ∈ GlobalTheory.ThetaPoisson.latt a J) (w : HeightOneSpectrum (𝓞 E)) (j : Fin a) :
    Valued.v (pLoc E w (y j) - (Pi.single ℓ 1 : Fin a → w.adicCompletion E) j) ≤
      WithZero.exp (-FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E)) := by
  have h1 := (GroundTheory.Global.mem_idealFiniteAdeles J).1 (hy j) w
  rw [← pLoc_apply, Pi.sub_apply, map_sub, pLoc_single] at h1
  exact h1

theorem exists_bump_ideal_rowGL : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ℓ : Fin a)
    (T : Finset (HeightOneSpectrum (𝓞 E))) (U : Subgroup (GL (Fin a) (Af E))), IsOpen (U : Set (GL (Fin a) (Af E))) →
    ∃ (Φ : (Fin a → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ),
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ ∧
      (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) ∧ 0 < (Φ (Pi.single ℓ 1)).re ∧
      (∀ w ∉ T, FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) = 0) ∧
      ∀ y : Fin a → Af E, y - Pi.single ℓ 1 ∈ GlobalTheory.ThetaPoisson.latt a J →
        ∃ κ ∈ U, (∀ w, GeneralLinearGroup.map (pLoc E w) κ ∈ KGL w a) ∧
          (∀ w ∉ T, GeneralLinearGroup.map (pLoc E w) κ = 1) ∧
          ∀ w ∈ T, ∀ j, (GeneralLinearGroup.map (pLoc E w) κ : Matrix (Fin a) (Fin a) (w.adicCompletion E)) ℓ j = pLoc E w (y j) := by
  intro E _ _ _ a ℓ T U hU
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (isOpen_rowSet (E := E) ℓ) (Pi.single ℓ 1) (by
    intro w; simp)
  let f : ContDiffBump (Pi.single ℓ 1 : Fin a → Cinf E) := ⟨r / 4, r / 2, by positivity, by linarith⟩
  choose Nw hNw using fun w => exists_nat_rowGL_mem (E := E) ℓ hU w
  set N : ℕ := T.sup Nw + 1 with hN
  set n : HeightOneSpectrum (𝓞 E) → ℤ := fun w => if w ∈ T then (N : ℤ) else 0 with hn
  have hfin : ∀ᶠ v in Filter.cofinite, n v = 0 := by
    refine Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => ?_)
    by_contra h
    simp [hn, h] at hv
  let J : (FractionalIdeal (𝓞 E)⁰ E)ˣ := ∏ᶠ w, GroundTheory.Global.primeIdealUnit w ^ n w
  have hJ : ∀ w, FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) = n w :=
    GroundTheory.Global.count_finprod_primeIdealUnit_zpow n hfin
  refine ⟨fun u => ((f u : ℝ) : ℂ), J, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp f.contDiff
  · exact f.hasCompactSupport.comp_left Complex.ofReal_zero
  · refine (tsupport_comp_subset Complex.ofReal_zero f).trans ?_
    rw [f.tsupport_eq]
    exact (Metric.closedBall_subset_ball (by show r / 2 < r; linarith)).trans hball
  · intro u; simp [f.nonneg]
  · simp [f.one_of_mem_closedBall (Metric.mem_closedBall_self (by show (0:ℝ) ≤ r / 4; positivity))]
  · intro w hw; rw [hJ, hn]; simp [hw]
  · intro y hy
    have hloc : ∀ w ∈ T, ∀ j, Valued.v (pLoc E w (y j) - (Pi.single ℓ 1 : Fin a → w.adicCompletion E) j) ≤
        WithZero.exp (-(N : ℤ)) := by
      intro w hw j
      have h1 := val_sub_single_le ℓ hy w j
      rw [hJ, hn] at h1
      simpa only [hw, if_true] using h1
    have hmem : ∀ w ∈ T, locGL E a w (rowGL ℓ (fun j => pLoc E w (y j))) ∈ U ∧
        rowGL ℓ (fun j => pLoc E w (y j)) ∈ KGL w a := by
      intro w hw
      refine hNw w _ fun j => (hloc w hw j).trans ?_
      rw [WithZero.exp_le_exp, neg_le_neg_iff, Nat.cast_le, hN]
      exact (Finset.le_sup hw).trans (Nat.le_succ _)
    have hunit : ∀ w ∈ T, IsUnit (pLoc E w (y ℓ)) := by
      intro w hw
      refine isUnit_iff_ne_zero.2 fun h0 => ?_
      have h2 := hloc w hw ℓ
      rw [h0, Pi.single_eq_same, zero_sub, Valuation.map_neg, Valuation.map_one, ← WithZero.exp_zero,
        WithZero.exp_le_exp] at h2
      omega
    have key := map_list_prod_locGL (E := E) (a := a) (fun v => rowGL ℓ (fun j => pLoc E v (y j))) T.toList
      T.nodup_toList
    refine ⟨(T.toList.map fun v => locGL E a v (rowGL ℓ (fun j => pLoc E v (y j)))).prod, ?_, ?_, ?_, ?_⟩
    · refine Subgroup.list_prod_mem U fun x hx => ?_
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
      exact (hmem v (Finset.mem_toList.1 hv)).1
    · intro w
      rw [key w]
      split_ifs with h
      · exact (hmem w (Finset.mem_toList.1 h)).2
      · exact one_mem _
    · intro w hw
      rw [key w, if_neg (by simpa using hw)]
    · intro w hw j
      rw [key w, if_pos (Finset.mem_toList.2 hw), val_rowGL (hunit w hw)]
      simp [rowMat]

end GlobalTheory.BumpOrbit
