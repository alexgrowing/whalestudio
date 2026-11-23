import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.Energy
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProdProofB
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant

open Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical MeasureTheory
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.Mean4
open scoped ContDiff

noncomputable section

namespace GlobalTheory.Mean4O.InhabCalc

section Algebra

variable {V : Type} [AddCommGroup V] [Module ℝ V] {e : ℕ}

def pick (s : Finset (Fin (e + 1))) : Equiv.Perm (Fin (e + 1)) :=
  if h : s.Nonempty then Equiv.swap 0 h.choose else 1

theorem pick_mem {s : Finset (Fin (e + 1))} (h : s.Nonempty) : pick s 0 ∈ s := by
  rw [pick, dif_pos h, Equiv.swap_apply_left]
  exact h.choose_spec

def symForm (T : MultilinearMap ℝ (fun _ : Fin (e + 1) => V) ℝ) (Q P : V →ₗ[ℝ] V) :
    MultilinearMap ℝ (fun _ : Fin (e + 1) => V) ℝ :=
  ∑ s : Finset (Fin (e + 1)), (T.domDomCongr (pick s)).compLinearMap fun i => if i ∈ s then Q else P

theorem symForm_apply (T : MultilinearMap ℝ (fun _ : Fin (e + 1) => V) ℝ) (Q P : V →ₗ[ℝ] V) (v : Fin (e + 1) → V) :
    symForm T Q P v = ∑ s : Finset (Fin (e + 1)), T ((s.piecewise (fun i => Q (v i)) fun i => P (v i)) ∘ pick s) := by
  rw [symForm, MultilinearMap.sum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [MultilinearMap.compLinearMap_apply, MultilinearMap.domDomCongr_apply]
  congr 1
  funext i
  by_cases h : pick s i ∈ s <;> simp [Finset.piecewise, h]

variable (T : MultilinearMap ℝ (fun _ : Fin (e + 1) => V) ℝ) (Q P : V →ₗ[ℝ] V)
  (h1 : ∀ (w : Fin (e + 1) → V) (ρ : Equiv.Perm (Fin (e + 1))), ρ 0 = 0 → T (w ∘ ρ) = T w)
  (h2 : ∀ (w : Fin (e + 1) → V) (k : Fin (e + 1)), w 0 ∈ LinearMap.range Q → w k ∈ LinearMap.range Q →
    T (w ∘ Equiv.swap 0 k) = T w)
  (h3 : ∀ w : Fin (e + 1) → V, w 0 ∈ LinearMap.range P → T w = 0)

include h1 h2 in
theorem perm_eq (w : Fin (e + 1) → V) (σ τ : Equiv.Perm (Fin (e + 1))) (hσ : w (σ 0) ∈ LinearMap.range Q)
    (hτ : w (τ 0) ∈ LinearMap.range Q) : T (w ∘ σ) = T (w ∘ τ) := by
  have e1 : w ∘ σ = ((w ∘ τ) ∘ Equiv.swap 0 (τ⁻¹ (σ 0))) ∘ (Equiv.swap 0 (τ⁻¹ (σ 0)) * τ⁻¹ * σ) := by
    funext i
    simp
  rw [e1, h1 _ _ (by simp), h2 _ _ (by simpa using hτ) (by simpa using hσ)]

include h1 h2 h3 in
theorem symForm_symm (v : Fin (e + 1) → V) (π : Equiv.Perm (Fin (e + 1))) :
    symForm T Q P (v ∘ π) = symForm T Q P v := by
  rw [symForm_apply, symForm_apply]
  refine Fintype.sum_equiv (Equiv.finsetCongr π) _ _ fun s => ?_
  have e1 : (s.piecewise (fun i => Q ((v ∘ π) i)) fun i => P ((v ∘ π) i)) ∘ pick s =
      ((Equiv.finsetCongr π s).piecewise (fun i => Q (v i)) fun i => P (v i)) ∘ (π * pick s) := by
    funext i
    by_cases h : pick s i ∈ s <;> simp [Finset.piecewise, h]
  rw [e1]
  by_cases hs : s.Nonempty
  · have hs' : (Equiv.finsetCongr π s).Nonempty := by simpa using hs
    refine perm_eq T Q h1 h2 _ _ _ ?_ ?_
    · rw [Finset.piecewise_eq_of_mem _ _ _ (by simpa using pick_mem hs)]
      exact ⟨_, rfl⟩
    · rw [Finset.piecewise_eq_of_mem _ _ _ (pick_mem hs')]
      exact ⟨_, rfl⟩
  · rw [Finset.not_nonempty_iff_eq_empty] at hs
    subst hs
    rw [h3, h3] <;> simp [Finset.piecewise]

include h1 h2 in
theorem symForm_of_mem (hQP : ∀ x, Q x + P x = x) (v : Fin (e + 1) → V) (hv : P (v 0) = 0) :
    symForm T Q P v = T v := by
  have hv' : v = (fun i => Q (v i)) + fun i => P (v i) := funext fun i => (hQP _).symm
  rw [symForm_apply]
  conv_rhs => rw [hv', T.map_add_univ]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h0 : (0 : Fin (e + 1)) ∈ s
  · have := perm_eq T Q h1 h2 (s.piecewise (fun i => Q (v i)) fun i => P (v i)) (pick s) 1
      (by rw [Finset.piecewise_eq_of_mem _ _ _ (pick_mem ⟨0, h0⟩)]; exact ⟨_, rfl⟩)
      (by rw [Equiv.Perm.one_apply, Finset.piecewise_eq_of_mem _ _ _ h0]; exact ⟨_, rfl⟩)
    rw [this]
    congr
  · rw [T.map_coord_zero ((pick s)⁻¹ 0) (by simp [Finset.piecewise, h0, hv]),
      T.map_coord_zero 0 (by simp [Finset.piecewise, h0, hv])]

end Algebra

section Analysis

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem mInt_congr_φ (A : FinHolAtlas e X) {Φ Ψ : Fin e → LocPot X} (h : ∀ i, (Φ i).φ = (Ψ i).φ) (g : X → ℝ) :
    mInt A Φ g = mInt A Ψ g := by
  unfold mInt integralWith locDens
  simp only [h]

theorem mInt_update_add' [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (F : Fin e → LocPot X) (k : Fin e)
    (P Q : LocPot X) (hF : ∀ i, IsPotential A (F i)) (hP : IsPotential A P) (hQ : IsPotential A Q) (g : X → ℝ)
    (hg : Continuous g) :
    mInt A (Function.update F k (P + Q)) g = mInt A (Function.update F k P) g + mInt A (Function.update F k Q) g := by
  cases e with
  | zero => exact k.elim0
  | succ e => convert ReciprocityTheory.AnForm.P.mInt_update_add A F k P Q hF hP hQ g hg

theorem mInt_update_rsmul (A : FinHolAtlas e X) (F : Fin e → LocPot X) (k : Fin e) (c : ℝ)
    (P : LocPot X) (hF : ∀ i, IsPotential A (F i)) (hP : IsPotential A P) (g : X → ℝ) :
    mInt A (Function.update F k (P.rsmul c)) g = c * mInt A (Function.update F k P) g := by
  cases e with
  | zero => exact k.elim0
  | succ e =>
    have h := mIntRsmul A c P (Fin.tail (F ∘ Equiv.swap 0 k)) hP (fun i => hF _) g
    rw [← ReciprocityTheory.AnForm.P.mInt_update_eq, ← ReciprocityTheory.AnForm.P.mInt_update_eq] at h
    convert h

theorem mInt_update_byParts [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (F : Fin e → LocPot X) (k : Fin e)
    (hF : ∀ i, IsPotential A (F i)) (v w : X → ℝ) (hv : A.Smooth v) (hw : A.Smooth w) :
    mInt A (Function.update F k (LocPot.ofFun w)) v = mInt A (Function.update F k (LocPot.ofFun v)) w := by
  cases e with
  | zero => exact k.elim0
  | succ e =>
    have h := byPartsSymm A v w hv hw (Fin.tail (F ∘ Equiv.swap 0 k)) (fun i => hF _)
    rw [← ReciprocityTheory.AnForm.P.mInt_update_eq, ← ReciprocityTheory.AnForm.P.mInt_update_eq] at h
    convert h

theorem mInt_one_pos [CompactSpace X] [T2Space X] [Nonempty X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X)
    (hΦ : ∀ i, IsPotential A (Φ i)) (hp : ∀ i, IsPosPot A (Φ i)) : 0 < mInt A Φ fun _ => 1 := by
  have hP := existsPartition A
  rw [mInt, dif_pos hP, integralWith]
  set R := hP.some
  have hnn : ∀ j, ∀ y ∈ (A.chart j).target, 0 ≤ R.χ j ((A.chart j).symm y) * 1 * locDens A Φ j y := fun j y hy =>
    mul_nonneg (mul_nonneg (R.nonneg _ _) zero_le_one) (locDensPos A Φ hΦ hp j y hy).le
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨j, hj⟩ : ∃ j, R.χ j x ≠ 0 := by
    by_contra! h
    simpa [h] using R.sum_eq_one x
  refine Finset.sum_pos' (fun j _ => setIntegral_nonneg (A.chart j).open_target.measurableSet (hnn j))
    ⟨j, Finset.mem_univ _, ?_⟩
  have hx : x ∈ (A.chart j).source := R.tsupport_subset j (subset_tsupport _ hj)
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    ((ae_restrict_iff' (A.chart j).open_target.measurableSet).2 (ae_of_all _ (hnn j)))
    (integrableOn_weight A R Φ (fun _ => 1) (mIntegrableCont A Φ hΦ _ continuous_const) j)]
  have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Function.support (R.χ j)) :=
    (A.chart j).isOpen_inter_preimage_symm (projLine_continuous_of_smooth A (R.smooth j)).isOpen_support
  refine lt_of_lt_of_le (hO.measure_pos volume ⟨A.chart j x, (A.chart j).map_source hx, ?_⟩) (measure_mono ?_)
  · simpa [(A.chart j).left_inv hx] using hj
  · rintro y ⟨hy, hy'⟩
    exact ⟨mul_ne_zero (mul_ne_zero hy' one_ne_zero) (locDensPos A Φ hΦ hp j y hy).ne', hy⟩

def combPot {I : Type} [Fintype I] (P : I → LocPot X) (a : I → ℝ) (u : X → ℝ) : LocPot X where
  U x := ⋂ i, (P i).U x
  isOpen_U x := isOpen_iInter_of_finite fun i => (P i).isOpen_U x
  mem_U x := Set.mem_iInter.2 fun i => (P i).mem_U x
  φ x y := ∑ i, a i * (P i).φ x y + u y

theorem isPotential_combPot (A : FinHolAtlas e X) {I : Type} [Fintype I] (P : I → LocPot X)
    (hP : ∀ i, IsPotential A (P i)) (a : I → ℝ) (u : X → ℝ) (hu : A.Smooth u) : IsPotential A (combPot P a u) := by
  refine ⟨fun x j => ?_, fun x x' y hy => ?_⟩
  · have h1 : ∀ i, ContDiffOn ℝ ∞ (fun y => a i * (P i).φ x ((A.chart j).symm y))
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (combPot P a u).U x) := fun i =>
      contDiffOn_const.mul (((hP i).1 x j).mono
        (Set.inter_subset_inter_right _ (Set.preimage_mono (Set.iInter_subset _ i))))
    exact (ContDiffOn.sum fun i _ => h1 i).add
      ((hu j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono (Set.subset_univ _))))
  · choose W hW hyW G hG hφ using fun i =>
      (hP i).2 x x' y ⟨Set.mem_iInter.1 hy.1 i, Set.mem_iInter.1 hy.2 i⟩
    refine ⟨⋂ i, W i, isOpen_iInter_of_finite hW, Set.mem_iInter.2 hyW, fun z => ∑ i, (a i : ℂ) * G i z, fun j => ?_, ?_⟩
    · intro t ht
      exact Finset.analyticAt_fun_sum _ fun i _ =>
        analyticAt_const.mul (hG i j t ⟨ht.1, Set.mem_iInter.1 ht.2 i⟩)
    · rintro z ⟨⟨h0, h1⟩, h2⟩
      simp only [combPot, Complex.re_sum, Complex.re_ofReal_mul]
      rw [add_sub_add_right_eq_sub, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hφ i z ⟨⟨Set.mem_iInter.1 h0 i, Set.mem_iInter.1 h1 i⟩, Set.mem_iInter.1 h2 i⟩, mul_sub]

theorem leviEq_of_φ (A : FinHolAtlas e X) {P Q : LocPot X} (h : P.φ = Q.φ) : LeviEq A P Q := by
  intro j y _ w
  simp only [leviAt, h]

theorem fs_isPosPot : IsPosPot p1 fsPot := by
  intro x j y hy v hv
  have hv0 : 0 < ‖v 0‖ ^ 2 := by
    have : v 0 ≠ 0 := fun h => hv (funext fun i => by rw [Subsingleton.elim i 0]; exact h)
    have := norm_pos_iff.2 this
    positivity
  have ht : 0 ≤ ‖y 0‖ ^ 2 := by positivity
  rcases fsPot_chart x j with h | ⟨h, hs⟩
  · rw [h]
    have h0 : (1 : ℝ) + ‖y 0‖ ^ 2 ≠ 0 := ne_of_gt (by linarith)
    rw [projLine_leviForm_radial (F := fun w => fubiniStudyProfile (fsQ w)) (G := fubiniStudyProfile) (G' := fun t => (1 / 2) * (1 + t)⁻¹)
      (Filter.Eventually.of_forall fun w => rfl) ?_
      ((((hasDerivAt_id _).const_add 1).inv h0).const_mul (1 / 2)) v]
    · have e : ∀ t : ℝ, 0 ≤ t → 0 < 1 / 2 * (-1 / (1 + t) ^ 2) * t + 1 / 2 * (1 + t)⁻¹ := by
        intro t ht0
        have h1 : (0 : ℝ) < 1 + t := by linarith
        rw [show 1 / 2 * (-1 / (1 + t) ^ 2) * t + 1 / 2 * (1 + t)⁻¹ = 1 / (2 * (1 + t) ^ 2) by
          field_simp; ring]
        positivity
      exact mul_pos (e _ ht) hv0
    · filter_upwards [Ioi_mem_nhds (show (-1 : ℝ) < ‖y 0‖ ^ 2 by linarith)] with t ht'
      exact hasDerivAt_fubiniStudyProfile ht'
  · rw [h]
    have hy0 : y 0 ≠ 0 := hs y hy
    have htp : 0 < ‖y 0‖ ^ 2 := by have := norm_pos_iff.2 hy0; positivity
    have h0 : ‖y 0‖ ^ 2 * (‖y 0‖ ^ 2 + 1) ≠ 0 := ne_of_gt (by positivity)
    rw [projLine_leviForm_radial (F := fun w => fubiniStudyProfileInv (fsQ w)) (G := fubiniStudyProfileInv) (G' := fun t => -(1 / 2) * (t * (t + 1))⁻¹)
      (Filter.Eventually.of_forall fun w => rfl) ?_
      ((((hasDerivAt_id _).mul ((hasDerivAt_id _).add_const 1)).inv h0).const_mul (-(1 / 2))) v]
    · have e : ∀ t : ℝ, 0 < t → 0 < -(1 / 2) * (-(1 * (t + 1) + t * 1) / (t * (t + 1)) ^ 2) * t +
          -(1 / 2) * (t * (t + 1))⁻¹ := by
        intro t ht0
        rw [show -(1 / 2) * (-(1 * (t + 1) + t * 1) / (t * (t + 1)) ^ 2) * t +
            -(1 / 2) * (t * (t + 1))⁻¹ = 1 / (2 * (t + 1) ^ 2) by field_simp; ring]
        positivity
      exact mul_pos (e _ htp) hv0
    · filter_upwards [Ioi_mem_nhds htp] with t ht'
      exact hasDerivAt_fubiniStudyProfileInv ht'

theorem isPosPot_prod {e' : ℕ} {Y : Type} [TopologicalSpace Y] (A : FinHolAtlas e X) (B : FinHolAtlas e' Y)
    (P : LocPot X) (Q : LocPot Y) (hP : IsPotential A P) (hQ : IsPotential B Q) (hp : IsPosPot A P)
    (hq : IsPosPot B Q) : IsPosPot (prodAtlas A B) (P.pr1 + Q.pr2) := by
  intro x i y hy w hw
  set j := (finProdFinEquiv.symm i).1
  set k := (finProdFinEquiv.symm i).2
  let F : (Fin (e + e') → ℂ) →L[ℂ] (Fin e → ℂ) :=
    (ContinuousLinearMap.fst ℂ _ _).comp (appendCLE e e').symm.toContinuousLinearMap
  let S : (Fin (e + e') → ℂ) →L[ℂ] (Fin e' → ℂ) :=
    (ContinuousLinearMap.snd ℂ _ _).comp (appendCLE e e').symm.toContinuousLinearMap
  have ht := (mem_prodChart_target A B j k y).1 hy.1
  have hy1 : F y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x.1 := ⟨ht.1, hy.2.1⟩
  have hy2 : S y ∈ (B.chart k).target ∩ (B.chart k).symm ⁻¹' Q.U x.2 := ⟨ht.2, hy.2.2⟩
  have c1 : ContDiffAt ℝ 2 (P.φ x.1 ∘ (A.chart j).symm) (F y) :=
    (contDiffAt_of_isPotential A P hP _ j hy1).of_le (by norm_cast)
  have c2 : ContDiffAt ℝ 2 (Q.φ x.2 ∘ (B.chart k).symm) (S y) :=
    (contDiffAt_of_isPotential B Q hQ _ k hy2).of_le (by norm_cast)
  have he : (P.pr1 + Q.pr2).φ x ∘ ((prodAtlas A B).chart i).symm =
      fun z => ((P.φ x.1 ∘ (A.chart j).symm) ∘ F) z + 1 * ((Q.φ x.2 ∘ (B.chart k).symm) ∘ S) z := by
    funext z
    rw [one_mul]
    rfl
  rw [he, levi_add_smul 1 (c1.comp y (F.contDiff.restrict_scalars ℝ).contDiffAt)
    (c2.comp y (S.contDiff.restrict_scalars ℝ).contDiffAt), levi_comp w (F.analyticAt y) c1,
    levi_comp w (S.analyticAt y) c2, F.fderiv, S.fderiv, one_mul]
  by_cases h1 : F w = 0
  · have h2 : S w ≠ 0 := by
      intro h2
      apply hw
      apply (appendCLE e e').symm.injective
      rw [map_zero]
      exact Prod.ext h1 h2
    rw [h1, levi_zero, zero_add]
    exact hq _ k _ hy2 _ h2
  · refine add_pos_of_pos_of_nonneg (hp _ j _ hy1 _ h1) ?_
    by_cases h2 : S w = 0
    · rw [h2, levi_zero]
    · exact (hq _ k _ hy2 _ h2).le

end Analysis

section Calculus

variable {e : ℕ} (M : Man e)

def smSub : Submodule ℝ M.Fun where
  carrier := {u | M.Smooth u}
  add_mem' hu hv σ j := (hu σ j).add (hv σ j)
  zero_mem' _ _ := contDiffOn_const
  smul_mem' c _ hu σ j := (contDiffOn_const (c := c)).mul (hu σ j)

def smProj : M.Fun →ₗ[ℝ] smSub M :=
  ((smSub M).subtype.exists_leftInverse_of_injective (smSub M).ker_subtype).choose

theorem smProj_of_smooth {u : M.Fun} (hu : M.Smooth u) : (smProj M u : M.Fun) = u := by
  have h := LinearMap.congr_fun ((smSub M).subtype.exists_leftInverse_of_injective (smSub M).ker_subtype).choose_spec
    ⟨u, hu⟩
  exact congrArg Subtype.val h

variable {I : Type} [Fintype I] (P : I → M.Pot)

def chern (v : (I → ℝ) × smSub M) : M.Pot := fun σ => combPot (fun i => P i σ) v.1 ((v.2 : M.Fun) σ)

theorem chern_add_φ (v w : (I → ℝ) × smSub M) (σ) :
    (chern M P (v + w) σ).φ = (chern M P v σ + chern M P w σ).φ := by
  funext x y
  simp only [add_φ, chern, combPot, Prod.fst_add, Prod.snd_add, Pi.add_apply, Submodule.coe_add, add_mul,
    Finset.sum_add_distrib]
  ring

theorem chern_smul_φ (c : ℝ) (v : (I → ℝ) × smSub M) (σ) :
    (chern M P (c • v) σ).φ = ((chern M P v σ).rsmul c).φ := by
  funext x y
  simp only [LocPot.rsmul, chern, combPot, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, Submodule.coe_smul,
    smul_eq_mul, mul_add, Finset.mul_sum, mul_assoc]

theorem chern_fun_φ (u : smSub M) (σ) : (chern M P (0, u) σ).φ = (LocPot.ofFun ((u : M.Fun) σ)).φ := by
  funext x y
  simp [chern, combPot, LocPot.ofFun]

theorem chern_single_φ (i : I) (σ) : (chern M P (Pi.single i 1, 0) σ).φ = (P i σ).φ := by
  funext x y
  simp [chern, combPot, Pi.single_apply]

theorem mInt_chern_update (v : Fin e → (I → ℝ) × smSub M) (k : Fin e) (x : (I → ℝ) × smSub M) (σ)
    (R : LocPot (M.X σ)) (hR : (chern M P x σ).φ = R.φ) (g : M.X σ → ℝ) :
    mInt (M.A σ) (fun i => chern M P (Function.update v k x i) σ) g =
      mInt (M.A σ) (Function.update (fun i => chern M P (v i) σ) k R) g := by
  refine mInt_congr_φ _ (fun i => ?_) g
  by_cases h : i = k
  · subst h
    simpa using hR
  · simp [Function.update_of_ne h]

variable (hP : ∀ i σ, IsPotential (M.A σ) (P i σ))

include hP in
theorem chern_pot (v : (I → ℝ) × smSub M) (σ) : IsPotential (M.A σ) (chern M P v σ) :=
  isPotential_combPot _ _ (fun i => hP i σ) _ _ (v.2.2 σ)

def intML (u : smSub M) : MultilinearMap ℝ (fun _ : Fin e => (I → ℝ) × smSub M) ℝ :=
  MultilinearMap.mk' (fun v => M.int (fun i => chern M P (v i)) u)
    (fun v k x y => by
      simp only [Man.int]
      rw [← mul_add, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [mInt_chern_update M P v k _ σ _ (chern_add_φ M P x y σ), mInt_chern_update M P v k x σ _ rfl,
        mInt_chern_update M P v k y σ _ rfl]
      exact mInt_update_add' _ _ k _ _ (fun i => chern_pot M P hP _ σ) (chern_pot M P hP _ σ) (chern_pot M P hP _ σ) _
        (projLine_continuous_of_smooth _ (u.2 σ)))
    (fun v k c x => by
      simp only [Man.int, smul_eq_mul]
      rw [mul_left_comm, Finset.mul_sum _ _ c]
      congr 1
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [mInt_chern_update M P v k _ σ _ (chern_smul_φ M P c x σ), mInt_chern_update M P v k x σ _ rfl]
      exact mInt_update_rsmul _ _ k _ _ (fun i => chern_pot M P hP _ σ) (chern_pot M P hP _ σ) _)

theorem intML_apply (u : smSub M) (v : Fin e → (I → ℝ) × smSub M) :
    intML M P hP u v = M.int (fun i => chern M P (v i)) u := rfl

theorem intML_lin (c : ℝ) (u u' : smSub M) (v : Fin e → (I → ℝ) × smSub M) :
    intML M P hP (c • u + u') v = c * intML M P hP u v + intML M P hP u' v := by
  simp only [intML_apply, Man.int]
  rw [mul_left_comm, Finset.mul_sum _ _ c, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hc : ∀ i, IsPotential (M.A σ) (chern M P (v i) σ) := fun i => chern_pot M P hP _ σ
  exact mIntLinear _ _ hc c _ _ (mIntegrableCont _ _ hc _ (projLine_continuous_of_smooth _ (u.2 σ)))
    (mIntegrableCont _ _ hc _ (projLine_continuous_of_smooth _ (u'.2 σ)))

def intL : smSub M →ₗ[ℝ] MultilinearMap ℝ (fun _ : Fin e => (I → ℝ) × smSub M) ℝ where
  toFun := intML M P hP
  map_add' u u' := by
    ext v
    simpa using intML_lin M P hP 1 u u' v
  map_smul' c u := by
    ext v
    have h0 := intML_lin M P hP 1 0 0 v
    have h1 := intML_lin M P hP c u 0 v
    simp only [smul_zero, add_zero, one_mul, left_eq_add] at h0 h1
    simp [h1, h0]

def form0 : MultilinearMap ℝ (fun _ : Fin (e + 1) => (I → ℝ) × smSub M) ℝ :=
  LinearMap.uncurryLeft (M := fun _ : Fin (e + 1) => (I → ℝ) × smSub M) ((intL M P hP).comp (LinearMap.snd ℝ _ _))

theorem zero_form_apply (w : Fin (e + 1) → (I → ℝ) × smSub M) :
    form0 M P hP w = M.int (fun i => chern M P (w i.succ)) (w 0).2 := rfl

theorem zero_form_perm_invariant (w : Fin (e + 1) → (I → ℝ) × smSub M) (ρ : Equiv.Perm (Fin (e + 1))) (h : ρ 0 = 0) :
    form0 M P hP (w ∘ ρ) = form0 M P hP w := by
  obtain ⟨⟨p, ρ'⟩, rfl⟩ := Equiv.Perm.decomposeFin.symm.surjective ρ
  rw [Equiv.Perm.decomposeFin_symm_apply_zero] at h
  subst h
  rw [zero_form_apply, zero_form_apply]
  simp only [Function.comp_apply, Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply]
  unfold Man.int
  refine congrArg (M.κ * ·) (Finset.sum_congr rfl fun σ _ => ?_)
  exact mIntSymm (M.A σ) (fun i => chern M P (w i.succ) σ) ρ' (((w 0).2 : M.Fun) σ)

theorem zero_form_swap_invariant (w : Fin (e + 1) → (I → ℝ) × smSub M) (k : Fin (e + 1)) (h0 : (w 0).1 = 0) (hk : (w k).1 = 0) :
    form0 M P hP (w ∘ Equiv.swap 0 k) = form0 M P hP w := by
  refine Fin.cases (fun _ => by simp) (fun k hk => ?_) k hk
  have e1 : ∀ i : Fin e, w (Equiv.swap 0 k.succ i.succ) = Function.update (fun i : Fin e => w i.succ) k (0, (w 0).2) i := by
    intro i
    by_cases h : i = k
    · subst h
      rw [Equiv.swap_apply_right, Function.update_self, ← h0]
    · rw [Function.update_of_ne h, Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i) (by simpa using h)]
  have e2 : ∀ i : Fin e, w i.succ = Function.update (fun i : Fin e => w i.succ) k (0, (w k.succ).2) i := by
    intro i
    by_cases h : i = k
    · subst h
      rw [Function.update_self, ← hk]
    · rw [Function.update_of_ne h]
  simp only [zero_form_apply, Man.int, Function.comp_apply, Equiv.swap_apply_left, e1]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [show (fun i : Fin e => chern M P (w i.succ) σ) = fun i => chern M P
      (Function.update (fun i : Fin e => w i.succ) k (0, (w k.succ).2) i) σ from funext fun i => by rw [← e2 i],
    mInt_chern_update M P _ k _ σ _ (chern_fun_φ M P _ σ), mInt_chern_update M P _ k _ σ _ (chern_fun_φ M P _ σ)]
  exact mInt_update_byParts _ _ k (fun i => chern_pot M P hP _ σ) _ _ ((w k.succ).2.2 σ) ((w 0).2.2 σ)

def calcOf : Calc M where
  V := (I → ℝ) × smSub M
  num := symForm (form0 M P hP) ((LinearMap.inr ℝ _ _).comp (LinearMap.snd ℝ _ _))
    ((LinearMap.inl ℝ _ _).comp (LinearMap.fst ℝ _ _))
  symm v π := by
    refine symForm_symm _ _ _ (zero_form_perm_invariant M P hP) (fun w k h0 hk => zero_form_swap_invariant M P hP w k ?_ ?_) ?_ v π
    · obtain ⟨x, hx⟩ := h0
      rw [← hx]
      rfl
    · obtain ⟨x, hx⟩ := hk
      rw [← hx]
      rfl
    · rintro w ⟨x, hx⟩
      have : (w 0).2 = 0 := by
        rw [← hx]
        rfl
      show intL M P hP (w 0).2 _ = 0
      rw [this, map_zero, MultilinearMap.zero_apply]
  c1 := chern M P
  firstChern_isPotential := chern_pot M P hP
  isOneCochain_add v w σ := leviEq_of_φ _ (chern_add_φ M P v w σ)
  firstChern_smul_leviEq a v σ := leviEq_of_φ _ (chern_smul_φ M P a v σ)
  ar := (LinearMap.inr ℝ _ _).comp (smProj M)
  c1_ar u hu σ := by
    refine leviEq_of_φ _ ?_
    have := chern_fun_φ M P (smProj M u) σ
    rw [smProj_of_smooth M hu] at this
    exact this
  num_ar u hu v := by
    rw [symForm_of_mem _ _ _ (zero_form_perm_invariant M P hP) (fun w k h0 hk => zero_form_swap_invariant M P hP w k ?_ ?_) (fun x => by simp)
      _ (by simp), zero_form_apply]
    · simp [smProj_of_smooth M hu]
    · obtain ⟨x, hx⟩ := h0
      rw [← hx]
      rfl
    · obtain ⟨x, hx⟩ := hk
      rw [← hx]
      rfl

def cls (i : I) : (calcOf M P hP).V := (Pi.single i 1, 0)

theorem first_chern_class_potential (i : I) (σ) : ((calcOf M P hP).c1 (cls M P hP i) σ).φ = (P i σ).φ := chern_single_φ M P i σ

theorem int_Om_pos (h : ∃ σ, Nonempty (M.X σ)) : 0 < M.int (fun _ => M.Om) fun _ _ => 1 := by
  obtain ⟨σ₀, h⟩ := h
  refine mul_pos M.κ_pos (Finset.sum_pos' (fun σ _ => ?_) ⟨σ₀, Finset.mem_univ _, ?_⟩)
  · refine mIntNonneg _ _ (fun _ => (M.bd σ).2.2.1) (fun _ x j y hy w => ?_) _ fun _ => zero_le_one
    by_cases hw : w = 0
    · rw [hw, levi_zero]
    · exact ((M.bd σ).2.2.2.1 x j y hy w hw).le
  · exact mInt_one_pos _ _ (fun _ => (M.bd σ₀).2.2.1) fun _ => (M.bd σ₀).2.2.2.1

theorem int_congr_φ {Q' Q : Fin e → M.Pot} (h : ∀ i σ, (Q' i σ).φ = (Q i σ).φ) (u : M.Fun) :
    M.int Q' u = M.int Q u :=
  congrArg (M.κ * ·) (Finset.sum_congr rfl fun σ _ => mInt_congr_φ (M.A σ) (fun i => h i σ) (u σ))

theorem smooth_one : M.Smooth fun _ _ => 1 := fun _ _ => contDiffOn_const

theorem num_one_pos (i : I) (hi : P i = M.Om) (h : ∃ σ, Nonempty (M.X σ)) :
    0 < (calcOf M P hP).num (Fin.cons ((calcOf M P hP).ar fun _ _ => 1) fun _ => cls M P hP i) := by
  rw [(calcOf M P hP).num_ar _ (smooth_one M)]
  rw [int_congr_φ M (Q := fun _ => M.Om) (fun _ σ => by rw [first_chern_class_potential, hi])]
  exact int_Om_pos M h

theorem exists_calc (M : Man e) {I : Type} [Fintype I] (P : I → M.Pot) (hP : ∀ i σ, IsPotential (M.A σ) (P i σ)) :
    ∃ (K : Calc M) (c : I → K.V), (∀ i σ, LeviEq (M.A σ) (K.c1 (c i) σ) (P i σ)) ∧
      ∀ i, P i = M.Om → (∃ σ, Nonempty (M.X σ)) → 0 < K.num (Fin.cons (K.ar fun _ _ => 1) fun _ => c i) :=
  ⟨calcOf M P hP, cls M P hP, fun i σ => leviEq_of_φ _ (first_chern_class_potential M P hP i σ), num_one_pos M P hP⟩

end Calculus

section Manifolds

theorem isBd_empty {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Om : LocPot X)
    (h : IsPotential A Om) (hp : IsPosPot A Om) : IsBd A ∅ (fun _ => Real.exp 1) Om := by
  refine ⟨isClosed_empty, fun j => by simp, h, hp, fun _ => contDiffOn_const, fun _ _ => le_rfl,
    fun a => by simp, ?_, 1, one_pos, fun j y hy _ w => ?_⟩
  · refine mIntegrableCont A _ (fun _ => h) _ ?_
    simp only [cut, Set.compl_empty, Set.inter_self, Set.indicator_univ]
    exact continuous_const
  · have hy' : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Om.U ((A.chart j).symm y) := ⟨hy, Om.mem_U _⟩
    have c1 : ContDiffAt ℝ 2 (Om.φ ((A.chart j).symm y) ∘ (A.chart j).symm) y :=
      (contDiffAt_of_isPotential A Om h _ j hy').of_le (by norm_cast)
    have h1 := levi_add_smul (g := fun _ => Real.exp 1) (-1) c1 contDiffAt_const w
    have h2 : levi (fun _ : Fin e → ℂ => Real.exp 1) y w = 0 := by simp [levi]
    rw [h2, mul_zero, add_zero] at h1
    refine le_of_le_of_eq ?_ h1.symm
    by_cases hw : w = 0
    · rw [hw, levi_zero]
    · exact (hp _ j y hy' w hw).le

def pointMan : Man 0 where
  n := 0
  X _ := PUnit
  A _ := ptAtlas PUnit
  Z _ := ∅
  r _ _ := Real.exp 1
  Om _ := LocPot.ofFun fun _ => 0
  bd _ := isBd_empty _ _ (isPotential_ofFun _ _ fun _ => contDiffOn_const)
    fun _ _ _ _ _ hw => absurd (Subsingleton.elim _ _) hw
  κ := 1
  κ_pos := one_pos

def timesLine {e : ℕ} (M : Man e) : Man (e + 1) where
  n := M.n
  X σ := M.X σ × OnePoint ℂ
  A σ := prodAtlas (M.A σ) p1
  Z _ := ∅
  r _ _ := Real.exp 1
  Om σ := (M.Om σ).pr1 + fsPot.pr2
  bd σ := isBd_empty _ _
    (isPotentialAdd (prodAtlas (M.A σ) p1) _ _ (isPotential_first_projection _ _ _ (M.bd σ).2.2.1)
      (isPotential_second_projection _ _ _ projLine_isSmoothPotential))
    (isPosPot_prod (M.A σ) p1 _ _ (M.bd σ).2.2.1 projLine_isSmoothPotential (M.bd σ).2.2.2.1 fs_isPosPot)
  κ := M.κ
  κ_pos := M.κ_pos

def linesMan (e : ℕ) : Man e := Nat.rec (motive := fun e => Man e) pointMan (fun _ M => timesLine M) e

theorem linesMan_nonempty (e : ℕ) : ∀ σ, Nonempty ((linesMan e).X σ) := by
  induction e with
  | zero => exact fun _ => ⟨PUnit.unit⟩
  | succ e ih => exact fun σ => (ih σ).elim fun x => ⟨(x, OnePoint.infty)⟩

theorem exists_man (e : ℕ) : ∃ M : Man e, ∀ σ, Nonempty (M.X σ) :=
  ⟨linesMan e, linesMan_nonempty e⟩

end Manifolds

section Record

variable {D : D7} (Y : ShimX D.what₂.Tau)

def realOf (M : Y.Comp → Man (dimY Y)) (ℓ : Wt Y →ₗ[ℝ] ℝ) : Real0 Y where
  M := M
  F c :=
    { th := fun u σ => ((M c).Om σ).rsmul (ℓ u)
      a := (M c).Om
      ph := 0
      phR := 0
      phS := 0 }
  K _ c := calcOf (M c) (fun _ : Unit => (M c).Om) fun _ σ => ((M c).bd σ).2.2.1
  L _ c := ℓ.smulRight (cls (M c) (fun _ : Unit => (M c).Om) (fun _ σ => ((M c).bd σ).2.2.1) ())
  a _ c := cls (M c) (fun _ : Unit => (M c).Om) (fun _ σ => ((M c).bd σ).2.2.1) ()
  th_pot c u σ := isPotentialRsmul _ _ _ ((M c).bd σ).2.2.1
  a_pot c σ := ((M c).bd σ).2.2.1
  c1_L _ c u σ := by
    refine leviEq_of_φ _ ((chern_smul_φ (M c) _ (ℓ u) _ σ).trans ?_)
    funext x y
    exact congrArg (ℓ u * ·) (congrFun (congrFun (chern_single_φ (M c) (fun _ : Unit => (M c).Om) () σ) x) y)
  firstChern_leviEq_constant _ c σ := leviEq_of_φ _ (first_chern_class_potential (M c) _ _ () σ)

def sumWt : Wt Y →ₗ[ℝ] ℝ where
  toFun u := ∑ τ, ∑ i, u τ i
  map_add' u v := by simp [Finset.sum_add_distrib]
  map_smul' c u := by simp [Finset.mul_sum]

end Record

end GlobalTheory.Mean4O.InhabCalc
