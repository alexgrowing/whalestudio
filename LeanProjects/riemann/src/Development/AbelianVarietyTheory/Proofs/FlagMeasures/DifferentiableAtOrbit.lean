import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.OrbitStepSpace
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.OrthonormalPlaceBasis
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalBasis
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousMultilinearMapOfInnerProd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNormSqTensUpdate
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDerivAtOrbitTens
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StepSpacePropsOfDiff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.VPSubOfLocalBound

open Formalism.MainNotions.S NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace (stepSpace IsDiffVec IsONFamily stepConst)

noncomputable section

namespace GlobalTheory.StepGlob

theorem stepConst_eq (n : ℕ) (b : ℝ) (P : ℕ) : stepConst n b P = beP n b P := by
  unfold stepConst beP
  have h : (n : ℝ) ^ (3 / 2 : ℝ) = n * Real.sqrt n := by
    rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add' (Nat.cast_nonneg n) (by norm_num), Real.rpow_one]
  rw [h, Real.sqrt_eq_rpow]

theorem beP_nonneg (n : ℕ) (b : ℝ) (P : ℕ) : 0 ≤ beP n b P := by
  unfold beP
  positivity

theorem finrank_of_isONBasis {n m : ℕ} {ε : Fin n → Bool} {E : Fin m → gLie ε} (h : IsONBasis E) :
    Module.finrank ℝ (gLie ε) = m := by
  have hli : LinearIndependent ℝ E := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have h1 := congrArg (fun X : gLie ε =>
      (((X : Matrix (Fin n) (Fin n) ℂ) * (E j : Matrix (Fin n) (Fin n) ℂ)ᴴ).trace).re) hg
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_mul, Matrix.trace_sum, smul_mul_assoc,
      Matrix.trace_smul, Complex.re_sum, Complex.smul_re, h.1] at h1
    simpa using h1
  rw [Module.finrank_eq_card_basis (Module.Basis.mk hli h.2.ge), Fintype.card_fin]

theorem card_of_isONBasis {n m : ℕ} {ε : Fin n → Bool} {E : Fin m → gLie ε} (h : IsONBasis E) :
    m = n ^ 2 := by
  obtain ⟨F, h1, h2, h3⟩ := GlobalTheory.LieONB.exists_orthonormal_basis n ε
  have hF : IsONBasis (fun i => (⟨F i, (h1 i).1⟩ : gLie ε)) := by
    refine ⟨h2, ?_⟩
    rw [eq_top_iff]
    rintro ⟨X, hX⟩ -
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun i => ((X * (F i)ᴴ).trace).re, Subtype.ext ?_⟩
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    conv_rhs => rw [h3 X hX]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.coe_smul]
  rw [← finrank_of_isONBasis h, finrank_of_isONBasis hF]

variable (B : RowsAut)

theorem orbit_sum {k : ℕ} (E : gInf B) (y : Fin k → B.Hs) :
    orbit B E (∑ l, y l) = fun t => ∑ l, orbit B E (y l) t := by
  funext t
  simp [orbit]

theorem dAct_add_smul {E : gInf B} {w w' : B.Hs} (hw : DifferentiableAt ℝ (orbit B E w) 0)
    (hw' : DifferentiableAt ℝ (orbit B E w') 0) (c : ℂ) :
    dAct B E (w + c • w') = dAct B E w + c • dAct B E w' := by
  have : orbit B E (w + c • w') = fun t => orbit B E w t + c • orbit B E w' t := by
    funext t
    simp [orbit]
  unfold dAct
  rw [this]
  exact (hw.hasDerivAt.fun_add (hw'.hasDerivAt.fun_const_smul c)).deriv

theorem dAct_zero (E : gInf B) : dAct B E 0 = 0 := by
  have : orbit B E 0 = fun _ => 0 := by
    funext t
    simp [orbit]
  unfold dAct
  rw [this]
  simp

section Diff

variable {B} (hU : ∀ v, IsURepOn (UJset (B.I.ε v)) (B.σ v))
  (hd : ∀ v P, ∀ w ∈ stepSpace (B.I.ε v) (B.lam v) (B.σ v) P, IsDiffVec (B.I.ε v) (B.σ v) w)

include hU hd

open Classical in

theorem hasDerivAt_orbit_sum {P k : ℕ} (E : gInf B) (u : Fin k → ∀ v, B.H v)
    (hu : ∀ l v, u l v ∈ stepSpace (B.I.ε v) (B.lam v) (B.σ v) P) :
    HasDerivAt (orbit B E (∑ l, B.tens (u l)))
      (∑ l, ∑ v, B.tens (Function.update (u l) v
        (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct (B.σ v) (E v).1 (u l v)))) 0 := by
  rw [orbit_sum]
  refine HasDerivAt.fun_sum fun l _ => ?_
  exact GlobalTheory.TensDer.hasDerivAt_orbit_tens B E (u l) _
    (fun v => (hd v P _ (hu l v) _ (E v).2).hasDerivAt) (fun v => (hU v).1.1)

open Classical in

theorem dAct_atPlace_sum {P k : ℕ} (v : InfinitePlace B.I.F) (X : gLie (B.I.ε v))
    (u : Fin k → ∀ v, B.H v) (hu : ∀ l v, u l v ∈ stepSpace (B.I.ε v) (B.lam v) (B.σ v) P) :
    dAct B (atPlace B v X) (∑ l, B.tens (u l)) =
      ∑ l, B.tens (Function.update (u l) v (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct (B.σ v) X.1 (u l v))) := by
  obtain ⟨m, hm, -⟩ := GlobalTheory.rowsAut_tens_continuousMultilinear B
  unfold dAct
  rw [(hasDerivAt_orbit_sum hU hd (atPlace B v X) u hu).deriv]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single v]
  · simp [atPlace]
  · intro v' _ h
    have h0 : atPlace B v X v' = 0 := by simp [atPlace, h]
    have h1 : GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit (B.σ v') (0 : gLie (B.I.ε v')).1 (u l v') = fun _ => u l v' := by
      funext t
      simp [GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit, (hU v').1.1]
    rw [h0, ← hm]
    refine m.map_coord_zero v' ?_
    rw [Function.update_self, GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct, h1]
    simp
  · simp

open Classical in
theorem dAct_atPlace_tens {P : ℕ} (v : InfinitePlace B.I.F) (X : gLie (B.I.ε v))
    (u : ∀ v, B.H v) (hu : ∀ v, u v ∈ stepSpace (B.I.ε v) (B.lam v) (B.σ v) P) :
    dAct B (atPlace B v X) (B.tens u) =
      B.tens (Function.update u v (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct (B.σ v) X.1 (u v))) := by
  simpa using dAct_atPlace_sum hU hd (k := 1) v X (fun _ => u) (fun _ => hu)

theorem differentiableAt_orbit {P : ℕ} (E : gInf B) {w : B.Hs} (hw : w ∈ VP B P) :
    DifferentiableAt ℝ (orbit B E w) 0 := by
  obtain ⟨k, u, hu, rfl⟩ := GlobalTheory.StepTens.stepSpan_le_of_differentiable B hU hd P w hw
  exact (hasDerivAt_orbit_sum hU hd E u hu).differentiableAt

theorem dAct_eq_sum {P : ℕ} (E : gInf B) {w : B.Hs} (hw : w ∈ VP B P) :
    dAct B E w = ∑ v, dAct B (atPlace B v (E v)) w := by
  obtain ⟨k, u, hu, rfl⟩ := GlobalTheory.StepTens.stepSpan_le_of_differentiable B hU hd P w hw
  simp only [dAct_atPlace_sum hU hd _ _ u hu]
  rw [Finset.sum_comm]
  exact (hasDerivAt_orbit_sum hU hd E u hu).deriv

theorem dAct_mem {P : ℕ} (E : gInf B) {w : B.Hs} (hw : w ∈ VP B P) : dAct B E w ∈ VP B (P + 1) := by
  rw [dAct_eq_sum hU hd E hw]
  refine Submodule.sum_mem _ fun v _ => ?_
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, u, hl, hu, rfl⟩ := hx
    exact Submodule.subset_span ⟨⟨v, E v⟩ :: l, u, by simpa using hl, hu, rfl⟩
  | zero => rw [dAct_zero]; exact Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
    have := dAct_add_smul B (differentiableAt_orbit hU hd (atPlace B v (E v)) hx)
      (differentiableAt_orbit hU hd (atPlace B v (E v)) hy) 1
    rw [one_smul, one_smul] at this
    rw [this]
    exact Submodule.add_mem _ ihx ihy
  | smul c x hx ihx =>
    have := dAct_add_smul B
      (differentiableAt_orbit hU hd (atPlace B v (E v)) (Submodule.zero_mem (VP B P)))
      (differentiableAt_orbit hU hd (atPlace B v (E v)) hx) c
    rw [zero_add, dAct_zero, zero_add] at this
    rw [this]
    exact Submodule.smul_mem _ c ihx

theorem wordAct_conj (k : B.I.Ginf) (hk : ∀ v, uMat (k v) ∈ Formalism.REAL.Kset (B.I.ε v)) (u : ∀ v, B.H v)
    (hu : ∀ v, u v ∈ lowKSub (B.I.ε v) (B.lam v) (B.σ v))
    (l : List (Σ v : InfinitePlace B.I.F, gLie (B.I.ε v))) :
    ∃ l' : List (Σ v : InfinitePlace B.I.F, gLie (B.I.ε v)), l'.length = l.length ∧
      B.σs k (wordAct B l (B.tens u)) = wordAct B l' (B.σs k (B.tens u)) := by
  classical
  induction l with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons X l ih =>
    obtain ⟨v, X⟩ := X
    obtain ⟨l', h1, h2⟩ := ih
    obtain ⟨y, h3, h4⟩ := GlobalTheory.StepTens.wordAct_tens_of_diff B hU hd u hu l
    refine ⟨⟨v, ⟨uMat (k v) * X.1 * (uMat (k v))ᴴ, GlobalTheory.StepLoc.inG_conj (hk v) X.2⟩⟩ :: l',
      by simp [h1], ?_⟩
    change B.σs k (dAct B (atPlace B v X) (wordAct B l (B.tens u))) =
      dAct B (atPlace B v _) (wordAct B l' (B.σs k (B.tens u)))
    have h5 : ∀ v, B.σ v (uMat (k v)) (y v) ∈ stepSpace (B.I.ε v) (B.lam v) (B.σ v) l.length :=
      fun v => (GlobalTheory.StepLoc.stepSpace_props_of_diff B.I.n (B.I.ε v) (B.H v) (B.σ v) (B.lam v) (hU v)
        (hd v) l.length).1 _ (hk v) _ (h3 v)
    have hs : ∀ x, B.σs k (B.tens x) = B.tens fun v => B.σ v (uMat (k v)) (x v) :=
      fun x => B.tens_spec.2.1 k x
    rw [← h2, h4, dAct_atPlace_tens hU hd v X y h3, hs, hs, dAct_atPlace_tens hU hd v _ _ h5]
    congr 1
    funext v'
    by_cases h : v' = v
    · subst h
      simp only [Function.update_self]
      exact (GlobalTheory.StepLoc.dAct_conj (hU v').1 (hk v') X.2 (hd v' _ _ (h3 v') _ X.2)).symm
    · simp only [Function.update_of_ne h]

theorem stepSpan_stable {P : ℕ} (k : B.I.Ginf) (hk : ∀ v, uMat (k v) ∈ Formalism.REAL.Kset (B.I.ε v))
    {w : B.Hs} (hw : w ∈ VP B P) : B.σs k w ∈ VP B P := by
  have : VP B P ≤ (VP B P).comap (B.σs k : B.Hs →ₗ[ℂ] B.Hs) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨l, u, hl, hu, rfl⟩
    obtain ⟨l', h1, h2⟩ := wordAct_conj hU hd k hk u hu l
    change B.σs k (wordAct B l (B.tens u)) ∈ VP B P
    have hs : B.σs k (B.tens u) = B.tens fun v => B.σ v (uMat (k v)) (u v) := B.tens_spec.2.1 k u
    rw [h2, hs]
    exact Submodule.subset_span ⟨l', _, h1.trans_le hl,
      fun v => GlobalTheory.StepLoc.lowKSub_stable _ _ _ _ (hk v) _ (hu v), rfl⟩
  exact this hw

theorem finiteDimensional_VP {P : ℕ}
    (hf : ∀ v, FiniteDimensional ℂ (stepSpace (B.I.ε v) (B.lam v) (B.σ v) P)) :
    FiniteDimensional ℂ (VP B P) := by
  classical
  obtain ⟨m, hm, -⟩ := GlobalTheory.rowsAut_tens_continuousMultilinear B
  let L := PiTensorProduct.lift (m.toMultilinearMap.compLinearMap
    fun v => (stepSpace (B.I.ε v) (B.lam v) (B.σ v) P).subtype)
  have hle : VP B P ≤ LinearMap.range L := by
    intro w hw
    obtain ⟨k, u, hu, rfl⟩ := GlobalTheory.StepTens.stepSpan_le_of_differentiable B hU hd P w hw
    refine Submodule.sum_mem _ fun l _ => ⟨PiTensorProduct.tprod ℂ fun v => ⟨u l v, hu l v⟩, ?_⟩
    simp [L, hm]
  exact Submodule.finiteDimensional_of_le hle

theorem sum_normSq_dAct_le {P m : ℕ} (v : InfinitePlace B.I.F) (E : Fin m → gLie (B.I.ε v)) (β : ℝ)
    (hβ : ∀ y ∈ stepSpace (B.I.ε v) (B.lam v) (B.σ v) P,
      ∑ i, ‖GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct (B.σ v) (E i).1 y‖ ^ 2 ≤ β * ‖y‖ ^ 2)
    {w : B.Hs} (hw : w ∈ VP B P) : ∑ i, ‖dAct B (atPlace B v (E i)) w‖ ^ 2 ≤ β * ‖w‖ ^ 2 := by
  obtain ⟨k, u, hu, rfl⟩ := GlobalTheory.StepTens.stepSpan_le_of_differentiable B hU hd P w hw
  simp only [dAct_atPlace_sum hU hd _ _ u hu]
  let L : Fin m → (stepSpace (B.I.ε v) (B.lam v) (B.σ v) P →ₗ[ℂ] B.H v) := fun i =>
    { toFun := fun y => GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct (B.σ v) (E i).1 y
      map_add' := fun x y => by
        simpa using GlobalTheory.StepLoc.dAct_add_smul (hd v P _ x.2 _ (E i).2) (hd v P _ y.2 _ (E i).2) 1
      map_smul' := fun c x => by
        simpa [GlobalTheory.StepLoc.dAct_zero] using GlobalTheory.StepLoc.dAct_add_smul
          (hd v P _ (Submodule.zero_mem _) _ (E i).2) (hd v P _ x.2 _ (E i).2) c }
  exact GlobalTheory.sum_normSq_tens_update_le B v (fun v => stepSpace (B.I.ε v) (B.lam v) (B.σ v) P) m L β
    (fun y => hβ y y.2) k (fun l v => ⟨u l v, hu l v⟩)

end Diff

theorem card_places_le : Fintype.card (InfinitePlace B.I.F) ≤ B.I.f := by
  have h1 := InfinitePlace.card_add_two_mul_card_eq_rank B.I.F
  have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces B.I.F
  unfold AutInst.f
  omega

theorem stepBoundAt_of_local : ∀ (B : RowsAut) (b : ℝ), (∀ v, IsURepOn (UJset (B.I.ε v)) (B.σ v) ∧ (∀ P : ℕ, FiniteDimensional ℂ (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace (B.I.ε v) (B.lam v) (B.σ v) P) ∧ (∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace (B.I.ε v) (B.lam v) (B.σ v) P, GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.IsDiffVec (B.I.ε v) (B.σ v) w) ∧ (∀ F : Fin (B.I.n ^ 2) → Matrix (Fin B.I.n) (Fin B.I.n) ℂ, GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.IsONFamily (B.I.ε v) F → ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace (B.I.ε v) (B.lam v) (B.σ v) P, ∑ i, ‖GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct (B.σ v) (F i) w‖ ^ 2 ≤ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst B.I.n b P ^ 2 * ‖w‖ ^ 2) ∧ ∀ X, Formalism.REAL.inG (B.I.ε v) X → ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace (B.I.ε v) (B.lam v) (B.σ v) P, ‖GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct (B.σ v) X w‖ ≤ Real.sqrt (Formalism.REAL.hs X) * GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst B.I.n b P * ‖w‖)) → ∀ P : ℕ, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.StepBoundAt B b P := by
  intro B b h P
  have hU : ∀ v, IsURepOn (UJset (B.I.ε v)) (B.σ v) := fun v => (h v).1
  have hd : ∀ v P, ∀ w ∈ stepSpace (B.I.ε v) (B.lam v) (B.σ v) P, IsDiffVec (B.I.ε v) (B.σ v) w :=
    fun v Q => ((h v).2 Q).2.1
  have hb := beP_nonneg B.I.n b P
  have hone : ∀ (v : InfinitePlace B.I.F) (X : gLie (B.I.ε v)), ∀ w ∈ VP B P,
      ‖dAct B (atPlace B v X) w‖ ≤ Real.sqrt (Formalism.REAL.hs X.1) * beP B.I.n b P * ‖w‖ := by
    intro v X w hw
    have h1 := sum_normSq_dAct_le hU hd v (fun _ : Fin 1 => X)
      ((Real.sqrt (Formalism.REAL.hs X.1) * beP B.I.n b P) ^ 2) (fun y hy => by
        have h2 := ((h v).2 P).2.2.2 X.1 X.2 y hy
        rw [stepConst_eq] at h2
        rw [Fin.sum_univ_one, ← mul_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) h2 2) hw
    rw [Fin.sum_univ_one, ← mul_pow] at h1
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h1
  refine ⟨finiteDimensional_VP hU hd fun v => ((h v).2 P).1, fun k hk w hw => stepSpan_stable hU hd k hk hw,
    fun E w hw => differentiableAt_orbit hU hd E hw, ?_, hone, ?_, fun E w hw => dAct_mem hU hd E hw⟩
  · intro v m E hE w hw
    obtain rfl := card_of_isONBasis hE
    refine sum_normSq_dAct_le hU hd v E _ (fun y hy => ?_) hw
    rw [← stepConst_eq]
    exact ((h v).2 P).2.2.1 (fun i => (E i).1) ⟨fun i => (E i).2, hE.1⟩ y hy
  · intro E w hw
    have hs0 : ∀ v, 0 ≤ Formalism.REAL.hs (E v).1 := fun v => by
      unfold Formalism.REAL.hs
      positivity
    have hcs : ∑ v, Real.sqrt (Formalism.REAL.hs (E v).1) ≤
        Real.sqrt B.I.f * Real.sqrt (∑ v, Formalism.REAL.hs (E v).1) := by
      have h1 := Real.sum_sqrt_mul_sqrt_le Finset.univ (f := fun _ : InfinitePlace B.I.F => (1 : ℝ))
        (g := fun v => Formalism.REAL.hs (E v).1) (fun _ => zero_le_one) hs0
      simp only [Real.sqrt_one, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        mul_one] at h1
      refine h1.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _))
      exact_mod_cast card_places_le B
    rw [dAct_eq_sum hU hd E hw]
    calc _ ≤ ∑ v, ‖dAct B (atPlace B v (E v)) w‖ := norm_sum_le _ _
      _ ≤ ∑ v, Real.sqrt (Formalism.REAL.hs (E v).1) * beP B.I.n b P * ‖w‖ :=
        Finset.sum_le_sum fun v _ => hone v (E v) w hw
      _ = (∑ v, Real.sqrt (Formalism.REAL.hs (E v).1)) * beP B.I.n b P * ‖w‖ := by
        rw [Finset.sum_mul, Finset.sum_mul]
      _ ≤ _ := by gcongr

end GlobalTheory.StepGlob
