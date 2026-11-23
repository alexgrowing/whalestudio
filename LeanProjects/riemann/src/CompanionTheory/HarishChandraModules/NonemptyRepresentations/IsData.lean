import Formalism.HermitianCurvature.HermitianCurvatureProofs.InvariantOperatorUnderJacquet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QNFAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction
import Formalism.HermitianCurvature.CompositeFormulaLevelZero

open MeasureTheory Matrix

noncomputable section

namespace CompanionTheory.D.Inhab.IsDataInh

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5

def π0 (k r : ℕ) : Mx k r → (ℂ →L[ℂ] ℂ) := fun _ => ContinuousLinearMap.id ℂ ℂ

def z0 (k r : ℕ) : Fin (2 * r + k + 1) → ℂ := bvec (wI k r (Fin.last k))

def uTriv (k : ℕ) : ℕ → ℝ := fun i => ((k : ℝ) + 1) / 2 - i

theorem foldr_ofFn_smul {X : Type*} [AddCommGroup X] [Module ℂ X] :
    ∀ (t : ℕ) (c : Fin t → ℂ) (x : X),
      (List.ofFn fun j : Fin t => fun y : X => c j • y).foldr (fun T h => T h) x = (∏ j, c j) • x
  | 0, c, x => by simp
  | t + 1, c, x => by
    rw [List.ofFn_succ, List.foldr_cons, foldr_ofFn_smul t (fun j => c j.succ) x, Fin.prod_univ_succ, mul_smul]

theorem ecRep_const (k r : ℕ) (Z : Mx k r) (v : ℂ) : EcRep (Hpk k r) (π0 k r) Z v = 0 := by
  simp [EcRep, dRep, π0]

theorem capRep_const (k r m : ℕ) (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (w v : ℂ) :
    capRep k r (π0 k r) Bs w v = (∏ j : Fin m, (w - ((j : ℕ) : ℂ))) • v := by
  unfold capRep qmF
  simp only [ecRep_const, add_zero, id_eq]
  have hfun : ∀ σ : Equiv.Perm (Fin m),
      (List.ofFn fun i : Fin m => fun y : ℂ => if σ i = i then (w - ((i : ℕ) : ℂ)) • y else 0) =
        List.ofFn fun i : Fin m => fun y : ℂ => (if σ i = i then w - ((i : ℕ) : ℂ) else 0) • y := by
    intro σ
    congr 1
    funext i y
    split_ifs <;> simp
  simp only [hfun, foldr_ofFn_smul]
  rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin m))]
  · simp
  · intro σ _ hσ
    obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := not_forall.1 fun h => hσ (Equiv.ext h)
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])]
    simp
  · simp

theorem prod_uTriv (k : ℕ) (w : ℂ) :
    (∏ i ∈ Finset.Icc 1 k, (w - (k : ℂ) / 2 + 1 / 2 + ((uTriv k i : ℝ) : ℂ))) = ∏ j : Fin k, (w - ((j : ℕ) : ℂ)) := by
  have h1 : ∀ i ∈ Finset.Icc 1 k, (w - (k : ℂ) / 2 + 1 / 2 + ((uTriv k i : ℝ) : ℂ)) = w - ((i : ℂ) - 1) := by
    intro i _
    simp only [uTriv]
    push_cast
    ring
  rw [Finset.prod_congr rfl h1, Fin.prod_univ_eq_prod_range (fun j => w - (j : ℂ)) k]
  clear h1
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih, Finset.prod_range_succ]
    push_cast
    ring

theorem capParam_triv (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : ℕ → ℝ)
    (hu : ∀ i ∈ Finset.Icc 1 k, u i = uTriv k i) : CapParam k r z (π0 k r) u := by
  intro Bs _ w v
  rw [capRep_const, ← prod_uTriv k w]
  congr 1
  exact Finset.prod_congr rfl fun i hi => by rw [hu i hi]

theorem isType_triv (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : ℕ → ℝ)
    (hu : ∀ i ∈ Finset.Icc 1 k, u i = uTriv k i) : IsType k r z (π0 k r) u := by
  refine ⟨inferInstance, ⟨rfl, fun a _ b _ => (ContinuousLinearMap.id_comp _).symm⟩, continuousOn_const,
    fun h _ v => by simp [π0], fun S _ => Ideal.eq_bot_or_top S, capParam_triv k r z u hu⟩

theorem par_ok (P : M.Par) (hk : 1 ≤ P.k) (hT : P.T = 1) (hT' : P.T' = 1) (huu : P.u' = P.u)
    (hu : ∀ i ∈ Finset.Icc 1 P.k, P.u i = uTriv P.k i) : P.OK := by
  have h1 : P.u 1 = uTriv P.k 1 := hu 1 (Finset.mem_Icc.2 ⟨le_rfl, hk⟩)
  refine ⟨hk, by rw [hT]; norm_num, by rw [hT']; norm_num, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · refine ⟨1 - (i : ℤ), ?_⟩
    rw [hu i hi, h1]; simp only [uTriv]; push_cast; ring
  · refine ⟨1 - (i : ℤ), ?_⟩
    rw [huu, hu i hi, h1]; simp only [uTriv]; push_cast; ring
  · have hi' := Finset.mem_Icc.1 hi
    have ha : P.u i = uTriv P.k i := hu i (Finset.mem_Icc.2 ⟨hi'.1, by omega⟩)
    have hb : P.u (i + 1) = uTriv P.k (i + 1) := hu (i + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    simp only [M.Par.lo, M.Par.hi, huu, max_self, min_self, ha, hb, uTriv]
    push_cast
    linarith

theorem isPlace_triv (P : M.Par) (hk : 1 ≤ P.k) (hT : P.T = 1) (hT' : P.T' = 1) (huu : P.u' = P.u)
    (hu : ∀ i ∈ Finset.Icc 1 P.k, P.u i = uTriv P.k i) :
    IsPlace P (z0 P.k P.r) (z0 P.k P.r) (π0 P.k P.r) (π0 P.k P.r) := by
  obtain ⟨hz, hTz⟩ := Formalism.FourierDecayAlt.P.base_vector_exists P.k P.r
  exact ⟨par_ok P hk hT hT' huu hu, hz, hz, by rw [z0, hTz, hT], by rw [z0, hTz, hT'],
    isType_triv _ _ _ _ hu, isType_triv _ _ _ _ (by rw [huu]; exact hu)⟩

theorem glev_last_eq (k r : ℕ) : Glev k r (Fin.last r) = B2.UWb k r := by
  ext g
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, fun a => h2 a (by simp)⟩, fun ⟨h1, h2⟩ => ⟨h1, fun a _ => h2 a⟩⟩

theorem haar_glev_last (k r : ℕ) : ∃ μ : Measure (Mt k r), B.IsHaarOn (Glev k r (Fin.last r)) μ := by
  rw [glev_last_eq]
  exact Formalism.FourierDecayAlt.P.opposite_weyl_haar_exists k r

theorem isData_of_place {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Mx P.k P.r → (Wq →L[ℂ] Wq))
    (hP : IsPlace P z z' π π') (μ : Measure (Mt P.k P.r)) (hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ)
    (l0 : ℕ) :
    ∃ (X : ActualOps P.k P.r z z' π π') (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r)
      (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))), IsData P z z' π π' X μ L st l0 := by
  obtain ⟨X⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist Wp Wq P z z' π π' hP
  obtain ⟨L, st, h1, h2, h3, h4, h5, h6⟩ := Formalism.FourierDecayAlt.P.level_start_actual Wp Wq P z z' π π' hP X l0
  exact ⟨X, L, st, hP, hμ, h1, h2, h3, h4, h5, h6⟩

def placeRankTwoOne : M.Par := ⟨2, 1, 1, 1, uTriv 2, uTriv 2⟩

def product_first_partition : M.Par := ⟨1, 1, 1, 1, uTriv 1, uTriv 1⟩

theorem isPlace_rank_two_one : IsPlace placeRankTwoOne (z0 2 1) (z0 2 1) (π0 2 1) (π0 2 1) :=
  isPlace_triv placeRankTwoOne (by decide) rfl rfl rfl fun _ _ => rfl

theorem isPlace_rank_one_one : IsPlace product_first_partition (z0 1 1) (z0 1 1) (π0 1 1) (π0 1 1) :=
  isPlace_triv product_first_partition le_rfl rfl rfl rfl fun _ _ => rfl

theorem isData_rank_two_one (l0 : ℕ) :
    ∃ (X : ActualOps placeRankTwoOne.k placeRankTwoOne.r (z0 2 1) (z0 2 1) (π0 2 1) (π0 2 1)) (μ : Measure (Mt 2 1))
      (L : R.LevelData (Pr (RadSp placeRankTwoOne.k placeRankTwoOne.r (z0 2 1) (z0 2 1) (π0 2 1) (π0 2 1))) placeRankTwoOne.r)
      (st : Fr.Start (Pr (RadSp placeRankTwoOne.k placeRankTwoOne.r (z0 2 1) (z0 2 1) (π0 2 1) (π0 2 1)))),
      IsData placeRankTwoOne (z0 2 1) (z0 2 1) (π0 2 1) (π0 2 1) X μ L st l0 := by
  obtain ⟨μ, hμ⟩ := haar_glev_last 2 1
  obtain ⟨X, L, st, h⟩ := isData_of_place placeRankTwoOne _ _ _ _ isPlace_rank_two_one μ hμ l0
  exact ⟨X, μ, L, st, h⟩

theorem isData_rank_one_one (l0 : ℕ) :
    ∃ (X : ActualOps product_first_partition.k product_first_partition.r (z0 1 1) (z0 1 1) (π0 1 1) (π0 1 1)) (μ : Measure (Mt 1 1))
      (L : R.LevelData (Pr (RadSp product_first_partition.k product_first_partition.r (z0 1 1) (z0 1 1) (π0 1 1) (π0 1 1))) product_first_partition.r)
      (st : Fr.Start (Pr (RadSp product_first_partition.k product_first_partition.r (z0 1 1) (z0 1 1) (π0 1 1) (π0 1 1)))),
      IsData product_first_partition (z0 1 1) (z0 1 1) (π0 1 1) (π0 1 1) X μ L st l0 := by
  obtain ⟨μ, hμ⟩ := haar_glev_last 1 1
  obtain ⟨X, L, st, h⟩ := isData_of_place product_first_partition _ _ _ _ isPlace_rank_one_one μ hμ l0
  exact ⟨X, μ, L, st, h⟩

end CompanionTheory.D.Inhab.IsDataInh
