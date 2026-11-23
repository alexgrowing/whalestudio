import Formalism.HermitianCurvature.StatementJCT
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InvariantOperatorUnderJacquet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QNFAsm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelTransfer.SecondCapelliMinorLevel
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelLiftBasics.LevelGroupUnitaryHermitian
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelImageArithmetic.GlevImageOf

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.JCTx5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section typ

variable {k i r' : ℕ}

theorem liftVec_inj {v w : Fin (2 * r' + k + 1) → ℂ} (h : liftVec k i r' v = liftVec k i r' w) : v = w := by
  funext j
  have hjl := j.isLt
  have hj := congrFun h ⟨j.val + i, by omega⟩
  have hc : i ≤ j.val + i ∧ j.val + i < 2 * r' + k + 1 + i := ⟨Nat.le_add_left _ _, by omega⟩
  simp only [liftVec, Fin.val_mk, dif_pos hc] at hj
  first
    | simpa using hj
    | (simp at hj; rwa [if_pos (by omega)] at hj)

private theorem levPos_injective : Function.Injective (levPos k i r') := by
  intro a b h
  apply Fin.ext
  have h' := congrArg Fin.val h
  simp only [levPos, Fin.val_mk] at h'
  omega

private theorem liftVec_apply_levPos (x : Fin (2 * r' + k + 1) → ℂ) (j : Fin (2 * r' + k + 1)) :
    liftVec k i r' x (levPos k i r' j) = x j := by
  have hj := j.isLt
  have hj' : (j : ℕ) ≤ 2 * r' + k := by omega
  simp [liftVec, levPos, hj']
  all_goals first
    | (intro h; omega)
    | rw [if_pos hj']
    | rfl

private theorem liftVec_apply_eq_zero_of_not_mem_range (x : Fin (2 * r' + k + 1) → ℂ) (p : Fin (2 * (i + r') + k + 1))
    (hp : p ∉ Set.range (levPos k i r')) : liftVec k i r' x p = 0 := by
  simp only [liftVec]
  split_ifs with hc
  · exfalso
    apply hp
    refine ⟨⟨p.val - i, by omega⟩, ?_⟩
    apply Fin.ext
    simp only [levPos, Fin.val_mk]
    omega
  · rfl

private theorem liftVec_dotProduct_eq_dotProduct_levPos (x : Fin (2 * r' + k + 1) → ℂ) (w : Fin (2 * (i + r') + k + 1) → ℂ) :
    liftVec k i r' x ⬝ᵥ w = x ⬝ᵥ (fun j => w (levPos k i r' j)) := by
  unfold dotProduct
  symm
  apply Fintype.sum_of_injective (levPos k i r') levPos_injective
  · intro p hp
    simp only [liftVec_apply_eq_zero_of_not_mem_range x p hp, zero_mul]
  · intro j
    simp only [liftVec_apply_levPos]

private theorem hpk_levPos_levPos (j q : Fin (2 * r' + k + 1)) :
    Hpk k (i + r') (levPos k i r' j) (levPos k i r' q) = Hpk k r' j q := by
  obtain ⟨jv, hjv⟩ := j
  obtain ⟨qv, hqv⟩ := q
  simp only [Hpk, levPos, Fin.ext_iff, Fin.val_mk]
  have e1 : (jv + i < i + r' ∧ jv + i + (qv + i) = 2 * (i + r') + k) ↔ (jv < r' ∧ jv + qv = 2 * r' + k) := by
    omega
  have e2 : (qv + i < i + r' ∧ jv + i + (qv + i) = 2 * (i + r') + k) ↔ (qv < r' ∧ jv + qv = 2 * r' + k) := by
    omega
  have e3 : (i + r' ≤ jv + i ∧ jv + i ≤ i + r' + k ∧ jv + i = qv + i) ↔ (r' ≤ jv ∧ jv ≤ r' + k ∧ jv = qv) := by
    omega
  have e4 : (jv + i = i + r' + k) ↔ (jv = r' + k) := by
    omega
  simp only [e1, e2, e3, e4]

private theorem hpk_levPos_apply_eq_zero_of_outside (j : Fin (2 * r' + k + 1)) (q : Fin (2 * (i + r') + k + 1))
    (hq : ¬(i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i)) :
    Hpk k (i + r') (levPos k i r' j) q = 0 := by
  have hj := j.isLt
  have hq' := q.isLt
  simp only [Hpk, levPos, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> (try split_ifs) <;> (try split_ifs) <;> first | rfl | (exfalso; omega)

private theorem hpk_mulVec_liftVec_apply_levPos (x : Fin (2 * r' + k + 1) → ℂ) (j : Fin (2 * r' + k + 1)) :
    (Hpk k (i + r') *ᵥ liftVec k i r' x) (levPos k i r' j) = (Hpk k r' *ᵥ x) j := by
  simp only [Matrix.mulVec]
  rw [dotProduct_comm, liftVec_dotProduct_eq_dotProduct_levPos]
  simp only [hpk_levPos_levPos]
  exact dotProduct_comm _ _

private theorem star_liftVec (y : Fin (2 * r' + k + 1) → ℂ) :
    star (liftVec k i r' y) = liftVec k i r' (star y) := by
  funext p
  simp only [liftVec, Pi.star_apply]
  split_ifs <;> simp

private theorem herm_hpk_liftVec_liftVec (x y : Fin (2 * r' + k + 1) → ℂ) :
    herm (Hpk k (i + r')) (liftVec k i r' x) (liftVec k i r' y) = herm (Hpk k r') x y := by
  unfold herm
  rw [star_liftVec, liftVec_dotProduct_eq_dotProduct_levPos]
  congr 1
  funext j
  exact hpk_mulVec_liftVec_apply_levPos x j

private theorem herm_bvec_liftVec_eq_zero_of_outside (y : Fin (2 * r' + k + 1) → ℂ) (q : Fin (2 * (i + r') + k + 1))
    (hq : ¬(i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i)) :
    herm (Hpk k (i + r')) (bvec q) (liftVec k i r' y) = 0 := by
  unfold herm
  rw [star_liftVec, liftVec_dotProduct_eq_dotProduct_levPos]
  have h0 : (fun j => (Hpk k (i + r') *ᵥ bvec q) (levPos k i r' j)) = 0 := by
    funext j
    simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply, hpk_levPos_apply_eq_zero_of_outside j q hq]
  rw [h0, dotProduct_zero]

private theorem liftVec_apply_of_mid (x : Fin (2 * r' + k + 1) → ℂ) (p : Fin (2 * (i + r') + k + 1))
    (hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i) : liftVec k i r' x p = x ⟨p.val - i, by omega⟩ := by
  simp only [liftVec]
  rw [dif_pos hp]

private theorem bvec_eq_liftVec_bvec_of_mid (q : Fin (2 * (i + r') + k + 1)) (hq : i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i) :
    bvec q = liftVec k i r' (bvec (⟨q.val - i, by omega⟩ : Fin (2 * r' + k + 1))) := by
  funext p
  simp only [bvec, liftVec, Pi.single_apply, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> (try split_ifs) <;> (try split_ifs) <;> first | rfl | (exfalso; omega)

theorem unitB_lift {m : ℕ} (Bs : Fin m → Fin (2 * r' + k + 1) → ℂ) (a b : Fin m) :
    unitB (Hpk k (i + r')) (fun c => liftVec k i r' (Bs c)) a b =
      PIQnLT.Lz k i r' (unitB (Hpk k r') Bs a b) := by
  unfold unitB
  ext p q
  unfold PIQnLT.Lz
  simp only [Matrix.of_apply]
  by_cases hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i
  · by_cases hq : i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i
    · rw [dif_pos hp, dif_pos hq, liftVec_apply_of_mid _ p hp, bvec_eq_liftVec_bvec_of_mid q hq, herm_hpk_liftVec_liftVec]
    · rw [dif_pos hp, dif_neg hq, herm_bvec_liftVec_eq_zero_of_outside _ q hq, mul_zero]
  · rw [dif_neg hp]
    have h0 : liftVec k i r' (Bs a) p = 0 := by
      simp only [liftVec]
      rw [dif_neg hp]
    rw [h0, zero_mul]

theorem hpart1_Lz (Z : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    hpart1 (Hpk k (i + r')) (PIQnLT.Lz k i r' Z) = PIQnLT.Lz k i r' (hpart1 (Hpk k r') Z) := by
  unfold hpart1
  rw [PIQnLT.hpk_inv, PIQnLT.hpk_inv, PIQnLT.Lz_conjTranspose, PIQnLT.hpk_mul_Lz, PIQnLT.Lz_mul_hpk,
    PIQnLT.Lz_smul, PIQnLT.Lz_sub]

theorem hpart2_Lz (Z : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    hpart2 (Hpk k (i + r')) (PIQnLT.Lz k i r' Z) = PIQnLT.Lz k i r' (hpart2 (Hpk k r') Z) := by
  unfold hpart2
  rw [PIQnLT.hpk_inv, PIQnLT.hpk_inv, PIQnLT.Lz_conjTranspose, PIQnLT.hpk_mul_Lz, PIQnLT.Lz_mul_hpk,
    PIQnLT.Lz_smul, PIQnLT.Lz_add]

variable {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]

theorem dRep_Lz (π0 : Mx k (i + r') → (Wp →L[ℂ] Wp)) (X : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ)
    (v : Wp) : dRep π0 (PIQnLT.Lz k i r' X) v = dRep (fun y => π0 (ιLev k i r' y)) X v := by
  unfold dRep
  congr 1
  funext t
  rw [← PIQnLT.Lz_smul, PIQnLT.exp_Lz PI.QnLevBasicsW.level_group_homomorphism]

theorem ecRep_Lz (π0 : Mx k (i + r') → (Wp →L[ℂ] Wp)) (Z : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ)
    (v : Wp) : EcRep (Hpk k (i + r')) π0 (PIQnLT.Lz k i r' Z) v =
      EcRep (Hpk k r') (fun y => π0 (ιLev k i r' y)) Z v := by
  unfold EcRep
  rw [hpart1_Lz, hpart2_Lz, dRep_Lz, dRep_Lz]

theorem capRep_lift {m : ℕ} (π0 : Mx k (i + r') → (Wp →L[ℂ] Wp)) (Bs : Fin m → Fin (2 * r' + k + 1) → ℂ)
    (w : ℂ) (v : Wp) :
    capRep k (i + r') π0 (fun c => liftVec k i r' (Bs c)) w v = capRep k r' (fun y => π0 (ιLev k i r' y)) Bs w v := by
  unfold capRep
  have e : (fun a b => EcRep (Hpk k (i + r')) π0 (unitB (Hpk k (i + r')) (fun c => liftVec k i r' (Bs c)) a b)) =
      (fun a b => EcRep (Hpk k r') (fun y => π0 (ιLev k i r' y)) (unitB (Hpk k r') Bs a b)) := by
    funext a b x
    rw [unitB_lift, ecRep_Lz]
  rw [e]

theorem frame_lift {m : ℕ} (z : Fin (2 * r' + k + 1) → ℂ) (Bs : Fin m → Fin (2 * r' + k + 1) → ℂ)
    (h : IsFrameOf k r' [z] Bs) : IsFrameOf k (i + r') [liftVec k i r' z] (fun c => liftVec k i r' (Bs c)) := by
  unfold IsFrameOf at h ⊢
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun a => ?_, fun a b => ?_, fun a v hv => ?_⟩
  · unfold inWb at h1 ⊢
    intro p hp
    dsimp only
    by_cases hm : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i
    · rw [liftVec_apply_of_mid _ p hm]
      exact h1 a _ (show p.val - i < r' ∨ r' + k < p.val - i by omega)
    · simp only [liftVec]
      rw [dif_neg hm]
  · simp only [herm_hpk_liftVec_liftVec]
    exact h2 a b
  · simp only [List.mem_singleton] at hv
    subst hv
    simp only [herm_hpk_liftVec_liftVec]
    exact h3 a z (List.mem_singleton_self z)

theorem continuous_ιLev : Continuous (ιLev k i r') := by
  refine continuous_matrix fun p q => ?_
  simp only [ιLev]
  split_ifs
  all_goals first
    | exact continuous_const
    | exact continuous_id.matrix_elem _ _
    | exact (continuous_apply _).comp (continuous_apply _)
    | fun_prop

theorem uw_onto (z : Fin (2 * r' + k + 1) → ℂ) (g : Mx k (i + r')) (hg : g ∈ UWset k (i + r') (liftVec k i r' z)) :
    ∃ y ∈ UWset k r' z, ιLev k i r' y = g := by
  have hG : g ∈ Glev k (i + r') ⟨i, by omega⟩ := ⟨hg.1, fun a _ => hg.2.1 a⟩
  rw [QnGlevImageW.glevImage_of PI.QnLevBasicsW.level_group_homomorphism PI.QnLevBasicsW.level_group_unitary_hermitian k i r'] at hG
  obtain ⟨y, hy, rfl⟩ := hG
  refine ⟨y, ⟨hy, fun a => ?_, ?_⟩, rfl⟩
  · have ha := a.isLt
    obtain ⟨h1, h2⟩ := hg.2.1 ⟨a.val + i, by omega⟩
    have e1 : bvec (eI k (i + r') ⟨a.val + i, by omega⟩) = liftVec k i r' (bvec (eI k r' a)) := by
      rw [← PIQnLT.bvec_lev]; congr 1; all_goals (ext; simp [eI, levPos])
    have e2 : bvec (esI k (i + r') ⟨a.val + i, by omega⟩) = liftVec k i r' (bvec (esI k r' a)) := by
      rw [← PIQnLT.bvec_lev]; congr 1; all_goals (ext; simp [esI, levPos]; try omega)
    rw [e1, PIQnLT.mulVec_liftVec] at h1
    rw [e2, PIQnLT.mulVec_liftVec] at h2
    exact ⟨liftVec_inj h1, liftVec_inj h2⟩
  · have h := hg.2.2
    rw [PIQnLT.mulVec_liftVec] at h
    exact liftVec_inj h

theorem isType_lev (z : Fin (2 * r' + k + 1) → ℂ) (π0 : Mx k (i + r') → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ)
    (h0 : IsType k (i + r') (liftVec k i r' z) π0 u) :
    IsType k r' z (fun y => π0 (ιLev k i r' y)) u := by
  obtain ⟨hnt, hrep, hcont, huni, hirr, hcap⟩ := h0
  have hmem : ∀ y ∈ UWset k r' z, ιLev k i r' y ∈ UWset k (i + r') (liftVec k i r' z) :=
    fun y hy => PI.QnLevBasicsW.level_group_unitary_weyl k i r' z y hy
  refine ⟨hnt, ⟨?_, fun a ha b hb => ?_⟩, ?_, fun h hh v => huni _ (hmem h hh) v, fun S hS => hirr S ?_, ?_⟩
  · show π0 (ιLev k i r' 1) = 1
    rw [(PI.QnLevBasicsW.level_group_homomorphism k i r').1]; exact hrep.1
  · show π0 (ιLev k i r' (a * b)) = (π0 (ιLev k i r' a)).comp (π0 (ιLev k i r' b))
    rw [(PI.QnLevBasicsW.level_group_homomorphism k i r').2]; exact hrep.2 _ (hmem a ha) _ (hmem b hb)
  · exact hcont.comp continuous_ιLev.continuousOn (fun y hy => hmem y hy)
  · intro h hh v hv
    obtain ⟨y, hy, rfl⟩ := uw_onto z h hh
    exact hS y hy v hv
  · intro Bs hBs w v
    rw [← capRep_lift]
    exact hcap _ (frame_lift z Bs hBs) w v

end typ

section cast

variable {k : ℕ}

theorem castV_rfl {a : ℕ} (v : Fin (2 * a + k + 1) → ℂ) : Formalism.FourierDecayAlt.D.castV (k := k) (rfl : a = a) v = v := by
  first
    | rfl
    | (funext j; simp [Formalism.FourierDecayAlt.D.castV])

theorem castM_rfl {a : ℕ} (g : Formalism.FourierDecayAlt.B.Mat k a) : Formalism.FourierDecayAlt.D.castM (rfl : a = a) g = g := by
  first
    | rfl
    | (ext p q; simp [Formalism.FourierDecayAlt.D.castM])

theorem isType_cast {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] {a b : ℕ} (h : a = b)
    (z : Fin (2 * a + k + 1) → ℂ) (π : Mx k b → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ)
    (hT : IsType k b (Formalism.FourierDecayAlt.D.castV h z) π u) : IsType k a z (fun g => π (Formalism.FourierDecayAlt.D.castM h g)) u := by
  subst h
  simpa only [castV_rfl, castM_rfl] using hT

theorem tz_cast {a b : ℕ} (h : a = b) (z : Fin (2 * a + k + 1) → ℂ) :
    Tz k b (Formalism.FourierDecayAlt.D.castV h z) = Tz k a z := by
  subst h
  rw [castV_rfl]

end cast

theorem isPlace_lev {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (P : M.Par) (T : Formalism.FourierDecayAlt.D.LevTower P.k P.r Wp Wq) (j : Fin (P.r + 1))
    (h0 : IsPlace P T.base.z T.base.z' T.base.π T.base.π') :
    IsPlace (Formalism.FourierDecayAlt.JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' := by
  obtain ⟨hOK, -, -, hT, hT', hty, hty'⟩ := h0
  have hjr : (j : ℕ) ≤ P.r := Nat.lt_succ_iff.mp j.isLt
  have hj : (j : ℕ) + (P.r - j) = P.r := by omega
  have ez : Formalism.FourierDecayAlt.D.castV hj (liftVec P.k j (P.r - j) (T.bs j).z) = T.base.z := T.z_lev j hjr
  have ez' : Formalism.FourierDecayAlt.D.castV hj (liftVec P.k j (P.r - j) (T.bs j).z') = T.base.z' := T.z'_lev j hjr
  have hπ : (T.bs j).π = fun y => T.base.π (Formalism.FourierDecayAlt.D.castM hj (ιLev P.k j (P.r - j) y)) :=
    funext fun y => T.π_lev j hjr y
  have hπ' : (T.bs j).π' = fun y => T.base.π' (Formalism.FourierDecayAlt.D.castM hj (ιLev P.k j (P.r - j) y)) :=
    funext fun y => T.π'_lev j hjr y
  have hWb := PI.QnLevBasicsW.level_group_isotropic_vector P.k j (P.r - j) (T.bs j).z (T.bs j).z_mem
  have hWb' := PI.QnLevBasicsW.level_group_isotropic_vector P.k j (P.r - j) (T.bs j).z' (T.bs j).z'_mem
  refine ⟨⟨hOK.k_pos, hOK.T_pos, hOK.T'_pos, hOK.int_u, hOK.int_u', hOK.gap⟩, (T.bs j).z_mem, (T.bs j).z'_mem,
    ?_, ?_, ?_, ?_⟩
  · show Tz P.k (P.r - j) (T.bs j).z = P.T
    rw [← hWb.2, ← tz_cast hj, ez, hT]
  · show Tz P.k (P.r - j) (T.bs j).z' = P.T'
    rw [← hWb'.2, ← tz_cast hj, ez', hT']
  · rw [hπ]
    exact isType_lev (i := j) (r' := P.r - j) (T.bs j).z (fun g => T.base.π (Formalism.FourierDecayAlt.D.castM hj g)) P.u
      (isType_cast hj (liftVec P.k j (P.r - j) (T.bs j).z) T.base.π P.u (by rw [ez]; exact hty))
  · rw [hπ']
    exact isType_lev (i := j) (r' := P.r - j) (T.bs j).z' (fun g => T.base.π' (Formalism.FourierDecayAlt.D.castM hj g)) P.u'
      (isType_cast hj (liftVec P.k j (P.r - j) (T.bs j).z') T.base.π' P.u' (by rw [ez']; exact hty'))

section haar

theorem exists_haar_level_zero {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {k a : ℕ} (h : a = 0) (Bs : Formalism.FourierDecayAlt.B.RealPlaceData k a Wp Wq) :
    ∃ μ : Measure (Mt k 0), Formalism.FourierDecayAlt.B.IsHaarOn (Formalism.FourierDecayAlt.B.GV k 0) μ := by
  subst h
  first
    | exact ⟨Bs.μG, Bs.haarG⟩
    | (cases Bs
       refine ⟨_, ?_⟩
       assumption)

def embL (k r' : ℕ) (x : Mt k 0) : Mt k r' := ιLev k r' 0 x

def projL (k r' : ℕ) (x : Mt k r') : Mt k 0 := fun p q => x (levPos k r' 0 p) (levPos k r' 0 q)

variable {k r' : ℕ}

theorem continuous_embL : Continuous (embL k r') := by
  first
    | exact continuous_ιLev
    | (unfold embL; exact continuous_ιLev)

theorem continuous_projL : Continuous (projL k r') := by
  unfold projL
  first
    | fun_prop
    | exact continuous_pi fun p => continuous_pi fun q => continuous_apply_apply _ _

theorem projL_embL (x : Mt k 0) : projL k r' (embL k r' x) = x := by
  funext p q
  have hp := p.isLt
  have hq := q.isLt
  have hp' : (p : ℕ) ≤ k := by omega
  have hq' : (q : ℕ) ≤ k := by omega
  simp [projL, embL, ιLev, levPos, hp', hq']

theorem glev_closed (k r : ℕ) (i : Fin (r + 1)) : IsClosed (Glev k r i) := by
  unfold Glev
  simp only [Set.setOf_and, Set.setOf_forall, Set.setOf_mem_eq]
  refine IsClosed.inter ?_ (isClosed_iInter fun a => isClosed_iInter fun _ => IsClosed.inter ?_ ?_)
  · unfold UH
    first
      | exact isClosed_eq (by fun_prop) continuous_const
      | exact isClosed_eq (((continuous_id.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul continuous_id) continuous_const
  all_goals first
    | exact isClosed_eq (by fun_prop) continuous_const
    | exact isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const

theorem glev_measurable (k r : ℕ) (i : Fin (r + 1)) : @MeasurableSet (Mt k r) _ (Glev k r i) := by
  first
    | exact (glev_closed k r i).measurableSet
    | exact IsClosed.measurableSet (α := Mt k r) (glev_closed k r i)
    | exact @IsClosed.measurableSet (Mt k r) _ _ _ _ (glev_closed k r i)

theorem haar_glev (μ0 : Measure (Mt k 0)) (h0 : Formalism.FourierDecayAlt.B.IsHaarOn (Formalism.FourierDecayAlt.B.GV k 0) μ0) :
    Formalism.FourierDecayAlt.B.IsHaarOn (Glev k r' (Fin.last r')) (μ0.map (embL k r')) := by
  have hU : Glev k r' (Fin.last r') = ιLev k r' 0 '' UH (Hpk k 0) :=
    QnGlevImageW.glevImage_of PI.QnLevBasicsW.level_group_homomorphism PI.QnLevBasicsW.level_group_unitary_hermitian k r' 0
  have hm : Measurable (embL k r') := continuous_embL.measurable
  have hhom := PI.QnLevBasicsW.level_group_homomorphism k r' 0
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine (Measure.map_apply hm (glev_measurable k r' (Fin.last r')).compl).trans ?_
    apply measure_mono_null _ h0.conc
    intro x hx hxG
    apply hx
    rw [hU]; exact ⟨x, hxG, rfl⟩
  · intro a ha
    rw [hU] at ha
    obtain ⟨a0, ha0, rfl⟩ := ha
    have hl : Measurable (lmulM (k := k) (r := r') (ιLev k r' 0 a0)) :=
      Continuous.measurable (by unfold lmulM; exact continuous_const.matrix_mul continuous_id)
    have hl0 : Measurable (lmulM (k := k) (r := 0) a0) :=
      Continuous.measurable (by unfold lmulM; exact continuous_const.matrix_mul continuous_id)
    rw [Measure.map_map hl hm]
    have e : lmulM (ιLev k r' 0 a0) ∘ embL k r' = embL k r' ∘ lmulM a0 := by
      funext x; simp only [Function.comp_apply, lmulM, embL]; rw [hhom.2]; rfl
    rw [e, ← Measure.map_map hm hl0, h0.left a0 ha0]
  · intro a ha
    rw [hU] at ha
    obtain ⟨a0, ha0, rfl⟩ := ha
    have hl : Measurable (Formalism.FourierDecayAlt.B.rmulF (n := 2 * r' + k + 1) (ιLev k r' 0 a0)) :=
      Continuous.measurable (by unfold Formalism.FourierDecayAlt.B.rmulF; exact continuous_id.matrix_mul continuous_const)
    have hl0 : Measurable (Formalism.FourierDecayAlt.B.rmulF (n := 2 * 0 + k + 1) a0) :=
      Continuous.measurable (by unfold Formalism.FourierDecayAlt.B.rmulF; exact continuous_id.matrix_mul continuous_const)
    rw [Measure.map_map hl hm]
    have e : Formalism.FourierDecayAlt.B.rmulF (ιLev k r' 0 a0) ∘ embL k r' = embL k r' ∘ Formalism.FourierDecayAlt.B.rmulF a0 := by
      funext x; simp only [Function.comp_apply, Formalism.FourierDecayAlt.B.rmulF, embL]; rw [hhom.2]; rfl
    rw [e, ← Measure.map_map hm hl0, h0.right a0 ha0]
  · intro K hK
    rw [Measure.map_apply hm hK.isClosed.measurableSet]
    refine lt_of_le_of_lt (measure_mono ?_) (h0.finite_compact _ (hK.image continuous_projL))
    intro x hx
    exact ⟨embL k r' x, hx, projL_embL x⟩
  · intro h
    exact h0.ne_zero ((Measure.map_eq_zero_iff hm.aemeasurable).mp h)

end haar

section cut

theorem anti_of (U : ℕ → ℝ) (k : ℕ) (hU : ∀ i, 1 ≤ i → i ≤ k - 1 → U (i + 1) ≤ U i) :
    ∀ a b, 1 ≤ a → a ≤ b → b ≤ k → U b ≤ U a := by
  intro a b ha hab
  induction b, hab using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ n hn ih =>
    intro hbk
    exact le_trans (hU n (by omega) (by omega)) (ih (by omega))

theorem cut_facts (U U' : ℕ → ℝ) (k l : ℕ) (hl1 : 1 ≤ l) (hlk : l ≤ k)
    (hgap : ∀ i, 1 ≤ i → i ≤ k - 1 →
      U (i + 1) ≤ U i - 1 ∧ U' (i + 1) ≤ U' i - 1 ∧ U (i + 1) ≤ U' i - 1 ∧ U' (i + 1) ≤ U i - 1)
    (y : ℝ) (hy : U l + 2 ≤ -y ∧ -y ≤ U' l - 2) :
    (∀ i, 1 ≤ i → i ≤ k - 1 → ∀ ρi : ℝ, U (i + 1) + 1 / 2 ≤ ρi → U' (i + 1) + 1 / 2 ≤ ρi →
      ρi ≤ U i - 1 / 2 → ρi ≤ U' i - 1 / 2 → ∀ e : ℝ, -1 ≤ e → e ≤ 1 → y + e + ρi ≠ 0) ∧
    (∀ i, 1 ≤ i → i ≤ k → ∀ e : ℝ, -1 ≤ e → e ≤ 0 → y + e + 1 / 2 + U i ≠ 0 ∧ y + e + 1 / 2 + U' i ≠ 0) := by
  have hA : ∀ a b, 1 ≤ a → a ≤ b → b ≤ k → U b ≤ U a :=
    anti_of U k (fun i h1 h2 => by linarith [(hgap i h1 h2).1])
  have hA' : ∀ a b, 1 ≤ a → a ≤ b → b ≤ k → U' b ≤ U' a :=
    anti_of U' k (fun i h1 h2 => by linarith [(hgap i h1 h2).2.1])
  obtain ⟨hy1, hy2⟩ := hy
  refine ⟨?_, ?_⟩
  · intro i hi1 hik ρi h1 h2 h3 h4 e he1 he2 h
    rcases Nat.lt_or_ge i l with hli | hli
    · have h5 := hA' (i + 1) l (by omega) (by omega) hlk
      linarith
    · have h5 := hA l i hl1 hli (by omega)
      linarith
  · intro i hi1 hik e he1 he2
    constructor
    · intro h
      rcases Nat.lt_or_ge i l with hli | hli
      · have h5 := hA' (i + 1) l (by omega) (by omega) hlk
        have h6 := (hgap i hi1 (by omega)).2.2.2
        linarith
      · have h5 := hA l i hl1 hli hik
        linarith
    · intro h
      rcases Nat.lt_or_ge l i with hli | hli
      · have h5 := hA l (i - 1) hl1 (by omega) (by omega)
        have h6 := (hgap (i - 1) (by omega) (by omega)).2.2.2
        rw [Nat.sub_add_cancel (by omega : 1 ≤ i)] at h6
        linarith
      · have h5 := hA' i l hi1 hli hlk
        linarith

variable (P : M.Par)

theorem gap4 (hOK : P.OK) (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ P.k - 1) :
    P.u (i + 1) ≤ P.u i - 1 ∧ P.u' (i + 1) ≤ P.u' i - 1 ∧ P.u (i + 1) ≤ P.u' i - 1 ∧
      P.u' (i + 1) ≤ P.u i - 1 := by
  obtain ⟨_, _, _, _, _, hg⟩ := hOK
  have hgi := hg i (by simp; omega)
  unfold M.Par.lo M.Par.hi at hgi
  have h3 := le_max_left (P.u (i + 1)) (P.u' (i + 1))
  have h4 := le_max_right (P.u (i + 1)) (P.u' (i + 1))
  have h5 := min_le_left (P.u i) (P.u' i)
  have h6 := min_le_right (P.u i) (P.u' i)
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem rho_bounds (hOK : P.OK) (ρ : M.Ty P) (i : ℕ) (hi1 : 1 ≤ i) (hi2 : i ≤ P.k - 1) :
    P.lo i ≤ M.rho P ρ i ∧ M.rho P ρ i ≤ P.hi i := by
  obtain ⟨_, _, _, _, _, hg⟩ := hOK
  have hgi := hg i (by simp; omega)
  have hw := (ρ ⟨i - 1, by omega⟩).isLt
  have he : i - 1 + 1 = i := by omega
  simp only [M.Par.wid, Fin.val_mk, he] at hw
  have hfl : ((⌊P.hi i - P.lo i⌋₊ : ℕ) : ℝ) ≤ P.hi i - P.lo i := Nat.floor_le (by linarith)
  have hv' : ((ρ ⟨i - 1, by omega⟩ : ℕ)) ≤ ⌊P.hi i - P.lo i⌋₊ := by
    first
      | exact Nat.lt_succ_iff.mp hw
      | omega
  have hv : ((ρ ⟨i - 1, by omega⟩ : ℕ) : ℝ) ≤ ((⌊P.hi i - P.lo i⌋₊ : ℕ) : ℝ) := by exact_mod_cast hv'
  have h0 : (0 : ℝ) ≤ ((ρ ⟨i - 1, by omega⟩ : ℕ) : ℝ) := Nat.cast_nonneg _
  unfold M.rho
  rw [dif_pos ⟨hi1, hi2⟩]
  constructor
  · linarith
  · linarith

theorem xC_ne (hOK : P.OK) (l : ℕ) (hl1 : 1 ≤ l) (hlk : l ≤ P.k) (y : ℝ) (hy : I.OnCut P.u P.u' l y)
    (e : ℝ) (he1 : -1 ≤ e) (he2 : e ≤ 1) (ρ : M.Ty P) : M.xC P ρ ((y + e : ℝ) : ℂ) ≠ 0 := by
  unfold M.xC
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  rw [Finset.mem_Icc] at hi
  have hb := rho_bounds P hOK ρ i hi.1 hi.2
  have hg4 := gap4 P hOK
  unfold M.Par.lo M.Par.hi at hb
  have a1 := le_max_left (P.u (i + 1)) (P.u' (i + 1))
  have a2 := le_max_right (P.u (i + 1)) (P.u' (i + 1))
  have a3 := min_le_left (P.u i) (P.u' i)
  have a4 := min_le_right (P.u i) (P.u' i)
  have key : y + e + M.rho P ρ i ≠ 0 := by
    unfold I.OnCut at hy
    rcases hy with hy | hy
    · exact (cut_facts P.u P.u' P.k l hl1 hlk hg4 y hy).1 i hi.1 hi.2 _
        (by linarith) (by linarith) (by linarith) (by linarith) e he1 he2
    · exact (cut_facts P.u' P.u P.k l hl1 hlk
        (fun j hj1 hj2 => ⟨(hg4 j hj1 hj2).2.1, (hg4 j hj1 hj2).1, (hg4 j hj1 hj2).2.2.2, (hg4 j hj1 hj2).2.2.1⟩)
        y hy).1 i hi.1 hi.2 _ (by linarith) (by linarith) (by linarith) (by linarith) e he1 he2
  intro h0
  apply key
  exact_mod_cast h0

theorem qC_ne (hOK : P.OK) (l : ℕ) (hl1 : 1 ≤ l) (hlk : l ≤ P.k) (y : ℝ) (hy : I.OnCut P.u P.u' l y)
    (e : ℝ) (he1 : -1 ≤ e) (he2 : e ≤ 0) : M.qC P ((y + e : ℝ) : ℂ) ≠ 0 := by
  have hg4 := gap4 P hOK
  obtain ⟨_, hT, hT', _, _, _⟩ := hOK
  unfold M.qC
  refine mul_ne_zero ?_ ?_
  · have h1 : (P.T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
    have h2 : (P.T' : ℂ) ≠ 0 := by exact_mod_cast hT'.ne'
    exact neg_ne_zero.mpr (mul_ne_zero h1 h2)
  · rw [Finset.prod_ne_zero_iff]
    intro i hi
    rw [Finset.mem_Icc] at hi
    have key : y + e + 1 / 2 + P.u i ≠ 0 ∧ y + e + 1 / 2 + P.u' i ≠ 0 := by
      unfold I.OnCut at hy
      rcases hy with hy | hy
      · exact (cut_facts P.u P.u' P.k l hl1 hlk hg4 y hy).2 i hi.1 hi.2 e he1 he2
      · have h3 := (cut_facts P.u' P.u P.k l hl1 hlk
          (fun j hj1 hj2 => ⟨(hg4 j hj1 hj2).2.1, (hg4 j hj1 hj2).1, (hg4 j hj1 hj2).2.2.2, (hg4 j hj1 hj2).2.2.1⟩)
          y hy).2 i hi.1 hi.2 e he1 he2
        exact ⟨h3.2, h3.1⟩
    refine mul_ne_zero ?_ ?_
    · intro h0
      apply key.1
      first
        | exact_mod_cast h0
        | (have h1 := congrArg Complex.re h0
           simp at h1
           linarith)
    · intro h0
      apply key.2
      first
        | exact_mod_cast h0
        | (have h1 := congrArg Complex.re h0
           simp at h1
           linarith)

end cut

theorem wordOK_of {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (st : Formalism.FourierDecayAlt.Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (hOK : P.OK) (hl1 : 1 ≤ l0) (hlk : l0 ≤ P.k) (hq : st.q = M.qC P)
    (hinv : st.inv = {Y | ∀ ρ : M.Ty P, M.xC P ρ Y ≠ 0}) (w : List Formalism.FourierDecayAlt.C.Letter)
    (hcut : ∀ a : Fin w.length, I.OnCut P.u P.u' l0 (w.get a).2)
    (hsep : ∀ a b : Fin w.length, a ≠ b → 2 < |(w.get a).2 - (w.get b).2|) :
    Formalism.FourierDecayAlt.P5.WordOK P z z' π π' st l0 (Formalism.FourierDecayAlt.D.positionted w) := by
  have hmem : ∀ x ∈ Formalism.FourierDecayAlt.D.positionted w, ∃ a : Fin w.length,
      x = (⟨(w.get a).1, a, ((w.get a).2 : ℂ)⟩ : Formalism.FourierDecayAlt.Wd.Letter ℂ (Fin w.length)) := by
    intro x hx
    unfold Formalism.FourierDecayAlt.D.positionted at hx
    obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hx
    exact ⟨a, rfl⟩
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · unfold Formalism.FourierDecayAlt.D.positionted
    rw [List.map_ofFn]
    exact List.nodup_ofFn.2 (fun a b h => h)
  · intro x hx
    obtain ⟨a, rfl⟩ := hmem x hx
    simp
  · intro x hx
    obtain ⟨a, rfl⟩ := hmem x hx
    have hc := hcut a
    have hx : ∀ e : ℝ, -1 ≤ e → e ≤ 1 → ∀ ρ, M.xC P ρ (((w.get a).2 + e : ℝ) : ℂ) ≠ 0 :=
      fun e h1 h2 ρ => xC_ne P hOK l0 hl1 hlk _ hc e h1 h2 ρ
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hinv]; intro ρ; simpa using hx 0 (by norm_num) (by norm_num) ρ
    · rw [hinv]; intro ρ; simpa using hx 1 (by norm_num) (by norm_num) ρ
    · rw [hinv]; intro ρ; simpa [sub_eq_add_neg] using hx (-1) (by norm_num) (by norm_num) ρ
    · rw [hq]; simpa using qC_ne P hOK l0 hl1 hlk _ hc 0 (by norm_num) (by norm_num)
    · rw [hq]; simpa [sub_eq_add_neg] using qC_ne P hOK l0 hl1 hlk _ hc (-1) (by norm_num) (by norm_num)
  · unfold Formalism.FourierDecayAlt.D.positionted
    rw [List.pairwise_ofFn]
    intro a b hab n hn h
    have h' : ((w.get a).2 : ℂ) - ((w.get b).2 : ℂ) = (n : ℂ) := h
    have h1 : (w.get a).2 - (w.get b).2 = (n : ℝ) := by exact_mod_cast h'
    have h2 : |(n : ℝ)| ≤ 2 := by exact_mod_cast hn
    have := hsep a b (ne_of_lt hab)
    rw [h1] at this
    linarith
  · intro x hx
    obtain ⟨a, rfl⟩ := hmem x hx
    exact ⟨by simp, by simpa using hcut a⟩
  · unfold Formalism.FourierDecayAlt.D.positionted
    rw [List.pairwise_ofFn]
    intro a b hab
    simpa using hsep a b (ne_of_lt hab)

theorem levelsActualBuilt : Formalism.FourierDecayAlt.JCT.LevelsActualBuilt := by
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hP
  obtain ⟨_, _, _, hB, hl1, hlk, hG, _, _, _, _, _, hOn⟩ := hP
  intro v j
  have hPl0 := (hB.2 v).2.2.2.1
  have hPl := isPlace_lev (Formalism.FourierDecayAlt.D.parOf S v) (T v) j hPl0
  obtain ⟨X⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist _ _ _ _ _ _ _ hPl
  obtain ⟨L, st, h1, h2, h3, h4, h5, h6⟩ := Formalism.FourierDecayAlt.P.level_start_actual _ _ _ _ _ _ _ hPl X (S.l + 1)
  obtain ⟨μ0, hμ0⟩ := exists_haar_level_zero (Nat.sub_self S.G.r) ((T v).bs S.G.r)
  refine ⟨X, μ0.map (embL S.G.k (S.G.r - j)), L, st, ⟨hPl, haar_glev μ0 hμ0, h1, h2, h3, h4, h5, h6⟩, ?_⟩
  intro w hw
  obtain ⟨W, rfl⟩ := hw
  obtain ⟨-, -, -, -, -, h6G⟩ := hG v
  refine wordOK_of _ _ _ _ _ st (S.l + 1) hPl.1 (by omega) (by change S.l + 1 ≤ S.G.k; omega) h3 h4 (W.1 v) (fun a => ?_) (fun a b hab => ?_)
  · have hn := W.2.1.1 v a.val a.isLt
    have hin : ∀ y, y ∈ S.grid v ((W.1 v).length - a.val) ∪ S.grid1 v →
        y ∈ (S.G.place (S.pl v)).cutI S.l ∧ y + 1 ∈ (S.G.place (S.pl v)).cutI S.l := by
      intro y hy
      rcases Finset.mem_union.1 hy with h | h
      · exact ⟨(h6G y (Or.inl ⟨_, h⟩)).1, (h6G y (Or.inl ⟨_, h⟩)).2.1⟩
      · exact ⟨(h6G y (Or.inr h)).1, (h6G y (Or.inr h)).2.1⟩
    have hpt : ((W.1 v).get a).2 ∈ (S.G.place (S.pl v)).cutI S.l := by
      rw [List.get_eq_getElem]
      by_cases hp : ((W.1 v)[a.val]'a.isLt).1 = true
      · rw [if_pos hp] at hn
        exact (hin _ hn).1
      · rw [if_neg hp] at hn
        have := (hin _ hn).2
        simpa using this
    apply hOn v
    simp only [Formalism.FourierDecayAlt.Sz.Cfg.cutI, Set.mem_ofPred_eq] at hpt
    simp only [Formalism.FourierDecayAlt.C.HidaSetting.cutLo, Formalism.FourierDecayAlt.C.HidaSetting.cutHi, Set.mem_Icc]
    constructor <;> linarith [hpt.1, hpt.2]
  · have := W.2.1.2 v a.val b.val a.isLt b.isLt (fun h => hab (Fin.ext h)) 0 (by norm_num) (by norm_num)
    simpa [List.get_eq_getElem] using this

end Formalism.FourierDecayAlt.P.JCTx5

namespace Formalism.FourierDecayAlt.P

theorem levels_of_built_setting : Formalism.FourierDecayAlt.JCT.LevelsActualBuilt := by
  exact Formalism.FourierDecayAlt.P.JCTx5.levelsActualBuilt

end Formalism.FourierDecayAlt.P
