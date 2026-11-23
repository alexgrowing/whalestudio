import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVCrdAlg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVCrdLoc
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVCrdGerm

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff Topology
open Filter

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.TVCrdE

open TVCrdAlg TVCrdLoc TVCrdGerm

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {r : ℕ}

theorem memW {f : (Fin r → ℂ) → X} (h : f ∈ WSm r X) :
    ContDiffOn ℝ ∞ f (OmX r) ∧ ∀ x, x ∉ OmX r → f x = 0 := h

def opE (l : Fin r) (i : Fin 6) : Module.End ℂ (WSm r X) where
  toFun f := ⟨opL l i f, preserved_operators_holds r X l i f f.2⟩
  map_add' f g := Subtype.ext (linear_operators_holds r X l i f g 1 f.2 g.2).1
  map_smul' a f := Subtype.ext (linear_operators_holds r X l i f f a f.2 f.2).2

@[simp] theorem opE_coe (l : Fin r) (i : Fin 6) (f : WSm r X) :
    ((opE l i f : WSm r X) : (Fin r → ℂ) → X) = opL l i f := rfl

theorem opL_three (l : Fin r) : opL (E := X) l 3 = pbOp l := rfl
theorem opL_four (l : Fin r) : opL (E := X) l 4 = cbOp l := rfl
theorem opL_five (l : Fin r) : opL (E := X) l 5 = cbiOp l := rfl

def mulE (a : (Fin r → ℂ) → ℂ) (ha : ContDiffOn ℝ ∞ a (OmX r)) : Module.End ℂ (WSm r X) where
  toFun f := ⟨fun x => a x • (f : (Fin r → ℂ) → X) x,
    ⟨ha.smul (memW f.2).1, fun x hx => by simp [(memW f.2).2 x hx]⟩⟩
  map_add' f g := Subtype.ext (funext fun x => by simp [smul_add])
  map_smul' s f := Subtype.ext (funext fun x => by simp [smul_comm (a x) s])

@[simp] theorem mulE_coe (a : (Fin r → ℂ) → ℂ) (ha : ContDiffOn ℝ ∞ a (OmX r)) (f : WSm r X) :
    ((mulE a ha f : WSm r X) : (Fin r → ℂ) → X) = fun x => a x • (f : (Fin r → ℂ) → X) x := rfl

theorem comm_of_mul (A B : Module.End ℂ (WSm r X)) (a b : (Fin r → ℂ) → ℂ)
    (hA : ∀ (f : WSm r X) x, (A f : (Fin r → ℂ) → X) x = a x • (f : (Fin r → ℂ) → X) x)
    (hB : ∀ (f : WSm r X) x, (B f : (Fin r → ℂ) → X) x = b x • (f : (Fin r → ℂ) → X) x) : Commute A B := by
  refine LinearMap.ext fun f => Subtype.ext (funext fun x => ?_)
  show (A (B f) : (Fin r → ℂ) → X) x = (B (A f) : (Fin r → ℂ) → X) x
  rw [hA, hB, hB, hA, smul_smul, smul_smul, mul_comm]

def PN (r : ℕ) (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (i : ℕ) : Module.End ℂ (WSm r X) :=
  if h : i < r then opE ⟨i, h⟩ 3 else 0
def CbN (r : ℕ) (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (i : ℕ) : Module.End ℂ (WSm r X) :=
  if h : i < r then opE ⟨i, h⟩ 4 else 0
def CbiN (r : ℕ) (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (i : ℕ) : Module.End ℂ (WSm r X) :=
  if h : i < r then opE ⟨i, h⟩ 5 else 0

theorem PN_coe (i : ℕ) (f : WSm r X) : ((PN r X i f : WSm r X) : (Fin r → ℂ) → X) = pbN r i f := by
  unfold PN pbN; split_ifs <;> rfl
theorem CbN_coe (i : ℕ) (f : WSm r X) : ((CbN r X i f : WSm r X) : (Fin r → ℂ) → X) = cbN r i f := by
  unfold CbN cbN; split_ifs <;> rfl
theorem CbiN_coe (i : ℕ) (f : WSm r X) : ((CbiN r X i f : WSm r X) : (Fin r → ℂ) → X) = cbiN r i f := by
  unfold CbiN cbiN; split_ifs <;> rfl

theorem CbN_mul (i : ℕ) (f : WSm r X) (x : Fin r → ℂ) :
    (CbN r X i f : (Fin r → ℂ) → X) x = (if h : i < r then star (x ⟨i, h⟩) else 0) • (f : (Fin r → ℂ) → X) x := by
  unfold CbN; split_ifs <;> simp [opL, cbOp]
theorem CbiN_mul (i : ℕ) (f : WSm r X) (x : Fin r → ℂ) :
    (CbiN r X i f : (Fin r → ℂ) → X) x =
      (if h : i < r then (star (x ⟨i, h⟩))⁻¹ else 0) • (f : (Fin r → ℂ) → X) x := by
  unfold CbiN; split_ifs <;> simp [opL, cbiOp]

theorem comm_PN_CbN {i j : ℕ} (h : i ≠ j) : Commute (PN r X i) (CbN r X j) := by
  unfold PN CbN
  split_ifs with h1 h2
  · refine LinearMap.ext fun f => Subtype.ext ?_
    exact commuting_functional_holds r X ⟨i, h1⟩ ⟨j, h2⟩ 3 4 f f.2 (Or.inl fun e => h (congrArg Fin.val e))
  all_goals simp
theorem comm_PN_CbiN {i j : ℕ} (h : i ≠ j) : Commute (PN r X i) (CbiN r X j) := by
  unfold PN CbiN
  split_ifs with h1 h2
  · refine LinearMap.ext fun f => Subtype.ext ?_
    exact commuting_functional_holds r X ⟨i, h1⟩ ⟨j, h2⟩ 3 5 f f.2 (Or.inl fun e => h (congrArg Fin.val e))
  all_goals simp

theorem comm_CbN_CbN (i j : ℕ) : Commute (CbN r X i) (CbN r X j) := comm_of_mul _ _ _ _ (CbN_mul i) (CbN_mul j)
theorem comm_CbN_CbiN (i j : ℕ) : Commute (CbN r X i) (CbiN r X j) := comm_of_mul _ _ _ _ (CbN_mul i) (CbiN_mul j)
theorem comm_CbiN_CbiN (i j : ℕ) : Commute (CbiN r X i) (CbiN r X j) :=
  comm_of_mul _ _ _ _ (CbiN_mul i) (CbiN_mul j)

def Gop (k r : ℕ) (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] : Module.End ℂ (WSm r X) :=
  mulE (gaugeF k r) gaugeF_smooth

theorem comm_G_CbN (k i : ℕ) : Commute (Gop k r X) (CbN r X i) :=
  comm_of_mul _ _ (gaugeF k r) _ (fun _ _ => rfl) (CbN_mul i)
theorem comm_G_CbiN (k i : ℕ) : Commute (Gop k r X) (CbiN r X i) :=
  comm_of_mul _ _ (gaugeF k r) _ (fun _ _ => rfl) (CbiN_mul i)

def sG (k r : ℕ) (i : Fin r) : ℂ := ((Mdim k r i - 1 : ℕ) : ℂ) / 2

theorem P_G (k : ℕ) (i : Fin r) : opE i 3 * Gop k r X = Gop k r X * opE i 3 + sG k r i • Gop k r X := by
  refine LinearMap.ext fun f => Subtype.ext ?_
  show pbOp i (fun x => gaugeF k r x • (f : (Fin r → ℂ) → X) x) = _
  rw [pbOp_gauge i _ f.2]
  funext x
  simp [Gop, opL_three, sG]

theorem G_PN (k : ℕ) {i : ℕ} (hi : i < r) :
    Gop k r X * PN r X i = (PN r X i - sG k r ⟨i, hi⟩ • 1) * Gop k r X := by
  have h := P_G (X := X) k ⟨i, hi⟩
  have hP : PN r X i = opE ⟨i, hi⟩ 3 := dif_pos hi
  rw [hP, sub_mul, smul_mul_assoc, one_mul, h]
  abel

def Dd (r : ℕ) (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (y : ℂ) (j : ℕ) : Module.End ℂ (WSm r X) :=
  y • 1 - PN r X j
def Ee (r : ℕ) (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (j : ℕ) : Module.End ℂ (WSm r X) :=
  CbN r X j * CbiN r X (j - 1)
def Dw (r : ℕ) (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (w : ℂ) (m : ℕ) : Module.End ℂ (WSm r X) :=
  (w - (m : ℂ)) • 1 - PN r X (r - m - 1)

theorem hDe (y : ℂ) : ∀ i j, i + 1 ≤ j → Dd r X y j * Ee r X i = Ee r X i * Dd r X y j := by
  intro i j hij
  have : Commute (Dd r X y j) (Ee r X i) := by
    unfold Dd Ee
    refine Commute.sub_left ((Commute.one_left _).smul_left y) ?_
    exact (comm_PN_CbN (by omega)).mul_right (comm_PN_CbiN (by omega))
  exact this.eq

theorem hee : ∀ i j, Ee r X i * Ee r X j = Ee r X j * Ee r X i := by
  intro i j
  have : Commute (Ee r X i) (Ee r X j) := by
    unfold Ee
    refine Commute.mul_left ?_ ?_
    · exact (comm_CbN_CbN i j).mul_right (comm_CbN_CbiN i (j - 1))
    · exact ((comm_CbN_CbiN j (i - 1)).symm).mul_right (comm_CbiN_CbiN (i - 1) (j - 1))
  exact this.eq

theorem hGe (k : ℕ) : ∀ j, Gop k r X * Ee r X j = Ee r X j * Gop k r X := by
  intro j
  exact ((comm_G_CbN k j).mul_right (comm_G_CbiN k (j - 1))).eq

theorem shift_eq (k : ℕ) (y : ℂ) {m : ℕ} (hm : m < r) :
    kvTop k r y - (m : ℂ) + sG k r ⟨r - m - 1, by omega⟩ = y := by
  have h : Mdim k r ⟨r - m - 1, by omega⟩ - 1 = 2 * m + k + 2 := by
    simp only [Mdim]; omega
  simp only [sG, kvTop, h]
  push_cast
  ring

theorem hG (k : ℕ) (y : ℂ) : ∀ m < r,
    Gop k r X * Dw r X (kvTop k r y) m = Dd r X y (r - m - 1) * Gop k r X := by
  intro m hm
  unfold Dw Dd
  rw [mul_sub, mul_smul_comm, mul_one, G_PN k (show r - m - 1 < r by omega), sub_mul, sub_mul, smul_mul_assoc,
    smul_mul_assoc, one_mul]
  have hy := shift_eq (r := r) k y hm
  conv_rhs => rw [← hy]
  rw [add_smul]
  abel

theorem iteratedOperator_coe (w : ℂ) : ∀ (m : ℕ) (f : WSm r X),
    (kvP r w m).1 (f : (Fin r → ℂ) → X) = ((topK (Dw r X w) (Ee r X) r m).1 f : WSm r X) ∧
      (kvP r w m).2 (f : (Fin r → ℂ) → X) = ((topK (Dw r X w) (Ee r X) r m).2 f : WSm r X)
  | 0, f => ⟨rfl, rfl⟩
  | m + 1, f => by
    have hD : (fun c => (w - (m : ℂ)) • (f : (Fin r → ℂ) → X) c - pbN r (r - m - 1) (f : (Fin r → ℂ) → X) c) =
        ((Dw r X w m f : WSm r X) : (Fin r → ℂ) → X) := by
      funext c
      simp [Dw, PN_coe]
    refine ⟨?_, (iteratedOperator_coe w m f).1⟩
    simp only [kvP, topK]
    rw [hD, (iteratedOperator_coe w m _).1, (iteratedOperator_coe w m f).2, ← CbiN_coe, ← CbN_coe]
    simp [Ee]

theorem vABm_coe (y : ℂ) : ∀ (i : ℕ) (f : WSm r X),
    (vABm r y i).1 (f : (Fin r → ℂ) → X) = ((botA (Dd r X y) (CbN r X) (CbiN r X) r i).1 f : WSm r X) ∧
      (vABm r y i).2 (f : (Fin r → ℂ) → X) = ((botA (Dd r X y) (CbN r X) (CbiN r X) r i).2 f : WSm r X)
  | 0, f => ⟨rfl, rfl⟩
  | i + 1, f => by
    by_cases h : i < r
    · obtain ⟨h1, h2⟩ := vABm_coe y i f
      have hP : PN r X i = opE ⟨i, h⟩ 3 := dif_pos h
      have hC : CbN r X i = opE ⟨i, h⟩ 4 := dif_pos h
      have hCi : CbiN r X i = opE ⟨i, h⟩ 5 := dif_pos h
      simp only [vABm, dif_pos h, botA, if_pos h]
      rw [h1, h2]
      refine ⟨?_, ?_⟩
      · simp [Dd, hP, hC, opL_three, opL_four]
      · simp [hCi, opL_five]
    · simp only [vABm, dif_neg h, botA, if_neg h]
      exact vABm_coe y i f

end Formalism.FourierDecayAlt.P.CutMP.TVCrdE

namespace Formalism.FourierDecayAlt.P.CutMP

open TVCrdAlg TVCrdLoc TVCrdGerm TVCrdE

theorem toda_coordinate_holds : TVCrd := by
  intro k r X _ _ y Φ U c hU hUO hc hΨ
  obtain ⟨φ, hφ, hΦ, hΨφ⟩ := TVCrdLoc.loc (k := k) Φ U c hU hUO hc hΨ
  have eL : kvC r (kvTop k r y) r Φ c = kvC r (kvTop k r y) r φ c :=
    (iteratedOperator_germ (kvTop k r y) r Φ φ c hΦ).1.eq_of_nhds
  have eR : (vABm r y r).1 (fun c' => gaugeF k r c' • Φ c') c =
      (vABm r y r).1 (fun c' => gaugeF k r c' • φ c') c :=
    (vABm_germ y r _ _ c hΨφ).1.eq_of_nhds
  rw [eL, eR]
  let f : WSm r X := ⟨φ, hφ⟩
  have hK : kvC r (kvTop k r y) r φ = ((topK (Dw r X (kvTop k r y)) (Ee r X) r r).1 f : WSm r X) :=
    (iteratedOperator_coe (kvTop k r y) r f).1
  have hA : (vABm r y r).1 (fun c' => gaugeF k r c' • φ c') =
      ((botA (Dd r X y) (CbN r X) (CbiN r X) r r).1 (Gop k r X f) : WSm r X) :=
    (vABm_coe y r (Gop k r X f)).1
  have hB := (botA_eq (Dd r X y) (CbN r X) (CbiN r X) r r le_rfl).1
  have hT := (topK_eq (Dd r X y) (Ee r X) (hDe y) hee r (fun m => Dd r X y (r - m - 1)) (fun _ _ => rfl) r le_rfl).1
  have hC := (topK_conj (Gop k r X) (Dw r X (kvTop k r y)) (fun m => Dd r X y (r - m - 1)) (Ee r X) r
    (hG k y) (hGe k) r le_rfl).1
  rw [Nat.sub_self] at hT
  have hAT : (botA (Dd r X y) (CbN r X) (CbiN r X) r r).1 =
      (topK (fun m => Dd r X y (r - m - 1)) (Ee r X) r r).1 := by
    rw [hB, hT]; rfl
  rw [hK, hA, hAT]
  have h2 : (topK (fun m => Dd r X y (r - m - 1)) (Ee r X) r r).1 (Gop k r X f) =
      Gop k r X ((topK (Dw r X (kvTop k r y)) (Ee r X) r r).1 f) := by
    rw [← Module.End.mul_apply, ← hC, Module.End.mul_apply]
  rw [h2]
  rfl

end Formalism.FourierDecayAlt.P.CutMP
