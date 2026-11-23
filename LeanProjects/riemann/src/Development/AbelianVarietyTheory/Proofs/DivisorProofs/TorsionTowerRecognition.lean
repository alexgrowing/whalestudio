import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilIsIffPull
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionLabelSystemsSeriesScalarIndependentOfLeve
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionPairingValuesOfFamiliesValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationSeriesTermsNestStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.Recog

open GlobalTheory.Ex GlobalTheory.TorusExt GlobalTheory.SeriesCompare GlobalTheory.IndefiniteRowSideFullHecke.ThetaTowerRecognition

section Nest
variable {O : Type} [CommRing O] [TopologicalSpace O] (N : NumD O)

theorem tx_nest {n m M : ℕ} (hn : Odd n) (hm : Odd m) (hM : M = n * m) (Q : N.QT (M ^ 2)) (q : N.QT (m ^ 2))
    (h₁ : Q.1.1 = q.1.1 ^ n) (h₂ : q.1.2 = Q.1.2 ^ n) : N.tx M Q = N.tx m q := by
  subst hM
  exact tsum_congr fun χ => GlobalTheory.T.degenerationSeriesTerms_nest O N n m hn hm Q q h₁ h₂ χ

end Nest

section Scalar
variable {C : Type} [NormedField C] {N N' : NumD C} {n : ℕ}

theorem io_one (w : TowerIso N N' n) (j : ℕ) : N'.QEq (w.io j 1) 1 := by
  have := w.mul j 1 1
  rw [_root_.mul_one (1 : N.QT ((n ^ j) ^ 2))] at this
  obtain ⟨z, hz⟩ := (N'.qEq_iff _ _).1 this
  refine (N'.qEq_equivalence _).symm ((N'.qEq_iff _ _).2 ⟨z, ?_⟩)
  rw [_root_.one_mul]
  exact mul_left_cancel hz

theorem io_pow (w : TowerIso N N' n) (j : ℕ) (p : N.QT ((n ^ j) ^ 2)) (m : ℕ) :
    N'.QEq (w.io j (p ^ m)) (w.io j p ^ m) := by
  have E := N'.qEq_equivalence ((n ^ j) ^ 2)
  induction m with
  | zero => rw [pow_zero p, pow_zero (w.io j p)]; exact io_one w j
  | succ m ih =>
    rw [pow_succ p m, pow_succ (w.io j p) m]
    exact E.trans (w.mul j _ _) (GlobalTheory.Ex.TateInh.qEq_mul N' ih (E.refl _))

theorem addCommGroup_nsmul_identity {X : Type} [AddCommGroup X] (n k : ℕ) (Y Y' U z : X) (y₁ : U = n • Y' + (n * (n * k)) • z)
    (a : U = (n * n) • Y) : n • Y' = n • (n • (Y + k • -z)) := by
  have h := eq_sub_of_add_eq (y₁.symm.trans a)
  rw [h, mul_smul, mul_smul, mul_smul]
  simp only [smul_add, smul_neg]
  abel

theorem scalar_const (hn : Odd n) (w : TowerIso N N' n) (hX : ∀ (z z' : N'.X), n • z = n • z' → z = z')
    (hd : ∀ g : N.Gt, ∃ g', g' ^ n = g)
    (hc : ∀ j, ∃ c : Cˣ, ∀ q, N'.tx (n ^ j) (w.io j q) = c * N.tx (n ^ j) q)
    (h0 : ∃ q : N.QT ((n ^ 1) ^ 2), N.tx (n ^ 1) q ≠ 0) :
    ∃ c₀ : C, c₀ ≠ 0 ∧ ∀ j q, N'.tx (n ^ j) (w.io j q) = c₀ * N.tx (n ^ j) q := by
  have down : ∀ (c : C) (j : ℕ), (∀ q, N'.tx (n ^ (j + 1)) (w.io (j + 1) q) = c * N.tx (n ^ (j + 1)) q) →
      ∀ q, N'.tx (n ^ j) (w.io j q) = c * N.tx (n ^ j) q := by
    intro c j H q
    have hK : (n ^ (j + 1)) ^ 2 = n * ((n ^ j) ^ 2 * n) := by ring
    have hK' : (n ^ (j + 1)) ^ 2 = (n ^ j) ^ 2 * n ^ 2 := by ring
    obtain ⟨g, hg⟩ := hd q.1.2
    have hq := N.mem_QT.1 q.2
    let Q : N.QT ((n ^ (j + 1)) ^ 2) := ⟨(q.1.1 ^ n, g), by
      refine N.mem_QT.2 ?_
      show g ^ (n ^ (j + 1)) ^ 2 = N.io (Multiplicative.toAdd (q.1.1 ^ n))
      rw [hK, pow_mul g n, hg, pow_mul q.1.2, hq, toAdd_pow, N.io_nsmul]⟩
    have t₁ : N.tx (n ^ (j + 1)) Q = N.tx (n ^ j) q := tx_nest N hn hn.pow (pow_succ' n j) Q q rfl hg.symm
    let upq : N.QT ((n ^ (j + 1)) ^ 2) := ⟨(q.1.1 ^ n ^ 2, q.1.2), by
      refine N.mem_QT.2 ?_
      show q.1.2 ^ (n ^ (j + 1)) ^ 2 = N.io (Multiplicative.toAdd (q.1.1 ^ n ^ 2))
      rw [hK', pow_mul q.1.2, hq, toAdd_pow, N.io_nsmul]⟩
    have eQ : Q ^ n = upq := Subtype.ext (Prod.ext (by
      show (q.1.1 ^ n) ^ n = q.1.1 ^ n ^ 2
      rw [← pow_mul, ← sq]) hg)
    have hio := N'.mem_QT.1 (w.io j q).2
    let upio : N'.QT ((n ^ (j + 1)) ^ 2) := ⟨((w.io j q).1.1 ^ n ^ 2, (w.io j q).1.2), by
      refine N'.mem_QT.2 ?_
      show (w.io j q).1.2 ^ (n ^ (j + 1)) ^ 2 = N'.io (Multiplicative.toAdd ((w.io j q).1.1 ^ n ^ 2))
      rw [hK', pow_mul (w.io j q).1.2, hio, toAdd_pow, N'.io_nsmul]⟩
    have E := N'.qEq_equivalence ((n ^ (j + 1)) ^ 2)
    have r₁ : N'.QEq (w.io (j + 1) upq) upio :=
      w.incl j q upq upio (toAdd_pow _ _) rfl (toAdd_pow _ _) rfl
    have r₂ : N'.QEq (w.io (j + 1) Q ^ n) upio := E.trans (E.symm (io_pow w (j + 1) Q n)) (eQ ▸ r₁)
    obtain ⟨z, hz⟩ := (N'.qEq_iff _ _).1 r₂
    set Q' := w.io (j + 1) Q with hQ'
    let q₁ : N'.QT ((n ^ j) ^ 2) := w.io j q * N'.qTriv _ (-z)
    have y₁ : upio.1.1.toAdd = n • Q'.1.1.toAdd + (n * (n * (n ^ j) ^ 2)) • z := by
      rw [hz]
      show n • Q'.1.1.toAdd + (n ^ (j + 1)) ^ 2 • z = _
      exact congrArg (n • Q'.1.1.toAdd + · • z) (by ring)
    have a : upio.1.1.toAdd = (n * n) • (w.io j q).1.1.toAdd := by
      show Multiplicative.toAdd ((w.io j q).1.1 ^ n ^ 2) = _
      rw [toAdd_pow, sq]
    have ey : Q'.1.1 = q₁.1.1 ^ n := by
      apply Multiplicative.toAdd.injective
      refine hX _ _ ?_
      rw [toAdd_pow]
      exact addCommGroup_nsmul_identity n ((n ^ j) ^ 2) _ _ _ z y₁ a
    have eg : q₁.1.2 = Q'.1.2 ^ n := by
      have g₁ : upio.1.2 = Q'.1.2 ^ n * N'.io z := by rw [hz]; rfl
      show (w.io j q).1.2 * N'.io (-z) = _
      rw [N'.io_neg]
      exact (eq_mul_inv_of_mul_eq g₁.symm).symm
    have t₂ : N'.tx (n ^ (j + 1)) Q' = N'.tx (n ^ j) q₁ := tx_nest N' hn hn.pow (pow_succ' n j) Q' q₁ ey eg
    have t₃ : N'.tx (n ^ j) q₁ = N'.tx (n ^ j) (w.io j q) :=
      (GlobalTheory.ModelData.Scalar.tx_congr N' hn.pow ((N'.qEq_iff _ _).2 ⟨-z, rfl⟩)).symm
    rw [← t₃, ← t₂, H Q, t₁]
  have exists_smul_pow_eq_sum_of_inFNc : ∀ (c : C) (j : ℕ), (∀ q, N'.tx (n ^ (j + 1)) (w.io (j + 1) q) = c * N.tx (n ^ (j + 1)) q) →
      ∀ q, N'.tx (n ^ 1) (w.io 1 q) = c * N.tx (n ^ 1) q := fun c j => by
    induction j with
    | zero => exact id
    | succ j ih => exact fun H => ih (down c _ H)
  obtain ⟨q₀, hq₀⟩ := h0
  obtain ⟨c₁, h₁⟩ := hc 1
  refine ⟨c₁, c₁.ne_zero, fun j => ?_⟩
  obtain ⟨c, hj⟩ := hc (j + 1)
  have e : (c : C) = c₁ := mul_right_cancel₀ hq₀ ((exists_smul_pow_eq_sum_of_inFNc c j hj q₀).symm.trans (h₁ q₀))
  rw [← e]
  exact down c j hj

end Scalar

section Tower
attribute [local instance] gtGroup

variable {W : Type} [CommRing W] [IsDomain W] {D D' : DegPre W} (he : D.PsiEven) (hb : D.TauBimult)
  (he' : D'.PsiEven) (hb' : D'.TauBimult) {A : PolAV (Sp (FractionRing W))} {C : Type} [Field C] [IsAlgClosed C]
  [Algebra (FractionRing W) C] {N N' : NumD C} (ν : NumOf D C N) (ν' : NumOf D' C N')

include he in
theorem qPt_add {k : ℕ} {p p' : QkPt D C k} {q q' : N.QT k} (h : ν.QPt p q) (h' : ν.QPt p' q') :
    ν.QPt (qkAdd hb p p') (q * q') := by
  have H := GlobalTheory.Ex.GtValues.points_correspond W D he hb C N ν
  refine ⟨?_, ?_⟩
  · show ν.eX (q.1.1.toAdd + q'.1.1.toAdd) = p.y + p'.y
    rw [map_add, h.1, h'.1]
  · obtain ⟨c, hc⟩ := (H.1 (qkAdd hb p p').g).exists
    have := (H.2.2.1 p.g p'.g _ _ _ _ h.2 h'.2 hc).1 ((isAdd_iff_eq _ _ _).2 rfl)
    rw [this] at hc
    exact hc

include he hb he' hb' in

theorem exists_tower {f : ∀ k, QkPt D C k → (TFK (R := W) C ⟶ A.A)} {f' : ∀ k, QkPt D' C k → (TFK (R := W) C ⟶ A.A)}
    (G : GoodLab D A C f) (G' : GoodLab D' A C f') (n : ℕ) (hn : 1 ≤ n) :
    ∃ w : TowerIso N N' n, ∀ j p p' q q', ν.QPt p q → ν'.QPt p' q' →
      (N'.QEq (w.io j q) q' ↔ f ((n ^ j) ^ 2) p = f' ((n ^ j) ^ 2) p') := by
  have hk : ∀ j, 1 ≤ (n ^ j) ^ 2 := fun j => Nat.one_le_pow _ _ (Nat.one_le_pow _ _ hn)
  have BG := GlobalTheory.Ex.GtValues.points_correspond W D he hb C N ν
  have BG' := GlobalTheory.Ex.GtValues.points_correspond W D' he' hb' C N' ν'
  have BW := GlobalTheory.WeilValues.weil_eq_values GlobalTheory.Ex.GtValues.points_correspond
    (GlobalTheory.Ex.brFam GlobalTheory.firstFiveLaws.1 GlobalTheory.firstFiveLaws.2.1)
  choose P hP using fun k (q : N.QT k) => exists_pt he hb ν q
  choose V hV using fun k (p : QkPt D' C k) => exists_val he' hb' ν' p
  choose S hS using fun j (p : QkPt D C ((n ^ j) ^ 2)) => G'.onto _ (hk j) (f _ p) (G.pow _ (hk j) p)
  have key : ∀ j p p' q q', ν.QPt p q → ν'.QPt p' q' →
      (N'.QEq (V _ (S j (P _ q))) q' ↔ f ((n ^ j) ^ 2) p = f' ((n ^ j) ^ 2) p') := by
    intro j p p' q q' h h'
    rw [← (BG'.2.2.2.2 _).2.2 _ _ _ _ (hV _ _) h', ← G'.eqv _ (hk j), hS, pt_unique he hb ν (hP _ q) h]
  have gpt : ∀ {k l} (p : QkPt D C k) (p₀ : QkPt D C l) (q : N.QT k) (q₀ : N.QT l), ν.QPt p q → ν.QPt p₀ q₀ →
      q.1.2 = q₀.1.2 → p.g = p₀.g := fun p p₀ q q₀ h h₀ e => (BG.2.1 q.1.2).unique h.2 (e ▸ h₀.2)
  have gpt' : ∀ {k l} (p : QkPt D' C k) (p₀ : QkPt D' C l) (q : N'.QT k) (q₀ : N'.QT l), ν'.QPt p q →
      ν'.QPt p₀ q₀ → q.1.2 = q₀.1.2 → p.g = p₀.g := fun p p₀ q q₀ h h₀ e => (BG'.2.1 q.1.2).unique h.2 (e ▸ h₀.2)
  refine ⟨⟨fun j q => V _ (S j (P _ q)), ?_, ?_, ?_, ?_, ?_⟩, key⟩
  · intro j p q
    rw [key j (P _ p) (S j (P _ q)) p _ (hP _ p) (hV _ _), hS, G.eqv _ (hk j)]
    exact (BG.2.2.2.2 _).2.2 _ _ _ _ (hP _ p) (hP _ q)
  · intro j p'
    obtain ⟨p₀', hp₀'⟩ := exists_pt he' hb' ν' p'
    obtain ⟨p, hp⟩ := G.onto _ (hk j) (f' _ p₀') (G'.pow _ (hk j) p₀')
    obtain ⟨q, hq⟩ := exists_val he hb ν p
    exact ⟨q, (key j p p₀' q p' hq hp₀').2 hp⟩
  · intro j p q
    refine (key j (qkAdd hb (P _ p) (P _ q)) (qkAdd hb' (S j (P _ p)) (S j (P _ q))) (p * q) _
      (qPt_add he hb ν (hP _ p) (hP _ q)) (qPt_add he' hb' ν' (hV _ _) (hV _ _))).2 ?_
    rw [G.add _ (hk j) _ _ _ (qkAdd_qkAdd hb _ _), G'.add _ (hk j) _ _ _ (qkAdd_qkAdd hb' _ _), hS, hS]
  · intro j p q q' a b c d
    have hN : (n ^ (j + 1)) ^ 2 = (n ^ j) ^ 2 * n ^ 2 := by ring
    obtain ⟨P'', hP''⟩ := exists_pt he' hb' ν' q'
    refine (key (j + 1) (P _ q) P'' q q' (hP _ q) hP'').2 ?_
    have l₁ : f _ (P _ q) = f _ (P _ p) := G.level _ (n ^ 2) _ (hk j) (Nat.one_le_pow _ _ hn) hN _ _
      (by rw [← (hP _ q).1, ← (hP _ p).1, a, map_nsmul]) (gpt _ _ _ _ (hP _ q) (hP _ p) b)
    have l₂ : f' _ P'' = f' _ (S j (P _ p)) := G'.level _ (n ^ 2) _ (hk j) (Nat.one_le_pow _ _ hn) hN _ _
      (by rw [← hP''.1, ← (hV _ _).1, c, map_nsmul]) (gpt' _ _ _ _ hP'' (hV _ _) d)
    rw [l₁, l₂, hS]
  · intro j p q
    have w₁ := G.weil _ (hk j) _ _ (N.wp p q) ((BW W D he hb C N ν _ (hk j) _ _ _ _ _ (hP _ p) (hP _ q)).2 rfl)
    have w₂ := G'.weil _ (hk j) _ _ (N'.wp (V _ (S j (P _ p))) (V _ (S j (P _ q))))
      ((BW W D' he' hb' C N' ν' _ (hk j) _ _ _ _ _ (hV _ _) (hV _ _)).2 rfl)
    rw [hS, hS] at w₂
    exact Units.ext (congrArg Units.val (unitOn_inj ((GlobalTheory.LevelCompare.weil_existsUnique A _ _ _
      (G.pow _ (hk j) _) (G.pow _ (hk j) _)).unique w₂ w₁)))

end Tower

section Rec
attribute [local instance] gtGroup

theorem recognitionSt : RecognitionSt :=
  recognition_iff.2 (uRecDvr_of_uRec (GlobalTheory.T.degenerationRecognition_of_abelianPartsIsoLabels (GlobalTheory.T.abelianPartsIsoLabels_of_thetaPoint_and_values GlobalTheory.firstFiveLaws.1
    GlobalTheory.thetaPtDetermines_and_endDeterminedOnTorsion.1 (GlobalTheory.T.abelianPartValues_of_expansionLaws GlobalTheory.firstFiveLaws.1))))

def upQ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    (hb : D.TauBimult) {k : ℕ} (p : QkPt D F k) : QkPt D F (k ^ 2) :=
  qkMk hb (k • p.y) p.g (by rw [sq, mul_nsmul, qk_nsmul hb p, map_nsmul])

theorem rec_trait {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (hV : GlobalTheory.LN.CDvr V)
    {D D' : DegData V (maximalIdeal V)} {A : PolAV (Sp (FractionRing V))}
    {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C]
    [Algebra (FractionRing V) C] (hC : CExt V (maximalIdeal V) C) {N N' : NumD C} (ν : NumOf D.toPre C N)
    (ν' : NumOf D'.toPre C N') {f : ∀ k, QkPt D.toPre C k → (TFK (R := V) C ⟶ A.A)}
    {f' : ∀ k, QkPt D'.toPre C k → (TFK (R := V) C ⟶ A.A)} (G : GoodLab D.toPre A C f) (G' : GoodLab D'.toPre A C f')
    {n : ℕ} (hn : n.Prime) (ho : Odd n) (hu : IsUnit (n : V)) (hd : ∀ g : N.Gt, ∃ g', g' ^ n = g)
    (gal : ∀ (σ : C ≃ₐ[FractionRing V] C) (p pσ : QkPt D.toPre C ((n ^ 1) ^ 2)) (p' pσ' : QkPt D'.toPre C ((n ^ 1) ^ 2)),
      QkExt (σ : C →+* C) p pσ → QkExt (σ : C →+* C) p' pσ' → f _ p = f' _ p' → f _ pσ = f' _ pσ')
    (hc : ∀ j, ∃ c : Cˣ, ∀ p p' q q', ν.QPt p q → ν'.QPt p' q' → f ((n ^ j) ^ 2) p = f' _ p' →
      N'.tx (n ^ j) q' = c * N.tx (n ^ j) q)
    (h0 : ∃ q : N.QT ((n ^ 1) ^ 2), N.tx (n ^ 1) q ≠ 0) :
    ∃ e : IsPullDeg (RingHom.id V) D.toPre D'.toPre, ∀ j (p : QkPt D.toPre C (n ^ j)) (p' : QkPt D'.toPre C (n ^ j)),
      p'.y = e.xe.symm p.y → IsPullGtF (RingHom.id V) e C p.g p'.g → f _ p = f' _ p' := by
  have he := D.psi_even
  have hb := D.tau_bimult
  have he' := D'.psi_even
  have hb' := D'.tau_bimult
  obtain ⟨w, hw⟩ := exists_tower he hb he' hb' ν ν' G G' n hn.one_lt.le
  have hX : ∀ z z' : N'.X, n • z = n • z' → z = z' := fun z z' h => ν'.eX.injective (by
    have h' := congrArg ν'.eX h
    rw [map_nsmul, map_nsmul, ← natCast_zsmul, ← natCast_zsmul] at h'
    exact smul_right_injective _ (Int.natCast_ne_zero.2 hn.ne_zero) h')
  have hc' : ∀ j, ∃ c : Cˣ, ∀ q, N'.tx (n ^ j) (w.io j q) = c * N.tx (n ^ j) q := fun j => by
    obtain ⟨c, hc⟩ := hc j
    refine ⟨c, fun q => ?_⟩
    obtain ⟨p, hp⟩ := exists_pt he hb ν q
    obtain ⟨p', hp'⟩ := exists_pt he' hb' ν' (w.io j q)
    exact hc p p' q _ hp hp' ((hw j p p' q _ hp hp').1 ((N'.qEq_equivalence _).refl _))
  obtain ⟨c₀, -, h₀⟩ := scalar_const ho w hX hd hc' h0
  have hprop : w.Proportional c₀ := fun j q => ⟨N.tx (n ^ j) q, (summable_of_data hV D hC ν ho.pow q).1.hasSum, by
    rw [← h₀ j q]; exact (summable_of_data hV D' hC ν' ho.pow _).1.hasSum⟩
  have hrat : w.RationalAt ν ν' 1 := fun σ p pσ p' pσ' q qσ q' qσ' e₁ e₂ e₃ e₄ e₅ e₆ e₇ =>
    (hw 1 pσ pσ' qσ qσ' e₄ e₆).2 (gal σ p pσ p' pσ' e₁ e₂ ((hw 1 p p' q q' e₃ e₅).1 e₇))
  obtain ⟨e, hI⟩ := recognitionSt V hV D D' n hn ho hu C hC N N' ν ν' w c₀ hprop ⟨1, le_rfl, hrat⟩
  have cC : ArcPull.Compat (RingHom.id V) C := fun _ => rfl
  refine ⟨e, fun j p p' hy hg => ?_⟩
  have hk : 1 ≤ n ^ j := Nat.one_le_pow _ _ hn.pos
  have l₁ : f _ (upQ hb p) = f _ p := G.level _ (n ^ j) _ hk hk (sq _) p (upQ hb p) rfl rfl
  have l₂ : f' _ (upQ hb' p') = f' _ p' := G'.level _ (n ^ j) _ hk hk (sq _) p' (upQ hb' p') rfl rfl
  rw [← l₁, ← l₂]
  obtain ⟨q, hq⟩ := exists_val he hb ν (upQ hb p)
  obtain ⟨p₀, p₀', q', h₁, h₂, h₃, h₄⟩ := hI j q
  obtain rfl := pt_unique he hb ν h₁ hq
  have hp₀ : p₀' = upQ hb' p' := by
    refine qk_ext ?_ ?_
    · show p₀'.y = n ^ j • p'.y
      rw [hy, ← map_nsmul]
      exact (e.xe.symm_apply_eq.2 h₃.1.symm).symm
    · have g₁ : IsPullGtF (RingHom.id V) e C (upQ hb p).g p₀'.g := (GlobalTheory.ArcPull.isPullGtF_iff e cC _ _).2 fun z => by
        have := h₃.2 (e.xe.symm z)
        rw [AddEquiv.apply_symm_apply] at this
        simpa using this
      exact GlobalTheory.ArcPull.pullGt_unique e cC g₁ hg
  rw [← hp₀]
  exact (hw j _ _ q q' hq h₂).1 h₄

end Rec

end GlobalTheory.Mum.Recog
