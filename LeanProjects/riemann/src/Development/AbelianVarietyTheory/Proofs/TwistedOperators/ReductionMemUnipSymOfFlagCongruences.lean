import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagGLConjApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelPlacesNotIsConjPlaceRealDat
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BunExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BSlotD
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueCoordinatesInFrameLinearStabiliserStatement
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.NatCastKPZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.SeeConjGroup
open Classical

section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem redFn_col {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hβ : IsFrame β Λ) (PP : Pl E) (M : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hM : M ∈ St β)
    (w : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) (j : Fin n) (hw : w ∈ Formalism.L2.Herm.hatL (F := F) Λ)
    (hwr : redV β PP w = Pi.single j 1) (A : Set (Fin n))
    (hmem : (M.val - 1) *ᵥ w ∈ Formalism.L2.Herm.hatL (F := F) Λ ∧
      redV β PP ((M.val - 1) *ᵥ w) ∈ Submodule.pi {q | q ∉ A} (fun _ => (⊥ : Submodule (kP PP) (kP PP)))) :
    ∀ q, q ∉ A → ((redFn β PP M : GL (Fin n) (kP PP)) : Matrix (Fin n) (Fin n) (kP PP)) q j = if q = j then 1 else 0 := by
  obtain ⟨hadd, -, hMv⟩ := GlobalTheory.T.residueCoordinatesInFrame_linear_stabiliser β Λ hβ PP
  intro q hq
  have e1 : (M.val - 1) *ᵥ w + w = (M : Matrix (Fin n) (Fin n) _) *ᵥ w := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_add_cancel]
  have e2 := hMv M hM w hw
  rw [← e1, hadd _ hmem.1 _ hw, hwr, Matrix.mulVec_single_one] at e2
  have e3 := congrFun e2 q
  have h0 : redV β PP ((M.val - 1) *ᵥ w) q = 0 := by
    have := (Submodule.mem_pi.1 hmem.2) q hq
    simpa using this
  rw [Pi.add_apply, h0, zero_add, Pi.single_apply] at e3
  exact e3.symm

end Gen

theorem redV_zero_of_frame {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)} (hβ : IsFrame β Λ) (PP : Pl E) :
    redV β PP 0 = 0 := by
  obtain ⟨hadd, -, -⟩ := GlobalTheory.T.residueCoordinatesInFrame_linear_stabiliser β Λ hβ PP
  have := hadd 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _)
  rw [add_zero] at this
  simpa using this

theorem single_mem_pi_bot {κ : Type} [CommRing κ] {n : ℕ} {A : Set (Fin n)} {p : Fin n} (hp : p ∈ A) :
    (Pi.single p (1 : κ) : Fin n → κ) ∈ Submodule.pi {q | q ∉ A} (fun _ => (⊥ : Submodule κ κ)) := by
  refine Submodule.mem_pi.2 fun q hq => ?_
  rw [Submodule.mem_bot, Pi.single_apply, if_neg]
  intro h
  subst h
  exact hq hp

theorem flagV_of_lt {M : Type} [Zero M] (ρ k n : ℕ) (e f : Fin ρ → M) (b : Fin k → M) (z : M) (i : Fin n)
    (h : i.1 < ρ) : flagV ρ k n e f b z i = e ⟨i.1, h⟩ := by
  unfold flagV; rw [dif_pos h]

theorem flagV_of_mid {M : Type} [Zero M] (ρ k n : ℕ) (e f : Fin ρ → M) (b : Fin k → M) (z : M) (i : Fin n)
    (h1 : ρ ≤ i.1) (h2 : i.1 < ρ + k) : flagV ρ k n e f b z i = b ⟨i.1 - ρ, by omega⟩ := by
  unfold flagV; rw [dif_neg (by omega), dif_pos h2]

theorem flagV_of_eq {M : Type} [Zero M] (ρ k n : ℕ) (e f : Fin ρ → M) (b : Fin k → M) (z : M) (i : Fin n)
    (h : i.1 = ρ + k) : flagV ρ k n e f b z i = z := by
  unfold flagV; rw [dif_neg (by omega), dif_neg (by omega), dif_pos h]

theorem flagV_of_gt {M : Type} [Zero M] (ρ k n : ℕ) (e f : Fin ρ → M) (b : Fin k → M) (z : M) (i : Fin n)
    (h1 : ρ + k < i.1) (h2 : i.1 < 2 * ρ + k + 1) : flagV ρ k n e f b z i = f ⟨2 * ρ + k - i.1, by omega⟩ := by
  unfold flagV; rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_pos h2]

theorem restrictedBlock_mem_unipSym_of_columns {κ : Type} [CommRing κ] {n r : ℕ} (ρ k : ℕ) (hr : r = n) (hle : r ≤ n) (N : GL (Fin n) κ)
    (hcol : ∀ j q : Fin n, ¬ ((j.1 = ρ + k ∧ q.1 < ρ) ∨ (j.1 ≠ ρ + k ∧ q.1 < j.1)) →
      (N : Matrix (Fin n) (Fin n) κ) q j = if q = j then 1 else 0) :
    upperLeftBlock hle N ∈ unipSym κ r ρ k := by
  have hall : N ∈ blockTri (blk2 r) := by
    rw [mem_blockTri]
    intro i j hij
    exfalso
    have hi : i.1 < r := by have := i.2; omega
    have hj : j.1 < r := by have := j.2; omega
    simp only [blk2, hi, hj, if_true, lt_irrefl] at hij
  have hv : ∀ i j : Fin r, ((upperLeftBlock hle N : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) i j =
      (N : Matrix (Fin n) (Fin n) κ) (Fin.castLE hle i) (Fin.castLE hle j) := by
    intro i j
    rw [upper_block_val_submatrix hle hall]
    rfl
  have hne : ∀ i j : Fin r, i.1 ≠ j.1 → (if Fin.castLE hle i = Fin.castLE hle j then (1 : κ) else 0) = 0 :=
    fun i j h => if_neg (fun e => h (by simpa using congrArg Fin.val e))
  refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j h0 h1 h2 => ?_⟩
  · have hij' : j.1 < i.1 := hij
    show ((upperLeftBlock hle N : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) i j = 0
    rw [hv, hcol _ _ (by simp only [Fin.coe_castLE]; omega), hne i j (by omega)]
  · rw [hv, hcol _ _ (by simp only [Fin.coe_castLE]; omega), if_pos rfl]
  · rw [hv, hcol _ _ (by simp only [Fin.coe_castLE]; omega), hne i j (by omega)]

theorem mem_hatL_of_Lf (D : D7) : ∀ v ∈ (II D).Lf, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (E := D.host.E) (n := (Yc D 0).rank) (II D).L :=
    fun v hv => (Set.ext_iff.1 (Formalism.IndefR.Eqv.lamAf_eq_hatL (V := Yc D 0) (II D).L) v).1 hv

set_option maxHeartbeats 1000000 in

theorem redV_mL (D : D7) (g : ℕ) (β : GL (Fin (Yc D 0).rank) (EAf D)) (PP : Pl D.host.E) (hβ : IsFrame β (II D).L)
    (hg : ((g : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) :
    ∀ v ∈ Formalism.L2.SG.HidaSetting.mL (II D) g,
      v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (E := D.host.E) (n := (Yc D 0).rank) (II D).L ∧ redV β PP v = 0 := by
  obtain ⟨hadd, hsmul, -⟩ := GlobalTheory.T.residueCoordinatesInFrame_linear_stabiliser β (II D).L hβ PP
  intro v hv
  unfold mL at hv
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    have hx' := mem_hatL_of_Lf D x hx
    have hc : ((g : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) = (g : EAf D) :=
      map_natCast (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype g
    have e : ((((g : ℕ) : (II D).E ⊗[(II D).F] Af (II D).F) • x : VA (II D)) : Fin (Yc D 0).rank → EAf D) =
        ((g : ℕ) : EAf D) • (show Fin (Yc D 0).rank → EAf D from x) := rfl
    have hm : ((g : ℕ) : EAf D) • (show Fin (Yc D 0).rank → EAf D from x) ∈
        Formalism.L2.Herm.hatL (F := D.host.F) (E := D.host.E) (n := (Yc D 0).rank) (II D).L := by
      exact Submodule.smul_mem _ (g : Formalism.L2.Herm.intAf D.host.F D.host.E) hx'
    have hs := hsmul (g : Formalism.L2.Herm.intAf D.host.F D.host.E) x hx'
    rw [e]
    refine ⟨hm, ?_⟩
    refine hs.trans ?_
    rw [map_natCast]
    have h0 : ((g : kP PP)) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
      exact Ideal.Quotient.eq_zero_iff_mem.2 hg
    rw [h0, zero_smul]
  | zero => exact ⟨Submodule.zero_mem _, redV_zero_of_frame hβ PP⟩
  | add a b _ _ ha hb =>
    exact ⟨Submodule.add_mem _ ha.1 hb.1, (hadd a ha.1 b hb.1).trans (by rw [ha.2, hb.2, add_zero])⟩
  | smul c a _ ha =>
    have c2 : (show EAf D from c.1) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := c.2
    have e : ((c • a : VA (II D)) : Fin (Yc D 0).rank → EAf D) =
        (show EAf D from c.1) • (show Fin (Yc D 0).rank → EAf D from a) := rfl
    rw [e]
    have hm := Submodule.smul_mem _ (⟨_, c2⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) ha.1
    exact ⟨hm, (hsmul ⟨_, c2⟩ a ha.1).trans (by rw [ha.2, smul_zero])⟩

set_option maxHeartbeats 1000000 in

theorem redV_span (D : D7) (β : GL (Fin (Yc D 0).rank) (EAf D)) (PP : Pl D.host.E) (hβ : IsFrame β (II D).L)
    (T : Submodule (kP PP) (Fin (Yc D 0).rank → kP PP)) (S : Set (VA (II D)))
    (hS : ∀ s ∈ S, s ∈ Formalism.L2.Herm.hatL (F := D.host.F) (E := D.host.E) (n := (Yc D 0).rank) (II D).L ∧ redV β PP s ∈ T) :
    ∀ v ∈ Submodule.span (IntAf (II D).F (II D).E) S,
      v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (E := D.host.E) (n := (Yc D 0).rank) (II D).L ∧ redV β PP v ∈ T := by
  obtain ⟨hadd, hsmul, -⟩ := GlobalTheory.T.residueCoordinatesInFrame_linear_stabiliser β (II D).L hβ PP
  intro v hv
  induction hv using Submodule.span_induction with
  | mem y hy => exact hS y hy
  | zero => exact ⟨Submodule.zero_mem _, (redV_zero_of_frame hβ PP) ▸ T.zero_mem⟩
  | add a b _ _ ha hb =>
    exact ⟨Submodule.add_mem _ ha.1 hb.1, by
      have e := hadd a ha.1 b hb.1
      exact e ▸ T.add_mem ha.2 hb.2⟩
  | smul c a _ ha =>
    have c2 : (show EAf D from c.1) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := c.2
    have e : ((c • a : VA (II D)) : Fin (Yc D 0).rank → EAf D) =
        (show EAf D from c.1) • (show Fin (Yc D 0).rank → EAf D from a) := rfl
    rw [e]
    have hm := Submodule.smul_mem _ (⟨_, c2⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) ha.1
    exact ⟨hm, (hsmul ⟨_, c2⟩ a ha.1) ▸ T.smul_mem _ ha.2⟩

set_option maxHeartbeats 1000000 in

theorem redV_Mo (D : D7) (g : ℕ) (β : GL (Fin (Yc D 0).rank) (EAf D)) (PP : Pl D.host.E) (hβ : IsFrame β (II D).L)
    (hg : ((g : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal)
    (T : Submodule (kP PP) (Fin (Yc D 0).rank → kP PP)) (S : Set (VA (II D)))
    (hS : ∀ s ∈ S, s ∈ Formalism.L2.Herm.hatL (F := D.host.F) (E := D.host.E) (n := (Yc D 0).rank) (II D).L ∧ redV β PP s ∈ T) :
    ∀ v ∈ Formalism.L2.SG.Pf.unitaryCongruence.Mo (II D) g S,
      v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (E := D.host.E) (n := (Yc D 0).rank) (II D).L ∧ redV β PP v ∈ T := by
  obtain ⟨hadd, -, -⟩ := GlobalTheory.T.residueCoordinatesInFrame_linear_stabiliser β (II D).L hβ PP
  intro v hv
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
  obtain ⟨hy1, hy2⟩ := redV_span D β PP hβ T S hS y hy
  obtain ⟨hz1, hz2⟩ := redV_mL D g β PP hβ hg z hz
  refine ⟨Submodule.add_mem _ hy1 hz1, ?_⟩
  have e := hadd y hy1 z hz1
  rw [hz2, add_zero] at e
  exact e ▸ hy2

set_option maxHeartbeats 1000000 in

theorem redFn_col_of_Mo (D : D7) (g : ℕ) (β : GL (Fin (Yc D 0).rank) (EAf D)) (PP : Pl D.host.E) (hβ : IsFrame β (II D).L)
    (hg : ((g : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) (w : Fin (Yc D 0).rank → VA (II D))
    (hw : ∀ j, w j ∈ Formalism.L2.Herm.hatL (F := D.host.F) (E := D.host.E) (n := (Yc D 0).rank) (II D).L ∧
      redV β PP (w j) = Pi.single j 1)
    (M : GL (Fin (Yc D 0).rank) (EAf D)) (hM : M ∈ St β) (j : Fin (Yc D 0).rank) (v : VA (II D)) (hv : w j = v)
    (S : Set (VA (II D))) (A : Set (Fin (Yc D 0).rank))
    (hmo : (M.val - 1) *ᵥ v ∈ Formalism.L2.SG.Pf.unitaryCongruence.Mo (II D) g S)
    (hS : ∀ s ∈ S, (∃ p ∈ A, s = w p) ∨
      (s ∈ Formalism.L2.Herm.hatL (F := D.host.F) (E := D.host.E) (n := (Yc D 0).rank) (II D).L ∧ redV β PP s = 0)) :
    ∀ q, q ∉ A → ((redFn β PP M : GL (Fin (Yc D 0).rank) (kP PP)) : Matrix (Fin (Yc D 0).rank) (Fin (Yc D 0).rank) (kP PP)) q j =
      if q = j then 1 else 0 := by
  subst hv
  refine redFn_col hβ PP M hM (w j) j (hw j).1 (hw j).2 A ?_
  refine redV_Mo D g β PP hβ hg _ S ?_ _ hmo
  intro s hs
  rcases hS s hs with ⟨p, hp, rfl⟩ | ⟨h1, h2⟩
  · refine ⟨(hw p).1, ?_⟩
    rw [(hw p).2]
    exact single_mem_pi_bot hp
  · refine ⟨h1, ?_⟩
    rw [h2]
    exact Submodule.zero_mem _

set_option maxHeartbeats 2000000 in

theorem redFn_mem_unipSym_of_cong : ∀ {D : D7} (g : ℕ) (e0 f0 : Fin D.R.rS → VA (II D)) (z0 : VA (II D)) (bb cc : Fin D.R.k → VA (II D)) (β : GL (Fin (Yc D 0).rank) (EAf D)) (PP : Pl D.host.E), IsFrame β (II D).L → ((g : 𝓞 D.host.E) ∈ PP.asIdeal) → RedIs β PP (flagV D.R.rS D.R.k (Yc D 0).rank e0 f0 bb z0) → (∀ i, cc i ∈ (II D).Lf ∧ redV β PP (cc i) = 0) → ∀ M : GL (Fin (Yc D 0).rank) (EAf D), M ∈ St β → (∀ a, (M.val - 1) *ᵥ e0 a ∈ Formalism.L2.SG.Pf.unitaryCongruence.Mo (II D) g (e0 '' {b | b.1 < a.1})) → ((M.val - 1) *ᵥ z0 ∈ Formalism.L2.SG.Pf.unitaryCongruence.Mo (II D) g (Set.range e0)) → (∀ i, (M.val - 1) *ᵥ bb i ∈ Formalism.L2.SG.Pf.unitaryCongruence.Mo (II D) g (Set.range e0 ∪ Set.range cc ∪ bb '' {j | j.1 < i.1})) → (∀ b, (M.val - 1) *ᵥ f0 b ∈ Formalism.L2.SG.Pf.unitaryCongruence.Mo (II D) g (Set.range e0 ∪ {z0} ∪ Set.range bb ∪ Set.range cc ∪ f0 '' {c | b < c})) → upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP M) ∈ unipSym (kP PP) D.R.r D.R.rS D.R.k := by
  intro D g e0 f0 z0 bb cc β PP hβ hg hRed hcc M hM he0 hz0 hbb hf0
  have hn : (Yc D 0).rank = 2 * D.R.rS + D.R.k + 1 := by
    have h1 : (Yc D 0).rank = D.R.r := Formalism.L2.SG.InstExistsPf.rank_eq D
    rw [h1]
    obtain ⟨j, hj⟩ := D.R.m_even
    have := D.R.two_le_m
    simp only [Formalism.BasicNotions.Ranks.r, Formalism.BasicNotions.Ranks.rS]
    omega
  have hw : ∀ j, flagV D.R.rS D.R.k (Yc D 0).rank e0 f0 bb z0 j ∈
      Formalism.L2.Herm.hatL (F := D.host.F) (E := D.host.E) (n := (Yc D 0).rank) (II D).L ∧
      redV β PP (flagV D.R.rS D.R.k (Yc D 0).rank e0 f0 bb z0 j) = Pi.single j 1 := by
    intro j
    refine ⟨(hβ _).2 (fun i => (hRed i j).1), ?_⟩
    funext i
    obtain ⟨hm, he⟩ := hRed i j
    unfold redV
    rw [dif_pos hm, Pi.single_apply]
    exact he
  have hcol : ∀ j q : Fin (Yc D 0).rank, ¬ ((j.1 = D.R.rS + D.R.k ∧ q.1 < D.R.rS) ∨ (j.1 ≠ D.R.rS + D.R.k ∧ q.1 < j.1)) →
      ((redFn β PP M : GL (Fin (Yc D 0).rank) (kP PP)) : Matrix (Fin (Yc D 0).rank) (Fin (Yc D 0).rank) (kP PP)) q j =
        if q = j then 1 else 0 := by
    intro j q hq
    have hj2 := j.2
    by_cases h1 : j.1 < D.R.rS
    · refine redFn_col_of_Mo D g β PP hβ hg _ hw M hM j (e0 ⟨j.1, h1⟩) (flagV_of_lt _ _ _ _ _ _ _ j h1) _ {q | q.1 < j.1}
        (he0 ⟨j.1, h1⟩) ?_ q (by simp only [Set.mem_setOf_eq]; omega)
      rintro s ⟨b, hb, rfl⟩
      have hb' : b.1 < j.1 := hb
      exact Or.inl ⟨⟨b.1, by omega⟩, hb', (flagV_of_lt _ _ _ _ _ _ _ ⟨b.1, by omega⟩ b.2).symm⟩
    by_cases h2 : j.1 < D.R.rS + D.R.k
    · refine redFn_col_of_Mo D g β PP hβ hg _ hw M hM j (bb ⟨j.1 - D.R.rS, by omega⟩)
        (flagV_of_mid _ _ _ _ _ _ _ j (by omega) h2) _ {q | q.1 < j.1}
        (hbb _) ?_ q (by simp only [Set.mem_setOf_eq]; omega)
      rintro s ((⟨b, rfl⟩ | ⟨c, rfl⟩) | ⟨l, hl, rfl⟩)
      · have := b.2
        exact Or.inl ⟨⟨b.1, by omega⟩, (show b.1 < j.1 by omega), (flagV_of_lt _ _ _ _ _ _ _ ⟨b.1, by omega⟩ b.2).symm⟩
      · exact Or.inr ⟨mem_hatL_of_Lf D _ (hcc c).1, (hcc c).2⟩
      · have hl' : l.1 < j.1 - D.R.rS := hl
        have := l.2
        refine Or.inl ⟨⟨D.R.rS + l.1, by omega⟩, (show D.R.rS + l.1 < j.1 by omega), ?_⟩
        rw [flagV_of_mid _ _ _ _ _ _ _ _ (by show D.R.rS ≤ D.R.rS + l.1; omega)
          (by show D.R.rS + l.1 < D.R.rS + D.R.k; omega)]
        congr 1
        ext
        simp
    by_cases h3 : j.1 = D.R.rS + D.R.k
    · refine redFn_col_of_Mo D g β PP hβ hg _ hw M hM j z0 (flagV_of_eq _ _ _ _ _ _ _ j h3) _ {q | q.1 < D.R.rS}
        hz0 ?_ q (by simp only [Set.mem_setOf_eq]; omega)
      rintro s ⟨b, rfl⟩
      exact Or.inl ⟨⟨b.1, by omega⟩, b.2, (flagV_of_lt _ _ _ _ _ _ _ ⟨b.1, by omega⟩ b.2).symm⟩
    · refine redFn_col_of_Mo D g β PP hβ hg _ hw M hM j (f0 ⟨2 * D.R.rS + D.R.k - j.1, by omega⟩)
        (flagV_of_gt _ _ _ _ _ _ _ j (by omega) (by omega)) _ {q | q.1 < j.1}
        (hf0 _) ?_ q (by simp only [Set.mem_setOf_eq]; omega)
      rintro s ((((⟨a, rfl⟩ | rfl) | ⟨l, rfl⟩) | ⟨c, rfl⟩) | ⟨c, hc, rfl⟩)
      · have := a.2
        exact Or.inl ⟨⟨a.1, by omega⟩, (show a.1 < j.1 by omega), (flagV_of_lt _ _ _ _ _ _ _ ⟨a.1, by omega⟩ a.2).symm⟩
      · exact Or.inl ⟨⟨D.R.rS + D.R.k, by omega⟩, (show D.R.rS + D.R.k < j.1 by omega),
          (flagV_of_eq _ _ _ _ _ _ _ _ rfl).symm⟩
      · have := l.2
        refine Or.inl ⟨⟨D.R.rS + l.1, by omega⟩, (show D.R.rS + l.1 < j.1 by omega), ?_⟩
        rw [flagV_of_mid _ _ _ _ _ _ _ _ (by show D.R.rS ≤ D.R.rS + l.1; omega)
          (by show D.R.rS + l.1 < D.R.rS + D.R.k; omega)]
        congr 1
        ext
        simp
      · exact Or.inr ⟨mem_hatL_of_Lf D _ (hcc c).1, (hcc c).2⟩
      · have hc' : 2 * D.R.rS + D.R.k - j.1 < c.1 := hc
        have := c.2
        refine Or.inl ⟨⟨2 * D.R.rS + D.R.k - c.1, by omega⟩, (show 2 * D.R.rS + D.R.k - c.1 < j.1 by omega), ?_⟩
        rw [flagV_of_gt _ _ _ _ _ _ _ _ (by show D.R.rS + D.R.k < 2 * D.R.rS + D.R.k - c.1; omega)
          (by show 2 * D.R.rS + D.R.k - c.1 < 2 * D.R.rS + D.R.k + 1; omega)]
        congr 1
        ext
        simp only
        omega
  exact restrictedBlock_mem_unipSym_of_columns D.R.rS D.R.k (Formalism.L2.SG.InstExistsPf.rank_eq D).symm _ _ hcol

end GlobalTheory.SeeConjGroup
