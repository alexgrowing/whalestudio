import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalCondMoveDecoratedLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetsInFramesEqIffReductions
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetMovesWithFrameChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberStepCharts
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPDivOfUnit
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TC.ChTw GlobalTheory.Mem.Col2.TC.ChTw.Match Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.ChTw.Match

theorem mem_image_units {κ : Type} [CommRing κ] {n : ℕ} (C : Set (Fin n → κ)) (y : GL (Fin n) κ) (w : Fin n → κ) :
    w ∈ (fun v => y.1 *ᵥ v) '' C ↔ (y⁻¹).1 *ᵥ w ∈ C := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  · intro h
    refine ⟨_, h, ?_⟩
    show y.1 *ᵥ ((y⁻¹).1 *ᵥ w) = w
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem conj_mem_setStab_image {κ : Type} [CommRing κ] {n : ℕ} (C : Set (Fin n → κ)) (y h : GL (Fin n) κ) :
    y * h * y⁻¹ ∈ MemChart.setStab ((fun v => y.1 *ᵥ v) '' C) ↔ h ∈ MemChart.setStab C := by
  have e1 : ∀ w : Fin n → κ, (y⁻¹).1 *ᵥ ((y * h * y⁻¹).1 *ᵥ w) = h.1 *ᵥ ((y⁻¹).1 *ᵥ w) := fun w => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, show y⁻¹ * (y * h * y⁻¹) = h * y⁻¹ by group, Units.val_mul, ← Matrix.mulVec_mulVec]
  have e2 : ∀ v : Fin n → κ, (y⁻¹).1 *ᵥ (y.1 *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  show (∀ w, (y * h * y⁻¹).1 *ᵥ w ∈ (fun v => y.1 *ᵥ v) '' C ↔ w ∈ (fun v => y.1 *ᵥ v) '' C) ↔ ∀ v, h.1 *ᵥ v ∈ C ↔ v ∈ C
  simp only [mem_image_units, e1]
  constructor
  · intro H v
    have := H (y.1 *ᵥ v)
    rwa [e2] at this
  · intro H w
    exact H _

set_option maxHeartbeats 1000000 in

theorem coset_match : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ), 1 ≤ i → i < B.R.m →
    ∀ (c : (I.stp u a i).Cl) (b0 : Idx I.sel (I.tup I.mu0) (I.idx I.mu0) i), ∃ c0 : (I.stp u I.mu0 i).Cl, c0.1 = b0 ∧
      ∃ y : GLG B.fields.E (B.R.N i) (B.primes X).vGs, y ∈ (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0).grp ∧
      ∀ (κ : (I.stp u a i).G c.1) (κ0 : (I.stp u I.mu0 i).G c0.1), (I.stp u a i).gam c.1 κ = 1 → (I.stp u I.mu0 i).gam c0.1 κ0 = 1 →
        κ.2.2 = 1 → (i + 1 = B.R.m → ∀ w, κ0.2.1.1 w = y w * κ.2.1.1 w * (y w)⁻¹) →
        (cosetIn ((I.stp u a i).act c.1 κ ((I.stp u a i).rep c)) = cosetIn ((I.stp u a i).rep c) ↔
          cosetIn ((I.stp u I.mu0 i).act c0.1 κ0 ((I.stp u I.mu0 i).rep c0)) = cosetIn ((I.stp u I.mu0 i).rep c0)) := by
  intro B X I hI l u a i h1 hm c b0
  classical
  haveI : NeZero (B.R.N i) := ⟨(B.R.N_pos i).ne'⟩
  by_cases hl : i + 1 = B.R.m
  · have hq : ∀ w ∈ (B.primes X).vGs, ((qOf w : ℕ) : 𝓞 B.fields.E) ∉ w.asIdeal ^ 2 :=
      fun _ hw => GlobalTheory.TopStep.qOf_notMem_sq (GlobalTheory.Mem.FieldsLaws.fields_ok B) l.pr hw
    set r : PtAt B.R I.sel (I.tup a) (I.cst a) u i := (I.stp u a i).rep c with hr
    obtain ⟨y, hy, hy0, hY⟩ := ChEx.ptAt_cosetG r hl
    have hGs : ∀ P : rowSG (B.primes X) I.sel (I.tup I.mu0), P.1 ∈ (B.primes X).vGs := fun P => by
      rcases Finset.mem_union.1 P.2 with h | h
      · exact h
      · have h' : P.1 ∈ I.Q I.mu0 := h
        rw [I.twistPrimes_reference_tuple_eq_empty] at h'
        exact absurd h' (Finset.notMem_empty _)
    let Y0 : Set (Sp B.fields.E (B.R.N i)) := {z | z - y ∈ locLat (rowSG (B.primes X) I.sel (I.tup I.mu0)) r.1.1.deco.1.N
        (fun P => if P.1 ∈ (B.primes X).vGs then 0 else ((I.cst I.mu0).M : ℤ))}
    have hY0 : Y0 ∈ (ysAt B.R I.sel (I.tup I.mu0) (I.cst I.mu0) i).ys
        (extTo (QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K)) r.1.1).deco.1.N := by
      rw [ysAt_ys_of_eq _ _ _ hl]
      refine ⟨y, (mem_locLat _ _ _ _).2 fun P => ?_, rfl⟩
      rw [if_pos (hGs P), _root_.zpow_neg_one, inv_inv]
      exact hy P.1 (hGs P)
    let q0 : PtAt B.R I.sel (I.tup I.mu0) (I.cst I.mu0) u i := ⟨(extTo _ r.1.1, Y0), hY0⟩
    have hbar : MemChart.bar q0 = MemChart.bar r := by
      funext w
      have hy' : ∀ w ∈ (B.primes X).vGs, ((qOf w : ℕ) : B.fields.E) • y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal q0.1.1.deco.1.N := hy
      have hy0' : y ∈ q0.1.2 := by
        change y - y ∈ locLat (rowSG (B.primes X) I.sel (I.tup I.mu0)) r.1.1.deco.1.N
          (fun P => if P.1 ∈ (B.primes X).vGs then 0 else ((I.cst I.mu0).M : ℤ))
        rw [sub_self]
        exact zero_mem _
      have hY' : ∀ z ∈ q0.1.2, ∀ w ∈ (B.primes X).vGs, z - y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal q0.1.1.deco.1.N := by
        intro z hz w hw
        have h2 := (mem_locLat _ _ _ _).1 hz ⟨w, Finset.mem_union_left _ hw⟩
        exact (by simpa [hw] using h2 : z - y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal r.1.1.deco.1.N)
      rw [ChEx.bar_eqG q0 hy' hy0' hY' w, ChEx.bar_eqG r hy hy0 hY w]
      rfl
    refine ⟨(I.stp u I.mu0 i).cl b0 q0, rfl, ?_⟩
    obtain ⟨g0, hg0⟩ := (I.stp u I.mu0 i).exists_mv b0 q0
    refine ⟨(g0.2.1.1)⁻¹, inv_mem g0.2.1.2, ?_⟩
    intro κ κ0 _ _ hθ hκ
    have hκ' := hκ hl
    set r0 : PtAt B.R I.sel (I.tup I.mu0) (I.cst I.mu0) u i := (I.stp u I.mu0 i).rep ((I.stp u I.mu0 i).cl b0 q0) with hr0
    have hb0 : ∀ w, MemChart.bar q0 w = (fun v => (g0.2.1.1 w).1 *ᵥ v) '' MemChart.bar r0 w := by
      intro w
      have e : MemChart.ya (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0)
          (levQAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0) g0 r0 = q0 := hg0
      have h3 := MemChart.bar_ya (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0)
          (levQAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0) g0 r0 w
      rw [e] at h3
      exact h3
    have hb0' : ∀ w, MemChart.bar r0 w = (fun v => (((g0.2.1.1)⁻¹ : GLG B.fields.E (B.R.N i) (B.primes X).vGs) w).1 *ᵥ v) '' MemChart.bar r w := by
      intro w
      have e : ∀ v, ((g0.2.1.1 w)⁻¹).1 *ᵥ ((g0.2.1.1 w).1 *ᵥ v) = v := fun v => by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      rw [← hbar, hb0 w, Set.image_image]
      show MemChart.bar r0 w = (fun v => ((g0.2.1.1 w)⁻¹).1 *ᵥ ((g0.2.1.1 w).1 *ᵥ v)) '' MemChart.bar r0 w
      simp only [e, Set.image_id']
    have hL : cosetIn ((I.stp u a i).act c.1 κ ((I.stp u a i).rep c)) = cosetIn ((I.stp u a i).rep c) ↔
        ∀ w, κ.2.1.1 w ∈ MemChart.setStab (MemChart.bar r w) := by
      show cosetIn (MemChart.ya (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i c.1)
          (levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) i c.1) κ r) = cosetIn r ↔ _
      rw [ChEx.cosetIn_eq_iff_bar_cq (ChEx.q_disj I hI a) hq, MemChart.bar_ya_eq_iff]
      have hcq : ChEx.cqOf (MemChart.ya (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i c.1)
          (levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) i c.1) κ r) = ChEx.cqOf r := by
        funext P
        rw [ChEx.invActs_cqOf (ChEx.q_disj I hI a) _ _ κ r P, hθ]
        ext v
        simp
      rw [hcq]
      simp
    have hR : cosetIn ((I.stp u I.mu0 i).act ((I.stp u I.mu0 i).cl b0 q0).1 κ0 r0) = cosetIn r0 ↔
        ∀ w, κ0.2.1.1 w ∈ MemChart.setStab (MemChart.bar r0 w) := by
      show cosetIn (MemChart.ya (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0)
          (levQAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0) κ0 r0) = cosetIn r0 ↔ _
      rw [ChEx.cosetIn_eq_iff_bar_cq (ChEx.q_disj I hI I.mu0) hq, MemChart.bar_ya_eq_iff]
      have hcq : ChEx.cqOf (MemChart.ya (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0)
          (levQAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0) κ0 r0) = ChEx.cqOf r0 := by
        funext P
        have h' : P.1 ∈ I.Q I.mu0 := P.2
        rw [I.twistPrimes_reference_tuple_eq_empty] at h'
        exact absurd h' (Finset.notMem_empty _)
      rw [hcq]
      simp
    rw [hL, hR]
    refine forall_congr' fun w => ?_
    rw [hκ' w, hb0' w]
    exact (conj_mem_setStab_image _ _ _).symm
  · let q0 : PtAt B.R I.sel (I.tup I.mu0) (I.cst I.mu0) u i :=
      ⟨(DecoF.base _ _ _ _ _, ∅), by rw [ysAt_ys_of_ne I.sel (I.tup I.mu0) (I.cst I.mu0) hl]; rfl⟩
    refine ⟨(I.stp u I.mu0 i).cl b0 q0, rfl, 1, one_mem _, fun κ κ0 _ _ _ _ => ?_⟩
    exact iff_of_true (ChEx.cos_of_neT I hl _ _) (ChEx.cos_of_neT I hl _ _)

end GlobalTheory.Mem.Col2.TC.ChTw.Match
