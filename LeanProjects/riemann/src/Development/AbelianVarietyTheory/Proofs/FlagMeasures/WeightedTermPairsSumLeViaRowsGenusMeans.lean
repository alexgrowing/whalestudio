import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PerRowC

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypeAsm.PairsSum

theorem ofReal_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ENNReal.ofReal (∑ i ∈ s, f i) ≤ ∑ i ∈ s, ENNReal.ofReal (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ENNReal.ofReal_add_le.trans (add_le_add le_rfl ih)

private theorem matrix_mul_comm_of_mul_eq_smul_one_of_ne_zero {α β γ : Type*} (s : Finset α) (A : Finset β) (A' : Finset γ) (w : α → ℝ≥0∞)
    (T : α → β → γ → ℝ≥0∞) (c : β → γ → ℝ≥0∞) :
    ∑ a ∈ s, w a * ∑ x ∈ A, ∑ x' ∈ A', T a x x' * c x x' =
      ∑ x ∈ A, ∑ x' ∈ A', c x x' * ∑ a ∈ s, w a * T a x x' := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm (s := s)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm (s := s)]
  refine Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun a _ => ?_
  ring

theorem pairs_sum_le : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ → CompatC → PerRowC →
    RowsMeanC → ∀ (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W),
    GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype →
    (∀ (s : Formalism.HermitianLatticesTheory.isom HW.B.flip) (M : Submodule (𝓞 D.host.E) W) (x x' : ℕ),
      (GlobalTheory.DegCnt.Trip HW (gS D) (s • M) D.R.rS x x').encard = (GlobalTheory.DegCnt.Trip HW (gS D) M D.R.rS x x').encard) →
    ∀ B : ℕ → ℕ → ℝ, (∀ x x', 0 ≤ B x x') →
    (∀ Λ ∈ Y.what₂ u, ∀ x x' : ℕ, 1 ≤ x → 1 ≤ x' →
      GlobalTheory.Mass.orbSum (Formalism.HermitianLatticesTheory.isom HW.B.flip) (Formalism.HermitianLatticesTheory.genus HW.B.flip (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ))
                   (fun L => (((GlobalTheory.DegCnt.Trip HW (gS D) L D.R.rS x x').encard : ℕ∞) : ℝ≥0∞)) ≤
        ENNReal.ofReal (Formalism.HermitianLatticesTheory.mass HW.B.flip (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ) * B x x')) →
    ∀ (j' j'' : ℕ) (δ' δ'' : ℕ → D.host.E) (S : Finset (GTu Y u × GTu Y u)),
    (∀ p ∈ S, p ∈ (Y.tO u u).allPairs (relSet Y u) ∧ jT p.1 = j' ∧ jT p.2 = j'' ∧ labT p.1 = δ' ∧ labT p.2 = δ'') →
    ENNReal.ofReal (∑ p ∈ S, (Formalism.L2.SG.TermOp.wt p.1 * Formalism.L2.SG.TermOp.wt p.2) * (omT p.1 * omT p.2)) ≤
      ∑ x ∈ Finset.Icc 1 ⌊k2Del D j' δ'⌋₊, ∑ x' ∈ Finset.Icc 1 ⌊k2Del D j'' δ''⌋₊,
        ENNReal.ofReal (GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j' δ') (DbL D j' δ') (NT D u) x *
          GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j'' δ'') (DbL D j'' δ'') (NT D u) x') *
        ENNReal.ofReal (massC Y u * B x x') := by
  intro D large₂ X Y u hStd hCompat hPerRow hMean W HW hEmb hInv B hB hOrb j' j'' δ' δ'' S hS
  have hw : ∀ Λ, 0 ≤ wRow D (X.Fu u) Λ := fun Λ => inv_nonneg.2 (Nat.cast_nonneg _)

  have hterm : ∀ p ∈ S, (Formalism.L2.SG.TermOp.wt p.1 * Formalism.L2.SG.TermOp.wt p.2) * (omT p.1 * omT p.2) =
      wRow D (X.Fu u) p.1.lam * (wRow D (X.Fu u) p.1.lam' * (omT p.1 * omT p.2)) := by
    intro p hp
    have hall : p ∈ (Y.tO u u).allPairs Set.univ := by
      have h1 := (hS p hp).1
      simp only [Formalism.FourierDecayAlt.PB.Terms.allPairs, Set.mem_ofPred_eq] at h1 ⊢
      exact ⟨Set.mem_univ _, Set.mem_univ _, h1.2.2⟩
    obtain ⟨hl, hl', -⟩ := hCompat D X Y u p hall
    unfold Formalism.L2.SG.TermOp.wt
    rw [← hl, ← hl', Real.mul_self_sqrt, mul_assoc]
    exacts [rfl, mul_nonneg (hw _) (hw _)]

  rw [Finset.sum_congr rfl hterm,
    ← Finset.sum_fiberwise_of_maps_to (g := fun p => p.1.lam) (t := Y.what₂ u) (fun p _ => p.1.mem)]
  refine (ofReal_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun Λ _ => ?_).trans ((le_of_eq (matrix_mul_comm_of_mul_eq_smul_one_of_ne_zero (Y.what₂ u) (Finset.Icc 1 ⌊k2Del D j' δ'⌋₊) (Finset.Icc 1 ⌊k2Del D j'' δ''⌋₊)
    (fun Λ => ENNReal.ofReal (wRow D (X.Fu u) Λ))
    (fun Λ x x' => (((GlobalTheory.DegCnt.Trip HW (gS D) (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ) D.R.rS x x').encard : ℕ∞) : ℝ≥0∞))
    (fun x x' => ENNReal.ofReal (GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j' δ') (DbL D j' δ') (NT D u) x *
          GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j'' δ'') (DbL D j'' δ'') (NT D u) x')))).trans ?_)
  ·
    beta_reduce
    have hrw : ∑ p ∈ S with p.1.lam = Λ, wRow D (X.Fu u) p.1.lam * (wRow D (X.Fu u) p.1.lam' * (omT p.1 * omT p.2)) =
        wRow D (X.Fu u) Λ * ∑ p ∈ S with p.1.lam = Λ, wRow D (X.Fu u) p.1.lam' * (omT p.1 * omT p.2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [(Finset.mem_filter.1 hp).2]
    rw [hrw, ENNReal.ofReal_mul (hw Λ)]
    refine mul_le_mul' le_rfl (hPerRow D large₂ X Y u hStd W HW hEmb Λ j' j'' δ' δ'' _ fun p hp => ?_)
    obtain ⟨hpS, hpΛ⟩ := Finset.mem_filter.1 hp
    obtain ⟨h1, h2, h3, h4, h5⟩ := hS p hpS
    exact ⟨h1, hpΛ, h2, h3, h4, h5⟩
  ·
    refine Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun x' hx' => mul_le_mul' le_rfl ?_
    exact hMean D large₂ X Y u hStd W HW hEmb
      (fun M => (((GlobalTheory.DegCnt.Trip HW (gS D) M D.R.rS x x').encard : ℕ∞) : ℝ≥0∞)) (B x x') (hB x x')
      (fun s M => by simp only [hInv s M x x'])
      (fun Λ hΛ => hOrb Λ hΛ x x' (Finset.mem_Icc.1 hx).1 (Finset.mem_Icc.1 hx').1)

end GlobalTheory.TypeAsm.PairsSum
