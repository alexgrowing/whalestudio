import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.RowActWeylMemDescentLattice
import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.CoreDesc
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.IsUnitDetBlockPreimage

open MvPolynomial Matrix Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.BasicNotions Formalism.L2.Forms

noncomputable section

namespace Formalism.L2.G.RelativeIndexFlags.Core

open Formalism.L2.G.Cmp Formalism.L2.G.RelativeIndexFlags

theorem int_inj : Function.Injective (algebraMap ℤ ℂ) := (algebraMap ℤ ℂ).injective_int

def OddId {m : ℕ} (lam : Fin (m + 1) → ℤ) (ft f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) ℤ) : Prop :=
  ∀ z : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ, IsUnit z.det →
    z.det ^ lam (Fin.last m) * eval (fun x => z x.1 x.2) (map (Int.castRingHom ℂ) ft) =
      (revCol (z⁻¹)ᵀ).det ^ lamStar lam (Fin.last m) *
        eval (fun x => revCol (z⁻¹)ᵀ x.1 x.2) (map (Int.castRingHom ℂ) f)

theorem oddZ (m : ℕ) (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam) (hodd : OddFact (K := ℂ) ℤ m lam) :
    (∀ f ∈ weyl ℤ (m + 1) (m + 1) le_rfl (nuOf (lamStar lam)),
      ∃ ft ∈ weyl ℤ (m + 1) (m + 1) le_rfl (nuOf lam), OddId lam ft f) ∧
    (∀ ft ∈ weyl ℤ (m + 1) (m + 1) le_rfl (nuOf lam),
      ∃ f ∈ weyl ℤ (m + 1) (m + 1) le_rfl (nuOf (lamStar lam)), OddId lam ft f) := by
  have h1 : IsUnit (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).det := by simp
  have hg' : IsUnit (((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)⁻¹)ᵀ).det := by simp
  have hst := lamStar_anti lam hlam
  have hi1 : ∀ w : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ, (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)⁻¹ * w = w := by
    intro w; simp
  have hi2 : ∀ w : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ,
      (((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)⁻¹)ᵀ)⁻¹ * w = w := by
    intro w; simp
  obtain ⟨hA, hB⟩ := hodd 1 h1
  constructor
  · intro f hf
    obtain ⟨F, hF, hev⟩ := hB _ (rowAct_weyl_mem_descentLattice int_inj m (lamStar lam) hst _ hg' f hf)
    obtain ⟨ft, hft, hev2⟩ := even_block_weyl_mem int_inj m lam hlam 1 h1 F hF
    refine ⟨ft, hft, fun z hz => ?_⟩
    have e1 := hev2 z
    rw [hi1] at e1
    have e3 := even_block_row_action_eval (((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)⁻¹)ᵀ) (lamStar lam (Fin.last m))
      (map (algebraMap ℤ ℂ) f) (revCol (z⁻¹)ᵀ)
    rw [hi2] at e3
    exact e1.symm.trans ((hev z hz).trans e3)
  · intro ft hft
    obtain ⟨F', hF', hev⟩ := hA _ (rowAct_weyl_mem_descentLattice int_inj m lam hlam 1 h1 ft hft)
    obtain ⟨f, hf, hev2⟩ := even_block_weyl_mem int_inj m (lamStar lam) hst _ hg' F' hF'
    refine ⟨f, hf, fun z hz => ?_⟩
    have e0 := even_block_row_action_eval (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (lam (Fin.last m)) (map (algebraMap ℤ ℂ) ft) z
    rw [hi1] at e0
    have e4 := hev2 (revCol (z⁻¹)ᵀ)
    rw [hi2] at e4
    exact e0.symm.trans ((hev z hz).trans e4)

theorem detShift_eq {m : ℕ} (lam : DomWeight (m + 1)) : lam.detShift = lam.w (Fin.last m) := by
  unfold DomWeight.detShift
  rw [dif_pos (Nat.succ_pos m)]
  rfl

theorem natW_eq {m : ℕ} (lam : DomWeight (m + 1)) : lam.natW = nuOf lam.w := by
  funext i
  unfold DomWeight.natW nuOf
  rw [detShift_eq]

theorem core_intSpanG_smul {Tau : Type} [Fintype Tau] {n : ℕ} {LL : Type} [Field LL] (embLL : LL →+* ℂ) (R0 : Subring LL)
    (lam : Tau → DomWeight n) (a : LL) (ha : a ∈ R0) {Pp : MvPolynomial (Tau × Fin n × Fin n) ℂ}
    (hP : Pp ∈ IntSpanG embLL R0 lam) : embLL a • Pp ∈ IntSpanG embLL R0 lam := by
  unfold IntSpanG at hP ⊢
  induction hP using AddSubgroup.closure_induction with
  | mem q hq =>
    obtain ⟨s, f, hs, hf, rfl⟩ := hq
    exact AddSubgroup.subset_closure ⟨a * s, f, R0.mul_mem ha hs, hf, by rw [map_mul, mul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

section Ev

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf) {Tau : Type} [Fintype Tau] {LL : Type} [Field LL]
  (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau) (lam : Tau → DomWeight (P.m + 1))
  (M N : Tau → GL (Fin (P.m + 1)) LL) (embLL : LL →+* ℂ)

abbrev mcOf {k : ℕ} (M : Tau → GL (Fin k) LL) (embLL : LL →+* ℂ) : Tau → Matrix (Fin k) (Fin k) ℂ :=
  fun τ => (M τ : Matrix (Fin k) (Fin k) LL).map embLL

abbrev kcOf {k : ℕ} (M N : Tau → GL (Fin k) LL) (embLL : LL →+* ℂ) : Tau → Matrix (Fin k) (Fin k) ℂ :=
  fun τ => (((N τ)⁻¹ * M τ : GL (Fin k) LL) : Matrix (Fin k) (Fin k) LL).map embLL

def BlockRealisation (x : Σ v : Fin P.nV, Fin (P.n' v)) (f ft : MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℤ) : Prop :=
  ∀ y : Tau → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ, (∀ τ, IsUnit (y τ).det) →
    (zAt P rfl pos (mcOf M embLL) y x.1 x.2).det ^ (eAt P x.1 x.2) *
        eval (fun a => zAt P rfl pos (mcOf M embLL) y x.1 x.2 a.1 a.2) (map embLL (bl P rfl pos N x.1 x.2 f)) =
      (kcOf M N embLL (pos x) * y (pos x)).det ^ (lam (pos x)).detShift *
        eval (fun a => (kcOf M N embLL (pos x) * y (pos x)) a.1 a.2) (map (Int.castRingHom ℂ) ft)

theorem blk_lhs (v : Fin P.nV) (s : Fin (P.n' v)) (f : MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℤ)
    (zz : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ) :
    zz.det ^ (eAt P v s) * eval (fun a => zz a.1 a.2) (map embLL (bl P rfl pos N v s f)) =
      ((niAt P rfl pos N v s).map embLL * zz).det ^ (eAt P v s) *
        eval (fun a => ((niAt P rfl pos N v s).map embLL * zz) a.1 a.2) (map (Int.castRingHom ℂ) f) := by
  rw [map_bl, even_block_row_action_eval, nAt_map_inv]

theorem even_mat (v : Fin P.nV) (s : Fin (P.n' v)) (hs : Even s.val)
    (y : Tau → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ) :
    (niAt P rfl pos N v s).map embLL * zAt P rfl pos (mcOf M embLL) y v s =
      kcOf M N embLL (pos ⟨v, s⟩) * y (pos ⟨v, s⟩) := by
  unfold niAt zAt reM
  rw [if_pos hs, if_pos hs, sub_rfl, sub_rfl]
  show _ = ((((N (pos ⟨v, s⟩))⁻¹ * M (pos ⟨v, s⟩) : GL (Fin (P.m + 1)) LL) :
    Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) LL).map embLL) * _
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

theorem odd_mat (v : Fin P.nV) (s : Fin (P.n' v)) (hs : ¬ Even s.val)
    (y : Tau → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ) :
    (niAt P rfl pos N v s).map embLL * zAt P rfl pos (mcOf M embLL) y v s =
      revCol (((kcOf M N embLL (pos ⟨v, s⟩) * y (pos ⟨v, s⟩))⁻¹)ᵀ) := by
  have hN : ((((N (pos ⟨v, s⟩))⁻¹ : GL (Fin (P.m + 1)) LL) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) LL).map embLL)⁻¹ =
      (N (pos ⟨v, s⟩) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) LL).map embLL := by
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.map_one embLL embLL.map_zero embLL.map_one]
  have hK : (kcOf M N embLL (pos ⟨v, s⟩) * y (pos ⟨v, s⟩))⁻¹ =
      (mcOf M embLL (pos ⟨v, s⟩) * y (pos ⟨v, s⟩))⁻¹ *
        (N (pos ⟨v, s⟩) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) LL).map embLL := by
    show (((((N (pos ⟨v, s⟩))⁻¹ * M (pos ⟨v, s⟩) : GL (Fin (P.m + 1)) LL) :
      Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) LL).map embLL) * y (pos ⟨v, s⟩))⁻¹ = _
    rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc, Matrix.mul_inv_rev, hN]
  unfold niAt zAt reM revCol
  rw [if_neg hs, if_neg hs, sub_rfl, sub_rfl, hK, Matrix.transpose_mul,
    Matrix.submatrix_mul _ _ id id Fin.rev Function.bijective_id, Matrix.submatrix_id_id, Matrix.transpose_map]

theorem blk_ev (hodd : ∀ (m : ℕ) (lam : Fin (m + 1) → ℤ), Antitone lam → OddFact (K := ℂ) ℤ m lam)
    (hw : WtTie P rfl pos lam) (x : Σ v : Fin P.nV, Fin (P.n' v)) :
    (∀ f ∈ weyl ℤ (P.m + 1) (P.m + 1) le_rfl (nuOf (lamAt (P.lam0 x.1) x.2)),
      ∃ ft ∈ delSq ℤ (P.m + 1) (lam (pos x)), BlockRealisation P pos lam M N embLL x f ft) ∧
    (∀ ft ∈ delSq ℤ (P.m + 1) (lam (pos x)),
      ∃ f ∈ weyl ℤ (P.m + 1) (P.m + 1) le_rfl (nuOf (lamAt (P.lam0 x.1) x.2)), BlockRealisation P pos lam M N embLL x f ft) := by
  obtain ⟨v, s⟩ := x
  have hl0 : P.lam0 v s = (lam (pos ⟨v, s⟩)).w := funext fun i => hw v s i
  have hdel : delSq ℤ (P.m + 1) (lam (pos ⟨v, s⟩)) = weyl ℤ (P.m + 1) (P.m + 1) le_rfl (nuOf (P.lam0 v s)) := by
    unfold delSq; rw [natW_eq, hl0]
  have hsh : (lam (pos ⟨v, s⟩)).detShift = P.lam0 v s (Fin.last P.m) := by rw [detShift_eq, hl0]
  show (∀ f ∈ weyl ℤ (P.m + 1) (P.m + 1) le_rfl (nuOf (lamAt (P.lam0 v) s)), _) ∧
    (∀ ft ∈ delSq ℤ (P.m + 1) (lam (pos ⟨v, s⟩)),
      ∃ f ∈ weyl ℤ (P.m + 1) (P.m + 1) le_rfl (nuOf (lamAt (P.lam0 v) s)), _)
  rw [hdel]
  by_cases hs : Even s.val
  · have hla := lamAt_even (P.lam0 v) s hs
    have hid : ∀ f, BlockRealisation P pos lam M N embLL ⟨v, s⟩ f f := by
      intro f y hy
      show (zAt P rfl pos (mcOf M embLL) y v s).det ^ (eAt P v s) *
        eval (fun a => zAt P rfl pos (mcOf M embLL) y v s a.1 a.2) (map embLL (bl P rfl pos N v s f)) = _
      rw [blk_lhs, even_mat P pos M N embLL v s hs y, hsh]
      unfold eAt
      rw [hla]
    rw [hla]
    exact ⟨fun f hf => ⟨f, hf, hid f⟩, fun f hf => ⟨f, hf, hid f⟩⟩
  · have hla := lamAt_odd (P.lam0 v) s hs
    obtain ⟨hA, hB⟩ := oddZ P.m (P.lam0 v s) (P.dom v s) (hodd _ _ (P.dom v s))
    have hid : ∀ f ft, OddId (P.lam0 v s) ft f → BlockRealisation P pos lam M N embLL ⟨v, s⟩ f ft := by
      intro f ft h y hy
      show (zAt P rfl pos (mcOf M embLL) y v s).det ^ (eAt P v s) *
        eval (fun a => zAt P rfl pos (mcOf M embLL) y v s a.1 a.2) (map embLL (bl P rfl pos N v s f)) = _
      rw [blk_lhs, odd_mat P pos M N embLL v s hs y, hsh]
      have hz : IsUnit (kcOf M N embLL (pos ⟨v, s⟩) * y (pos ⟨v, s⟩)).det := by
        rw [Matrix.det_mul]; exact (gl_map_det embLL _).mul (hy _)
      have h2 := h _ hz
      unfold eAt
      rw [hla]
      exact h2.symm
    rw [hla]
    exact ⟨fun f hf => let ⟨ft, hft, h⟩ := hA f hf; ⟨ft, hft, hid f ft h⟩,
      fun ft hft => let ⟨f, hf, h⟩ := hB ft hft; ⟨f, hf, hid f ft h⟩⟩

theorem fnOf_ten (G K : Tau → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ)
    (g : Tau → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℂ) (z : Frames G) :
    fnOf G (shiftOf lam) K (ten g) z =
      ∏ τ, ((K τ * z.1 τ).det ^ (lam τ).detShift * eval (fun a => (K τ * z.1 τ) a.1 a.2) (g τ)) := by
  rw [Finset.prod_mul_distrib]
  show (∏ τ, (K τ * z.1 τ).det ^ shiftOf lam τ) *
    eval (fun x : Tau × Fin (P.m + 1) × Fin (P.m + 1) => (K x.1 * z.1 x.1) x.2.1 x.2.2) (ten g) = _
  simp only [ten, map_prod, eval_rename, Function.comp_def, shiftOf]

theorem evC_gen (G : Tau → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ)
    (f : ∀ v, Fin (P.n' v) → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℤ)
    (ft : Tau → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℤ)
    (hid : ∀ x : Σ v : Fin P.nV, Fin (P.n' v), BlockRealisation P pos lam M N embLL x (f x.1 x.2) (ft (pos x))) (z : Frames G) :
    evC P rfl pos G (mcOf M embLL) (map embLL (gen P rfl pos N f)) z =
      fnOf G (shiftOf lam) (kcOf M N embLL) (ten fun τ => map (Int.castRingHom ℂ) (ft τ)) z := by
  rw [map_gen, evC_prod, fnOf_ten, ← pos.prod_comp, Fintype.prod_sigma]
  exact Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun s _ => hid ⟨v, s⟩ z.1 z.2

theorem span_to_int (hodd : ∀ (m : ℕ) (lam : Fin (m + 1) → ℤ), Antitone lam → OddFact (K := ℂ) ℤ m lam)
    (hw : WtTie P rfl pos lam) (G : Tau → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ) (R0 : Subring LL) (Q : XR P LL)
    (hQ : Q ∈ Submodule.span R0 (genSet P rfl pos N)) :
    ∃ Pp ∈ IntSpanG embLL R0 lam, ∀ z : Frames G,
      evC P rfl pos G (mcOf M embLL) (map embLL Q) z = fnOf G (shiftOf lam) (kcOf M N embLL) Pp z := by
  induction hQ using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨f, hf, rfl⟩ := hq
    choose ft0 hft0 hev using fun x : Σ v : Fin P.nV, Fin (P.n' v) =>
      (blk_ev P pos lam M N embLL hodd hw x).1 (f x.1 x.2) (hf x.1 x.2)
    refine ⟨embLL 1 • ten (fun τ => map (Int.castRingHom ℂ) (ft0 (pos.symm τ))),
      AddSubgroup.subset_closure ⟨1, fun τ => ft0 (pos.symm τ), R0.one_mem, fun τ => ?_, rfl⟩, fun z => ?_⟩
    · have h1 := hft0 (pos.symm τ)
      rwa [pos.apply_symm_apply] at h1
    · rw [map_one, one_smul]
      refine evC_gen P pos lam M N embLL G f (fun τ => ft0 (pos.symm τ)) (fun x => ?_) z
      show BlockRealisation P pos lam M N embLL x (f x.1 x.2) (ft0 (pos.symm (pos x)))
      rw [pos.symm_apply_apply]
      exact hev x
  | zero => exact ⟨0, zero_mem _, fun z => by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨A, hA, e1⟩ := ha
    obtain ⟨B, hB, e2⟩ := hb
    exact ⟨A + B, add_mem hA hB, fun z => by
      rw [map_add, map_add, map_add, Pi.add_apply, Pi.add_apply, e1 z, e2 z]⟩
  | smul r a _ ha =>
    obtain ⟨A, hA, e1⟩ := ha
    refine ⟨embLL r.1 • A, core_intSpanG_smul embLL R0 lam r.1 r.2 hA, fun z => ?_⟩
    rw [Subring.smul_def, Cmp.map_smul', map_smul, map_smul, Pi.smul_apply, Pi.smul_apply, e1 z]

theorem int_to_span (hodd : ∀ (m : ℕ) (lam : Fin (m + 1) → ℤ), Antitone lam → OddFact (K := ℂ) ℤ m lam)
    (hw : WtTie P rfl pos lam) (G : Tau → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ) (R0 : Subring LL)
    (Pp : MvPolynomial (Tau × Fin (P.m + 1) × Fin (P.m + 1)) ℂ) (hP : Pp ∈ IntSpanG embLL R0 lam) :
    ∃ Q ∈ Submodule.span R0 (genSet P rfl pos N), ∀ z : Frames G,
      evC P rfl pos G (mcOf M embLL) (map embLL Q) z = fnOf G (shiftOf lam) (kcOf M N embLL) Pp z := by
  unfold IntSpanG at hP
  induction hP using AddSubgroup.closure_induction with
  | mem q hq =>
    obtain ⟨r, ft, hr, hft, rfl⟩ := hq
    choose f hf hev using fun x : Σ v : Fin P.nV, Fin (P.n' v) =>
      (blk_ev P pos lam M N embLL hodd hw x).2 (ft (pos x)) (hft (pos x))
    refine ⟨(⟨r, hr⟩ : R0) • gen P rfl pos N (fun v s => f ⟨v, s⟩),
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨fun v s => f ⟨v, s⟩, fun v s => hf ⟨v, s⟩, rfl⟩), fun z => ?_⟩
    rw [Subring.smul_def, Cmp.map_smul', map_smul, map_smul, Pi.smul_apply, Pi.smul_apply]
    congr 1
    exact evC_gen P pos lam M N embLL G (fun v s => f ⟨v, s⟩) ft (fun x => hev x) z
  | zero => exact ⟨0, zero_mem _, fun z => by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨A, hA, e1⟩ := ha
    obtain ⟨B, hB, e2⟩ := hb
    exact ⟨A + B, add_mem hA hB, fun z => by
      rw [map_add, map_add, map_add, Pi.add_apply, Pi.add_apply, e1 z, e2 z]⟩
  | neg a _ ha =>
    obtain ⟨A, hA, e1⟩ := ha
    exact ⟨-A, neg_mem hA, fun z => by
      rw [map_neg, map_neg, map_neg, Pi.neg_apply, Pi.neg_apply, e1 z]⟩

end Ev

end Formalism.L2.G.RelativeIndexFlags.Core

namespace Formalism.L2.G.RelativeIndexFlags

open Formalism.L2.G.Cmp Formalism.L2.G.RelativeIndexFlags.Core

theorem weylLatticeDescent_of_valuation (hD : DescVal)
    (hodd : ∀ (m : ℕ) (lam : Fin (m + 1) → ℤ), Antitone lam → OddFact (K := ℂ) ℤ m lam) : WeylLatticeDescent := by
  intro p O Kf _ _ _ _ _ P Tau _ n LL _ h pos G embLL e R0 hfr hR0 lam hw M N L HL Q
  subst h
  unfold CoreAt
  rw [mem_htupW_iff P rfl pos N hD hfr e R0 hR0 L HL Q]
  constructor
  · intro hQ
    exact span_to_int P pos lam M N embLL hodd hw G R0 Q hQ
  · rintro ⟨Pp, hPp, hev⟩
    obtain ⟨Q', hQ', hev'⟩ := int_to_span P pos lam M N embLL hodd hw G R0 Pp hPp
    have h0 := Formalism.L2.G.evC_inj P rfl pos G (mcOf M embLL) (fun τ => gl_map_det embLL (M τ))
      (map embLL Q - map embLL Q') (by
        funext z
        rw [map_sub, Pi.sub_apply, hev z, hev' z, sub_self]
        rfl)
    have h1 : Q = Q' := map_injective embLL embLL.injective (sub_eq_zero.1 h0)
    rw [h1]; exact hQ'

theorem weylLatticeDescent_of_integral_models
    (hodd : ∀ (m : ℕ) (lam : Fin (m + 1) → ℤ), Antitone lam → OddFact (K := ℂ) ℤ m lam) : WeylLatticeDescent :=
  weylLatticeDescent_of_valuation descVal hodd

end Formalism.L2.G.RelativeIndexFlags
