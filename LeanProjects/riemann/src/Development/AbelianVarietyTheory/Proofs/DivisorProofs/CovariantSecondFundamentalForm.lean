import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HermitianCurvatureForms
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CovariantDbarLeibniz

open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V]
variable {m l n : Type*} [Fintype m] [Fintype l] [Fintype n]
  [DecidableEq m] [DecidableEq l] [DecidableEq n]

def SameJet {k : Type*} (u u' : V → k → ℂ) (z : V) : Prop :=
  ∀ a, u z a = u' z a ∧ ∃ D : V →L[ℝ] ℂ,
    HasFDerivAt (fun x => u x a) D z ∧ HasFDerivAt (fun x => u' x a) D z

section Jet

variable {k : Type*} {u u' v v' : V → k → ℂ} {z : V}

omit [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V] in

theorem SameJet.val (h : SameJet u u' z) : u z = u' z := funext fun a => (h a).1

omit [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V] in

theorem SameJet.add (h : SameJet u u' z) (h' : SameJet v v' z) :
    SameJet (fun x => u x + v x) (fun x => u' x + v' x) z := fun a => by
  obtain ⟨e, D, h1, h2⟩ := h a
  obtain ⟨e', D', h1', h2'⟩ := h' a
  exact ⟨by simp [e, e'], D + D', h1.add h1', h2.add h2'⟩

omit [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V] in

theorem SameJet.mulVec [Fintype k] {p : Type*} {M : V → Matrix p k ℂ} (hM : MContDiffAt 1 M z)
    (h : SameJet u u' z) : SameJet (fun x => M x *ᵥ u x) (fun x => M x *ᵥ u' x) z := fun a => by
  choose e D h1 h2 using h
  refine ⟨by simp [Matrix.mulVec, dotProduct, e],
    ∑ b, (M z a b • D b + u' z b • fderiv ℝ (fun x => M x a b) z), ?_, ?_⟩
  · simp only [← e]
    exact HasFDerivAt.fun_sum fun b _ => (hM.diff a b).hasFDerivAt.mul (h1 b)
  · exact HasFDerivAt.fun_sum fun b _ => (hM.diff a b).hasFDerivAt.mul (h2 b)

theorem SameJet.covDel [Fintype k] [DecidableEq k] (h : SameJet u u' z) (K : V → Matrix k k ℂ)
    (ξ : V) : covDel K u z ξ = covDel K u' z ξ := by
  rw [HermFrame.covDel, HermFrame.covDel, h.val]
  congr 1
  funext a
  obtain ⟨-, D, h1, h2⟩ := h a
  rw [del_eq_of_hasFDerivAt h1, del_eq_of_hasFDerivAt h2]

theorem SameJet.secDbar (h : SameJet u u' z) (ξ : V) :
    HermitianCurvatureForms.secDbar u z ξ = HermitianCurvatureForms.secDbar u' z ξ := by
  funext a
  obtain ⟨-, D, h1, h2⟩ := h a
  rw [HermitianCurvatureForms.secDbar, HermitianCurvatureForms.secDbar, dbar_eq_of_hasFDerivAt h1, dbar_eq_of_hasFDerivAt h2]

end Jet

variable {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V}

omit [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V] in

theorem mContDiffAt_orthLift {k : WithTop ℕ∞} (h : MContDiffAt k H z)
    (hs : IsUnit (subGram (H z)).det) : MContDiffAt k (fun x => orthLift (H x)) z := by
  have hc : MContDiffAt k (fun x => orthCoeff (H x)) z :=
    (h.subGram.transpose.inv (by rwa [det_transpose])).mul (h.submatrix Sum.inr Sum.inl).transpose
  rintro (a | a) b
  exacts [hc.neg a b, contDiffAt_const]

theorem trace_eq_blocks (K T : Matrix (m ⊕ l) (m ⊕ l) ℂ) :
    T.trace = (blockSS K T).trace + (blockQQ K T).trace := by
  rw [blockSS, blockQQ, trace_mul_cycle, trace_mul_cycle (quotMap m l), ← trace_add,
    ← Matrix.add_mul, incl_mul_orthProj_add, Matrix.one_mul]

def BodyA (U : Set V) (H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ) : Prop :=
  (IsHermFrame U H → (∀ z ∈ U, IsUnit (subGram (H z)).det) →
    IsHermFrame U (HermitianCurvatureForms.gramS H) ∧ IsHermFrame U (HermitianCurvatureForms.gramQ H) ∧
      ∀ z ∈ U, HermitianCurvatureForms.SubQuotAt H z) ∧
  (IsPosFrame U H →
    IsPosFrame U (HermitianCurvatureForms.gramS H) ∧ IsPosFrame U (HermitianCurvatureForms.gramQ H) ∧
    (∀ z ∈ U, HermitianCurvatureForms.SecondFormSignAt H z ∧ HermitianCurvatureForms.ExtBlocksAt H z ∧ HermitianCurvatureForms.AnyRankAt H z) ∧
    (Fintype.card m = 1 → Fintype.card l = 1 → ∀ z ∈ U, HermitianCurvatureForms.RankTwoAt H z))

def BodyB (U : Set V) (H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ) : Prop :=
  (IsHermFrame U H → (∀ z ∈ U, IsUnit (CovariantDbarLeibniz.subField H z).det) →
    IsHermFrame U (CovariantDbarLeibniz.subField H) ∧ IsHermFrame U (CovariantDbarLeibniz.quotField H) ∧
      ∀ z ∈ U, CovariantDbarLeibniz.SubQuotAt H z) ∧
  (∀ [Unique m] [Unique l], IsPosFrame U H →
    ∀ z ∈ U, CovariantDbarLeibniz.ExtBlocksAt H z ∧ CovariantDbarLeibniz.RankTwoAt H z) ∧
  (IsPosFrame U H → ∀ z ∈ U, CovariantDbarLeibniz.ExtBlocksAt H z ∧ CovariantDbarLeibniz.ChTwoAt H z)

omit [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V] in

theorem isUnit_sub (h : IsPosFrame U H) (z : V) (hz : z ∈ U) : IsUnit (subGram (H z)).det :=
  h.sub.isHermFrame.isUnit z hz

section Pull

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedSpace ℝ W]
  [IsScalarTower ℝ ℂ W] (L : W →L[ℂ] V) {w : W}

variable {K : V → Matrix n n ℂ}

variable (h : IsHermFrame U H) (hs : ∀ z ∈ U, IsUnit (subGram (H z)).det)
include h

include hs

end Pull

section Smooth

variable (h : IsHermFrame U H) (hs : ∀ z ∈ U, IsUnit (subGram (H z)).det) (hz : z ∈ U)
include h hs hz

omit hs in

theorem smooth_secondForm (ξ : V) : MContDiffAt ∞ (fun x => secondForm H x ξ) z :=
  ((mContDiffAt_const _).mul ((h.mContDiffAt hz).conn (h.isUnit z hz) le_rfl ξ)).mul
    (mContDiffAt_const _)

theorem smooth_secondFormAdj (ξ : V) : MContDiffAt ∞ (fun x => secondFormAdj H x ξ) z :=
  ((((h.sub hs).mContDiffAt hz).transpose.inv (by rw [det_transpose]; exact hs z hz)).mul
    (smooth_secondForm h hz ξ).conjTranspose).mul ((h.quot hs).mContDiffAt hz).transpose

theorem smooth_extForm (ξ : V) : MContDiffAt ∞ (fun x => extForm H x ξ) z := by
  have hl := mContDiffAt_orthLift (h.mContDiffAt hz) (hs z hz)
  simp only [extForm_eq_neg_mdbar]
  have hc : MContDiffAt ∞ (fun x => orthCoeff (H x)) z := fun a b => by
    simpa [orthLift] using hl.neg (.inl a) b
  exact (hc.mdbar le_rfl ξ).neg

theorem smooth_extFormAdj (ξ : V) : MContDiffAt ∞ (fun x => extFormAdj H x ξ) z :=
  ((((h.quot hs).mContDiffAt hz).transpose.inv
    (by rw [det_transpose]; exact (h.quot hs).isUnit z hz)).mul
    (smooth_extForm h hs hz ξ).conjTranspose).mul ((h.sub hs).mContDiffAt hz).transpose

end Smooth

def Above (H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z : V)
    (P : ((Fin 5 → ℂ) → Matrix (m ⊕ l) (m ⊕ l) ℂ) → (Fin 5 → ℂ) → Prop) : Prop :=
  ∀ (L : (Fin 5 → ℂ) →L[ℂ] V) (w : Fin 5 → ℂ), L w = z → P (fun x => H (L x)) w

section Descend

variable {p q : Type*}

variable (h : IsHermFrame U H) (hs : ∀ z ∈ U, IsUnit (subGram (H z)).det) (hz : z ∈ U)
include h hs hz

end Descend

end GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm
