import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.UniformityLowerBounds
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.DeltaIsGreatest
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsOperators
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPtEqUnitMulTh
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionPointsOfSquareLevel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymLiftGlobal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UtestGeomNonempty
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ThetaPtSupportMeetsEveryCoset
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.RealCompare
open GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds hiding fn PsiNorm

section General
variable {B : Scheme.{0}}

theorem exists_heis (hL : Laws) [IsLocallyNoetherian B] (P : PolAV B) {k : ℕ} (hk : Odd k) (hu : IsUnit (k : Γ(B, ⊤)))
    {T : Over B} {x : T ⟶ P.A} (hx : x ^ k = 1) {U : ThetaGrp P.A P.L k T} (hU : SymLift P.A P.L k k x U)
    (s s' : LB.Sec (LPow P.A P.L k T)) : IsHeis P k x s s' ↔ IsActOf P.A P.L k U s s' := by
  refine ⟨fun ⟨_, U', hU', H⟩ => ?_, fun H => ⟨hx, U, hU, H⟩⟩
  have hc := (hL.symLift B P k hk hu T x hx).2 U U' hU hU'
  have e := hU.pt_eq.trans hU'.pt_eq.symm
  obtain ⟨y, φ, hφ⟩ := U
  obtain ⟨y', φ', hφ'⟩ := U'
  obtain rfl : y = y' := e
  refine VVRank.isTwistPull_of_sv P.A P.isLB hφ fun z J hJ => ?_
  exact (VVRank.sv_of_isTwistPull P.A H _ z hJ).trans
    (congrArg (fun q : ((T ⊗ P.A).left.presheaf.stalk z)ˣ => q.val * _) (val_corr hJ hc _).symm)

theorem exists_heis_linear (hL : Laws) [IsLocallyNoetherian B] (P : PolAV B) {k : ℕ} (hk : Odd k)
    (hu : IsUnit (k : Γ(B, ⊤))) {T : Over B} {x : T ⟶ P.A} (hx : x ^ k = 1) :
    ∃ u : SecM P.A P.L k T →ₗ[Γ(T.left, ⊤)] SecM P.A P.L k T,
      ∀ s s', IsHeis P k x s s' ↔ u (SecM.ofSec P.A s) = SecM.ofSec P.A s' := by
  obtain ⟨U, hU⟩ := GlobalTheory.exists_symLift_global hL B P k hk hu T x hx
  obtain ⟨r, hr, -⟩ := GlobalTheory.thetaGrp_acts_linearly hL.globalFns B P k T
  exact ⟨(r U).toLinearMap, fun s s' => (exists_heis hL P hk hu hx hU s s').trans (hr _ _ _)⟩

theorem isValueAt_sum {A : Over B} [GrpObj A] {L : LB A.left} (hL : L.IsLB) {k : ℤ} {T : Over B} {x : T ⟶ A} {τ}
    {I : Type} [Fintype I] (c v : I → Γ(T.left, ⊤)) (s : I → LB.Sec (LPow A L k T))
    (h : ∀ i, IsValueAt A L k (s i) x τ (v i)) {σ : LB.Sec (LPow A L k T)}
    (e : SecM.ofSec A σ = ∑ i, c i • SecM.ofSec A (s i)) : IsValueAt A L k σ x τ (∑ i, c i * v i) := by
  refine ThetaPtMove.isValueAt_of_sv hL fun y J hJ => ?_
  have a := (congrArg (fun q => ThetaAct.sv q (𝟙 _ ≫ (ptSecT A x).left) y J) e).trans (ThetaGeom.sv_sum _ _ _ y hJ)
  refine a.trans ?_
  have g : gs (𝟙 T.left) y ⊤ (∑ i, c i * v i) = ∑ i, gs (𝟙 T.left) y ⊤ (c i) * gs (𝟙 T.left) y ⊤ (v i) := by
    simp only [gs_eq (𝟙 T.left) y ⊤ trivial, map_sum, map_mul]
  rw [g, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Category.assoc, ThetaPtMove.ptSecT_fst, Category.comp_id, _root_.mul_assoc]
  exact congrArg (_ * ·) (ThetaPtMove.sv_of_isValueAt (h i) (𝟙 _) y hJ)

theorem norm_iff (P : PolAV B) (rig : LB.Gen (P.L.pull (eSec P.A))) (k : ℕ) (a : ℤ) (T : Over B)
    (α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ k).left] ![a, -1])) :
    LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ α (ptSecT P.A 1).left)
      (LB.mulGen P.L _ _ _ _ (rigT P.A P.L rig T a) (LB.invGen P.L _ _ (rigT P.A P.L rig T 1))) ↔
    LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ α (ptSecT P.A 1).left)
      (LB.mulGen P.L _ _ _ _ (rigT P.A P.L rig T a) (rigT P.A P.L rig T (-1))) := by
  have key : ∀ y J, Good P.L y J →
      val (LB.mulGen P.L _ _ _ _ (rigT P.A P.L rig T a) (LB.invGen P.L _ _ (rigT P.A P.L rig T 1))) (𝟙 _) y J =
      val (LB.mulGen P.L _ _ _ _ (rigT P.A P.L rig T a) (rigT P.A P.L rig T (-1))) (𝟙 _) y J := fun y J hJ => by
    rw [val_mul hJ, val_mul hJ, val_inv, ThetaCompare.val_rigT _ 1 hJ, ThetaCompare.val_rigT _ (-1) hJ, zpow_neg]
  exact ⟨fun H => corr_of_val P.isLB fun y J hJ => (val_corr hJ H _).trans (key y J hJ),
    fun H => corr_of_val P.isLB fun y J hJ => (val_corr hJ H _).trans (key y J hJ).symm⟩

open SquareLevel ThetaCoord in

theorem tor_props (hL : Laws) [IsLocallyNoetherian B] (P : PolAV B) (M : ℕ) (ze : Γ(B, ⊤)ˣ) (hM : 1 ≤ M)
    (hu : IsUnit (M : Γ(B, ⊤))) (lev : Out.Level P (M ^ 2) ze) {g : ℕ} (h : P.g = g)
    (pt : (Fin g ⊕ Fin g → ZMod M) → (baseOver B ⟶ P.A))
    (hpt : ∀ a, pt a = linComb lev.pt (fun i => (a (idx h i)).val) ^ M) :
    (∀ a b, pt (a + b) = pt a * pt b) ∧
    (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ B) (z : Over.mk x ⟶ P.A), z ^ M = 1 →
      ∃! a, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver B) ≫ pt a = z) ∧
    ∀ a b, WeilIs P.A P.L (M : ℕ) (pt a) (pt b) (ze ^ (M * (eStd g M a b).val)) := by
  subst h
  have : NeZero M := ⟨by omega⟩
  have hq : ∀ i, (lev.pt i ^ M) ^ M = 1 := fun i => by rw [← pow_mul, ← sq, lev.torsion]
  obtain ⟨pt', h₁, h₂, h₃, -, h₅⟩ := GlobalTheory.exists_torsionPoints_of_squareLevel hL B P M ze hM hu lev
  have e : ∀ a, pt a = lab (fun i => lev.pt i ^ M) (a ∘ (halves P.g).symm) := fun a =>
    (hpt a).trans ((linComb_pow_right _ _ _).trans (linComb_pow_left _ _ _).symm)
  have e' : ∀ a, pt' (a ∘ halves P.g) = lab (fun i => lev.pt i ^ M) a := fun a => by
    refine char_ext (fun a => pt' (a ∘ halves P.g)) _ (fun a b => h₁ _ _) (lab_add hq) (fun i => ?_) a
    obtain ⟨s, rfl⟩ := (halves P.g).surjective i
    have q : (Pi.single (halves P.g s) (1 : ZMod M) : _ → ZMod M) ∘ halves P.g = Pi.single s 1 := by
      funext j
      simp [Pi.single_apply]
    beta_reduce
    rw [q, lab_single hq]
    rcases s with i | i
    · exact (h₅ i _ (halves P.g (.inr i)) rfl (Nat.add_comm _ _)).1
    · exact (h₅ i (halves P.g (.inl i)) _ rfl (Nat.add_comm _ _)).2
  obtain rfl : pt = pt' := funext fun a => by
    rw [e, ← e']
    congr 1
    funext j
    simp
  exact ⟨h₁, h₂, h₃⟩

end General

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem mem_cstSpan (S : ThetaSys o Ω) {M : Type} [AddCommGroup M] [Module Γ((Base S).left, ⊤) M] {X : Set M} {x : M}
    (h : x ∈ X) : x ∈ cstSpan S X := AddSubgroup.subset_closure ⟨1, x, h, by rw [map_one, one_smul]⟩

theorem smul_mem_cstSpan (S : ThetaSys o Ω) {M : Type} [AddCommGroup M] [Module Γ((Base S).left, ⊤) M] {X : Set M}
    (c : o) {x : M} (h : x ∈ cstSpan S X) : cst S c • x ∈ cstSpan S X := by
  induction h using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨d, y, hy, rfl⟩ := hx
    exact AddSubgroup.subset_closure ⟨c * d, y, hy, by rw [map_mul, mul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem cstSpan_le (S : ThetaSys o Ω) {M : Type} [AddCommGroup M] [Module Γ((Base S).left, ⊤) M] {X Y : Set M}
    (h : ∀ x ∈ X, x ∈ cstSpan S Y) : cstSpan S X ≤ cstSpan S Y :=
  (AddSubgroup.closure_le _).2 fun _ ⟨c, x, hx, e⟩ => e ▸ smul_mem_cstSpan S c (h x hx)

theorem mem_cstSpan_range (S : ThetaSys o Ω) {M : Type} [AddCommGroup M] [Module Γ((Base S).left, ⊤) M] {I : Type}
    [Fintype I] (b : I → M) (x : M) : x ∈ cstSpan S (Set.range b) ↔ ∃ c : I → o, x = ∑ i, cst S (c i) • b i := by
  refine ⟨fun h => ?_, fun ⟨c, e⟩ => e ▸ sum_mem fun i _ => smul_mem_cstSpan S _ (mem_cstSpan S ⟨i, rfl⟩)⟩
  induction h using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨d, _, ⟨i, rfl⟩, rfl⟩ := hx
    exact ⟨Pi.single i d, by
      rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, map_zero, zero_smul]) (fun h => (h (Finset.mem_univ i)).elim),
        Pi.single_eq_same]⟩
  | zero => exact ⟨0, (Finset.sum_eq_zero fun i _ => by rw [Pi.zero_apply, map_zero, zero_smul]).symm⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, rfl⟩ := hx
    obtain ⟨d, rfl⟩ := hy
    exact ⟨c + d, by simp [add_smul, Finset.sum_add_distrib]⟩
  | neg x _ hx =>
    obtain ⟨c, rfl⟩ := hx
    exact ⟨-c, by simp⟩

theorem comb_comb (S : ThetaSys o Ω) {M : Type} [AddCommGroup M] [Module Γ((Base S).left, ⊤) M] {I J : Type}
    [Fintype I] [Fintype J] (b : I → M) (A : Matrix I J o) (c : J → o) :
    ∑ j, cst S (c j) • ∑ i, cst S (A i j) • b i = ∑ i, cst S (∑ j, A i j * c j) • b i := by
  simp only [Finset.smul_sum, map_sum, Finset.sum_smul, smul_smul, map_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [mul_comm]

structure Change (S : ThetaSys o Ω) where
  J : Type
  [fin : Fintype J]
  [ne : Nonempty J]
  M : Matrix S.J J o
  M' : Matrix J S.J o
  mul_inv : M * M' = 1
  inv_mul : M' * M = 1
  e : S.Gam → ℕ

attribute [instance] Change.fin Change.ne

def Change.scalar (S : ThetaSys o Ω) (u : oˣ) (e : S.Gam → ℕ) : Change S where
  J := S.J
  M := (u : o) • 1
  M' := (↑u⁻¹ : o) • 1
  mul_inv := by simp [smul_smul]
  inv_mul := by simp [smul_smul]
  e := e

theorem Change.sum_mul {S : ThetaSys o Ω} (c : Change S) (l i : S.J) :
    ∑ j, c.M l j * c.M' j i = if l = i then 1 else 0 :=
  Matrix.mul_apply.symm.trans ((congrFun (congrFun c.mul_inv l) i).trans Matrix.one_apply)

theorem Change.sum_mul' {S : ThetaSys o Ω} (c : Change S) (l i : c.J) :
    ∑ j, c.M' l j * c.M j i = if l = i then 1 else 0 :=
  Matrix.mul_apply.symm.trans ((congrFun (congrFun c.inv_mul l) i).trans Matrix.one_apply)

theorem zeta_ne_zero (S : ThetaSys o Ω) (e : ℕ) : algebraMap o Ω (S.ζ ^ e) ≠ 0 :=
  (((S.prim.isUnit (level_ne_zero S)).pow e).map _).ne_zero

def change (S : ThetaSys o Ω) (c : Change S) : ThetaSys o Ω :=
  { S with
    J := c.J
    fin := c.fin
    ne := c.ne
    ρ := fun a => c.M' * S.ρ a * c.M
    ρ_one := fun a h => by rw [S.ρ_one a h, Matrix.mul_one, c.inv_mul]
    ρ_mul := fun a b => (S.ρ_mul a b).imp fun k hk => by
      rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← hk]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc c.M, c.mul_inv, Matrix.one_mul]
    ρ_add := fun a b h => by
      rw [← S.ρ_add a b h]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc c.M, c.mul_inv, Matrix.one_mul]
    th := fun a => algebraMap o Ω (S.ζ ^ c.e a) * S.th a
    ev := fun a j => ∑ i, algebraMap o Ω (c.M i j) * S.ev a i
    th_mem := fun a => mul_mem (S.R.algebraMap_mem _) (S.th_mem a)
    ev_mem := fun a j => sum_mem fun i _ => mul_mem (S.R.algebraMap_mem _) (S.ev_mem a i)
    supp := by
      rw [← S.supp]
      congr 1
      ext a
      simp only [Set.mem_setOf_eq, ne_eq, mul_eq_zero, zeta_ne_zero S, false_or]
    th_ne := S.th_ne.imp fun a h => mul_ne_zero (zeta_ne_zero S _) h }

def Change.inv {S : ThetaSys o Ω} (c : Change S) : Change (change S c) where
  J := S.J
  M := c.M'
  M' := c.M
  mul_inv := c.inv_mul
  inv_mul := c.mul_inv
  e := fun a => ((S.r * S.N) ^ 2 - 1) * c.e a

theorem change_inv (S : ThetaSys o Ω) (c : Change S) : change (change S c) c.inv = S := by
  have key : ∀ ρ h₁ h₂ h₃ th ev h₄ h₅ h₆ h₇, ρ = S.ρ → th = S.th → ev = S.ev →
      ({ S with
        ρ := ρ, ρ_one := h₁, ρ_mul := h₂, ρ_add := h₃, th := th, ev := ev, th_mem := h₄, ev_mem := h₅
        supp := h₆, th_ne := h₇ } : ThetaSys o Ω) = S := by
    intro ρ _ _ _ th ev _ _ _ _ e₁ e₂ e₃
    subst e₁ e₂ e₃
    rfl
  refine key _ _ _ _ _ _ _ _ _ _ (funext fun a => ?_) (funext fun a => ?_) (funext fun (a : S.Gam) => funext fun (i : S.J) => ?_)
  · show c.M * (c.M' * S.ρ a * c.M) * c.M' = _
    simp only [Matrix.mul_assoc]
    rw [c.mul_inv, Matrix.mul_one, ← Matrix.mul_assoc, c.mul_inv, Matrix.one_mul]
  · show algebraMap o Ω (S.ζ ^ (((S.r * S.N) ^ 2 - 1) * c.e a)) * (algebraMap o Ω (S.ζ ^ c.e a) * S.th a) = _
    rw [← _root_.mul_assoc, ← map_mul, ← pow_add, ← Nat.succ_mul, Nat.succ_eq_add_one,
      Nat.sub_add_cancel (Nat.pos_of_ne_zero (level_ne_zero S)), pow_mul, S.prim.pow_eq_one, one_pow, map_one,
      _root_.one_mul]
  · show ∑ j, algebraMap o Ω (c.M' j i) * ∑ l, algebraMap o Ω (c.M l j) * S.ev a l = _
    have : ∀ l, ∑ j, algebraMap o Ω (c.M' j i) * (algebraMap o Ω (c.M l j) * S.ev a l) =
        algebraMap o Ω (if l = i then 1 else 0) * S.ev a l := fun l => by
      rw [← c.sum_mul, map_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by rw [map_mul]; ring
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [this]
    simp [apply_ite (algebraMap o Ω)]

theorem big_iff (S : ThetaSys o Ω) (h : 7 ≤ S.N) : S.Big ↔ LowerBounds S.g S.N (S.r * S.N) := by
  refine ⟨fun H => ⟨H.1, H.2.1⟩, fun H => ?_⟩
  rcases Nat.eq_zero_or_pos S.g with h0 | h0
  · refine ⟨H.1, H.2, ?_⟩
    rw [h0]
    have := S.r_pos
    simp only [pow_zero, Nat.factorial_zero]
    nlinarith
  · exact RealCase.big_third S h0 H.1 H.2

theorem seven_le {n k N : ℕ} (hn : n.Prime) (hk : 2 ≤ k) (h : N = (n ^ k) ^ 2) : 7 ≤ N := by
  have h1 : 2 ^ 2 ≤ n ^ k := (Nat.pow_le_pow_left hn.two_le 2).trans (Nat.pow_le_pow_right hn.pos hk)
  rw [h]; nlinarith

theorem one_le_j {S : ThetaSys o Ω} (Z : Realisation S) (hg : 1 ≤ S.g) : 1 ≤ Z.j := by
  have h := ((big_iff S (seven_le Z.prime Z.two_le Z.N_eq)).2 Z.bounds).2.2
  by_contra h0
  have hr : S.r = 1 := by rw [Z.r_eq, show Z.j = 0 by omega, pow_zero]
  have h1 : S.N ≤ S.N ^ S.g := Nat.le_self_pow (by omega) _
  have h2 := Nat.factorial_pos S.g
  rw [hr] at h
  nlinarith

end GlobalTheory.RealCompare
end
