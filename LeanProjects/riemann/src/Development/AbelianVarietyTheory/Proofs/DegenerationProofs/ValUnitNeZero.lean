import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsBasisB
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace GlobalTheory.ZH.FrameNorm
open CrdCalc

section Reg
variable {K C : Type} [Field K] [Field C] {Y : Scheme.{0}} {q : Y ⟶ Sp K} {σ : K →+* C}

variable (q σ) in

def Reg (W : Y.Opens) (F : (Sp C ⟶ Y) → C) : Prop :=
  ∃ r : Γ(Y, W), ∀ x : Sp C ⟶ Y, x ≫ q = spMap σ → ⊤ ≤ x ⁻¹ᵁ W → F x = valR x W r

variable {W : Y.Opens} {F G : (Sp C ⟶ Y) → C}

theorem Reg.mul (hF : Reg q σ W F) (hG : Reg q σ W G) : Reg q σ W fun x => F x * G x := by
  obtain ⟨r, hr⟩ := hF
  obtain ⟨s, hs⟩ := hG
  exact ⟨r * s, fun x hx hW => by rw [valR_mul x W hW, ← hr x hx hW, ← hs x hx hW]⟩

theorem Reg.pow (hF : Reg q σ W F) (n : ℕ) : Reg q σ W fun x => F x ^ n := by
  obtain ⟨r, hr⟩ := hF
  exact ⟨r ^ n, fun x hx hW => by
    beta_reduce
    rw [hr x hx hW, valR_eq x W hW, valR_eq x W hW, map_pow]⟩

theorem Reg.sum {I : Type} [Fintype I] {F : I → (Sp C ⟶ Y) → C} (hF : ∀ i, Reg q σ W (F i)) :
    Reg q σ W fun x => ∑ i, F i x := by
  choose r hr using hF
  refine ⟨∑ i, r i, fun x hx hW => ?_⟩
  rw [valR_eq x W hW, map_sum]
  exact Finset.sum_congr rfl fun i _ => (hr i x hx hW).trans (valR_eq x W hW _)

theorem Reg.const (a : K) : Reg q σ W fun _ => σ a :=
  ⟨constFn q W a, fun x hx hW => (GlobalTheory.Points.valR_constFn_of_over q σ x hx W hW a).symm⟩

theorem Reg.pull {X : Scheme.{0}} (g : Y ⟶ X) {U : X.Opens} (h : W ≤ g ⁻¹ᵁ U) (s : Γ(X, U)) :
    Reg q σ W fun x => valR (x ≫ g) U s :=
  ⟨(g.appLE U W h).hom s, fun x _ hW => (GlobalTheory.Points.valR_appLE x g h hW s).symm⟩

theorem Reg.inv_unit {X : Scheme.{0}} (g : Y ⟶ X) {U : X.Opens} (h : W ≤ g ⁻¹ᵁ U) (s : Γ(X, U)ˣ) :
    Reg q σ W fun x => (valR (x ≫ g) U s.val)⁻¹ := by
  refine ⟨(g.appLE U W h).hom (s⁻¹).val, fun x _ hW => ?_⟩
  have hU : ⊤ ≤ (x ≫ g) ⁻¹ᵁ U := fun _ hz => h (hW hz)
  rw [GlobalTheory.Points.valR_appLE x g h hW]
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← valR_mul _ U hU, Units.mul_inv, valR_eq _ U hU, map_one]

theorem Reg.inv_basicOpen {X : Scheme.{0}} (g : Y ⟶ X) {U : X.Opens} (s : Γ(X, U))
    (h : W ≤ g ⁻¹ᵁ X.basicOpen s) : Reg q σ W fun x => (valR (x ≫ g) U s)⁻¹ := by
  obtain ⟨r, hr⟩ := Reg.inv_unit (q := q) (σ := σ) g h (X.toRingedSpace.isUnit_res_basicOpen s).unit
  refine ⟨r, fun x hx hW => ?_⟩
  rw [← hr x hx hW]
  exact congrArg _ (valR_res (x ≫ g) (X.basicOpen_le s) (fun _ hz => h (hW hz)) s).symm

end Reg

section Val
variable {C : Type} [Field C] {X Y : Scheme.{0}}

theorem val_unit_ne_zero (x : Sp C ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (s : Γ(X, U)ˣ) :
    valR x U s.val ≠ 0 := by
  rw [valR_eq x U h]
  exact (s.isUnit.map _).ne_zero

theorem val_zpow (x : Sp C ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (s : Γ(X, U)ˣ) (n : ℤ) :
    valR x U (s ^ n).val = valR x U s.val ^ n := by
  rw [valR_eq x U h, valR_eq x U h, ← MonoidHom.coe_coe, ← Units.coe_map, map_zpow, Units.val_zpow_eq_zpow_val]
  rfl

theorem val_res_pull (x : Sp C ⟶ Y) (g : Y ⟶ X) {U : X.Opens} {W : Y.Opens} (e : W ≤ g ⁻¹ᵁ U)
    (h : ⊤ ≤ x ⁻¹ᵁ W) (s : Γ(X, U)ˣ) : valR x W (res e (pullU g U s)).val = valR (x ≫ g) U s.val :=
  GlobalTheory.Points.valR_appLE x g e h s.val

def tv (L : LB X) (x : Sp C ⟶ X) (i j : L.ι) : C := valR x (L.U i ⊓ L.U j) (L.g i j).val

theorem tv_ne_zero (L : LB X) {x : Sp C ⟶ X} {i j : L.ι} (hi : ⊤ ≤ x ⁻¹ᵁ L.U i) (hj : ⊤ ≤ x ⁻¹ᵁ L.U j) :
    tv L x i j ≠ 0 := val_unit_ne_zero x (U := L.U i ⊓ L.U j) (fun _ hz => ⟨hi hz, hj hz⟩) _

theorem tv_self {L : LB X} (hL : L.IsLB) {x : Sp C ⟶ X} {i : L.ι} (hi : ⊤ ≤ x ⁻¹ᵁ L.U i) :
    tv L x i i = 1 := by
  have e := congrArg (fun u : Γ(X, L.U i)ˣ => valR x (L.U i) u.val) (hL.g_self i)
  refine (valR_res x (le_inf le_rfl le_rfl) hi _).symm.trans (e.trans ?_)
  rw [valR_eq x _ hi, Units.val_one, map_one]

theorem le_wchart {L : LB X} {I : Type} [Fintype I] {φ : I → (Y ⟶ X)} {x : Sp C ⟶ Y} {j : I → L.ι}
    (h : ∀ k, ⊤ ≤ (x ≫ φ k) ⁻¹ᵁ L.U (j k)) : ⊤ ≤ x ⁻¹ᵁ LB.wchart L φ j :=
  fun _ hz => Set.mem_iInter.2 fun k => h k hz

theorem tv_linComb (L : LB X) {I : Type} [Fintype I] (φ : I → (Y ⟶ X)) (ε : I → ℤ) {x : Sp C ⟶ Y}
    {j j' : I → L.ι} (h : ∀ k, ⊤ ≤ (x ≫ φ k) ⁻¹ᵁ L.U (j k)) (h' : ∀ k, ⊤ ≤ (x ≫ φ k) ⁻¹ᵁ L.U (j' k)) :
    tv (LB.LinComb L φ ε) x j j' = ∏ k, tv L (x ≫ φ k) (j k) (j' k) ^ ε k := by
  have hh : ⊤ ≤ x ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j') := fun _ hz => ⟨le_wchart h hz, le_wchart h' hz⟩
  have A : ∀ u : I → Γ(Y, LB.wchart L φ j ⊓ LB.wchart L φ j')ˣ,
      valR x _ (∏ k, u k ^ ε k).val = ∏ k, valR x _ (u k).val ^ ε k := fun u => by
    rw [valR_eq x _ hh, Units.coe_prod, map_prod]
    exact Finset.prod_congr rfl fun k _ => (valR_eq x _ hh _).symm.trans (val_zpow x hh _ _)
  refine (A _).trans (Finset.prod_congr rfl fun k _ => ?_)
  exact congrArg (· ^ ε k) (val_res_pull x (φ k) (U := L.U (j k) ⊓ L.U (j' k)) _ hh (L.g (j k) (j' k)))

theorem sec_val {L : LB X} (s : L.Sec) {x : Sp C ⟶ X} {i j : L.ι} (hi : ⊤ ≤ x ⁻¹ᵁ L.U i)
    (hj : ⊤ ≤ x ⁻¹ᵁ L.U j) : valR x (L.U i) (s.f i) = tv L x i j * valR x (L.U j) (s.f j) := by
  have hh : ⊤ ≤ x ⁻¹ᵁ (L.U i ⊓ L.U j) := fun y hy => ⟨hi hy, hj hy⟩
  have e := congrArg (valR x (L.U i ⊓ L.U j)) (s.compat i j)
  rw [valR_mul x _ hh] at e
  exact (valR_res x inf_le_left hh _).symm.trans (e.trans (congrArg _ (valR_res x inf_le_right hh _)))

theorem gen_val {L : LB X} {t : L.Gen} (ht : t.IsGen) {x : Sp C ⟶ X} {i j : L.ι} (hi : ⊤ ≤ x ⁻¹ᵁ L.U i)
    (hj : ⊤ ≤ x ⁻¹ᵁ L.U j) : valR x (L.U i) (t.s i).val = tv L x i j * valR x (L.U j) (t.s j).val :=
  sec_val ⟨fun i => (t.s i).val, fun i j => congrArg Units.val (ht i j)⟩ hi hj

end Val

structure IsoVal {K C : Type} [Field K] [Field C] {X H Y : Scheme.{0}} (q : Y ⟶ Sp K) (σ : K →+* C)
    (L : LB X) (M : LB H) (ψ : Y ⟶ X) (j : Y ⟶ H) (ω : (Sp C ⟶ Y) → M.ι → L.ι → C) : Prop where
  ne : ∀ x l m, ⊤ ≤ (x ≫ j) ⁻¹ᵁ M.U l → ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U m → ω x l m ≠ 0
  left : ∀ x l l' m, ⊤ ≤ (x ≫ j) ⁻¹ᵁ M.U l → ⊤ ≤ (x ≫ j) ⁻¹ᵁ M.U l' → ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U m →
    ω x l m = tv M (x ≫ j) l l' * ω x l' m
  right : ∀ x l m m', ⊤ ≤ (x ≫ j) ⁻¹ᵁ M.U l → ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U m → ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U m' →
    ω x l m * tv L (x ≫ ψ) m m' = ω x l m'
  reg : ∀ (g : Y ⟶ Y) (W : Y.Opens) l m, W ≤ (g ≫ j) ⁻¹ᵁ M.U l → W ≤ (g ≫ ψ) ⁻¹ᵁ L.U m →
    Reg q σ W (fun x => ω (x ≫ g) l m) ∧ Reg q σ W (fun x => (ω (x ≫ g) l m)⁻¹)

theorem exists_isoVal {K C : Type} [Field K] [Field C] {X H Y : Scheme.{0}} (q : Y ⟶ Sp K) (σ : K →+* C)
    {L : LB X} {M : LB H} (hL : L.IsLB) (hM : M.IsLB) {ψ : Y ⟶ X} {j : Y ⟶ H}
    (h : LBIso (L.pull ψ) (M.pull j)) : ∃ ω, IsoVal q σ L M ψ j ω := by
  obtain ⟨w, hw⟩ := h
  have mem : ∀ {x : Sp C ⟶ Y} {l m}, ⊤ ≤ (x ≫ j) ⁻¹ᵁ M.U l → ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U m →
      ⊤ ≤ x ⁻¹ᵁ (LB.div (M.pull j) (L.pull ψ)).U (fun _ => l, fun _ => m) := fun hl hm _ hz =>
    ⟨Set.mem_iInter.2 fun _ => hl hz, Set.mem_iInter.2 fun _ => hm hz⟩
  have key : ∀ (x : Sp C ⟶ Y) l l' m m', ⊤ ≤ (x ≫ j) ⁻¹ᵁ M.U l → ⊤ ≤ (x ≫ j) ⁻¹ᵁ M.U l' →
      ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U m → ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U m' →
      valR x _ (w.s (fun _ => l, fun _ => m)).val =
        tv M (x ≫ j) l l' * (tv L (x ≫ ψ) m m')⁻¹ * valR x _ (w.s (fun _ => l', fun _ => m')).val := by
    intro x l l' m m' hl hl' hm hm'
    refine (gen_val hw (mem hl hm) (mem hl' hm')).trans (congrArg (· * _) ?_)
    have hh : ⊤ ≤ x ⁻¹ᵁ ((LB.div (M.pull j) (L.pull ψ)).U (fun _ => l, fun _ => m) ⊓
        (LB.div (M.pull j) (L.pull ψ)).U (fun _ => l', fun _ => m')) :=
      fun _ hz => ⟨mem hl hm hz, mem hl' hm' hz⟩
    refine (valR_mul x _ hh _ _).trans (congrArg₂ (· * ·) ?_ ?_)
    · refine (valR_res x _ hh _).trans ((tv_linComb M _ _ (fun _ => hl) (fun _ => hl')).trans ?_)
      simp
    · rw [← zpow_neg_one, ← zpow_neg_one]
      refine (val_zpow x hh _ _).trans (congrArg (· ^ (-1 : ℤ)) ?_)
      refine (valR_res x _ hh _).trans ((tv_linComb L _ _ (fun _ => hm) (fun _ => hm')).trans ?_)
      simp
  refine ⟨fun x l m => valR x _ (w.s (fun _ => l, fun _ => m)).val,
    fun x l m hl hm => val_unit_ne_zero x (mem hl hm) _, fun x l l' m hl hl' hm => ?_,
    fun x l m m' hl hm hm' => ?_, fun g W l m hl hm => ?_⟩
  · rw [key x l l' m m hl hl' hm hm, tv_self hL hm, inv_one, _root_.mul_one]
  · rw [key x l l m m' hl hl hm hm', tv_self hM hl, _root_.one_mul, mul_right_comm,
      inv_mul_cancel₀ (tv_ne_zero L hm hm'), _root_.one_mul]
  · have e : W ≤ g ⁻¹ᵁ (LB.div (M.pull j) (L.pull ψ)).U (fun _ => l, fun _ => m) := fun _ hz =>
      ⟨Set.mem_iInter.2 fun _ => hl hz, Set.mem_iInter.2 fun _ => hm hz⟩
    exact ⟨Reg.pull g e _, Reg.inv_unit g e _⟩

end GlobalTheory.ZH.FrameNorm
end
