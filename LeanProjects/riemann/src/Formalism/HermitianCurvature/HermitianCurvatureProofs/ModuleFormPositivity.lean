import Formalism.HermitianCurvature.HermitianCurvatureProofs.PrStarFst
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TransferWordEntriesMem
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DualKernelLemmas

namespace Formalism.FourierDecayAlt.P.PBF

open Finset Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5.HerA
open scoped ComplexConjugate

section Cls

variable {V : Type} [AddCommGroup V] [Module ℂ V]

structure SesqCls (U : Submodule ℂ V) (β : V → V → ℂ) : Prop where
  herm : ∀ x ∈ U, ∀ y ∈ U, β y x = conj (β x y)
  add_left : ∀ x ∈ U, ∀ x' ∈ U, ∀ y ∈ U, β (x + x') y = β x y + β x' y
  smul_left : ∀ x ∈ U, ∀ y ∈ U, ∀ c : ℂ, β (c • x) y = c * β x y

variable {U : Submodule ℂ V} {β : V → V → ℂ}

theorem SesqCls.add_right (hβ : SesqCls U β) {x y y' : V} (hx : x ∈ U) (hy : y ∈ U) (hy' : y' ∈ U) :
    β x (y + y') = β x y + β x y' := by
  rw [hβ.herm _ (U.add_mem hy hy') _ hx, hβ.add_left _ hy _ hy' _ hx, map_add, ← hβ.herm _ hy _ hx,
    ← hβ.herm _ hy' _ hx]

theorem SesqCls.smul_right (hβ : SesqCls U β) {x y : V} (hx : x ∈ U) (hy : y ∈ U) (c : ℂ) :
    β x (c • y) = conj c * β x y := by
  rw [hβ.herm _ (U.smul_mem c hy) _ hx, hβ.smul_left _ hy _ hx, map_mul, ← hβ.herm _ hy _ hx]

theorem SesqCls.zero_left (hβ : SesqCls U β) {y : V} (hy : y ∈ U) : β 0 y = 0 := by
  have h := hβ.smul_left 0 U.zero_mem y hy 0
  rwa [zero_smul, zero_mul] at h

theorem SesqCls.sum_left (hβ : SesqCls U β) {ι : Type*} (s : Finset ι) (f : ι → V) (hf : ∀ i, f i ∈ U)
    {y : V} (hy : y ∈ U) : β (∑ i ∈ s, f i) y = ∑ i ∈ s, β (f i) y := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, hβ.zero_left hy]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hβ.add_left _ (hf a) _ (U.sum_mem fun i _ => hf i) _ hy, ih]

theorem SesqCls.sum_right (hβ : SesqCls U β) {ι : Type*} (s : Finset ι) (f : ι → V) (hf : ∀ i, f i ∈ U)
    {x : V} (hx : x ∈ U) : β x (∑ i ∈ s, f i) = ∑ i ∈ s, β x (f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, hβ.herm _ U.zero_mem _ hx, hβ.zero_left hx, map_zero]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hβ.add_right hx (hf a) (U.sum_mem fun i _ => hf i), ih]

def adjB (U : Submodule ℂ V) (β : V → V → ℂ) (hβ : SesqCls U β) : StarSubalgebra ℂ (Q.Pr V) where
  carrier := {a | (∀ x ∈ U, a.1 x ∈ U) ∧ (∀ x ∈ U, a.2.unop x ∈ U) ∧
    ∀ x ∈ U, ∀ y ∈ U, β (a.1 x) y = β x (a.2.unop y)}
  mul_mem' := by
    rintro a b ⟨ha1, ha2, ha⟩ ⟨hb1, hb2, hb⟩
    refine ⟨fun x hx => ha1 _ (hb1 x hx), fun x hx => hb2 _ (ha2 x hx), fun x hx y hy => ?_⟩
    change β (a.1 (b.1 x)) y = β x (b.2.unop (a.2.unop y))
    rw [ha _ (hb1 x hx) y hy, hb x hx _ (ha2 y hy)]
  add_mem' := by
    rintro a b ⟨ha1, ha2, ha⟩ ⟨hb1, hb2, hb⟩
    refine ⟨fun x hx => U.add_mem (ha1 x hx) (hb1 x hx), fun x hx => U.add_mem (ha2 x hx) (hb2 x hx),
      fun x hx y hy => ?_⟩
    change β (a.1 x + b.1 x) y = β x (a.2.unop y + b.2.unop y)
    rw [hβ.add_left _ (ha1 x hx) _ (hb1 x hx) _ hy, hβ.add_right hx (ha2 y hy) (hb2 y hy), ha x hx y hy,
      hb x hx y hy]
  algebraMap_mem' := by
    intro c
    refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx y hy => ?_⟩
    · show (algebraMap ℂ (Module.End ℂ V) c) x ∈ U
      rw [Module.algebraMap_end_apply]; exact U.smul_mem c hx
    · show (algebraMap ℂ (Module.End ℂ V) (conj c)) x ∈ U
      rw [Module.algebraMap_end_apply]; exact U.smul_mem _ hx
    · show β ((algebraMap ℂ (Module.End ℂ V) c) x) y = β x ((algebraMap ℂ (Module.End ℂ V) (conj c)) y)
      rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, hβ.smul_left x hx y hy,
        hβ.smul_right hx hy, Complex.conj_conj]
  star_mem' := by
    rintro a ⟨ha1, ha2, ha⟩
    refine ⟨ha2, ha1, fun x hx y hy => ?_⟩
    show β (a.2.unop x) y = β x (a.1 y)
    rw [hβ.herm _ (ha1 y hy) _ hx, ha y hy x hx]
    exact hβ.herm _ hy _ (ha2 x hx)

theorem mem_adjB {hβ : SesqCls U β} {a : Q.Pr V} :
    a ∈ adjB U β hβ ↔ (∀ x ∈ U, a.1 x ∈ U) ∧ (∀ x ∈ U, a.2.unop x ∈ U) ∧
      ∀ x ∈ U, ∀ y ∈ U, β (a.1 x) y = β x (a.2.unop y) := Iff.rfl

end Cls

section Pair

variable {V : Type} [AddCommGroup V] [Module ℂ V] {S : Type} [Fintype S] [DecidableEq S]
variable {U : Submodule ℂ V} {β : V → V → ℂ}

def pairS (β : V → V → ℂ) (X X' : Ix S → V) : ℂ := ∑ z, β (X z) (X' z)

def InU (U : Submodule ℂ V) (X : Ix S → V) : Prop := ∀ z, X z ∈ U

theorem blockMulVec_apply_mem {M : SlopeTestRemainingChoices S (Q.Pr V)} (hM : ∀ a b, ∀ x ∈ U, (M a b).1 x ∈ U) {X : Ix S → V} (hX : InU U X) :
    InU U (actP M X) := fun a => U.sum_mem fun b _ => hM a b _ (hX b)

theorem pairS_adj (hβ : SesqCls U β) (M : SlopeTestRemainingChoices S (Q.Pr V)) (hM : M ∈ entSub (adjB U β hβ)) (X Y : Ix S → V)
    (hX : InU U X) (hY : InU U Y) : pairS β X (actP M Y) = pairS β (actP (star M) X) Y := by
  have hM2 : ∀ a b, M a b ∈ adjB U β hβ := hM
  have hM' := fun a b => (mem_adjB (hβ := hβ)).1 (hM2 a b)
  have key : ∀ z b, β (((star M) z b).1 (X b)) (Y z) = β (X b) ((M b z).1 (Y z)) := by
    intro z b
    have h1 : (M b z).2.unop (X b) ∈ U := (hM' b z).2.1 _ (hX b)
    have h2 : (M b z).1 (Y z) ∈ U := (hM' b z).1 _ (hY z)
    show β ((M b z).2.unop (X b)) (Y z) = _
    rw [hβ.herm _ (hY z) _ h1, ← (hM' b z).2.2 _ (hY z) _ (hX b), ← hβ.herm _ h2 _ (hX b)]
  unfold pairS actP
  rw [Finset.sum_congr rfl fun z _ => hβ.sum_right Finset.univ (fun b => (M z b).1 (Y b))
    (fun b => (hM' z b).1 _ (hY b)) (hX z)]
  rw [Finset.sum_congr rfl fun z _ => hβ.sum_left Finset.univ (fun b => ((star M) z b).1 (X b))
    (fun b => (hM' b z).2.1 _ (hX b)) (hY z)]
  simp_rw [key]
  exact Finset.sum_comm

theorem pairS_smul_left (hβ : SesqCls U β) (c : ℂ) (X Y : Ix S → V) (hX : InU U X) (hY : InU U Y) :
    pairS β (c • X) Y = c * pairS β X Y := by
  unfold pairS
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun z _ => hβ.smul_left _ (hX z) _ (hY z) c

theorem smul_blockMulVec (M : SlopeTestRemainingChoices S (Q.Pr V)) (c : ℂ) (X : Ix S → V) : actP (c • M) X = c • actP M X := by
  funext a
  unfold actP
  rw [Pi.smul_apply, Finset.smul_sum]
  rfl

def frmU (hβ : SesqCls U β) (M : SlopeTestRemainingChoices S (Q.Pr V)) (hM : ∀ a b, ∀ x ∈ U, (M a b).1 x ∈ U) :
    F7.Sesq (Submodule.pi Set.univ (fun _ : Ix S => U)) :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun X X' => pairS β (actP M X.1) X'.1)
    (fun X X' Y => by
      have hX : InU U X.1 := fun z => X.2 z (Set.mem_univ z)
      have hX' : InU U X'.1 := fun z => X'.2 z (Set.mem_univ z)
      have hY : InU U Y.1 := fun z => Y.2 z (Set.mem_univ z)
      show pairS β (actP M (X.1 + X'.1)) Y.1 = _
      rw [blockMulVec_add]
      unfold pairS
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun z _ => hβ.add_left _ (blockMulVec_apply_mem hM hX z) _ (blockMulVec_apply_mem hM hX' z) _ (hY z))
    (fun c X Y => by
      have hX : InU U X.1 := fun z => X.2 z (Set.mem_univ z)
      have hY : InU U Y.1 := fun z => Y.2 z (Set.mem_univ z)
      show pairS β (actP M (c • X.1)) Y.1 = c • pairS β (actP M X.1) Y.1
      rw [actP_smul, smul_eq_mul]
      exact pairS_smul_left hβ c _ _ (blockMulVec_apply_mem hM hX) hY)
    (fun X Y Y' => by
      have hX : InU U X.1 := fun z => X.2 z (Set.mem_univ z)
      have hY : InU U Y.1 := fun z => Y.2 z (Set.mem_univ z)
      have hY' : InU U Y'.1 := fun z => Y'.2 z (Set.mem_univ z)
      show pairS β (actP M X.1) (Y.1 + Y'.1) = _
      unfold pairS
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun z _ => hβ.add_right (blockMulVec_apply_mem hM hX z) (hY z) (hY' z))
    (fun c X Y => by
      have hX : InU U X.1 := fun z => X.2 z (Set.mem_univ z)
      have hY : InU U Y.1 := fun z => Y.2 z (Set.mem_univ z)
      show pairS β (actP M X.1) (c • Y.1) = (starRingEnd ℂ) c • pairS β (actP M X.1) Y.1
      unfold pairS
      rw [smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun z _ => hβ.smul_right (blockMulVec_apply_mem hM hX z) (hY z) c)

theorem cs_U (hβ : SesqCls U β) (M : SlopeTestRemainingChoices S (Q.Pr V)) (hM : ∀ a b, ∀ x ∈ U, (M a b).1 x ∈ U)
    (hP : ∀ X : Ix S → V, InU U X → 0 ≤ (pairS β (actP M X) X).re ∧ (pairS β (actP M X) X).im = 0)
    (X X' : Ix S → V) (hX : InU U X) (hX' : InU U X') :
    ‖pairS β (actP M X) X'‖ ^ 2 ≤ (pairS β (actP M X) X).re * (pairS β (actP M X') X').re := by
  let W := Submodule.pi Set.univ (fun _ : Ix S => U)
  let x : W := ⟨X, fun z _ => hX z⟩
  let x' : W := ⟨X', fun z _ => hX' z⟩
  have := Formalism.FourierDecayAlt.P.GramProductIdentities.cs_of_pos (frmU hβ M hM) (fun m => hP m.1 fun z => m.2 z (Set.mem_univ z)) x x'
  exact this

end Pair

section Ent

variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
variable {𝒜 : StarSubalgebra ℂ A}

theorem word_transfer_mem_entrywise (QQ : ℂ → M2 A) (w : List (Letter ℂ S)) (Y : ℂ) (hQ : ∀ a b, QQ Y a b ∈ 𝒜) :
    E2 𝒜 (TTw QQ w Y) := by
  induction w with
  | nil =>
    intro a b
    show io (QQ Y a b) ∈ entSub 𝒜
    exact io_mem (hQ a b)
  | cons l w ih =>
    by_cases hp : l.plus
    · rw [TTw, if_pos hp]; exact entries_mem_mul ih (reflection_entries_mem _ _)
    · rw [TTw, if_neg hp]; exact entries_mem_mul (reflection_transpose_entries_mem _ _) ih

theorem rrw_mem_at (QQ : ℂ → M2 A) (w : List (Letter ℂ S)) (hw : ∀ l ∈ w, ∀ a b, QQ l.pt a b ∈ 𝒜) :
    RRw QQ w ∈ entSub 𝒜 := by
  induction w with
  | nil => exact (entSub 𝒜).one_mem
  | cons l w ih =>
    rw [RRw]
    refine (entSub 𝒜).mul_mem (ih fun l' hl' => hw l' (by simp [hl'])) (ins_mem _ ?_)
    have hT := word_transfer_mem_entrywise QQ w l.pt (hw l (by simp))
    split_ifs
    · exact hT
    · exact entries_mem_transpose hT

theorem symplectic_form_mem_entrywise : E2 𝒜 (Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A)) := by
  unfold Formalism.YangianSpanCharacter.T.J
  exact entries_mem_of_four (entSub 𝒜).zero_mem (entSub 𝒜).one_mem (neg_mem (entSub 𝒜).one_mem) (entSub 𝒜).zero_mem

theorem ps_mem_at (QQ : ℂ → M2 A) (q : ℂ → ℂ) (w : List (Letter ℂ S)) (L : List (Letter ℂ S))
    (hL : ∀ l ∈ L, ∀ a b, (l.plus = true → QQ (l.pt + 1) a b ∈ 𝒜) ∧ (l.plus = false → QQ (l.pt - 1) a b ∈ 𝒜)) :
    Ps QQ q w L ∈ entSub 𝒜 := by
  induction L with
  | nil => exact (entSub 𝒜).one_mem
  | cons l L ih =>
    rw [Ps]
    refine (entSub 𝒜).mul_mem ?_ (ih fun l' hl' => hL l' (by simp [hl']))
    split_ifs with hp
    · unfold PsiP
      refine ins_mem _ ?_
      intro i j
      rw [Matrix.neg_apply]
      refine neg_mem ((entSub 𝒜).smul_mem ?_ _)
      exact entries_mem_mul symplectic_form_mem_entrywise (entries_mem_transpose (word_transfer_mem_entrywise QQ _ _ (fun a b => (hL l (by simp) a b).1 hp))) i j
    · unfold PsiM
      refine ins_mem _ ?_
      intro i j
      refine (entSub 𝒜).smul_mem ?_ _
      exact entries_mem_mul symplectic_form_mem_entrywise (word_transfer_mem_entrywise QQ _ _ (fun a b => (hL l (by simp) a b).2 (by simpa using hp))) i j

end Ent

section DK

variable {V : Type} [AddCommGroup V] [Module ℂ V] {S : Type} [Fintype S] [DecidableEq S]
variable {U : Submodule ℂ V} {β : V → V → ℂ}

theorem dk_partial (hβ : SesqCls U β) (QQ : ℂ → M2 (Q.Pr V)) (q : ℂ → ℂ) (w L : List (Letter ℂ S))
    (hS : IsStart QQ q) (hD : FormPairingAction.DKHyp q w L)
    (hPs : Ps QQ q w L ∈ entSub (adjB U β hβ))
    (hRR : ∀ a b, ∀ x ∈ U, (RRw QQ (L ++ w) a b).1 x ∈ U)
    (hPos : ∀ X : Ix S → V, InU U X → 0 ≤ (pairS β (actP (RRw QQ (L ++ w)) X) X).re ∧
      (pairS β (actP (RRw QQ (L ++ w)) X) X).im = 0)
    (X₁ X₂ : Ix S → V) (h1 : InU U X₁) (h2 : InU U X₂) :
    (pairS β (actP (RRw QQ (L ++ w)) X₁) X₁ * pairS β (actP (RRw QQ (L.map dl ++ w)) X₂) X₂ /
        (L.map fun l => qw q w l.pt).prod).im = 0 ∧
    ‖pairS β (actP (JL L * RRw QQ w) X₁) X₂‖ ^ 2 ≤
      (pairS β (actP (RRw QQ (L ++ w)) X₁) X₁ * pairS β (actP (RRw QQ (L.map dl ++ w)) X₂) X₂ /
        (L.map fun l => qw q w l.pt).prod).re := by
  have hok := Formalism.FourierDecayAlt.P.DualKernelLemmas.dkDualOK S q w L hD
  have hdl := Formalism.FourierDecayAlt.P.duality_list_holds ℂ (Q.Pr V) S QQ q w L hS hD.2.1 hD.2.2.1 hok
  have hkap := Formalism.FourierDecayAlt.P.kappa_formula_holds ℂ S q w L hD.2.1 hD.2.2.1 hok
  have h4 := Formalism.FourierDecayAlt.P.GramProductIdentities.dkStep4 S q w L hD.1
  have hk0 : kap q w L ≠ 0 := hdl.2.1
  have hprod : (L.map fun l => qw q w l.pt).prod = kap q w L := by rw [hkap, h4]
  have hPsU : ∀ a b, ∀ x ∈ U, (Ps QQ q w L a b).1 x ∈ U := fun a b x hx => (hPs a b).1 x hx
  have hsPs : star (Ps QQ q w L) ∈ entSub (adjB U β hβ) := star_mem_entSub hPs
  have hsPsU : ∀ a b, ∀ x ∈ U, (star (Ps QQ q w L) a b).1 x ∈ U := fun a b x hx => (hsPs a b).1 x hx
  have hY : InU U (actP (Ps QQ q w L) X₂) := blockMulVec_apply_mem hPsU h2
  have hR1 : InU U (actP (RRw QQ (L ++ w)) X₁) := blockMulVec_apply_mem hRR h1
  have hR2 : InU U (actP (RRw QQ (L ++ w)) (actP (Ps QQ q w L) X₂)) := blockMulVec_apply_mem hRR hY
  have e1 : pairS β (actP (JL L * RRw QQ w) X₁) X₂ =
      pairS β (actP (RRw QQ (L ++ w)) X₁) (actP (Ps QQ q w L) X₂) := by
    rw [← hdl.2.2.1, polyAction_mul, pairS_adj hβ _ hPs _ _ hR1 h2]
  have hm : pairS β (actP (RRw QQ (L.map dl ++ w)) X₂) X₂ = kap q w L *
      pairS β (actP (RRw QQ (L ++ w)) (actP (Ps QQ q w L) X₂)) (actP (Ps QQ q w L) X₂) := by
    have e : RRw QQ (L.map dl ++ w) = kap q w L • (star (Ps QQ q w L) * RRw QQ (L ++ w) * Ps QQ q w L) := by
      rw [hdl.2.2.2.1, smul_smul, mul_inv_cancel₀ hk0, one_smul]
    rw [e, smul_blockMulVec, polyAction_mul, polyAction_mul, pairS_smul_left hβ _ _ _ (blockMulVec_apply_mem hsPsU hR2) h2,
      pairS_adj hβ _ hPs _ _ hR2 h2]
  rw [hprod, hm, e1]
  refine Formalism.FourierDecayAlt.P.DualKernelLemmas.real_bound _ _ _ _ hk0 (hPos X₁ h1).2 (hPos _ hY).2 ?_
  exact cs_U hβ _ hRR hPos X₁ _ h1 hY

end DK

end Formalism.FourierDecayAlt.P.PBF
