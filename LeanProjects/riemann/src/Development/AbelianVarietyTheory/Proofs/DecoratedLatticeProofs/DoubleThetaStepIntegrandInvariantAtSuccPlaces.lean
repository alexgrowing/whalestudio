import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValQOfValQr
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaStepSplitPlaceValuePeriodGroupInvariaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupClosedEmbeddingIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodLocalGroupsNormalFramesSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisOFinsetSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalSchrodingerModelUniqTransportExists
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSet
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.QVal GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.QVal.Inv

variable {D : D7}

section Idem
variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

theorem infPart_idem (q : GlobalTheory.FinPl.SplitPt D k) : infPart D (q.e + cA D q.e) = 0 := by
  obtain ⟨ε, ⟨α, rfl, -⟩, h4⟩ := q.above
  rw [h4]
  exact TensorProduct.zero_tmul _ _

theorem cA_idem (q : GlobalTheory.FinPl.SplitPt D k) : cA D (q.e + cA D q.e) = q.e + cA D q.e := by
  obtain ⟨ε, -, h4⟩ := q.above
  rw [h4]
  show cA D (ε ⊗ₜ[D.host.F] (1 : D.host.E)) = ε ⊗ₜ[D.host.F] (1 : D.host.E)
  simp [cA, sigR]

theorem idem_mul_idem (q : GlobalTheory.FinPl.SplitPt D k) (q' : GlobalTheory.FinPl.SplitPt D k') (hne : q.v ≠ q'.v) :
    (q.e + cA D q.e) * (q'.e + cA D q'.e) = 0 := by
  obtain ⟨ε, ⟨α, rfl, -, hα⟩, h⟩ := q.above
  obtain ⟨ε', ⟨β, rfl, -, hβ⟩, h'⟩ := q'.above
  have key : ∀ w, evalV D.host.F w (α * β) = 0 := by
    intro w
    rw [map_mul]
    by_cases hw : w = q.v
    · rw [hβ w (hw ▸ hne), mul_zero]
    · rw [hα w hw, zero_mul]
  have hab : α * β = 0 := RestrictedProduct.ext _ _ fun w => key w
  have h0 : pairA D.host.F 0 α * pairA D.host.F 0 β = 0 := by
    show ((0 : Ainf D.host.F), α) * ((0 : Ainf D.host.F), β) = 0
    rw [Prod.mk_mul_mk, hab, mul_zero]
    rfl
  rw [h, h', ← map_mul, h0, map_zero]

theorem idem_sq (q : GlobalTheory.FinPl.SplitPt D k) : (q.e + cA D q.e) * (q.e + cA D q.e) = q.e + cA D q.e := by
  have h1 := q.split.1
  have h2 := q.split.2.1
  have h3 : cA D q.e * cA D q.e = cA D q.e := by rw [← map_mul, h1]
  linear_combination h1 + 2 * h2 + h3

end Idem

section Comb
variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem aconv_cons {G : Type} [AddMonoid G] (e : G →₀ ℂ) (l : List (G →₀ ℂ)) :
    aconv (e :: l) = ∑ g ∈ e.support, ∑ h ∈ (aconv l).support, Finsupp.single (g + h) (e g * aconv l h) := rfl

theorem support_aconv {G : Type} [AddMonoid G] (p : G → Prop) (h0 : p 0) (hadd : ∀ x y, p x → p y → p (x + y))
    (l : List (G →₀ ℂ)) (hl : ∀ e ∈ l, ∀ u ∈ e.support, p u) : ∀ u ∈ (aconv l).support, p u := by
  classical
  induction l with
  | nil =>
    intro u hu
    have h3 := Finsupp.support_single_subset hu
    rw [Finset.mem_singleton] at h3
    exact h3 ▸ h0
  | cons e l ih =>
    intro w hw
    rw [aconv_cons] at hw
    obtain ⟨x, hx, hw2⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum hw)
    obtain ⟨y, hy, hw3⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum hw2)
    have h3 := Finsupp.support_single_subset hw3
    rw [Finset.mem_singleton] at h3
    exact h3 ▸ hadd x y (hl e List.mem_cons_self x hx) (ih (fun e' he' => hl e' (List.mem_cons_of_mem _ he')) y hy)

theorem comb_aconv_cons (e : WO S T →₀ ℂ) (l : List (WO S T →₀ ℂ))
    (h : ∀ x ∈ e.support, ∀ y ∈ (aconv l).support, symplO S T x y = 0) (f : WO S T → ℂ) :
    comb ψ S T (aconv (e :: l)) f = comb ψ S T e (comb ψ S T (aconv l) f) := by
  rw [GlobalTheory.HeisComb.comb_comb, GlobalTheory.HeisComb.comb_eq_sum, aconv_cons]
  rw [← Finsupp.sum_finset_sum_index (fun u => zero_smul ℂ (heisO ψ S T u f)) (fun u a b => add_smul a b (heisO ψ S T u f))]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [← Finsupp.sum_finset_sum_index (fun u => zero_smul ℂ (heisO ψ S T u f)) (fun u a b => add_smul a b (heisO ψ S T u f))]
  refine Finset.sum_congr rfl fun y hy => ?_
  have h0 : symplOH S T x y = 0 := by
    unfold symplOH
    rw [h x hx y hy, mul_zero]
  rw [Finsupp.sum_single_index (zero_smul ℂ (heisO ψ S T (x + y) f)), GlobalTheory.WeilVacMove.heisO_heisO, h0, AddChar.map_zero_eq_one,
    one_smul]

theorem half_add {e : AE D} {x y : WO S T} (hx : IsHalf e x) (hy : IsHalf e y) : IsHalf e (x + y) := fun i j => by
  show e * (x i j + y i j) = x i j + y i j
  rw [mul_add, hx i j, hy i j]

theorem half_zero (e : AE D) : IsHalf e (0 : WO S T) := fun _ _ => mul_zero e

theorem half_compl {e e' : AE D} (h : e * e' = 0) {x : WO S T} (hx : IsHalf e' x) : IsHalf (1 - e) x := fun i j => by
  rw [sub_mul, one_mul, ← hx i j, ← mul_assoc, h, zero_mul, sub_zero]

theorem fin_add {x y : WO S T} (hx : x.map (infPart D) = 0) (hy : y.map (infPart D) = 0) : (x + y).map (infPart D) = 0 := by
  rw [Matrix.map_add _ (fun a b => (infPart D).map_add a b), hx, hy, add_zero]

theorem fin_of_half {e : AE D} (he : infPart D e = 0) {u : WO S T} (hu : IsHalf e u) : u.map (infPart D) = 0 := by
  ext i j
  rw [Matrix.map_apply, ← hu i j, map_mul, he, zero_mul]
  rfl

theorem comb_aconv_isolate : ∀ (n : ℕ) (ε : Fin n → AE D) (d : Fin n → WO S T →₀ ℂ), (∀ j, cA D (ε j) = ε j) →
    (∀ j, ε j * ε j = ε j) → (∀ j j', j ≠ j' → ε j * ε j' = 0) → (∀ j, infPart D (ε j) = 0) →
    (∀ j, ∀ u ∈ (d j).support, IsHalf (ε j) u) → ∀ i, ∃ c : WO S T →₀ ℂ,
      (∀ u ∈ c.support, IsHalf (1 - ε i) u ∧ u.map (infPart D) = 0) ∧
        ∀ f, comb ψ S T (aconv (List.ofFn d)) f = comb ψ S T (d i) (comb ψ S T c f) := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _ i; exact i.elim0
  | succ n ih =>
    intro ε d hc hi ho hf hd i
    have htail : ∀ u ∈ (aconv (List.ofFn fun j : Fin n => d j.succ)).support, IsHalf (1 - ε 0) u ∧ u.map (infPart D) = 0 := by
      refine support_aconv (fun u : WO S T => IsHalf (1 - ε 0) u ∧ u.map (infPart D) = 0)
        ⟨half_zero _, Matrix.map_zero _ (infPart D).map_zero⟩
        (fun x y hx hy => ⟨half_add hx.1 hy.1, fin_add hx.2 hy.2⟩) _ fun e he u hu => ?_
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 he
      exact ⟨half_compl (ho 0 j.succ (Fin.succ_ne_zero j).symm) (hd _ u hu), fin_of_half (hf _) (hd _ u hu)⟩
    have h1 : ∀ f, comb ψ S T (aconv (List.ofFn d)) f =
        comb ψ S T (d 0) (comb ψ S T (aconv (List.ofFn fun j : Fin n => d j.succ)) f) := fun f => by
      rw [List.ofFn_succ]
      exact comb_aconv_cons _ _ (fun x hx y hy => GlobalTheory.HeisComb.symplO_half S T (ε 0) (1 - ε 0) x y (hc 0)
        (by rw [mul_sub, mul_one, hi 0, sub_self]) (hd 0 x hx) (htail y hy).1) f
    refine Fin.cases ⟨_, htail, h1⟩ (fun i => ?_) i
    obtain ⟨c', hc', he'⟩ := ih (fun j => ε j.succ) (fun j => d j.succ) (fun j => hc _) (fun j => hi _)
      (fun j j' h => ho _ _ fun h' => h (Fin.succ_injective _ h')) (fun j => hf _) (fun j => hd _) i
    obtain ⟨c'', hs, he''⟩ := (GlobalTheory.HeisComb.main D ψ S T).1 (d 0) c'
    refine ⟨c'', fun w hw => ?_, fun f => ?_⟩
    · obtain ⟨x, hx, y, hy, rfl⟩ := hs w hw
      exact ⟨half_add (half_compl (ho _ _ (Fin.succ_ne_zero i)) (hd 0 x hx)) (hc' y hy).1,
        fin_add (fin_of_half (hf 0) (hd 0 x hx)) (hc' y hy).2⟩
    · rw [h1, he', he'']
      exact (GlobalTheory.HeisComb.main D ψ S T).2.1 _ _ (fun x hx y hy => GlobalTheory.HeisComb.symplO_half S T (ε 0) (ε i.succ) x y (hc 0)
        (ho _ _ (Fin.succ_ne_zero i).symm) (hd 0 x hx) (hd _ y hy)) _

def combLin (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun := comb ψ S T c
  map_add' f f' := by
    funext w
    simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  map_smul' a f := by
    funext w
    simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

theorem comb_single_one (y : WO S T) (f : WO S T → ℂ) : comb ψ S T (Finsupp.single y 1) f = heisO ψ S T y f := by
  rw [GlobalTheory.HeisComb.comb_eq_sum, Finsupp.sum_single_index (zero_smul ℂ (heisO ψ S T y f)), one_smul]

theorem isModel_comb {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hψ : IsStdChar D ψ (-1)) (q : GlobalTheory.FinPl.SplitPt D k) {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
    (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (c : WO S T →₀ ℂ)
    (hc : ∀ u ∈ c.support, IsHalf (1 - (q.e + cA D q.e)) u ∧ u.map (infPart D) = 0) (Tm)
    (h : (ofSplit q).IsModel ψ FS FT Tm) : (ofSplit q).IsModel ψ FS FT (combLin ψ S T c ∘ₗ Tm) := by
  have hi := idem_sq q
  refine (GlobalTheory.LocModU.localModel_uniq_transport_exist D k (ofSplit q) Y Y' S T FS FT ψ hψ).2.1 Tm h (combLin ψ S T c)
    (fun f hf => (GlobalTheory.HeisComb.main D ψ S T).2.2.1 c f hf (fun u hu => (hc u hu).2) hψ) fun f _ y hy => ?_
  show comb ψ S T c (heisO ψ S T y f) = heisO ψ S T y (comb ψ S T c f)
  rw [← comb_single_one, ← comb_single_one y (comb ψ S T c f)]
  refine ((GlobalTheory.HeisComb.main D ψ S T).2.1 _ _ (fun x hx u hu => ?_) f).symm
  have hx' : x = y := Finset.mem_singleton.1 (Finsupp.support_single_subset hx)
  exact GlobalTheory.HeisComb.symplO_half S T (q.e + cA D q.e) (1 - (q.e + cA D q.e)) x u (cA_idem q)
    (by rw [mul_sub, mul_one, hi, sub_self]) (hx' ▸ hy) (hc u hu).1

end Comb

section Group
variable {V : HSp D}

theorem eq_one_of_grpAt_empty {x : GA D V} (hx : x ∈ grpAt V fun _ => False) : x = 1 := by
  have h1 : x ∈ grpAt V (· ∈ (∅ : Finset (GlobalTheory.FinPl.Pl D))) := by simpa using hx
  have h2 : x ∈ grpAt V (· ∉ (∅ : Finset (GlobalTheory.FinPl.Pl D))) :=
    (SetCut.mem_grpAt_iff_parts V _ x).2 fun i j => ⟨((SetCut.mem_grpAt_iff_parts V _ x).1 hx i j).1,
      fun w hw => absurd (Finset.notMem_empty w) hw⟩
  have h3 := (SetCut.cutG_left V ∅ h1 (one_mem _)).symm
  rw [mul_one, ← one_mul x, SetCut.cutG_left V ∅ (one_mem _) h2] at h3
  rwa [one_mul] at h3

theorem induction_places {n : ℕ} (v : Fin n → GlobalTheory.FinPl.Pl D) (H : Subgroup (GA D V)) (C : GA D V → Prop) (h1 : C 1)
    (hmul : ∀ x y, C x → C y → C (x * y))
    (hloc : ∀ i, ∀ x ∈ H, ∃ a ∈ H, C a ∧ a ∈ grpAt V (· = v i) ∧ x * a⁻¹ ∈ grpOff V (· = v i)) :
    ∀ x ∈ H, x ∈ grpAt V (fun p => ∃ i, v i = p) → C x := by
  classical
  have key : ∀ s : Finset (Fin n), ∀ x ∈ H, x ∈ grpAt V (fun p => ∃ i ∈ s, v i = p) → C x := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro x _ hx
      rw [eq_one_of_grpAt_empty (x := x) (by simpa using hx)]
      exact h1
    | insert i s _ ih =>
      intro x hH hx
      obtain ⟨a, haH, hCa, ha, hoff⟩ := hloc i x hH
      have ha' : a ∈ grpAt V (fun p => ∃ j ∈ insert i s, v j = p) :=
        (SetCut.mem_grpAt_iff_parts V _ a).2 fun r t => ⟨((SetCut.mem_grpAt_iff_parts V _ a).1 ha r t).1, fun w hw =>
          ((SetCut.mem_grpAt_iff_parts V _ a).1 ha r t).2 w fun h => hw ⟨i, Finset.mem_insert_self _ _, h.symm⟩⟩
      have hy := (SetCut.mem_grpAt_iff_parts V _ _).1 (mul_mem hx (inv_mem ha'))
      have hy' : x * a⁻¹ ∈ grpAt V (fun p => ∃ j ∈ s, v j = p) := by
        refine (SetCut.mem_grpAt_iff_parts V _ _).2 fun r t => ⟨(hy r t).1, fun w hw => ?_⟩
        by_cases h : w = v i
        · exact (SetCut.mem_grpOff_iff_parts V _ _).1 hoff r t w h
        · refine (hy r t).2 w ?_
          rintro ⟨j, hj, rfl⟩
          rcases Finset.mem_insert.1 hj with rfl | hj
          · exact h rfl
          · exact hw ⟨j, hj, rfl⟩
      have := hmul _ _ (ih _ (mul_mem hH (inv_mem haH)) hy') hCa
      rwa [inv_mul_cancel_right] at this
  intro x hH hx
  exact key Finset.univ x hH (by simpa using hx)

theorem grpOff_of_places {P : GlobalTheory.FinPl.Pl D → Prop} {v : GlobalTheory.FinPl.Pl D} (hv : P v) {x : GA D V} (hx : x ∈ grpOff V P) :
    x ∈ grpOff V (· = v) :=
  (SetCut.mem_grpOff_iff_parts V _ x).2 fun i j w hw => (SetCut.mem_grpOff_iff_parts V _ x).1 hx i j w (hw ▸ hv)

end Group

variable {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ}

theorem val_inv (hψ : IsStdChar D ψ (-1)) (Q : QStep S) {c₁ c₂} (h₁ : Q.Away c₁) (h₂ : Q.Away c₂) {f₁ f₂} (hv : Q.Vac f₁ f₂) {φ f}
    (hφ : IsContAut S.B.A φ) (hf : IsContAut S.B'.V f) (ht : Q.Typed f) (g : GA D S.B.V) (x : GA D S.J.W) (y : GA D S.B'.V)
    {a j a' j'} (ha : a ∈ RFJ Q.k Q.n₁ (Q.c + 1 + 1) (σ + 1)) (hj : j ∈ Q.L₁.J) (ha' : a' ∈ R Q.k Q.n₂ (Q.c + 1) (σ + 1))
    (hj' : j' ∈ Q.L₂.J) :
    S.val c₁ c₂ (comb ψ _ _ Q.D₁ f₁) (comb ψ _ _ Q.D₂ f₂) φ f g (Q.gl₁ a * x * Q.gl₁ j) (Q.gl₂ a' * y * Q.gl₂ j') =
      S.val c₁ c₂ (comb ψ _ _ Q.D₁ f₁) (comb ψ _ _ Q.D₂ f₂) φ f g x y := by
  have G₀ := GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D Q.k Q.q S.B.V _ Q.F.G₀ Q.gl₀ Q.loc₀
  have G₁ := GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D Q.k Q.q S.J.W _ Q.F.G₁ Q.gl₁ Q.loc₁
  have G₂ := GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D Q.k Q.q S.B'.V _ Q.F.G₂ Q.gl₂ Q.loc₂
  obtain ⟨g₀, hg, -⟩ := G₀.2.2.1 g
  obtain ⟨x₀, hx, -⟩ := G₁.2.2.1 x
  obtain ⟨y₀, hy, -⟩ := G₂.2.2.1 y
  have key := GlobalTheory.T.doubleThetaStep_splitPlace_value_periodGroup_invariant D ψ hψ σ S Q c₁ c₂ h₁ h₂ f₁ f₂ hv φ f hφ hf ht _ _ _ hg hx hy g₀ x₀ y₀ a ha j hj a' ha' j' hj'
  have e₁ : x * (Q.gl₁ x₀)⁻¹ * Q.gl₁ (a * x₀ * j) = Q.gl₁ a * x * Q.gl₁ j := by
    rw [map_mul, map_mul, ← mul_assoc, ← mul_assoc, ← G₁.2.2.2.1 a _ hx, mul_assoc (Q.gl₁ a), inv_mul_cancel_right]
  have e₂ : y * (Q.gl₂ y₀)⁻¹ * Q.gl₂ (a' * y₀ * j') = Q.gl₂ a' * y * Q.gl₂ j' := by
    rw [map_mul, map_mul, ← mul_assoc, ← mul_assoc, ← G₂.2.2.2.1 a' _ hy, mul_assoc (Q.gl₂ a'), inv_mul_cancel_right]
  rw [e₁, e₂, inv_mul_cancel_right, inv_mul_cancel_right, inv_mul_cancel_right] at key
  exact key

theorem integrand_inv (hψ : IsStdChar D ψ (-1)) {n : ℕ} (Q : Fin n → QStep S) (hinj : Function.Injective fun i => (Q i).q.v)
    {c₁ c₂ f₁ f₂ φ f g h₁ h₂} (hH : Hyps Q c₁ c₂ f₁ f₂ φ f g h₁ h₂) (i : Fin n) (x : GA D S.J.W) (y : GA D S.B'.V) {a j a' j'}
    (ha : a ∈ RFJ (Q i).k (Q i).n₁ ((Q i).c + 1 + 1) (σ + 1)) (hj : j ∈ (Q i).L₁.J)
    (ha' : a' ∈ R (Q i).k (Q i).n₂ ((Q i).c + 1) (σ + 1)) (hj' : j' ∈ (Q i).L₂.J) :
    integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ ((Q i).gl₁ a * x * (Q i).gl₁ j) ((Q i).gl₂ a' * y * (Q i).gl₂ j') =
      integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x y := by
  obtain ⟨hc, -, -, hv, hφ, hf, ht, -, hh₁, hh₂⟩ := hH
  have hi : ∀ j, ((Q j).q.e + cA D (Q j).q.e) * ((Q j).q.e + cA D (Q j).q.e) = (Q j).q.e + cA D (Q j).q.e := fun j => idem_sq _
  have ho : ∀ j j', j ≠ j' → ((Q j).q.e + cA D (Q j).q.e) * ((Q j').q.e + cA D (Q j').q.e) = 0 := fun j j' h =>
    idem_mul_idem _ _ fun h' => h (hinj h')
  obtain ⟨d₁, hd₁, e₁⟩ := comb_aconv_isolate (ψ := ψ) n (fun j => (Q j).q.e + cA D (Q j).q.e) (fun j => (Q j).D₁)
    (fun j => cA_idem _) hi ho (fun j => infPart_idem _) (fun j => (Q j).dat₁.1) i
  obtain ⟨d₂, hd₂, e₂⟩ := comb_aconv_isolate (ψ := ψ) n (fun j => (Q j).q.e + cA D (Q j).q.e) (fun j => (Q j).D₂)
    (fun j => cA_idem _) hi ho (fun j => infPart_idem _) (fun j => (Q j).dat₂.1) i
  have hv' : (Q i).Vac (comb ψ _ _ d₁ f₁) (comb ψ _ _ d₂ f₂) := by
    obtain ⟨⟨T₁, O₁, m₁, o₁, rfl⟩, T₂, O₂, m₂, o₂, rfl⟩ := hv i
    exact ⟨⟨_, O₁, isModel_comb hψ _ _ _ d₁ hd₁ T₁ m₁, o₁, rfl⟩, _, O₂, isModel_comb hψ _ _ _ d₂ hd₂ T₂ m₂, o₂, rfl⟩
  have c₁' := (GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D (Q i).k (Q i).q S.J.W _ (Q i).F.G₁ (Q i).gl₁ (Q i).loc₁).2.2.2.1 a h₁
    (grpOff_of_places (P := places Q) ⟨i, rfl⟩ hh₁)
  have c₂' := (GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D (Q i).k (Q i).q S.B'.V _ (Q i).F.G₂ (Q i).gl₂ (Q i).loc₂).2.2.2.1 a' h₂
    (grpOff_of_places (P := places Q) ⟨i, rfl⟩ hh₂)
  have m₁ : h₁ * ((Q i).gl₁ a * x * (Q i).gl₁ j) = (Q i).gl₁ a * (h₁ * x) * (Q i).gl₁ j := by
    rw [← mul_assoc h₁, ← mul_assoc h₁, ← c₁', mul_assoc _ h₁]
  have m₂ : h₂ * ((Q i).gl₂ a' * y * (Q i).gl₂ j') = (Q i).gl₂ a' * (h₂ * y) * (Q i).gl₂ j' := by
    rw [← mul_assoc h₂, ← mul_assoc h₂, ← c₂', mul_assoc _ h₂]
  unfold integrand
  refine congrArg (GlobalTheory.PosOne.comb _) (funext fun b => ?_)
  rw [e₁ f₁, e₂ f₂, m₁, m₂]
  exact val_inv hψ (Q i) (hc i).1 (hc i).2 hv' hφ hf (ht i) (g * b) (h₁ * x) (h₂ * y) ha hj ha' hj'

section Main
variable (hψ : IsStdChar D ψ (-1)) {n : ℕ} (Q : Fin n → QStep S) (hinj : Function.Injective fun i => (Q i).q.v)
  {c₁ : WO S.B.A S.J.W₀ →₀ ℂ} {c₂ : WO S.J.W₀ S.B'.A →₀ ℂ} {f₁ : WO S.B.V S.J.W → ℂ} {f₂ : WO S.J.W S.B'.V → ℂ}
  {φ : GA D S.B.A → ℂ} {f : GA D S.B'.V → ℂ} {g : GA D S.B.V} {h₁ : GA D S.J.W} {h₂ : GA D S.B'.V}
  (hH : Hyps Q c₁ c₂ f₁ f₂ φ f g h₁ h₂)
include hψ hinj hH

theorem left₁ (i : Fin n) {a} (ha : a ∈ RFJ (Q i).k (Q i).n₁ ((Q i).c + 1 + 1) (σ + 1)) (x y) :
    integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ ((Q i).gl₁ a * x) y = integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x y := by
  have h := integrand_inv hψ Q hinj hH i x y ha (one_mem _) (one_mem _) (one_mem _)
  rwa [map_one, map_one, mul_one, mul_one, one_mul] at h

theorem right₁ (i : Fin n) {j} (hj : j ∈ (Q i).L₁.J) (x y) :
    integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ (x * (Q i).gl₁ j) y = integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x y := by
  have h := integrand_inv hψ Q hinj hH i x y (one_mem _) hj (one_mem _) (one_mem _)
  rwa [map_one, map_one, one_mul, mul_one, one_mul] at h

theorem left₂ (i : Fin n) {a} (ha : a ∈ R (Q i).k (Q i).n₂ ((Q i).c + 1) (σ + 1)) (x y) :
    integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x ((Q i).gl₂ a * y) = integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x y := by
  have h := integrand_inv hψ Q hinj hH i x y (one_mem _) (one_mem _) ha (one_mem _)
  rwa [map_one, map_one, mul_one, mul_one, one_mul] at h

theorem right₂ (i : Fin n) {j} (hj : j ∈ (Q i).L₂.J) (x y) :
    integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x (y * (Q i).gl₂ j) = integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x y := by
  have h := integrand_inv hψ Q hinj hH i x y (one_mem _) (one_mem _) (one_mem _) hj
  rwa [map_one, map_one, mul_one, one_mul, one_mul] at h

theorem left_jac {m : ℕ} (τ : Fin m → Fin n) {ρ : GA D S.J.W} (hρ : ρ ∈ jacGrp S.J.d)
    (hP : ρ ∈ grpAt S.J.W (places fun i => Q (τ i))) (x y) :
    integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ (ρ * x) y = integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x y := by
  refine induction_places (fun i => (Q (τ i)).q.v) (jacGrp S.J.d)
    (fun ρ => ∀ x, integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ (ρ * x) y = integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x y)
    (fun x => by rw [one_mul]) (fun a b ha hb x => by rw [mul_assoc, ha, hb]) (fun i z hz => ?_) ρ hρ hP x
  have G := GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D (Q (τ i)).k (Q (τ i)).q S.J.W _ (Q (τ i)).F.G₁ (Q (τ i)).gl₁ (Q (τ i)).loc₁
  have H := (GlobalTheory.T.periodLocalGroups_normalFrames_splitPlace D (Q (τ i)).k (Q (τ i)).q (Q (τ i)).n₁ ((Q (τ i)).c + 1 + 1) (σ + 1)).1 S.J _ _ _ _ (Q (τ i)).gl₁
    (Nat.le_add_left 1 σ) (Q (τ i)).F.s_ne (GlobalTheory.LocMod.Witness.hz_ne _ S.B) (Q (τ i)).F.jac (Q (τ i)).loc₁
  obtain ⟨a, ha, -⟩ := G.2.2.1 z
  have hm : (Q (τ i)).gl₁ a ∈ jacGrp S.J.d := H.2 a _ ha (by rw [G.2.2.2.1 a _ ha, inv_mul_cancel_right]; exact hz)
  exact ⟨_, hm, fun x => left₁ hψ Q hinj hH (τ i) ((H.1 a).1 hm) x y, G.2.1 ▸ MonoidHom.mem_range.2 ⟨a, rfl⟩, ha⟩

theorem left_bes {m : ℕ} (τ : Fin m → Fin n) {ρ : GA D S.B'.V} (hρ : ρ ∈ besGrp S.B'.d S.B'.o)
    (hP : ρ ∈ grpAt S.B'.V (places fun i => Q (τ i))) (x y) :
    integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x (ρ * y) = integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x y := by
  refine induction_places (fun i => (Q (τ i)).q.v) (besGrp S.B'.d S.B'.o)
    (fun ρ => ∀ y, integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x (ρ * y) = integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x y)
    (fun x => by rw [one_mul]) (fun a b ha hb x => by rw [mul_assoc, ha, hb]) (fun i z hz => ?_) ρ hρ hP y
  have G := GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D (Q (τ i)).k (Q (τ i)).q S.B'.V _ (Q (τ i)).F.G₂ (Q (τ i)).gl₂ (Q (τ i)).loc₂
  have H := (GlobalTheory.T.periodLocalGroups_normalFrames_splitPlace D (Q (τ i)).k (Q (τ i)).q (Q (τ i)).n₂ ((Q (τ i)).c + 1) σ).2 S.B' _ _ _ (Q (τ i)).gl₂
    (mul_ne_zero (Q (τ i)).F.s_ne (GlobalTheory.LocMod.Witness.xi_ne _)) (Q (τ i)).F.bes' (Q (τ i)).loc₂
  obtain ⟨a, ha, -⟩ := G.2.2.1 z
  have hm : (Q (τ i)).gl₂ a ∈ besGrp S.B'.d S.B'.o := H.2 a _ ha (by rw [G.2.2.2.1 a _ ha, inv_mul_cancel_right]; exact hz)
  exact ⟨_, hm, fun y => left₂ hψ Q hinj hH (τ i) ((H.1 a).1 hm) x y, G.2.1 ▸ MonoidHom.mem_range.2 ⟨a, rfl⟩, ha⟩

theorem right_lev₁ {m : ℕ} (τ : Fin m → Fin n) {κ : GA D S.J.W} (hκ : κ ∈ ⨆ i, (Q (τ i)).L₁.J.map (Q (τ i)).gl₁) (x y) :
    integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ (x * κ) y = integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x y := by
  refine Subgroup.iSup_induction _
    (C := fun κ => ∀ x, integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ (x * κ) y = integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x y) hκ ?_
    (fun x => by rw [mul_one]) (fun a b ha hb x => by rw [← mul_assoc, hb, ha]) x
  rintro i _ ⟨j, hj, rfl⟩ x
  exact right₁ hψ Q hinj hH (τ i) hj x y

theorem right_lev₂ {m : ℕ} (τ : Fin m → Fin n) {κ : GA D S.B'.V} (hκ : κ ∈ ⨆ i, (Q (τ i)).L₂.J.map (Q (τ i)).gl₂) (x y) :
    integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x (y * κ) = integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x y := by
  refine Subgroup.iSup_induction _
    (C := fun κ => ∀ y, integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x (y * κ) = integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x y) hκ ?_
    (fun x => by rw [mul_one]) (fun a b ha hb x => by rw [← mul_assoc, hb, ha]) y
  rintro i _ ⟨j, hj, rfl⟩ y
  exact right₂ hψ Q hinj hH (τ i) hj x y

end Main

theorem pint_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (r : ℕ) (Q : Fin (r + 1) → QStep S), Function.Injective (fun i => (Q i).q.v) → ∀ c₁ c₂ f₁ f₂ φ f g h₁ h₂, Hyps Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ → (∀ x y, ∀ r ∈ ((besGrp S.B'.d S.B'.o).subgroupOf (grpAt S.B'.V (places fun i => Q i.succ))).prod (R (Q 0).k (Q 0).n₂ ((Q 0).c + 1) (σ + 1)), ∀ κ ∈ (levB fun i => Q i.succ).prod (Q 0).L₂.J, pint Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x (r * y * κ) = pint Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x y) ∧ (∀ x y, ∀ κ ∈ (levJ fun i => Q i.succ).prod (Q 0).L₁.J, pint Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ (x * κ) y = pint Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x y) ∧ (∀ x y, ∀ r ∈ ((jacGrp S.J.d).subgroupOf (grpAt S.J.W (places fun i => Q i.succ))).prod (RFJ (Q 0).k (Q 0).n₁ ((Q 0).c + 1 + 1) (σ + 1)), pint Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ (r * x) y = pint Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x y) := by
  intro D ψ hψ σ S r Q hinj c₁ c₂ f₁ f₂ φ f g h₁ h₂ hH
  have hdis : ∀ p, places (fun i : Fin r => Q i.succ) p → ¬ p = (Q 0).q.v := by
    rintro p ⟨i, rfl⟩ h
    exact Fin.succ_ne_zero i (hinj h)
  have k₁ : ∀ a (z : grpAt S.J.W (places fun i : Fin r => Q i.succ)), (Q 0).gl₁ a * z.1 = z.1 * (Q 0).gl₁ a := fun a z =>
    (GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D (Q 0).k (Q 0).q S.J.W _ (Q 0).F.G₁ (Q 0).gl₁ (Q 0).loc₁).2.2.2.1 a _
      (SetCut.grpAt_le_grpOff _ _ _ hdis z.2)
  have k₂ : ∀ a (z : grpAt S.B'.V (places fun i : Fin r => Q i.succ)), (Q 0).gl₂ a * z.1 = z.1 * (Q 0).gl₂ a := fun a z =>
    (GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D (Q 0).k (Q 0).q S.B'.V _ (Q 0).F.G₂ (Q 0).gl₂ (Q 0).loc₂).2.2.2.1 a _
      (SetCut.grpAt_le_grpOff _ _ _ hdis z.2)
  refine ⟨fun x y ρ hρ κ hκ => ?_, fun x y κ hκ => ?_, fun x y ρ hρ => ?_⟩
  · have e : (ρ * y * κ).1.1 * (Q 0).gl₂ (ρ * y * κ).2 =
        ρ.1.1 * ((Q 0).gl₂ ρ.2 * (y.1.1 * (Q 0).gl₂ y.2 * κ.1.1 * (Q 0).gl₂ κ.2)) := by
      show ρ.1.1 * y.1.1 * κ.1.1 * (Q 0).gl₂ (ρ.2 * y.2 * κ.2) = _
      rw [map_mul, map_mul, ← map_mul _ ρ.2, ← mul_assoc, mul_assoc _ κ.1.1, ← k₂, map_mul, ← mul_assoc, ← mul_assoc,
        mul_assoc _ y.1.1, ← k₂]
      simp only [mul_assoc]
    unfold pint
    rw [e, left_bes hψ Q hinj hH Fin.succ (Subgroup.mem_subgroupOf.1 hρ.1) ρ.1.2, left₂ hψ Q hinj hH 0 hρ.2,
      right₂ hψ Q hinj hH 0 hκ.2, right_lev₂ hψ Q hinj hH Fin.succ (Subgroup.mem_subgroupOf.1 hκ.1)]
  · have e : (x * κ).1.1 * (Q 0).gl₁ (x * κ).2 = x.1.1 * (Q 0).gl₁ x.2 * κ.1.1 * (Q 0).gl₁ κ.2 := by
      show x.1.1 * κ.1.1 * (Q 0).gl₁ (x.2 * κ.2) = _
      rw [map_mul, ← mul_assoc, mul_assoc _ κ.1.1, ← k₁, ← mul_assoc]
    unfold pint
    rw [e, right₁ hψ Q hinj hH 0 hκ.2, right_lev₁ hψ Q hinj hH Fin.succ (Subgroup.mem_subgroupOf.1 hκ.1)]
  · have e : (ρ * x).1.1 * (Q 0).gl₁ (ρ * x).2 = ρ.1.1 * ((Q 0).gl₁ ρ.2 * (x.1.1 * (Q 0).gl₁ x.2)) := by
      show ρ.1.1 * x.1.1 * (Q 0).gl₁ (ρ.2 * x.2) = _
      rw [map_mul, ← mul_assoc, mul_assoc _ x.1.1, ← k₁]
      simp only [mul_assoc]
    unfold pint
    rw [e, left_jac hψ Q hinj hH Fin.succ (Subgroup.mem_subgroupOf.1 hρ.1) ρ.1.2, left₁ hψ Q hinj hH 0 hρ.2]

end GlobalTheory.QVal.Inv

end
