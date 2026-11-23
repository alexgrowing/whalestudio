import Mathlib
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

open Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.CasselmanOsborne

open Formalism.REAL (GlRel qdet qminor Tm)
open CompanionTheory.D.DSIC

section Rel

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def Pres (R : Submodule ℂ (V × W)) (S : Module.End ℂ V) (T : Module.End ℂ W) : Prop :=
  ∀ x y, (x, y) ∈ R → (S x, T y) ∈ R

theorem pres_mul {R : Submodule ℂ (V × W)} {S S' : Module.End ℂ V} {T T' : Module.End ℂ W}
    (h : Pres R S T) (h' : Pres R S' T') : Pres R (S * S') (T * T') :=
  fun x y hxy => h _ _ (h' x y hxy)

theorem pres_ofFn {R : Submodule ℂ (V × W)} : ∀ {t : ℕ} (S : Fin t → Module.End ℂ V)
    (T : Fin t → Module.End ℂ W), (∀ k, Pres R (S k) (T k)) →
    Pres R (List.ofFn S).prod (List.ofFn T).prod
  | 0, _, _, _ => by
    intro x y hxy
    simpa using hxy
  | t + 1, S, T, h => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    exact pres_mul (h 0) (pres_ofFn _ _ fun k => h k.succ)

theorem pres_qminor {n t : ℕ} {R : Submodule ℂ (V × W)} (E : Fin n → Fin n → Module.End ℂ V)
    (F : Fin n → Fin n → Module.End ℂ W) (a b : Fin t → Fin n)
    (h : ∀ i j, Pres R (E (a i) (b j)) (F (a i) (b j))) (u : ℂ) :
    Pres R (qminor E a b u) (qminor F a b u) := by
  intro x y hxy
  have key : ∀ σ : Equiv.Perm (Fin t), Pres R
      (((Equiv.Perm.sign σ : ℤ) : Module.End ℂ V) *
        (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (a (σ k)) (b k)).prod)
      (((Equiv.Perm.sign σ : ℤ) : Module.End ℂ W) *
        (List.ofFn fun k : Fin t => Tm F (u - (k : ℂ)) (a (σ k)) (b k)).prod) := by
    intro σ
    refine pres_mul ?_ (pres_ofFn _ _ fun k => ?_)
    · intro x y hxy
      have := R.smul_mem (((Equiv.Perm.sign σ : ℤ) : ℂ)) hxy
      simpa [Module.End.intCast_apply, Int.cast_smul_eq_zsmul] using this
    · intro x y hxy
      have h1 := h (σ k) k x y hxy
      unfold Tm
      split_ifs with hc
      · have h2 := R.smul_mem (u - (k : ℂ)) hxy
        have := R.add_mem h2 h1
        exact this
      · simpa using h1
  have := R.sum_mem (t := univ) (fun σ _ => key σ x y hxy)
  unfold qminor
  rw [LinearMap.sum_apply, LinearMap.sum_apply, prod_mk_sum]
  exact this

theorem blk_eq {n : ℕ} (ε : Fin n → Bool) (s : Bool) (i : Fin (nb ε s)) : ε (blk ε s i) = s := by
  have := Finset.orderEmbOfFin_mem (univ.filter fun a => ε a = s) rfl i
  exact (Finset.mem_filter.1 this).2

theorem pres_zeta {n : ℕ} {R : Submodule ℂ (V × W)} (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V)
    (F : Fin n → Fin n → Module.End ℂ W)
    (h : ∀ c d, ε c = ε d → Pres R (E c d) (F c d)) (u : ℂ) :
    Pres R (zeta ε E u) (zeta ε F u) :=
  pres_mul (pres_qminor E F _ _ (fun _ _ => h _ _ ((blk_eq ε _ _).trans (blk_eq ε _ _).symm)) _)
    (pres_qminor E F _ _ (fun _ _ => h _ _ ((blk_eq ε _ _).trans (blk_eq ε _ _).symm)) _)

theorem pres_graph (φ : V →ₗ[ℂ] W) (S : Module.End ℂ V) (T : Module.End ℂ W) :
    Pres φ.graph S T ↔ ∀ x, φ (S x) = T (φ x) := by
  constructor
  · intro h x
    have := h x (φ x) (by simp)
    simpa using this.symm
  · intro h x y hxy
    have : y = φ x := by simpa using hxy
    simp [this, h]

end Rel

section Chains

variable {n : ℕ} {ε : Fin n → Bool} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def degSub (ε : Fin n → Bool) (V : Type) [AddCommGroup V] [Module ℂ V] (j : ℕ) : Submodule ℂ (Ch ε V) where
  carrier := {x | Deg j x}
  add_mem' := fun {x y} hx hy A hA => by simp [hx A hA, hy A hA]
  zero_mem' := fun A _ => rfl
  smul_mem' := fun c x hx A hA => by simp [hx A hA]

theorem deg_lift {j : ℕ} (φ : V →ₗ[ℂ] W) {x : Ch ε V} (hx : Deg j x) : Deg j (lift ε φ x) :=
  fun A hA => by simp [hx A hA]

theorem bd_apply (E : Fin n → Fin n → Module.End ℂ V) (x : Ch ε V) (A : Finset (NC ε)) :
    bd ε E x A = ∑ i : NC ε, E i.1.1 i.1.2 (if i ∈ A then 0 else sg i A • x (insert i A)) := by
  simp [bd, bdA, LinearMap.sum_apply, Finset.sum_apply, ann]

theorem deg_bd {j : ℕ} (E : Fin n → Fin n → Module.End ℂ V) {x : Ch ε V} (hx : Deg (j + 1) x) :
    Deg j (bd ε E x) := by
  intro A hA
  rw [bd_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  split_ifs with h
  · simp
  · rw [hx _ (by rw [Finset.card_insert_of_notMem h]; omega)]
    simp

theorem lift_bd (φ : V →ₗ[ℂ] W) (E : Fin n → Fin n → Module.End ℂ V) (F : Fin n → Fin n → Module.End ℂ W)
    (h : ∀ a b x, φ (E a b x) = F a b (φ x)) (x : Ch ε V) : lift ε φ (bd ε E x) = bd ε F (lift ε φ x) := by
  funext A
  rw [lift_apply, bd_apply, bd_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h]
  split_ifs <;> simp

theorem lift_qdet (φ : V →ₗ[ℂ] W) (E : Fin n → Fin n → Module.End ℂ V) (F : Fin n → Fin n → Module.End ℂ W)
    (h : ∀ a b x, φ (E a b x) = F a b (φ x)) (u : ℂ) (x : Ch ε V) :
    lift ε φ (lift ε (qdet E u) x) = lift ε (qdet F u) (lift ε φ x) := by
  funext A
  simp only [lift_apply]
  exact (pres_graph φ _ _).1 (pres_qminor E F id id (fun i j => (pres_graph φ _ _).2 (h i j)) u) _

theorem lift_zeta (hG : GFacts) (φ : V →ₗ[ℂ] W) (E : Fin n → Fin n → Module.End ℂ V)
    (F : Fin n → Fin n → Module.End ℂ W)
    (h : ∀ a b x, φ (E a b x) = F a b (φ x)) (u : ℂ) (x : Ch ε V) :
    lift ε φ (zeta ε (Fop ε E) u x) = zeta ε (Fop ε F) u (lift ε φ x) := by
  obtain ⟨g, hg, -⟩ := hG n ε
  refine (pres_graph (lift ε φ) _ _).1 (pres_zeta ε _ _ (fun c d _ => (pres_graph _ _ _).2 fun x => ?_) u) x
  funext A
  simp [Fop, hg, h, map_sum]

theorem deg_Fop (hG : GFacts) {j : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (c d : Fin n) {x : Ch ε V}
    (hx : Deg j x) : Deg j (Fop ε E c d x) := by
  obtain ⟨g, hg, -, hc, -⟩ := hG n ε
  intro A hA
  simp only [Fop, LinearMap.add_apply, Pi.add_apply, lift_apply, hx A hA, map_zero, zero_add, hg]
  refine Finset.sum_eq_zero fun B _ => ?_
  by_cases h0 : g c d A B = 0
  · simp [h0]
  · rw [hx B (by rw [← (hc c d A B h0).1]; exact hA), smul_zero]

theorem deg_zeta (hG : GFacts) {j : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (u : ℂ) {x : Ch ε V}
    (hx : Deg j x) : Deg j (zeta ε (Fop ε E) u x) := by
  have := pres_zeta (R := (degSub ε V j).prod ⊤) ε (Fop ε E) (Fop ε E)
    (fun c d _ x y hxy => ⟨deg_Fop hG E c d hxy.1, trivial⟩) u x x ⟨hx, trivial⟩
  exact this.1

theorem Gop_deg_zero (c d : Fin n) {x : Ch ε V} (hx : Deg 0 x) : Gop ε c d x = 0 := by
  have : ∀ j : NC ε, ann j x = 0 := by
    intro j
    funext A
    by_cases h : j ∈ A
    · simp [ann, h]
    · simp [ann, h, hx (insert j A) (by rw [Finset.card_insert_of_notMem h]; omega)]
  simp [Gop, LinearMap.sum_apply, this]

theorem zeta_deg_zero (E : Fin n → Fin n → Module.End ℂ V) (u : ℂ) {x : Ch ε V}
    (hx : Deg 0 x) : zeta ε (Fop ε E) u x ∅ = zeta ε E u (x ∅) := by
  have := pres_zeta (R := (degSub ε V 0).prod ⊤ ⊓ (LinearMap.proj (R := ℂ) (φ := fun _ => V) ∅).graph)
    ε (Fop ε E) E (fun c d _ x y hxy => by
      have h1 : Deg 0 x := hxy.1.1
      have h2 : y = x ∅ := by simpa using hxy.2
      have h3 : Fop ε E c d x = lift ε (E c d) x := by simp [Fop, Gop_deg_zero c d h1]
      refine ⟨⟨?_, trivial⟩, ?_⟩
      · rw [h3]; exact deg_lift _ h1
      · simp [h3, h2]) u x (x ∅) ⟨⟨hx, trivial⟩, by simp⟩
  have h := this.2
  simpa using Eq.symm h

theorem bd_zeta (hB : BdFacts) (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (u : ℂ) (x : Ch ε V) :
    bd ε E (zeta ε (Fop ε E) u x) = zeta ε (Fop ε E) u (bd ε E x) :=
  (pres_graph (bd ε E) _ _).1 (pres_zeta ε _ _ (fun c d hcd => (pres_graph _ _ _).2 fun x =>
    (LinearMap.congr_fun ((hB n ε V E hE).2 c d hcd).1.eq x).symm) u) x

theorem bd_qdet (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (u : ℂ) (x : Ch ε V) :
    bd ε E (lift ε (qdet E u) x) = lift ε (qdet E u) (bd ε E x) :=
  (lift_bd (qdet E u) E E (fun a b v => LinearMap.congr_fun (Formalism.REAL.qDetCentral _ n E hE u a b) v) x).symm

end Chains

theorem co_of (hB : BdFacts) (hG : GFacts) (hC : Cover) (h0 : CapelliDeterminantBlockProduct) : CO := by
  intro n ε V _ _ E hE u j
  induction j generalizing V with
  | zero =>
    intro x hx _
    obtain ⟨w, hw⟩ := h0 n ε V E hE u (x ∅)
    classical
    let w' : Ch ε V := fun A => ∑ i : NC ε, if A = {i} then w i else 0
    have hw' : Deg (0 + 1) w' := by
      intro A hA
      refine Finset.sum_eq_zero fun i _ => if_neg ?_
      rintro rfl
      simp at hA
    refine ⟨w', hw', ?_⟩
    funext A
    by_cases hA : A = ∅
    · subst hA
      rw [Pi.sub_apply, lift_apply, zeta_deg_zero E u hx, hw, bd_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [sg, w']
    · have hc : A.card ≠ 0 := by simpa using hA
      rw [Pi.sub_apply, deg_lift _ hx A hc, deg_zeta hG E u hx A hc, deg_bd E hw' A hc, sub_zero]
  | succ j ih =>
    intro x hx hbx
    obtain ⟨Y, _, _, EY, π, hY, hs, hπ, hac⟩ := hC n ε V E hE
    classical
    have hK : ∀ a b, ∀ y ∈ LinearMap.ker π, EY a b y ∈ LinearMap.ker π := by
      intro a b y hy
      rw [LinearMap.mem_ker] at hy ⊢
      rw [hπ, hy, map_zero]
    let EK : Fin n → Fin n → Module.End ℂ (LinearMap.ker π) := fun a b => (EY a b).restrict (hK a b)
    have hι : ∀ a b y, (LinearMap.ker π).subtype (EK a b y) = EY a b ((LinearMap.ker π).subtype y) :=
      fun _ _ _ => rfl
    have hEK : GlRel EK := by
      intro a b c d
      ext y
      have := LinearMap.congr_fun (hY a b c d) (y : Y)
      split_ifs at this ⊢ <;> simpa [EK] using this
    let x' : Ch ε Y := fun A => if A.card = j + 1 then (hs (x A)).choose else 0
    have hx' : Deg (j + 1) x' := fun A hA => if_neg hA
    have hπx : lift ε π x' = x := by
      funext A
      by_cases hA : A.card = j + 1
      · simp only [lift_apply, x', if_pos hA]
        exact (hs (x A)).choose_spec
      · simp [x', hA, hx A hA]
    have hy : ∀ A, bd ε EY x' A ∈ LinearMap.ker π := by
      intro A
      have := congrFun (lift_bd π EY E hπ x') A
      rw [hπx, hbx] at this
      exact this
    let y : Ch ε (LinearMap.ker π) := fun A => ⟨_, hy A⟩
    have hιy : lift ε (LinearMap.ker π).subtype y = bd ε EY x' := rfl
    have hyd : Deg j y := fun A hA => Subtype.ext (deg_bd EY hx' A hA)
    have hyb : bd ε EK y = 0 := by
      have := lift_bd _ EK EY hι y
      rw [hιy, show bd ε EY (bd ε EY x') = 0 from LinearMap.congr_fun (hB n ε Y EY hY).1 x'] at this
      funext A
      exact Subtype.ext (congrFun this A)
    obtain ⟨w, hw, hDw⟩ := ih _ EK hEK y hyd hyb
    have hpush := congrArg (lift ε (LinearMap.ker π).subtype) hDw
    rw [map_sub, lift_qdet _ EK EY hι, lift_zeta hG _ EK EY hι, lift_bd _ EK EY hι, hιy] at hpush
    obtain ⟨t, ht, hbt⟩ := hac j
      (lift ε (qdet EY u) x' - zeta ε (Fop ε EY) u x' - lift ε (LinearMap.ker π).subtype w)
      ((degSub ε Y (j + 1)).sub_mem ((degSub ε Y (j + 1)).sub_mem (deg_lift _ hx') (deg_zeta hG EY u hx'))
        (deg_lift _ hw))
      (by rw [map_sub, map_sub, bd_qdet EY hY, bd_zeta hB EY hY, hpush, sub_self])
    refine ⟨lift ε π t, deg_lift _ ht, ?_⟩
    have h2 : lift ε π (lift ε (LinearMap.ker π).subtype w) = 0 := by
      funext A
      exact (w A).2
    rw [← lift_bd π EY E hπ, hbt, map_sub, map_sub, h2, lift_qdet π EY E hπ, lift_zeta hG π EY E hπ, hπx, sub_zero]

end GlobalTheory.CompanionTheory.CasselmanOsborne
