import Formalism.LocalToGlobal.CharacterGerms.CoeffSingleSubstOfLowDegree

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds
namespace GeneralGermZero

open Formalism.IncomingBounds FormalGermZero

variable {C : Type} [Field C] {κ : Type} [Fintype κ]

def addK {σ : Type} (F : κ → MvPowerSeries (Fin 2 × κ) C) (a b : κ → MvPowerSeries σ C) : κ → MvPowerSeries σ C :=
  fun k => MvPowerSeries.subst (fun q : Fin 2 × κ => ![a, b] q.1 q.2) (F k)

def gsumK {σ ι : Type} (F : κ → MvPowerSeries (Fin 2 × κ) C) (Γ : ι → κ → MvPowerSeries σ C) :
    List ι → κ → MvPowerSeries σ C
  | [] => 0
  | c :: l => addK F (Γ c) (gsumK F Γ l)

private theorem cc_subst_lemma {σ τ A : Type} [Finite σ] [CommRing A] (a : σ → MvPowerSeries τ A)
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f : MvPowerSeries σ A) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = MvPowerSeries.constantCoeff f := by
  rw [MvPowerSeries.constantCoeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha)]
  rw [finsum_eq_single _ 0]
  · simp
  · intro e he
    obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
      by_contra h
      push_neg at h
      exact he (Finsupp.ext h)
    rw [map_finsuppProd]
    simp only [map_pow, ha, Finsupp.prod]
    rw [Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (zero_pow hs), smul_zero]

theorem pairK_const {σ : Type} {a b : κ → MvPowerSeries σ C} (ha : ∀ j, MvPowerSeries.constantCoeff (a j) = 0)
    (hb : ∀ j, MvPowerSeries.constantCoeff (b j) = 0) :
    ∀ q : Fin 2 × κ, MvPowerSeries.constantCoeff (![a, b] q.1 q.2) = 0 := by
  rintro ⟨j, k⟩
  fin_cases j <;> simp [ha, hb]

theorem pairK_int {V : VF C} {σ : Type} {a b : κ → MvPowerSeries σ C} (ha : ∀ j, IntS V (a j))
    (hb : ∀ j, IntS V (b j)) : ∀ q : Fin 2 × κ, IntS V (![a, b] q.1 q.2) := by
  rintro ⟨j, k⟩
  fin_cases j <;> simp [ha, hb]

def LgAdd (F : κ → MvPowerSeries (Fin 2 × κ) C) (lg : κ → MvPowerSeries κ C) : Prop :=
  ∀ k, MvPowerSeries.subst F (lg k) =
    MvPowerSeries.subst (fun q : κ => (MvPowerSeries.X ((0 : Fin 2), q) : MvPowerSeries (Fin 2 × κ) C)) (lg k) +
      MvPowerSeries.subst (fun q : κ => (MvPowerSeries.X ((1 : Fin 2), q) : MvPowerSeries (Fin 2 × κ) C)) (lg k)

theorem lg_addK {σ : Type} (F : κ → MvPowerSeries (Fin 2 × κ) C) (hF0 : ∀ k, MvPowerSeries.constantCoeff (F k) = 0)
    (lg : κ → MvPowerSeries κ C) (hadd : LgAdd F lg) (a b : κ → MvPowerSeries σ C)
    (ha : ∀ j, MvPowerSeries.constantCoeff (a j) = 0) (hb : ∀ j, MvPowerSeries.constantCoeff (b j) = 0) (k : κ) :
    MvPowerSeries.subst (addK F a b) (lg k) = MvPowerSeries.subst a (lg k) + MvPowerSeries.subst b (lg k) := by
  have hP : MvPowerSeries.HasSubst (fun q : Fin 2 × κ => ![a, b] q.1 q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (pairK_const ha hb)
  have hF : MvPowerSeries.HasSubst F := MvPowerSeries.hasSubst_of_constantCoeff_zero hF0
  have hX0 : MvPowerSeries.HasSubst
      (fun q : κ => (MvPowerSeries.X ((0 : Fin 2), q) : MvPowerSeries (Fin 2 × κ) C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
  have hX1 : MvPowerSeries.HasSubst
      (fun q : κ => (MvPowerSeries.X ((1 : Fin 2), q) : MvPowerSeries (Fin 2 × κ) C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
  have e := congrArg (MvPowerSeries.subst (fun q : Fin 2 × κ => ![a, b] q.1 q.2)) (hadd k)
  rw [MvPowerSeries.subst_comp_subst_apply hF hP, MvPowerSeries.subst_add hP,
    MvPowerSeries.subst_comp_subst_apply hX0 hP, MvPowerSeries.subst_comp_subst_apply hX1 hP] at e
  simp only [MvPowerSeries.subst_X hP, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at e
  exact e

section Sum

variable {F : κ → MvPowerSeries (Fin 2 × κ) C} (hF0 : ∀ k, MvPowerSeries.constantCoeff (F k) = 0)
include hF0

theorem gsumK_const {σ ι : Type} (Γ : ι → κ → MvPowerSeries σ C)
    (hΓ : ∀ c j, MvPowerSeries.constantCoeff (Γ c j) = 0) :
    ∀ (l : List ι) j, MvPowerSeries.constantCoeff (gsumK F Γ l j) = 0
  | [], j => by
    show MvPowerSeries.constantCoeff ((0 : κ → MvPowerSeries σ C) j) = 0
    simp
  | c :: l, j => constantCoeff_subst_zero (pairK_const (hΓ c) (gsumK_const Γ hΓ l)) (hF0 j)

theorem gsumK_int {V : VF C} (hFI : ∀ k, IntS V (F k)) {σ ι : Type} (Γ : ι → κ → MvPowerSeries σ C)
    (hΓ0 : ∀ c j, MvPowerSeries.constantCoeff (Γ c j) = 0) (hΓ : ∀ c j, IntS V (Γ c j)) :
    ∀ (l : List ι) j, IntS V (gsumK F Γ l j)
  | [], j => by
    intro μ
    show V.Ge 0 (MvPowerSeries.coeff μ ((0 : κ → MvPowerSeries σ C) j))
    rw [Pi.zero_apply, map_zero]
    exact VF.Ge.zero 0
  | c :: l, j => IntS.subst (pairK_const (hΓ0 c) (gsumK_const hF0 Γ hΓ0 l))
      (pairK_int (hΓ c) (gsumK_int hFI Γ hΓ0 hΓ l)) (hFI j)

theorem gsumK_lg {lg : κ → MvPowerSeries κ C} (hadd : LgAdd F lg) (hlg0 : ∀ k, MvPowerSeries.constantCoeff (lg k) = 0)
    {σ ι : Type} (Γ : ι → κ → MvPowerSeries σ C)
    (hΓ : ∀ c j, MvPowerSeries.constantCoeff (Γ c j) = 0) (i : κ) :
    ∀ l : List ι, MvPowerSeries.subst (gsumK F Γ l) (lg i) = (l.map fun c => MvPowerSeries.subst (Γ c) (lg i)).sum
  | [] => by
    rw [List.map_nil, List.sum_nil]
    exact subst_zero_of_const _ (hlg0 i)
  | c :: l => by
    rw [List.map_cons, List.sum_cons, ← gsumK_lg hadd hlg0 Γ hΓ i l]
    exact lg_addK F hF0 lg hadd (Γ c) (gsumK F Γ l) (hΓ c) (gsumK_const hF0 Γ hΓ l) i

end Sum

section Sys1

variable {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] (X : RawChart C d I κ)
  (F : κ → MvPowerSeries (Fin 2 × κ) C) (hF0 : ∀ k, MvPowerSeries.constantCoeff (F k) = 0)
  (hFI : ∀ k, IntS V (F k)) (hadd : LgAdd F X.lg)
  (hlin : ∀ k (μ : κ →₀ ℕ), μ.degree ≤ 1 → MvPowerSeries.coeff μ (X.lg k) = MvPowerSeries.coeff μ (MvPowerSeries.X k))
  (hexlg : ∀ k, MvPowerSeries.subst X.lg (X.ex k) = (MvPowerSeries.X k : MvPowerSeries κ C))

include hF0 hFI hadd hlin hexlg

theorem sysK_P {g : Fin 2} (hg : X.CartHyp V g) (S : Sys (RawChart.cart hg)) :
    ∃ P : κ → MvPowerSeries (I g) C, (∀ j, MvPowerSeries.constantCoeff (P j) = 0) ∧
      (∀ j, IntS V (P j)) ∧
      (∀ j c, MvPowerSeries.coeff (Finsupp.single c 1) (P j) = ∑ c', X.u g c' j * S.tan c c') ∧
      ∀ t : I g → MvPowerSeries (I g) C, S.IsT t → ∀ j,
        MvPowerSeries.subst t (P j) =
          MvPowerSeries.subst (fun i => ∑ c', X.u g c' i • (MvPowerSeries.X c' : MvPowerSeries (I g) C)) (X.ex j) := by
  have hl : 2 ≤ V.l := V.l_prime.two_le
  have hlg0 : ∀ k, MvPowerSeries.constantCoeff (X.lg k) = 0 := fun k => by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hlin k 0 (by simp),
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.constantCoeff_X]
  have hcur : ∀ c, ∃ γ : κ → PowerSeries C, IsCv V γ ∧ ∀ i, MvPowerSeries.subst γ (X.lg i) =
      ∑ c' : I g, X.u g c' i • tyS V.l (fun s => S.al c s c') := by
    intro c
    have hm : S.cur c ∈ X.TySet V g := (S.curve c).1
    obtain ⟨γ, lam, hγ, -, hlog, -⟩ := hm
    exact ⟨γ, hγ, hlog⟩
  choose γ hγ hlog using hcur
  have hγ0 : ∀ c, ∀ j, MvPowerSeries.constantCoeff (γ c j) = 0 := fun c j => (hγ c j).1
  have hXc : ∀ c : I g, MvPowerSeries.HasSubst (fun _ : Unit => (MvPowerSeries.X c : MvPowerSeries (I g) C)) :=
    fun c => MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X c
  set Γ : I g → κ → MvPowerSeries (I g) C :=
    fun c j => PowerSeries.subst (MvPowerSeries.X c : MvPowerSeries (I g) C) (γ c j) with hΓdef
  have hΓ0 : ∀ c j, MvPowerSeries.constantCoeff (Γ c j) = 0 := fun c j =>
    constantCoeff_subst_zero (fun _ => MvPowerSeries.constantCoeff_X c) (hγ0 c j)
  have hΓI : ∀ c j, IntS V (Γ c j) := fun c j =>
    IntS.subst (fun _ => MvPowerSeries.constantCoeff_X c) (fun _ => intS_X c) (intS_ps.2 (hγ c j).2)
  have hΓlg : ∀ c i, MvPowerSeries.subst (Γ c) (X.lg i) =
      ∑ c', X.u g c' i • PowerSeries.subst (MvPowerSeries.X c : MvPowerSeries (I g) C) (tyS V.l (fun s => S.al c s c')) := by
    intro c i
    have e1 : MvPowerSeries.subst (Γ c) (X.lg i) =
        PowerSeries.subst (MvPowerSeries.X c : MvPowerSeries (I g) C) (MvPowerSeries.subst (γ c) (X.lg i)) := by
      show _ = MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X c : MvPowerSeries (I g) C)) _
      rw [MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero (hγ0 c)) (hXc c)]
      rfl
    rw [e1, hlog c i, ← PowerSeries.coe_substAlgHom
      (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X c)), map_sum]
    simp only [map_smul]
  set P : κ → MvPowerSeries (I g) C := gsumK F Γ Finset.univ.toList with hPdef
  have hP0 : ∀ j, MvPowerSeries.constantCoeff (P j) = 0 := gsumK_const hF0 Γ hΓ0 _
  have hPlg : ∀ i, MvPowerSeries.subst P (X.lg i) =
      ∑ c, ∑ c', X.u g c' i • PowerSeries.subst (MvPowerSeries.X c : MvPowerSeries (I g) C)
        (tyS V.l (fun s => S.al c s c')) := by
    intro i
    rw [gsumK_lg hF0 hadd hlg0 Γ hΓ0 i, Finset.sum_map_toList]
    exact Finset.sum_congr rfl fun c _ => hΓlg c i
  refine ⟨P, hP0, gsumK_int hF0 hFI Γ hΓ0 hΓI _, ?_, ?_⟩
  · intro j c
    have hl1 := coeff_single_subst_lin P hP0 (X.lg j) j (hlin j) c
    rw [← hl1, hPlg j, map_sum]
    simp only [map_sum, MvPowerSeries.coeff_smul, coeff_single_substX_tyS hl, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
    congr 1
    exact congrFun (S.curve c).2.1 (Sum.inl c')
  · intro t ht j
    have ht0 := ht.1
    have hts := MvPowerSeries.hasSubst_of_constantCoeff_zero ht0
    set Q : κ → MvPowerSeries (I g) C := fun j => MvPowerSeries.subst t (P j) with hQ
    have hQ0 : ∀ j, MvPowerSeries.constantCoeff (Q j) = 0 := fun j => constantCoeff_subst_zero ht0 (hP0 j)
    have hPS := MvPowerSeries.hasSubst_of_constantCoeff_zero hP0
    have hQlg : ∀ i, MvPowerSeries.subst Q (X.lg i) =
        ∑ c', X.u g c' i • (MvPowerSeries.X c' : MvPowerSeries (I g) C) := by
      intro i
      have e1 : MvPowerSeries.subst Q (X.lg i) = MvPowerSeries.subst t (MvPowerSeries.subst P (X.lg i)) := by
        rw [MvPowerSeries.subst_comp_subst_apply hPS hts]
      have e2 : ∀ c (A : PowerSeries C), MvPowerSeries.subst t
          (PowerSeries.subst (MvPowerSeries.X c : MvPowerSeries (I g) C) A) = PowerSeries.subst (t c) A := by
        intro c A
        show MvPowerSeries.subst t (MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X c : MvPowerSeries (I g) C)) A) =
          MvPowerSeries.subst (fun _ : Unit => t c) A
        rw [MvPowerSeries.subst_comp_subst_apply (hXc c) hts]
        congr 1
        funext u
        rw [MvPowerSeries.subst_X hts]
      rw [e1, hPlg i, ← MvPowerSeries.coe_substAlgHom hts, map_sum]
      simp only [map_sum, map_smul, MvPowerSeries.coe_substAlgHom hts, e2]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c' _ => ?_
      rw [← Finset.smul_sum, isT_sum S ht c']
    have hlgS := MvPowerSeries.hasSubst_of_constantCoeff_zero hlg0
    have hQS := MvPowerSeries.hasSubst_of_constantCoeff_zero hQ0
    have h := congrArg (MvPowerSeries.subst Q) (hexlg j)
    rw [MvPowerSeries.subst_comp_subst_apply hlgS hQS, MvPowerSeries.subst_X hQS] at h
    show Q j = _
    rw [← h]
    congr 1
    funext i
    exact hQlg i

private theorem v_sum_lemma {K : Type} [Field K] (w : AddValuation K (WithTop ℝ)) {ι : Type} (s : Finset ι)
    (x : ι → K) (hx : ∀ i ∈ s, (0 : WithTop ℝ) ≤ w (x i)) : (0 : WithTop ℝ) ≤ w (∑ i ∈ s, x i) :=
  Finset.sum_induction x (fun y => (0 : WithTop ℝ) ≤ w y) (fun a b ha hb => le_trans (le_min ha hb) (AddValuation.map_add w a b))
    (by
      show (0 : WithTop ℝ) ≤ w 0
      rw [AddValuation.map_zero]
      exact le_top) hx

theorem general_germ_zero
    (hsat : ∀ g, ∃ w : κ → I g → C, (∀ x c, V.Ge 0 (w x c)) ∧
      ∀ c c' : I g, ∑ x, X.u g c x * w x c' = if c = c' then 1 else 0)
    (H : ∀ g, X.CartHyp V g) : RawChart.IntegralGermIndependentOfSystem H := by
  intro S S₂ t t₂ hT hT₂
  choose w hw0 hw using hsat
  choose P hP0 hPI hPlin hPeq using fun g => sysK_P X F hF0 hFI hadd hlin hexlg (H g) (S g)
  choose P₂ hP0₂ hPI₂ hPlin₂ hPeq₂ using fun g => sysK_P X F hF0 hFI hadd hlin hexlg (H g) (S₂ g)
  refine AbstractGermZero.abstract_germ_zero V I t t₂ (fun g k => ∑ x, w g x k • P g x) (fun g k => ∑ x, w g x k • P₂ g x)
    (fun g c => (hT g).1 c) (fun g c => (hT₂ g).1 c) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro g k
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_sum]
    simp [MvPowerSeries.coeff_smul, hP0]
  · intro g k μ
    show (0 : WithTop ℝ) ≤ V.v (MvPowerSeries.coeff μ (∑ x, w g x k • P g x))
    rw [map_sum]
    refine v_sum_lemma X F hF0 hFI hadd hlin hexlg V.v _ _ (fun x _ => ?_)
    have h1 : (0 : WithTop ℝ) ≤ V.v (w g x k) := hw0 g x k
    have h2 : (0 : WithTop ℝ) ≤ V.v (MvPowerSeries.coeff μ (P g x)) := hPI g x μ
    rw [MvPowerSeries.coeff_smul, AddValuation.map_mul]
    exact add_nonneg h1 h2
  · intro g
    have hm : (Matrix.of fun k c : I g => MvPowerSeries.coeff (Finsupp.single c 1) (∑ x, w g x k • P g x)) =
        (Matrix.of (S g).tan).transpose := by
      ext k c
      simp only [Matrix.of_apply, Matrix.transpose_apply, map_sum, MvPowerSeries.coeff_smul, hPlin, Finset.mul_sum]
      rw [Finset.sum_comm]
      have hr : ∀ c' : I g, ∑ x, w g x k * (X.u g c' x * (S g).tan c c') =
          (∑ x, X.u g c' x * w g x k) * (S g).tan c c' := by
        intro c'
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun x _ => by ring)
      simp [hr, hw g]
    rw [hm, Matrix.det_transpose]
    exact (S g).unimod
  · intro g k
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_sum]
    simp [MvPowerSeries.coeff_smul, hP0₂]
  · intro g k μ
    show (0 : WithTop ℝ) ≤ V.v (MvPowerSeries.coeff μ (∑ x, w g x k • P₂ g x))
    rw [map_sum]
    refine v_sum_lemma X F hF0 hFI hadd hlin hexlg V.v _ _ (fun x _ => ?_)
    have h1 : (0 : WithTop ℝ) ≤ V.v (w g x k) := hw0 g x k
    have h2 : (0 : WithTop ℝ) ≤ V.v (MvPowerSeries.coeff μ (P₂ g x)) := hPI₂ g x μ
    rw [MvPowerSeries.coeff_smul, AddValuation.map_mul]
    exact add_nonneg h1 h2
  · intro g
    have hm : (Matrix.of fun k c : I g => MvPowerSeries.coeff (Finsupp.single c 1) (∑ x, w g x k • P₂ g x)) =
        (Matrix.of (S₂ g).tan).transpose := by
      ext k c
      simp only [Matrix.of_apply, Matrix.transpose_apply, map_sum, MvPowerSeries.coeff_smul, hPlin₂, Finset.mul_sum]
      rw [Finset.sum_comm]
      have hr : ∀ c' : I g, ∑ x, w g x k * (X.u g c' x * (S₂ g).tan c c') =
          (∑ x, X.u g c' x * w g x k) * (S₂ g).tan c c' := by
        intro c'
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun x _ => by ring)
      simp [hr, hw g]
    rw [hm, Matrix.det_transpose]
    exact (S₂ g).unimod
  · intro g k
    have ht : MvPowerSeries.HasSubst (t g) := MvPowerSeries.hasSubst_of_constantCoeff_zero (hT g).1
    have ht₂ : MvPowerSeries.HasSubst (t₂ g) := MvPowerSeries.hasSubst_of_constantCoeff_zero (hT₂ g).1
    rw [← MvPowerSeries.coe_substAlgHom ht, ← MvPowerSeries.coe_substAlgHom ht₂]
    simp only [map_sum, map_smul]
    simp only [MvPowerSeries.coe_substAlgHom, hPeq g (t g) (hT g), hPeq₂ g (t₂ g) (hT₂ g)]

end Sys1

end GeneralGermZero

end Formalism.L2.FormalSeriesBounds
