import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.JetProd

open Finsupp

section General

variable {C : Type} [Field C] {ι τ : Type} [Fintype ι] {σ : ι → Type} (e : ∀ i, σ i ↪ τ)

open scoped BigOperators in
open NumberField in
open Finsupp in
variable {C : Type} [Field C] {ι τ : Type} [Fintype ι] {σ : ι → Type} (e : ∀ i, σ i ↪ τ) in
private lemma prod_monomial_eq_monomial_sum_prod' {α κ : Type} (s : Finset κ) (D : κ → α →₀ ℕ) (a : κ → C) :
    ∏ k ∈ s, MvPolynomial.monomial (D k) (a k) =
      MvPolynomial.monomial (∑ k ∈ s, D k) (∏ k ∈ s, a k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    rw [Finset.prod_insert hk, Finset.sum_insert hk, Finset.prod_insert hk, ih,
      MvPolynomial.monomial_mul]

open scoped BigOperators in
open NumberField in
open Finsupp in
variable {C : Type} [Field C] {ι τ : Type} [Fintype ι] {σ : ι → Type} (e : ∀ i, σ i ↪ τ) in
private lemma jetAt0_zero_left_unramified_depth {α : Type} (G : MvPowerSeries α C) :
    _root_.Formalism.IncomingBounds.jetAt0 (0 : MvPolynomial α C) G = 0 := by
  unfold _root_.Formalism.IncomingBounds.jetAt0
  simp

open scoped BigOperators in
open NumberField in
open Finsupp in
variable {C : Type} [Field C] {ι τ : Type} [Fintype ι] {σ : ι → Type} (e : ∀ i, σ i ↪ τ) in
private lemma jetAt0_eq_sum_coeff_mul_mfact_of_support_subset {α : Type} (P : MvPolynomial α C) (G : MvPowerSeries α C)
    {s : Finset (α →₀ ℕ)} (hs : P.support ⊆ s) :
    _root_.Formalism.IncomingBounds.jetAt0 P G = ∑ m ∈ s, MvPolynomial.coeff m P * (_root_.Formalism.IncomingBounds.mfact m : C) * MvPowerSeries.coeff m G := by
  unfold _root_.Formalism.IncomingBounds.jetAt0
  refine Finset.sum_subset hs fun m _ hm => ?_
  rw [MvPolynomial.mem_support_iff, not_not] at hm
  rw [hm, zero_mul, zero_mul]

open scoped BigOperators in
open NumberField in
open Finsupp in
variable {C : Type} [Field C] {ι τ : Type} [Fintype ι] {σ : ι → Type} (e : ∀ i, σ i ↪ τ) in
private lemma jetAt0_add_left' {α : Type} (P Q : MvPolynomial α C) (G : MvPowerSeries α C) :
    _root_.Formalism.IncomingBounds.jetAt0 (P + Q) G = _root_.Formalism.IncomingBounds.jetAt0 P G + _root_.Formalism.IncomingBounds.jetAt0 Q G := by
  classical
  rw [jetAt0_eq_sum_coeff_mul_mfact_of_support_subset (P + Q) G (MvPolynomial.support_add (p := P) (q := Q)),
    jetAt0_eq_sum_coeff_mul_mfact_of_support_subset P G Finset.subset_union_left,
    jetAt0_eq_sum_coeff_mul_mfact_of_support_subset Q G Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add]
  ring

open scoped BigOperators in
open NumberField in
open Finsupp in
variable {C : Type} [Field C] {ι τ : Type} [Fintype ι] {σ : ι → Type} (e : ∀ i, σ i ↪ τ) in
private lemma jetAt0_monomial_eq_mul_mfact_mul_coeff {α : Type} (D : α →₀ ℕ) (a : C) (G : MvPowerSeries α C) :
    _root_.Formalism.IncomingBounds.jetAt0 (MvPolynomial.monomial D a) G = a * (_root_.Formalism.IncomingBounds.mfact D : C) * MvPowerSeries.coeff D G := by
  classical
  rw [jetAt0_eq_sum_coeff_mul_mfact_of_support_subset _ G (MvPolynomial.support_monomial_subset (s := D) (a := a)),
    Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl]

open scoped BigOperators in
open NumberField in
open Finsupp in
variable {C : Type} [Field C] {ι τ : Type} [Fintype ι] {σ : ι → Type} (e : ∀ i, σ i ↪ τ) in
private lemma jetAt0_sum_monomial_eq_sum_mul_mfact_mul_coeff {α κ : Type} (F : Finset κ) (D : κ → α →₀ ℕ) (a : κ → C)
    (G : MvPowerSeries α C) :
    _root_.Formalism.IncomingBounds.jetAt0 (∑ f ∈ F, MvPolynomial.monomial (D f) (a f)) G =
      ∑ f ∈ F, a f * (_root_.Formalism.IncomingBounds.mfact (D f) : C) * MvPowerSeries.coeff (D f) G := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [jetAt0_zero_left_unramified_depth]
  | insert f F hf ih => rw [Finset.sum_insert hf, Finset.sum_insert hf, jetAt0_add_left', ih, jetAt0_monomial_eq_mul_mfact_mul_coeff]

open scoped BigOperators in
open NumberField in
open Finsupp in
variable {C : Type} [Field C] {ι τ : Type} [Fintype ι] {σ : ι → Type} (e : ∀ i, σ i ↪ τ) in
private lemma coeff_rename_eq_zero_of_not_mem_range_embDomain {α β : Type} (f : α ↪ β) (p : MvPowerSeries α C)
    {x : β →₀ ℕ} (hx : x ∉ Set.range (Finsupp.embDomain f)) :
    MvPowerSeries.coeff x (MvPowerSeries.rename f p) = 0 := by
  rw [MvPowerSeries.coeff_rename]
  refine Finset.sum_eq_zero fun y hy => ?_
  rw [Set.Finite.mem_toFinset] at hy
  exact absurd ⟨y, by rw [Finsupp.embDomain_eq_mapDomain]; simpa using hy⟩ hx

open scoped BigOperators in
open NumberField in
open Finsupp in
variable {C : Type} [Field C] {ι τ : Type} [Fintype ι] {σ : ι → Type} (e : ∀ i, σ i ↪ τ) in
private lemma sum_embDomain_apply_eq_of_disjoint (hd : ∀ i j x y, e i x = e j y → i = j)
    (z : ∀ i, σ i →₀ ℕ) (j : ι) (x : σ j) :
    (∑ k, Finsupp.embDomain (e k) (z k)) (e j x) = z j x := by
  classical
  rw [Finsupp.finset_sum_apply, Finset.sum_eq_single j]
  · exact Finsupp.embDomain_apply_self (e j) (z j) x
  · intro k _ hk
    apply Finsupp.embDomain_notin_range
    rintro ⟨w, hw⟩
    exact hk (hd k j w x hw)
  · intro h
    exact absurd (Finset.mem_univ j) h

open scoped BigOperators in
open NumberField in
open Finsupp in
variable {C : Type} [Field C] {ι τ : Type} [Fintype ι] {σ : ι → Type} (e : ∀ i, σ i ↪ τ) in
private lemma coeff_sum_embDomain_prod_rename_eq_prod_coeff (hd : ∀ i j x y, e i x = e j y → i = j)
    (G : ∀ i, MvPowerSeries (σ i) C) (m : ∀ i, σ i →₀ ℕ) :
    MvPowerSeries.coeff (∑ k, Finsupp.embDomain (e k) (m k))
        (∏ j, MvPowerSeries.rename (e j) (G j)) = ∏ j, MvPowerSeries.coeff (m j) (G j) := by
  classical
  rw [MvPowerSeries.coeff_prod]
  set l0 : ι →₀ (τ →₀ ℕ) := Finsupp.equivFunOnFinite.symm fun k => Finsupp.embDomain (e k) (m k)
    with hl0
  have hl0j : ∀ j, l0 j = Finsupp.embDomain (e j) (m j) := fun j => by simp [hl0]
  rw [Finset.sum_eq_single l0]
  · refine Finset.prod_congr rfl fun j _ => ?_
    rw [hl0j]
    exact MvPowerSeries.coeff_embDomain_rename (e j) (G j) (m j)
  · intro b hb hne
    by_contra hprod
    apply hne
    rw [Finset.mem_finsuppAntidiag] at hb
    have hz : ∀ j, ∃ z, Finsupp.embDomain (e j) z = b j := fun j => by
      by_contra h
      exact Finset.prod_ne_zero_iff.mp hprod j (Finset.mem_univ j)
        (coeff_rename_eq_zero_of_not_mem_range_embDomain (e j) (G j) (by rintro ⟨z, hz⟩; exact h ⟨z, hz⟩))
    choose z hz using hz
    have hsum : ∑ k, Finsupp.embDomain (e k) (z k) = ∑ k, Finsupp.embDomain (e k) (m k) := by
      rw [← hb.1]
      exact Finset.sum_congr rfl fun k _ => hz k
    have hzm : z = m := by
      funext j
      ext x
      rw [← sum_embDomain_apply_eq_of_disjoint e hd z j x, hsum,
        sum_embDomain_apply_eq_of_disjoint e hd m j x]
    ext j : 1
    rw [← hz j, hzm, hl0j]
  · intro h
    exfalso
    apply h
    rw [Finset.mem_finsuppAntidiag]
    refine ⟨?_, by simp⟩
    exact Finset.sum_congr rfl fun j _ => hl0j j

open scoped BigOperators in
open NumberField in
open Finsupp in
variable {C : Type} [Field C] {ι τ : Type} [Fintype ι] {σ : ι → Type} (e : ∀ i, σ i ↪ τ) in
private lemma prod_factorial_sum_embDomain_eq_prod_prod_factorial (hd : ∀ i j x y, e i x = e j y → i = j)
    (m : ∀ i, σ i →₀ ℕ) :
    ((∑ k, Finsupp.embDomain (e k) (m k)).prod fun _ n => n.factorial) =
      ∏ j, (m j).prod fun _ n => n.factorial := by
  classical
  have hsub : (∑ k, Finsupp.embDomain (e k) (m k)).support ⊆
      Finset.univ.biUnion fun j => (m j).support.map (e j) := by
    refine (Finsupp.support_finset_sum).trans ?_
    simp [Finsupp.support_embDomain]
  have hdisj : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint
      fun j => (m j).support.map (e j) := by
    intro j _ k _ hjk
    refine Finset.disjoint_left.mpr fun y hy hy' => ?_
    simp only [Finset.mem_map] at hy hy'
    obtain ⟨x, _, rfl⟩ := hy
    obtain ⟨x', _, hx'⟩ := hy'
    exact hjk (hd k j x' x hx').symm
  rw [Finsupp.prod_of_support_subset _ hsub _ (fun _ _ => rfl), Finset.prod_biUnion hdisj]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Finset.prod_map, Finsupp.prod]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [sum_embDomain_apply_eq_of_disjoint e hd m j x]

open scoped BigOperators in
open NumberField in
open Finsupp in
variable {C : Type} [Field C] {ι τ : Type} [Fintype ι] {σ : ι → Type} (e : ∀ i, σ i ↪ τ) in
theorem _root_.GlobalTheory.JetProd.jetAt0_prod_rename (hd : ∀ i j x y, e i x = e j y → i = j)
    (P : ∀ i, MvPolynomial (σ i) C) (G : ∀ i, MvPowerSeries (σ i) C) :
    _root_.Formalism.IncomingBounds.jetAt0 (∏ j, MvPolynomial.rename (e j) (P j)) (∏ j, MvPowerSeries.rename (e j) (G j)) =
      ∏ j, _root_.Formalism.IncomingBounds.jetAt0 (P j) (G j) := by
  classical
  have hP : ∏ j, MvPolynomial.rename (e j) (P j) =
      ∑ f ∈ Fintype.piFinset fun j => (P j).support,
        MvPolynomial.monomial (∑ k, Finsupp.embDomain (e k) (f k))
          (∏ k, MvPolynomial.coeff (f k) (P k)) := by
    conv_lhs => rw [show P = fun j => ∑ v ∈ (P j).support,
      MvPolynomial.monomial v (MvPolynomial.coeff v (P j)) from
        funext fun j => MvPolynomial.as_sum (P j)]
    simp only [map_sum, MvPolynomial.rename_monomial]
    rw [Finset.prod_univ_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [prod_monomial_eq_monomial_sum_prod']
    simp only [Finsupp.embDomain_eq_mapDomain]
  rw [hP, jetAt0_sum_monomial_eq_sum_mul_mfact_mul_coeff]
  simp only [jetAt0_eq_sum_coeff_mul_mfact_of_support_subset _ _ (subset_refl _)]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [coeff_sum_embDomain_prod_rename_eq_prod_coeff e hd, _root_.Formalism.IncomingBounds.mfact, prod_factorial_sum_embDomain_eq_prod_prod_factorial e hd,
    Nat.cast_prod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  rfl

theorem mvExp_zero' {σ : Type} : mvExp (0 : MvPowerSeries σ C) = 1 := by
  classical
  ext m
  show (∑ k ∈ Finset.range (m.degree + 1),
    MvPowerSeries.coeff m ((0 : MvPowerSeries σ C) ^ k) / (k.factorial : C)) = _
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    simp [zero_pow hk]
  · simp

end General

section Rows

variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)]

def rowEmb {N : ℕ} (ρ : Fin N) : WV I ↪ Fin N × WV I :=
  ⟨fun w => (ρ, w), fun _ _ h => congrArg Prod.snd h⟩

noncomputable def rowSer (hL : Fin 2 → ZMod d → ZMod d → MvPowerSeries (WV I) C) (k : Knd d)
    (g : MvPowerSeries (WV I) C) : MvPowerSeries (WV I) C :=
  g * mvExp (match k with
      | Option.some (g, a, a') => hL g a a'
      | none => 0)

open scoped BigOperators in
open NumberField in
open Finsupp in
variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] in
private lemma mvExp_zero_eq_one' {α : Type} : _root_.Formalism.IncomingBounds.mvExp (0 : MvPowerSeries α C) = 1 := by
  ext m
  show (∑ k ∈ Finset.range (m.degree + 1),
    MvPowerSeries.coeff m ((0 : MvPowerSeries α C) ^ k) / (k.factorial : C)) =
      MvPowerSeries.coeff m 1
  rw [Finset.sum_range_succ']
  simp

open scoped BigOperators in
open NumberField in
open Finsupp in
variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] in
private lemma rowCopy_eq_rename_rowEmb {N : ℕ} (ρ : Fin N) (g : MvPowerSeries (_root_.Formalism.L2.FormalSeriesBounds.WV I) C) :
    _root_.Formalism.L2.FormalSeriesBounds.rowCopy ρ g = MvPowerSeries.rename (_root_.GlobalTheory.JetProd.rowEmb ρ) g := by
  unfold _root_.Formalism.L2.FormalSeriesBounds.rowCopy
  rw [MvPowerSeries.rename_eq_subst]
  rfl

open scoped BigOperators in
open NumberField in
open Finsupp in
variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] in
private lemma degree_embDomain_eq_degree {α β : Type} (f : α ↪ β) (y : α →₀ ℕ) :
    (Finsupp.embDomain f y).degree = y.degree := by
  classical
  show ∑ i ∈ (Finsupp.embDomain f y).support, (Finsupp.embDomain f y) i = ∑ i ∈ y.support, y i
  rw [Finsupp.support_embDomain, Finset.sum_map]
  simp

open scoped BigOperators in
open NumberField in
open Finsupp in
variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] in
private lemma rename_mvExp_eq_mvExp_rename {α β : Type} (f : α ↪ β) (g : MvPowerSeries α C) :
    MvPowerSeries.rename f (_root_.Formalism.IncomingBounds.mvExp g) = _root_.Formalism.IncomingBounds.mvExp (MvPowerSeries.rename f g) := by
  ext x
  by_cases hx : x ∈ Set.range (Finsupp.embDomain f)
  · obtain ⟨y, rfl⟩ := hx
    rw [MvPowerSeries.coeff_embDomain_rename]
    show (∑ k ∈ Finset.range (y.degree + 1), MvPowerSeries.coeff y (g ^ k) / (k.factorial : C)) =
      ∑ k ∈ Finset.range ((Finsupp.embDomain f y).degree + 1),
        MvPowerSeries.coeff (Finsupp.embDomain f y) (MvPowerSeries.rename f g ^ k) /
          (k.factorial : C)
    rw [degree_embDomain_eq_degree]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← map_pow, MvPowerSeries.coeff_embDomain_rename]
  · rw [coeff_rename_eq_zero_of_not_mem_range_embDomain f _ hx]
    show (0 : C) = ∑ k ∈ Finset.range (x.degree + 1),
        MvPowerSeries.coeff x (MvPowerSeries.rename f g ^ k) / (k.factorial : C)
    refine (Finset.sum_eq_zero fun k _ => ?_).symm
    rw [← map_pow, coeff_rename_eq_zero_of_not_mem_range_embDomain f _ hx, zero_div]

open scoped BigOperators in
open NumberField in
open Finsupp in
variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] in
private lemma valOf_eq_jetAt0_prod_rename_rowSer
    (hL : Fin 2 → ZMod d → ZMod d → MvPowerSeries (_root_.Formalism.L2.FormalSeriesBounds.WV I) C)
    {N : ℕ} (P : MvPolynomial (Fin N × _root_.Formalism.L2.FormalSeriesBounds.WV I) C) (kd : Fin N → _root_.Formalism.L2.FormalSeriesBounds.Knd d)
    (gs : Fin N → MvPowerSeries (_root_.Formalism.L2.FormalSeriesBounds.WV I) C) :
    _root_.Formalism.L2.FormalSeriesBounds.ValOf hL P kd gs = _root_.Formalism.IncomingBounds.jetAt0 P (∏ ρ, MvPowerSeries.rename (_root_.GlobalTheory.JetProd.rowEmb ρ)
      (_root_.GlobalTheory.JetProd.rowSer hL (kd ρ) (gs ρ))) := by
  unfold _root_.Formalism.L2.FormalSeriesBounds.ValOf
  congr 1
  refine Finset.prod_congr rfl fun ρ _ => ?_
  simp only [rowCopy_eq_rename_rowEmb]
  rw [← rename_mvExp_eq_mvExp_rename, ← map_mul]
  rfl

open scoped BigOperators in
open NumberField in
open Finsupp in
variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] in
theorem _root_.GlobalTheory.JetProd.jetProd : _root_.Formalism.L2.FormalSeriesBounds.JetProdSt := by
  intro C _ d I _ hL N K what₂ pl hpl P kind gr
  classical
  let emb : ∀ i, Fin (what₂ i) × _root_.Formalism.L2.FormalSeriesBounds.WV I ↪ Fin N × _root_.Formalism.L2.FormalSeriesBounds.WV I := fun i =>
    ⟨fun x => (pl ⟨i, x.1⟩, x.2), fun x y h => by
      simp only [Prod.mk.injEq] at h
      have h1 := hpl h.1
      simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and] at h1
      exact Prod.ext h1 h.2⟩
  have hdisj : ∀ i j (x : Fin (what₂ i) × _root_.Formalism.L2.FormalSeriesBounds.WV I) (y : Fin (what₂ j) × _root_.Formalism.L2.FormalSeriesBounds.WV I),
      emb i x = emb j y → i = j := fun i j x y h =>
    congrArg Sigma.fst (hpl (congrArg Prod.fst h))
  have hZ : ∀ s, _root_.Formalism.L2.FormalSeriesBounds.grAll pl gr (pl s) = gr s.1 s.2 := fun s => by
    unfold _root_.Formalism.L2.FormalSeriesBounds.grAll
    split_ifs with h
    · rw [hpl h.choose_spec]
    · exact absurd ⟨s, rfl⟩ h
  have hT : ∏ ρ, MvPowerSeries.rename (_root_.GlobalTheory.JetProd.rowEmb ρ)
        (_root_.GlobalTheory.JetProd.rowSer hL (_root_.Formalism.L2.FormalSeriesBounds.kindAll pl kind ρ) (_root_.Formalism.L2.FormalSeriesBounds.grAll pl gr ρ)) =
      ∏ i, MvPowerSeries.rename (emb i) (∏ r, MvPowerSeries.rename (_root_.GlobalTheory.JetProd.rowEmb r)
        (_root_.GlobalTheory.JetProd.rowSer hL (kind i r) (gr i r))) := by
    rw [← Fintype.prod_of_injective pl hpl
      (fun s => MvPowerSeries.rename (_root_.GlobalTheory.JetProd.rowEmb (pl s))
        (_root_.GlobalTheory.JetProd.rowSer hL (kind s.1 s.2) (gr s.1 s.2)))]
    · rw [Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [map_prod]
      refine Finset.prod_congr rfl fun r _ => ?_
      rw [MvPowerSeries.rename_rename]
      rfl
    · intro ρ hρ
      have hn : ¬ ∃ s, pl s = ρ := fun ⟨s, hs⟩ => hρ ⟨s, hs⟩
      have hZ1 : _root_.Formalism.L2.FormalSeriesBounds.grAll pl gr ρ = 1 := by unfold _root_.Formalism.L2.FormalSeriesBounds.grAll; rw [dif_neg hn]
      have hK : _root_.Formalism.L2.FormalSeriesBounds.kindAll pl kind ρ = none := by unfold _root_.Formalism.L2.FormalSeriesBounds.kindAll; rw [dif_neg hn]
      rw [hZ1, hK]
      show MvPowerSeries.rename _ (1 * _root_.Formalism.IncomingBounds.mvExp 0) = 1
      rw [mvExp_zero_eq_one', mul_one, map_one]
    · intro s
      rw [hZ, _root_.Formalism.L2.FormalSeriesBounds.kindAll_pl hpl]
  simp only [valOf_eq_jetAt0_prod_rename_rowSer]
  rw [hT]
  exact _root_.GlobalTheory.JetProd.jetAt0_prod_rename emb hdisj P _

end Rows

end GlobalTheory.JetProd
