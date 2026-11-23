import Formalism.LocalToGlobal.CharacterGerms.MemVarsProdAll
import Formalism.LocalToGlobal.CharacterGerms.ContentZeroAt
import Formalism.LocalToGlobal.CharacterGerms.CartesianBoundOnCurves
import Formalism.LocalToGlobal.CharacterGerms.CoeffIterateZero

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds

section SlopeTestRemainingChoices

variable {C : Type} [Field C] {V : VF C} {d : ℕ}

theorem v_prod (V : VF C) {α : Type} (s : Finset α) (x : α → C) : V.v (∏ o ∈ s, x o) = ∑ o ∈ s, V.v (x o) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, AddValuation.map_mul, ih]

theorem exists_sys_isT {I J : Type} [Fintype I] [Fintype J] (X : Cart V d I J) :
    ∃ (S : Sys X) (t : I → MvPowerSeries I C), S.IsT t := by
  obtain ⟨S, -⟩ := sysExists X (fun c x => if c = x then 1 else 0)
    (by
      intro c x
      split_ifs
      · exact VF.Ge.one
      · exact VF.Ge.zero 0)
    (by
      intro c x h
      rw [if_neg]
      rintro rfl
      exact h rfl)
    (by
      have : (Matrix.of fun c x : I => if c = x then (1 : C) else 0) = 1 := by
        ext c x
        simp [Matrix.one_apply]
      rw [this, Matrix.det_one, V.v.map_one])
  obtain ⟨t, ht, -⟩ := tExistsUnique X S
  exact ⟨S, t, ht⟩

theorem one_mem_intGerm {I : Fin 2 → Type} [∀ g, Fintype (I g)] (t : ∀ g, I g → MvPowerSeries (I g) C) :
    (1 : MvPowerSeries (WV I) C) ∈ IntGerm V t := by
  refine ⟨1, fun μ => ?_, ?_⟩
  · by_cases hμ : μ = 0
    · subst hμ
      simp [VF.Ge]
    · simp [VF.Ge, MvPowerSeries.coeff_one, hμ]
  · rw [← map_one (MvPowerSeries.C (σ := WV I) (R := C)), MvPowerSeries.subst_C]

theorem sum_get {α M : Type} [AddCommMonoid M] (l : List α) (f : α → M) :
    ∑ i : Fin l.length, f (l.get i) = (l.map f).sum := by
  rw [← List.sum_ofFn]
  congr 1
  have h : (fun i : Fin l.length => f (l.get i)) = f ∘ l.get := rfl
  rw [h, ← List.map_ofFn, List.ofFn_get]

end SlopeTestRemainingChoices

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
  (X : ∀ o, RowData C V d (I o) (J o)) (n : ℕ)

def ValO (FFimg : Set (∀ o, MvPolynomial (Fin n × WV (I o)) C)) (ν : ℝ) : Prop :=
  ∀ Po ∈ FFimg, ∀ kind : Orb → Fin n → Knd d, (∀ o, RowsOK (X o).G (X o).Alt (Po o) (kind o)) →
    ∀ (S : ∀ o g, Sys ((X o).G g)) (t : ∀ o g, I o g → MvPowerSeries (I o g) C), (∀ o g, (S o g).IsT (t o g)) →
    ∀ gr : ∀ o, Fin n → MvPowerSeries (WV (I o)) C, (∀ o ρ, gr o ρ ∈ IntGerm V (t o)) →
      (ν : WithTop ℝ) ≤ ∑ o, V.v (ValOf (X o).hL (Po o) (kind o) (gr o))

def plAt {K : Orb → ℕ} {what₂ : ∀ o, Fin (K o) → ℕ} (pl : (Σ o, Σ i : Fin (K o), Fin (what₂ o i)) → Fin n) (o : Orb) :
    (Σ i : Fin (K o), Fin (what₂ o i)) → Fin n := fun s => pl ⟨o, s⟩

theorem plAt_inj {K : Orb → ℕ} {what₂ : ∀ o, Fin (K o) → ℕ} {pl : (Σ o, Σ i : Fin (K o), Fin (what₂ o i)) → Fin n}
    (h : Function.Injective pl) (o : Orb) : Function.Injective (plAt n pl o) := by
  intro s s' hs
  have h1 := h hs
  simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and] at h1
  exact h1

variable {X n}

theorem val_pieces {FFimg : Set (∀ o, MvPolynomial (Fin n × WV (I o)) C)} {ν : ℝ} (hV : ValO X n FFimg ν) (hJ : JetProdSt)
    (K : Orb → ℕ) (what₂ : ∀ o, Fin (K o) → ℕ) (pl : (Σ o, Σ i : Fin (K o), Fin (what₂ o i)) → Fin n)
    (hpl : Function.Injective pl)
    (Pc : ∀ o i, MvPolynomial (Fin (what₂ o i) × WV (I o)) C) (kind : ∀ o i, Fin (what₂ o i) → Knd d)
    (c : ∀ o, Fin (K o) → ℝ)
    (hrow : ∀ o i, RowsOK (X o).G (X o).Alt (Pc o i) (kind o i))
    (hatt : ∀ o i, ∃ (S : ∀ g, Sys ((X o).G g)) (t : ∀ g, I o g → MvPowerSeries (I o g) C),
      (∀ g, (S g).IsT (t g)) ∧ ∃ gr : Fin (what₂ o i) → MvPowerSeries (WV (I o)) C, (∀ ρ, gr ρ ∈ IntGerm V t) ∧
        V.v (ValOf (X o).hL (Pc o i) (kind o i) gr) ≤ ((c o i : ℝ) : WithTop ℝ))
    (hmem : (fun o => prodAll (plAt n pl o) (Pc o)) ∈ FFimg) :
    ν ≤ ∑ o, ∑ i, c o i := by
  choose S₁ t₁ ht₁ gr₁ hg₁ hc₁ using hatt
  have hsys : ∀ o g, ∃ (S : Sys ((X o).G g)) (t : I o g → MvPowerSeries (I o g) C), S.IsT t :=
    fun o g => exists_sys_isT _
  choose S₀ t₀ ht₀ using hsys
  have hG : ∀ o i, IntGerm V (t₁ o i) = IntGerm V (t₀ o) :=
    fun o i => (X o).G0 (S₁ o i) (S₀ o) (t₁ o i) (t₀ o) (ht₁ o i) (ht₀ o)
  have hgr : ∀ o ρ, grAll (plAt n pl o) (gr₁ o) ρ ∈ IntGerm V (t₀ o) := by
    intro o ρ
    unfold grAll
    split_ifs with h
    · rw [← hG o h.choose.1]
      exact hg₁ o _ _
    · exact one_mem_intGerm _
  have h1 := hV _ hmem (fun o => kindAll (plAt n pl o) (kind o))
    (fun o => rowsOK_prodAll _ _ (plAt_inj n hpl o) _ _ (hrow o)) S₀ t₀ ht₀
    (fun o => grAll (plAt n pl o) (gr₁ o)) hgr
  have h2 : ∑ o, V.v (ValOf (X o).hL (prodAll (plAt n pl o) (Pc o)) (kindAll (plAt n pl o) (kind o))
      (grAll (plAt n pl o) (gr₁ o))) = ∑ o, ∑ i, V.v (ValOf (X o).hL (Pc o i) (kind o i) (gr₁ o i)) := by
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [hJ C d (I o) _ n (K o) (what₂ o) (plAt n pl o) (plAt_inj n hpl o) (Pc o) (kind o) (gr₁ o), v_prod]
  have h3 : (ν : WithTop ℝ) ≤ ((∑ o, ∑ i, c o i : ℝ) : WithTop ℝ) := by
    rw [h2] at h1
    refine h1.trans ?_
    push_cast
    exact Finset.sum_le_sum fun o _ => Finset.sum_le_sum fun i _ => hc₁ o i
  exact_mod_cast h3

def GlobalTheory.AttainsOK {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J) (F : Flag X)
    (b : GlobalTheory d) (c : ℝ) : Prop :=
  ∃ kind : Fin (b.what₂ X.n) → Knd d, RowsOK X.G X.Alt (b.poly X F) kind ∧
    ∃ (S : ∀ g, Sys (X.G g)) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) ∧
      ∃ gr : Fin (b.what₂ X.n) → MvPowerSeries (WV I) C, (∀ ρ, gr ρ ∈ IntGerm V t) ∧
        V.v (ValOf X.hL (b.poly X F) kind gr) ≤ ((c : ℝ) : WithTop ℝ)

abbrev blkAt (L : Orb → List (GlobalTheory d × ℝ)) (o : Orb) (i : Fin (L o).length) : GlobalTheory d := ((L o).get i).1

variable (X) in

abbrev rowsAt (L : Orb → List (GlobalTheory d × ℝ)) (o : Orb) (i : Fin (L o).length) : ℕ := (blkAt L o i).what₂ (X o).n

variable (X n) in

def ProdMem (F : ∀ o, Flag (X o)) (FFimg : Set (∀ o, MvPolynomial (Fin n × WV (I o)) C)) (L : Orb → List (GlobalTheory d × ℝ)) : Prop :=
  ∀ pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin n, Function.Injective pl →
    (fun o => prodAll (plAt n pl o) fun i => (blkAt L o i).poly (X o) (F o)) ∈ FFimg

theorem val_lists {FFimg : Set (∀ o, MvPolynomial (Fin n × WV (I o)) C)} {ν : ℝ} (hV : ValO X n FFimg ν) (hJ : JetProdSt)
    (F : ∀ o, Flag (X o)) (L : Orb → List (GlobalTheory d × ℝ))
    (hOK : ∀ o, ∀ q ∈ L o, q.1.AttainsOK (X o) (F o) q.2)
    (hrows : (∑ o, ((L o).map fun q => q.1.what₂ (X o).n).sum) ≤ n) (hmem : ProdMem X n F FFimg L) :
    ν ≤ ∑ o, ((L o).map Prod.snd).sum := by
  have hOK' : ∀ o (i : Fin (L o).length), (blkAt L o i).AttainsOK (X o) (F o) ((L o).get i).2 :=
    fun o i => hOK o _ (List.get_mem _ _)
  have hcard : Fintype.card (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) ≤ Fintype.card (Fin n) := by
    rw [Fintype.card_sigma, Fintype.card_fin]
    refine le_trans (le_of_eq ?_) hrows
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    exact sum_get (L o) fun q => q.1.what₂ (X o).n
  obtain ⟨pl⟩ := Function.Embedding.nonempty_of_card_le hcard
  choose kind hrow hatt' using hOK'
  have key := val_pieces hV hJ (fun o => (L o).length) (fun o i => rowsAt X L o i) pl pl.injective
    (fun o i => (blkAt L o i).poly (X o) (F o)) kind (fun o i => ((L o).get i).2) hrow hatt' (hmem pl pl.injective)
  refine key.trans (le_of_eq ?_)
  exact Finset.sum_congr rfl fun o _ => sum_get (L o) Prod.snd

variable (X n)

def BlockMembership (F : ∀ o, Flag (X o)) (FFimg : Set (∀ o, MvPolynomial (Fin n × WV (I o)) C)) (Z : Finset Orb)
    (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ) : Prop :=
  ∀ L : Orb → List (GlobalTheory d × ℝ), (∀ o, o ∉ Z → L o = []) →
    (∀ o ∈ Z, ∀ g a k, ((L o).map fun q => q.1.wt (X o) g a k).sum = ga o g a k) → ProdMem X n F FFimg L

def BlockAdmissible (F : ∀ o, Flag (X o)) (Z : Finset Orb) (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ) : Prop :=
  ∀ L : Orb → List (GlobalTheory d × ℝ),
    (∀ o ∈ Z, ∀ g a k, ((L o).map fun q => q.1.wt (X o) g a k).sum = ga o g a k) →
    ∀ o ∈ Z, ∀ q ∈ L o, q.1.Attains (X o) (F o) q.2 → q.1.AttainsOK (X o) (F o) q.2

variable {X n}

theorem valBlocks_G {FFimg : Set (∀ o, MvPolynomial (Fin n × WV (I o)) C)} {ν : ℝ} (hV : ValO X n FFimg ν) (hJ : JetProdSt)
    (F : ∀ o, Flag (X o)) (Z : Finset Orb) (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ)
    (hM : BlockMembership X n F FFimg Z ga) (hA : BlockAdmissible X F Z ga) : ValBlocks X F Z n ga ν := by
  intro L hatt hrows hwt
  set L' : Orb → List (GlobalTheory d × ℝ) := fun o => if o ∈ Z then L o else [] with hL'
  have hLZ : ∀ o ∈ Z, L' o = L o := fun o ho => by simp [hL', ho]
  have hLn : ∀ o, o ∉ Z → L' o = [] := fun o ho => by simp [hL', ho]
  have hwt' : ∀ o ∈ Z, ∀ g a k, ((L' o).map fun q => q.1.wt (X o) g a k).sum = ga o g a k := by
    intro o ho g a k
    rw [hLZ o ho]
    exact hwt o ho g a k
  have hOK : ∀ o, ∀ q ∈ L' o, q.1.AttainsOK (X o) (F o) q.2 := by
    intro o q hq
    by_cases ho : o ∈ Z
    · exact hA L' hwt' o ho q hq (hatt o ho q (by rwa [hLZ o ho] at hq))
    · rw [hLn o ho] at hq
      exact absurd hq (by simp)
  have hsum : ∀ f : Orb → List (GlobalTheory d × ℝ) → ℕ, (∀ o, f o [] = 0) → ∑ o, f o (L' o) = ∑ o ∈ Z, f o (L o) := by
    intro f hf
    rw [← Finset.sum_subset (Finset.subset_univ Z)]
    · exact Finset.sum_congr rfl fun o ho => by rw [hLZ o ho]
    · intro o _ ho
      rw [hLn o ho, hf]
  have hsumR : ∑ o, ((L' o).map Prod.snd).sum = ∑ o ∈ Z, ((L o).map Prod.snd).sum := by
    rw [← Finset.sum_subset (Finset.subset_univ Z)]
    · exact Finset.sum_congr rfl fun o ho => by rw [hLZ o ho]
    · intro o _ ho
      rw [hLn o ho]
      simp
  rw [← hsumR]
  refine val_lists hV hJ F L' hOK ?_ (hM L' hLn hwt')
  rw [hsum (fun o l => (l.map fun q => q.1.what₂ (X o).n).sum) (fun o => by simp)]
  exact hrows

end Formalism.L2.FormalSeriesBounds.RF

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds

variable {C : Type} [Field C] {V : VF C}
  {Orb : Type} [Fintype Orb] {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
  (X : ∀ o, RowData C V 2 (I o) (J o)) (n : ℕ)

def BlockMembershipSelfConjugate (F : ∀ o, Flag (X o)) (FFimg : Set (∀ o, MvPolynomial (Fin n × WV (I o)) C))
    (gaC : Orb → ZMod 2 → ℕ → ℕ) : Prop :=
  ∀ L : Orb → List (GlobalTheory 2 × ℝ),
    (∀ o, ∀ q ∈ L o, ∀ g e N, q.1 = GlobalTheory.mon g e N → ∃ s : ZMod 2, ∀ a k, a ≠ s → e a k = 0) →
    (∀ o s k, ((L o).map fun q => q.1.wt (X o) 0 s k + q.1.wt (X o) 1 (s + 1) k).sum = gaC o s k) → ProdMem X n F FFimg L

def BlockAdmissibleSelfConjugate (F : ∀ o, Flag (X o)) (gaC : Orb → ZMod 2 → ℕ → ℕ) : Prop :=
  ∀ L : Orb → List (GlobalTheory 2 × ℝ),
    (∀ o s k, ((L o).map fun q => q.1.wt (X o) 0 s k + q.1.wt (X o) 1 (s + 1) k).sum = gaC o s k) →
    ∀ o, ∀ q ∈ L o, q.1.Attains (X o) (F o) q.2 → q.1.AttainsOK (X o) (F o) q.2

variable {X n}

theorem valBlocksC_G {FFimg : Set (∀ o, MvPolynomial (Fin n × WV (I o)) C)} {ν : ℝ} (hV : ValO X n FFimg ν) (hJ : JetProdSt)
    (F : ∀ o, Flag (X o)) (nW : ℕ) (hn : nW ≤ 2 * n + 1) (gaC : Orb → ZMod 2 → ℕ → ℕ)
    (hM : BlockMembershipSelfConjugate X n F FFimg gaC) (hA : BlockAdmissibleSelfConjugate X F gaC) : ValBlocksC X F nW gaC ν := by
  intro L hatt hmon hrows hwt
  exact val_lists hV hJ F L (fun o q hq => hA L hwt o q hq (hatt o q hq)) (by omega) (hM L hmon hwt)

end Formalism.L2.FormalSeriesBounds.RF
