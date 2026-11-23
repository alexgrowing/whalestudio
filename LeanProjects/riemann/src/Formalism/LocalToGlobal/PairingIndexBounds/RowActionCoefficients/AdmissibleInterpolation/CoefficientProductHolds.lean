import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.CoefProd

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.L2.G.Model.TS

section disjointProducts

variable {R B σ τ : Type*} [CommRing R] [Fintype B]

def dGlue (em : B → σ → τ) (p : B → σ →₀ ℕ) : τ →₀ ℕ :=
  ∑ b, (p b).mapDomain (em b)

lemma dGlue_apply (em : B → σ → τ) (hem : Function.Injective fun x : B × σ => em x.1 x.2)
    (p : B → σ →₀ ℕ) (b : B) (s : σ) : dGlue em p (em b s) = p b s := by
  classical
  unfold dGlue
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single b]
  · exact Finsupp.mapDomain_apply (fun x y h => congrArg Prod.snd (hem (a₁ := (b, x)) (a₂ := (b, y)) h)) _ _
  · intro b' _ hb
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨w, hw⟩
    exact hb (congrArg Prod.fst (hem (a₁ := (b', w)) (a₂ := (b, s)) hw))
  · simp

lemma dGlue_injective (em : B → σ → τ) (hem : Function.Injective fun x : B × σ => em x.1 x.2) :
    Function.Injective (dGlue em) := fun p q h =>
  funext fun b => Finsupp.ext fun s => by rw [← dGlue_apply em hem p, h, dGlue_apply em hem]

lemma dGlue_fact (em : B → σ → τ) (hem : Function.Injective fun x : B × σ => em x.1 x.2)
    (p : B → σ →₀ ℕ) :
    ∏ x ∈ (dGlue em p).support, (dGlue em p x).factorial = ∏ b, ∏ v ∈ (p b).support, (p b v).factorial := by
  classical
  have key : ∀ t : Finset B, (∑ b ∈ t, (p b).mapDomain (em b)).prod (fun _ k => k.factorial) =
      ∏ b ∈ t, (p b).prod (fun _ k => k.factorial) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t ha ih =>
      have hinj : Function.Injective (em a) := fun x y h =>
        congrArg Prod.snd (hem (a₁ := (a, x)) (a₂ := (a, y)) h)
      have hd : Disjoint ((p a).mapDomain (em a)).support (∑ b ∈ t, (p b).mapDomain (em b)).support := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        rw [Finsupp.mem_support_iff] at hx1 hx2
        obtain ⟨s, rfl⟩ := Finsupp.mem_range_of_mapDomain_ne_zero hx1
        apply hx2
        rw [Finsupp.finsetSum_apply]
        refine Finset.sum_eq_zero fun b hb => ?_
        apply Finsupp.mapDomain_of_notMem_range
        rintro ⟨w, hw⟩
        have hba : b = a := congrArg Prod.fst (hem (a₁ := (b, w)) (a₂ := (a, s)) hw)
        exact ha (hba ▸ hb)
      rw [Finset.sum_insert ha, Finset.prod_insert ha, Finsupp.prod_add_index_of_disjoint hd, ih,
        Finsupp.prod_mapDomain_index_inj hinj]
  exact key Finset.univ

lemma rename_prod_expand [DecidableEq B] (em : B → σ → τ) (F : B → MvPolynomial σ R) :
    ∏ b, rename (em b) (F b) = ∑ p ∈ Fintype.piFinset (fun b => (F b).support),
      monomial (dGlue em p) (∏ b, coeff (p b) (F b)) := by
  calc ∏ b, rename (em b) (F b)
      = ∏ b, ∑ m ∈ (F b).support, rename (em b) (monomial m (coeff m (F b))) := by
        refine Finset.prod_congr rfl fun b _ => ?_
        conv_lhs => rw [(F b).as_sum]
        rw [map_sum]
    _ = ∑ p ∈ Fintype.piFinset (fun b => (F b).support),
          ∏ b, rename (em b) (monomial (p b) (coeff (p b) (F b))) := Finset.prod_univ_sum _ _
    _ = _ := Finset.sum_congr rfl fun p _ => by
        simp only [rename_monomial]
        exact prod_monomial_eq _ _ _

end disjointProducts

theorem fock_product_holds : FockProd := by
  intro K B σ τ _ _ em hem F G
  classical
  rw [rename_prod_expand em F, rename_prod_expand em G, fockR_sum_left]
  simp_rw [fockR_sum_right, fockR_expand (F _) (G _)]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp_rw [fockR_monomial]
  by_cases h : p = q
  · subst h
    simp only [if_true, dGlue_fact em hem, Finset.prod_mul_distrib, Nat.cast_prod]
  · have h' : dGlue em p ≠ dGlue em q := fun e => h (dGlue_injective em hem e)
    rw [if_neg h']
    obtain ⟨s, hs⟩ := Function.ne_iff.mp h
    exact (Finset.prod_eq_zero (Finset.mem_univ s) (if_neg hs)).symm

theorem coefficient_product_holds : CoefProd := by
  intro R B σ τ _ _ xm hxm H p
  classical
  rw [show (∑ b, (p b).mapDomain (xm b)) = dGlue xm p from rfl, rename_prod_expand xm H, coeff_sum]
  by_cases hp : p ∈ Fintype.piFinset fun b => (H b).support
  · rw [Finset.sum_eq_single p]
    · rw [coeff_monomial, if_pos rfl]
    · intro q _ hq
      rw [coeff_monomial, if_neg (fun e => hq (dGlue_injective xm hxm e))]
    · intro h; exact absurd hp h
  · rw [Finset.sum_eq_zero]
    · rw [Fintype.mem_piFinset] at hp
      push Not at hp
      obtain ⟨b, hb⟩ := hp
      exact (Finset.prod_eq_zero (Finset.mem_univ b) (notMem_support_iff.mp hb)).symm
    · intro q hq
      rw [coeff_monomial, if_neg]
      intro e
      exact hp (dGlue_injective xm hxm e ▸ hq)

end Formalism.L2.PairingIndexBounds.Ent
