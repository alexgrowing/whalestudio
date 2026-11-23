import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalComponentDefiniteUnitaryFinitePartEqLocalPo
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.RegVan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem mem_GLint_of_entries {L : Type} [Field L] {k : ℕ} (O : Subring L) (g : GL (Fin k) L)
    (h1 : ∀ i j, g.1 i j ∈ O) (h2 : ∀ i j, g⁻¹.1 i j ∈ O) : g ∈ Formalism.UG.GLint (Fin k) O := by
  have hi : Function.Injective fun A : Matrix (Fin k) (Fin k) O => A.map O.subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.inv_mul

theorem eventually_toSub_mem (x : finU E n) :
    ∀ᶠ w in cofinite, toSub (UL n w) (cLoc w (x : UA E n)) ∈ KL n w := by
  have h : ∀ y : FiniteAdeleRing (𝓞 E) E, ∀ᶠ w in cofinite, pLoc E w y ∈ Formalism.UG.Ov E w := fun y => y.2
  have h1 : ∀ᶠ w in cofinite, ∀ i j, pLoc E w (pFin E (((x : UA E n) : GA E n).val i j)) ∈ Formalism.UG.Ov E w := by
    simp only [Filter.eventually_all]; exact fun i j => h _
  have h2 : ∀ᶠ w in cofinite, ∀ i j, pLoc E w (pFin E ((((x : UA E n) : GA E n))⁻¹.val i j)) ∈ Formalism.UG.Ov E w := by
    simp only [Filter.eventually_all]; exact fun i j => h _
  filter_upwards [h1, h2] with w a b
  have hK : cLoc w (x : UA E n) ∈ GlobalTheory.LFun.KGL w n := by
    refine mem_GLint_of_entries _ _ (fun i j => a i j) (fun i j => ?_)
    rw [← map_inv]
    exact b i j
  unfold toSub
  split_ifs with hU
  · exact Subgroup.mem_subgroupOf.2 hK
  · exact one_mem _

theorem cLoc_finPt_val (w : Pl E) (γ : UE E n) :
    (cLoc w ((finPt γ : finU E n) : UA E n)).val = γ.1.val.map (algebraMap E (w.adicCompletion E)) := by
  rw [FinPtLoc.finPt_eq]
  refine Matrix.ext fun i j => ?_
  change pLoc E w (pFin E ((finGL E n (ratF E n γ.1)).val i j)) = algebraMap E _ (γ.1.val i j)
  rw [FinPtLoc.snd_entry]
  rfl

theorem separable_of_monic_natDegree_le_one {K : Type} [Field K] {p : K[X]} (hm : p.Monic) (hd : p.natDegree ≤ 1) :
    p.Separable := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hd with h | h
  · rw [Polynomial.eq_one_of_monic_natDegree_zero hm h]; exact separable_one
  · rw [Polynomial.Monic.eq_X_add_C hm h]; exact separable_X_add_C _

end GlobalTheory.BCT.RegVan

theorem GlobalTheory.BCT.regvan : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E))
    (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ), IsTest (KL n) K' f → ∀ w ∈ S,
    (∀ y, f w y ≠ 0 → y.1.val.charpoly.Separable) → ∀ (x : finU E n) (γ : UE E n),
    globFn S f (x⁻¹ * finPt γ * x) ≠ 0 → γ.1.val.charpoly.Separable := by
  intro E _ _ _ n S K' f hT w hw hsep x γ hne
  set y : finU E n := x⁻¹ * finPt γ * x with hy
  set g : Pl E → ℂ := fun u => f u (toSub (UL n u) (cLoc u (y : UA E n))) with hg
  have hev : ∀ᶠ u in cofinite, g u = 1 := by
    filter_upwards [RegVan.eventually_toSub_mem y, hT.2] with u a b
    simp only [hg, b]
    rw [Set.indicator_of_mem a]
    rfl
  have hfin : (Function.mulSupport g).Finite := hev
  have hgw : g w ≠ 0 := by
    intro h0
    apply hne
    unfold globFn
    rw [finprod_mem_def]
    refine finprod_eq_zero (S.mulIndicator g) w (by rw [Set.mulIndicator_of_mem hw]; exact h0) ?_
    exact hfin.subset (by rw [Set.mulSupport_mulIndicator]; exact Set.inter_subset_right)
  have hs := hsep _ hgw
  by_cases hmem : cLoc w (y : UA E n) ∈ UL n w
  · rw [show toSub (UL n w) (cLoc w (y : UA E n)) = ⟨_, hmem⟩ from dif_pos hmem] at hs
    change (cLoc w (y : UA E n)).val.charpoly.Separable at hs
    have hyv : (cLoc w (y : UA E n)).val = (cLoc w (x : UA E n))⁻¹.val *
        (cLoc w ((finPt γ : finU E n) : UA E n)).val * (cLoc w (x : UA E n)).val := by
      rw [hy]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, Units.val_mul]
    rw [hyv, Matrix.coe_units_inv, Matrix.charpoly_units_conj', RegVan.cLoc_finPt_val, Matrix.charpoly_map] at hs
    exact (separable_map _).1 hs
  · rw [show toSub (UL n w) (cLoc w (y : UA E n)) = 1 from dif_neg hmem] at hs
    change (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)).charpoly.Separable at hs
    rw [Matrix.charpoly_one, Fintype.card_fin, ← C_1] at hs
    have hn : n ≤ 1 := by
      rcases hs.of_pow' with h | ⟨_, h⟩ | h
      · exact absurd h (not_isUnit_X_sub_C _)
      · omega
      · omega
    exact RegVan.separable_of_monic_natDegree_le_one (Matrix.charpoly_monic _)
      (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; exact hn)
