import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSpanTprodOfCommuteAtEachPlace
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SpanRangeEqTopOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDefiniteUnitaryInfinitePointOfUnitaryFamil
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIrreducibleSmallRepUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultilinearMemSpanImagePartial
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TrKer

theorem multilinear_mem_span {ι : Type} [Fintype ι] [DecidableEq ι] {M : ι → Type}
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] {N : Type} [AddCommGroup N] [Module ℂ N]
    (Φ : MultilinearMap ℂ M N) (s : ∀ i, Set (M i)) (f : ∀ i, M i)
    (hf : ∀ i, f i ∈ Submodule.span ℂ (s i)) :
    Φ f ∈ Submodule.span ℂ {y | ∃ g : ∀ i, M i, (∀ i, g i ∈ s i) ∧ y = Φ g} := by
  first
  | exact @_root_.GlobalTheory.MultilinearSpanImage.multilinear_apply_mem_span_image
  | exact _root_.GlobalTheory.MultilinearSpanImage.multilinear_apply_mem_span_image
  | (apply _root_.GlobalTheory.MultilinearSpanImage.multilinear_apply_mem_span_image <;> assumption)
  | (intros; apply _root_.GlobalTheory.MultilinearSpanImage.multilinear_apply_mem_span_image <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MultilinearSpanImage.multilinear_apply_mem_span_image <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MultilinearSpanImage.multilinear_apply_mem_span_image ..)

theorem span_smallRep_unitary (n : ℕ) (mu : DomWeight n) :
    Submodule.span ℂ (Set.range (GlobalTheory.Branching.smallRep (GlobalTheory.Branching.unitaryIncl n) mu)) = ⊤ :=
  GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible _ _ _ (GlobalTheory.Branching.isIrreducible_smallRep_unitary n mu)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem span_wInf (lam : InfinitePlace E → DomWeight n) :
    Submodule.span ℂ (Set.range fun k : infU E n => wInf lam k.1) = ⊤ := by
  rw [eq_top_iff]
  rintro Q -
  obtain ⟨z, rfl⟩ := GlobalTheory.PiTensorCommute.mem_range_piTensorHomMap Q
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, PiTensorProduct.piTensorHomMap_tprod_eq_map]
    refine Submodule.smul_mem _ _ ?_
    have h := multilinear_mem_span
      (PiTensorProduct.mapMultilinear ℂ (fun v => nablaSq ℂ n (lam v)) (fun v => nablaSq ℂ n (lam v)))
      (fun v => Set.range (GlobalTheory.Branching.smallRep (GlobalTheory.Branching.unitaryIncl n) (lam v))) f
      (fun v => by rw [span_smallRep_unitary]; trivial)
    refine Submodule.span_le.2 ?_ h
    rintro _ ⟨g, hg, rfl⟩
    choose u hu using hg
    obtain ⟨x, hx, hxc⟩ := GlobalTheory.InfSurj.exists_infU_cAll_eq E n
      (fun v => GlobalTheory.Branching.unitaryIncl n (u v)) (fun v => (u v).2)
    refine Submodule.subset_span ⟨⟨x, hx⟩, ?_⟩
    rw [PiTensorProduct.mapMultilinear_apply]
    change PiTensorProduct.map _ = _
    congr 1
    funext v
    rw [← hu v]
    have h1 := congrFun hxc v
    change cEmb v.embedding x = _ at h1
    change GlobalTheory.Branching.sqRep ℂ n (lam v) (cEmb v.embedding x) = GlobalTheory.Branching.sqRep ℂ n (lam v) _
    rw [h1]
  | add a b ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb

end GlobalTheory.BCT.TrKer

namespace GlobalTheory.BCT.TrKer

theorem Phi_injective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
    ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n)
    (K' : ∀ w : Pl E, Subgroup (UL n w)),
    IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → Function.Injective (Phi S lam K') := by
  intro E _ _ _ _ n _ S _ lam K' _
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  let b := Module.finBasis ℂ (Wsp lam)
  let e := TensorProduct.equivFinsuppOfBasisRight (M := vecM S lam K') b
  have hxe : x = ∑ j, e x j ⊗ₜ b j := by
    conv_lhs => rw [← e.symm_apply_apply x]
    rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply, Finsupp.sum_fintype]
    simp
  have hval : ∀ (x₀ : finU E n) (k : infU E n), ∑ j, (e x j).1 x₀ (wInf lam k.1 (b j)) = 0 := by
    intro x₀ k
    have h := congrFun hx (x₀.1 * k.1)
    have hw : wInf lam (x₀.1 * k.1) = wInf lam k.1 := by rw [map_mul, wInf_fin, one_mul]
    rw [hxe, map_sum] at h
    simpa only [Phi_tmul, phiFun_apply, splitFin_mul, hw, Finset.sum_apply, Pi.zero_apply] using h
  have hall : ∀ (x₀ : finU E n) (T : Module.End ℂ (Wsp lam)), ∑ j, (e x j).1 x₀ (T (b j)) = 0 := by
    intro x₀ T
    let Λ : Module.End ℂ (Wsp lam) →ₗ[ℂ] ℂ :=
      { toFun := fun T => ∑ j, (e x j).1 x₀ (T (b j))
        map_add' := fun T T' => by simp [Finset.sum_add_distrib]
        map_smul' := fun c T => by simp [Finset.mul_sum] }
    have hS : Submodule.span ℂ (Set.range fun k : infU E n => wInf lam k.1) ≤ LinearMap.ker Λ := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact hval x₀ k
    rw [span_wInf] at hS
    exact hS (Submodule.mem_top (x := T))
  have hc : e x = 0 := by
    refine Finsupp.ext fun j => Subtype.ext (funext fun x₀ => LinearMap.ext fun w => ?_)
    have h := hall x₀ ((b.coord j).smulRight w)
    simp [Finsupp.single_apply] at h
    rwa [Finset.sum_eq_single j (fun i _ hi => by simp [hi]) (by simp), if_pos rfl] at h
  exact e.injective (by rw [hc, map_zero])

end GlobalTheory.BCT.TrKer
