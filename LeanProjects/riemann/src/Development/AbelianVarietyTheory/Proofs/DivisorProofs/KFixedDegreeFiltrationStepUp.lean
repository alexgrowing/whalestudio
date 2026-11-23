import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemDegLE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterPartTensorSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionHomogeneousEigenvectorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineMatrixKroneckerLeftFactorEqZeroOfIsPC

noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.RealLift MvPolynomial

namespace GlobalTheory.KFixIrr.EvenStepTens

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ℕ}

theorem atPl_tprod' (w : ι) (L : Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S)) (f : ι → Formalism.BasicNotions.TH.Pol P Q R S) :
    atPl (V := fun _ : ι => Formalism.BasicNotions.TH.Pol P Q R S) w L (PiTensorProduct.tprod ℂ f) =
      PiTensorProduct.tprod ℂ (Function.update f w (L (f w))) := by
  rw [atPl, PiTensorProduct.map_tprod]
  congr 1
  funext i
  by_cases h : i = w
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem tprod_mem_chi (c : ι → ℚ) (g : ι → Formalism.BasicNotions.TH.Pol P Q R S) (hg : ∀ w, g w ∈ chiOne P Q R S (c w)) :
    PiTensorProduct.tprod ℂ g ∈ chiPart ι P Q R S c := by
  rw [mem_chiPart]
  intro w X hX
  rw [atPl_tprod', (mem_chiOne _ _).1 (hg w) X hX, MultilinearMap.map_update_smul, Function.update_eq_self]

theorem sum_update_le (h : ι → Formalism.BasicNotions.TH.Pol P Q R S) (e : ι → ℕ) (hh : ∀ v, (h v).totalDegree ≤ e v) (w : ι)
    (g' : Formalism.BasicNotions.TH.Pol P Q R S) (k : ℕ) (hg' : g'.totalDegree ≤ k) :
    ∑ v, (Function.update h w g' v).totalDegree ≤ k + ∑ v ∈ Finset.univ.erase w, e v := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ w), Function.update_self]
  have e1 : ∑ v ∈ Finset.univ.erase w, (Function.update h w g' v).totalDegree =
      ∑ v ∈ Finset.univ.erase w, (h v).totalDegree :=
    Finset.sum_congr rfl fun v hv => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hv)]
  rw [e1]
  exact Nat.add_le_add hg' (Finset.sum_le_sum fun v _ => hh v)

end GlobalTheory.KFixIrr.EvenStepTens

namespace GlobalTheory.KFixIrr.EvenStepTens

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ℕ}

abbrev tgt (ι : Type) [Fintype ι] [DecidableEq ι] (P Q R S : ℕ) (c : ι → ℚ) (m : ℕ) :
    Submodule ℂ (⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol P Q R S) :=
  GlobalTheory.KFixIrr.degLE ι P Q R S (m + 1) ⊔ Submodule.span ℂ {T' | ∃ (w : ι) (Z : Formalism.BasicNotions.TH.Mat R S),
               ∃ T₁ ∈ GlobalTheory.KFixIrr.chiPart ι P Q R S c ⊓ GlobalTheory.KFixIrr.degLE ι P Q R S m,
                 T' = GlobalTheory.RealLift.atPl (V := fun _ : ι => Formalism.BasicNotions.TH.Pol P Q R S) w (Formalism.BasicNotions.TH.fockAct2 P Q R S Z) T₁}

theorem plusPart_mem (Z : Mat R S) (hZ : IsPC Z) (k : ℕ) (g : Formalism.BasicNotions.TH.Pol P Q R S)
    (hg : g ∈ homog (Ln P Q R S) k) : plusPart (fockAct2 P Q R S Z) g ∈ homog (Ln P Q R S) (k + 2) := by
  rw [GlobalTheory.FockDeg.fockAct2_eq, GlobalTheory.FockDeg.plusPart_omAct (GlobalTheory.FockDeg.lineMatrixKroneckerRightFactor_eq_zero_of_isPC hZ)]
  exact GlobalTheory.FockDeg.upOp_mem _ k g hg

theorem minusPart_mem (Z : Mat R S) (hZ : IsPC Z) (k : ℕ) (g : Formalism.BasicNotions.TH.Pol P Q R S)
    (hg : g ∈ homog (Ln P Q R S) k) : minusPart (fockAct2 P Q R S Z) g ∈ homog (Ln P Q R S) (k - 2) := by
  rw [GlobalTheory.FockDeg.fockAct2_eq, GlobalTheory.FockDeg.minusPart_omAct (GlobalTheory.FockDeg.lineMatrixKroneckerRightFactor_eq_zero_of_isPC hZ)]
  exact GlobalTheory.FockDeg.downOp_mem _ k g hg

theorem plusPart_eq (Z : Mat R S) (hZ : IsPC Z) (g : Formalism.BasicNotions.TH.Pol P Q R S) :
    plusPart (fockAct2 P Q R S Z) g = fockAct2 P Q R S Z g - minusPart (fockAct2 P Q R S Z) g := by
  rw [eq_sub_iff_add_eq, GlobalTheory.FockDeg.fockAct2_eq]
  exact (GlobalTheory.FockDeg.omAct_eq_parts (GlobalTheory.FockDeg.lineMatrixKroneckerRightFactor_eq_zero_of_isPC hZ) g).symm

end GlobalTheory.KFixIrr.EvenStepTens

namespace GlobalTheory.KFixIrr.EvenStepTens

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ℕ}

theorem key (c : ι → ℚ) (m : ℕ) (d : ι → ℕ) (hd : ∑ w, d w ≤ m) (g₀ : ι → Formalism.BasicNotions.TH.Pol P Q R S)
    (hg₀ : ∀ w, g₀ w ≠ 0 ∧ g₀ w ∈ homog (Ln P Q R S) (d w) ∧ g₀ w ∈ chiOne P Q R S (c w))
    (e : ι → ℕ) (he : ∑ w, e w ≤ m + 2) (h : ι → Formalism.BasicNotions.TH.Pol P Q R S)
    (hh : ∀ w, h w ∈ homog (Ln P Q R S) (e w) ∧ h w ∈ chiOne P Q R S (c w)) :
    PiTensorProduct.tprod ℂ h ∈ tgt ι P Q R S c m := by
  have hdeg : ∀ v, (h v).totalDegree ≤ e v := fun v => (hh v).1.totalDegree_le
  by_cases hs : ∑ w, e w ≤ m + 1
  · exact Submodule.mem_sup_left (tprod_mem_degLE h ((Finset.sum_le_sum fun v _ => hdeg v).trans hs))
  have hlt : ∑ w, d w < ∑ w, e w := by omega
  obtain ⟨w, -, hw⟩ := Finset.exists_lt_of_sum_lt hlt
  have hspan := GlobalTheory.T.fock_action_homogeneous_eigenvector P Q R S (c w) (e w) (d w) (h w) (g₀ w) (hh w).1 ((mem_chiOne _ _).1 (hh w).2)
    (hg₀ w).1 (hg₀ w).2.1 ((mem_chiOne _ _).1 (hg₀ w).2.2) hw
  by_cases he2 : 2 ≤ e w
  · let L := (PiTensorProduct.tprod ℂ (s := fun _ : ι => Formalism.BasicNotions.TH.Pol P Q R S)).toLinearMap h w
    have hL : ∀ v, L v = PiTensorProduct.tprod ℂ (Function.update h w v) := fun v => rfl
    have hsum : e w + ∑ v ∈ Finset.univ.erase w, e v = ∑ v, e v := Finset.add_sum_erase _ _ (Finset.mem_univ w)
    have hle : Submodule.span ℂ {f' | ∃ Z : Formalism.BasicNotions.TH.Mat R S, Formalism.BasicNotions.TH.IsPC Z ∧
        ∃ g' ∈ Formalism.BasicNotions.TH.homog (Formalism.BasicNotions.TH.Ln P Q R S) (e w - 2),
          (∀ Y : Formalism.BasicNotions.TH.Mat P Q, Formalism.BasicNotions.TH.IsKC Y → Formalism.BasicNotions.TH.fockAct1 P Q R S Y g' = ((c w : ℂ) * Y.trace) • g') ∧
          f' = Formalism.BasicNotions.TH.plusPart (Formalism.BasicNotions.TH.fockAct2 P Q R S Z) g'} ≤ (tgt ι P Q R S c m).comap L := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨Z, hZ, g', hg', hchi, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap]
      have hg'd : g'.totalDegree ≤ e w - 2 := (show g'.IsHomogeneous (e w - 2) from hg').totalDegree_le
      rw [plusPart_eq Z hZ, map_sub]
      refine Submodule.sub_mem _ ?_ ?_
      · refine Submodule.mem_sup_right (Submodule.subset_span ⟨w, Z, PiTensorProduct.tprod ℂ (Function.update h w g'),
          ⟨tprod_mem_chi c _ fun v => ?_, tprod_mem_degLE _ ?_⟩, ?_⟩)
        · by_cases hv : v = w
          · subst hv; rw [Function.update_self]; exact (mem_chiOne _ _).2 hchi
          · rw [Function.update_of_ne hv]; exact (hh v).2
        · have := sum_update_le h e hdeg w g' (e w - 2) hg'd
          omega
        · rw [hL, atPl_tprod', Function.update_idem, Function.update_self]
      · refine Submodule.mem_sup_left ?_
        rw [hL]
        refine tprod_mem_degLE _ ?_
        have hm := minusPart_mem Z hZ (e w - 2) g' hg'
        have hmd : (minusPart (fockAct2 P Q R S Z) g').totalDegree ≤ e w - 2 :=
          ((show (minusPart (fockAct2 P Q R S Z) g').IsHomogeneous (e w - 2 - 2) from hm).totalDegree_le).trans
            (Nat.sub_le _ _)
        have := sum_update_le h e hdeg w _ (e w - 2) hmd
        omega
    have := hle hspan
    rw [Submodule.mem_comap, hL, Function.update_eq_self] at this
    exact this
  · have hle : Submodule.span ℂ {f' | ∃ Z : Formalism.BasicNotions.TH.Mat R S, Formalism.BasicNotions.TH.IsPC Z ∧
        ∃ g' ∈ Formalism.BasicNotions.TH.homog (Formalism.BasicNotions.TH.Ln P Q R S) (e w - 2),
          (∀ Y : Formalism.BasicNotions.TH.Mat P Q, Formalism.BasicNotions.TH.IsKC Y → Formalism.BasicNotions.TH.fockAct1 P Q R S Y g' = ((c w : ℂ) * Y.trace) • g') ∧
          f' = Formalism.BasicNotions.TH.plusPart (Formalism.BasicNotions.TH.fockAct2 P Q R S Z) g'} ≤ homog (Ln P Q R S) 2 := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨Z, hZ, g', hg', -, rfl⟩
      have := plusPart_mem Z hZ (e w - 2) g' hg'
      rwa [show e w - 2 + 2 = 2 by omega] at this
    have h0 : h w = 0 := by
      by_contra hne
      have := MvPolynomial.IsHomogeneous.inj_right (show (h w).IsHomogeneous 2 from hle hspan)
        (show (h w).IsHomogeneous (e w) from (hh w).1) hne
      omega
    rw [MultilinearMap.map_coord_zero _ w h0]
    exact Submodule.zero_mem _

end GlobalTheory.KFixIrr.EvenStepTens

namespace GlobalTheory.KFixIrr.EvenStepTens

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ℕ}

theorem pure (c : ι → ℚ) (m : ℕ) (d : ι → ℕ) (hd : ∑ w, d w ≤ m) (g₀ : ι → Formalism.BasicNotions.TH.Pol P Q R S)
    (hg₀ : ∀ w, g₀ w ≠ 0 ∧ g₀ w ∈ homog (Ln P Q R S) (d w) ∧ g₀ w ∈ chiOne P Q R S (c w))
    (g : ι → Formalism.BasicNotions.TH.Pol P Q R S) (hg : ∀ w, g w ∈ chiOne P Q R S (c w))
    (hgd : ∑ w, (g w).totalDegree ≤ m + 2) :
    PiTensorProduct.tprod ℂ g ∈ tgt ι P Q R S c m := by
  have e : PiTensorProduct.tprod ℂ g = PiTensorProduct.tprod ℂ
      (fun w => ∑ n ∈ Finset.range ((g w).totalDegree + 1), homogeneousComponent n (g w)) := by
    congr 1; funext w; exact (sum_homogeneousComponent (g w)).symm
  rw [e, MultilinearMap.map_sum_finset]
  refine Submodule.sum_mem _ fun r hr => ?_
  rw [Fintype.mem_piFinset] at hr
  refine key c m d hd g₀ hg₀ r ((Finset.sum_le_sum fun w _ => ?_).trans hgd) _ fun w =>
    ⟨homogeneousComponent_mem _ _, TensProj.homogeneousComponent_mem_chiOne _ _ (hg w) _⟩
  have := hr w
  rw [Finset.mem_range] at this
  omega

theorem witness (c : ι → ℚ) (m : ℕ) (T₀ : ⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol P Q R S) (h0 : T₀ ≠ 0)
    (hT₀ : T₀ ∈ chiPart ι P Q R S c ⊓ degLE ι P Q R S m) :
    ∃ d : ι → ℕ, ∑ w, d w ≤ m ∧ ∃ g₀ : ι → Formalism.BasicNotions.TH.Pol P Q R S,
      ∀ w, g₀ w ≠ 0 ∧ g₀ w ∈ homog (Ln P Q R S) (d w) ∧ g₀ w ∈ chiOne P Q R S (c w) := by
  by_contra hne
  apply h0
  have hspan := mem_span_tprod_chiOne ι P Q R S c m T₀ hT₀
  have hle : Submodule.span ℂ {U | ∃ g : ι → Formalism.BasicNotions.TH.Pol P Q R S, (∀ w, g w ∈ GlobalTheory.KFixIrr.chiOne P Q R S (c w)) ∧
      ∑ w, (g w).totalDegree ≤ m ∧ U = PiTensorProduct.tprod ℂ g} ≤ ⊥ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, hg, hgd, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_bot]
    by_contra hU
    have hgw : ∀ w, g w ≠ 0 := fun w hw => hU (MultilinearMap.map_coord_zero _ w hw)
    have hn : ∀ w, ∃ n, n ≤ (g w).totalDegree ∧ homogeneousComponent n (g w) ≠ 0 := by
      intro w
      by_contra hc
      push_neg at hc
      apply hgw w
      rw [← sum_homogeneousComponent (g w)]
      exact Finset.sum_eq_zero fun n hn => hc n (by rw [Finset.mem_range] at hn; omega)
    choose n hnd hn0 using hn
    exact hne ⟨n, (Finset.sum_le_sum fun w _ => hnd w).trans hgd, fun w => homogeneousComponent (n w) (g w),
      fun w => ⟨hn0 w, homogeneousComponent_mem _ _, TensProj.homogeneousComponent_mem_chiOne _ _ (hg w) _⟩⟩
  exact (Submodule.mem_bot ℂ).1 (hle hspan)

end GlobalTheory.KFixIrr.EvenStepTens

namespace GlobalTheory.KFixIrr

theorem evenStep_tens : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P Q R S : ℕ) (c : ι → ℚ) (m : ℕ)
    (T₀ T : ⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol P Q R S), T₀ ≠ 0 →
    T₀ ∈ GlobalTheory.KFixIrr.chiPart ι P Q R S c ⊓ GlobalTheory.KFixIrr.degLE ι P Q R S m →
    T ∈ GlobalTheory.KFixIrr.chiPart ι P Q R S c ⊓ GlobalTheory.KFixIrr.degLE ι P Q R S (m + 2) →
    T ∈ GlobalTheory.KFixIrr.degLE ι P Q R S (m + 1) ⊔ Submodule.span ℂ {T' | ∃ (w : ι) (Z : Formalism.BasicNotions.TH.Mat R S),
      ∃ T₁ ∈ GlobalTheory.KFixIrr.chiPart ι P Q R S c ⊓ GlobalTheory.KFixIrr.degLE ι P Q R S m,
        T' = GlobalTheory.RealLift.atPl (V := fun _ : ι => Formalism.BasicNotions.TH.Pol P Q R S) w (Formalism.BasicNotions.TH.fockAct2 P Q R S Z) T₁} := by
  intro ι _ _ P Q R S c m T₀ T h0 hT₀ hT
  obtain ⟨d, hd, g₀, hg₀⟩ := EvenStepTens.witness c m T₀ h0 hT₀
  have hspan := mem_span_tprod_chiOne ι P Q R S c (m + 2) T hT
  refine (Submodule.span_le.2 ?_ : _ ≤ EvenStepTens.tgt ι P Q R S c m) hspan
  rintro _ ⟨g, hg, hgd, rfl⟩
  exact EvenStepTens.pure c m d hd g₀ hg₀ g hg hgd

end GlobalTheory.KFixIrr
