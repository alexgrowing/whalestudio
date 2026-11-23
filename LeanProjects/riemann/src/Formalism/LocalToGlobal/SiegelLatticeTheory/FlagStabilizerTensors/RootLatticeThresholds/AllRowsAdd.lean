import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsEtAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RhoSurjPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsTr
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowsGoodRed
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsRedKer
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsRMul

noncomputable section

open MonoidAlgebra MeasureTheory
open scoped InnerProductSpace

namespace Formalism.L2.SG.Pf.AllRowsAdd

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.SG.HidaSetting Formalism.L2.SG.AllRowsOf Formalism.L2.SG.Pf.AllRowsGA
  Formalism.L2.SG.Pf.AllRowsFin Formalism.L2.SG.Pf.AllRowsRhoX Formalism.L2.SG.Pf.AllRowsES Formalism.L2.SG.Pf.AllRowsTr
  Formalism.L2.SG.Pf.AllRowsEtAlg

variable {D : D7}

instance instFactG' (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

open Classical in

theorem ES_inter (S S' : Set (Tup2 D)) : ES S * ES S' = ES (S ∩ S') := by
  rw [ES_eq, ES_eq, ES_eq, Finset.sum_mul_sum]
  simp only [Ea_mul]
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_ite_eq _ _ _, ← Finset.sum_filter]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_inter_iff]

theorem Ea_zero (a : CV D) (h : tupOf a ∉ labT (D := D)) : Ea a = 0 := by
  classical
  have : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  have : ∃ kv : (Σ k : Fin 2, D.nd.PlG k), ¬ IsLabel D kv.1 (Formalism.CyclotomicNorms.monicOf (a kv)) := by
    by_contra hc
    push Not at hc
    apply h
    unfold labT
    refine Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩, fun k v => hc ⟨k, v⟩⟩
  obtain ⟨kv, hkv⟩ := this
  have h0 : D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv)) = 0 := D.ntypes.eSer_zero _ _ hkv
  apply MonoidAlgebra.ext; ext γ
  rw [Ea_coeff, Finset.prod_eq_zero (Finset.mem_univ kv) (by rw [h0]; rfl)]
  rfl

open Classical in

theorem ES_split (S : Set (Tup2 D)) : ES S = ∑ t ∈ (labT (D := D)).filter (· ∈ S), ES {t} := by
  simp only [ES_eq]
  have e1 : ∑ a ∈ Finset.univ.filter (fun a : CV D => tupOf a ∈ S), Ea a =
      ∑ a ∈ Finset.univ.filter (fun a : CV D => tupOf a ∈ S ∧ tupOf a ∈ labT (D := D)), Ea a := by
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h1 : tupOf a ∈ S
    · by_cases h2 : tupOf a ∈ labT (D := D)
      · rw [if_pos h1, if_pos ⟨h1, h2⟩]
      · rw [if_pos h1, if_neg (fun h => h2 h.2), Ea_zero a h2]
    · rw [if_neg h1, if_neg (fun h => h1 h.1)]
  rw [e1, ← Finset.sum_fiberwise_of_maps_to (g := tupOf) (t := (labT (D := D)).filter (· ∈ S)) (fun a ha => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact ⟨ha.2, ha.1⟩)]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.filter_filter]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_singleton_iff]
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h; rw [Finset.mem_filter] at ht; exact ⟨⟨h ▸ ht.2, h ▸ ht.1⟩, h⟩

section Fin

variable {X : HidaSetting D} (hS : Function.Surjective (rhoX X))
include hS

theorem eT_inter (S S' : Set (Tup2 D)) : X.B.I.convF X.B.μf (eT X S) (eT X S') = eT X (S ∩ S') := by
  refine hat_inj hS (biInv_conv hS (biInv_eT X S) (biInv_eT X S')) (biInv_eT X _) fun γ => ?_
  rw [conv_hat hS (biInv_eT X S) (biInv_eT X S'), hat_eT' hS]
  simp only [hat_eT' hS]
  rw [← coeff_mul_fin]
  have key : (Ehat hS * ES S) * (Ehat hS * ES S') = Ehat hS * ES (S ∩ S') := by
    calc (Ehat hS * ES S) * (Ehat hS * ES S') = Ehat hS * (ES S * Ehat hS) * ES S' := by noncomm_ring
      _ = Ehat hS * (Ehat hS * ES S) * ES S' := by rw [ES_central]
      _ = (Ehat hS * Ehat hS) * (ES S * ES S') := by noncomm_ring
      _ = Ehat hS * ES (S ∩ S') := by rw [Ehat_idem, ES_inter]
  rw [key]

omit hS in
theorem biInv_sum {ι : Type} (F : Finset ι) (f : ι → X.B.I.Gf → ℂ) (h : ∀ i, BiInv X (f i)) :
    BiInv X (fun x => ∑ i ∈ F, f i x) := by
  refine ⟨fun x hx => ?_, fun x n hn => ?_, fun x n hn => ?_⟩
  · obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
    exact (h i).1 x hi
  · exact Finset.sum_congr rfl fun i _ => (h i).2.1 x n hn
  · exact Finset.sum_congr rfl fun i _ => (h i).2.2 x n hn

theorem hat_sum {ι : Type} (F : Finset ι) (f : ι → X.B.I.Gf → ℂ) (γ : G0g D.nd) :
    hat hS (fun x => ∑ i ∈ F, f i x) γ = ∑ i ∈ F, hat hS (f i) γ := by
  unfold hat; rw [Finset.mul_sum]

open Classical in

theorem eT_split (S : Set (Tup2 D)) :
    eT X S = fun x => ∑ t ∈ (labT (D := D)).filter (· ∈ S), eT X {t} x := by
  refine hat_inj hS (biInv_eT X S) (biInv_sum _ _ fun t => biInv_eT X {t}) fun γ => ?_
  rw [hat_sum, hat_eT' hS, ES_split, Finset.mul_sum, MonoidAlgebra.coeff_sum, Finset.sum_apply']
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [hat_eT' hS]

end Fin

section Ops

variable (X : HidaSetting D)

theorem hS_X : Function.Surjective (rhoX X) := Formalism.L2.SG.Pf.RhoSurjW.reduction_map_surjective D X

theorem egA_conv_eT (S S' : Set (Tup2 D)) :
    X.B.I.convF X.B.μf (egA X (ES S')) (eT X S) = eT X (S' ∩ S) := by
  have hS := hS_X X
  refine hat_inj hS (biInv_conv hS (biInv_egA X _ (ES_conj S')) (biInv_eT X S)) (biInv_eT X _) fun γ => ?_
  rw [conv_hat hS (biInv_egA X _ (ES_conj S')) (biInv_eT X S), hat_eT' hS]
  simp only [hat_egA hS _ (ES_conj S'), hat_eT' hS]
  rw [← coeff_mul_fin]
  have key : ES S' * (Ehat hS * ES S) = Ehat hS * ES (S' ∩ S) := by
    rw [← mul_assoc, ES_central, mul_assoc, ES_inter]
  rw [key]

theorem reT_inter (S S' : Set (Tup2 D)) : (ReT X S).comp (ReT X S') = ReT X (S ∩ S') := by
  have h := Formalism.L2.SG.Pf.AllRowsRMul.isRConvF_conv X (reT_spec X (etInt_holds X) S) (reT_spec X (etInt_holds X) S')
  rw [eT_inter (hS_X X) S S'] at h
  exact isRConvF_unique X h (reT_spec X (etInt_holds X) (S ∩ S'))

theorem etConv_holds : Formalism.L2.SG.Pf.RowsGoodRed.EtConv X := fun S S' φ => by
  rw [← ContinuousLinearMap.comp_apply, reT_inter]

theorem etSA_holds : Formalism.L2.SG.Pf.RowsGoodRed.EtSA X := fun S x => by
  rw [eT_inv (hS_X X) S x, star_star]

theorem projT_holds (G : Formalism.L2.SG.RowDict.GoodOp X) : Formalism.L2.SG.Pf.RowsGoodRed.ProjT X G :=
  Formalism.L2.SG.Pf.RowsGoodRed.projT_of X G (etConv_holds X) (Formalism.L2.SG.Pf.RowsGoodRed.etEmpty X)
    (Formalism.L2.SG.Pf.RowsGoodRed.etAdj_of X (etSA_holds X)) (Formalism.L2.SG.Pf.RowsGoodRed.etGood_of X G (egA_conv_eT X))

end Ops

section Split

variable (X : HidaSetting D)

theorem isRConvF_sum {ι : Type} (F : Finset ι) (f : ι → X.B.I.Gf → ℂ)
    (T : ι → (X.B.I.L2 X.B.μf X.B.fund →L[ℂ] X.B.I.L2 X.B.μf X.B.fund))
    (h : ∀ i, X.B.I.IsRConvF X.B.μf X.B.fund X.B.R (f i) (T i)) :
    X.B.I.IsRConvF X.B.μf X.B.fund X.B.R (fun x => ∑ i ∈ F, f i x) (∑ i ∈ F, T i) := by
  obtain ⟨-, -, hmeas⟩ := Formalism.L2.SG.Pf.AllRowsRMul.R_facts X
  refine ⟨integrable_finsetSum _ fun i _ => (h i).1, fun x y => ?_⟩
  rw [ContinuousLinearMap.sum_apply, inner_sum]
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ fun i _ => (h i).1.mul_bdd ((hmeas x y).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun c => Formalism.L2.SG.Pf.AllRowsRMul.phi_bound X x y c)]
  exact Finset.sum_congr rfl fun i _ => (h i).2 x y

open Classical in

theorem reT_split (S : Set (Tup2 D)) : ReT X S = ∑ t ∈ (labT (D := D)).filter (· ∈ S), ReT X {t} := by
  have h := isRConvF_sum X ((labT (D := D)).filter (· ∈ S)) (fun t => eT X {t}) (fun t => ReT X {t})
    (fun t => reT_spec X (etInt_holds X) {t})
  rw [← eT_split (hS_X X) S] at h
  exact isRConvF_unique X (reT_spec X (etInt_holds X) S) h

theorem reT_orth (t t' : Tup2 D) :
    (ReT X {t}).comp (ReT X {t'}) = if t = t' then ReT X {t} else 0 := by
  rw [reT_inter]
  split_ifs with h
  · rw [h, Set.inter_self]
  · have e : ({t} : Set (Tup2 D)) ∩ {t'} = ∅ := by
      ext u; simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      rintro ⟨rfl, rfl⟩; exact h rfl
    rw [e]
    exact ContinuousLinearMap.ext fun φ => Formalism.L2.SG.Pf.RowsGoodRed.etEmpty X φ

end Split

section LA

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (W : Submodule ℂ V)

theorem finrank_map_sum {ι : Type} [DecidableEq ι] (Q : ι → V →ₗ[ℂ] V) :
    ∀ (F : Finset ι), (∀ i ∈ F, ∀ j ∈ F, Q i ∘ₗ Q j = if i = j then Q i else 0) →
      (∀ i ∈ F, ∀ x ∈ W, Q i x ∈ W) →
      (∀ G ⊆ F, FiniteDimensional ℂ (W.map (∑ i ∈ G, Q i))) →
      Module.finrank ℂ (W.map (∑ i ∈ F, Q i)) = ∑ i ∈ F, Module.finrank ℂ (W.map (Q i)) := by
  intro F
  induction F using Finset.induction_on with
  | empty => intro _ _ _; rw [Finset.sum_empty, Finset.sum_empty, Submodule.map_zero, finrank_bot]
  | insert t F ht ih =>
    intro hQ hW hfin
    have hQ' : ∀ i ∈ F, ∀ j ∈ F, Q i ∘ₗ Q j = if i = j then Q i else 0 := fun i hi j hj =>
      hQ i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)
    have hW' : ∀ i ∈ F, ∀ x ∈ W, Q i x ∈ W := fun i hi => hW i (Finset.mem_insert_of_mem hi)
    have hfin' : ∀ G ⊆ F, FiniteDimensional ℂ (W.map (∑ i ∈ G, Q i)) := fun G hG =>
      hfin G (hG.trans (Finset.subset_insert _ _))
    rw [Finset.sum_insert ht, Finset.sum_insert ht, ← ih hQ' hW' hfin']
    set QF := ∑ i ∈ F, Q i with hQF
    have htt : ∀ x, Q t (Q t x) = Q t x := fun x => by
      have := congrArg (fun L : V →ₗ[ℂ] V => L x) (hQ t (Finset.mem_insert_self t F) t (Finset.mem_insert_self t F))
      simpa using this
    have htF : ∀ x, Q t (QF x) = 0 := fun x => by
      rw [hQF, LinearMap.sum_apply, map_sum]
      refine Finset.sum_eq_zero fun i hi => ?_
      have := congrArg (fun L : V →ₗ[ℂ] V => L x)
        (hQ t (Finset.mem_insert_self t F) i (Finset.mem_insert_of_mem hi))
      simp only [LinearMap.comp_apply] at this
      rw [this, if_neg (fun (h : t = i) => ht (h ▸ hi))]
      rfl
    have hFt : ∀ x, QF (Q t x) = 0 := fun x => by
      rw [hQF, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i hi => ?_
      have := congrArg (fun L : V →ₗ[ℂ] V => L x)
        (hQ i (Finset.mem_insert_of_mem hi) t (Finset.mem_insert_self t F))
      simp only [LinearMap.comp_apply] at this
      rw [this, if_neg (fun (h : i = t) => ht (h ▸ hi))]
      rfl
    have hFF : ∀ x, QF (QF x) = QF x := fun x => by
      rw [hQF]
      simp only [LinearMap.sum_apply, map_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.sum_eq_single i]
      · have := congrArg (fun L : V →ₗ[ℂ] V => L x) (hQ' i hi i hi)
        simpa using this
      · intro j hj hji
        have := congrArg (fun L : V →ₗ[ℂ] V => L x) (hQ' j hj i hi)
        simp only [LinearMap.comp_apply] at this
        rw [this, if_neg hji]; rfl
      · intro h; exact absurd hi h
    have hWF : ∀ x ∈ W, QF x ∈ W := fun x hx => by
      rw [hQF, LinearMap.sum_apply]; exact Submodule.sum_mem _ fun i hi => hW' i hi x hx
    have hC : W.map (Q t + QF) = W.map (Q t) ⊔ W.map QF := by
      apply le_antisymm
      · rintro _ ⟨w, hw, rfl⟩
        exact Submodule.add_mem_sup ⟨w, hw, rfl⟩ ⟨w, hw, rfl⟩
      · refine sup_le ?_ ?_
        · rintro _ ⟨w, hw, rfl⟩
          refine ⟨Q t w, hW t (Finset.mem_insert_self t F) w hw, ?_⟩
          simp only [LinearMap.add_apply, htt, hFt, add_zero]
        · rintro _ ⟨w, hw, rfl⟩
          refine ⟨QF w, hWF w hw, ?_⟩
          simp only [LinearMap.add_apply, htF, hFF, zero_add]
    have hdis : W.map (Q t) ⊓ W.map QF = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨⟨w, _, rfl⟩, ⟨w', _, hw'⟩⟩
      have h1 : Q t (Q t w) = Q t w := htt w
      have h2 : Q t (Q t w) = 0 := by rw [← hw', htF]
      rw [Submodule.mem_bot, ← h1, h2]
    have hfA : FiniteDimensional ℂ (W.map (Q t)) := by
      have := hfin {t} (Finset.singleton_subset_iff.2 (Finset.mem_insert_self t F))
      rwa [Finset.sum_singleton] at this
    have hfB : FiniteDimensional ℂ (W.map QF) := hfin' F (Finset.Subset.refl _)
    have := Submodule.finrank_sup_add_finrank_inf_eq (W.map (Q t)) (W.map QF)
    rw [hdis, finrank_bot, add_zero] at this
    rw [hC, this]

end LA

section Add

variable (X : HidaSetting D)

theorem reT_comm (S : Set (Tup2 D)) (g : X.B.I.Ginf) :
    (ReT X S).comp (X.B.R (g, 1)) = (X.B.R (g, 1)).comp (ReT X S) := by
  obtain ⟨hmul, -, -⟩ := Formalism.L2.SG.Pf.AllRowsRMul.R_facts X
  have hT := reT_spec X (etInt_holds X) S
  refine ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun x => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hT.2,
    ← ContinuousLinearMap.adjoint_inner_left, hT.2]
  congr 1
  funext a
  rw [ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply,
    ← hmul, ← hmul, Prod.mk_mul_mk, Prod.mk_mul_mk, one_mul, mul_one, one_mul, mul_one]

theorem reT_univ' : ReT X Set.univ = X.B.Re :=
  reT_univ X (etUniv_of X (redKer_of X (redKerOne_of X (Formalism.L2.SG.Pf.AllRowsRedKer.redKerP_holds X 0)
    (Formalism.L2.SG.Pf.AllRowsRedKer.redKerP_holds X 1)))) (etInt_holds X)

open Classical in

theorem rowsAdd_of (hFD : FiniteDimensional ℂ (X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re)) : RowsAdd X := by
  intro S
  set W := X.B.I.HomS X.B.σs X.B.μf X.B.fund X.B.R
  let Q : Tup2 D → ((X.B.Hs →L[ℂ] X.B.I.L2 X.B.μf X.B.fund) →ₗ[ℂ] (X.B.Hs →L[ℂ] X.B.I.L2 X.B.μf X.B.fund)) :=
    fun t => (ContinuousLinearMap.compL ℂ X.B.Hs _ _ (ReT X {t}) : _ →ₗ[ℂ] _)
  have hQapp : ∀ t A, Q t A = (ReT X {t}).comp A := fun t A => rfl
  have hsumQ : ∀ G : Finset (Tup2 D), (∑ t ∈ G, Q t) =
      (ContinuousLinearMap.compL ℂ X.B.Hs _ _ (∑ t ∈ G, ReT X {t}) : _ →ₗ[ℂ] _) := by
    intro G
    apply LinearMap.ext
    intro A
    rw [LinearMap.sum_apply]
    simp only [hQapp]
    show ∑ t ∈ G, (ReT X {t}).comp A = (∑ t ∈ G, ReT X {t}).comp A
    ext y
    simp
  have hQQ : ∀ i ∈ labT (D := D), ∀ j ∈ labT (D := D), Q i ∘ₗ Q j = if i = j then Q i else 0 := by
    intro i _ j _
    apply LinearMap.ext
    intro A
    rw [LinearMap.comp_apply, hQapp, hQapp, ← ContinuousLinearMap.comp_assoc, reT_orth]
    split_ifs
    · rfl
    · simp
  have hWQ : ∀ i ∈ labT (D := D), ∀ A ∈ W, Q i A ∈ W := by
    intro i _ A hA g
    rw [hQapp]
    show ((ReT X {i}).comp A).comp (X.B.σs g) = (X.B.R (g, 1)).comp ((ReT X {i}).comp A)
    rw [ContinuousLinearMap.comp_assoc, hA g, ← ContinuousLinearMap.comp_assoc, reT_comm,
      ContinuousLinearMap.comp_assoc]
  have hfin : ∀ G ⊆ labT (D := D), FiniteDimensional ℂ (W.map (∑ t ∈ G, Q t)) := by
    intro G _
    have := hFD
    let Qe : (X.B.Hs →L[ℂ] X.B.I.L2 X.B.μf X.B.fund) →ₗ[ℂ] (X.B.Hs →L[ℂ] X.B.I.L2 X.B.μf X.B.fund) :=
      (ContinuousLinearMap.compL ℂ X.B.Hs (X.B.I.L2 X.B.μf X.B.fund) (X.B.I.L2 X.B.μf X.B.fund) X.B.Re :
        (X.B.Hs →L[ℂ] X.B.I.L2 X.B.μf X.B.fund) →ₗ[ℂ] (X.B.Hs →L[ℂ] X.B.I.L2 X.B.μf X.B.fund))
    have hcomp : (∑ t ∈ G, Q t) ∘ₗ Qe = ∑ t ∈ G, Q t := by
      apply LinearMap.ext
      intro A
      rw [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [hQapp, hQapp]
      show (ReT X {t}).comp (X.B.Re.comp A) = (ReT X {t}).comp A
      rw [← ContinuousLinearMap.comp_assoc, ← reT_univ' X, reT_inter, Set.inter_univ]
    have e2 : W.map (∑ t ∈ G, Q t) = (X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re).map (∑ t ∈ G, Q t) := by
      unfold AutInst.eHom
      rw [← Submodule.map_comp]
      exact congrArg (fun L => W.map L) hcomp.symm
    rw [e2]
    infer_instance
  have hF := finrank_map_sum W Q ((labT (D := D)).filter (· ∈ S))
    (fun i hi j hj => hQQ i (Finset.mem_of_mem_filter i hi) j (Finset.mem_of_mem_filter j hj))
    (fun i hi => hWQ i (Finset.mem_of_mem_filter i hi))
    (fun G hG => hfin G (hG.trans (Finset.filter_subset _ _)))
  unfold dimX AutInst.Dcount AutInst.eHom
  rw [reT_split X S, ← hsumQ, hF, Finset.sum_filter]

end Add

end Formalism.L2.SG.Pf.AllRowsAdd
