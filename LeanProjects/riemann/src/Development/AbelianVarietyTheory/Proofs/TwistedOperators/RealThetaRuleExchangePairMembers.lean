import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDualPairSwapSymmetry

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

noncomputable section

namespace GlobalTheory.SwapRule

open MvPolynomial

local notation "FP" => Formalism.BasicNotions.TH.Pol

variable {p q r s : ℕ}

theorem rename_swap_swap (P : FP p q r s) :
    rename Prod.swap (rename Prod.swap P : FP r s p q) = P := by
  rw [rename_rename, Prod.swap_swap_eq, rename_id_apply]

theorem comm_comm' {V1 V2 : Type*} [AddCommGroup V1] [Module ℂ V1] [AddCommGroup V2] [Module ℂ V2]
    (x : V1 ⊗[ℂ] V2) : TensorProduct.comm ℂ V2 V1 (TensorProduct.comm ℂ V1 V2 x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add a b ha hb => simp only [map_add, ha, hb]

theorem comm_map' {V1 V2 W1 W2 : Type*} [AddCommGroup V1] [Module ℂ V1] [AddCommGroup V2] [Module ℂ V2]
    [AddCommGroup W1] [Module ℂ W1] [AddCommGroup W2] [Module ℂ W2]
    (g : V1 →ₗ[ℂ] W1) (h : V2 →ₗ[ℂ] W2) (x : V1 ⊗[ℂ] V2) :
    TensorProduct.comm ℂ W1 W2 (TensorProduct.map g h x) =
      TensorProduct.map h g (TensorProduct.comm ℂ V1 V2 x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add a b ha hb => simp only [map_add, ha, hb]

def tr {V1 V2 : Type*} [AddCommGroup V1] [Module ℂ V1] [AddCommGroup V2] [Module ℂ V2]
    (f : FP r s p q →ₗ[ℂ] V2 ⊗[ℂ] V1) : FP p q r s →ₗ[ℂ] V1 ⊗[ℂ] V2 :=
  (TensorProduct.comm ℂ V2 V1).toLinearMap ∘ₗ f ∘ₗ
    (rename (Prod.swap : Ix p q × Ix r s → Ix r s × Ix p q)).toLinearMap

section Tr
variable {V1 V2 : Type*} [AddCommGroup V1] [Module ℂ V1] [AddCommGroup V2] [Module ℂ V2]

theorem tr_apply (f : FP r s p q →ₗ[ℂ] V2 ⊗[ℂ] V1) (P : FP p q r s) :
    tr f P = TensorProduct.comm ℂ V2 V1 (f (rename Prod.swap P)) := rfl

theorem tr_tr (f : FP r s p q →ₗ[ℂ] V2 ⊗[ℂ] V1) : tr (tr f) = f := by
  refine LinearMap.ext fun P => ?_
  rw [tr_apply, tr_apply, rename_swap_swap, comm_comm']

theorem tr_smul (c : ℂ) (f : FP r s p q →ₗ[ℂ] V2 ⊗[ℂ] V1) : tr (c • f) = c • tr f := by
  refine LinearMap.ext fun P => ?_
  simp [tr_apply]

theorem tr_zero : tr (0 : FP r s p q →ₗ[ℂ] V2 ⊗[ℂ] V1) = 0 := by
  refine LinearMap.ext fun P => ?_
  simp [tr_apply]

theorem tr_eq_zero {f : FP r s p q →ₗ[ℂ] V2 ⊗[ℂ] V1} (h : tr f = 0) : f = 0 := by
  rw [← tr_tr f, h, tr_zero]

end Tr
end GlobalTheory.SwapRule

namespace GlobalTheory.SwapRule

open MvPolynomial

local notation "FP" => Formalism.BasicNotions.TH.Pol

variable {p q r s : ℕ}

theorem intw_tr {T0 : GrpData (p * r + q * s) (p * s + q * r)} {T1 : GrpData p q} {T2 : GrpData r s}
    (F : FockData T0 T1 T2) {T0' : GrpData (r * p + s * q) (r * q + s * p)} {T1' : GrpData r s}
    {T2' : GrpData p q} (F' : FockData T0' T1' T2') (M1 : GKMod p q) (M2 : GKMod r s)
    (f : FP r s p q →ₗ[ℂ] M2.V ⊗[ℂ] M1.V) (hf : Formalism.BasicNotions.TH.IsIntw F' M2 M1 f) :
    Formalism.BasicNotions.TH.IsIntw F M1 M2 (tr f) := by
  refine ⟨fun Z => LinearMap.ext fun P => ?_, fun Z => LinearMap.ext fun P => ?_⟩
  · have h := LinearMap.congr_fun (hf.2 Z) (rename Prod.swap P)
    simp only [FockData.act1, FockData.act2, LinearMap.comp_apply] at h ⊢
    rw [tr_apply, tr_apply, GlobalTheory.FockSwap.rename_fockAct1, h, comm_map']
  · have h := LinearMap.congr_fun (hf.1 Z) (rename Prod.swap P)
    simp only [FockData.act1, FockData.act2, LinearMap.comp_apply] at h ⊢
    rw [tr_apply, tr_apply, GlobalTheory.FockSwap.rename_fockAct2, h, comm_map']

theorem isHW_map {n m : ℕ} {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (act : Mat n m →ₗ[ℂ] Module.End ℂ V) (act' : Mat n m →ₗ[ℂ] Module.End ℂ W) (e : V →ₗ[ℂ] W)
    (he : Function.Injective e) (h : ∀ Z v, e (act Z v) = act' Z (e v)) (μ : Ix n m → ℚ) (v : V)
    (hv : IsHW act μ v) : IsHW act' μ (e v) := by
  obtain ⟨hne, hmem⟩ := hv
  refine ⟨fun h0 => hne (he (by rw [h0, map_zero])), ?_⟩
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hmem ⊢
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · rw [← h, ← map_smul, ← map_sub, hmem.1 a, map_zero]
  · rw [← h, hmem.2 a b hab, map_zero]

theorem fock_inner_sum {T0 : GrpData (p * r + q * s) (p * s + q * r)} {T1 : GrpData p q}
    {T2 : GrpData r s} (F : FockData T0 T1 T2) {ι : Type*} (t : Finset ι) (c : ι → ℂ)
    (m : ι → (Ix p q × Ix r s →₀ ℕ)) (hm : Set.InjOn m t) :
    inner ℂ (F.ι (∑ i ∈ t, c i • monomial (m i) 1)) (F.ι (∑ i ∈ t, c i • monomial (m i) 1)) =
      ∑ i ∈ t, star (c i) * c i * (m i).prod (fun _ k => (k.factorial : ℂ)) := by
  simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right, F.fockIP]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single i]
  · simp only [if_true]; simp [mul_assoc, mul_left_comm]
  · intro j hj hji
    rw [if_neg (fun h => hji (hm hj hi h))]
    simp
  · intro hi'; exact absurd hi hi'

theorem pol_as_sum (P : FP p q r s) : P = ∑ α ∈ P.support, coeff α P • monomial α 1 := by
  conv_lhs => rw [P.as_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [smul_monomial, smul_eq_mul, mul_one]

theorem norm_swap {T0 : GrpData (p * r + q * s) (p * s + q * r)} {T1 : GrpData p q}
    {T2 : GrpData r s} (F : FockData T0 T1 T2) {T0' : GrpData (r * p + s * q) (r * q + s * p)}
    {T1' : GrpData r s} {T2' : GrpData p q} (F' : FockData T0' T1' T2') (Φ : FP r s p q) :
    ‖F.ι (rename Prod.swap Φ)‖ = ‖F'.ι Φ‖ := by
  have h1 : rename Prod.swap Φ = ∑ α ∈ Φ.support, coeff α Φ • monomial (Finsupp.mapDomain Prod.swap α) 1 := by
    conv_lhs => rw [pol_as_sum Φ]
    simp only [map_sum, map_smul, rename_monomial]
  have hinj : Set.InjOn (fun α : Ix r s × Ix p q →₀ ℕ => Finsupp.mapDomain Prod.swap α) Φ.support :=
    fun a _ b _ h => Finsupp.mapDomain_injective Prod.swap_injective h
  have e1 := fock_inner_sum F Φ.support (fun α => coeff α Φ) _ hinj
  have e2 := fock_inner_sum F' Φ.support (fun α => coeff α Φ) id (Set.injOn_id _)
  simp only [id] at e2
  rw [← pol_as_sum Φ] at e2
  rw [← h1] at e1
  have hprod : ∀ α : Ix r s × Ix p q →₀ ℕ, (Finsupp.mapDomain Prod.swap α).prod (fun _ k => (k.factorial : ℂ)) =
      α.prod (fun _ k => (k.factorial : ℂ)) := by
    intro α
    have := Finsupp.prod_equivMapDomain (Equiv.prodComm _ _) α (fun _ k => (k.factorial : ℂ))
    rw [Finsupp.equivMapDomain_eq_mapDomain] at this
    exact this
  simp only [hprod] at e1
  rw [← e2] at e1
  have k1 := inner_self_eq_norm_sq (𝕜 := ℂ) (F.ι (rename Prod.swap Φ))
  have k2 := inner_self_eq_norm_sq (𝕜 := ℂ) (F'.ι Φ)
  rw [e1, k2] at k1
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 k1.symm

end GlobalTheory.SwapRule

namespace GlobalTheory.SwapRule

open MvPolynomial

local notation "FP" => Formalism.BasicNotions.TH.Pol

variable {p q r s : ℕ}

theorem jointHW_swap {T0 : GrpData (p * r + q * s) (p * s + q * r)} {T1 : GrpData p q}
    {T2 : GrpData r s} (F : FockData T0 T1 T2) {T0' : GrpData (r * p + s * q) (r * q + s * p)}
    {T1' : GrpData r s} {T2' : GrpData p q} (F' : FockData T0' T1' T2') (Λ : Ix p q → ℚ)
    (Λ' : Ix r s → ℚ) (Φ : FP r s p q) (h : Formalism.BasicNotions.TH.JointHW F' Λ' Λ Φ) :
    Formalism.BasicNotions.TH.JointHW F Λ Λ' (rename Prod.swap Φ) := by
  obtain ⟨hJ, h1, h2, hn⟩ := h
  have hinj : Function.Injective (rename Prod.swap : FP r s p q →ₐ[ℂ] FP p q r s).toLinearMap :=
    rename_injective _ Prod.swap_injective
  refine ⟨⟨fun Z hZ => ?_, fun Z hZ => ?_⟩, ?_, ?_, ?_⟩
  · simp only [FockData.act1]
    exact (GlobalTheory.FockSwap.minusPart_eq_zero_iff (Equiv.prodComm _ _) (fockAct2 r s p q Z) _
      (GlobalTheory.FockSwap.rename_fockAct2 Z) Φ).1 (hJ.2 Z hZ)
  · simp only [FockData.act2]
    exact (GlobalTheory.FockSwap.minusPart_eq_zero_iff (Equiv.prodComm _ _) (fockAct1 r s p q Z) _
      (GlobalTheory.FockSwap.rename_fockAct1 Z) Φ).1 (hJ.1 Z hZ)
  · exact isHW_map F'.act2 F.act1 _ hinj (fun Z v => GlobalTheory.FockSwap.rename_fockAct2 Z v) Λ Φ h2
  · exact isHW_map F'.act1 F.act2 _ hinj (fun Z v => GlobalTheory.FockSwap.rename_fockAct1 Z v) Λ' Φ h1
  · rw [norm_swap F F' Φ, hn]

theorem swap_rule : ∀ (X : ProvA) (p q r s : ℕ) (lam : Ix p q → ℚ) (lam' : Ix r s → ℚ),
    (Formalism.MainNotions.SchurIrreducible.ARiiiUp X lam lam' → Formalism.MainNotions.SchurIrreducible.ARiiiDown X lam' lam) ∧
    (Formalism.MainNotions.SchurIrreducible.ARiiiLine X lam lam' → Formalism.MainNotions.SchurIrreducible.ARiiiLine X lam' lam) ∧
    (Formalism.MainNotions.SchurIrreducible.ARiv X (r := r) (s := s) lam → NoLow X r s lam) := by
  intro X p q r s lam lam'
  refine ⟨fun hUp => ?_, fun hL => ?_, fun hiv => ?_⟩
  · intro MM f hf hne
    have hf' := intw_tr (X.fock p q r s) (X.fock r s p q) (X.ds p q lam).HK MM.M f hf
    have hne' : tr f ≠ 0 := fun h0 => hne (by rw [← tr_tr f, h0, tr_zero])
    obtain ⟨⟨N, hN, e, he, hr⟩, hΦ⟩ := hUp MM (tr f) hf' hne'
    refine ⟨⟨N, hN, e, he, ?_⟩, fun Φ hJ => ?_⟩
    · ext y
      simp only [LinearMap.mem_range]
      constructor
      · rintro ⟨P, rfl⟩
        have hm : TensorProduct.comm ℂ _ _ (f P) ∈ LinearMap.range (tr f) :=
          ⟨rename Prod.swap P, by rw [tr_apply, rename_swap_swap]⟩
        rw [hr] at hm
        obtain ⟨t, ht⟩ := hm
        refine ⟨TensorProduct.comm ℂ _ _ t, ?_⟩
        rw [← comm_map', ht, comm_comm']
      · rintro ⟨t, rfl⟩
        have hm : TensorProduct.comm ℂ _ _ (TensorProduct.map N.subtype LinearMap.id t) ∈
            LinearMap.range (tr f) := by
          rw [hr, comm_map']
          exact ⟨_, rfl⟩
        obtain ⟨P, hP⟩ := hm
        refine ⟨rename Prod.swap P, ?_⟩
        rw [tr_apply] at hP
        have := congrArg (TensorProduct.comm ℂ _ _) hP
        rwa [comm_comm', comm_comm'] at this
    · have hJ' := jointHW_swap (X.fock p q r s) (X.fock r s p q) _ _ Φ hJ
      obtain ⟨hne1, hu⟩ := hΦ _ hJ'
      have key : tr f (rename Prod.swap Φ) = TensorProduct.comm ℂ _ _ (f Φ) := by
        rw [tr_apply, rename_swap_swap]
      refine ⟨fun h0 => hne1 (by rw [key, h0, map_zero]), fun f' hf'' hΦf => ?_⟩
      have h2 := hu (tr f') (intw_tr (X.fock p q r s) (X.fock r s p q) _ _ f' hf'')
        (by rw [key, tr_apply, rename_swap_swap, hΦf])
      rw [← tr_tr f', h2, tr_tr]
  · obtain ⟨f₀, h₀, hne, hu⟩ := hL
    refine ⟨tr f₀, intw_tr (X.fock r s p q) (X.fock p q r s) _ _ f₀ h₀,
      fun h0 => hne (tr_eq_zero h0), fun g hg => ?_⟩
    obtain ⟨c, hc⟩ := hu (tr g) (intw_tr (X.fock p q r s) (X.fock r s p q) _ _ g hg)
    exact ⟨c, by rw [← tr_tr g, hc, tr_smul]⟩
  · intro i h1 hir his MM f hf
    exact tr_eq_zero (hiv i h1 hir his MM (tr f)
      (intw_tr (X.fock p q (r - i) (s - i)) (X.fock (r - i) (s - i) p q) _ _ f hf))

end GlobalTheory.SwapRule
