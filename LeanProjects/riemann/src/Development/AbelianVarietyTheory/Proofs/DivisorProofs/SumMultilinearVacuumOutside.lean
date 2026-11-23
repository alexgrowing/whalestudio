import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PureTensor

theorem sum_prod_functionals {ι Y : Type} [DecidableEq ι] {X : ι → Type} (T : Finset ι) {m : ℕ}
    (f : Fin m → Y → ℂ) (φ : Fin m → ∀ v, X v → ℂ) (L : ∀ v, (X v → ℂ) →ₗ[ℂ] ℂ) (z₀ : ∀ v, X v)
    (h : ∀ y (z : ∀ v, X v), ∑ j, f j y * ∏ v ∈ T, φ j v (z v) = 0) (y : Y) :
    ∑ j, f j y * ∏ v ∈ T, L v (φ j v) = 0 := by
  have key : ∀ S : Finset ι, S ⊆ T → ∀ y (z : ∀ v, X v),
      ∑ j, f j y * (∏ v ∈ T \ S, φ j v (z v)) * ∏ v ∈ S, L v (φ j v) = 0 := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro _ y z; simpa using h y z
    | @insert a S ha ih =>
      intro hS y z
      have haT : a ∈ T := hS (Finset.mem_insert_self a S)
      have ih' := ih ((Finset.subset_insert a S).trans hS)
      set c : Fin m → ℂ := fun j => f j y * (∏ v ∈ T \ insert a S, φ j v (z v)) * ∏ v ∈ S, L v (φ j v) with hc
      have hsplit : T \ S = insert a (T \ insert a S) := by
        rw [Finset.sdiff_insert, Finset.insert_erase (Finset.mem_sdiff.2 ⟨haT, ha⟩)]
      have hnot : a ∉ T \ insert a S := by simp
      have hg : (∑ j, c j • φ j a) = 0 := by
        funext t
        have := ih' y (Function.update z a t)
        rw [Finset.sum_apply]
        simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        rw [← this]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hsplit, Finset.prod_insert hnot, Function.update_self]
        have : ∏ v ∈ T \ insert a S, φ j v (Function.update z a t v) = ∏ v ∈ T \ insert a S, φ j v (z v) := by
          refine Finset.prod_congr rfl fun v hv => ?_
          have hva : v ≠ a := by rintro rfl; exact hnot hv
          rw [Function.update_of_ne hva]
        rw [this, hc]; ring
      have hL := congrArg (L a) hg
      rw [map_sum, map_zero] at hL
      simp only [map_smul, smul_eq_mul] at hL
      rw [← hL]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.prod_insert ha, hc]; ring
  simpa using key T le_rfl y z₀

theorem tensor_eq_zero {ι Y V P₀ : Type} {X : ι → Type} {P : ι → Type}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup P₀] [Module ℂ P₀] [∀ v, AddCommGroup (P v)] [∀ v, Module ℂ (P v)]
    (ev : Y → V →ₗ[ℂ] ℂ) (hev : ∀ g : V, (∀ y, ev y g = 0) → g = 0) (T : Finset ι) {m : ℕ}
    (f : Fin m → V) (φ : Fin m → ∀ v, X v → ℂ)
    (h : ∀ (L : ∀ v, (X v → ℂ) →ₗ[ℂ] ℂ) y, ∑ j, ev y (f j) * ∏ v ∈ T, L v (φ j v) = 0)
    (q₀ : V →ₗ[ℂ] P₀) (q : ∀ v, (X v → ℂ) →ₗ[ℂ] P v) :
    ∑ j, q₀ (f j) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (fun v : T => q v (φ j v)) = 0 := by
  classical
  let b : ∀ v : T, Module.Basis (Module.Free.ChooseBasisIndex ℂ (P v)) ℂ (P v) :=
    fun v => Module.Free.chooseBasis ℂ (P v)
  let B := Basis.piTensorProduct b
  apply (TensorProduct.equivFinsuppOfBasisRight B).injective
  rw [map_zero]
  ext k
  rw [map_sum, Finsupp.finset_sum_apply, Finsupp.zero_apply]
  simp only [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, B, Basis.piTensorProduct_repr_tprod_apply]
  let L : ∀ v, (X v → ℂ) →ₗ[ℂ] ℂ := fun v =>
    if hv : v ∈ T then ((b ⟨v, hv⟩).coord (k ⟨v, hv⟩)).comp (q v) else 0
  have hc : ∀ j, (∏ v : T, (b v).repr (q v (φ j v)) (k v)) = ∏ v ∈ T, L v (φ j v) := by
    intro j
    rw [← Finset.prod_coe_sort T (fun v => L v (φ j v))]
    refine Finset.prod_congr rfl fun v _ => ?_
    simp [L, v.2, Module.Basis.coord_apply]
  have hzero : ∑ j, (∏ v ∈ T, L v (φ j v)) • f j = 0 := by
    refine hev _ fun y => ?_
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
    rw [← h L y]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  simp_rw [hc, ← map_smul, ← map_sum, hzero, map_zero]

theorem sum_zero_of_pure {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (M : Model σ Y W) (ψ : AddChar (AF F) ℂ)
    (hM : M.IsGood ψ) (T : Finset (Pl F)) {m : ℕ} (f : Fin m → SInf F (Fin n × Fin d))
    (φ : Fin m → ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) (hT : ∀ j, ∀ v ∉ T, φ j v = M.vac v)
    (hsum : ∑ j, pure (f j) (φ j) = 0)
    (y : Fin n × Fin d → mixedEmbedding.mixedSpace F) (z : ∀ v : Pl F, Fin n × Fin d → Fv F v) :
    ∑ j, f j y * ∏ v ∈ T, φ j v (z v) = 0 := by
  classical
  let std : Pl F → Prop := fun v => M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1
  have hfin : {v | ¬ std v}.Finite := Filter.eventually_cofinite.1 hM.std
  have hne : ∀ v, ∃ t, M.vac v t ≠ 0 := fun v => by
    have h0 := (hM.vac v).2.1
    by_contra hc
    push_neg at hc
    exact h0 (funext hc)
  let w : ∀ v : Pl F, Fin n × Fin d → Fv F v := fun v => if std v then 0 else (hne v).choose
  have hstd0 : ∀ v, std v → M.vac v 0 = 1 := by
    intro v hv
    rw [hv, Set.indicator_of_mem (by simp)]
    rfl
  have hw : ∀ v, M.vac v (w v) ≠ 0 := by
    intro v
    by_cases hv : std v
    · simp only [w, if_pos hv, hstd0 v hv]; exact one_ne_zero
    · simp only [w, if_neg hv]; exact (hne v).choose_spec
  let a : ∀ v : Pl F, Fin n × Fin d → Fv F v := fun v => if v ∈ T then z v else w v
  have ha0 : ∀ v, v ∉ T → std v → a v = 0 := by
    intro v hvT hv
    simp only [a, if_neg hvT, w, if_pos hv]
  have hint : ∀ i, ∀ᶠ v in Filter.cofinite, a v i ∈ v.adicCompletionIntegers F := by
    intro i
    refine Filter.eventually_cofinite.2 ((hfin.union T.finite_toSet).subset ?_)
    intro v hv
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not, Finset.mem_coe] at hc
    apply hv
    rw [ha0 v hc.2 hc.1]
    exact zero_mem _
  let xf : Fin n × Fin d → Af F := fun i => ⟨fun v => a v i, hint i⟩
  let x : Fin n × Fin d → AF F := fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), xf i)
  have hxI : (fun i => evI F (x i)) = y := by funext i; simp [evI, x]
  have hxv : ∀ v, (fun i => evFin F v (x i)) = a v := by intro v; funext i; rfl
  let S : Finset (Pl F) := T ∪ hfin.toFinset
  let c : ℂ := ∏ v ∈ S \ T, M.vac v (w v)
  have hc0 : c ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => hw v
  have hpure : ∀ j, pure (f j) (φ j) x = f j y * (c * ∏ v ∈ T, φ j v (z v)) := by
    intro j
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, hxI, hxv]
    congr 1
    have hsupp : Function.mulSupport (fun v => φ j v (a v)) ⊆ (S : Set (Pl F)) := by
      intro v hv
      by_contra hvS
      simp only [S, Finset.coe_union, Set.Finite.coe_toFinset, Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq,
        not_or, not_not] at hvS
      apply hv
      simp only [hT j v hvS.1, ha0 v hvS.1 hvS.2, hstd0 v hvS.2]
    rw [finprod_eq_prod_of_mulSupport_subset _ hsupp, ← Finset.prod_sdiff (Finset.subset_union_left (s₂ := hfin.toFinset))]
    congr 1
    · refine Finset.prod_congr rfl fun v hv => ?_
      have hvT : v ∉ T := (Finset.mem_sdiff.1 hv).2
      simp only [a, if_neg hvT, hT j v hvT]
    · refine Finset.prod_congr rfl fun v hv => ?_
      simp only [a, if_pos hv]
  have hp := congrFun hsum x
  rw [Finset.sum_apply, Pi.zero_apply] at hp
  simp only [hpure] at hp
  have : c * ∑ j, f j y * ∏ v ∈ T, φ j v (z v) = 0 := by
    rw [Finset.mul_sum, ← hp]
    exact Finset.sum_congr rfl fun j _ => by ring
  exact (mul_eq_zero.1 this).resolve_left hc0

theorem pure_sum_tensor_eq_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y W) (ψ : AddChar (AF F) ℂ), M.IsGood ψ → ∀ (T : Finset (Pl F)) (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d)) (φ : Fin m → ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ), (∀ j, ∀ v ∉ T, φ j v = M.vac v) → ∑ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f j) (φ j) = 0 → ∀ (P₀ : Type) [AddCommGroup P₀] [Module ℂ P₀] (P : Pl F → Type) [∀ v, AddCommGroup (P v)] [∀ v, Module ℂ (P v)] (q₀ : SInf F (Fin n × Fin d) →ₗ[ℂ] P₀) (q : ∀ v, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] P v), ∑ j, q₀ (f j) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (fun v : T => q v (φ j v)) = 0 := by
  intro F E _ _ _ _ _ σ n d Y W M ψ hM T m f φ hT hsum P₀ _ _ P _ _ q₀ q
  classical
  let ev : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → SInf F (Fin n × Fin d) →ₗ[ℂ] ℂ := fun y =>
    { toFun := fun g => g y, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  refine tensor_eq_zero ev (fun g hg => SchwartzMap.ext fun y => hg y) T f φ (fun L y => ?_) q₀ q
  exact sum_prod_functionals T (fun j y => f j y) φ L (fun _ _ => 0) (sum_zero_of_pure M ψ hM T f φ hT hsum) y

end GlobalTheory.PureTensor
