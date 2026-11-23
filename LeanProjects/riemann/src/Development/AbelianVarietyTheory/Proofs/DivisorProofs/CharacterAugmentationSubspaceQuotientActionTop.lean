import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QActMSubAlgebraMap
import Development.AbelianVarietyTheory.Definitions.Divisors.KottwitzDimSignatureOneOne
open Module GlobalTheory.HTRho GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model

noncomputable section

namespace GlobalTheory.HTRho.CRTSplit

variable {k O C V : Type*} [Field k] [Ring O] [CommRing C] [Algebra C O] [AddCommGroup V] [Module k V]

abbrev actC (τ : O →+* Module.End k V) : MonoidAlgebra k C →ₐ[k] Module.End k V :=
  MonoidAlgebra.lift k (Module.End k V) C (τ.comp (algebraMap C O)).toMonoidHom

abbrev chiC (χ : C →+* k) : MonoidAlgebra k C →ₐ[k] k :=
  MonoidAlgebra.lift k k C χ.toMonoidHom

theorem actC_apply (τ : O →+* Module.End k V) (f : MonoidAlgebra k C) (v : V) :
    actC τ f v = ∑ c ∈ f.coeff.support, f.coeff c • τ (algebraMap C O c) v := by
  rw [actC, MonoidAlgebra.lift_apply, Finsupp.sum, LinearMap.sum_apply]
  rfl

theorem chiC_apply (χ : C →+* k) (f : MonoidAlgebra k C) :
    chiC χ f = ∑ c ∈ f.coeff.support, f.coeff c * χ c := by
  rw [chiC, MonoidAlgebra.lift_apply, Finsupp.sum]
  rfl

theorem actC_of (τ : O →+* Module.End k V) (c : C) :
    actC τ (MonoidAlgebra.of k C c) = τ (algebraMap C O c) := by
  rw [actC, MonoidAlgebra.lift_of]; rfl

theorem chiC_of (χ : C →+* k) (c : C) : chiC χ (MonoidAlgebra.of k C c) = χ c := by
  rw [chiC, MonoidAlgebra.lift_of]; rfl

theorem actC_eq_zero {Idx : Type*} (τ : O →+* Module.End k V) (χ : Idx → C →+* k)
    (hJ : jSub τ χ ⊤ = ⊥) (f : MonoidAlgebra k C) (hf : ∀ i, chiC (χ i) f = 0) (v : V) :
    actC τ f v = 0 := by
  have hmem : actC τ f v ∈ jSub τ χ ⊤ := by
    apply Submodule.subset_span
    refine ⟨f.coeff.support.card, fun l => f.coeff (f.coeff.support.equivFin.symm l),
      fun l => (f.coeff.support.equivFin.symm l : C), v, trivial, fun i => ?_, ?_⟩
    · have h1 := Equiv.sum_comp f.coeff.support.equivFin.symm
        (fun x : f.coeff.support => f.coeff x * χ i x)
      beta_reduce at h1
      rw [h1, Finset.sum_coe_sort f.coeff.support (fun x => f.coeff x * χ i x), ← chiC_apply, hf i]
    · have h1 := Equiv.sum_comp f.coeff.support.equivFin.symm
        (fun x : f.coeff.support => f.coeff x • τ (algebraMap C O x) v)
      beta_reduce at h1
      rw [h1, Finset.sum_coe_sort f.coeff.support (fun x => f.coeff x • τ (algebraMap C O x) v),
        actC_apply]
  rw [hJ] at hmem
  simpa using hmem

theorem actC_mem_mSub (τ : O →+* Module.End k V) (χ : C →+* k) (f : MonoidAlgebra k C)
    (hf : chiC χ f = 0) (x : V) : actC τ f x ∈ mSub τ χ ⊤ := by
  have h : actC τ f x = ∑ c ∈ f.coeff.support, f.coeff c • (τ (algebraMap C O c) x - χ c • x) := by
    simp only [smul_sub, Finset.sum_sub_distrib, smul_smul]
    rw [actC_apply, ← Finset.sum_smul, ← chiC_apply, hf, zero_smul, sub_zero]
  rw [h]
  exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, x, trivial, rfl⟩)

theorem actC_mSub_eq_zero {Idx : Type*} (τ : O →+* Module.End k V) (χ : Idx → C →+* k)
    (hJ : jSub τ χ ⊤ = ⊥) (i : Idx) (e : MonoidAlgebra k C) (he : ∀ l, l ≠ i → chiC (χ l) e = 0)
    (y : V) (hy : y ∈ mSub τ (χ i) ⊤) : actC τ e y = 0 := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨c, x, -, rfl⟩ := hz
    have h2 : τ (algebraMap C O c) x - χ i c • x =
        actC τ (MonoidAlgebra.of k C c - algebraMap k _ (χ i c)) x := by
      rw [map_sub, AlgHom.commutes, actC_of, LinearMap.sub_apply, Module.algebraMap_end_apply]
    rw [h2, ← Module.End.mul_apply, ← map_mul]
    refine actC_eq_zero τ χ hJ _ (fun l => ?_) x
    rw [map_mul]
    by_cases hl : l = i
    · subst hl
      rw [map_sub, AlgHom.commutes, chiC_of, Algebra.algebraMap_self, RingHom.id_apply, sub_self,
        mul_zero]
    · rw [he l hl, zero_mul]
  | zero => simp
  | add _ _ _ _ h1 h2 => rw [map_add, h1, h2, add_zero]
  | smul a _ _ h => rw [map_smul, h, smul_zero]

end GlobalTheory.HTRho.CRTSplit

open GlobalTheory.HTRho.CRTSplit in

theorem GlobalTheory.HTRho.finrank_homO_eq_sum_quot : ∀ {k O C Idx W V : Type*} [Field k] [Ring O] [CommRing C] [Algebra C O]
    [Fintype Idx] [AddCommGroup W] [Module k W] [FiniteDimensional k W] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (σW : O →+* Module.End k W) (τ : O →+* Module.End k V) (χ : Idx → C →+* k),
    Function.Injective χ → jSub τ χ ⊤ = ⊥ →
    finrank k (homO σW τ) = ∑ i, finrank k (homO σW (qAct τ (mSub τ (χ i) ⊤)
      (mSub_stable τ (χ i) ⊤ (fun _ _ _ => trivial)))) := by
  intro k O C Idx W V _ _ _ _ _ _ _ _ _ _ _ σW τ χ hχ hJ
  classical
  have hb : ∀ i j, ∃ b : MonoidAlgebra k C, i ≠ j → chiC (χ i) b = 1 ∧ chiC (χ j) b = 0 := by
    intro i j
    by_cases hij : i = j
    · exact ⟨0, fun h => (h hij).elim⟩
    obtain ⟨c, hc⟩ := DFunLike.ne_iff.mp (hχ.ne hij)
    have hc' : χ i c - χ j c ≠ 0 := sub_ne_zero.mpr hc
    refine ⟨(χ i c - χ j c)⁻¹ • (MonoidAlgebra.of k C c - algebraMap k _ (χ j c)), fun _ => ⟨?_, ?_⟩⟩
    · rw [map_smul, map_sub, AlgHom.commutes, chiC_of, Algebra.algebraMap_self, RingHom.id_apply,
        smul_eq_mul, inv_mul_cancel₀ hc']
    · rw [map_smul, map_sub, AlgHom.commutes, chiC_of, Algebra.algebraMap_self, RingHom.id_apply,
        sub_self, smul_zero]
  choose b hb using hb
  let e : Idx → MonoidAlgebra k C := fun i => ∏ j ∈ Finset.univ.erase i, b i j
  have he : ∀ i l, chiC (χ l) (e i) = if l = i then 1 else 0 := by
    intro i l
    simp only [e, map_prod]
    split_ifs with hl
    · subst hl; exact Finset.prod_eq_one fun j hj => (hb l j (Finset.ne_of_mem_erase hj).symm).1
    · exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hl, Finset.mem_univ l⟩) (hb i l (Ne.symm hl)).2
  have hsum : ∀ v : V, v = ∑ i, actC τ (e i) v := by
    intro v
    have h0 : actC τ (1 - ∑ i, e i) v = 0 :=
      actC_eq_zero τ χ hJ _ (fun l => by simp [map_sub, map_sum, he]) v
    rw [map_sub, map_one, map_sum, LinearMap.sub_apply, Module.End.one_apply, LinearMap.sum_apply,
      sub_eq_zero] at h0
    exact h0
  let Φ : V →ₗ[k] ((i : Idx) → V ⧸ mSub τ (χ i) ⊤) := LinearMap.pi fun i => (mSub τ (χ i) ⊤).mkQ
  have hΦ : Function.Bijective Φ := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro v hv
      have hv' : ∀ i, v ∈ mSub τ (χ i) ⊤ := fun i => by
        have := congr_fun hv i
        simpa [Φ, Submodule.Quotient.mk_eq_zero] using this
      rw [hsum v]
      exact Finset.sum_eq_zero fun i _ =>
        actC_mSub_eq_zero τ χ hJ i (e i) (fun l hl => by rw [he, if_neg hl]) v (hv' i)
    · intro q
      choose w hw using fun i => Submodule.Quotient.mk_surjective (mSub τ (χ i) ⊤) (q i)
      refine ⟨∑ j, actC τ (e j) (w j), funext fun i => ?_⟩
      simp only [Φ, LinearMap.pi_apply, Submodule.mkQ_apply]
      rw [← hw i, Submodule.Quotient.eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), add_sub_right_comm]
      refine add_mem ?_ (Submodule.sum_mem _ fun j hj => actC_mem_mSub τ (χ i) _
        (by rw [he, if_neg (Finset.ne_of_mem_erase hj).symm]) (w j))
      have h3 := actC_mem_mSub τ (χ i) (e i - 1) (by rw [map_sub, he, if_pos rfl, map_one, sub_self]) (w i)
      simpa [map_sub] using h3
  let Φe := LinearEquiv.ofBijective Φ hΦ
  let Ψ : homO σW τ →ₗ[k] ((i : Idx) → homO σW (qAct τ (mSub τ (χ i) ⊤)
      (mSub_stable τ (χ i) ⊤ (fun _ _ _ => trivial)))) :=
    LinearMap.pi fun i =>
      { toFun := fun T => ⟨(mSub τ (χ i) ⊤).mkQ ∘ₗ T.1, (mem_homO _ _ _).mpr fun a x => by
            rw [LinearMap.comp_apply, LinearMap.comp_apply, (mem_homO _ _ _).mp T.2 a x, qAct_mk]⟩
        map_add' := fun S T => by ext; simp
        map_smul' := fun c T => by ext; simp }
  have hΨ : Function.Bijective Ψ := by
    constructor
    · intro S T h
      apply Subtype.ext
      apply LinearMap.ext
      intro x
      apply hΦ.1
      funext i
      have := congrArg (fun F => ((F i).1 x)) h
      simpa [Ψ, Φ] using this
    · intro F
      let T : W →ₗ[k] V := Φe.symm.toLinearMap ∘ₗ LinearMap.pi (fun i => (F i).1)
      have hT : ∀ x i, (mSub τ (χ i) ⊤).mkQ (T x) = (F i).1 x := fun x i =>
        congr_fun (Φe.apply_symm_apply (fun i => (F i).1 x)) i
      have hTm : T ∈ homO σW τ := by
        rw [mem_homO]
        intro a x
        apply hΦ.1
        funext i
        change (mSub τ (χ i) ⊤).mkQ (T (σW a x)) = (mSub τ (χ i) ⊤).mkQ (τ a (T x))
        rw [hT, ← qAct_mk τ _ (mSub_stable τ (χ i) ⊤ (fun _ _ _ => trivial)), hT,
          (mem_homO _ _ _).mp (F i).2 a x]
      refine ⟨⟨T, hTm⟩, funext fun i => Subtype.ext (LinearMap.ext fun x => ?_)⟩
      exact hT x i
  rw [LinearEquiv.finrank_eq (LinearEquiv.ofBijective Ψ hΨ), Module.finrank_pi_fintype]
