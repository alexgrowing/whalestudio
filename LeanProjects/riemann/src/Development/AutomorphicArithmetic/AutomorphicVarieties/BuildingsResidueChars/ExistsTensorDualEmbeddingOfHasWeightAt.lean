import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ISupRangeWeightMapsEqTopDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsotypicOfJointlyInjectiveIntoIsotypic
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsMultilinearIntertwinerOfCommutingSubgroups
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsDualSchurModuleIsoDualWeight
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ArchimedeanUnitaryLeISupEmbUAndCommute
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.BasicNotions
open scoped TensorProduct

section
open GlobalTheory.DefU GlobalTheory.Branching
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem irr_emb (τ : E →+* ℂ) (lam : DomWeight n) :
    Representation.IsIrreducible ((sqRep ℂ n lam).comp ((cEmb τ).comp (embU n τ).subtype)) := by
  obtain ⟨e, he⟩ := GlobalTheory.EmbUnitary.exists_equiv_unitaryGroup E n τ
  have heq : (sqRep ℂ n lam).comp ((cEmb τ).comp (embU n τ).subtype) =
      (smallRep (unitaryIncl n) lam).comp e.toMulEquiv.toMonoidHom := by
    ext x : 1
    change sqRep ℂ n lam (cEmb τ (x : UA E n)) = sqRep ℂ n lam (unitaryIncl n (e x))
    rw [he]
  rw [heq]
  exact GlobalTheory.CuspMult.isIrreducible_comp_mulEquiv _ e.toMulEquiv (isIrreducible_smallRep_unitary n lam)

private noncomputable def locRep (τ : E →+* ℂ) (lam : DomWeight n) :
    Representation ℂ ((embU n τ).subgroupOf (infU E n)) (nablaSq ℂ n lam) :=
  (sqRep ℂ n lam).comp ((cEmb τ).comp ((infU E n).subtype.comp (Subgroup.subtype _)))

private theorem irr_locRep (τ : E →+* ℂ) (lam : DomWeight n) : (locRep τ lam).IsIrreducible :=
  GlobalTheory.CuspMult.isIrreducible_comp_mulEquiv _ (Subgroup.subgroupOfEquivOfLe (embU_le_infU τ)) (irr_emb τ lam)

private noncomputable def repN {m : ℕ} (N : Submodule ℂ (Fin m → UA E n → ℂ))
    (hN : ∀ x ∈ infU E n, ∀ F ∈ N, (fun k => RU E n x (F k)) ∈ N) : Representation ℂ (infU E n) N where
  toFun x :=
    { toFun := fun F => ⟨fun k => RU E n x (F.1 k), hN x x.2 F.1 F.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    ext F k g
    simp
  map_mul' x y := by
    ext F k : 3
    exact (RU_RU x.1 y.1 (F.1 k)).symm

private theorem isoN {m : ℕ} (N : Submodule ℂ (Fin m → UA E n → ℂ))
    (hN : ∀ x ∈ infU E n, ∀ F ∈ N, (fun k => RU E n x (F k)) ∈ N) (σ : Submodule ℂ (UA E n → ℂ))
    (hσ : IsAutRepU σ) (hNσ : ∀ F ∈ N, ∀ k, F k ∈ σ) (τ : E →+* ℂ) (lam : DomWeight n) (h : HasWeightAt σ τ lam) :
    (⨆ f : {f : nablaSq ℂ n lam →ₗ[ℂ] N // ∀ (g : (embU n τ).subgroupOf (infU E n)) v,
      f (locRep τ lam g v) = repN N hN g (f v)}, LinearMap.range f.1) = ⊤ := by
  let π : AutSub E n := ⟨σ, hσ⟩
  have h1 := iSup_range_weight_eq_top E n π τ lam h
  refine UpperTheory.isotypic_of_jointly_injective_into_isotypic _ _ π.V (locRep τ lam) (π.rep.comp ((infU E n).subtype.comp (Subgroup.subtype _)))
    (irr_locRep τ lam) ?_ N ((repN N hN).comp (Subgroup.subtype _)) (Fin m)
    (fun k => ((LinearMap.proj k).comp N.subtype).codRestrict σ fun F => hNσ F.1 F.2 k) (fun _ _ _ => rfl)
    (fun y hy => Subtype.ext (funext fun k => congrArg Subtype.val (hy k)))
  refine top_le_iff.1 (h1.ge.trans (iSup_le fun f => ?_))
  exact le_iSup_of_le ⟨f.toLinearMap, fun g v => LinearMap.congr_fun (f.isIntertwining' ⟨g.1.1, g.2⟩) v⟩ le_rfl

private theorem exists_multi {I : Type} [Finite I] (emb : I → (E →+* ℂ))
    (hb : Function.Bijective (fun i => InfinitePlace.mk (emb i))) (lam : I → DomWeight n)
    (σ : Submodule ℂ (UA E n → ℂ)) (hσ : IsAutRepU σ) (hw : ∀ i, HasWeightAt σ (emb i) (lam i)) {m : ℕ}
    (N : Submodule ℂ (Fin m → UA E n → ℂ)) (h0 : N ≠ ⊥) (hNσ : ∀ F ∈ N, ∀ k, F k ∈ σ)
    (hN : ∀ x ∈ infU E n, ∀ F ∈ N, (fun k => RU E n x (F k)) ∈ N) :
    ∃ μ : MultilinearMap ℂ (fun i => nablaSq ℂ n (lam i)) N, μ ≠ 0 ∧ ∀ x ∈ infU E n, ∀ v k,
      RU E n x ((μ v).1 k) = (μ fun i => sqRep ℂ n (lam i) (cEmb (emb i) x) (v i)).1 k := by
  classical
  haveI : Nontrivial N := Submodule.nontrivial_iff_ne_bot.2 h0
  obtain ⟨hgen, hcomm⟩ := UpperTheory.archimedeanUnitary_le_iSup_embU_and_commute E n
  obtain ⟨μ, hμ0, hμ⟩ := UpperTheory.exists_multilinear_intertwiner_of_commuting_subgroups (infU E n) I (fun i => (embU n (emb i)).subgroupOf (infU E n))
    (fun i j hij a ha b hb' => Subtype.ext (hcomm (emb i) (emb j) (fun e => hij (hb.1 e)) a.1 ha b.1 hb'))
    (fun i => nablaSq ℂ n (lam i)) (fun i => locRep (emb i) (lam i)) (fun i => irr_locRep _ _) N (repN N hN)
    (fun i => isoN N hN σ hσ hNσ (emb i) (lam i) (hw i))
  refine ⟨μ, hμ0, fun x hx => ?_⟩
  refine Subgroup.iSup_induction _ (C := fun x => ∀ v k,
      RU E n x ((μ v).1 k) = (μ fun i => sqRep ℂ n (lam i) (cEmb (emb i) x) (v i)).1 k) (hgen hx) ?_ ?_ ?_
  · intro τ y hy v k
    obtain ⟨i, hi⟩ := hb.2 (InfinitePlace.mk τ)
    have hi' : InfinitePlace.mk (emb i) = InfinitePlace.mk τ := hi
    have hy' : y ∈ embU n (emb i) := by
      unfold embU at hy ⊢
      rwa [hi']
    have h2 := hμ i ⟨⟨y, embU_le_infU _ hy'⟩, hy'⟩ v
    have h3 : (fun j => sqRep ℂ n (lam j) (cEmb (emb j) y) (v j)) =
        Function.update v i (locRep (emb i) (lam i) ⟨⟨y, embU_le_infU _ hy'⟩, hy'⟩ (v i)) := by
      funext j
      by_cases e : j = i
      · subst e
        rw [Function.update_self]
        rfl
      · have h4 := (Subgroup.mem_inf.1 hy').2
        rw [Subgroup.mem_iInf] at h4
        have h5 := h4 (emb j)
        rw [Subgroup.mem_iInf] at h5
        have h6 : cEmb (emb j) y = 1 := h5 fun e' => e (hb.1 e')
        rw [Function.update_of_ne e, h6, map_one, Module.End.one_apply]
    rw [h3, h2]
    rfl
  · intro v k
    simp only [map_one, Module.End.one_apply]
  · intro a b ha hb v k
    rw [← RU_RU, hb, ha]
    simp only [map_mul, Module.End.mul_apply]

end

private theorem dualDistrib_comp_map {I : Type} [Finite I] {M : I → Type} [∀ i, AddCommGroup (M i)]
    [∀ i, Module ℂ (M i)] (f : ∀ i, Module.Dual ℂ (M i)) (g : ∀ i, M i →ₗ[ℂ] M i) :
    PiTensorProduct.dualDistrib (PiTensorProduct.tprod ℂ f) ∘ₗ PiTensorProduct.map g =
      PiTensorProduct.dualDistrib (PiTensorProduct.tprod ℂ fun i => f i ∘ₗ g i) := by
  have := Fintype.ofFinite I
  ext v
  simp [PiTensorProduct.dualDistrib_apply]

theorem UpperTheory.exists_tensor_dual_embedding_of_hasWeightAt :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (I : Type) [Finite I] (emb : I → (E →+* ℂ)), Function.Bijective (fun i => InfinitePlace.mk (emb i)) → ∀ (lam : I → DomWeight n) (σ : Submodule ℂ (UA E n → ℂ)), IsAutRepU σ → (∀ i, HasWeightAt σ (emb i) (lam i).dual) → ∀ (m : ℕ) (N : Submodule ℂ (Fin m → UA E n → ℂ)), N ≠ ⊥ → (∀ F ∈ N, ∀ k, F k ∈ σ) → (∀ x ∈ infU E n, ∀ F ∈ N, (fun k => RU E n x (F k)) ∈ N) → ∃ Φ : Module.Dual ℂ (⨂[ℂ] i : I, nablaSq ℂ n (lam i)) →ₗ[ℂ] (Fin m → UA E n → ℂ), Φ ≠ 0 ∧ (∀ ℓ, Φ ℓ ∈ N) ∧ ∀ ℓ, ∀ x ∈ infU E n, ∀ k, RU E n x (Φ ℓ k) = Φ (ℓ ∘ₗ PiTensorProduct.map fun i => GlobalTheory.Branching.sqRep ℂ n (lam i) (cEmb (emb i) x⁻¹)) k := by
  intro E _ _ _ n hn I _ emb hb lam σ hσ hw m N h0 hNσ hN
  obtain ⟨μ, hμ0, hμ⟩ := exists_multi emb hb (fun i => (lam i).dual) σ hσ hw N h0 hNσ hN
  choose κ hκ using fun i => UpperTheory.exists_dual_schur_module_iso_dual_weight n hn (lam i)
  let D := PiTensorProduct.dualDistribEquiv (R := ℂ) (M := fun i => nablaSq ℂ n (lam i))
  have hD : ∀ t, D t = PiTensorProduct.dualDistrib t := fun _ => rfl
  let Ψ := PiTensorProduct.lift (μ.compLinearMap fun i => (κ i).toLinearMap)
  have hΦ : ∀ f, (N.subtype ∘ₗ Ψ ∘ₗ D.symm.toLinearMap) (D (PiTensorProduct.tprod ℂ f)) =
      (μ fun i => κ i (f i)).1 := by
    intro f
    change (Ψ (D.symm (D _))).1 = _
    rw [D.symm_apply_apply, PiTensorProduct.lift.tprod]
    rfl
  refine ⟨N.subtype ∘ₗ Ψ ∘ₗ D.symm.toLinearMap, fun h => hμ0 ?_, fun ℓ => (Ψ (D.symm ℓ)).2, fun ℓ x hx k => ?_⟩
  · ext v : 1
    have := hΦ fun i => (κ i).symm (v i)
    rw [h] at this
    simp only [LinearEquiv.apply_symm_apply] at this
    exact Subtype.ext this.symm
  · obtain ⟨t, rfl⟩ := D.surjective ℓ
    generalize (N.subtype ∘ₗ Ψ ∘ₗ D.symm.toLinearMap) = Φ at hΦ
    induction t using PiTensorProduct.induction_on with
    | smul_tprod c f =>
      rw [map_smul, LinearMap.smul_comp, map_smul, map_smul, Pi.smul_apply, Pi.smul_apply, map_smul]
      congr 1
      rw [hΦ, hμ x hx, hD, dualDistrib_comp_map, ← hD, hΦ]
      simp only [map_inv (cEmb _), hκ]
    | add a b ha hb => simp only [map_add, LinearMap.add_comp, Pi.add_apply, ha, hb]
