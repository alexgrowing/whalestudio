import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ISupRangeWeightMapsEqTopDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsotypicOfJointlyInjectiveIntoIsotypic
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsMultilinearIntertwinerOfCommutingSubgroups
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ArchimedeanUnitaryLeISupEmbUAndCommute
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.ExponentialEntries.RightSub
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep

open scoped TensorProduct Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.RealLift UpperTheory.TP.RP

section
variable {I : Type} [Fintype I] {V : I → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, FiniteDimensional ℂ (V i)]

private theorem map_update_mem (S : Submodule ℂ (⨂[ℂ] i, V i)) (C : ∀ i, Set (Module.End ℂ (V i)))
    (hC : ∀ i, Submodule.span ℂ (C i) = ⊤)
    (hS : ∀ i, ∀ B ∈ C i, ∀ x ∈ S,
      PiTensorProduct.map (Function.update (fun i => (1 : Module.End ℂ (V i))) i B) x ∈ S)
    (i : I) (B : Module.End ℂ (V i)) :
    ∀ x ∈ S, PiTensorProduct.map (Function.update (fun i => (1 : Module.End ℂ (V i))) i B) x ∈ S := by
  have hB : B ∈ Submodule.span ℂ (C i) := hC i ▸ Submodule.mem_top
  induction hB using Submodule.span_induction with
  | mem B hB => exact hS i B hB
  | zero =>
    intro x _
    have h0 := (PiTensorProduct.mapMultilinear ℂ V V).map_update_zero (fun i => (1 : Module.End ℂ (V i))) i
    have h1 : PiTensorProduct.map (Function.update (fun i => (1 : Module.End ℂ (V i))) i 0) = 0 := h0
    rw [h1]
    exact S.zero_mem
  | add B D _ _ hB hD =>
    intro x hx
    rw [PiTensorProduct.map_update_add, LinearMap.add_apply]
    exact add_mem (hB x hx) (hD x hx)
  | smul c B _ hB =>
    intro x hx
    rw [PiTensorProduct.map_update_smul, LinearMap.smul_apply]
    exact S.smul_mem _ (hB x hx)

private theorem map_mem (S : Submodule ℂ (⨂[ℂ] i, V i))
    (hS : ∀ i (B : Module.End ℂ (V i)), ∀ x ∈ S,
      PiTensorProduct.map (Function.update (fun i => (1 : Module.End ℂ (V i))) i B) x ∈ S)
    (s : Finset I) : ∀ A : ∀ i, Module.End ℂ (V i), (∀ i, i ∉ s → A i = 1) → ∀ x ∈ S, PiTensorProduct.map A x ∈ S := by
  induction s using Finset.induction_on with
  | empty =>
    intro A hA x hx
    have : A = fun i => LinearMap.id := funext fun i => hA i (Finset.notMem_empty i)
    rw [this, PiTensorProduct.map_id]
    exact hx
  | insert a s ha ih =>
    intro A hA x hx
    have hsplit : A = fun i => (Function.update (fun i => (1 : Module.End ℂ (V i))) a (A a)) i ∘ₗ
        (Function.update A a 1) i := by
      funext i
      by_cases e : i = a
      · subst e
        simp only [Function.update_self]
        rfl
      · simp only [Function.update_of_ne e]
        rfl
    rw [hsplit, PiTensorProduct.map_comp, LinearMap.comp_apply]
    refine hS a _ _ (ih _ (fun i hi => ?_) x hx)
    by_cases e : i = a
    · subst e
      simp
    · rw [Function.update_of_ne e]
      exact hA i (by simp [e, hi])

private theorem exists_dual_ne (x : ⨂[ℂ] i, V i) (hx : x ≠ 0) :
    ∃ f : ∀ i, Module.Dual ℂ (V i), PiTensorProduct.dualDistrib (PiTensorProduct.tprod ℂ f) x ≠ 0 := by
  by_contra hc
  push_neg at hc
  refine hx ((Module.forall_dual_apply_eq_zero_iff ℂ x).1 fun ℓ => ?_)
  obtain ⟨t, rfl⟩ := (PiTensorProduct.dualDistribEquiv (R := ℂ) (M := V)).surjective ℓ
  change PiTensorProduct.dualDistrib t x = 0
  induction t using PiTensorProduct.induction_on with
  | smul_tprod c f => simp [hc f]
  | add a b ha hb => simp [ha, hb]

private theorem map_rank_one (f : ∀ i, Module.Dual ℂ (V i)) (v : ∀ i, V i) (x : ⨂[ℂ] i, V i) :
    PiTensorProduct.map (fun i => (f i).smulRight (v i)) x =
      PiTensorProduct.dualDistrib (PiTensorProduct.tprod ℂ f) x • PiTensorProduct.tprod ℂ v := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c w =>
    simp only [map_smul, PiTensorProduct.map_tprod, PiTensorProduct.dualDistrib_apply, LinearMap.smulRight_apply,
      LinearMap.smul_apply]
    rw [MultilinearMap.map_smul_univ, smul_assoc]
  | add a b ha hb => simp only [map_add, ha, hb, LinearMap.add_apply, add_smul]

private theorem eq_top_of_closed (S : Submodule ℂ (⨂[ℂ] i, V i)) (hne : S ≠ ⊥)
    (hS : ∀ A : ∀ i, Module.End ℂ (V i), ∀ x ∈ S, PiTensorProduct.map A x ∈ S) : S = ⊤ := by
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff S).1 hne
  obtain ⟨f, hf⟩ := exists_dual_ne x hx0
  refine top_le_iff.1 ?_
  rw [← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  have := hS (fun i => (f i).smulRight (v i)) x hx
  rw [map_rank_one] at this
  exact (S.smul_mem_iff hf).1 this

private theorem isIrreducible_of_factors {G : Type} [Group G] (ρ : Representation ℂ G (⨂[ℂ] i, V i))
    [Nontrivial (⨂[ℂ] i, V i)] (C : ∀ i, Set (Module.End ℂ (V i))) (hC : ∀ i, Submodule.span ℂ (C i) = ⊤)
    (h : ∀ i, ∀ B ∈ C i, ∃ g, ρ g = PiTensorProduct.map (Function.update (fun i => (1 : Module.End ℂ (V i))) i B)) :
    ρ.IsIrreducible := by
  refine { exists_pair_ne := ⟨⊥, ⊤, fun e => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · exact bot_ne_top (congrArg Subrepresentation.toSubmodule e : (⊥ : Submodule ℂ (⨂[ℂ] i, V i)) = ⊤)
  by_cases hb : S.toSubmodule = ⊥
  · exact Or.inl (Subrepresentation.toSubmodule_injective hb)
  · refine Or.inr (Subrepresentation.toSubmodule_injective (eq_top_of_closed _ hb fun A x hx => ?_))
    refine map_mem _ (map_update_mem _ C hC fun i B hB y hy => ?_) Finset.univ A
      (fun i hi => (hi (Finset.mem_univ i)).elim) x hx
    obtain ⟨g, hg⟩ := h i B hB
    rw [← hg]
    exact S.apply_mem_toSubmodule g hy

end

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem irr_on_emb (τ : E →+* ℂ) (lam : DomWeight n) :
    Representation.IsIrreducible ((GlobalTheory.Branching.sqRep ℂ n lam).comp
      ((GlobalTheory.UnitaryBC.cEmb τ).comp (GlobalTheory.UnitaryBC.embU n τ).subtype)) := by
  obtain ⟨e, he⟩ := GlobalTheory.EmbUnitary.exists_equiv_unitaryGroup E n τ
  have heq : (GlobalTheory.Branching.sqRep ℂ n lam).comp ((GlobalTheory.UnitaryBC.cEmb τ).comp (GlobalTheory.UnitaryBC.embU n τ).subtype) =
      (GlobalTheory.Branching.smallRep (GlobalTheory.Branching.unitaryIncl n) lam).comp e.toMulEquiv.toMonoidHom := by
    ext x : 1
    change GlobalTheory.Branching.sqRep ℂ n lam (GlobalTheory.UnitaryBC.cEmb τ (x : GlobalTheory.UnitaryBC.UA E n)) =
      GlobalTheory.Branching.sqRep ℂ n lam (GlobalTheory.Branching.unitaryIncl n (e x))
    rw [he]
  rw [heq]
  exact GlobalTheory.CuspMult.isIrreducible_comp_mulEquiv _ e.toMulEquiv (GlobalTheory.Branching.isIrreducible_smallRep_unitary n lam)

private noncomputable def atEmb (τ : E →+* ℂ) (lam : DomWeight n) :
    Representation ℂ ((GlobalTheory.UnitaryBC.embU n τ).subgroupOf (GlobalTheory.UnitaryBC.infU E n)) (nablaSq ℂ n lam) :=
  (GlobalTheory.Branching.sqRep ℂ n lam).comp
    ((GlobalTheory.UnitaryBC.cEmb τ).comp ((GlobalTheory.UnitaryBC.infU E n).subtype.comp (Subgroup.subtype _)))

private theorem irr_atEmb (τ : E →+* ℂ) (lam : DomWeight n) : (atEmb τ lam).IsIrreducible :=
  GlobalTheory.CuspMult.isIrreducible_comp_mulEquiv _ (Subgroup.subgroupOfEquivOfLe (GlobalTheory.DefU.embU_le_infU τ)) (irr_on_emb τ lam)

private noncomputable def tensRep {I : Type} (emb : I → (E →+* ℂ)) (lam : I → DomWeight n) [Fintype I] :
    Representation ℂ (GlobalTheory.UnitaryBC.infU E n) (⨂[ℂ] i, nablaSq ℂ n (lam i)) where
  toFun k := PiTensorProduct.map fun i => GlobalTheory.Branching.sqRep ℂ n (lam i) (GlobalTheory.UnitaryBC.cEmb (emb i) k.1)
  map_one' := by
    simp only [OneMemClass.coe_one, map_one]
    exact PiTensorProduct.map_id
  map_mul' a b := by
    simp only [Subgroup.coe_mul, map_mul]
    exact PiTensorProduct.map_mul _ _

private theorem comp_other {I : Type} {emb : I → (E →+* ℂ)}
    (hb : Function.Bijective (fun i => InfinitePlace.mk (emb i))) {i j : I} (e : j ≠ i)
    {y : GlobalTheory.UnitaryBC.UA E n} (hy : y ∈ GlobalTheory.UnitaryBC.embU n (emb i)) : GlobalTheory.UnitaryBC.cEmb (emb j) y = 1 := by
  have h4 := (Subgroup.mem_inf.1 hy).2
  rw [Subgroup.mem_iInf] at h4
  have h5 := h4 (emb j)
  rw [Subgroup.mem_iInf] at h5
  exact h5 fun e' => e (hb.1 e')

private theorem comps_eq_update {I : Type} {emb : I → (E →+* ℂ)} (lam : I → DomWeight n)
    (hb : Function.Bijective (fun i => InfinitePlace.mk (emb i))) {i : I}
    {y : GlobalTheory.UnitaryBC.UA E n} (hy : y ∈ GlobalTheory.UnitaryBC.embU n (emb i)) :
    (fun j => GlobalTheory.Branching.sqRep ℂ n (lam j) (GlobalTheory.UnitaryBC.cEmb (emb j) y)) =
      Function.update (fun j => (1 : Module.End ℂ (nablaSq ℂ n (lam j)))) i
        (GlobalTheory.Branching.sqRep ℂ n (lam i) (GlobalTheory.UnitaryBC.cEmb (emb i) y)) := by
  funext j
  by_cases e : j = i
  · subst e
    rw [Function.update_self]
  · rw [Function.update_of_ne e, comp_other hb e hy, map_one]

private theorem irr_tensRep {I : Type} [Fintype I] {emb : I → (E →+* ℂ)} (lam : I → DomWeight n)
    (hb : Function.Bijective (fun i => InfinitePlace.mk (emb i))) [Nontrivial (⨂[ℂ] i, nablaSq ℂ n (lam i))] :
    (tensRep emb lam).IsIrreducible := by
  refine isIrreducible_of_factors _ (fun i => Set.range (atEmb (emb i) (lam i)))
    (fun i => GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible _ _ _ (irr_atEmb _ _)) ?_
  rintro i _ ⟨g, rfl⟩
  refine ⟨g.1, ?_⟩
  exact congrArg PiTensorProduct.map (comps_eq_update lam hb (i := i) (y := g.1.1) g.2)

private theorem exists_equivariant {I : Type} [Fintype I] (emb : I → (E →+* ℂ))
    (hb : Function.Bijective (fun i => InfinitePlace.mk (emb i))) (lam : I → DomWeight n)
    (π : GlobalTheory.DefU.AutSub E n) (hw : ∀ i, GlobalTheory.UnitaryBC.HasWeightAt π.V (emb i) (lam i)) :
    ∃ μ : MultilinearMap ℂ (fun i => nablaSq ℂ n (lam i)) π.V, μ ≠ 0 ∧ ∀ x ∈ GlobalTheory.UnitaryBC.infU E n, ∀ v,
      π.rep x (μ v) = μ fun i => GlobalTheory.Branching.sqRep ℂ n (lam i) (GlobalTheory.UnitaryBC.cEmb (emb i) x) (v i) := by
  haveI : Nontrivial π.V := Submodule.nontrivial_iff_ne_bot.2 π.isAut.ne_bot
  obtain ⟨hgen, hcomm⟩ := UpperTheory.archimedeanUnitary_le_iSup_embU_and_commute E n
  obtain ⟨μ, hμ0, hμ⟩ := UpperTheory.exists_multilinear_intertwiner_of_commuting_subgroups (GlobalTheory.UnitaryBC.infU E n) I
    (fun i => (GlobalTheory.UnitaryBC.embU n (emb i)).subgroupOf (GlobalTheory.UnitaryBC.infU E n))
    (fun i j hij a ha b hb' => Subtype.ext (hcomm (emb i) (emb j) (fun e => hij (hb.1 e)) a.1 ha b.1 hb'))
    (fun i => nablaSq ℂ n (lam i)) (fun i => atEmb (emb i) (lam i)) (fun i => irr_atEmb _ _) π.V
    (π.rep.comp (GlobalTheory.UnitaryBC.infU E n).subtype) (fun i => by
      have h1 := GlobalTheory.DefU.iSup_range_weight_eq_top E n π (emb i) (lam i) (hw i)
      refine top_le_iff.1 (h1.ge.trans (iSup_le fun f => ?_))
      exact le_iSup_of_le ⟨f.toLinearMap, fun g v => LinearMap.congr_fun (f.isIntertwining' ⟨g.1.1, g.2⟩) v⟩ le_rfl)
  refine ⟨μ, hμ0, fun x hx => ?_⟩
  refine Subgroup.iSup_induction _ (C := fun x => ∀ v, π.rep x (μ v) =
      μ fun i => GlobalTheory.Branching.sqRep ℂ n (lam i) (GlobalTheory.UnitaryBC.cEmb (emb i) x) (v i)) (hgen hx) ?_ ?_ ?_
  · intro τ y hy v
    obtain ⟨i, hi⟩ := hb.2 (InfinitePlace.mk τ)
    have hi' : InfinitePlace.mk (emb i) = InfinitePlace.mk τ := hi
    have hy' : y ∈ GlobalTheory.UnitaryBC.embU n (emb i) := by
      unfold GlobalTheory.UnitaryBC.embU at hy ⊢
      rwa [hi']
    have hyI : y ∈ GlobalTheory.UnitaryBC.infU E n := GlobalTheory.DefU.embU_le_infU _ hy'
    have h2 := hμ i ⟨⟨y, hyI⟩, hy'⟩ v
    have h3 : (fun j => GlobalTheory.Branching.sqRep ℂ n (lam j) (GlobalTheory.UnitaryBC.cEmb (emb j) y) (v j)) =
        Function.update v i (atEmb (emb i) (lam i) ⟨⟨y, hyI⟩, hy'⟩ (v i)) := by
      funext j
      by_cases e : j = i
      · subst e
        rw [Function.update_self]
        rfl
      · rw [Function.update_of_ne e, comp_other hb e hy', map_one, Module.End.one_apply]
    rw [h3, h2]
    rfl
  · intro v
    simp only [map_one, Module.End.one_apply]
  · intro a b ha hb v
    rw [map_mul, Module.End.mul_apply, hb, ha]
    simp only [map_mul, Module.End.mul_apply]

end

theorem UpperTheory.TP.RP.formEx :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (I : Type) [Fintype I] (emb : I → (E →+* ℂ)),
      Function.Bijective (fun i => InfinitePlace.mk (emb i)) → ∀ (lam : I → DomWeight n) (U : Submodule ℂ (GlobalTheory.UnitaryBC.UA E n → ℂ)),
      GlobalTheory.UnitaryBC.IsAutRepU U → (∀ i, GlobalTheory.UnitaryBC.HasWeightAt U (emb i) (lam i)) →
      ∃ (ρ : Representation ℂ (GlobalTheory.UnitaryBC.infU E n) (⨂[ℂ] i, nablaSq ℂ n (lam i))) (j : (⨂[ℂ] i, nablaSq ℂ n (lam i)) →ₗ[ℂ] (GlobalTheory.UnitaryBC.UA E n → ℂ)),
        FiniteDimensional ℂ (⨂[ℂ] i, nablaSq ℂ n (lam i)) ∧ ρ.IsIrreducible ∧
        (∀ k, ρ k = PiTensorProduct.map fun i => GlobalTheory.Branching.sqRep ℂ n (lam i) (GlobalTheory.UnitaryBC.cEmb (emb i) k.1)) ∧
        Function.Injective j ∧ (∀ x, j x ∈ U) ∧ ∀ k x, j (ρ k x) = GlobalTheory.UnitaryBC.RU E n k.1 (j x) := by
  intro E _ _ _ n hn I _ emb hb lam U hU hw
  let π : GlobalTheory.DefU.AutSub E n := ⟨U, hU⟩
  obtain ⟨μ, hμ0, hμ⟩ := exists_equivariant emb hb lam π hw
  have hl : PiTensorProduct.lift μ ≠ 0 := fun h => hμ0 (by
    ext v : 1
    have := LinearMap.congr_fun h (PiTensorProduct.tprod ℂ v)
    rw [PiTensorProduct.lift.tprod] at this
    simpa using this)
  haveI : Nontrivial (⨂[ℂ] i, nablaSq ℂ n (lam i)) := by
    by_contra hs
    rw [not_nontrivial_iff_subsingleton] at hs
    exact hl (LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero])
  have hirr := irr_tensRep (emb := emb) lam hb
  let j : (⨂[ℂ] i, nablaSq ℂ n (lam i)) →ₗ[ℂ] (GlobalTheory.UnitaryBC.UA E n → ℂ) :=
    π.V.subtype ∘ₗ PiTensorProduct.lift μ
  have hj : ∀ k x, j (tensRep emb lam k x) = GlobalTheory.UnitaryBC.RU E n k.1 (j x) := by
    intro k x
    induction x using PiTensorProduct.induction_on with
    | smul_tprod c v =>
      simp only [map_smul]
      congr 1
      change ((PiTensorProduct.lift μ) (PiTensorProduct.map _ (PiTensorProduct.tprod ℂ v))).1 =
        GlobalTheory.UnitaryBC.RU E n k.1 ((PiTensorProduct.lift μ) (PiTensorProduct.tprod ℂ v)).1
      rw [PiTensorProduct.map_tprod, PiTensorProduct.lift.tprod, PiTensorProduct.lift.tprod, ← hμ k.1 k.2 v]
      rfl
    | add a b ha hb => simp only [map_add, ha, hb]
  refine ⟨tensRep emb lam, j, inferInstance, hirr, fun _ => rfl, ?_, fun x => (PiTensorProduct.lift μ x).2, hj⟩
  let S : Subrepresentation (tensRep emb lam) :=
    ⟨LinearMap.ker j, fun k x hx => by
      have hx' : j x = 0 := hx
      change j _ = 0
      rw [hj, hx', map_zero]⟩
  rcases hirr.eq_bot_or_eq_top S with h | h
  · exact LinearMap.ker_eq_bot.1 (congrArg Subrepresentation.toSubmodule h)
  · exfalso
    refine hl (LinearMap.ext fun x => Subtype.ext ?_)
    have hx : x ∈ S.toSubmodule := by rw [h]; trivial
    exact hx
