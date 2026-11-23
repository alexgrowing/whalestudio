import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmRep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InductionContragredient

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.IndDual
open scoped TensorProduct

namespace GlobalTheory.SmGL.IndTensor

section Linear

variable {α : Type} [Fintype α] {W V : α → Type} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

def prodForm (l : ∀ i, Module.Dual ℂ (W i)) : Module.Dual ℂ (⨂[ℂ] i, W i) :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ α ℂ).compLinearMap l)

@[simp] theorem prodForm_tprod (l : ∀ i, Module.Dual ℂ (W i)) (v : ∀ i, W i) :
    prodForm l (PiTensorProduct.tprod ℂ v) = ∏ i, l i (v i) := by
  simp [prodForm]

theorem eq_zero_of_prodForm (t : ⨂[ℂ] i, W i) (h : ∀ l, prodForm l t = 0) : t = 0 := by
  classical
  let b := fun i => Module.Free.chooseBasis ℂ (W i)
  refine (Basis.piTensorProduct b).ext_elem fun p => ?_
  have : (Basis.piTensorProduct b).coord p = prodForm fun i => (b i).coord (p i) := by
    ext v
    simp
  have h2 := h fun i => (b i).coord (p i)
  rw [← this] at h2
  simpa using h2

theorem exists_contraction [DecidableEq α] (l : ∀ i, Module.Dual ℂ (W i)) (i : α)
    (t : ⨂[ℂ] i, W i) : ∃ u : W i, ∀ μ, prodForm (Function.update l i μ) t = μ u := by
  induction t using PiTensorProduct.induction_on with
  | add x y hx hy =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    exact ⟨u + v, fun μ => by rw [map_add, map_add, hu, hv]⟩
  | smul_tprod c v =>
    refine ⟨c • (∏ j ∈ Finset.univ.erase i, l j (v j)) • v i, fun μ => ?_⟩
    rw [map_smul, map_smul, map_smul, prodForm_tprod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
      Function.update_self, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_comm (μ _)]
    congr 2
    exact Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

theorem eq_zero_of_map {X : α → Type} (ev : ∀ i, X i → W i →ₗ[ℂ] V i)
    (hev : ∀ i w, (∀ x, ev i x w = 0) → w = 0) (t : ⨂[ℂ] i, W i)
    (ht : ∀ x : ∀ i, X i, PiTensorProduct.map (fun i => ev i (x i)) t = 0) : t = 0 := by
  classical
  have key : ∀ (s : Finset α) (l : ∀ i, Module.Dual ℂ (W i)),
      (∀ i ∉ s, ∃ x, ∃ μ : Module.Dual ℂ (V i), l i = μ ∘ₗ ev i x) → prodForm l t = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro l hl
      choose x μ h using fun i => hl i (by simp)
      have : prodForm l = prodForm μ ∘ₗ PiTensorProduct.map (fun i => ev i (x i)) := by
        ext v
        simp [h]
      rw [this, LinearMap.comp_apply, ht, map_zero]
    | insert i s hi ih =>
      intro l hl
      obtain ⟨u, hu⟩ := exists_contraction l i t
      have hu0 : u = 0 := hev i u fun x => (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun μ => by
        refine (hu (μ ∘ₗ ev i x)).symm.trans (ih _ fun j hj => ?_)
        by_cases hji : j = i
        · subst hji
          exact ⟨x, μ, by simp⟩
        · rw [Function.update_of_ne hji]
          exact hl j (by simp [hj, hji])
      have := hu (l i)
      rwa [Function.update_eq_self, hu0, map_zero] at this
  exact eq_zero_of_prodForm t fun l => key Finset.univ l (by simp)

end Linear

section Fixed

variable {α : Type} [Fintype α] {G V : α → Type} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
  [∀ i, IsTopologicalGroup (G i)] [∀ i, T2Space (G i)] [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

theorem mem_span_of_fixed {τ : ∀ i, Representation ℂ (G i) (V i)} (hτ : ∀ i, IsSmooth (τ i))
    {H : ∀ i, Subgroup (G i)} (hH : ∀ i, IsCompact (H i : Set (G i))) (w : ⨂[ℂ] i, V i)
    (hw : ∀ h ∈ Subgroup.pi Set.univ H, piTensor τ h w = w) :
    w ∈ Submodule.span ℂ {y | ∃ v : ∀ i, V i, (∀ i, v i ∈ fixed (τ i) (H i)) ∧
      y = PiTensorProduct.tprod ℂ v} := by
  classical
  by_contra hn
  obtain ⟨l, hl, hl0⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
  obtain ⟨l₁, h1, h2⟩ := GlobalTheory.SmGL.DualAverage.exists_invariant_form _ _ (piTensor τ)
    (isSmooth_piTensor hτ) (Subgroup.pi Set.univ H) (isCompact_univ_pi hH) l
  have key : ∀ (s : Finset α) (v : ∀ i, V i), (∀ i ∉ s, v i ∈ fixed (τ i) (H i)) →
      l₁ (PiTensorProduct.tprod ℂ v) = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro v hv
      rw [h2 _ fun h hh => by
        rw [piTensor_tprod]
        congr 1
        exact funext fun i => mem_fixed_iff.1 (hv i (by simp)) _ (hh i trivial)]
      rw [← Submodule.mem_bot ℂ, ← hl0]
      exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨v, fun i => hv i (by simp), rfl⟩)
    | insert i s hi ih =>
      intro v hv
      obtain ⟨u, hu, e⟩ := IwahoriOnto.exists_fixed_map_eq (hτ i) (hH i)
        (l₁ ∘ₗ (PiTensorProduct.tprod ℂ (s := V)).toLinearMap v i) (v i) fun h hh => by
          have := h1 (Pi.mulSingle i h) (fun j _ => by
            by_cases hji : j = i
            · subst hji; simpa using hh
            · simp [Pi.mulSingle_eq_of_ne hji]) (PiTensorProduct.tprod ℂ v)
          rw [piTensor_tprod] at this
          simp only [LinearMap.comp_apply, MultilinearMap.toLinearMap_apply, Function.update_eq_self]
          rw [← this]
          congr 2
          funext j
          by_cases hji : j = i
          · subst hji; simp
          · simp [Pi.mulSingle_eq_of_ne hji, Function.update_of_ne hji]
      simp only [LinearMap.comp_apply, MultilinearMap.toLinearMap_apply, Function.update_eq_self] at e
      rw [← e]
      refine ih _ fun j hj => ?_
      by_cases hji : j = i
      · subst hji; simpa using hu
      · rw [Function.update_of_ne hji]
        exact hv j (by simp [hj, hji])
  apply hl
  rw [← h2 w hw]
  have : l₁ = 0 := by
    ext v
    simpa using key Finset.univ v (by simp)
  simp [this]

end Fixed

section Induction

variable {α : Type} [Fintype α] {G V : α → Type} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
  [∀ i, IsTopologicalGroup (G i)] [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  {P : ∀ i, Subgroup (G i)} (τ : ∀ i, Representation ℂ (P i) (V i))

def ev (i : α) (x : G i) : smoothPart (ind (P i) (τ i)) →ₗ[ℂ] V i :=
  LinearMap.proj x ∘ₗ (indSpace (P i) (τ i)).subtype ∘ₗ (smoothPart (ind (P i) (τ i))).subtype

omit [Fintype α] in
theorem map_ev_left (p : ∀ i, P i) (g : ∀ i, G i) (t : ⨂[ℂ] i, smoothPart (ind (P i) (τ i))) :
    PiTensorProduct.map (fun i => ev τ i (p i * g i)) t =
      piTensor τ p (PiTensorProduct.map (fun i => ev τ i (g i)) t) := by
  have : (fun i => ev τ i (p i * g i)) = fun i => τ i (p i) ∘ₗ ev τ i (g i) :=
    funext fun i => LinearMap.ext fun f => f.1.2 (p i) (g i)
  rw [this, PiTensorProduct.map_comp]
  rfl

omit [Fintype α] in
theorem map_ev_right (x g : ∀ i, G i) (t : ⨂[ℂ] i, smoothPart (ind (P i) (τ i))) :
    PiTensorProduct.map (fun i => ev τ i (x i * g i)) t =
      PiTensorProduct.map (fun i => ev τ i (x i)) (piTensor (fun i => smInd (P i) (τ i)) g t) := by
  have : (fun i => ev τ i (x i * g i)) = fun i => ev τ i (x i) ∘ₗ smInd (P i) (τ i) (g i) := rfl
  rw [this, PiTensorProduct.map_comp]
  rfl

variable (ρ : Representation ℂ (Subgroup.pi Set.univ P) (⨂[ℂ] i, V i))
  (hρ : ∀ p, ρ p = piTensor τ fun i => ⟨p.1 i, p.2 i trivial⟩)

def tensorMap : (⨂[ℂ] i, smoothPart (ind (P i) (τ i))) →ₗ[ℂ]
    smoothPart (ind (Subgroup.pi Set.univ P) ρ) where
  toFun t := ⟨⟨fun g => PiTensorProduct.map (fun i => ev τ i (g i)) t, fun p g => by
      rw [hρ]
      exact map_ev_left τ (fun i => ⟨p.1 i, p.2 i trivial⟩) g t⟩,
    mem_smoothPart_of_nhds (Filter.mem_of_superset
      ((isSmooth_piTensor (ρ := fun i => smInd (P i) (τ i))
        (fun i => isSmooth_smoothRep _) t).mem_nhds (x := 1) (by simp)) fun g hg => by
      have hg' : piTensor (fun i => smInd (P i) (τ i)) g t = t := hg
      refine Subtype.ext (funext fun x => ?_)
      exact (map_ev_right τ x g t).trans (by rw [hg']))⟩
  map_add' s t := Subtype.ext (Subtype.ext (funext fun g => map_add _ s t))
  map_smul' c t := Subtype.ext (Subtype.ext (funext fun g => map_smul _ c t))

theorem tensorMap_apply (t : ⨂[ℂ] i, smoothPart (ind (P i) (τ i))) (g : ∀ i, G i) :
    (tensorMap τ ρ hρ t).1.1 g = PiTensorProduct.map (fun i => ev τ i (g i)) t := rfl

theorem tensorMap_piTensor (g : ∀ i, G i) (t : ⨂[ℂ] i, smoothPart (ind (P i) (τ i))) :
    tensorMap τ ρ hρ (piTensor (fun i => smInd (P i) (τ i)) g t) =
      smInd _ ρ g (tensorMap τ ρ hρ t) :=
  Subtype.ext (Subtype.ext (funext fun x => (map_ev_right τ x g t).symm))

theorem tensorMap_injective : Function.Injective (tensorMap τ ρ hρ) :=
  (injective_iff_map_eq_zero _).2 fun t ht => eq_zero_of_map (ev τ)
    (fun _ _ hw => Subtype.ext (Subtype.ext (funext hw))) t fun x =>
      congrArg (fun φ : smoothPart (ind (Subgroup.pi Set.univ P) ρ) => φ.1.1 x) ht

theorem tensorMap_bump {J : ∀ i, Subgroup (G i)} (hJ : ∀ i, IsOpen (J i : Set (G i)))
    (hJ' : IsOpen (Subgroup.pi Set.univ J : Set (∀ i, G i)))
    (v : ∀ i, fixed (τ i) ((J i).subgroupOf (P i)))
    (w : fixed ρ ((Subgroup.pi Set.univ J).subgroupOf (Subgroup.pi Set.univ P)))
    (hw : w.1 = PiTensorProduct.tprod ℂ fun i => (v i).1) :
    tensorMap τ ρ hρ (PiTensorProduct.tprod ℂ fun i => bump (τ i) (hJ i) (v i)) = bump ρ hJ' w := by
  classical
  refine Subtype.ext (Subtype.ext (funext fun g => ?_))
  rw [tensorMap_apply, PiTensorProduct.map_tprod]
  rcases cell_cases (P := Subgroup.pi Set.univ P) (Subgroup.pi Set.univ J) g with h | ⟨p, j, hj, rfl⟩
  · rw [bump_zero _ _ _ h]
    have : ∃ i, g i ∉ cell (P i) (J i) := by
      by_contra! hc
      choose p hp using hc
      exact h ⟨⟨fun i => p i, fun i _ => (p i).2⟩, fun i _ => hp i⟩
    obtain ⟨i, hi⟩ := this
    exact MultilinearMap.map_coord_zero _ i (bump_zero (τ i) (hJ i) (v i) hi)
  · rw [bump_mul _ _ _ _ hj, hρ, hw, piTensor_tprod]
    congr 1
    exact funext fun i => bump_mul (τ i) (hJ i) (v i) ⟨p.1 i, p.2 i trivial⟩ (hj i trivial)

theorem tensorMap_surjective [∀ i, T2Space (G i)] (hτ : ∀ i, IsSmooth (τ i)) {K : ∀ i, Subgroup (G i)}
    (hP : ∀ i, IsClosed (P i : Set (G i))) (hK : ∀ i, IsCompact (K i : Set (G i)))
    (hPK : ∀ i (g : G i), ∃ p ∈ P i, ∃ x ∈ K i, g = p * x)
    (hb : ∀ i, ∀ U ∈ nhds (1 : G i), ∃ J : Subgroup (G i), IsOpen (J : Set (G i)) ∧ (J : Set (G i)) ⊆ U ∧
      J ≤ K i ∧ ∀ x ∈ K i, ∀ j ∈ J, x * j * x⁻¹ ∈ J) :
    Function.Surjective (tensorMap τ ρ hρ) := by
  intro f
  have hf : {g | smInd _ ρ g f = f} ∈ nhds (1 : ∀ i, G i) :=
    IsOpen.mem_nhds (isSmooth_smoothRep _ f) (by
      rw [Set.mem_ofPred_eq, map_one, Module.End.one_apply])
  rw [nhds_pi, Filter.mem_pi'] at hf
  obtain ⟨I, U, hU, hUf⟩ := hf
  choose J hJ hJU hle hn using fun i => hb i _ (hU i)
  have hJ' : IsOpen (Subgroup.pi Set.univ J : Set (∀ i, G i)) :=
    isOpen_set_pi Set.finite_univ fun i _ => hJ i
  have h1 := mem_span_bump ρ (K := Subgroup.pi Set.univ K) hJ' (isCompact_univ_pi hK)
    (fun g hg i _ => hle i (hg i trivial)) (fun x hx j hj i _ => hn i _ (hx i trivial) _ (hj i trivial))
    (fun g => by
      choose p hp x hx h using fun i => hPK i (g i)
      exact ⟨p, fun i _ => hp i, x, fun i _ => hx i, funext h⟩) f
    (fun j hj => hUf fun i _ => hJU i (hj i trivial))
  show f ∈ LinearMap.range (tensorMap τ ρ hρ)
  refine Submodule.span_le.2 ?_ h1
  rintro _ ⟨z, -, w, rfl⟩
  suffices bump ρ hJ' w ∈ LinearMap.range (tensorMap τ ρ hρ) by
    obtain ⟨t, ht⟩ := this
    exact ⟨_, (tensorMap_piTensor τ ρ hρ z⁻¹ t).trans (by rw [ht])⟩
  have h2 := mem_span_of_fixed hτ (H := fun i => (J i).subgroupOf (P i))
    (fun i => (hP i).isClosedEmbedding_subtypeVal.isCompact_preimage
      ((hK i).of_isClosed_subset ((J i).isClosed_of_isOpen (hJ i)) (hle i))) w.1 fun h hh => by
      have := mem_fixed_iff.1 w.2 ⟨fun i => h i, fun i _ => (h i).2⟩ fun i _ => hh i trivial
      rwa [hρ] at this
  let M := ((LinearMap.range (tensorMap τ ρ hρ)).comap (bump ρ hJ')).map (Submodule.subtype _)
  obtain ⟨w', hw', e⟩ : w.1 ∈ M := by
    refine Submodule.span_le.2 ?_ h2
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨⟨_, mem_fixed_iff.2 fun h hh => ?_⟩,
      ⟨_, tensorMap_bump τ ρ hρ hJ hJ' (fun i => ⟨v i, hv i⟩) _ rfl⟩, rfl⟩
    rw [hρ, piTensor_tprod]
    congr 1
    exact funext fun i => mem_fixed_iff.1 (hv i) _ (hh i trivial)
  obtain rfl : w' = w := Subtype.ext e
  exact hw'

end Induction

theorem relInd_piTensor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α β : Type) [Fintype α] [Fintype β] [LinearOrder β] (m : α → Type) [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (c : α → β → Type) [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] (f : ∀ i, (Σ j, c i j) ≃ m i) (Z : α → Type) [∀ i, AddCommGroup (Z i)] [∀ i, Module ℂ (Z i)] (σ : ∀ i, Representation ℂ (GlobalTheory.SmGL.Levi k (c i)) (Z i)), (∀ i, GlobalTheory.PRep.IsSmooth (σ i)) → Nonempty ((GlobalTheory.SmGL.relInd f (GlobalTheory.SmGL.piTensor σ)).Equiv (GlobalTheory.SmGL.piTensor fun i => GlobalTheory.SmGL.parInd (f i) (σ i))) := by
  intro k _ _ _ _ α β _ _ _ m _ _ c _ _ f Z _ _ σ hσ
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have facts := fun i => GlobalTheory.SmGL.LeviInt.levi_integral_facts k β (m i) (c i) (f i)
  let τ : ∀ i, Representation ℂ (parab k (f i)) (Z i) := fun i =>
    (twist (σ i) (deltaHalf k (c i))).comp (leviProj k (f i))
  let ρ : Representation ℂ (Subgroup.pi Set.univ fun i => parab k (f i)) (⨂[ℂ] i, Z i) :=
    (twist (piTensor σ) (relDeltaHalf k c)).comp (relProj k f)
  have hρ : ∀ p, ρ p = piTensor τ fun i => ⟨p.1 i, p.2 i trivial⟩ := by
    intro p
    ext v
    show (relDeltaHalf k c (relProj k f p) : ℂ) • piTensor σ (relProj k f p) (PiTensorProduct.tprod ℂ v) =
      piTensor τ _ (PiTensorProduct.tprod ℂ v)
    rw [piTensor_tprod, piTensor_tprod, relDeltaHalf_apply, Units.coe_prod, ← MultilinearMap.map_smul_univ]
    rfl
  have hbij : Function.Bijective (tensorMap τ ρ hρ) := ⟨tensorMap_injective τ ρ hρ,
    tensorMap_surjective τ ρ hρ (K := fun i => KO k (m i))
      (fun i => isSmooth_comp (isSmooth_twist (hσ i) (isSmoothChar_deltaHalf k)) _ (facts i).2.2.2.2.2.1)
      (fun i => (facts i).2.2.2.2.2.2.1) (fun _ => SplitFlip.isCompact_KO)
      (fun i => (facts i).2.2.2.2.2.2.2.2) fun i => exists_open_normalised_subgroup_subset k (m i)⟩
  let E : (piTensor fun i => parInd (f i) (σ i)).Equiv (relInd f (piTensor σ)) :=
    .mk (LinearEquiv.ofBijective (tensorMap τ ρ hρ) hbij) fun g =>
      LinearMap.ext fun t => tensorMap_piTensor τ ρ hρ g t
  exact ⟨E.symm⟩

end GlobalTheory.SmGL.IndTensor
