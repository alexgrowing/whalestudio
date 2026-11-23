import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmRep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmIndCoinvariants
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenNormalisedSubgroupSubset
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviIntegralFacts

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.SmGL.IndExact

section General

variable {G X U : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup X] [Module ℂ X]
  [AddCommGroup U] [Module ℂ U] {P : Subgroup G} {σ : Representation ℂ P X} {ρ : Representation ℂ P U}

theorem smIndMap_injective (ι : σ.IntertwiningMap ρ) (hι : Function.Injective ι) :
    Function.Injective (smIndMap ι) := fun φ ψ h =>
  Subtype.ext (Subtype.ext (funext fun g =>
    hι (congrFun (congrArg (fun χ : smoothPart (ind P ρ) => χ.1.1) h) g)))

theorem exists_smIndMap_eq (ι : σ.IntertwiningMap ρ) (hι : Function.Injective ι)
    (F : smoothPart (ind P ρ)) (hF : ∀ g, ∃ u, ι u = F.1.1 g) : ∃ F', smIndMap ι F' = F := by
  choose u hu using hF
  refine ⟨⟨⟨u, fun h g => hι ?_⟩, mem_smoothPart_of_nhds (Filter.mem_of_superset
    (IsOpen.mem_nhds F.2 (by simp)) fun g hg => ?_)⟩, Subtype.ext (Subtype.ext (funext hu))⟩
  · rw [ι.isIntertwining, hu, hu, F.1.2 h g]
  · have hg' : ind P ρ g F.1 = F.1 := hg
    refine Subtype.ext (funext fun x => hι ?_)
    show ι (u (x * g)) = ι (u x)
    rw [hu, hu]
    exact congrFun (congrArg Subtype.val hg') x

theorem exists_normalised_pi {α : Type} [Finite α] {Γ : α → Type} [∀ i, Group (Γ i)]
    [∀ i, TopologicalSpace (Γ i)] (K : ∀ i, Subgroup (Γ i))
    (h : ∀ i, ∀ U ∈ nhds (1 : Γ i), ∃ J : Subgroup (Γ i), IsOpen (J : Set (Γ i)) ∧ (J : Set (Γ i)) ⊆ U ∧
      J ≤ K i ∧ ∀ x ∈ K i, ∀ j ∈ J, x * j * x⁻¹ ∈ J) :
    ∀ U ∈ nhds (1 : ∀ i, Γ i), ∃ J : Subgroup (∀ i, Γ i), IsOpen (J : Set (∀ i, Γ i)) ∧
      (J : Set (∀ i, Γ i)) ⊆ U ∧ J ≤ Subgroup.pi Set.univ K ∧
        ∀ x ∈ Subgroup.pi Set.univ K, ∀ j ∈ J, x * j * x⁻¹ ∈ J := by
  intro U hU
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, -, t, ht, hI⟩ := hU
  choose J h1 h2 h3 h4 using fun i => h i (t i) (ht i)
  exact ⟨Subgroup.pi Set.univ J, isOpen_set_pi Set.finite_univ fun i _ => h1 i,
    fun x hx => hI fun i _ => h2 i (hx i trivial), fun x hx i _ => h3 i (hx i trivial),
    fun x hx j hj i _ => h4 i _ (hx i trivial) _ (hj i trivial)⟩

end General

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α β : Type} [Fintype α] [Fintype β] [LinearOrder β]
  {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  {c : α → β → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
  {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

theorem isSmoothChar_relDeltaHalf : IsSmoothChar (relDeltaHalf k c) := by
  unfold relDeltaHalf
  refine Finset.prod_induction _ IsSmoothChar (fun _ _ => IsSmoothChar.mul) isSmoothChar_one
    fun a _ => ?_
  exact (isSmoothChar_deltaHalf k).comp _ (continuous_apply a)

theorem relInd_surjective (f : ∀ i, (Σ j, c i j) ≃ m i)
    {π : Representation ℂ (∀ i, Levi k (c i)) W} {π' : Representation ℂ (∀ i, Levi k (c i)) W'}
    (p : π.IntertwiningMap π') (hp : Function.Surjective p) (hπ : IsSmooth π) :
    Function.Surjective (smIndMap (compMap (twistMap p (relDeltaHalf k c)) (relProj k f))) := by
  have H := fun i => GlobalTheory.SmGL.LeviInt.levi_integral_facts k β (m i) (c i) (f i)
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hP : IsClosed (relParab k f : Set (Levi k m)) :=
    isClosed_set_pi fun i _ => (H i).2.2.2.2.2.2.1
  have hK : IsCompact (Subgroup.pi Set.univ (fun i => KO k (m i)) : Set (Levi k m)) :=
    isCompact_univ_pi fun i => SplitFlip.isCompact_KO
  have hPK : ∀ g : Levi k m, ∃ q ∈ relParab k f, ∃ x ∈ Subgroup.pi Set.univ (fun i => KO k (m i)),
      g = q * x := fun g => by
    choose q hq x hx e using fun i => (H i).2.2.2.2.2.2.2.2 (g i)
    exact ⟨q, fun i _ => hq i, x, fun i _ => hx i, funext e⟩
  have hcont : Continuous (relProj k f) := continuous_pi fun i =>
    (H i).2.2.2.2.2.1.comp (((continuous_apply i).comp continuous_subtype_val).subtype_mk _)
  let σ₀ : Representation ℂ (relParab k f) W := (twist π (relDeltaHalf k c)).comp (relProj k f)
  let z : Representation.IntertwiningMap σ₀ σ₀ :=
    { toLinearMap := 0, isIntertwining' := fun _ => by ext; simp }
  refine (GlobalTheory.SmGL.IndCoinv.smInd_coinvariants (Levi k m) (relParab k f) _ hP hK hPK
    (exists_normalised_pi _ fun i => GlobalTheory.SmGL.exists_open_normalised_subgroup_subset k (m i)) _ _ _ _
    (isSmooth_comp (isSmooth_twist hπ isSmoothChar_relDeltaHalf) _ hcont)
    (compMap (twistMap p _) _) Unit (fun _ => z) hp ?_).1
  intro x _
  refine Submodule.subset_span ⟨(), -x, ?_⟩
  show x = (0 : _) - -x
  simp

end Local

theorem jhMult_relInd_exact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α β : Type) [Fintype α] [Fintype β] [LinearOrder β] (m : α → Type) [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (c : α → β → Type) [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] (f : ∀ i, (Σ j, c i j) ≃ m i) (W W₁ W₂ : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂] (π : Representation ℂ (∀ i, GlobalTheory.SmGL.Levi k (c i)) W) (π₁ : Representation ℂ (∀ i, GlobalTheory.SmGL.Levi k (c i)) W₁) (π₂ : Representation ℂ (∀ i, GlobalTheory.SmGL.Levi k (c i)) W₂) (ι : π₁.IntertwiningMap π) (p : π.IntertwiningMap π₂), Function.Injective ι → Function.Surjective p → (∀ u, p (ι u) = 0) → (∀ v, p v = 0 → ∃ u, ι u = v) → GlobalTheory.PRep.IsSmooth π → ∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ (GlobalTheory.SmGL.Levi k m) Y), τ.IsIrreducible → GlobalTheory.SmGL.jhMult τ (GlobalTheory.SmGL.relInd f π) = GlobalTheory.SmGL.jhMult τ (GlobalTheory.SmGL.relInd f π₁) + GlobalTheory.SmGL.jhMult τ (GlobalTheory.SmGL.relInd f π₂) := by
  intro k _ _ _ _ α β _ _ _ m _ _ c _ _ f W W₁ W₂ _ _ _ _ _ _ π π₁ π₂ ι p hι hp h0 hker hπ Y _ _ τ hτ
  refine GlobalTheory.JHMult.jhMult_exact
    (smIndMap (compMap (twistMap ι (relDeltaHalf k c)) (relProj k f)))
    (smIndMap (compMap (twistMap p (relDeltaHalf k c)) (relProj k f))) hτ
    (smIndMap_injective _ hι) (relInd_surjective f p hp hπ)
    (fun u => Subtype.ext (Subtype.ext (funext fun g => h0 _))) fun F hF => ?_
  exact exists_smIndMap_eq _ hι F fun g =>
    hker _ (congrFun (congrArg (fun χ => χ.1.1) hF) g)

end GlobalTheory.SmGL.IndExact
