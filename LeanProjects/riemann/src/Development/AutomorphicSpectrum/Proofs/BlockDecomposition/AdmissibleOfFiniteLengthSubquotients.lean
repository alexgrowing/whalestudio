import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.AdmFL

variable {G X Y Z : Type} [Group G] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
  [AddCommGroup Z] [Module ℂ Z]

theorem mem_fixed_iff {α : Representation ℂ G X} {K : Subgroup G} {x : X} :
    x ∈ fixed α K ↔ ∀ g ∈ K, α g x = x := by
  change (∀ h : K, α h x = ((1 : K →* ℂˣ) h : ℂ) • x) ↔ _
  simp only [MonoidHom.one_apply, Units.val_one, one_smul]
  exact ⟨fun h g hg => h ⟨g, hg⟩, fun h g => h g g.2⟩

private theorem finiteDimensional_fixed_of_exact_lemma {α : Representation ℂ G X}
    {β : Representation ℂ G Y} (i : α.IntertwiningMap β) (g : G) (x : X) :
    i (α g x) = β g (i x) := by
  have h := LinearMap.congr_fun (i.isIntertwining' g) x
  simpa [LinearMap.comp_apply] using h

theorem finiteDimensional_fixed_of_exact {α : Representation ℂ G X} {β : Representation ℂ G Y}
    {γ : Representation ℂ G Z} (i : α.IntertwiningMap β) (p : β.IntertwiningMap γ)
    (hi : Function.Injective i) (hker : ∀ y, p y = 0 → ∃ x, i x = y) (K : Subgroup G)
    [FiniteDimensional ℂ (fixed α K)] [FiniteDimensional ℂ (fixed γ K)] :
    FiniteDimensional ℂ (fixed β K) := by
  let j : fixed α K →ₗ[ℂ] fixed β K :=
    { toFun := fun x => ⟨i x, mem_fixed_iff.2 fun g hg => by
        rw [← finiteDimensional_fixed_of_exact_lemma i g x, mem_fixed_iff.1 x.2 g hg]⟩
      map_add' := fun x y => by ext; simp
      map_smul' := fun c x => by ext; simp }
  let q : fixed β K →ₗ[ℂ] fixed γ K :=
    { toFun := fun y => ⟨p y, mem_fixed_iff.2 fun g hg => by
        rw [← finiteDimensional_fixed_of_exact_lemma p g y, mem_fixed_iff.1 y.2 g hg]⟩
      map_add' := fun x y => by ext; simp
      map_smul' := fun c x => by ext; simp }
  have hK : LinearMap.ker q ≤ LinearMap.range j := by
    intro y hy
    rw [LinearMap.mem_ker] at hy
    have hpy : p (y : Y) = 0 := congrArg Subtype.val hy
    obtain ⟨x, hx⟩ := hker _ hpy
    have hxfix : x ∈ fixed α K := mem_fixed_iff.2 fun g hg => hi (by
      rw [finiteDimensional_fixed_of_exact_lemma i, hx, mem_fixed_iff.1 y.2 g hg])
    exact ⟨⟨x, hxfix⟩, Subtype.ext hx⟩
  refine ⟨?_⟩
  apply Submodule.fg_of_fg_map_of_fg_inf_ker (f := q)
  · exact IsNoetherian.noetherian _
  · rw [Submodule.fg_iff_finiteDimensional]
    exact Submodule.finiteDimensional_of_le (le_trans inf_le_right hK)

private theorem isAdmissible_of_hasFiniteLength_lemma_3 {M : Type} [AddCommGroup M] [Module ℂ M]
    [Module (MonoidAlgebra ℂ G) M] [IsScalarTower ℂ (MonoidAlgebra ℂ G) M] (g : G) (x : M) :
    Representation.ofModule' (k := ℂ) (G := G) M g x = MonoidAlgebra.single g (1 : ℂ) • x := by
  first
  | rfl
  | simp only [Representation.ofModule', MonoidAlgebra.lift_symm_apply, Algebra.lsmul_coe]

private theorem isAdmissible_of_hasFiniteLength_lemma_2 {M₁ M₂ : Type} [AddCommGroup M₁] [Module ℂ M₁]
    [Module (MonoidAlgebra ℂ G) M₁] [IsScalarTower ℂ (MonoidAlgebra ℂ G) M₁] [AddCommGroup M₂] [Module ℂ M₂]
    [Module (MonoidAlgebra ℂ G) M₂] [IsScalarTower ℂ (MonoidAlgebra ℂ G) M₂]
    (f : M₁ →ₗ[MonoidAlgebra ℂ G] M₂) :
    ∃ φ : (Representation.ofModule' (k := ℂ) (G := G) M₁).IntertwiningMap
        (Representation.ofModule' (k := ℂ) (G := G) M₂), ∀ x, φ x = f x := by
  refine ⟨⟨f.restrictScalars ℂ, fun g => ?_⟩, fun x => rfl⟩
  ext x
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, isAdmissible_of_hasFiniteLength_lemma_3,
    map_smul]

private theorem isAdmissible_of_hasFiniteLength_lemma_5 {M : Type} [AddCommGroup M] [Module ℂ M]
    [Module (MonoidAlgebra ℂ G) M] [IsScalarTower ℂ (MonoidAlgebra ℂ G) M]
    [IsSimpleModule (MonoidAlgebra ℂ G) M] :
    (Representation.ofModule' (k := ℂ) (G := G) M).IsIrreducible := by
  have e : Subrepresentation (Representation.ofModule' (k := ℂ) (G := G) M) ≃o
      Submodule (MonoidAlgebra ℂ G) M :=
    { toFun := fun S =>
        { carrier := S.toSubmodule
          add_mem' := fun hx hy => S.toSubmodule.add_mem hx hy
          zero_mem' := S.toSubmodule.zero_mem
          smul_mem' := fun a x hx => by
            induction a using MonoidAlgebra.induction_on with
            | of g =>
              rw [MonoidAlgebra.of_apply, ← isAdmissible_of_hasFiniteLength_lemma_3]
              exact S.apply_mem_toSubmodule g hx
            | add a b ha hb =>
              rw [add_smul]
              exact S.toSubmodule.add_mem ha hb
            | smul r a ha =>
              rw [smul_assoc]
              exact S.toSubmodule.smul_mem r ha }
      invFun := fun P => ⟨P.restrictScalars ℂ, fun g v hv => by
        rw [Submodule.restrictScalars_mem, isAdmissible_of_hasFiniteLength_lemma_3]
        exact P.smul_mem _ hv⟩
      left_inv := fun S => by
        apply Subrepresentation.ext
        rfl
      right_inv := fun P => by
        ext x
        rfl
      map_rel_iff' := by
        intro S T
        exact Iff.rfl }
  exact e.isSimpleOrder

private theorem isAdmissible_of_hasFiniteLength_lemma_4 [TopologicalSpace G] (K : Subgroup G) :
    ∀ {M : Type} [AddCommGroup M] [Module (MonoidAlgebra ℂ G) M], IsFiniteLength (MonoidAlgebra ℂ G) M →
    ∀ [Module ℂ M] [IsScalarTower ℂ (MonoidAlgebra ℂ G) M],
    (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W),
      IsSubquotient σ (Representation.ofModule' (k := ℂ) (G := G) M) → σ.IsIrreducible → IsAdmissible σ) →
    IsOpen (K : Set G) → IsCompact (K : Set G) →
    FiniteDimensional ℂ (fixed (Representation.ofModule' (k := ℂ) (G := G) M) K) := by
  intro M _ _ hM
  induction hM with
  | of_subsingleton =>
    intro _ _ _ _ _
    infer_instance
  | @of_simple_quotient M _ _ N _ hN ih =>
    intro _ _ hsub hKo hKc
    obtain ⟨i, hi⟩ := isAdmissible_of_hasFiniteLength_lemma_2 (G := G) N.subtype
    obtain ⟨p, hp⟩ := isAdmissible_of_hasFiniteLength_lemma_2 (G := G) N.mkQ
    have hinj : Function.Injective i := by
      intro x y hxy
      rw [hi, hi] at hxy
      exact Subtype.ext hxy
    have hker : ∀ y, p y = 0 → ∃ x, i x = y := by
      intro y hy
      rw [hp, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hy
      exact ⟨⟨y, hy⟩, by rw [hi]; rfl⟩
    have hsurj : Function.Surjective p := by
      intro z
      obtain ⟨m, hm⟩ := Submodule.mkQ_surjective N z
      exact ⟨m, by rw [hp]; exact hm⟩
    have hNsub : IsSubquotient (Representation.ofModule' (k := ℂ) (G := G) N)
        (Representation.ofModule' (k := ℂ) (G := G) M) := IsSubquotient.of_injective i hinj
    haveI : FiniteDimensional ℂ (fixed (Representation.ofModule' (k := ℂ) (G := G) N) K) :=
      ih (fun W _ _ σ hσ hirr => hsub W σ (hσ.trans hNsub) hirr) hKo hKc
    haveI : FiniteDimensional ℂ (fixed (Representation.ofModule' (k := ℂ) (G := G) (M ⧸ N)) K) := by
      have hirr : (Representation.ofModule' (k := ℂ) (G := G) (M ⧸ N)).IsIrreducible :=
        isAdmissible_of_hasFiniteLength_lemma_5
      have hadm := hsub _ _ (IsSubquotient.of_surjective p hsurj) hirr
      unfold IsAdmissible at hadm
      exact hadm.2 K hKo hKc
    exact finiteDimensional_fixed_of_exact i p hinj hker K

theorem isAdmissible_of_hasFiniteLength : ∀ {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), IsSmooth ρ → HasFiniteLength ρ → (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W), IsSubquotient σ ρ → σ.IsIrreducible → IsAdmissible σ) → IsAdmissible ρ := by
  intro G V _ _ _ _ _ ρ hsm hfl hirr
  unfold IsAdmissible
  refine ⟨hsm, fun K hKo hKc => ?_⟩
  letI instA : Module (MonoidAlgebra ℂ G) V := Module.compHom V ρ.asAlgebraHom.toRingHom
  haveI instT : IsScalarTower ℂ (MonoidAlgebra ℂ G) V := ⟨fun c a v => by
    show ρ.asAlgebraHom (c • a) v = c • ρ.asAlgebraHom a v
    rw [map_smul]
    rfl⟩
  have hρ : Representation.ofModule' (k := ℂ) (G := G) V = ρ := by
    ext g v
    rw [isAdmissible_of_hasFiniteLength_lemma_3]
    show ρ.asAlgebraHom (MonoidAlgebra.single g 1) v = ρ g v
    rw [Representation.asAlgebraHom_single_one]
  have hfl' : IsFiniteLength (MonoidAlgebra ℂ G) V := hfl
  have h := @isAdmissible_of_hasFiniteLength_lemma_4 G _ _ K V _ instA hfl' _ instT
    (fun W _ _ σ hσ h => hirr W σ (hρ ▸ hσ) h) hKo hKc
  rw [hρ] at h
  exact h

end GlobalTheory.CompanionTheory.AdmFL

end
