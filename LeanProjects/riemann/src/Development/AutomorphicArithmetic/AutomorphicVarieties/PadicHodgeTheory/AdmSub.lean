import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OpenField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndepOnOfInvariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RatioInvariantInK0
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

section Generic

variable {G Q B : Type} [Group G] [Field Q] [AddCommGroup B] [Module Q B] (a : G → B →ₗ[Q] B)

private noncomputable def invT {V : Type} [AddCommGroup V] [Module Q V] (ρ : Representation Q G V) :
    Submodule Q (V ⊗[Q] B) :=
  ⨅ g : G, LinearMap.ker (AlgebraTensorModule.map (ρ g) (a g) - LinearMap.id)

private theorem mem_invT {V : Type} [AddCommGroup V] [Module Q V] (ρ : Representation Q G V) (x : V ⊗[Q] B) :
    x ∈ invT a ρ ↔ ∀ g, AlgebraTensorModule.map (ρ g) (a g) x = x := by
  simp only [invT, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

private theorem rT_comm {V V' : Type} [AddCommGroup V] [Module Q V] [AddCommGroup V'] [Module Q V']
    {ρ : Representation Q G V} {ρ' : Representation Q G V'} {f : V →ₗ[Q] V'}
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) (g : G) (y : V ⊗[Q] B) :
    f.rTensor B (AlgebraTensorModule.map (ρ g) (a g) y) =
      AlgebraTensorModule.map (ρ' g) (a g) (f.rTensor B y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [hf g]
  | add x y hx hy => simp only [map_add, hx, hy]

private noncomputable def invMap {V V' : Type} [AddCommGroup V] [Module Q V] [AddCommGroup V'] [Module Q V']
    {ρ : Representation Q G V} {ρ' : Representation Q G V'} {f : V →ₗ[Q] V'}
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) : invT a ρ →ₗ[Q] invT a ρ' :=
  (f.rTensor B).restrict fun x hx => (mem_invT a ρ' _).2 fun g => by
    rw [← rT_comm a hf, (mem_invT a ρ _).1 hx]

private theorem of_exact {V₀ V V' : Type} [AddCommGroup V₀] [Module Q V₀] [AddCommGroup V] [Module Q V]
    [AddCommGroup V'] [Module Q V'] [FiniteDimensional Q V]
    {ρ₀ : Representation Q G V₀} {ρ : Representation Q G V} {ρ' : Representation Q G V'}
    {i : V₀ →ₗ[Q] V} {p : V →ₗ[Q] V'}
    (hi : ∀ g x, i (ρ₀ g x) = ρ g (i x)) (hp : ∀ g x, p (ρ g x) = ρ' g (p x))
    (h1 : Function.Injective i) (h2 : Function.Exact i p) (h3 : Function.Surjective p) (n : ℕ)
    [Module.Finite Q (invT a ρ)] [Module.Finite Q (invT a ρ')]
    (c₀ : finrank Q (invT a ρ₀) ≤ n * finrank Q V₀) (c' : finrank Q (invT a ρ') ≤ n * finrank Q V')
    (h : finrank Q (invT a ρ) = n * finrank Q V) :
    finrank Q (invT a ρ₀) = n * finrank Q V₀ ∧ finrank Q (invT a ρ') = n * finrank Q V' := by
  have hex : Function.Exact (i.rTensor B) (p.rTensor B) := rTensor_exact B h2 h3
  have hinj : Function.Injective (i.rTensor B) := Module.Flat.rTensor_preserves_injective_linearMap _ h1
  have e1 : Function.Injective (invMap a hi) := fun x y h => Subtype.ext (hinj (congrArg Subtype.val h))
  have e2 : Function.Exact (invMap a hi) (invMap a hp) := by
    refine fun x => ⟨fun h => ?_, ?_⟩
    · obtain ⟨y, hy⟩ := (hex x).1 (congrArg Subtype.val h)
      refine ⟨⟨y, (mem_invT a ρ₀ y).2 fun g => hinj ?_⟩, Subtype.ext hy⟩
      rw [rT_comm a hi, hy]
      exact (mem_invT a ρ _).1 x.2 g
    · rintro ⟨y, rfl⟩
      exact Subtype.ext ((hex _).2 ⟨_, rfl⟩)
  have h4 := (invMap a hp).finrank_range_add_finrank_ker
  rw [e2.linearMap_ker_eq, LinearMap.finrank_range_of_inj e1] at h4
  have h5 := p.finrank_range_add_finrank_ker
  rw [h2.linearMap_ker_eq, LinearMap.finrank_range_of_inj h1, LinearMap.range_eq_top.2 h3, finrank_top] at h5
  have h6 := (LinearMap.range (invMap a hp)).finrank_le
  rw [← h5, mul_add] at h
  exact ⟨by omega, by omega⟩

private theorem sub_quot (n : ℕ)
    (hb : ∀ (W : Type) [AddCommGroup W] [Module Q W] [FiniteDimensional Q W] (σ : Representation Q G W),
      Module.Finite Q (invT a σ) ∧ finrank Q (invT a σ) ≤ n * finrank Q W)
    {V V' : Type} [AddCommGroup V] [Module Q V] [AddCommGroup V'] [Module Q V']
    [FiniteDimensional Q V] [FiniteDimensional Q V']
    {ρ : Representation Q G V} {ρ' : Representation Q G V'} {f : V →ₗ[Q] V'}
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) :
    (Function.Injective f → finrank Q (invT a ρ') = n * finrank Q V' → finrank Q (invT a ρ) = n * finrank Q V) ∧
    (Function.Surjective f → finrank Q (invT a ρ) = n * finrank Q V →
      finrank Q (invT a ρ') = n * finrank Q V') := by
  have := (hb V ρ).1
  have := (hb V' ρ').1
  refine ⟨fun hi h => ?_, fun hs h => ?_⟩
  · have hst : ∀ g, LinearMap.range f ≤ (LinearMap.range f).comap (ρ' g) := by
      rintro g _ ⟨v, rfl⟩
      exact ⟨ρ g v, hf g v⟩
    have := (hb _ (ρ'.quotient (LinearMap.range f) hst)).1
    exact (of_exact a (ρ' := ρ'.quotient (LinearMap.range f) hst) hf (fun g v => rfl) hi
      (LinearMap.exact_map_mkQ_range f) (LinearMap.range f).mkQ_surjective n (hb V ρ).2 (hb _ _).2 h).1
  · have hst : ∀ g, LinearMap.ker f ≤ (LinearMap.ker f).comap (ρ g) := by
      intro g v hv
      rw [Submodule.mem_comap, LinearMap.mem_ker, hf, LinearMap.mem_ker.1 hv, map_zero]
    exact (of_exact a (ρ₀ := ρ.subrepresentation (LinearMap.ker f) hst) (fun g v => rfl) hf
      (LinearMap.ker f).injective_subtype (LinearMap.exact_subtype_ker_map f) hs n (hb _ _).2 (hb V' ρ').2 h).2

end Generic

private theorem bound {G H Q K B : Type} [Group G] [Group H] [Field Q] [Field K] [Algebra Q K] [CommRing B]
    [IsDomain B] [Algebra Q B] [Algebra K B] [IsScalarTower Q K B] [FiniteDimensional Q K]
    (e : G ≃* H) (act : H →* (B ≃ₐ[K] B))
    (hreg : ∀ b b' : B, b ≠ 0 → (∀ g, b * act g b' = act g b * b') → ∃ c : K, b' = algebraMap K B c * b)
    (a : G → B →ₗ[Q] B) (ha : ∀ g b, a g b = act (e g) b)
    (W : Type) [AddCommGroup W] [Module Q W] [FiniteDimensional Q W] (σ : Representation Q G W) :
    Module.Finite Q (invT a σ) ∧ finrank Q (invT a σ) ≤ finrank Q K * finrank Q W := by
  have h := GlobalTheory.Per.FontaineBound.finite_finrank_le_base (Qp := Q) (act.comp e.toMonoidHom)
    (fun b b' hb h => hreg b b' hb fun g => by simpa using h (e.symm g)) σ
  have : a = fun g => ((act.comp e.toMonoidHom g).toAlgHom.toLinearMap).restrictScalars Q :=
    funext fun g => LinearMap.ext fun b => ha g b
  subst this
  exact h

theorem UpperTheory.V.Loc.isCrys_isDR_sub_quot :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {A : Type} [CommRing A] [Algebra ℚ_[l] A] {A' : Type} [CommRing A'] [Algebra ℚ_[l] A'] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] {V' : Type} [AddCommGroup V'] [Module A' V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] A' V'] [FiniteDimensional ℚ_[l] V'] [TopologicalSpace V'] [IsModuleTopology ℚ_[l] V'] [IsTopologicalAddGroup V'] [ContinuousConstSMul A' V'] (ρ : Representation A G V) (ρ' : Representation A' G V'), ContAction ρ → ContAction ρ' → ∀ f : V →ₗ[ℚ_[l]] V', (∀ g x, f (ρ g x) = ρ' g (f x)) → (Function.Injective f → (IsCr φ ρ' → IsCr φ ρ) ∧ (IsDr φ ρ' → IsDr φ ρ)) ∧ (Function.Surjective f → (IsCr φ ρ → IsCr φ ρ') ∧ (IsDr φ ρ → IsDr φ ρ')) := by
  intro l _ G _ _ _ φ hφ A _ _ A' _ _ V _ _ _ _ _ _ _ _ _ V' _ _ _ _ _ _ _ _ _ ρ ρ' _ _ f hf
  obtain ⟨K, e, -, -, he, -, hK, hK0⟩ := openField φ hφ
  obtain ⟨T⟩ := tiedP l
  have hF := GlobalTheory.Per.FontaineBound.isField_of_tied T
  have := GlobalTheory.Per.FontaineBound.isDomain_cris ((PP l).PD K) hF
  have := hF.isDomain
  have := ((PP l).PD K).finK₀
  have := K.2
  have hφe : ∀ g, φ g = (e g : GQ l) := fun g => by rw [← he]; rfl
  have hc := sub_quot (fun g => ((PP l).actQ (φ g)).toLinearMap) _
    (bound e ((PP l).PD K).actB (fun b b' hb h =>
      GlobalTheory.Per.FracInv.tied_frac_invariant l (PP l) (AIP l) T K b' b hb fun g hg => by
        have h1 := h ⟨g, hg⟩
        rw [(PP l).PD_actB, (PP l).PD_actB] at h1
        rw [mul_comm, h1, mul_comm]) _ fun g b => by rw [(PP l).PD_actB, hφe]; rfl)
    (ρ := resCoef ℚ_[l] ρ) (ρ' := resCoef ℚ_[l] ρ') (f := f) hf
  have hd := sub_quot (fun g => ((PP l).actQdR (φ g)).toLinearMap) _
    (bound e ((PP l).PD K).actdR (GlobalTheory.Per.FontaineBound.frac_dR ((PP l).PD K) hF) _
      fun g b => by rw [(PP l).PD_actdR, hφe]; rfl)
    (ρ := resCoef ℚ_[l] ρ) (ρ' := resCoef ℚ_[l] ρ') (f := f) hf
  unfold IsCr IsDr
  rw [hK, hK0]
  exact ⟨fun h => ⟨hc.1 h, hd.1 h⟩, fun h => ⟨hc.2 h, hd.2 h⟩⟩
