import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CharPolyRootsConstruction
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharpolyBlockAndInvariantUnderStabilizerNilradic

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal TensorProduct

noncomputable section
namespace GlobalTheory.ConsCompare

theorem map_algebraMap_padic : ∀ (p : ℕ) [Fact p.Prime] (A B : Type) [CommRing A] [Algebra ℤ_[p] A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra ℤ_[p] B] [Module.Finite ℤ_[p] B] (φ : A →+* B) (a : ℤ_[p]), φ (algebraMap ℤ_[p] A a) = algebraMap ℤ_[p] B a := by
  intro p _ A B _ _ _ _ _ _ _ φ a
  have hp : (p : B) ∈ IsLocalRing.maximalIdeal B := by
    have hm := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := ℤ_[p]) (IsLocalRing.maximalIdeal B)
    have : (p : ℤ_[p]) ∈ (IsLocalRing.maximalIdeal B).comap (algebraMap ℤ_[p] B) := by
      rw [IsLocalRing.eq_maximalIdeal hm, PadicInt.maximalIdeal_eq_span_p]
      exact Ideal.mem_span_singleton_self _
    simpa using this
  rw [← sub_eq_zero, ← Ideal.mem_bot,
    ← Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal B) (IsLocalRing.maximalIdeal.isMaximal B).ne_top,
    Ideal.mem_iInf]
  intro n
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n a)
  have : a = y * (p : ℤ_[p]) ^ n + (a.appr n : ℤ_[p]) := by rw [hy]; ring
  rw [this]
  simp only [map_add, map_mul, map_pow, map_natCast, add_sub_add_right_eq_sub, ← sub_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hp n)

theorem autCongr_continuous_cyc_inertia : ∀ (E Ω Ω₁ : Type) [Field E] [NumberField E] [Field Ω] [Field Ω₁] [Algebra E Ω] [Algebra E Ω₁] [IsAlgClosure E Ω] [IsAlgClosure E Ω₁] (σ : Ω ≃ₐ[E] Ω₁), Continuous (fun g : G E Ω => (AlgEquiv.autCongr σ g : G E Ω₁)) ∧ (∀ (p : ℕ) [Fact p.Prime] (g : G E Ω), cycZ E Ω₁ p (AlgEquiv.autCongr σ g) = cycZ E Ω p g) ∧ ∀ (A : ValuationSubring Ω) (A₁ : ValuationSubring Ω₁), (∀ y, σ y ∈ A₁ ↔ y ∈ A) → ∀ g : G E Ω, g ∈ Ine (F := E) A → (AlgEquiv.autCongr σ g : G E Ω₁) ∈ Ine (F := E) A₁ := by
  intro E Ω Ω₁ _ _ _ _ _ _ _ _ σ
  refine ⟨?_, fun p _ g => ?_, fun A A₁ hA g hg => ?_⟩
  · apply continuous_of_continuousAt_one (AlgEquiv.autCongr σ).toMonoidHom
    intro s hs
    rw [map_one, krullTopology_mem_nhds_one_iff] at hs
    obtain ⟨F, hF, hs⟩ := hs
    rw [Filter.mem_map, krullTopology_mem_nhds_one_iff]
    refine ⟨F.map σ.symm.toAlgHom,
      (IntermediateField.equivMap F σ.symm.toAlgHom).toLinearEquiv.finiteDimensional, fun g hg => hs ?_⟩
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hg ⊢
    intro x hx
    have := hg (σ.symm x) ⟨x, hx, rfl⟩
    show σ (g (σ.symm x)) = x
    rw [this, σ.apply_symm_apply]
  · have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
    have : IsAlgClosed Ω₁ := IsAlgClosure.isAlgClosed E
    have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
    have : CharZero Ω₁ := charZero_of_injective_algebraMap (algebraMap E Ω₁).injective
    have : NeZero ((p : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
    have : NeZero ((p : ℕ) : Ω₁) := ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
    apply Units.ext
    refine PadicInt.ext_of_toZModPow.mp fun n => ?_
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (p ^ n)
    have hζ' : IsPrimitiveRoot (σ ζ) (p ^ n) := hζ.map_of_injective σ.injective
    have h1 : g ζ = ζ ^ (PadicInt.toZModPow n ((cycZ E Ω p g : ℤ_[p]ˣ) : ℤ_[p])).val :=
      cyclotomicCharacter.spec (L := Ω) p (MulSemiringAction.toRingAut (G E Ω) Ω g) ζ hζ.pow_eq_one
    have h2 : σ (g (σ.symm (σ ζ))) = σ ζ ^ (PadicInt.toZModPow n
        ((cycZ E Ω₁ p (AlgEquiv.autCongr σ g) : ℤ_[p]ˣ) : ℤ_[p])).val :=
      cyclotomicCharacter.spec (L := Ω₁) p
        (MulSemiringAction.toRingAut (G E Ω₁) Ω₁ (AlgEquiv.autCongr σ g)) (σ ζ) hζ'.pow_eq_one
    rw [σ.symm_apply_apply, h1, map_pow] at h2
    apply ZMod.val_injective
    exact (hζ'.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h2).symm
  · have hv : ∀ y, A₁.valuation (σ y) < 1 ↔ A.valuation y < 1 := fun y => by
      rw [valuation_lt_one_iff', valuation_lt_one_iff', hA, ← map_inv₀, hA, map_eq_zero_iff _ σ.injective]
    refine ⟨?_, fun x hx => ?_⟩
    · show AlgEquiv.autCongr σ g ∈ Dec (F := E) A₁
      rw [mem_Dec]
      ext y
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      obtain ⟨z, rfl⟩ := σ.surjective y
      have : (AlgEquiv.autCongr σ g)⁻¹ • σ z = σ ((g⁻¹ : G E Ω) z) := by
        rw [← map_inv]
        show σ ((g⁻¹ : G E Ω) (σ.symm (σ z))) = _
        rw [σ.symm_apply_apply]
      rw [this, hA, hA]
      exact apply_mem_iff_of_mem_Dec ((Dec (F := E) A).inv_mem hg.1) z
    · obtain ⟨z, rfl⟩ := σ.surjective x
      have : (AlgEquiv.autCongr σ g) (σ z) - σ z = σ (g z - z) := by
        rw [map_sub]
        show σ (g (σ.symm (σ z))) - _ = _
        rw [σ.symm_apply_apply]
      rw [this, hv]
      apply hg.2
      rwa [ValuationSubring.valuation_le_one_iff, hA, ← ValuationSubring.valuation_le_one_iff] at hx

theorem isLocalRing_span_image : ∀ (O B X : Type) [CommRing O] [IsLocalRing O] [CommRing B] [IsLocalRing B] [Algebra O B] [IsLocalHom (algebraMap O B)] [Finite X] [Nonempty X] (T : Subalgebra O (X → O)) (T₁ : Subalgebra B (X → B)), IsLocalRing T → Subalgebra.toSubmodule T₁ = Submodule.span B ((fun (f : X → O) (x : X) => algebraMap O B (f x)) '' (T : Set (X → O))) → IsLocalRing T₁ := by
  intro O B X _ _ _ _ _ _ _ _ T T₁ hT hs
  obtain ⟨x₀⟩ := ‹Nonempty X›
  have h0 : ∀ f ∈ T, ∀ x, f x - f x₀ ∈ IsLocalRing.maximalIdeal O := by
    intro f hf x
    by_contra hx
    let u : T := ⟨f, hf⟩ - algebraMap O T (f x₀)
    let v : T := algebraMap O T (f x) - ⟨f, hf⟩
    have huv : IsUnit (u + v) := by
      have : u + v = algebraMap O T (f x - f x₀) := by simp [u, v]
      rw [this]
      exact (IsLocalRing.notMem_maximalIdeal.1 hx).map _
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add huv with h | h
    · have := h.map ((Pi.evalRingHom (fun _ : X => O) x₀).comp T.val.toRingHom)
      simp [u] at this
    · have := h.map ((Pi.evalRingHom (fun _ : X => O) x).comp T.val.toRingHom)
      simp [v] at this
  have h1 : ∀ f ∈ T₁, ∀ x, f x - f x₀ ∈ IsLocalRing.maximalIdeal B := by
    intro f hf x
    rw [← Subalgebra.mem_toSubmodule, hs] at hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨g, hg, rfl⟩ := hf
      show algebraMap O B _ - algebraMap O B _ ∈ _
      rw [← map_sub]
      exact IsLocalRing.map_maximalIdeal_le _ (Ideal.mem_map_of_mem _ (h0 g hg x))
    | zero => simp
    | add f g _ _ hf hg =>
      have := Ideal.add_mem _ hf hg
      simp only [Pi.add_apply]
      rwa [← add_sub_add_comm] at this
    | smul b f _ hf =>
      have := Ideal.mul_mem_left _ b hf
      simp only [Pi.smul_apply, smul_eq_mul]
      rwa [mul_sub] at this
  have hint : Algebra.IsIntegral T₁ (X → B) := Algebra.IsIntegral.tower_top (R := B)
  have hl : IsLocalHom (algebraMap T₁ (X → B)) := Algebra.IsIntegral.isLocalHom T₁ (X → B)
  have hu : ∀ f : T₁, IsUnit ((f : X → B) x₀) → IsUnit f := fun f hf => by
    refine hl.map_nonunit f (Pi.isUnit_iff.2 fun x => ?_)
    by_contra hx
    have := Ideal.sub_mem _ ((IsLocalRing.mem_maximalIdeal _).2 hx) (h1 f f.2 x)
    exact (IsLocalRing.mem_maximalIdeal _).1 (by simpa using this) hf
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun f => ?_
  exact (IsLocalRing.isUnit_or_isUnit_one_sub_self ((f : X → B) x₀)).imp (hu f) (hu (1 - f))

theorem exists_semilinear_baseChange : ∀ (O B M : Type) [CommRing O] [IsDomain O] [CommRing B] [IsDomain B] [Algebra O B] [AddCommGroup M] [Module O M] (κ : FractionRing O →+* FractionRing B), (∀ a : O, κ (algebraMap O (FractionRing O) a) = algebraMap B (FractionRing B) (algebraMap O B a)) → ∃ ι : (FractionRing O ⊗[O] M) →ₛₗ[κ] (FractionRing B ⊗[B] (B ⊗[O] M)), (∀ S : Set (FractionRing O ⊗[O] M), Submodule.span (FractionRing O) S = ⊤ → Submodule.span (FractionRing B) (ι '' S) = ⊤) ∧ ∀ S : Set (FractionRing O ⊗[O] M), Submodule.span O S = LinearMap.range (TensorProduct.mk O (FractionRing O) M 1) → Submodule.span B (ι '' S) = LinearMap.range (TensorProduct.mk B (FractionRing B) (B ⊗[O] M) 1) := by
  intro O B M _ _ _ _ _ _ _ κ hκ
  let F : FractionRing O →+ M →+ FractionRing B ⊗[B] (B ⊗[O] M) :=
    { toFun := fun k =>
        { toFun := fun m => κ k ⊗ₜ (1 ⊗ₜ m), map_zero' := by simp
          map_add' := fun _ _ => by simp [tmul_add] }
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp [add_tmul] }
  have hsm : ∀ (a : O) (l : FractionRing B) (m : M), (l ⊗ₜ[B] ((1 : B) ⊗ₜ[O] (a • m)) :
      FractionRing B ⊗[B] (B ⊗[O] M)) = algebraMap O B a • l ⊗ₜ[B] ((1 : B) ⊗ₜ[O] m) := fun a l m => by
    rw [tmul_smul a (1 : B) m, ← algebraMap_smul B a, tmul_smul]
  let ι₀ := TensorProduct.liftAddHom (R := O) F fun a k m => by
    show κ (a • k) ⊗ₜ _ = κ k ⊗ₜ _
    rw [hsm, smul_tmul', Algebra.smul_def, Algebra.smul_def, map_mul, hκ]
  have hι : ∀ k m, ι₀ (k ⊗ₜ m) = κ k ⊗ₜ (1 ⊗ₜ m) := fun _ _ => rfl
  let ι : (FractionRing O ⊗[O] M) →ₛₗ[κ] (FractionRing B ⊗[B] (B ⊗[O] M)) :=
    { toFun := ι₀, map_add' := ι₀.map_add
      map_smul' := fun c z => by
        induction z using TensorProduct.induction_on with
        | zero => simp
        | tmul k m => rw [smul_tmul', hι, hι, smul_tmul', smul_eq_mul, smul_eq_mul, map_mul]
        | add x y hx hy => rw [smul_add, map_add, map_add, smul_add, hx, hy] }
  have hι' : ∀ m, ι (1 ⊗ₜ m) = 1 ⊗ₜ (1 ⊗ₜ m) := fun m => (hι 1 m).trans (by rw [map_one])
  refine ⟨ι, fun S hS => ?_, fun S hS => ?_⟩
  · have h1 : ∀ z, ι z ∈ Submodule.span (FractionRing B) (ι '' S) := fun z => by
      have hz : z ∈ Submodule.span (FractionRing O) S := hS ▸ Submodule.mem_top
      induction hz using Submodule.span_induction with
      | mem z hz => exact Submodule.subset_span ⟨z, hz, rfl⟩
      | zero => simp
      | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
    rw [eq_top_iff]
    rintro z -
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => exact Submodule.add_mem _ hx hy
    | tmul l y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => rw [tmul_add]; exact Submodule.add_mem _ hx hy
      | tmul b m =>
        have : (l ⊗ₜ[B] (b ⊗ₜ[O] m) : FractionRing B ⊗[B] (B ⊗[O] M)) = (b • l) • ι (1 ⊗ₜ m) := by
          rw [hι', smul_tmul', smul_eq_mul, mul_one, smul_tmul, smul_tmul', smul_eq_mul, mul_one]
        rw [this]
        exact Submodule.smul_mem _ _ (h1 _)
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨m, rfl⟩ : z ∈ LinearMap.range (TensorProduct.mk O (FractionRing O) M 1) :=
        hS ▸ Submodule.subset_span hz
      exact ⟨1 ⊗ₜ m, (hι' m).symm⟩
    · have h1 : ∀ z ∈ Submodule.span O S, ι z ∈ Submodule.span B (ι '' S) := fun z hz => by
        induction hz using Submodule.span_induction with
        | mem z hz => exact Submodule.subset_span ⟨z, hz, rfl⟩
        | zero => simp
        | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
        | smul c x _ hx =>
          rw [← algebraMap_smul (FractionRing O), map_smulₛₗ, hκ, algebraMap_smul]
          exact Submodule.smul_mem _ _ hx
      rintro _ ⟨y, rfl⟩
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
      | tmul b m =>
        have : TensorProduct.mk B (FractionRing B) (B ⊗[O] M) 1 (b ⊗ₜ[O] m) = b • ι (1 ⊗ₜ m) := by
          rw [hι', ← tmul_smul, smul_tmul', smul_eq_mul, mul_one]
          rfl
        rw [this]
        exact Submodule.smul_mem _ _ (h1 _ (hS ▸ ⟨m, rfl⟩))

theorem one_tmul_injective (O B M : Type) [CommRing O] [CommRing B] [Algebra O B] [AddCommGroup M]
    [Module O M] [Module.Flat O M] (h : Function.Injective (algebraMap O B)) :
    Function.Injective (TensorProduct.mk O B M 1) := by
  have h1 := (Module.Flat.rTensor_preserves_injective_linearMap (M := M) (Algebra.linearMap O B) h).comp
    (TensorProduct.lid O M).symm.injective
  intro a b hab
  apply h1
  simpa using hab

theorem heckeEig_baseChange_ne_bot : ∀ (O B X M : Type) [CommRing O] [IsDomain O] [CommRing B] [IsDomain B] [Algebra O B] [AddCommGroup M] [Module O M] [Module.Free O M] [Module.Finite O M] (T : Subalgebra O (X → O)) (T₁ : Subalgebra B (X → B)) (act : T →ₐ[O] Module.End O M) (act₁ : T₁ →ₐ[B] Module.End B (B ⊗[O] M)), Function.Injective (algebraMap O B) → Subalgebra.toSubmodule T₁ = Submodule.span B ((fun (f : X → O) (x : X) => algebraMap O B (f x)) '' (T : Set (X → O))) → (∀ (f : T) (f₁ : T₁), (∀ x, (f₁ : X → B) x = algebraMap O B ((f : X → O) x)) → act₁ f₁ = (act f).baseChange B) → ∀ x : X, heckeEig T act x ≠ ⊥ → heckeEig T₁ act₁ x ≠ ⊥ := by
  intro O B X M _ _ _ _ _ _ _ _ _ T T₁ act act₁ hinj hs hac x hx
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hx
  obtain ⟨⟨m, s⟩, hms⟩ := IsLocalizedModule.surj (nonZeroDivisors O) (TensorProduct.mk O (FractionRing O) M 1) v
  have hs0 : algebraMap O (FractionRing O) (s : O) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  have hms' : algebraMap O (FractionRing O) (s : O) • v = TensorProduct.mk O (FractionRing O) M 1 m := by
    rw [algebraMap_smul]
    exact hms
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [map_zero] at hms'
    exact hv0 ((smul_eq_zero.1 hms').resolve_left hs0)
  have hm : ∀ f : T, act f m = (f : X → O) x • m := fun f => by
    have h1 := (Submodule.mem_iInf _).1 (hms' ▸ Submodule.smul_mem _ _ hv) f
    rw [Module.End.mem_eigenspace_iff, algebraMap_smul] at h1
    apply one_tmul_injective O (FractionRing O) M (IsFractionRing.injective O _)
    rw [map_smul, ← h1]
    rfl
  have h1 : ∀ g (hg : g ∈ Submodule.span B ((fun (f : X → O) (x : X) => algebraMap O B (f x)) ''
      (T : Set (X → O)))) (hg' : g ∈ T₁), act₁ ⟨g, hg'⟩ (1 ⊗ₜ m) = g x • (1 ⊗ₜ m) := fun g hg => by
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨f, hf, rfl⟩ := hg
      intro hg'
      rw [hac ⟨f, hf⟩ _ fun _ => rfl, LinearMap.baseChange_tmul, hm, tmul_smul, algebraMap_smul]
    | zero =>
      intro hg'
      have : (⟨0, hg'⟩ : T₁) = 0 := rfl
      simp [this]
    | add f g hf hg ihf ihg =>
      intro hg'
      rw [← hs] at hf hg
      have : (⟨f + g, hg'⟩ : T₁) = ⟨f, hf⟩ + ⟨g, hg⟩ := rfl
      rw [this, map_add, LinearMap.add_apply, ihf, ihg, Pi.add_apply, add_smul]
    | smul b f hf ih =>
      intro hg'
      rw [← hs] at hf
      have : (⟨b • f, hg'⟩ : T₁) = b • ⟨f, hf⟩ := rfl
      rw [this, map_smul, LinearMap.smul_apply, ih, Pi.smul_apply, smul_assoc]
  refine (Submodule.ne_bot_iff _).2 ⟨1 ⊗ₜ (1 ⊗ₜ m), (Submodule.mem_iInf _).2 fun f => ?_, fun h => hm0 ?_⟩
  · rw [Module.End.mem_eigenspace_iff, LinearMap.baseChange_tmul, h1 f.1 (hs ▸ f.2) f.2, tmul_smul,
      algebraMap_smul]
  · apply one_tmul_injective O B M hinj
    apply one_tmul_injective B (FractionRing B) _ (IsFractionRing.injective B _)
    simpa using h

theorem exists_act_baseChange : ∀ (O B X M : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing B] [IsDomain B] [Algebra O B] [Finite X] [AddCommGroup M] [Module O M] [Module.Free O M] [Module.Finite O M] (T : Subalgebra O (X → O)) (T₁ : Subalgebra B (X → B)) (act : T →ₐ[O] Module.End O M), Function.Injective (algebraMap O B) → Subalgebra.toSubmodule T₁ = Submodule.span B ((fun (f : X → O) (x : X) => algebraMap O B (f x)) '' (T : Set (X → O))) → Function.Injective act → ∃ act₁ : T₁ →ₐ[B] Module.End B (B ⊗[O] M), Function.Injective act₁ ∧ ∀ (f : T) (f₁ : T₁), (∀ x, (f₁ : X → B) x = algebraMap O B ((f : X → O) x)) → act₁ f₁ = (act f).baseChange B := by
  intro O B X M _ _ _ _ _ _ _ _ _ _ _ T T₁ act hinj hs hact
  classical
  have := Fintype.ofFinite X
  have : FaithfulSMul O B := (faithfulSMul_iff_algebraMap_injective O B).2 hinj
  have : Module.Flat O B := inferInstance
  let g : T →ₐ[O] (X → B) := ((Algebra.ofId O B).compLeft X).comp T.val
  let F : B ⊗[O] T →ₐ[B] (X → B) := Algebra.TensorProduct.lift (Algebra.ofId B _) g fun _ _ => Commute.all _ _
  have hF : ∀ b f, F (b ⊗ₜ f) = b • fun x => algebraMap O B ((f : X → O) x) := fun b f => by
    rw [Algebra.smul_def]
    rfl
  have hFi : Function.Injective F := by
    have h1 := (TensorProduct.piScalarRight O O B X).injective.comp
      (Module.Flat.lTensor_preserves_injective_linearMap (M := B) T.val.toLinearMap Subtype.val_injective)
    have : ⇑F = ⇑(TensorProduct.piScalarRight O O B X) ∘ ⇑(T.val.toLinearMap.lTensor B) := funext fun z => by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [Function.comp_apply, map_add] at hx hy ⊢; rw [hx, hy]
      | tmul b f =>
        rw [hF]
        funext x
        simp [Algebra.smul_def, mul_comm]
    rwa [this]
  have hFr : F.range = T₁ := by
    apply Subalgebra.toSubmodule_injective
    rw [hs]
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      show F z ∈ _
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
      | tmul b f => rw [hF]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨f, f.2, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨f, hf, rfl⟩
      exact ⟨1 ⊗ₜ ⟨f, hf⟩, (hF 1 _).trans (one_smul _ _)⟩
  let G : B ⊗[O] T →ₐ[B] Module.End B (B ⊗[O] M) := Algebra.TensorProduct.lift (Algebra.ofId B _)
    ((Module.End.baseChangeHom O B M).comp act) fun b _ => Algebra.commutes b _
  have hG : ∀ b f, G (b ⊗ₜ f) = b • (act f).baseChange B := fun b f => by
    rw [Algebra.smul_def]
    rfl
  have hGi : Function.Injective G := by
    let e := Module.finBasis O M
    let Φ : T →ₗ[O] (Fin (Module.finrank O M) → M) :=
      LinearMap.pi fun j => (LinearMap.applyₗ (e j)).comp act.toLinearMap
    have hΦ : Function.Injective Φ := fun f f' h => hact (e.ext fun j => congrFun h j)
    have h1 := (TensorProduct.piRight O O B fun _ : Fin (Module.finrank O M) => M).injective.comp
      (Module.Flat.lTensor_preserves_injective_linearMap (M := B) Φ hΦ)
    have h2 : ∀ z j, TensorProduct.piRight O O B (fun _ : Fin (Module.finrank O M) => M) (Φ.lTensor B z) j =
        G z (1 ⊗ₜ e j) := fun z j => by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, Pi.add_apply, LinearMap.add_apply, hx, hy]
      | tmul b f => simp [hG, Φ, smul_tmul']
    intro z z' h
    apply h1
    funext j
    simp only [Function.comp_apply, h2, h]
  let e : B ⊗[O] T ≃ₐ[B] T₁ := (AlgEquiv.ofInjective F hFi).trans (Subalgebra.equivOfEq _ _ hFr)
  refine ⟨G.comp e.symm.toAlgHom, hGi.comp e.symm.injective, fun f f₁ h => ?_⟩
  have : e.symm f₁ = 1 ⊗ₜ f := by
    rw [AlgEquiv.symm_apply_eq]
    apply Subtype.ext
    show _ = F (1 ⊗ₜ f)
    rw [hF, one_smul]
    exact funext h
  show G (e.symm f₁) = _
  rw [this, hG, one_smul]

section CharpolySeries
variable {k A : Type} [Field k] [Ring A] [Algebra k A]

def cpOn (k : Type) [Field k] [Algebra k A] (a : A) (M : Type) [AddCommGroup M] [Module k M] [Module A M]
    [IsScalarTower k A M] [FiniteDimensional k M] : Polynomial k :=
  LinearMap.charpoly (Algebra.lsmul k k M a)

variable (a : A) {M M' : Type} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  [FiniteDimensional k M] [AddCommGroup M'] [Module k M'] [Module A M'] [IsScalarTower k A M']
  [FiniteDimensional k M']

theorem cpOn_congr (e : M ≃ₗ[A] M') : cpOn k a M = cpOn k a M' := by
  unfold cpOn
  rw [← LinearEquiv.charpoly_conj (e.restrictScalars k)]
  congr 1
  ext v
  simp [LinearEquiv.conj_apply]

instance finiteDimensional_sub (N : Submodule A M) : FiniteDimensional k N :=
  inferInstanceAs (FiniteDimensional k (N.restrictScalars k))

theorem cpOn_sub_quot (N : Submodule A M) : cpOn k a M = cpOn k a N * cpOn k a (M ⧸ N) :=
  GlobalTheory.CuspGL.charpoly_eq_restrict_mul_mapQ (N.restrictScalars k) (Algebra.lsmul k k M a)
    fun _ hx => N.smul_mem a hx

theorem last_eq_mul_prod {P : Type} [CommMonoid P] : ∀ (n : ℕ) (u : Fin (n + 1) → P) (c : Fin n → P),
    (∀ j, u j.succ = u j.castSucc * c j) → u (Fin.last n) = u 0 * ∏ j, c j
  | 0, u, c, _ => by simp
  | n + 1, u, c, h => by
    have := last_eq_mul_prod n (fun j => u j.castSucc) (fun j => c j.castSucc) fun j => h j.castSucc
    rw [Fin.prod_univ_castSucc, ← Fin.succ_last, h, this, mul_assoc]
    rfl

theorem cpOn_series (s : CompositionSeries (Submodule A M)) (h0 : s.head = ⊥) (h1 : s.last = ⊤) :
    cpOn k a M = ∏ j : Fin s.length,
      cpOn k a (↥(s j.succ) ⧸ (s j.castSucc).submoduleOf (s j.succ)) := by
  have := last_eq_mul_prod s.length (fun j => cpOn k a (s j)) _ fun j =>
    (cpOn_sub_quot a ((s j.castSucc).submoduleOf (s j.succ))).trans (congrArg (· * _)
      (cpOn_congr a (Submodule.submoduleOfEquivOfLe (s.step j).le)))
  have e1 : cpOn k a (s (Fin.last _)) = cpOn k a M :=
    cpOn_congr a (LinearEquiv.ofTop _ h1)
  have e0 : cpOn k a (s 0) = 1 := by
    have : Subsingleton (s 0) := by
      have h0' : s 0 = ⊥ := h0
      rw [h0']
      infer_instance
    unfold cpOn
    rw [← (LinearMap.charpoly_monic _).natDegree_eq_zero, LinearMap.charpoly_natDegree]
    exact Module.finrank_zero_of_subsingleton
  rw [← e1, this, e0, one_mul]

end CharpolySeries

theorem charpoly_eq_of_sameSS : ∀ (k Γ V W : Type) [Field k] [Group Γ] [AddCommGroup V] [Module k V] [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W] (ρ : Representation k Γ V) (σ : Representation k Γ W), GlobalTheory.IndefiniteRowSideFullHecke.CharPolyRootsConstruction.SameSS ρ σ → ∀ g : Γ, LinearMap.charpoly (ρ g) = LinearMap.charpoly (σ g) := by
  intro k Γ V W _ _ _ _ _ _ _ _ ρ σ ⟨s, t, h1, h2, h3, h4, f, hf⟩ g
  have : FiniteDimensional k ρ.asModule := inferInstanceAs (FiniteDimensional k V)
  have : FiniteDimensional k σ.asModule := inferInstanceAs (FiniteDimensional k W)
  have e1 : LinearMap.charpoly (ρ g) = cpOn k (MonoidAlgebra.of k Γ g) ρ.asModule := by
    unfold cpOn
    rw [← LinearEquiv.charpoly_conj ρ.asModuleEquiv]
    congr 1
    ext v
    simp [LinearEquiv.conj_apply]
    rfl
  have e2 : LinearMap.charpoly (σ g) = cpOn k (MonoidAlgebra.of k Γ g) σ.asModule := by
    unfold cpOn
    rw [← LinearEquiv.charpoly_conj σ.asModuleEquiv]
    congr 1
    ext v
    simp [LinearEquiv.conj_apply]
    rfl
  rw [e1, e2, cpOn_series _ s h1 h2, cpOn_series _ t h3 h4]
  exact Fintype.prod_equiv f _ _ fun j => cpOn_congr _ (hf j).some

end GlobalTheory.ConsCompare
end
