import Mathlib
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CentralProducts.TopProdD
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralCharacterEqProdSupercuspidalSupport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProductTwoRepsEquivTwoBlockInduction

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir.Leib
open scoped TensorProduct

namespace PositivityTheory.RgUd.Prod.Eig

section Lin

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem sub_injective (f : Module.End ℂ V) (α : ℂ) (h : ∀ a : V, f a = α • a → a = 0) :
    Function.Injective (f - α • (LinearMap.id : V →ₗ[ℂ] V)) := by
  refine (injective_iff_map_eq_zero _).2 fun a ha => h a ?_
  simpa [sub_eq_zero] using ha

theorem exists_fin (S : Module.End ℂ V) (T : Module.End ℂ W)
    (hA : ∀ a : V, ∃ U : Submodule ℂ V, FiniteDimensional ℂ U ∧ a ∈ U ∧ ∀ u ∈ U, S u ∈ U)
    (hB : ∀ b : W, ∃ U : Submodule ℂ W, FiniteDimensional ℂ U ∧ b ∈ U ∧ ∀ u ∈ U, T u ∈ U)
    (y : V ⊗[ℂ] W) : ∃ (U₁ : Submodule ℂ V) (U₂ : Submodule ℂ W), FiniteDimensional ℂ U₁ ∧
      FiniteDimensional ℂ U₂ ∧ (∀ u ∈ U₁, S u ∈ U₁) ∧ (∀ u ∈ U₂, T u ∈ U₂) ∧
      y ∈ LinearMap.range (TensorProduct.map U₁.subtype U₂.subtype) := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨⊥, ⊥, inferInstance, inferInstance, by simp, by simp, zero_mem _⟩
  | tmul a b =>
    obtain ⟨U₁, h₁, ha, s₁⟩ := hA a
    obtain ⟨U₂, h₂, hb, s₂⟩ := hB b
    exact ⟨U₁, U₂, h₁, h₂, s₁, s₂, ⟨⟨a, ha⟩ ⊗ₜ ⟨b, hb⟩, by simp⟩⟩
  | add y z hy hz =>
    obtain ⟨U₁, U₂, h₁, h₂, s₁, s₂, my⟩ := hy
    obtain ⟨U₁', U₂', h₁', h₂', s₁', s₂', mz⟩ := hz
    have st : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] (F : Module.End ℂ M) (P Q : Submodule ℂ M),
        (∀ u ∈ P, F u ∈ P) → (∀ u ∈ Q, F u ∈ Q) → ∀ u ∈ P ⊔ Q, F u ∈ P ⊔ Q := by
      intro M _ _ F P Q hP hQ u hu
      obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 hu
      rw [map_add]
      exact Submodule.add_mem_sup (hP p hp) (hQ q hq)
    have mono : ∀ (P P' : Submodule ℂ V) (Q Q' : Submodule ℂ W), P ≤ P' → Q ≤ Q' →
        LinearMap.range (TensorProduct.map P.subtype Q.subtype) ≤
          LinearMap.range (TensorProduct.map P'.subtype Q'.subtype) := by
      intro P P' Q Q' hP hQ
      have : TensorProduct.map P.subtype Q.subtype =
          TensorProduct.map P'.subtype Q'.subtype ∘ₗ
            TensorProduct.map (Submodule.inclusion hP) (Submodule.inclusion hQ) := by
        rw [← TensorProduct.map_comp]; rfl
      rw [this]
      exact LinearMap.range_comp_le_range _ _
    exact ⟨U₁ ⊔ U₁', U₂ ⊔ U₂', inferInstance, inferInstance, st S _ _ s₁ s₁', st T _ _ s₂ s₂',
      add_mem (mono _ _ _ _ le_sup_left le_sup_left my) (mono _ _ _ _ le_sup_right le_sup_right mz)⟩

theorem tensor_eig (S : Module.End ℂ V) (T : Module.End ℂ W) (hS : Function.Injective S)
    (U₁ : Submodule ℂ V) (U₂ : Submodule ℂ W) [FiniteDimensional ℂ U₁] [FiniteDimensional ℂ U₂]
    (h₁ : ∀ u ∈ U₁, S u ∈ U₁)
    (y : V ⊗[ℂ] W) (hy : y ∈ LinearMap.range (TensorProduct.map U₁.subtype U₂.subtype))
    (hy0 : y ≠ 0) (c : ℂ) (hc : TensorProduct.map S T y = c • y) :
    ∃ α β : ℂ, c = α * β ∧ (∃ a : V, a ≠ 0 ∧ S a = α • a) ∧ ∃ b : W, b ≠ 0 ∧ T b = β • b := by
  set R := LinearMap.range (TensorProduct.map U₁.subtype U₂.subtype) with hR
  set S' := LinearMap.rTensor W S with hS'
  set T' := LinearMap.lTensor V T with hT'
  set P := TensorProduct.map S T with hP
  have hPST : ∀ z, P z = S' (T' z) := fun z => by
    rw [hP, hS', hT', ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor]
  have hPS : ∀ z, P (S' z) = S' (P z) := fun z => by
    have : P ∘ₗ S' = S' ∘ₗ P := TensorProduct.ext' fun a b => by simp [hP, hS']
    exact LinearMap.congr_fun this z
  have hRS : ∀ z ∈ R, S' z ∈ R := by
    rintro _ ⟨z, rfl⟩
    refine ⟨TensorProduct.map (S.restrict h₁) LinearMap.id z, ?_⟩
    have : TensorProduct.map U₁.subtype U₂.subtype ∘ₗ TensorProduct.map (S.restrict h₁) LinearMap.id =
        S' ∘ₗ TensorProduct.map U₁.subtype U₂.subtype :=
      TensorProduct.ext' fun a b => by simp [hS', LinearMap.restrict_apply]
    exact LinearMap.congr_fun this z
  let E : Submodule ℂ (V ⊗[ℂ] W) := R ⊓ LinearMap.ker (P - c • LinearMap.id)
  have memE : ∀ z, z ∈ E ↔ z ∈ R ∧ P z = c • z := fun z => by
    simp [E, sub_eq_zero]
  have hES : ∀ z ∈ E, S' z ∈ E := fun z hz => by
    rw [memE] at hz ⊢
    exact ⟨hRS z hz.1, by rw [hPS, hz.2, map_smul]⟩
  have : FiniteDimensional ℂ R := LinearMap.finiteDimensional_range _
  have : FiniteDimensional ℂ E := Submodule.finiteDimensional_of_le inf_le_left
  have hyE : y ∈ E := (memE y).2 ⟨hy, hc⟩
  have : Nontrivial E := ⟨⟨⟨y, hyE⟩, 0, fun h => hy0 (congrArg Subtype.val h)⟩⟩
  obtain ⟨α, hα⟩ := Module.End.exists_eigenvalue (S'.restrict hES)
  obtain ⟨v, hv⟩ := hα.exists_hasEigenvector
  have hv1 : S' v.1 = α • v.1 := by
    have := Module.End.mem_eigenspace_iff.1 hv.1
    exact congrArg Subtype.val this
  have hv0 : v.1 ≠ 0 := fun h => hv.2 (Subtype.ext h)
  have hv2 : P v.1 = c • v.1 := ((memE _).1 v.2).2
  have hS'inj : Function.Injective S' := Module.Flat.rTensor_preserves_injective_linearMap S hS
  have hα0 : α ≠ 0 := by
    rintro rfl
    exact hv0 (hS'inj (by rw [hv1, zero_smul, map_zero]))
  have hT1 : T' v.1 = (c / α) • v.1 := by
    apply hS'inj
    rw [← hPST, hv2, map_smul, hv1, smul_smul, div_mul_cancel₀ _ hα0]
  refine ⟨α, c / α, (mul_div_cancel₀ _ hα0).symm, ?_, ?_⟩
  · by_contra hno
    push Not at hno
    have hinj := sub_injective S α fun a ha => by
      by_contra h0; exact hno a h0 ha
    have h3 := Module.Flat.rTensor_preserves_injective_linearMap (M := W) _ hinj
    have h4 : LinearMap.rTensor W (S - α • LinearMap.id) v.1 = 0 := by
      rw [LinearMap.rTensor_sub, LinearMap.rTensor_smul, LinearMap.rTensor_id, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.id_apply, ← hS', hv1, sub_self]
    exact hv0 (h3 (by rw [h4, map_zero]))
  · by_contra hno
    push Not at hno
    have hinj := sub_injective T (c / α) fun b hb => by
      by_contra h0; exact hno b h0 hb
    have h3 := Module.Flat.lTensor_preserves_injective_linearMap (M := V) _ hinj
    have h4 : LinearMap.lTensor V (T - (c / α) • LinearMap.id) v.1 = 0 := by
      rw [LinearMap.lTensor_sub, LinearMap.lTensor_smul, LinearMap.lTensor_id, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.id_apply, ← hT', hT1, sub_self]
    exact hv0 (h3 (by rw [h4, map_zero]))

end Lin

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eigProd : EigProd k := by
  intro r t A B _ _ hA hB x c f hf hfc
  have hinj : ∀ {n : ℕ} (C : GRep k n), Function.Injective (C.ρ (sc n x)) := fun {n} C => by
    refine Function.LeftInverse.injective (g := C.ρ (sc n x⁻¹)) fun a => ?_
    rw [← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one, Module.End.one_apply]
  have h1 : leviEmb k (two (stdSum (rfl : r + t = r + t)))
      (fun a => GeneralLinearGroup.scalar (Two (Fin r) (Fin t) a) x) = sc (r + t) x := by
    ext i j
    obtain ⟨⟨b, y⟩, rfl⟩ := (two (stdSum (rfl : r + t = r + t))).surjective i
    obtain ⟨⟨b', y'⟩, rfl⟩ := (two (stdSum (rfl : r + t = r + t))).surjective j
    by_cases hb : b = b'
    · subst hb
      rw [leviEmb_apply_same]
      simp [GeneralLinearGroup.scalar, diagonal_apply]
    · rw [leviEmb_apply_ne _ _ _ hb]
      simp [hb]
  obtain ⟨g, hg⟩ : ∃ g, f.1.1 g ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (Subtype.ext (Subtype.ext (funext h)))
  have hc : f.1.1 (g * sc (r + t) x) = c • f.1.1 g := congrArg (fun F : (A.prod B).V => F.1.1 g) hfc
  have hcomm : g * sc (r + t) x = sc (r + t) x * g := by
    ext i j
    simp [mul_comm]
  have h5 := parInd_law (two (stdSum (rfl : r + t = r + t))) (piTensor (twoRep A.ρ B.ρ)) f
    ⟨_, leviEmb_mem_parab k _ (fun a => GeneralLinearGroup.scalar (Two (Fin r) (Fin t) a) x)⟩ g
  rw [leviProj_leviEmb, GlobalTheory.CentralSupport.deltaHalf_scalar] at h5
  have h6 : piTensor (twoRep A.ρ B.ρ) (fun a => GeneralLinearGroup.scalar (Two (Fin r) (Fin t) a) x) (f.1.1 g) =
      c • f.1.1 g := by
    have h7 : f.1.1 (leviEmb k (two (stdSum (rfl : r + t = r + t)))
        (fun a => GeneralLinearGroup.scalar (Two (Fin r) (Fin t) a) x) * g) = c • f.1.1 g := by
      rw [h1, ← hcomm]; exact hc
    rw [h5] at h7
    simpa using h7
  have htr : ∀ z, Exponents.boolTensorEquiv (X := TwoT A.V B.V)
      (piTensor (twoRep A.ρ B.ρ) (fun a => GeneralLinearGroup.scalar (Two (Fin r) (Fin t) a) x) z) =
      TensorProduct.map (A.ρ (sc r x)) (B.ρ (sc t x)) (Exponents.boolTensorEquiv (X := TwoT A.V B.V) z) := by
    intro z
    induction z using PiTensorProduct.induction_on with
    | add z w hz hw => rw [map_add, map_add, hz, hw, map_add, map_add]
    | smul_tprod s z =>
      rw [map_smul, map_smul, map_smul, map_smul, piTensor_tprod, Exponents.boolTensorEquiv_tprod,
        Exponents.boolTensorEquiv_tprod, TensorProduct.map_tmul]
      rfl
  set y := Exponents.boolTensorEquiv (X := TwoT A.V B.V) (f.1.1 g) with hy
  have hy0 : y ≠ 0 := by
    rw [hy]; exact (LinearEquiv.map_ne_zero_iff _).2 hg
  have hyc : TensorProduct.map (A.ρ (sc r x)) (B.ρ (sc t x)) y = c • y := by
    rw [hy, ← htr, h6, map_smul]
  obtain ⟨U₁, U₂, fd₁, fd₂, s₁, -, hmem⟩ := exists_fin (A.ρ (sc r x)) (B.ρ (sc t x))
    (fun a => by obtain ⟨U, h, ha, hs⟩ := hA a; exact ⟨U, h, ha, fun u hu => hs x u hu⟩)
    (fun b => by obtain ⟨U, h, hb, hs⟩ := hB b; exact ⟨U, h, hb, fun u hu => hs x u hu⟩) y
  exact tensor_eig _ _ (hinj A) U₁ U₂ s₁ y hmem hy0 c hyc

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem eigFilt : EigFilt k := by
  intro n V _ _ ρ ℓ F hF h0 hℓ x c v hv hvc
  classical
  have hex : ∃ j, v ∉ (F (j + 1)).toSubmodule := ⟨ℓ, by
    rw [hℓ]
    intro h
    exact hv ((Submodule.mem_bot ℂ).1 h)⟩
  set j := Nat.find hex with hjdef
  have hj : v ∉ (F (j + 1)).toSubmodule := Nat.find_spec hex
  have hvj : v ∈ (F j).toSubmodule := by
    rcases hjj : j with _ | j'
    · rw [h0]; exact Submodule.mem_top
    · have := Nat.find_min hex (show j' < Nat.find hex by omega)
      push Not at this
      exact this
  refine ⟨j, Nat.find_min' hex (show v ∉ (F (ℓ + 1)).toSubmodule from ?_), ?_⟩
  · rw [hℓ]; intro h; exact hv ((Submodule.mem_bot ℂ).1 h)
  refine ⟨Submodule.Quotient.mk ⟨v, hvj⟩, fun h => hj (Submodule.mem_comap.1 ((Submodule.Quotient.mk_eq_zero _).1 h)), ?_⟩
  rw [← Submodule.Quotient.mk_smul]
  show Submodule.Quotient.mk (⟨ρ (sc n x) v, _⟩ : (F j).toSubmodule) = _
  congr 1
  exact Subtype.ext hvc

end PositivityTheory.RgUd.Prod.Eig
