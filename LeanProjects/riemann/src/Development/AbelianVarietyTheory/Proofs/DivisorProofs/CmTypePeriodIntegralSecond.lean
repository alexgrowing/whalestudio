import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

namespace GlobalTheory.EigenLattice
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type} [Field K] [Algebra O K] [IsFractionRing O K]
variable {H : Type} [AddCommGroup H] [Module O H] {c : Ideal (OF E)}

theorem sat (ρ : orderC c →+* Module.End O H) (σ : E →+* K) : IsSat (eigLat ρ σ) := by
  intro x h hx hxh
  have hK : (algebraMap O K x) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hx
  show inK K H h ∈ eigK ρ σ
  have h1 : inK K H (x • h) ∈ eigK ρ σ := hxh
  rw [map_smul, ← algebraMap_smul K] at h1
  have := (eigK ρ σ).smul_mem (algebraMap O K x)⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ hK, one_smul] at this

theorem exists_ne_mem (ρ : orderC c →+* Module.End O H) (σ : E →+* K) (h1 : Module.finrank K (eigK ρ σ) = 1) :
    ∃ g : H, g ≠ 0 ∧ g ∈ eigLat ρ σ := by
  have : Nontrivial (eigK ρ σ) := Module.nontrivial_of_finrank_eq_succ h1
  obtain ⟨⟨v, hv⟩, hv0⟩ := _root_.exists_ne (0 : eigK ρ σ)
  have hv0' : v ≠ 0 := fun h => hv0 (by ext; simp [h])
  haveI : IsLocalizedModule (nonZeroDivisors O) (inK K H) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors O) K (inK K H)).2 (TensorProduct.isBaseChange O H K)
  obtain ⟨⟨h, s⟩, hs⟩ := IsLocalizedModule.surj (nonZeroDivisors O) (inK K H) v
  have hsK : algebraMap O K (s : O) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 (nonZeroDivisors.ne_zero s.2)
  have hs' : inK K H h = algebraMap O K (s : O) • v := by
    simp only at hs; rw [← hs, Submonoid.smul_def, algebraMap_smul]
  refine ⟨h, ?_, ?_⟩
  · intro h0; rw [h0, map_zero] at hs'; exact (smul_ne_zero hsK hv0') hs'.symm
  · show inK K H h ∈ eigK ρ σ
    rw [hs']; exact (eigK ρ σ).smul_mem _ hv

theorem finrank_le [Module.Free O H] [Module.Finite O H] (ρ : orderC c →+* Module.End O H) (σ : E →+* K)
    (h1 : Module.finrank K (eigK ρ σ) = 1) : Module.finrank O (eigLat ρ σ) ≤ 1 := by
  haveI : Module.Flat O K := IsLocalization.flat K (nonZeroDivisors O)
  haveI : Module.Finite K (eigK ρ σ) := Module.finite_of_finrank_eq_succ h1
  set N := eigLat ρ σ
  have hinj : Function.Injective (N.subtype.baseChange K) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ N.injective_subtype
  have hmem : ∀ z, N.subtype.baseChange K z ∈ eigK ρ σ := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul k n =>
      rw [LinearMap.baseChange_tmul]
      have hn : inK K H (n : H) ∈ eigK ρ σ := n.2
      have : k ⊗ₜ[O] (N.subtype n) = k • inK K H (n : H) := by
        simp [inK, TensorProduct.smul_tmul']
      rw [this]; exact (eigK ρ σ).smul_mem k hn
    | add x y hx hy => rw [map_add]; exact (eigK ρ σ).add_mem hx hy
  have hle := LinearMap.finrank_le_finrank_of_injective
    (f := (N.subtype.baseChange K).codRestrict (eigK ρ σ) hmem)
    (fun a b hab => hinj (by simpa using congrArg Subtype.val hab))
  rw [Module.finrank_baseChange, h1] at hle
  exact hle

theorem compl [Module.Finite O H] (N : Submodule O H) (hN : IsSat N) : ∃ C : Submodule O H, IsCompl N C := by
  haveI : Module.IsTorsionFree O (H ⧸ N) := by
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    intro r m hrm
    by_cases hr : r = 0
    · exact Or.inl hr
    · right
      obtain ⟨h, rfl⟩ := N.mkQ_surjective m
      rw [← map_smul] at hrm
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hrm ⊢
      exact hN r h hr hrm
  haveI : Module.Free O (H ⧸ N) := Module.free_of_finite_type_torsion_free'
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective
  have hs' : ∀ q, N.mkQ (s q) = q := fun q => LinearMap.congr_fun hs q
  let f : H →ₗ[O] N := LinearMap.codRestrict N (LinearMap.id - s ∘ₗ N.mkQ) (by
    intro h
    rw [← Submodule.Quotient.mk_eq_zero]
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
    rw [Submodule.Quotient.mk_sub]
    have := hs' (N.mkQ h)
    simp only [Submodule.mkQ_apply] at this ⊢
    rw [this, sub_self])
  refine ⟨LinearMap.ker f, LinearMap.isCompl_of_proj (f := f) ?_⟩
  intro x
  ext
  simp [f, (Submodule.Quotient.mk_eq_zero N).2 x.2]
end GlobalTheory.EigenLattice

theorem GlobalTheory.EigenLattice.main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → ∀ σ : E →+* K, IsSat (eigLat ρ σ) ∧ (∃ g : H, g ≠ 0 ∧ eigLat ρ σ = O ∙ g) ∧ Module.Free O (eigLat ρ σ) ∧ Module.finrank O (eigLat ρ σ) = 1 ∧ ∃ C : Submodule O H, IsCompl (eigLat ρ σ) C := by
  intro E _ _ _ c _ l _ O _ _ _ _ K _ _ _ _ _ D _ _ I _ φ _ H _ _ ρ Fil B hL σ
  obtain ⟨hfree, hfin, -, hline, -⟩ := hL
  haveI := hfree; haveI := hfin
  have hsat := GlobalTheory.EigenLattice.sat (K := K) ρ σ
  obtain ⟨g0, hg0, hg0m⟩ := GlobalTheory.EigenLattice.exists_ne_mem ρ σ (hline σ)
  set N := eigLat ρ σ
  have hle := GlobalTheory.EigenLattice.finrank_le ρ σ (hline σ)
  haveI : Nontrivial N := ⟨⟨⟨g0, hg0m⟩, 0, fun h => hg0 (congrArg Subtype.val h)⟩⟩
  have hpos : 0 < Module.finrank O N := Module.finrank_pos_iff.2 inferInstance
  have h1 : Module.finrank O N = 1 := le_antisymm hle hpos
  let b := Module.finBasisOfFinrankEq O N h1
  refine ⟨hsat, ⟨(b 0 : H), fun h => b.ne_zero 0 (Subtype.ext h), ?_⟩, inferInstance, h1,
    GlobalTheory.EigenLattice.compl N hsat⟩
  apply le_antisymm
  · intro x hx
    have := b.sum_repr ⟨x, hx⟩
    rw [Fin.sum_univ_one] at this
    rw [Submodule.mem_span_singleton]
    exact ⟨b.repr ⟨x, hx⟩ 0, by simpa using congrArg Subtype.val this⟩
  · rw [Submodule.span_singleton_le_iff_mem]; exact (b 0).2
