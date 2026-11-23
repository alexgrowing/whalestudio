import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory.ClassDict

theorem exu_rep {G Γ Gf : Type} [Group G] [Group Γ] [Group Gf] (P R U : Subgroup G) (ιf : Γ →* Gf)
    (K : Subgroup Gf) (Φ : Gf ≃* P) (h0 : P)
    (hK : ∀ h : Gf, h ∈ K ↔ ((h0⁻¹ * Φ h * h0 : P) : G) ∈ U)
    (h1 : ∀ γ : Γ, (Φ (ιf γ)).1 ∈ R) (h2 : ∀ r ∈ R, ∃ γ : Γ, (Φ (ιf γ)).1 = r)
    {C : Type} (yc : C → P)
    (hb : Function.Bijective
      (fun c => (Quotient.mk'' (yc c) : ClassSet (R.subgroupOf P) (U.subgroupOf P)))) (h : Gf) :
    ∃! c : C, ∃ (γ : Γ) (κ : K), h = ιf γ * Φ.symm (yc c * h0⁻¹) * (κ : Gf) := by
  have key : ∀ a b : P, (Quotient.mk'' a : ClassSet (R.subgroupOf P) (U.subgroupOf P)) = Quotient.mk'' b ↔
      ∃ x ∈ R.subgroupOf P, ∃ y ∈ U.subgroupOf P, b = x * a * y := fun a b => DoubleCoset.eq _ _ a b
  have fwd : ∀ (c : C) (γ : Γ) (κ : K), h = ιf γ * Φ.symm (yc c * h0⁻¹) * (κ : Gf) →
      (Quotient.mk'' (yc c) : ClassSet (R.subgroupOf P) (U.subgroupOf P)) = Quotient.mk'' (Φ h * h0) := by
    intro c γ κ hc
    rw [key]
    refine ⟨Φ (ιf γ), ?_, h0⁻¹ * Φ κ * h0, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact h1 γ
    · rw [Subgroup.mem_subgroupOf]
      exact (hK κ).1 κ.2
    · simp only [hc, map_mul, MulEquiv.apply_symm_apply, mul_assoc]
  obtain ⟨c, hc⟩ := hb.2 (Quotient.mk'' (Φ h * h0))
  refine ⟨c, ?_, ?_⟩
  · obtain ⟨x, hx, y, hy, hxy⟩ := (key _ _).1 hc
    rw [Subgroup.mem_subgroupOf] at hx hy
    obtain ⟨γ, hγ⟩ := h2 _ hx
    have hκ : Φ.symm (h0 * y * h0⁻¹) ∈ K := by
      rw [hK, MulEquiv.apply_symm_apply]
      have e : h0⁻¹ * (h0 * y * h0⁻¹) * h0 = y := by group
      rw [e]
      exact hy
    refine ⟨γ, ⟨_, hκ⟩, ?_⟩
    apply Φ.injective
    have hγ' : Φ (ιf γ) = x := Subtype.ext hγ
    have hΦ : Φ h = x * yc c * y * h0⁻¹ := by
      rw [← hxy]
      group
    simp only [map_mul, MulEquiv.apply_symm_apply, hγ', hΦ]
    group
  · rintro c' ⟨γ, κ, hc'⟩
    exact hb.1 ((fwd c' γ κ hc').trans hc.symm)

theorem stab_triv {G Γ Gf : Type} [Group G] [Group Γ] [Group Gf] (P U : Subgroup G) (ιf : Γ →* Gf)
    (K : Subgroup Gf) (Φ : Gf ≃* P) (h0 : P)
    (hK : ∀ h : Gf, h ∈ K ↔ ((h0⁻¹ * Φ h * h0 : P) : G) ∈ U)
    (hn : ∀ (x : Gf) (γ : Γ), x⁻¹ * ιf γ * x ∈ K → γ = 1) (y : P) (γ : Γ)
    (hγ : (Φ (ιf γ)).1 ∈ U.map (MulAut.conj y.1).toMonoidHom) : (Φ (ιf γ)).1 = 1 := by
  obtain ⟨u, hu, hyu⟩ := Subgroup.mem_map.1 hγ
  have e : ((Φ (ιf γ) : P) : G) = (y : G) * u * (y : G)⁻¹ := by
    rw [← hyu]
    simp [MulAut.conj_apply]
  have hmem : (Φ.symm (y * h0⁻¹))⁻¹ * ιf γ * Φ.symm (y * h0⁻¹) ∈ K := by
    rw [hK]
    convert hu using 1
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    push_cast
    rw [e]
    group
  rw [hn _ _ hmem]
  simp

theorem bc_inj_of_inj {A B : Type} [CommRing A] [CommRing B] {k : ℕ} {φ : A →+* B}
    (hφ : Function.Injective φ) : Function.Injective (bc (n := Fin k) φ) := by
  intro a b h
  apply Units.ext
  have h' := congrArg Units.val h
  funext i j
  exact hφ (congrFun (congrFun h' i) j)

theorem finAdele_algebraMap_inj (F : Type) [Field F] [NumberField F] :
    Function.Injective (algebraMap F (FiniteAdeleRing (𝓞 F) F)) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
  let v : HeightOneSpectrum (𝓞 F) :=
    ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField F)⟩
  have : Nontrivial (FiniteAdeleRing (𝓞 F) F) := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h' := congrArg (fun x : FiniteAdeleRing (𝓞 F) F => x v) h
    rw [← map_zero (algebraMap F (FiniteAdeleRing (𝓞 F) F)),
      ← map_one (algebraMap F (FiniteAdeleRing (𝓞 F) F))] at h'
    simp only [FiniteAdeleRing.algebraMap_apply] at h'
    rw [HeightOneSpectrum.adicCompletion.coe_zero, HeightOneSpectrum.adicCompletion.coe_one] at h'
    exact zero_ne_one h'
  exact (algebraMap F _).injective

theorem classReps_dictionary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E σ J T f bad) (Γ Gf : Type) [Group Γ] [Group Gf] (ιf : Γ →* Gf) (K : Subgroup Gf) (Φ : Gf ≃* UPts σ J (FiniteAdeleRing (𝓞 F) F)) (h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)), (∀ h : Gf, h ∈ K ↔ ((h0⁻¹ * Φ h * h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) ∈ S.U) → (∀ γ : Γ, ∃ g : GL (Fin n) E, g ∈ UJ (σ : E →+* E) J ∧ (Φ (ιf γ)).1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) g) → (∀ g : GL (Fin n) E, g ∈ UJ (σ : E →+* E) J → ∃ γ : Γ, (Φ (ιf γ)).1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) g) → ∀ (C : Type) (yc : C → UPts σ J (FiniteAdeleRing (𝓞 F) F)), Function.Bijective (fun c => (Quotient.mk'' (yc c) : Cls S)) → (∀ h : Gf, ∃! c : C, ∃ (γ : Γ) (κ : K), h = ιf γ * Φ.symm (yc c * h0⁻¹) * (κ : Gf)) ∧ ((∀ (x : Gf) (γ : Γ), x⁻¹ * ιf γ * x ∈ K → γ = 1) → ∀ (c : C) (g : GL (Fin n) E), g ∈ UJ (σ : E →+* E) J → bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) g ∈ S.U.map (MulAut.conj (yc c).1).toMonoidHom → g = 1) := by
  intro F E _ _ _ _ _ σ n J T f bad S Γ Gf _ _ ιf K Φ h0 hK h1 h2 C yc hb
  have hR1 : ∀ γ : Γ, (Φ (ιf γ)).1 ∈ ratPts σ J (FiniteAdeleRing (𝓞 F) F) := by
    intro γ
    obtain ⟨g, hg, hgγ⟩ := h1 γ
    rw [hgγ]
    unfold ratPts
    exact Subgroup.mem_map_of_mem _ hg
  have hR2 : ∀ r ∈ ratPts σ J (FiniteAdeleRing (𝓞 F) F), ∃ γ : Γ, (Φ (ιf γ)).1 = r := by
    intro r hr
    unfold ratPts at hr
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hr
    exact h2 g hg
  refine ⟨fun h => exu_rep _ _ S.U ιf K Φ h0 hK hR1 hR2 yc hb h, fun hn c g hg hgU => ?_⟩
  obtain ⟨γ, hγ⟩ := h2 g hg
  have hs := stab_triv _ S.U ιf K Φ h0 hK hn (yc c) γ (by rw [hγ]; exact hgU)
  rw [hγ] at hs
  have hinj : Function.Injective (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)) := by
    intro a b hab
    exact Algebra.TensorProduct.includeLeft_injective (S := F) (finAdele_algebraMap_inj F) hab
  exact bc_inj_of_inj hinj (hs.trans (map_one _).symm)

end GlobalTheory.ClassDict
