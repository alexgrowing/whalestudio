import Mathlib
import GroundTheory.ProfiniteCohomology.EulerCharDefs
import GroundTheory.ProfiniteCohomology.ContinuousCochains.LongExactSequence
import GroundTheory.ProfiniteCohomology.Shapiro
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

universe u

section Counting

variable {R M N : Type*} [Ring R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

theorem card_eq_card_ker_mul_card_range (f : M →ₗ[R] N) :
    Nat.card M = Nat.card (LinearMap.ker f) * Nat.card (LinearMap.range f) := by
  have h1 := AddSubgroup.card_mul_index f.toAddMonoidHom.ker
  rw [AddSubgroup.index_ker] at h1
  exact h1.symm

end Counting

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem eulerChar_eq (A : Rep.{u} k G) [IsDiscreteRep A] :
    eulerChar A = (Nat.card (cohomology A 0) : ℚ) * Nat.card (cohomology A 2) /
      Nat.card (cohomology A 1) := by
  simp [eulerChar, Finset.prod_range_succ, div_eq_mul_inv]
  ring

section ShortExact

theorem card_range_eq_card_ker_of_exact {T : ShortComplex (ModuleCat k)} (hT : T.Exact) :
    Nat.card (LinearMap.range T.f.hom) = Nat.card (LinearMap.ker T.g.hom) := by
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hT
  rw [hT]

variable {S : ShortComplex (Rep.{u} k G)} [IsDiscreteRep S.X₁] [IsDiscreteRep S.X₂]
  [IsDiscreteRep S.X₃]

theorem eulerChar_shortExact_of_finite (hS : S.ShortExact)
    [Finite (cohomology S.X₁ 1)] [Finite (cohomology S.X₂ 1)] [Finite (cohomology S.X₃ 1)]
    [Subsingleton (cohomology S.X₁ 3)] :
    eulerChar S.X₂ = eulerChar S.X₁ * eulerChar S.X₃ := by
  have hk := fun {X Y : ModuleCat k} (φ : X ⟶ Y) => card_eq_card_ker_mul_card_range φ.hom
  have e2 : ∀ i, Nat.card (LinearMap.range (cohomologyMap S.f i).hom) =
      Nat.card (LinearMap.ker (cohomologyMap S.g i).hom) := fun i =>
    card_range_eq_card_ker_of_exact (cohomology_exact₂ hS i)
  have e30 : Nat.card (LinearMap.range (cohomologyMap S.g 0).hom) =
      Nat.card (LinearMap.ker (δ hS 0 1 rfl).hom) :=
    card_range_eq_card_ker_of_exact (cohomology_exact₃ hS 0 1 rfl)
  have e31 : Nat.card (LinearMap.range (cohomologyMap S.g 1).hom) =
      Nat.card (LinearMap.ker (δ hS 1 2 rfl).hom) :=
    card_range_eq_card_ker_of_exact (cohomology_exact₃ hS 1 2 rfl)
  have e32 : Nat.card (LinearMap.range (cohomologyMap S.g 2).hom) =
      Nat.card (LinearMap.ker (δ hS 2 3 rfl).hom) :=
    card_range_eq_card_ker_of_exact (cohomology_exact₃ hS 2 3 rfl)
  have e10 : Nat.card (LinearMap.range (δ hS 0 1 rfl).hom) =
      Nat.card (LinearMap.ker (cohomologyMap S.f 1).hom) :=
    card_range_eq_card_ker_of_exact (cohomology_exact₁ hS 0 1 rfl)
  have e11 : Nat.card (LinearMap.range (δ hS 1 2 rfl).hom) =
      Nat.card (LinearMap.ker (cohomologyMap S.f 2).hom) :=
    card_range_eq_card_ker_of_exact (cohomology_exact₁ hS 1 2 rfl)
  have h0 : Nat.card (LinearMap.ker (cohomologyMap S.f 0).hom) = 1 := by
    have := hS.mono_f
    have hm : Mono (cohomologyMap S.f 0) :=
      HomologicalComplex.mono_homologyMap_of_mono_of_not_rel (cochainsMap S.f) 0
        (fun i => by simp)
    rw [LinearMap.ker_eq_bot.2 ((ModuleCat.mono_iff_injective _).1 hm)]
    simp
  have htop : Nat.card (LinearMap.range (δ hS 2 3 rfl).hom) = 1 :=
    Nat.card_of_subsingleton (0 : LinearMap.range (δ hS 2 3 rfl).hom)
  have hA1 : Nat.card (cohomology S.X₁ 1) ≠ 0 := Nat.card_pos.ne'
  have hB1 : Nat.card (cohomology S.X₂ 1) ≠ 0 := Nat.card_pos.ne'
  have hC1 : Nat.card (cohomology S.X₃ 1) ≠ 0 := Nat.card_pos.ne'
  rw [hk (cohomologyMap S.f 1), ← e10] at hA1
  rw [hk (cohomologyMap S.g 1), ← e2 1] at hB1
  rw [hk (δ hS 1 2 rfl), ← e31] at hC1
  rw [eulerChar_eq, eulerChar_eq, eulerChar_eq,
    hk (cohomologyMap S.f 0), hk (cohomologyMap S.f 1), hk (cohomologyMap S.f 2),
    hk (cohomologyMap S.g 0), hk (cohomologyMap S.g 1), hk (cohomologyMap S.g 2),
    hk (δ hS 0 1 rfl), hk (δ hS 1 2 rfl), hk (δ hS 2 3 rfl),
    h0, htop, ← e2 0, ← e2 1, ← e2 2, ← e30, ← e31, ← e32, ← e10, ← e11]
  simp only [mul_ne_zero_iff] at hA1 hB1 hC1
  obtain ⟨hz0, hx1⟩ := hA1
  obtain ⟨-, hy1⟩ := hB1
  obtain ⟨-, hz1⟩ := hC1
  push_cast
  field_simp

end ShortExact

section Hypothesis

variable {P : ℕ → Prop}

theorem eulerChar_pos (hG : HasFiniteCohomology k G P) (A : Rep.{u} k G) [IsDiscreteRep A]
    [Finite A] (hA : P (Nat.card A)) : 0 < eulerChar A := by
  obtain ⟨hfin, -⟩ := hG A ‹_› hA
  have h0 := hfin 0
  have h1 := hfin 1
  have h2 := hfin 2
  rw [eulerChar_eq]
  have p0 : (0 : ℚ) < Nat.card (cohomology A 0) := by exact_mod_cast Nat.card_pos
  have p1 : (0 : ℚ) < Nat.card (cohomology A 1) := by exact_mod_cast Nat.card_pos
  have p2 : (0 : ℚ) < Nat.card (cohomology A 2) := by exact_mod_cast Nat.card_pos
  positivity

variable {S : ShortComplex (Rep.{u} k G)} [IsDiscreteRep S.X₁] [IsDiscreteRep S.X₂]
  [IsDiscreteRep S.X₃]

theorem eulerChar_shortExact_of_mem (hG : HasFiniteCohomology k G P) (hS : S.ShortExact)
    [Finite S.X₁] [Finite S.X₂] [Finite S.X₃] (h₁ : P (Nat.card S.X₁))
    (h₂ : P (Nat.card S.X₂)) (h₃ : P (Nat.card S.X₃)) :
    eulerChar S.X₂ = eulerChar S.X₁ * eulerChar S.X₃ := by
  obtain ⟨f₁, z₁⟩ := hG S.X₁ ‹_› h₁
  have := f₁ 1
  have := z₁ 3 le_rfl
  have := (hG S.X₂ ‹_› h₂).1 1
  have := (hG S.X₃ ‹_› h₃).1 1
  exact eulerChar_shortExact_of_finite hS

theorem eulerChar_shortExact (hP : ∀ m n, m ∣ n → P n → P m) (hG : HasFiniteCohomology k G P)
    (hS : S.ShortExact) [Finite S.X₂] (h₂ : P (Nat.card S.X₂)) :
    eulerChar S.X₂ = eulerChar S.X₁ * eulerChar S.X₃ := by
  have hinj : Function.Injective S.f.hom := (Rep.mono_iff_injective _).1 hS.mono_f
  have hsurj : Function.Surjective S.g.hom := (Rep.epi_iff_surjective _).1 hS.epi_g
  have : Finite S.X₁ := Finite.of_injective _ hinj
  have : Finite S.X₃ := Finite.of_surjective _ hsurj
  have h₁ : P (Nat.card S.X₁) :=
    hP _ _ (AddSubgroup.card_dvd_of_injective S.f.hom.toLinearMap.toAddMonoidHom hinj) h₂
  have h₃ : P (Nat.card S.X₃) := by
    refine hP _ _ ⟨Nat.card (LinearMap.ker S.g.hom.toLinearMap), ?_⟩ h₂
    rw [card_eq_card_ker_mul_card_range S.g.hom.toLinearMap,
      LinearMap.range_eq_top.2 hsurj, mul_comm]
    congr 1
    exact Nat.card_congr (Submodule.topEquiv).toEquiv
  exact eulerChar_shortExact_of_mem hG hS h₁ h₂ h₃

noncomputable def eulerCharUnit (hG : HasFiniteCohomology k G P)
    (A : (finiteDiscreteRep k G P).FullSubcategory) : ℚˣ :=
  haveI := A.property.1
  haveI := A.property.2.1
  Units.mk0 (eulerChar A.obj) (eulerChar_pos hG A.obj A.property.2.2).ne'

theorem coe_eulerCharUnit (hG : HasFiniteCohomology k G P)
    (A : (finiteDiscreteRep k G P).FullSubcategory) :
    haveI := A.property.1
    (eulerCharUnit hG A : ℚ) = eulerChar A.obj :=
  rfl

noncomputable def eulerCharHom (hG : HasFiniteCohomology k G P) :
    GrothendieckGroup k G P →+ Additive ℚˣ :=
  QuotientAddGroup.lift (grothendieckRelations k G P)
    (FreeAbelianGroup.lift fun A => Additive.ofMul (eulerCharUnit hG A)) (by
      rw [grothendieckRelations, AddSubgroup.closure_le]
      rintro x ⟨S, h₁, h₂, h₃, hS, rfl⟩
      have := h₁.1
      have := h₂.1
      have := h₃.1
      have := h₁.2.1
      have := h₂.2.1
      have := h₃.2.1
      have key := eulerChar_shortExact_of_mem hG hS h₁.2.2 h₂.2.2 h₃.2.2
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, FreeAbelianGroup.lift_apply_of]
      rw [sub_sub, sub_eq_zero, ← ofMul_mul]
      congr 1
      ext
      simp only [Units.val_mul, coe_eulerCharUnit]
      exact key)

end Hypothesis

section Shapiro

variable [CompactSpace G] (U : OpenSubgroup G)

theorem eulerChar_coind (B : Rep.{u} k (U : Subgroup G)) [IsDiscreteRep B] :
    eulerChar (Rep.coind (U : Subgroup G).subtype B) = eulerChar B := by
  simp only [eulerChar]
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [Nat.card_congr (shapiroIso U B q).toLinearEquiv.toEquiv]

theorem eulerChar_res_eq_eulerChar_coind (A : Rep.{u} k G) [IsDiscreteRep A] :
    eulerChar (Rep.res (U : Subgroup G).subtype A) =
      eulerChar (Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype A)) :=
  (eulerChar_coind U _).symm

noncomputable def coindValues (B : Rep.{u} k (U : Subgroup G)) :
    Rep.coind (U : Subgroup G).subtype B →+ (G ⧸ (U : Subgroup G) → B) :=
  AddMonoidHom.mk' (fun f c => f.1 (Quotient.out c)⁻¹) fun _ _ => rfl

omit [IsTopologicalGroup G] [CompactSpace G] in
theorem coindValues_injective (B : Rep.{u} k (U : Subgroup G)) :
    Function.Injective (coindValues U B) := by
  intro f g hfg
  apply Subtype.ext
  funext x
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul (U : Subgroup G) x⁻¹
  have hx : x = (U : Subgroup G).subtype u * (Quotient.out
      (QuotientGroup.mk x⁻¹ : G ⧸ (U : Subgroup G)))⁻¹ := by
    rw [show (Quotient.out (QuotientGroup.mk x⁻¹ : G ⧸ (U : Subgroup G))) = x⁻¹ * u from hu]
    simp
  have h := congrFun hfg (QuotientGroup.mk x⁻¹)
  simp only [coindValues, AddMonoidHom.mk'_apply] at h
  rw [hx, f.2 u, g.2 u, h]

instance finite_coind (B : Rep.{u} k (U : Subgroup G)) [Finite B] :
    Finite (Rep.coind (U : Subgroup G).subtype B) :=
  Finite.of_injective _ (coindValues_injective U B)

theorem card_coind_dvd (B : Rep.{u} k (U : Subgroup G)) [Finite B] :
    Nat.card (Rep.coind (U : Subgroup G).subtype B) ∣ Nat.card B ^ (U : Subgroup G).index := by
  have h := AddSubgroup.card_dvd_of_injective (coindValues U B) (coindValues_injective U B)
  rwa [Nat.card_fun] at h

end Shapiro

end GroundTheory.ProfCoh
