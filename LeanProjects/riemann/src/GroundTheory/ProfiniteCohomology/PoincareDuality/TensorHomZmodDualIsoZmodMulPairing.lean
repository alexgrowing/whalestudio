import Mathlib
import GroundTheory.ProfiniteCohomology.PoincareDuality.NsmulEqZeroOfNonemptyAddEquiv
import GroundTheory.ProfiniteCohomology.PoincareDuality.Torsion
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory

universe u

attribute [local instance 2000] Rep.hV2

abbrev zmodULiftModule (n : ℕ) : Module (ULift.{u} ℤ) (ULift.{u} (ZMod n)) :=
  (zmodRep.{u} PUnit.{u + 1} n).hV2

attribute [local instance 3000] zmodULiftModule

variable {G : Type u} [Group G] {n : ℕ}

section Basic

variable {D M : Rep.{u} (ULift.{u} ℤ) G}

theorem nsmul_dualRep_eq_zero (hD : ∀ d : D, n • d = 0) (f : dualRep D M) : n • f = 0 := by
  let f' : M →ₗ[ULift.{u} ℤ] D := f
  change n • f' = 0
  refine LinearMap.ext fun m => ?_
  rw [LinearMap.smul_apply, hD, LinearMap.zero_apply]

theorem finite_of_nonempty_addEquiv [NeZero n] (hD : Nonempty (D ≃+ ZMod n)) : Finite D := by
  obtain ⟨e⟩ := hD
  exact Finite.of_equiv _ e.symm.toEquiv

instance finite_dualRep [Finite D] [Finite M] : Finite (dualRep D M) :=
  Finite.of_injective (fun f : M →ₗ[ULift.{u} ℤ] D => (f : M → D)) DFunLike.coe_injective

theorem card_dualRep_le [NeZero n] (hD : Nonempty (D ≃+ ZMod n)) [Finite M] :
    Nat.card (dualRep D M) ≤ Nat.card M := by
  obtain ⟨e⟩ := hD
  let F : (M →ₗ[ULift.{u} ℤ] D) → (M →+ ZMod n) := fun f => e.toAddMonoidHom.comp f.toAddMonoidHom
  have hF : Function.Injective F := fun f f' h => LinearMap.ext fun m =>
    e.injective (DFunLike.congr_fun h m)
  exact (Nat.card_le_card_of_injective F hF).trans card_addMonoidHom_zmod_le

theorem exists_dualRep_apply_ne_zero [NeZero n] (hD : Nonempty (D ≃+ ZMod n))
    (hM : ∀ m : M, n • m = 0) {m : M} (hm : m ≠ 0) :
    ∃ f : M →ₗ[ULift.{u} ℤ] D, f m ≠ 0 := by
  obtain ⟨e⟩ := hD
  obtain ⟨χ, hχ⟩ := zmod_exists_apply_ne_zero hM hm
  refine ⟨(uliftIntLinearEquivAddHom M D).symm (e.symm.toAddMonoidHom.comp χ), fun h => hχ ?_⟩
  rw [uliftIntLinearEquivAddHom_symm_apply, AddMonoidHom.comp_apply,
    AddEquiv.coe_toAddMonoidHom, AddEquiv.map_eq_zero_iff] at h
  exact h

theorem bijective_toDualDual [NeZero n] (hD : Nonempty (D ≃+ ZMod n)) [Finite M]
    (hM : ∀ m : M, n • m = 0) : Function.Bijective (toDualDual D M).hom := by
  have : Finite D := finite_of_nonempty_addEquiv hD
  have : Finite (dualRep D M) := finite_dualRep
  have : Finite (dualRep D (dualRep D M)) := finite_dualRep
  refine Function.Injective.bijective_of_nat_card_le ?_
    ((card_dualRep_le hD).trans (card_dualRep_le hD))
  rw [injective_iff_map_eq_zero]
  intro m hm
  by_contra hne
  obtain ⟨f, hf⟩ := exists_dualRep_apply_ne_zero hD hM hne
  exact hf (DFunLike.congr_fun hm f)

end Basic

section EvalAt

variable {k : Type u} [CommRing k]

private theorem dualMap_zero (D : Rep.{u} k G) {A B : Rep.{u} k G} : dualMap D (0 : A ⟶ B) = 0 := by
  ext f a
  change f ((0 : A ⟶ B).hom a) = 0
  rw [Rep.zero_hom]
  exact map_zero f

def dualEvalAt (D X : Rep.{u} k G) (x : X) (hx : ∀ g : G, X.ρ g x = x) : dualRep D X ⟶ D :=
  Rep.ofHom ⟨{ toFun := fun ν => (ν : X →ₗ[k] D) x
               map_add' := fun _ _ => rfl
               map_smul' := fun _ _ => rfl }, fun σ => LinearMap.ext fun ν => by
    change D.ρ σ ((ν : X →ₗ[k] D) (X.ρ σ⁻¹ x)) = D.ρ σ ((ν : X →ₗ[k] D) x)
    rw [hx]⟩

theorem tensorHom_dualEvalAt (D X : Rep.{u} k G) (x : X) (hx : ∀ g : G, X.ρ g x = x)
    (μ : X ⊗ D ⟶ D) (h : ∀ (a : X) (ν : X →ₗ[k] D), μ.hom (a ⊗ₜ[k] ν x : (X ⊗ D : Rep k G)) = ν a) :
    (𝟙 X ⊗ₘ dualEvalAt D X x hx) ≫ μ = evalPairing D X := by
  ext y
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a ν =>
    change μ.hom (a ⊗ₜ[k] (ν : X →ₗ[k] D) x : (X ⊗ D : Rep k G)) = (ν : X →ₗ[k] D) a
    exact h a ν
  | add y z hy hz => simp only [map_add, hy, hz]

end EvalAt

section Exact

attribute [local instance 3000] Submodule.Quotient.module

variable (D : Rep.{u} (ULift.{u} ℤ) G)

abbrev dualShortComplex (S : ShortComplex (Rep.{u} (ULift.{u} ℤ) G)) :
    ShortComplex (Rep.{u} (ULift.{u} ℤ) G) :=
  ShortComplex.mk (dualMap D S.g) (dualMap D S.f) (by
    rw [← dualMap_comp, S.zero, dualMap_zero])

variable {D}

theorem dualShortComplex_injective_f {S : ShortComplex (Rep.{u} (ULift.{u} ℤ) G)}
    (hS : S.ShortExact) : Function.Injective (dualShortComplex D S).f.hom := by
  have hg : Function.Surjective S.g.hom := (Rep.epi_iff_surjective _).1 hS.epi_g
  intro f₁ f₂ h
  refine LinearMap.ext fun c => ?_
  obtain ⟨b, rfl⟩ := hg c
  exact LinearMap.congr_fun h b

theorem dualShortComplex_exact {S : ShortComplex (Rep.{u} (ULift.{u} ℤ) G)}
    (hS : S.ShortExact) : (dualShortComplex D S).Exact := by
  have hg : Function.Surjective S.g.hom := (Rep.epi_iff_surjective _).1 hS.epi_g
  have hex : ∀ b : S.X₂, S.g.hom b = 0 → ∃ a : S.X₁, S.f.hom a = b := by
    have := (ShortComplex.exact_map_iff_of_faithful _
      (forget₂ (Rep.{u} (ULift.{u} ℤ) G) (ModuleCat.{u} (ULift.{u} ℤ)))).2 hS.exact
    exact (ShortComplex.moduleCat_exact_iff _).1 this
  rw [← ShortComplex.exact_map_iff_of_faithful _
    (forget₂ (Rep.{u} (ULift.{u} ℤ) G) (ModuleCat.{u} (ULift.{u} ℤ))),
    ShortComplex.moduleCat_exact_iff]
  intro φ₀ hφ₀
  let φ : S.X₂ →ₗ[ULift.{u} ℤ] D := φ₀
  have hφ : ∀ a : S.X₁, φ (S.f.hom a) = 0 := fun a => LinearMap.congr_fun hφ₀ a
  let g : S.X₂ →ₗ[ULift.{u} ℤ] S.X₃ := S.g.hom.toLinearMap
  have hker : LinearMap.ker g ≤ LinearMap.ker φ := by
    intro b hb
    obtain ⟨a, rfl⟩ := hex b hb
    exact hφ a
  let ψ : S.X₃ →ₗ[ULift.{u} ℤ] D :=
    ((LinearMap.ker g).liftQ φ hker).comp (g.quotKerEquivOfSurjective hg).symm.toLinearMap
  refine ⟨ψ, LinearMap.ext fun b => ?_⟩
  change ψ (g b) = φ b
  simp only [ψ, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]

theorem dualShortComplex_surjective_g [NeZero n] (hD : Nonempty (D ≃+ ZMod n))
    {S : ShortComplex (Rep.{u} (ULift.{u} ℤ) G)} (hS : S.ShortExact)
    (hn : ∀ x : S.X₂, n • x = 0) : Function.Surjective (dualShortComplex D S).g.hom := by
  obtain ⟨e⟩ := hD
  have hf : Function.Injective S.f.hom := (Rep.mono_iff_injective _).1 hS.mono_f
  intro ψ₀
  let ψ : S.X₁ →ₗ[ULift.{u} ℤ] D := ψ₀
  let h : S.X₁ →+ S.X₂ := S.f.hom.toLinearMap.toAddMonoidHom
  obtain ⟨Φ, hΦ⟩ := zmod_exists_comp_eq_of_ker_le hn h (e.toAddMonoidHom.comp ψ.toAddMonoidHom)
    (fun a ha => by
      rw [AddMonoidHom.mem_ker] at ha ⊢
      have : a = 0 := hf (by rw [map_zero]; exact ha)
      rw [this, map_zero])
  refine ⟨(uliftIntLinearEquivAddHom S.X₂ D).symm (e.symm.toAddMonoidHom.comp Φ),
    LinearMap.ext fun a => ?_⟩
  change e.symm (Φ (S.f.hom a)) = ψ a
  have := DFunLike.congr_fun hΦ a
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom] at this
  change e.symm (Φ (h a)) = ψ a
  rw [this, AddEquiv.symm_apply_apply]
  rfl

theorem dualShortComplex_shortExact [NeZero n] (hD : Nonempty (D ≃+ ZMod n))
    {S : ShortComplex (Rep.{u} (ULift.{u} ℤ) G)} (hS : S.ShortExact)
    (hn : ∀ x : S.X₂, n • x = 0) : (dualShortComplex D S).ShortExact where
  exact := dualShortComplex_exact hS
  mono_f := (Rep.mono_iff_injective _).2 (dualShortComplex_injective_f hS)
  epi_g := (Rep.epi_iff_surjective _).2 (dualShortComplex_surjective_g hD hS hn)

end Exact

section ZModDual

variable (n) (D : Rep.{u} (ULift.{u} ℤ) G) (hD : ∀ d : D, n • d = 0)

def zmodDualHom : dualRep D (zmodRep.{u} G n) ⟶ D :=
  dualEvalAt D (zmodRep.{u} G n) (ULift.up 1) fun _ => rfl

theorem zmodDualHom_hom_apply (ν : dualRep D (zmodRep.{u} G n)) :
    (zmodDualHom n D).hom ν = ν (ULift.up 1 : zmodRep.{u} G n) :=
  rfl

theorem dualRep_zmodRep_apply (ν : dualRep D (zmodRep.{u} G n)) (a : ZMod n) :
    ν (ULift.up a : zmodRep.{u} G n) = (ZMod.cast a : ℤ) • ν (ULift.up 1 : zmodRep.{u} G n) := by
  conv_lhs => rw [← ZMod.intCast_zmod_cast a]
  rw [zmodRep_eq_zsmul G n, map_zsmul]

include hD in
theorem bijective_zmodDualHom : Function.Bijective (zmodDualHom n D).hom := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro ν hν
    rw [zmodDualHom_hom_apply] at hν
    refine DFunLike.ext _ _ fun a => ?_
    obtain ⟨a⟩ := a
    rw [dualRep_zmodRep_apply, hν, zsmul_zero]
    rfl
  · intro d
    refine ⟨(uliftIntLinearEquivAddHom (zmodRep.{u} G n) D).symm
      ((zmodMulAddHom n hD).flip d |>.comp
        ((AddEquiv.ulift : ULift.{u} (ZMod n) ≃+ ZMod n).toAddMonoidHom.comp
          (AddMonoidHom.id (zmodRep.{u} G n)))), ?_⟩
    change (zmodMulAddHom n hD) 1 d = d
    rw [zmodMulAddHom_apply]
    rw [zsmul_eq_zsmul_of_intCast_eq hD (b := 1) (by simp) d, one_zsmul]

def zmodDualIso : dualRep D (zmodRep.{u} G n) ≅ D :=
  Rep.isoOfBijective (zmodDualHom n D) (bijective_zmodDualHom n D hD)

theorem tensorHom_zmodDualIso_zmodMulPairing :
    (𝟙 (zmodRep.{u} G n) ⊗ₘ (zmodDualIso n D hD).hom) ≫ zmodMulPairing n D hD =
      evalPairing D (zmodRep.{u} G n) :=
  tensorHom_dualEvalAt D (zmodRep.{u} G n) (ULift.up 1) (fun _ => rfl) _ fun a ν => by
    obtain ⟨a⟩ := a
    change zmodMulAddHom n hD a (ν (ULift.up 1)) = ν (ULift.up a)
    rw [zmodMulAddHom_apply]
    exact (dualRep_zmodRep_apply n D ν a).symm

end ZModDual

end GroundTheory.ProfCoh
