import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.SliceExt

theorem exists_extend {G S V : Type*} [Monoid G] [AddCommGroup S] [Module ℂ S]
    [AddCommGroup V] [Module ℂ V] (j : S →ₗ[ℂ] V) (hj : Function.Injective j)
    (ρ : G →* Module.End ℂ S) :
    ∃ L : G →* Module.End ℂ V, ∀ g s, L g (j s) = j (ρ g s) := by
  obtain ⟨p, hp⟩ := j.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hj)
  have hp' : ∀ s, p (j s) = s := fun s => LinearMap.congr_fun hp s
  refine ⟨{ toFun := fun g => j ∘ₗ (ρ g) ∘ₗ p + (LinearMap.id - j ∘ₗ p)
            map_one' := ?_
            map_mul' := ?_ }, ?_⟩
  · ext v; simp
  · intro g g'; ext v; simp [hp']
  · intro g s; simp [hp']

noncomputable def splitPts (F : Type) [Field F] [NumberField F] (κ : Type) :
    (κ → AF F) ≃ (κ → mixedEmbedding.mixedSpace F) × (κ → Af F) where
  toFun x := (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1, fun i => (x i).2)
  invFun p := fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i)
  left_inv x := by
    funext i
    show (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
      (InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1), (x i).2) : AF F) = x i
    rw [RingEquiv.symm_apply_apply]; rfl
  right_inv p := by
    refine Prod.ext ?_ rfl
    funext i
    exact RingEquiv.apply_symm_apply _ _

open scoped TensorProduct in
open NumberField MeasureTheory in

theorem _root_.GlobalTheory.SliceExt.exists_rep_pure (F : Type) [Field F] [NumberField F]
    (κ : Type) [Fintype κ]
    (G : Type) [Group G] (ρ : G →* (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ →L[ℂ] _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ)) :
    ∃ ω₀ : G →* Module.End ℂ ((κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ), ∀ (g : G) (f : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ)
      (h : (κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) → ℂ),
      ω₀ g (_root_.GlobalTheory.WeilM.pureA F f h) = _root_.GlobalTheory.WeilM.pureA F (ρ g f) h := by
  classical
  let ι : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ →ₗ[ℂ] ((κ → mixedEmbedding.mixedSpace F) → ℂ) :=
    { toFun := fun f => ⇑f, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hι : Function.Injective ι := DFunLike.coe_injective
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.range ι)
  let j := LinearEquiv.ofInjective ι hι
  let e := Submodule.prodEquivOfIsCompl _ C hC
  let A : G → Module.End ℂ ((κ → mixedEmbedding.mixedSpace F) → ℂ) := fun g =>
    e.toLinearMap ∘ₗ ((j.toLinearMap ∘ₗ (ρ g).toLinearMap ∘ₗ j.symm.toLinearMap).prodMap
      LinearMap.id) ∘ₗ e.symm.toLinearMap
  have hA1 : A 1 = 1 := by
    ext v
    simp [A]
  have hAmul : ∀ g h, A (g * h) = A g * A h := by
    intro g h
    ext v
    simp [A]
  have hAι : ∀ g f, A g (ι f) = ι (ρ g f) := by
    intro g f
    have : e.symm (ι f) = (j f, 0) := by
      rw [show ι f = ((j f : LinearMap.range ι) : _) from rfl]
      exact Submodule.prodEquivOfIsCompl_symm_apply_left _ _ hC _
    simp only [A, LinearMap.comp_apply, LinearEquiv.coe_coe, this, LinearMap.prodMap_apply,
      LinearEquiv.symm_apply_apply, map_zero, LinearMap.id_apply]
    rw [Submodule.coe_prodEquivOfIsCompl']
    simp [j]
  let s := _root_.GlobalTheory.SliceExt.splitPts F κ
  let slice : ((κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ) → (κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) → (κ → mixedEmbedding.mixedSpace F) → ℂ :=
    fun Φ y a => Φ (s.symm (a, y))
  let W : G → Module.End ℂ ((κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ) := fun g =>
    { toFun := fun Φ x => A g (slice Φ (s x).2) (s x).1
      map_add' := by
        intro Φ Ψ
        funext x
        have : slice (Φ + Ψ) (s x).2 = slice Φ (s x).2 + slice Ψ (s x).2 := rfl
        simp only [this, map_add, Pi.add_apply]
      map_smul' := by
        intro c Φ
        funext x
        have : slice (c • Φ) (s x).2 = c • slice Φ (s x).2 := rfl
        simp only [this, map_smul, Pi.smul_apply, RingHom.id_apply] }
  refine ⟨{ toFun := W, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · ext Φ x
    simp only [W, hA1, LinearMap.coe_mk, AddHom.coe_mk, Module.End.one_apply, slice,
      Prod.mk.eta, Equiv.symm_apply_apply]
  · intro g h
    ext Φ x
    simp only [W, hAmul, LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply]
    have hsl : slice (fun x => A h (slice Φ (s x).2) (s x).1) (s x).2 = A h (slice Φ (s x).2) := by
      funext a
      simp only [slice, Equiv.apply_symm_apply]
    rw [hsl]
  · intro g f h
    funext x
    have hsl : ∀ (f' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ),
        slice (_root_.GlobalTheory.WeilM.pureA F f' h) (s x).2 = h (s x).2 • ι f' := by
      intro f'
      funext a
      have h1 := s.apply_symm_apply (a, (s x).2)
      simp only [slice, _root_.GlobalTheory.WeilM.pureA, Pi.smul_apply, smul_eq_mul]
      have ha : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (s.symm (a, (s x).2) i).1) = a :=
        congrArg Prod.fst h1
      have hy : (fun i => (s.symm (a, (s x).2) i).2) = (s x).2 := congrArg Prod.snd h1
      rw [ha, hy, mul_comm]
      rfl
    show A g (slice (_root_.GlobalTheory.WeilM.pureA F f h) (s x).2) (s x).1 = _
    rw [hsl, map_smul, hAι]
    simp only [Pi.smul_apply, smul_eq_mul, _root_.GlobalTheory.WeilM.pureA]
    rw [mul_comm]
    rfl

end GlobalTheory.SliceExt
