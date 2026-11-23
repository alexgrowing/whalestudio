import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RePosOfIsMultIP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcFiniteAndSchurMult
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsInnerProductSmoothVectorsTensorStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainMetric

theorem integ_pair {ι : Type} [Fintype ι] {E : ι → Type} [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)]
    {X : Type} [MeasurableSpace X] {μ : Measure X} {A : Set X}
    (f g : (⨂[ℂ] i, E i) →ₗ[ℂ] (X → ℂ)) (B : (⨂[ℂ] i, E i) →ₗ[ℂ] (⨂[ℂ] i, E i) →ₗ⋆[ℂ] ℂ) (k : ℂ)
    (h : ∀ v v' : ∀ i, E i, IntegrableOn (fun x => f (PiTensorProduct.tprod ℂ v) x * conj (g (PiTensorProduct.tprod ℂ v') x)) A μ ∧
      ∫ x in A, f (PiTensorProduct.tprod ℂ v) x * conj (g (PiTensorProduct.tprod ℂ v') x) ∂μ =
        k * B (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v')) :
    ∀ w w', IntegrableOn (fun x => f w x * conj (g w' x)) A μ ∧ ∫ x in A, f w x * conj (g w' x) ∂μ = k * B w w' := by

  have left : ∀ (w : ⨂[ℂ] i, E i) (v' : ∀ i, E i),
      IntegrableOn (fun x => f w x * conj (g (PiTensorProduct.tprod ℂ v') x)) A μ ∧
        ∫ x in A, f w x * conj (g (PiTensorProduct.tprod ℂ v') x) ∂μ = k * B w (PiTensorProduct.tprod ℂ v') := by
    intro w v'
    induction w using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      obtain ⟨h1, h2⟩ := h v v'
      have e : (fun x => f (r • PiTensorProduct.tprod ℂ v) x * conj (g (PiTensorProduct.tprod ℂ v') x)) =
          fun x => r * (f (PiTensorProduct.tprod ℂ v) x * conj (g (PiTensorProduct.tprod ℂ v') x)) := by
        funext x
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
      refine ⟨?_, ?_⟩
      · rw [e]
        exact Integrable.const_mul h1 r
      · rw [e, integral_const_mul, h2]
        simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
        ring
    | add a b ha hb =>
      obtain ⟨ha1, ha2⟩ := ha
      obtain ⟨hb1, hb2⟩ := hb
      have e : (fun x => f (a + b) x * conj (g (PiTensorProduct.tprod ℂ v') x)) =
          fun x => f a x * conj (g (PiTensorProduct.tprod ℂ v') x) + f b x * conj (g (PiTensorProduct.tprod ℂ v') x) := by
        funext x
        simp only [map_add, Pi.add_apply, add_mul]
      refine ⟨?_, ?_⟩
      · rw [e]
        exact Integrable.add ha1 hb1
      · rw [e, integral_add ha1 hb1, ha2, hb2]
        simp only [map_add, LinearMap.add_apply, mul_add]

  intro w w'
  induction w' using PiTensorProduct.induction_on with
  | smul_tprod r v' =>
    obtain ⟨h1, h2⟩ := left w v'
    have e : (fun x => f w x * conj (g (r • PiTensorProduct.tprod ℂ v') x)) =
        fun x => conj r * (f w x * conj (g (PiTensorProduct.tprod ℂ v') x)) := by
      funext x
      simp only [map_smul, Pi.smul_apply, smul_eq_mul, map_mul]
      ring
    refine ⟨?_, ?_⟩
    · rw [e]
      exact Integrable.const_mul h1 (conj r)
    · rw [e, integral_const_mul, h2]
      simp only [LinearMap.map_smulₛₗ, smul_eq_mul]
      ring
  | add a b ha hb =>
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    have e : (fun x => f w x * conj (g (a + b) x)) =
        fun x => f w x * conj (g a x) + f w x * conj (g b x) := by
      funext x
      simp only [map_add, Pi.add_apply, mul_add]
    refine ⟨?_, ?_⟩
    · rw [e]
      exact Integrable.add ha1 hb1
    · rw [e, integral_add ha1 hb1, ha2, hb2]
      simp only [map_add, mul_add]

variable {D : D7}

theorem val_tprod {V' : HSp D} {S' : D.what₂.Tau → SPar} {M' : DSModel V' S'} (x : (⨂[ℂ] τ, M'.sm τ) →ₗ[ℂ] (GA D V' → ℂ))
    (v : M'.Vec) : x (PiTensorProduct.tprod ℂ v) = PiTensorProduct.lift.symm x v := by
  rw [PiTensorProduct.lift_symm, LinearMap.compMultilinearMap_apply]

theorem metEx : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, MetEx D := by
  intro hP D c hc j _ s hs
  obtain ⟨ipD, hpure, hhermD, hposD⟩ := GlobalTheory.T.exists_inner_product_smooth_vectors_tensor D s.V s.par s.M
  have hθ : IsInfFam c.θ := hc.inf
  have hμ := hs.haar
  have h𝓕 := hs.fund
  have hSM : SchurMult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) s.ν s.fd :=
    GlobalTheory.MultFinite.schurMult hP s.ν s.fd
  have hmem : ∀ x : s.CC c, PiTensorProduct.lift.symm (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈
      Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) :=
    fun x => (mem_multT c.θ s.M _ _ _).1 x.2
  by_cases hsm : ∀ τ, s.M.sm τ ≠ ⊥
  ·
    obtain ⟨hlin, hpos⟩ := GlobalTheory.SchurConst.ipM_posDef D c.θ s.V s.par s.M _ _ s.ν s.fd hθ hμ h𝓕 hSM hsm
    have hherm : ∀ T ∈ Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L),
        ∀ T' ∈ Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L),
          ipM s.M s.ν s.fd T' T = star (ipM s.M s.ν s.fd T T') :=
      fun T hT T' hT' => (hlin T hT T' hT' T' hT' 0).2
    have hadd : ∀ T ∈ Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L),
        ∀ T' ∈ Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L),
          ∀ T'' ∈ Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L),
            ipM s.M s.ν s.fd T (T' + T'') = ipM s.M s.ν s.fd T T' + ipM s.M s.ν s.fd T T'' := by
      intro T hT T' hT' T'' hT''
      have := (hlin T hT T' hT' T'' hT'' 1).1
      rwa [one_smul, one_mul] at this
    have hzero : ∀ T ∈ Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L), ipM s.M s.ν s.fd T 0 = 0 := by
      intro T hT
      have := hadd T hT 0 (zero_mem _) 0 (zero_mem _)
      rw [add_zero] at this
      linear_combination -this
    have hsmul : ∀ T ∈ Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L),
        ∀ T' ∈ Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L), ∀ a : ℂ,
          ipM s.M s.ν s.fd T (a • T') = a * ipM s.M s.ν s.fd T T' := by
      intro T hT T' hT' a
      have := (hlin T hT 0 (zero_mem _) T' hT' a).1
      rwa [zero_add, hzero T hT, zero_add] at this

    have hIP : ∀ x y : s.CC c, ∀ w w',
        IntegrableOn (fun g => (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w g *
          conj ((y : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w' g)) s.fd s.ν ∧
        ∫ g in s.fd, (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w g * conj ((y : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w' g) ∂s.ν =
          ipM s.M s.ν s.fd (PiTensorProduct.lift.symm (y : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)))
            (PiTensorProduct.lift.symm (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ))) * ipD w w' := by
      intro x y
      apply integ_pair
      intro v v'
      have hex := hSM hθ hμ h𝓕 _ (hmem y) _ (hmem x)
      have hc : IsMultIP s.M s.ν s.fd (PiTensorProduct.lift.symm (y : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)))
          (PiTensorProduct.lift.symm (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)))
          (ipM s.M s.ν s.fd (PiTensorProduct.lift.symm (y : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)))
            (PiTensorProduct.lift.symm (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)))) := by
        rw [ipM, dif_pos hex]
        exact hex.choose_spec
      obtain ⟨h1, h2⟩ := hc v' v
      have e : (fun g => (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) (PiTensorProduct.tprod ℂ v) g *
          conj ((y : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) (PiTensorProduct.tprod ℂ v') g)) =
          fun g => star (PiTensorProduct.lift.symm (y : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) v' g) *
            PiTensorProduct.lift.symm (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) v g := by
        funext g
        rw [val_tprod, val_tprod, mul_comm, starRingEnd_apply]
      refine ⟨?_, ?_⟩
      · rw [e]
        exact h1
      · rw [e, h2, hpure]
    refine ⟨ipD, LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
      (fun x y : s.CC c => ipM s.M s.ν s.fd (PiTensorProduct.lift.symm (y : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)))
        (PiTensorProduct.lift.symm (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)))) ?_ ?_ ?_ ?_, ?_⟩
    · intro x x' y
      simp only [Submodule.coe_add, map_add]
      exact hadd _ (hmem y) _ (hmem x) _ (hmem x')
    · intro a x y
      simp only [Submodule.coe_smul, map_smul, RingHom.id_apply, smul_eq_mul]
      exact hsmul _ (hmem y) _ (hmem x) a
    · intro x y y'
      simp only [Submodule.coe_add, map_add]
      rw [hherm _ (hmem x) _ (add_mem (hmem y) (hmem y')), hadd _ (hmem x) _ (hmem y) _ (hmem y'), star_add,
        ← hherm _ (hmem x) _ (hmem y), ← hherm _ (hmem x) _ (hmem y')]
    · intro a x y
      simp only [Submodule.coe_smul, map_smul, smul_eq_mul]
      rw [hherm _ (hmem x) _ (Submodule.smul_mem _ a (hmem y)), hsmul _ (hmem x) _ (hmem y), star_mul',
        ← hherm _ (hmem x) _ (hmem y), starRingEnd_apply]
    · refine ⟨hpure, hhermD, hposD, ?_, ?_, ?_, ?_⟩
      · intro x y
        simp only [LinearMap.mk₂'ₛₗ_apply]
        rw [hherm _ (hmem x) _ (hmem y), starRingEnd_apply]
      · intro x hx
        simp only [LinearMap.mk₂'ₛₗ_apply]
        refine hpos _ (hmem x) fun h0 => hx ?_
        apply Subtype.ext
        rw [Submodule.coe_zero]
        exact (LinearEquiv.map_eq_zero_iff _).1 h0
      · intro x y w w'
        exact (hIP x y w w').1
      · intro x y w w'
        simp only [Lift.pet, LinearMap.mk₂'ₛₗ_apply]
        exact (hIP x y w w').2
  ·
    push_neg at hsm
    obtain ⟨τ₀, hτ₀⟩ := hsm
    have htp : ∀ v : s.M.Vec, PiTensorProduct.tprod ℂ v = 0 := by
      intro v
      apply (PiTensorProduct.tprod ℂ).map_coord_zero τ₀
      have : (v τ₀ : s.M.H τ₀) ∈ (⊥ : Submodule ℂ (s.M.H τ₀)) := hτ₀ ▸ (v τ₀).2
      exact Subtype.ext ((Submodule.mem_bot ℂ).1 this)
    have hz : ∀ w : SmT s.M, w = 0 := by
      intro w
      induction w using PiTensorProduct.induction_on with
      | smul_tprod r v => rw [htp v, smul_zero]
      | add a b ha hb => rw [ha, hb, add_zero]
    refine ⟨ipD, 0, hpure, hhermD, hposD, ?_, ?_, ?_, ?_⟩
    · intro x y
      simp
    · intro x hx
      exfalso
      apply hx
      apply Subtype.ext
      apply LinearMap.ext
      intro w
      rw [hz w]
      simp
    · intro x y w w'
      rw [hz w, hz w']
      simp
    · intro x y w w'
      rw [hz w, hz w']
      simp [Lift.pet]

end GlobalTheory.ChainMetric
