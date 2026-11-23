import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFHoriz
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace PFHoriz

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')}

def genMap (G : GenFibre v P') : MRing ι ⧸ imageZ v P' →+* G.Φ :=
  Ideal.Quotient.lift _ (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom
    (fun a ha => by rw [← G.ker_x] at ha; exact RingHom.mem_ker.mp ha)

theorem genMap_mk (G : GenFibre v P') (f : MRing ι) :
    genMap G (Ideal.Quotient.mk _ f) = aeval G.x f := rfl

theorem genMap_injective (G : GenFibre v P') : Function.Injective (genMap G) := by
  refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [genMap_mk] at ha
  rw [Ideal.Quotient.eq_zero_iff_mem, ← G.ker_x]
  exact RingHom.mem_ker.mpr ha

theorem isFractionRing_genMap (G : GenFibre v P') :
    @IsFractionRing (MRing ι ⧸ imageZ v P') _ G.Φ _ (genMap G).toAlgebra := by
  letI := (genMap G).toAlgebra
  haveI : FaithfulSMul (MRing ι ⧸ imageZ v P') G.Φ :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (genMap_injective G)
  refine IsFractionRing.of_field _ _ fun z => ?_
  obtain ⟨f, g, -, rfl⟩ := G.gen z
  exact ⟨Ideal.Quotient.mk _ f, Ideal.Quotient.mk _ g, rfl⟩

def quotIncl (W : Ideal (MRing ι')) [W.IsPrime] (hW : imageZ v W = imageZ v P') :
    MRing ι ⧸ imageZ v P' →+* FractionRing (MRing ι' ⧸ W) :=
  (algebraMap (MRing ι' ⧸ W) (FractionRing (MRing ι' ⧸ W))).comp
    (Ideal.quotientMap W (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom hW.symm.le)

theorem quotIncl_injective (W : Ideal (MRing ι')) [W.IsPrime] (hW : imageZ v W = imageZ v P') :
    Function.Injective (quotIncl W hW) :=
  (IsFractionRing.injective (MRing ι' ⧸ W) (FractionRing (MRing ι' ⧸ W))).comp
    (Ideal.quotientMap_injective' (H := hW.symm.le) hW.le)

def genAlg (G : GenFibre v P') (W : Ideal (MRing ι')) [W.IsPrime] (hW : imageZ v W = imageZ v P') :
    G.Φ →+* FractionRing (MRing ι' ⧸ W) :=
  letI := (genMap G).toAlgebra
  haveI := isFractionRing_genMap G
  IsFractionRing.lift (quotIncl_injective W hW)

theorem genAlg_alt (G : GenFibre v P') (W : Ideal (MRing ι')) [W.IsPrime] (hW : imageZ v W = imageZ v P')
    (p : Σ k, ι k) :
    genAlg G W hW (G.x p) =
      algebraMap (MRing ι' ⧸ W) (FractionRing (MRing ι' ⧸ W)) (Ideal.Quotient.mk W (X (v p))) := by
  letI := (genMap G).toAlgebra
  haveI := isFractionRing_genMap G
  have hx : G.x p = algebraMap (MRing ι ⧸ imageZ v P') G.Φ (Ideal.Quotient.mk _ (X p)) := by
    show G.x p = genMap G (Ideal.Quotient.mk _ (X p))
    rw [genMap_mk, aeval_X]
  rw [hx]
  exact (IsFractionRing.lift_algebraMap (quotIncl_injective W hW) _).trans (by
    simp [quotIncl, Ideal.quotientMap_mk])

def xW (W : Ideal (MRing ι')) [W.IsPrime] (q : Σ k', ι' k') : FractionRing (MRing ι' ⧸ W) :=
  algebraMap (MRing ι' ⧸ W) (FractionRing (MRing ι' ⧸ W)) (Ideal.Quotient.mk W (X q))

theorem aeval_xW (W : Ideal (MRing ι')) [W.IsPrime] (f : MRing ι') :
    aeval (R := ℤ) (xW W) f =
      algebraMap (MRing ι' ⧸ W) (FractionRing (MRing ι' ⧸ W)) (Ideal.Quotient.mk W f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C, eq_intCast (algebraMap ℤ (FractionRing (MRing ι' ⧸ W))) a]
    exact (eq_intCast (((algebraMap (MRing ι' ⧸ W) (FractionRing (MRing ι' ⧸ W))).comp
      (Ideal.Quotient.mk W)).comp C) a).symm
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p n hp => rw [map_mul, map_mul, map_mul, hp, aeval_X, xW]

theorem ker_aeval_xW (W : Ideal (MRing ι')) [W.IsPrime] :
    RingHom.ker (aeval (R := ℤ) (xW W)) = W := by
  ext f
  rw [RingHom.mem_ker, aeval_xW, map_eq_zero_iff _ (IsFractionRing.injective _ _),
    Ideal.Quotient.eq_zero_iff_mem]

def genFibreOf (G : GenFibre v P') (W : Ideal (MRing ι')) [W.IsPrime] (hW : imageZ v W = imageZ v P') :
    GenFibre v W where
  Φ := G.Φ
  Φ' := FractionRing (MRing ι' ⧸ W)
  alg := (genAlg G W hW).toAlgebra
  x := G.x
  x' := xW W
  ker_x := by rw [hW]; exact G.ker_x
  gen := G.gen
  genericFibre_ker_target := by
    refine Eq.trans ?_ (ker_aeval_xW W)
    ext f
    simp only [RingHom.mem_ker, aeval_def, algebraMap_int_eq]
    rw [RingHom.ext_int (algebraMap ℤ (FractionRing (MRing ι' ⧸ W))) (Int.castRingHom _)]
  compat p := (genAlg_alt G W hW p).symm

theorem baseSubst_rename (hκv : IsBlockMap κ v) (G : GenFibre v P') (f : MRing ι) :
    baseSubst κ G (rename v f) = C (aeval G.x f) := by
  have e : (baseSubst κ G).comp (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom =
      (C : G.Φ →+* MRingOver G.Φ (fibreIdx ι' κ)).comp (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun p => ?_)
    · exact RingHom.congr_fun (RingHom.ext_int (((baseSubst κ G).comp
        (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom).comp C)
        (((C : G.Φ →+* MRingOver G.Φ (fibreIdx ι' κ)).comp
          (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom).comp C)) a
    · have h1 : (v p).1 ∈ Set.range κ := ⟨p.1, (hκv.2.2.1 p).symm⟩
      have h2 : v p ∈ Set.range v := ⟨p, rfl⟩
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X, aeval_X]
      rw [baseSubst, eval₂Hom_X', dif_pos h1, dif_pos h2, hκv.2.1 h2.choose_spec]
  exact RingHom.congr_fun e f

theorem exists_clear (hκv : IsBlockMap κ v) (G : GenFibre v P') (g : MRingOver G.Φ (fibreIdx ι' κ)) :
    ∃ (b : MRing ι) (F : MRing ι'), aeval G.x b ≠ 0 ∧ C (aeval G.x b) * g = baseSubst κ G F := by
  induction g using MvPolynomial.induction_on with
  | C a =>
    obtain ⟨f, b, hb, rfl⟩ := G.gen a
    refine ⟨b, rename v f, hb, ?_⟩
    rw [baseSubst_rename hκv, ← C_mul, mul_div_cancel₀ _ hb]
  | add p q hp hq =>
    obtain ⟨b₁, F₁, h₁, e₁⟩ := hp
    obtain ⟨b₂, F₂, h₂, e₂⟩ := hq
    refine ⟨b₁ * b₂, rename v b₂ * F₁ + rename v b₁ * F₂, by rw [map_mul]; exact mul_ne_zero h₁ h₂, ?_⟩
    simp only [map_add, map_mul, baseSubst_rename hκv, ← e₁, ← e₂]
    ring
  | mul_X p n hp =>
    obtain ⟨b, F, h, e⟩ := hp
    refine ⟨b, F * X ⟨n.1.1, n.2⟩, h, ?_⟩
    rw [map_mul, ← e, mul_assoc]
    congr 2
    rw [baseSubst, eval₂Hom_X', dif_neg n.1.2]

theorem ker_eq_map {σ τ Φ Φ' : Type} [Field Φ] [Field Φ'] [Algebra Φ Φ']
    (β : MvPolynomial τ ℤ →+* MvPolynomial σ Φ) (y : σ → Φ') (φ : MvPolynomial τ ℤ →+* Φ')
    (W : Ideal (MvPolynomial τ ℤ)) (hφ : RingHom.ker φ = W) (hcomp : ∀ F, aeval y (β F) = φ F)
    (hclear : ∀ g, ∃ c : Φ, c ≠ 0 ∧ ∃ F, C c * g = β F) :
    RingHom.ker (aeval y : MvPolynomial σ Φ →ₐ[Φ] Φ') = Ideal.map β W := by
  apply le_antisymm
  · intro g hg
    obtain ⟨c, hc, F, e⟩ := hclear g
    have hF : F ∈ W := by
      rw [← hφ, RingHom.mem_ker, ← hcomp, ← e, map_mul, RingHom.mem_ker.mp hg, mul_zero]
    have hg' : g = C c⁻¹ * β F := by
      rw [← e, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hc, C_1, one_mul]
    rw [hg']
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hF)
  · rw [Ideal.map_le_iff_le_comap]
    intro F hF
    rw [Ideal.mem_comap, RingHom.mem_ker, hcomp, ← RingHom.mem_ker, hφ]
    exact hF

variable {W : Ideal (MRing ι')} [W.IsPrime] (hW : imageZ v W = imageZ v P')

theorem aeval_baseSubst (hκv : IsBlockMap κ v) (G : GenFibre v P') (f : MRing ι') :
    letI := (genAlg G W hW).toAlgebra
    aeval (fun q : Σ k : FibreBlock κ, ι' k.1 => xW W ⟨q.1.1, q.2⟩) (baseSubst κ G f) =
      aeval (R := ℤ) (xW W) f := by
  letI := (genAlg G W hW).toAlgebra
  have e : (aeval (fun q : Σ k : FibreBlock κ, ι' k.1 => xW W ⟨q.1.1, q.2⟩) :
        MRingOver G.Φ (fibreIdx ι' κ) →ₐ[G.Φ] FractionRing (MRing ι' ⧸ W)).toRingHom.comp (baseSubst κ G) =
      (aeval (R := ℤ) (xW W)).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun q => ?_)
    · rw [RingHom.comp_apply, baseSubst, eval₂Hom_C,
        eq_intCast (algebraMap ℤ (MRingOver G.Φ (fibreIdx ι' κ))) a, eq_intCast (C : ℤ →+* MRing ι') a,
        map_intCast, map_intCast]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
      rw [baseSubst, eval₂Hom_X']
      by_cases h : q.1 ∈ Set.range κ
      · have h' : q ∈ Set.range v := hκv.2.2.2 q h
        rw [dif_pos h, dif_pos h', aeval_C, RingHom.algebraMap_toAlgebra, genAlg_alt, h'.choose_spec]
        rfl
      · rw [dif_neg h, aeval_X]
  exact RingHom.congr_fun e f

theorem fibreIdeal_genFibreOf (hκv : IsBlockMap κ v) (G : GenFibre v P') :
    fibreIdeal κ (genFibreOf G W hW) = fibreOf κ G W := by
  letI := (genAlg G W hW).toAlgebra
  exact ker_eq_map (baseSubst κ G) (fun q : Σ k : FibreBlock κ, ι' k.1 => xW W ⟨q.1.1, q.2⟩)
    (aeval (R := ℤ) (xW W)).toRingHom W (ker_aeval_xW W) (aeval_baseSubst hW hκv G)
    (fun g => let ⟨_, F, hb, e⟩ := exists_clear hκv G g; ⟨_, hb, F, e⟩)

end PFHoriz

theorem PFHoriz.proof : PFHoriz.Statement := by
  intro I r hPF K _ ι _ K' _ ι' _ κ v P' W d G J L L' N hκv hW hWP hP hJ hL hLL hN
  haveI : W.IsPrime := hW.2.1.1
  have h := hPF K ι K' ι' κ v W d (PFHoriz.genFibreOf G W hWP) J L L' N hκv hW (by rw [hWP]; exact hP)
    hJ hL hLL hN
  rw [PFHoriz.fibreIdeal_genFibreOf hWP hκv G, hWP] at h
  exact h

end

end GroundTheory.Heights₂.Heights.Inter
