import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalStageTensorPolynomialOrigin
open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PolyOrigin

theorem originIdeal_eq_comap (T : Type) [CommRing T] [IsLocalRing T] :
    GlobalTheory.KeyOriginCut.originIdeal T = (maximalIdeal T).comap (Polynomial.constantCoeff : Polynomial T →+* T) := by
  ext g
  rw [GlobalTheory.LocalStage.mem_originIdeal_iff, Ideal.mem_comap, Polynomial.constantCoeff_apply]

theorem originIdeal_isMaximal (T : Type) [CommRing T] [IsLocalRing T] :
    (GlobalTheory.KeyOriginCut.originIdeal T).IsMaximal := by
  rw [originIdeal_eq_comap]
  exact Ideal.comap_isMaximal_of_surjective _ (fun a => ⟨Polynomial.C a, by simp⟩)

theorem mapRingHom_isIntegral {A S : Type} [CommRing A] [CommRing S] (f : A →+* S) (hf : f.IsIntegral) :
    (Polynomial.mapRingHom f).IsIntegral := by
  letI : Algebra (Polynomial A) (Polynomial S) := (Polynomial.mapRingHom f).toAlgebra
  have hC : ∀ s : S, IsIntegral (Polynomial A) (Polynomial.C s) := by
    intro s
    obtain ⟨P, hPm, hP⟩ := hf s
    refine ⟨P.map Polynomial.C, hPm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap (Polynomial A) (Polynomial S)).comp Polynomial.C = Polynomial.C.comp f := by
      refine RingHom.ext fun a => ?_
      change Polynomial.map f (Polynomial.C a) = _
      simp
    rw [hcomp, ← Polynomial.hom_eval₂, hP, map_zero]
  have hX : IsIntegral (Polynomial A) (Polynomial.X : Polynomial S) := by
    have : algebraMap (Polynomial A) (Polynomial S) Polynomial.X = Polynomial.X := Polynomial.map_X f
    rw [← this]
    exact isIntegral_algebraMap
  intro p
  change IsIntegral (Polynomial A) p
  induction p using Polynomial.induction_on with
  | C a => exact hC a
  | add p q hp hq => exact hp.add hq
  | monomial n a _ => exact (hC a).mul (hX.pow _)

theorem polyOrigin : ∀ (A S : Type) [CommRing A] [IsLocalRing A] [CommRing S] [IsLocalRing S] (f : A →+* S), f.IsIntegral →
    (Polynomial.mapRingHom f).IsIntegral ∧ (GlobalTheory.KeyOriginCut.originIdeal S).IsPrime ∧
    (GlobalTheory.KeyOriginCut.originIdeal S).comap (Polynomial.mapRingHom f) = GlobalTheory.KeyOriginCut.originIdeal A ∧
    ∀ 𝔔 : Ideal (Polynomial S), 𝔔.IsPrime → 𝔔.comap (Polynomial.mapRingHom f) = GlobalTheory.KeyOriginCut.originIdeal A → 𝔔 = GlobalTheory.KeyOriginCut.originIdeal S := by
  intro A S _ _ _ _ f hf

  have hmA : (maximalIdeal S).comap f = maximalIdeal A := by
    haveI := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' f hf (maximalIdeal S)
    exact IsLocalRing.eq_maximalIdeal this
  haveI hloc : IsLocalHom f := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have : a ∈ (maximalIdeal S).comap f := by
      rw [hmA]; exact (mem_maximalIdeal a).mpr hna
    exact (mem_maximalIdeal _).mp this ha
  refine ⟨mapRingHom_isIntegral f hf, (originIdeal_isMaximal S).isPrime,
    GlobalTheory.LocalStage.comap_originIdeal f, ?_⟩
  intro 𝔔 h𝔔 hc
  have hXmem : (Polynomial.X : Polynomial S) ∈ 𝔔 := by
    have : (Polynomial.X : Polynomial A) ∈ 𝔔.comap (Polynomial.mapRingHom f) := by
      rw [hc, GlobalTheory.LocalStage.mem_originIdeal_iff]; simp
    simpa using this

  haveI : (𝔔.comap (Polynomial.C : S →+* Polynomial S)).IsPrime := Ideal.comap_isPrime _ _
  have hcC : (𝔔.comap (Polynomial.C : S →+* Polynomial S)).comap f = maximalIdeal A := by
    ext a
    rw [Ideal.mem_comap, Ideal.mem_comap]
    have h1 : Polynomial.C (f a) = Polynomial.mapRingHom f (Polynomial.C a) := by simp
    rw [h1, ← Ideal.mem_comap, hc, GlobalTheory.LocalStage.mem_originIdeal_iff, Polynomial.coeff_C_zero]
  have hmax : (𝔔.comap (Polynomial.C : S →+* Polynomial S)).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' f hf _ (by rw [hcC]; infer_instance)
  have hP : 𝔔.comap (Polynomial.C : S →+* Polynomial S) = maximalIdeal S :=
    IsLocalRing.eq_maximalIdeal hmax
  have hle : GlobalTheory.KeyOriginCut.originIdeal S ≤ 𝔔 := by
    intro g hg
    rw [GlobalTheory.LocalStage.mem_originIdeal_iff] at hg
    rw [← Polynomial.X_mul_divX_add g]
    refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ hXmem) ?_
    have : g.coeff 0 ∈ 𝔔.comap (Polynomial.C : S →+* Polynomial S) := by rw [hP]; exact hg
    exact this
  exact ((originIdeal_isMaximal S).eq_of_le h𝔔.ne_top hle).symm

end GlobalTheory.PolyOrigin
