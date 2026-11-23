import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianFormPrimitiveVectorPairingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorel
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WittExtensionArtinianRingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearlyIndependentFramesOpen

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.FreeTrans

section Form

variable {A : Type} [CommRing A] {n : ℕ} (s : A →+* A) (J : Matrix (Fin n) (Fin n) A)

theorem hform_add_right (x y z : Fin n → A) :
    hform s J x (y + z) = hform s J x y + hform s J x z := by
  simp only [hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hform_add_left (x y z : Fin n → A) :
    hform s J (x + y) z = hform s J x z + hform s J y z := by
  simp only [hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem hform_smul_right (t : A) (x y : Fin n → A) :
    hform s J x (t • y) = t * hform s J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_smul_left (t : A) (x y : Fin n → A) :
    hform s J (t • x) y = s t * hform s J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Form

theorem exists_hyperbolic_partner {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : IsHermND σ J) (R : Type) [CommRing R] [Algebra F R] (x y : Fin M → R ⊗[F] E)
    (hxx : hR R σ J x x = 0) (hxy : hR R σ J x y = 1) :
    ∃ y₁ : Fin M → R ⊗[F] E, hR R σ J x y₁ = 1 ∧ hR R σ J y₁ x = 1 ∧ hR R σ J y₁ y₁ = 0 := by
  have herm : ∀ u v : Fin M → R ⊗[F] E, sigR R σ (hR R σ J u v) = hR R σ J v u := by
    intro u v
    have h : ∀ a b, sigR R σ (gramR R σ J ![u, v] b a) = gramR R σ J ![u, v] a b :=
      GlobalTheory.CompanionTheory.SW.HermTop.gramR_mem R (GlobalTheory.CompanionTheory.SW.HermTop.sigma_sigma hσ) hJ.1 ![u, v]
    simpa [gramR] using h 1 0
  have hyx : hR R σ J y x = 1 := by rw [← herm, hxy, map_one]
  set c : R ⊗[F] E := algebraMap F (R ⊗[F] E) (1 / 2) with hc
  have hcc : c + c = 1 := by
    rw [hc, ← map_add, ← map_one (algebraMap F (R ⊗[F] E))]
    norm_num
  have hsc : sigR R σ c = c := AlgHom.commutes (Algebra.TensorProduct.map (AlgHom.id F R) σ) _
  set q := hR R σ J y y with hq
  have hsq : sigR R σ q = q := herm y y
  refine ⟨y + (-(c * q)) • x, ?_, ?_, ?_⟩
  · have : hR R σ J x (y + (-(c * q)) • x) = hR R σ J x y + -(c * q) * hR R σ J x x := by
      simp only [hR, hform_add_right, hform_smul_right]
    rw [this, hxx, hxy]
    ring
  · have : hR R σ J (y + (-(c * q)) • x) x =
        hR R σ J y x + sigR R σ (-(c * q)) * hR R σ J x x := by
      simp only [hR, hform_add_left, hform_smul_left]
    rw [this, hxx, hyx]
    ring
  · have : hR R σ J (y + (-(c * q)) • x) (y + (-(c * q)) • x) =
        hR R σ J y y + -(c * q) * hR R σ J y x + (sigR R σ (-(c * q)) * hR R σ J x y +
          sigR R σ (-(c * q)) * (-(c * q) * hR R σ J x x)) := by
      simp only [hR, hform_add_left, hform_add_right, hform_smul_left, hform_smul_right]
      ring
    rw [this, hxx, hxy, hyx, ← hq, map_neg, map_mul, hsc, hsq]
    linear_combination (-q) * hcc

theorem transitive_free_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ X Y : Fin 1 → Fin M → R ⊗[F] E, LinearIndependent (R ⊗[F] E) X → LinearIndependent (R ⊗[F] E) Y → gramR R σ J X = 0 → gramR R σ J Y = 0 → ∃ h : HA R σ J, actW R σ J h X = Y := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hL X Y hX hY gX gY
  haveI : IsArtinianRing R := hL.2.2.2.2.1
  haveI : IsReduced R := hL.2.2.2.2.2.1
  have hconst : ∀ Z : Fin 1 → Fin M → R ⊗[F] E, (fun _ : Fin 1 => Z 0) = Z := by
    intro Z
    funext a
    rw [Subsingleton.elim a 0]
  have hlx : LinearIndependent (R ⊗[F] E) (fun _ : Fin 1 => X 0) := by rwa [hconst]
  have hly : LinearIndependent (R ⊗[F] E) (fun _ : Fin 1 => Y 0) := by rwa [hconst]
  have hxx : hR R σ J (X 0) (X 0) = 0 := congrFun (congrFun gX 0) 0
  have hyy : hR R σ J (Y 0) (Y 0) = 0 := congrFun (congrFun gY 0) 0
  obtain ⟨y, hy⟩ := GlobalTheory.T.hermitian_form_primitive_vector_pairing F E σ hσ M J hJ R hL (X 0) hlx
  obtain ⟨y', hy'⟩ := GlobalTheory.T.hermitian_form_primitive_vector_pairing F E σ hσ M J hJ R hL (Y 0) hly
  obtain ⟨u, hu1, hu2, hu3⟩ := exists_hyperbolic_partner hσ hJ R (X 0) y hxx hy
  obtain ⟨u', hu1', hu2', hu3'⟩ := exists_hyperbolic_partner hσ hJ R (Y 0) y' hyy hy'
  have hG : gramR R σ J ![X 0, u] = !![0, 1; 1, 0] := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [gramR, hxx, hu1, hu2, hu3]
  have hG' : gramR R σ J ![Y 0, u'] = !![0, 1; 1, 0] := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [gramR, hyy, hu1', hu2', hu3']
  have hdet : IsUnit (gramR R σ J ![X 0, u]).det := by
    rw [hG, Matrix.det_fin_two_of]
    simp
  obtain ⟨h, hh⟩ := GlobalTheory.T.witt_extension_artinian_ring F E σ hσ M J hJ R 2 ![X 0, u] ![Y 0, u'] (hG.trans hG'.symm) hdet
  refine ⟨h, ?_⟩
  funext a
  rw [Subsingleton.elim a 0]
  simpa [actW, actTup] using congrFun hh 0

end GlobalTheory.CompanionTheory.WeilSiegel.FreeTrans
