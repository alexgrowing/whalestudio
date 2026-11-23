import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdaptedLatticeFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT)

namespace GlobalTheory.WittCompl

section Alg

variable {E : Type} [Field E]

theorem cT_cT_inv {s : E →+* E} (hs : ∀ x, s (s x) = x) {p q : Type} (M : Matrix p q E) :
    cT s (cT s M) = M := by
  ext i j; simp [Formalism.UG.cT, hs]

theorem cT_zero' (s : E →+* E) {p q : Type} : cT s (0 : Matrix p q E) = 0 := by
  ext i j; simp [Formalism.UG.cT]

theorem cT_sandwich {s : E →+* E} (hs : ∀ x, s (s x) = x) {n a b : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : cT s J = J) (A : Matrix (Fin n) (Fin a) E) (B : Matrix (Fin n) (Fin b) E) :
    cT s (cT s A * J * B) = cT s B * J * A := by
  rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, cT_cT_inv hs, hJ, Matrix.mul_assoc]

variable {n r : ℕ} (X Y : Matrix (Fin n) (Fin r) E) (a b : Matrix (Fin r) (Fin n) E)

theorem projC_mul_X (haX : a * X = 0) (hbX : b * X = 1) :
    (1 - X * b - Y * a) * X = 0 := by
  simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hbX, haX, Matrix.mul_one, Matrix.mul_zero,
    sub_self, sub_zero]

theorem projC_mul_Y (haY : a * Y = 1) (hbY : b * Y = 0) :
    (1 - X * b - Y * a) * Y = 0 := by
  simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hbY, haY, Matrix.mul_one, Matrix.mul_zero,
    sub_self, sub_zero]

theorem a_mul_projC (haX : a * X = 0) (haY : a * Y = 1) :
    a * (1 - X * b - Y * a) = 0 := by
  simp only [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, haX, haY, Matrix.zero_mul, Matrix.one_mul,
    sub_zero, sub_self]

theorem b_mul_projC (hbX : b * X = 1) (hbY : b * Y = 0) :
    b * (1 - X * b - Y * a) = 0 := by
  simp only [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hbX, hbY, Matrix.zero_mul, Matrix.one_mul,
    sub_zero, sub_self]

theorem projC_idem (haX : a * X = 0) (haY : a * Y = 1) (hbX : b * X = 1) (hbY : b * Y = 0) :
    (1 - X * b - Y * a) * (1 - X * b - Y * a) = 1 - X * b - Y * a := by
  conv_lhs => rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc,
    a_mul_projC X Y a b haX haY, b_mul_projC X Y a b hbX hbY, Matrix.mul_zero, Matrix.mul_zero, sub_zero, sub_zero]

end Alg

end GlobalTheory.WittCompl

namespace GlobalTheory.WittCompl

theorem exists_complement_data : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n r : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
    ∃ (m : ℕ) (I : Matrix (Fin n) (Fin m) E) (Q : Matrix (Fin m) (Fin n) E), m + 2 * r = n ∧
      cT (σ : E →+* E) I * J * X = 0 ∧ cT (σ : E →+* E) I * J * Y = 0 ∧
      cT (σ : E →+* E) X * J * I = 0 ∧ cT (σ : E →+* E) Y * J * I = 0 ∧
      Q * X = 0 ∧ Q * Y = 0 ∧ Q * I = 1 ∧ (cT (σ : E →+* E) I * J * I) * Q = cT (σ : E →+* E) I * J ∧
      X * (cT (σ : E →+* E) Y * J) + I * Q + Y * (cT (σ : E →+* E) X * J) = 1 ∧
      IsHermND σ (cT (σ : E →+* E) I * J * I) := by
  intro F E _ _ _ _ _ σ hcm n r J hJ X Y hW
  have hs : ∀ x, (σ : E →+* E) ((σ : E →+* E) x) = x := fun x => GlobalTheory.SiegelSet.sigma_sigma (σ := σ) hcm x
  have hJs : cT (σ : E →+* E) J = J := by
    ext i j; exact hJ.1 i j
  have hyx : cT (σ : E →+* E) Y * J * X = 1 := by
    rw [← cT_sandwich hs hJs X Y, hW.xy, Formalism.UG.cT_one]
  have hxx := hW.xx
  have hyy := hW.yy
  have hxy := hW.xy
  generalize ha : cT (σ : E →+* E) X * J = a at hxx hxy
  generalize hb : cT (σ : E →+* E) Y * J = b at hyy hyx
  set P : Matrix (Fin n) (Fin n) E := 1 - X * b - Y * a with hP
  have hPX : P * X = 0 := projC_mul_X X Y a b hxx hyx
  have hPY : P * Y = 0 := projC_mul_Y X Y a b hxy hyy
  have haP : a * P = 0 := a_mul_projC X Y a b hxx hxy
  have hbP : b * P = 0 := b_mul_projC X Y a b hyx hyy
  have hPP : P * P = P := projC_idem X Y a b hxx hxy hyx hyy

  let V0 : Submodule E (Fin n → E) := LinearMap.range (Matrix.toLin' P)
  have hPV : ∀ v ∈ V0, Matrix.toLin' P v = v := by
    rintro v ⟨w, rfl⟩
    rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, hPP]
  let m := Module.finrank E V0
  let bas : Module.Basis (Fin m) E V0 := Module.finBasis E V0
  let g : (Fin m → E) →ₗ[E] (Fin n → E) := V0.subtype ∘ₗ bas.equivFun.symm.toLinearMap
  let f : (Fin n → E) →ₗ[E] (Fin m → E) := bas.equivFun.toLinearMap ∘ₗ (Matrix.toLin' P).rangeRestrict
  have hgf : g ∘ₗ f = Matrix.toLin' P := by
    refine LinearMap.ext fun z => ?_; simp [g, f]
  have hfg : f ∘ₗ g = LinearMap.id := by
    refine LinearMap.ext fun c => ?_
    have hv : (Matrix.toLin' P).rangeRestrict (bas.equivFun.symm c : Fin n → E) = bas.equivFun.symm c :=
      Subtype.ext (by simpa using hPV _ (bas.equivFun.symm c).2)
    simp only [f, g, LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe, hv,
      LinearEquiv.apply_symm_apply, LinearMap.id_apply]
  let I : Matrix (Fin n) (Fin m) E := LinearMap.toMatrix' g
  let Q : Matrix (Fin m) (Fin n) E := LinearMap.toMatrix' f
  have hIQ : I * Q = P := by
    rw [← LinearMap.toMatrix'_comp, hgf, LinearMap.toMatrix'_toLin']
  have hQI : Q * I = 1 := by
    rw [← LinearMap.toMatrix'_comp, hfg, LinearMap.toMatrix'_id]
  have hPI : P * I = I := by rw [← hIQ, Matrix.mul_assoc, hQI, Matrix.mul_one]
  have hQP : Q * P = Q := by rw [← hIQ, ← Matrix.mul_assoc, hQI, Matrix.one_mul]
  have hQX : Q * X = 0 := by rw [← hQP, Matrix.mul_assoc, hPX, Matrix.mul_zero]
  have hQY : Q * Y = 0 := by rw [← hQP, Matrix.mul_assoc, hPY, Matrix.mul_zero]
  have haI : a * I = 0 := by rw [← hPI, ← Matrix.mul_assoc, haP, Matrix.zero_mul]
  have hbI : b * I = 0 := by rw [← hPI, ← Matrix.mul_assoc, hbP, Matrix.zero_mul]
  have hIX : cT (σ : E →+* E) I * J * X = 0 := by
    rw [← cT_sandwich hs hJs X I, ha, haI, cT_zero']
  have hIY : cT (σ : E →+* E) I * J * Y = 0 := by
    rw [← cT_sandwich hs hJs Y I, hb, hbI, cT_zero']
  have hGQ : (cT (σ : E →+* E) I * J * I) * Q = cT (σ : E →+* E) I * J := by
    rw [Matrix.mul_assoc, hIQ, hP, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, hIX, hIY, Matrix.zero_mul, Matrix.zero_mul, sub_zero, sub_zero]
  have h1 : X * b + I * Q + Y * a = 1 := by rw [hIQ, hP]; abel

  have hdim : m + 2 * r = n := by
    let Φ : (Fin r → E) × ((Fin m → E) × (Fin r → E)) →ₗ[E] (Fin n → E) :=
      (Matrix.toLin' X).coprod ((Matrix.toLin' I).coprod (Matrix.toLin' Y))
    let Ψ : (Fin n → E) →ₗ[E] (Fin r → E) × ((Fin m → E) × (Fin r → E)) :=
      (Matrix.toLin' b).prod ((Matrix.toLin' Q).prod (Matrix.toLin' a))
    have hΦΨ : Φ ∘ₗ Ψ = LinearMap.id := by
      refine LinearMap.ext fun z => ?_
      simp only [Φ, Ψ, LinearMap.comp_apply, LinearMap.prod_apply, LinearMap.coprod_apply, Function.prod,
        Matrix.toLin'_apply, Matrix.mulVec_mulVec, LinearMap.id_apply]
      rw [← Matrix.add_mulVec, ← Matrix.add_mulVec, ← add_assoc, h1, Matrix.one_mulVec]
    have hΨΦ : Ψ ∘ₗ Φ = LinearMap.id := by
      refine LinearMap.ext fun ⟨u, c, w⟩ => ?_
      simp only [Φ, Ψ, LinearMap.comp_apply, LinearMap.prod_apply, LinearMap.coprod_apply, Function.prod,
        Matrix.toLin'_apply, Matrix.mulVec_add, Matrix.mulVec_mulVec, LinearMap.id_apply, hyx, hbI, hyy,
        hQX, hQI, hQY, hxx, haI, hxy, Matrix.one_mulVec, Matrix.zero_mulVec, add_zero, zero_add]
    let e : (Fin n → E) ≃ₗ[E] ((Fin r → E) × ((Fin m → E) × (Fin r → E))) :=
      LinearEquiv.ofLinear Ψ Φ hΨΦ hΦΨ
    have := e.finrank_eq
    simp only [Module.finrank_prod, Module.finrank_fin_fun] at this
    omega
  refine ⟨m, I, Q, hdim, hIX, hIY, ?_, ?_, hQX, hQY, hQI, hGQ, ?_, ?_⟩
  · exact haI
  · exact hbI
  · exact h1
  · refine ⟨fun i j => ?_, ?_⟩
    · have hG : cT (σ : E →+* E) (cT (σ : E →+* E) I * J * I) = cT (σ : E →+* E) I * J * I :=
        cT_sandwich hs hJs I I
      have := congrFun (congrFun hG i) j
      exact this
    · have hJinv : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J (isUnit_iff_ne_zero.mpr hJ.2)
      have hinv : (cT (σ : E →+* E) I * J * I) * (Q * J⁻¹ * cT (σ : E →+* E) Q) = 1 := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hGQ, Matrix.mul_assoc (cT _ I), hJinv, Matrix.mul_one,
          ← Formalism.UG.cT_mul, hQI, Formalism.UG.cT_one]
      exact (Matrix.isUnit_det_of_right_inverse hinv).ne_zero

end GlobalTheory.WittCompl
