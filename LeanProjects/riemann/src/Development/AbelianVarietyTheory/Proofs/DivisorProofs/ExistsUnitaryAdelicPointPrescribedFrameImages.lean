import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.SphEis.ColImg

open Formalism.UG (cT_mul cT_one)

section Ring

variable {S : Type} [CommRing S] (s : S →+* S)

theorem cT_add' {a b : Type} (M N : Matrix a b S) : cT s (M + N) = cT s M + cT s N := by
  ext i k; simp [cT]

theorem cT_zero' {a b : Type} : cT s (0 : Matrix a b S) = 0 := by
  ext i k; simp [cT]

theorem cT_cT' (hs : ∀ x, s (s x) = x) {a b : Type} (M : Matrix a b S) : cT s (cT s M) = M := by
  ext i k; simp [cT, hs]

theorem cT_gram {n a b : ℕ} (hs : ∀ x, s (s x) = x) (J : Matrix (Fin n) (Fin n) S) (hJ : cT s J = J)
    (M : Matrix (Fin n) (Fin a) S) (N : Matrix (Fin n) (Fin b) S) :
    cT s (cT s M * J * N) = cT s N * J * M := by
  rw [cT_mul, cT_mul, cT_cT' s hs, hJ, Matrix.mul_assoc]

theorem gram_comb {n j m : ℕ} (J : Matrix (Fin n) (Fin n) S) (J0 : Matrix (Fin m) (Fin m) S)
    (A B : Matrix (Fin n) (Fin j) S) (Z : Matrix (Fin n) (Fin m) S)
    (pX pY : Matrix (Fin j) (Fin n) S) (p0 : Matrix (Fin m) (Fin n) S)
    (aa : cT s A * J * A = 0) (bb : cT s B * J * B = 0) (ab : cT s A * J * B = 1) (ba : cT s B * J * A = 1)
    (az : cT s A * J * Z = 0) (bz : cT s B * J * Z = 0) (za : cT s Z * J * A = 0) (zb : cT s Z * J * B = 0)
    (zz : cT s Z * J * Z = J0) :
    cT s (A * pX + Z * p0 + B * pY) * J * (A * pX + Z * p0 + B * pY) =
      cT s pX * pY + cT s p0 * J0 * p0 + cT s pY * pX := by
  have h1 : cT s A * (J * (A * pX + Z * p0 + B * pY)) = pY := by
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, aa, az, ab, Matrix.zero_mul, Matrix.one_mul, zero_add]
  have h2 : cT s Z * (J * (A * pX + Z * p0 + B * pY)) = J0 * p0 := by
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, za, zz, zb, Matrix.zero_mul, zero_add, add_zero]
  have h3 : cT s B * (J * (A * pX + Z * p0 + B * pY)) = pX := by
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, ba, bz, bb, Matrix.zero_mul, Matrix.one_mul, zero_add, add_zero]
  rw [cT_add', cT_add', cT_mul, cT_mul, cT_mul]
  simp only [Matrix.add_mul, Matrix.mul_assoc, h1, h2, h3]

end Ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sig_invol {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem sigR_invol (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (e : AF F ⊗[F] E) :
    sigR (AF F) σ (sigR (AF F) σ e) = e := by
  induction e using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a x => simp [sigR, hσ]

theorem cT_adMat (σ : E →ₐ[F] E) {a b : Type} (X : Matrix a b E) :
    cT (sigR (AF F) σ) (adMat F X) = adMat F (cT (σ : E →+* E) X) := by
  ext i k; simp [cT, adMat, sigR, inclR]

end GlobalTheory.SphEis.ColImg

namespace GlobalTheory.SphEis.ColImg

open Formalism.UG (cT_mul cT_one)

section Ring

variable {S : Type} [CommRing S] (s : S →+* S)

theorem images_ring {n j m : ℕ} (Ja Jai : Matrix (Fin n) (Fin n) S) (j0 k0 : Matrix (Fin m) (Fin m) S)
    (hJi : Jai * Ja = 1) (hk0 : k0 * j0 = 1)
    (c d C' D' : Matrix (Fin n) (Fin j) S) (z Z' : Matrix (Fin n) (Fin m) S)
    (cc : cT s c * Ja * c = 0) (dd : cT s d * Ja * d = 0) (cd : cT s c * Ja * d = 1) (dc : cT s d * Ja * c = 1)
    (cz : cT s c * Ja * z = 0) (dz : cT s d * Ja * z = 0) (zc : cT s z * Ja * c = 0) (zd : cT s z * Ja * d = 0)
    (zz : cT s z * Ja * z = j0)
    (sum : c * (cT s d * Ja) + z * (k0 * (cT s z * Ja)) + d * (cT s c * Ja) = 1)
    (cc' : cT s C' * Ja * C' = 0) (dd' : cT s D' * Ja * D' = 0) (cd' : cT s C' * Ja * D' = 1) (dc' : cT s D' * Ja * C' = 1)
    (cz' : cT s C' * Ja * Z' = 0) (dz' : cT s D' * Ja * Z' = 0) (zc' : cT s Z' * Ja * C' = 0) (zd' : cT s Z' * Ja * D' = 0)
    (zz' : cT s Z' * Ja * Z' = j0) :
    ∃ u : GL (Fin n) S, cT s u.1 * Ja * u.1 = Ja ∧ u.1 * c = C' ∧ u.1 * z = Z' ∧ u.1 * d = D' := by
  obtain ⟨pX, hpX⟩ : ∃ p, p = cT s d * Ja := ⟨_, rfl⟩
  obtain ⟨p0, hp0⟩ : ∃ p, p = k0 * (cT s z * Ja) := ⟨_, rfl⟩
  obtain ⟨pY, hpY⟩ : ∃ p, p = cT s c * Ja := ⟨_, rfl⟩
  rw [← hpX, ← hp0, ← hpY] at sum
  have Xc : pX * c = 1 := by rw [hpX, dc]
  have Xz : pX * z = 0 := by rw [hpX, dz]
  have Xd : pX * d = 0 := by rw [hpX, dd]
  have Yc : pY * c = 0 := by rw [hpY, cc]
  have Yz : pY * z = 0 := by rw [hpY, cz]
  have Yd : pY * d = 1 := by rw [hpY, cd]
  have Oc : p0 * c = 0 := by rw [hp0, Matrix.mul_assoc, zc, Matrix.mul_zero]
  have Oz : p0 * z = 1 := by rw [hp0, Matrix.mul_assoc, zz, hk0]
  have Od : p0 * d = 0 := by rw [hp0, Matrix.mul_assoc, zd, Matrix.mul_zero]
  obtain ⟨g, hg⟩ : ∃ g, g = C' * pX + Z' * p0 + D' * pY := ⟨_, rfl⟩
  have gram : cT s g * Ja * g = Ja := by
    rw [hg, gram_comb s Ja j0 C' D' Z' pX pY p0 cc' dd' cd' dc' cz' dz' zc' zd' zz',
      ← gram_comb s Ja j0 c d z pX pY p0 cc dd cd dc cz dz zc zd zz, sum, cT_one, Matrix.one_mul, Matrix.mul_one]
  have hl : (Jai * cT s g * Ja) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT s g), gram, hJi]
  have hr : g * (Jai * cT s g * Ja) = 1 := mul_eq_one_comm.1 hl
  refine ⟨⟨g, Jai * cT s g * Ja, hr, hl⟩, gram, ?_, ?_, ?_⟩
  · change g * c = C'
    simp only [hg, Matrix.add_mul, Matrix.mul_assoc, Xc, Oc, Yc, Matrix.mul_zero, Matrix.mul_one, add_zero]
  · change g * z = Z'
    simp only [hg, Matrix.add_mul, Matrix.mul_assoc, Xz, Oz, Yz, Matrix.mul_zero, Matrix.mul_one, add_zero, zero_add]
  · change g * d = D'
    simp only [hg, Matrix.add_mul, Matrix.mul_assoc, Xd, Od, Yd, Matrix.mul_zero, Matrix.mul_one, add_zero, zero_add]

end Ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem adMat_gram (σ : E →ₐ[F] E) {n a b : ℕ} (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin a) E)
    (Y : Matrix (Fin n) (Fin b) E) (R : Matrix (Fin a) (Fin b) E) (h : cT (σ : E →+* E) X * J * Y = R) :
    cT (sigR (AF F) σ) (adMat F X) * adMat F J * adMat F Y = adMat F R := by
  rw [cT_adMat, adMat, adMat, adMat, adMat, ← Matrix.map_mul, ← Matrix.map_mul, h]

theorem adMat_zero' {a b : Type} : adMat F (0 : Matrix a b E) = 0 := Matrix.map_zero _ (map_zero _)

theorem adMat_one' {a : Type} [DecidableEq a] : adMat F (1 : Matrix a a E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

theorem adMat_mul' {a b c : Type} [Fintype b] (X : Matrix a b E) (Y : Matrix b c E) :
    adMat F (X * Y) = adMat F X * adMat F Y := Matrix.map_mul

end GlobalTheory.SphEis.ColImg

namespace GlobalTheory.SphEis.ColImg

open Formalism.UG (cT_mul cT_one)

theorem exists_point_images :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ (C' D' : Matrix (Fin n) (Fin j) (AF F ⊗[F] E)) (Z' : Matrix (Fin n) (Fin m) (AF F ⊗[F] E)), cT (sigR (AF F) σ) C' * adMat F J * C' = 0 → cT (sigR (AF F) σ) D' * adMat F J * D' = 0 → cT (sigR (AF F) σ) C' * adMat F J * D' = 1 → cT (sigR (AF F) σ) C' * adMat F J * Z' = 0 → cT (sigR (AF F) σ) D' * adMat F J * Z' = 0 → cT (sigR (AF F) σ) Z' * adMat F J * Z' = adMat F J₀ → ∃ g : GAd σ J, (matHom _ σ J g).1 * adMat F C = C' ∧ (matHom _ σ J g).1 * adMat F Z = Z' ∧ (matHom _ σ J g).1 * adMat F D = D' := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ fr C' D' Z' cc dd cd cz dz zz
  have hσ : ∀ x, σ (σ x) = x := sig_invol fr.cm
  have hs : ∀ x, sigR (AF F) σ (sigR (AF F) σ x) = x := sigR_invol σ hσ
  have hJ : cT (sigR (AF F) σ) (adMat F J) = adMat F J := by rw [cT_adMat, cT_form fr.herm]
  have dc : cT (sigR (AF F) σ) D' * adMat F J * C' = 1 := by
    rw [← cT_gram _ hs _ hJ, cd, cT_one]
  have zc : cT (sigR (AF F) σ) Z' * adMat F J * C' = 0 := by rw [← cT_gram _ hs _ hJ, cz, cT_zero']
  have zd : cT (sigR (AF F) σ) Z' * adMat F J * D' = 0 := by rw [← cT_gram _ hs _ hJ, dz, cT_zero']
  have acc := adMat_gram (F := F) σ J C C 0 fr.cc
  have add := adMat_gram (F := F) σ J D D 0 fr.dd
  have acd := adMat_gram (F := F) σ J C D 1 fr.cd
  have adc := adMat_gram (F := F) σ J D C 1 fr.dc
  have acz := adMat_gram (F := F) σ J C Z 0 fr.cz
  have adz := adMat_gram (F := F) σ J D Z 0 fr.dz
  have azc := adMat_gram (F := F) σ J Z C 0 fr.zc
  have azd := adMat_gram (F := F) σ J Z D 0 fr.zd
  have azz := adMat_gram (F := F) σ J Z Z J₀ fr.zz
  rw [adMat_zero'] at acc add acz adz azc azd
  rw [adMat_one'] at acd adc
  have hJ0 : adMat F J₀⁻¹ * adMat F J₀ = 1 := by
    rw [← adMat_mul', Matrix.nonsing_inv_mul _ (det_isUnit fr.herm₀), adMat_one']
  have hJi : adMat F J⁻¹ * adMat F J = 1 := by
    rw [← adMat_mul', Matrix.nonsing_inv_mul _ (det_isUnit fr.herm), adMat_one']
  have hsum : adMat F C * (cT (sigR (AF F) σ) (adMat F D) * adMat F J) +
      adMat F Z * (adMat F J₀⁻¹ * (cT (sigR (AF F) σ) (adMat F Z) * adMat F J)) +
      adMat F D * (cT (sigR (AF F) σ) (adMat F C) * adMat F J) = 1 := by
    have := congrArg (adMat F) fr.sum
    rw [adMat_one'] at this
    rw [← this, cT_adMat, cT_adMat, cT_adMat]
    simp only [adMat_mul', adMat, Matrix.map_add _ (map_add _)]
  obtain ⟨u, hu, h1, h2, h3⟩ := images_ring (sigR (AF F) σ) (adMat F J) (adMat F J⁻¹) (adMat F J₀) (adMat F J₀⁻¹) hJi hJ0
    (adMat F C) (adMat F D) C' D' (adMat F Z) Z' acc add acd adc acz adz azc azd azz hsum cc dd cd dc cz dz zc zd zz
  exact ⟨(show HA (AF F) σ J from (⟨u, hu⟩ : HR (AF F) σ J)), h1, h2, h3⟩

end GlobalTheory.SphEis.ColImg
