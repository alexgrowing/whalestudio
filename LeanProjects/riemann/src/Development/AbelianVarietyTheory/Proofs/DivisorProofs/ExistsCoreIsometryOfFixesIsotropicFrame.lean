import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.SphEis.CoreIsom

theorem cT_add' {A : Type} [CommRing A] (s : A →+* A) {p q : ℕ} (X Y : Matrix (Fin p) (Fin q) A) :
    cT s (X + Y) = cT s X + cT s Y := by
  ext i k; simp [cT]

theorem unitary_core {A : Type} [CommRing A] (s : A →+* A) {n j m : ℕ} {J : Matrix (Fin n) (Fin n) A}
    {J₀ : Matrix (Fin m) (Fin m) A} {C : Matrix (Fin n) (Fin j) A} {Z : Matrix (Fin n) (Fin m) A}
    {G : Matrix (Fin n) (Fin n) A} {M : Matrix (Fin m) (Fin m) A} {b : Matrix (Fin j) (Fin m) A}
    (hG : cT s G * J * G = J) (hcz : cT s C * J * Z = 0) (hzc : cT s Z * J * C = 0)
    (hcc : cT s C * J * C = 0) (hzz : cT s Z * J * Z = J₀) (hGZ : G * Z = Z * M + C * b) :
    cT s M * J₀ * M = J₀ := by
  have e : cT s (G * Z) * J * (G * Z) = J₀ := by
    calc cT s (G * Z) * J * (G * Z) = cT s Z * (cT s G * J * G) * Z := by
          rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = J₀ := by rw [hG, hzz]
  rw [hGZ, cT_add', Formalism.UG.cT_mul, Formalism.UG.cT_mul] at e
  have h : (cT s M * cT s Z + cT s b * cT s C) * J * (Z * M + C * b) =
      cT s M * (cT s Z * J * Z) * M + cT s M * (cT s Z * J * C) * b +
        (cT s b * (cT s C * J * Z) * M + cT s b * (cT s C * J * C) * b) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]; abel
  rw [h, hzz, hzc, hcz, hcc] at e
  simpa using e

theorem isUnit_of_form {A : Type} [CommRing A] (s : A →+* A) {m : ℕ} {J₀ M : Matrix (Fin m) (Fin m) A}
    (h : cT s M * J₀ * M = J₀) (hJ : IsUnit J₀.det) : IsUnit M := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have e := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul] at e
  rw [← e] at hJ
  exact isUnit_of_mul_isUnit_right hJ

end GlobalTheory.SphEis.CoreIsom

open GlobalTheory.SphEis.CoreIsom in

theorem GlobalTheory.SphEis.core_isom : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ g ∈ fixG σ J C, ∃ (g₀ : GAd σ J₀) (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)), (matHom _ σ J g).1 * adMat F Z = adMat F Z * (matHom _ σ J₀ g₀).1 + adMat F C * b ∧ b = adMat F (cT (σ : E →+* E) D * J) * (matHom _ σ J g).1 * adMat F Z ∧ (matHom _ σ J₀ g₀).1 = adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) * (matHom _ σ J g).1 * adMat F Z ∧ (g ∈ ratPts σ J → g₀ ∈ ratPts σ J₀) := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF g hg
  have hmap : ∀ {a b c d : ℕ} (X : Matrix (Fin a) (Fin b) E) (Y : Matrix (Fin a) (Fin c) E)
      (W : Matrix (Fin c) (Fin d) E), cT (sigR (AF F) σ) (adMat F X) * adMat F Y * adMat F W =
        adMat F (cT (σ : E →+* E) X * Y * W) := by
    intro a b c d X Y W
    rw [adMat, adMat, adMat, GlobalTheory.AutFunCounterexample.cT_map_gen, ← Matrix.map_mul, ← Matrix.map_mul]
  have hgC : (matHom _ σ J g).1 * adMat F C = adMat F C := hg
  have hCJ : adMat F (cT (σ : E →+* E) C * J) * (matHom _ σ J g).1 = adMat F (cT (σ : E →+* E) C * J) := by
    have h1 : (matHom _ σ J g⁻¹).1 * adMat F C = adMat F C * (1 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) := by
      rw [Matrix.mul_one]
      conv_lhs => rw [← hgC]
      rw [← Matrix.mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul]
    have h2 := form_mul_of_mul_cols h1
    rwa [inv_inv, Formalism.UG.cT_one, Matrix.one_mul] at h2
  have hsum : adMat F C * adMat F (cT (σ : E →+* E) D * J) + adMat F Z * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) +
      adMat F D * adMat F (cT (σ : E →+* E) C * J) = 1 := by
    simp only [adMat]
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add _),
      ← Matrix.map_add _ (map_add _), hF.sum, Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨M, hM⟩ : ∃ M, M = adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) * (matHom _ σ J g).1 * adMat F Z := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = adMat F (cT (σ : E →+* E) D * J) * (matHom _ σ J g).1 * adMat F Z := ⟨_, rfl⟩
  have hZ : (matHom _ σ J g).1 * adMat F Z = adMat F Z * M + adMat F C * b := by
    calc (matHom _ σ J g).1 * adMat F Z = (adMat F C * adMat F (cT (σ : E →+* E) D * J) +
          adMat F Z * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) + adMat F D * adMat F (cT (σ : E →+* E) C * J)) *
          ((matHom _ σ J g).1 * adMat F Z) := by rw [hsum, Matrix.one_mul]
      _ = adMat F C * (adMat F (cT (σ : E →+* E) D * J) * (matHom _ σ J g).1 * adMat F Z) +
          adMat F Z * (adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) * (matHom _ σ J g).1 * adMat F Z) +
          adMat F D * (adMat F (cT (σ : E →+* E) C * J) * (matHom _ σ J g).1 * adMat F Z) := by
        simp only [Matrix.add_mul, Matrix.mul_assoc]
      _ = adMat F Z * M + adMat F C * b := by
        rw [hCJ, ← hM, ← hb]
        have h0 : adMat F (cT (σ : E →+* E) C * J) * adMat F Z = 0 := by
          simp only [adMat]; rw [← Matrix.map_mul, hF.cz]; simp
        rw [h0, Matrix.mul_zero, add_zero, add_comm]
  have hG : cT (sigR (AF F) σ) (matHom _ σ J g).1 * adMat F J * (matHom _ σ J g).1 = adMat F J := g.2
  have hMu : cT (sigR (AF F) σ) M * adMat F J₀ * M = adMat F J₀ :=
    unitary_core (sigR (AF F) σ) hG (by rw [hmap, hF.cz]; simp) (by rw [hmap, hF.zc]; simp)
      (by rw [hmap, hF.cc]; simp) (by rw [hmap, hF.zz]) hZ
  have hdet : IsUnit (adMat F J₀).det := by
    rw [adMat, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (Ne.isUnit hF.herm₀.2).map _
  have hMU := isUnit_of_form _ hMu hdet
  let g₀ : GAd σ J₀ := ⟨hMU.unit, by
    show cT (sigR (AF F) σ) (hMU.unit : Matrix (Fin m) (Fin m) (AF F ⊗[F] E)) * adMat F J₀ * hMU.unit = adMat F J₀
    rw [hMU.unit_spec]; exact hMu⟩
  have hg₀ : (matHom _ σ J₀ g₀).1 = M := hMU.unit_spec
  refine ⟨g₀, b, ?_, hb, ?_, ?_⟩
  · rw [hg₀]; exact hZ
  · rw [hg₀]; exact hM
  · intro hr
    have hr' : (show HR (AF F) σ J from g).1 ∈ (Formalism.UG.UJ (σ : E →+* E) J).map (bc (inclR (F := F) (AF F))) := hr
    obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.1 hr'
    have hGx : (matHom _ σ J g).1 = adMat F (x : Matrix (Fin n) (Fin n) E) := by
      exact (congrArg Units.val hxg).symm
    have hMM : M = adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J) * (x : Matrix (Fin n) (Fin n) E) * Z) := by
      rw [hM, hGx]; simp only [adMat, Matrix.map_mul]
    have inj : Function.Injective (inclR (F := F) (E := E) (AF F)) := fun a c h =>
      Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F) h
    have hM₀ : cT (σ : E →+* E) (J₀⁻¹ * (cT (σ : E →+* E) Z * J) * (x : Matrix (Fin n) (Fin n) E) * Z) * J₀ *
        (J₀⁻¹ * (cT (σ : E →+* E) Z * J) * (x : Matrix (Fin n) (Fin n) E) * Z) = J₀ := by
      apply Matrix.map_injective inj
      show adMat F _ = adMat F _
      rw [← hmap, ← hMM]; exact hMu
    have hM₀U := isUnit_of_form _ hM₀ (Ne.isUnit hF.herm₀.2)
    show (show HR (AF F) σ J₀ from g₀).1 ∈ (Formalism.UG.UJ (σ : E →+* E) J₀).map (bc (inclR (F := F) (AF F)))
    refine Subgroup.mem_map.2 ⟨hM₀U.unit, ?_, Units.ext ?_⟩
    · show cT (σ : E →+* E) (hM₀U.unit : Matrix (Fin m) (Fin m) E) * J₀ * hM₀U.unit = J₀
      rw [hM₀U.unit_spec]; exact hM₀
    · show (hM₀U.unit : Matrix (Fin m) (Fin m) E).map (inclR (F := F) (AF F)) = (matHom _ σ J₀ g₀).1
      rw [hM₀U.unit_spec, hg₀, hMM]
