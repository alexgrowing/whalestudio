import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.SphEis

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {j m : ℕ}
  {C D : Matrix (Fin n) (Fin j) E} {Z : Matrix (Fin n) (Fin m) E} {J₀ : Matrix (Fin m) (Fin m) E}

theorem Fr.invol (hF : Fr σ J C D Z J₀) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  exact τ.injective (by rw [hF.cm.2.2.2, hF.cm.2.2.2, star_star])

theorem Fr.isIsoCols (hF : Fr σ J C D Z J₀) : IsIsoCols σ J C := by
  refine ⟨Matrix.mulVec_injective_iff.1 ?_, hF.cc⟩
  intro v w h
  have := congrArg ((cT (σ : E →+* E) D * J) *ᵥ ·) h
  simpa only [Matrix.mulVec_mulVec, hF.dc, Matrix.one_mulVec] using this

theorem isClosed_fixG' {k : ℕ} (X : Matrix (Fin n) (Fin k) E) : IsClosed (fixG σ J X : Set (GAd σ J)) := by
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  have : T2Space (AF F ⊗[F] E) := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension
  have hm : Continuous fun g : GAd σ J => (matHom _ σ J g).1 := Units.continuous_val.comp continuous_subtype_val
  exact isClosed_eq (hm.matrix_mul continuous_const) continuous_const

theorem unipRad_le_fixG' (X : Matrix (Fin n) (Fin j) E) : unipRad σ J X ≤ fixG σ J X := by
  rw [unipRad, Subgroup.closure_le]
  intro g hg
  obtain ⟨h, -, -⟩ := hg
  show _ * _ = _
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h
  exact h

theorem unipRad_onZ (hF : Fr σ J C D Z J₀) {g : GAd σ J} (hg : g ∈ unipRad σ J C) :
    ∃ b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E), (matHom _ σ J g).1 * adMat F Z = adMat F Z + adMat F C * b := by
  unfold unipRad at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨-, -, h3⟩ := hx
    choose a ha using fun k : Fin m => h3 (fun i => Z i k) (funext fun i => congrFun (congrFun hF.cz i) k)
    have e : ((matHom _ σ J x).1 - 1) * adMat F Z = adMat F C * Matrix.of fun i k => a k i :=
      Matrix.ext fun i k => congrFun (ha k) i
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_iff_eq_add'] at e
    exact ⟨_, e⟩
  | one => exact ⟨0, by simp⟩
  | mul x y hxm _ hx hy =>
    obtain ⟨b, hb⟩ := hx
    obtain ⟨b', hb'⟩ := hy
    have hxC : (matHom _ σ J x).1 * adMat F C = adMat F C := unipRad_le_fixG' (σ := σ) (J := J) C hxm
    refine ⟨b + b', ?_⟩
    rw [map_mul, Units.val_mul, Matrix.mul_assoc, hb', Matrix.mul_add, hb, ← Matrix.mul_assoc, hxC, Matrix.mul_add,
      add_assoc]
  | inv x hxm hx =>
    obtain ⟨b, hb⟩ := hx
    have hi : (matHom _ σ J x⁻¹).1 * (matHom _ σ J x).1 = 1 := Units.inv_mul x.1
    have hxC : (matHom _ σ J x⁻¹).1 * adMat F C = adMat F C :=
      unipRad_le_fixG' (σ := σ) (J := J) C (inv_mem (show x ∈ unipRad σ J C from hxm))
    have e : (matHom _ σ J x⁻¹).1 * ((matHom _ σ J x).1 * adMat F Z) = (matHom _ σ J x⁻¹).1 * (adMat F Z + adMat F C * b) :=
      congrArg _ hb
    rw [← Matrix.mul_assoc, hi, Matrix.one_mul, Matrix.mul_add, ← Matrix.mul_assoc, hxC] at e
    refine ⟨-b, ?_⟩
    rw [Matrix.mul_neg, ← sub_eq_add_neg]
    exact eq_sub_of_add_eq e.symm

theorem unipRad_inf_fixG (hF : Fr σ J C D Z J₀) (g : GAd σ J) (hu : g ∈ unipRad σ J C)
    (hg : g ∈ (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J))) : g = 1 := by
  obtain ⟨b, hb⟩ := unipRad_onZ hF hu
  have hC : (matHom _ σ J g).1 * adMat F C = adMat F C := hg.1
  have hD : (matHom _ σ J g).1 * adMat F D = adMat F D := hg.2
  have hD1 : (matHom _ σ J g).1 * adMat F D = adMat F D * (1 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) := by rw [Matrix.mul_one]; exact hD
  have e := form_mul_of_mul_cols hD1
  rw [Formalism.UG.cT_one, Matrix.one_mul] at e
  have hi : (matHom _ σ J g⁻¹).1 * (matHom _ σ J g).1 = 1 := Units.inv_mul g.1
  have e2 : adMat F (cT (σ : E →+* E) D * J) * (matHom _ σ J g).1 = adMat F (cT (σ : E →+* E) D * J) := by
    conv_lhs => rw [← e, Matrix.mul_assoc, hi, Matrix.mul_one]
  have hb0 : b = 0 := by
    have h : adMat F (cT (σ : E →+* E) D * J) * ((matHom _ σ J g).1 * adMat F Z) =
        adMat F (cT (σ : E →+* E) D * J) * (adMat F Z + adMat F C * b) := congrArg _ hb
    have hdc : adMat F (cT (σ : E →+* E) D * J) * adMat F C = 1 := by
      rw [adMat, adMat, ← Matrix.map_mul, hF.dc, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [← Matrix.mul_assoc, e2, Matrix.mul_add, ← Matrix.mul_assoc, hdc, Matrix.one_mul] at h
    calc b = (adMat F (cT (σ : E →+* E) D * J) * adMat F Z + b) -
          adMat F (cT (σ : E →+* E) D * J) * adMat F Z := by abel
      _ = 0 := by rw [← h, sub_self]
  rw [hb0, Matrix.mul_zero, add_zero] at hb
  have key : ∀ h : GAd σ J, (matHom _ σ J h).1 =
      (matHom _ σ J h).1 * adMat F C * adMat F (cT (σ : E →+* E) D * J) +
      (matHom _ σ J h).1 * adMat F Z * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) +
      (matHom _ σ J h).1 * adMat F D * adMat F (cT (σ : E →+* E) C * J) := by
    intro h
    have e : (matHom _ σ J h).1 = (matHom _ σ J h).1 * adMat F (C * (cT (σ : E →+* E) D * J) +
        Z * (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) + D * (cT (σ : E →+* E) C * J)) := by
      rw [hF.sum, adMat, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
    conv_lhs => rw [e]
    simp only [adMat, Matrix.map_add (inclR (F := F) (E := E) (AF F)) (map_add _), Matrix.map_mul, Matrix.mul_add,
      Matrix.mul_assoc]
  apply matHom_injective _ σ J
  apply Units.ext
  have k1 := key 1
  simp only [map_one, Units.val_one, Matrix.one_mul] at k1
  rw [key g, hC, hb, hD, map_one, Units.val_one]
  exact k1.symm

theorem frame_facts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → IsIsoCols σ J C ∧ IsClosed (fixG σ J C : Set (GAd σ J)) ∧ IsClosed ((fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)) : Set (GAd σ J)) ∧ IsClosed (unipRad σ J C : Set (GAd σ J)) ∧ unipRad σ J C ≤ fixG σ J C ∧ fixG σ J C ≤ parFlag σ J C (fun _ => 0) ∧ (∀ g ∈ unipRad σ J C, g ∈ (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)) → g = 1) ∧ (∀ p ∈ parFlag σ J C (fun _ => 0), ∀ u, u ∈ unipRad σ J C ↔ p * u * p⁻¹ ∈ unipRad σ J C) ∧ ∀ (p : GAd σ J) (β : GL (Fin j) (AF F ⊗[F] E)), (matHom _ σ J p).1 * adMat F C = adMat F C * β.1 → p ∈ parFlag σ J C (fun _ => 0) := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF
  have hJ := hF.herm
  have hσ := hF.invol
  have hIC := hF.isIsoCols
  refine ⟨hIC, isClosed_fixG' C, ?_, ?_, unipRad_le_fixG' C, ?_, unipRad_inf_fixG hF, ?_, ?_⟩
  · rw [Subgroup.coe_inf]; exact (isClosed_fixG' C).inter (isClosed_fixG' D)
  · rw [← unipFlag_const C 0]; exact isClosed_unipFlag hJ hσ hIC _
  · intro g hg
    have hg' : g⁻¹ ∈ fixG σ J C := inv_mem hg
    refine ⟨⟨1, fun _ _ h => absurd h (lt_irrefl 0), ?_⟩, 1, fun _ _ h => absurd h (lt_irrefl 0), ?_⟩
    · rw [Matrix.mul_one]; exact hg
    · rw [Matrix.mul_one]; exact hg'
  · intro p hp u
    rw [← unipFlag_const C 0]
    exact ⟨fun hu => conj_mem_unipFlag hJ hσ hIC _ hp hu, fun hu => by
      have := conj_mem_unipFlag hJ hσ hIC _ (inv_mem hp) hu
      simpa [mul_assoc] using this⟩
  · intro p β h
    have hi : (matHom _ σ J p⁻¹).1 * (matHom _ σ J p).1 = 1 := Units.inv_mul p.1
    have hb : β.1 * (β⁻¹).1 = 1 := Units.mul_inv β
    refine ⟨⟨β.1, fun _ _ h => absurd h (lt_irrefl 0), h⟩, (β⁻¹).1, fun _ _ h => absurd h (lt_irrefl 0), ?_⟩
    calc (matHom _ σ J p⁻¹).1 * adMat F C = (matHom _ σ J p⁻¹).1 * (adMat F C * (β.1 * (β⁻¹).1)) := by
          rw [hb, Matrix.mul_one]
      _ = (matHom _ σ J p⁻¹).1 * (matHom _ σ J p).1 * adMat F C * (β⁻¹).1 := by
          rw [← Matrix.mul_assoc (adMat F C), ← h]; simp only [Matrix.mul_assoc]
      _ = adMat F C * (β⁻¹).1 := by rw [hi, Matrix.one_mul]

end GlobalTheory.SphEis

end
