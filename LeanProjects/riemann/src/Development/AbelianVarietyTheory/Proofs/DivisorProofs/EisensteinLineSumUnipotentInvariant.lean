import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT)

namespace GlobalTheory.EisCT

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem stabL_inv {x : Matrix (Fin n) (Fin 1) E} {g : GAd σ J} (hg : StabL σ J x g) : StabL σ J x g⁻¹ := by
  obtain ⟨l, hl⟩ := hg
  refine ⟨l⁻¹, ?_⟩
  rw [map_inv]
  conv_lhs => rw [show adMat F x = (↑l⁻¹ : AF F ⊗[F] E) • ((matHom _ σ J g).1 * adMat F x) by
    rw [hl, smul_smul, Units.inv_mul, one_smul]]
  rw [Matrix.mul_smul, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

theorem unipRad_fix {r : ℕ} {C : Matrix (Fin n) (Fin r) E} {u : GAd σ J} (hu : u ∈ unipRad σ J C) :
    (matHom _ σ J u).1 * adMat F C = adMat F C := by
  induction hu using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨h1, -, -⟩ := hg
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1
    exact h1
  | one => rw [map_one, Units.val_one, Matrix.one_mul]
  | mul a b _ _ ha hb => rw [map_mul, Units.val_mul, Matrix.mul_assoc, hb, ha]
  | inv a _ ha =>
    conv_lhs => rw [← ha]
    rw [map_inv, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

theorem absE_eq_one_of_rat {x : Matrix (Fin n) (Fin 1) E} (hx : ∃ i, x i 0 ≠ 0) (t : ratPts σ J)
    (l : (AF F ⊗[F] E)ˣ) (hl : (matHom _ σ J t.1).1 * adMat F x = l.1 • adMat F x) : absE F E l = 1 := by
  haveI : Nontrivial (AF F) := (NumberField.AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  haveI : Nontrivial (AF F ⊗[F] E) := inferInstance
  obtain ⟨i, hi⟩ := hx
  have ht : matHom (AF F) σ J t.1 ∈ HFin (AF F) σ J := Subgroup.mem_subgroupOf.1 t.2
  obtain ⟨γ, -, hγ⟩ := Subgroup.mem_map.1 ht
  have hM : (matHom _ σ J t.1).1 = (γ.1).map (inclR (F := F) (AF F)) := by
    exact (congrArg Units.val hγ).symm
  rw [hM] at hl
  have he := congrFun (congrFun hl i) 0
  rw [← Matrix.map_mul, Matrix.map_apply, Matrix.smul_apply] at he
  simp only [adMat, Matrix.map_apply, smul_eq_mul] at he
  have hl' : l.1 = inclR (F := F) (AF F) ((γ.1 * x) i 0 * (x i 0)⁻¹) := by
    rw [map_mul, he, mul_assoc, ← map_mul, mul_inv_cancel₀ hi, map_one, mul_one]
  have hne : (γ.1 * x) i 0 * (x i 0)⁻¹ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hl'
    exact l.ne_zero hl'
  have : l = Units.map (inclR (F := F) (AF F)).toMonoidHom (Units.mk0 _ hne) := Units.ext (by
    rw [Units.coe_map, hl']; rfl)
  rw [this, GlobalTheory.Doubling.absE_inclR]

end GlobalTheory.EisCT

namespace GlobalTheory.EisCT

theorem lineSum_eq_fs : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), HidaSetting σ J X Y L a h →
    ∀ T, GlobalTheory.EisCT.IsTransv σ J (col0 X) T → ∀ u ∈ unipRad σ J (col0 X), ∀ (s : ℂ) (g : GAd σ J),
    GlobalTheory.EisCT.lineSum σ J (col0 X) T h s (u * g) = GlobalTheory.EisCT.fs σ J h s g := by
  intro F E _ _ _ _ _ σ n J r X Y L a h hS T hT u hu s g
  obtain ⟨-, -, -, -, hW, -, hI⟩ := hS
  have hx : ∃ i, col0 X i 0 ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have e := congrFun (congrFun hW.xy 0) 0
    have hc : ∀ i, X i 0 = 0 := fun i => hcon i
    simp [Matrix.mul_apply, cT, hc] at e
  obtain ⟨t₁, ⟨ht₁T, ht₁S⟩, huniq⟩ := hT 1
  have hst : StabL σ J (col0 X) t₁.1 := by
    have := stabL_inv σ J ht₁S
    simpa using this
  have hmem : ∀ t : ratPts σ J, t ∈ lineSet σ J (col0 X) T → t = t₁ := fun t ht =>
    huniq t ⟨ht.1, by simpa using stabL_inv σ J ht.2⟩
  unfold lineSum
  rw [tsum_eq_single (⟨t₁, ht₁T, hst⟩ : lineSet σ J (col0 X) T) (fun b hb =>
    absurd (Subtype.ext (hmem b.1 b.2)) hb)]
  unfold fs
  congr 2
  obtain ⟨p, l, hpl, k, hk, rfl⟩ := hI.1 g
  obtain ⟨c₁, hc₁⟩ := hst
  have h1 := absE_eq_one_of_rat σ J hx t₁ c₁ hc₁
  have hux := unipRad_fix σ J hu
  have key : (matHom _ σ J (t₁.1 * u * p)).1 * adMat F (col0 X) = (l * c₁).1 • adMat F (col0 X) := by
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc, hpl, Matrix.mul_smul,
      hux, Matrix.mul_smul, hc₁, smul_smul, Units.val_mul]
  show h (t₁.1 * (u * (p * k))) = h (p * k)
  rw [show t₁.1 * (u * (p * k)) = t₁.1 * u * p * k by simp only [mul_assoc], hI.2 _ _ key k hk, hI.2 p l hpl k hk,
    map_mul, h1, mul_one]

end GlobalTheory.EisCT
