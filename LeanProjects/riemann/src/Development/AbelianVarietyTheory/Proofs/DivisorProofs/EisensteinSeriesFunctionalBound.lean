import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT)

noncomputable section

namespace GlobalTheory.EisCT

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField F] [NumberField E] in

theorem isotropic_frame_first_column_isotropic {n r : ℕ} {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E}
    {X : Matrix (Fin n) (Fin (r + 1)) E} (hX : cT (σ : E →+* E) X * J * X = 0) :
    cT (σ : E →+* E) (col0 X) * J * col0 X = 0 := by
  ext i j
  have := congrFun (congrFun hX 0) 0
  simpa [cT, col0, Matrix.mul_apply] using this

theorem orthL_of_stabL {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {x : Matrix (Fin n) (Fin 1) E}
    (hx : cT (σ : E →+* E) x * J * x = 0) {g : GAd σ J} (hg : StabL σ J x g) : OrthL σ J x g := by
  obtain ⟨l, hl⟩ := hg
  have h0 : (matHom _ σ J g⁻¹).1 * ((matHom _ σ J g).1 * adMat F x) = adMat F x := by
    rw [← Matrix.mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul]
  rw [hl, Matrix.mul_smul] at h0
  have h1 : (matHom _ σ J g⁻¹).1 * adMat F x = (l⁻¹ : (AF F ⊗[F] E)ˣ).1 • adMat F x := by
    calc (matHom _ σ J g⁻¹).1 * adMat F x
        = (l⁻¹ : (AF F ⊗[F] E)ˣ).1 • (l.1 • ((matHom _ σ J g⁻¹).1 * adMat F x)) := by
          rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
      _ = _ := by rw [h0]
  unfold OrthL
  rw [Matrix.mul_assoc, h1, Matrix.mul_smul, adMat, adMat, ← Matrix.map_mul, hx]
  simp

end GlobalTheory.EisCT

open GlobalTheory.EisCT in

theorem GlobalTheory.EisCT.eis_eq_three_sums : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ) (Eis : ℂ → GAd σ J → ℂ), HidaSetting σ J X Y L a h → IsSerG σ J (col0 X) h Eis →
    ∀ T, GlobalTheory.EisCT.IsTransv σ J (col0 X) T → ∀ s : ℂ, ((n : ℝ) - 1) / 2 < s.re → ∀ g,
    Eis s g = GlobalTheory.EisCT.lineSum σ J (col0 X) T h s g + GlobalTheory.EisCT.midSum σ J (col0 X) T h s g +
      GlobalTheory.EisCT.bigSum σ J (col0 X) T h s g := by
  intro F E _ _ _ _ _ σ n J r X Y L a h Eis hS hE T hT s hs g
  have hW : IsWittFrame σ J X Y := hS.2.2.2.2.1
  have hx := isotropic_frame_first_column_isotropic (σ := σ) (J := J) hW.xx
  have hser := hE T hT s hs g
  set f : ratPts σ J → ℂ := fun t => fs σ J h s (t.1 * g) with hf
  have hsum : Summable (f ∘ ((↑) : T → ratPts σ J)) := hser.summable
  have hsub : ∀ S ⊆ T, Summable (f ∘ ((↑) : S → ratPts σ J)) := by
    intro S hST
    have hind : Summable (T.indicator f) := summable_subtype_iff_indicator.1 hsum
    exact (hind.subtype S).congr fun t => Set.indicator_of_mem (hST t.2) f
  have hLT : lineSet σ J (col0 X) T ⊆ T := fun t ht => ht.1
  have hMT : midSet σ J (col0 X) T ⊆ T := fun t ht => ht.1
  have hBT : bigSet σ J (col0 X) T ⊆ T := fun t ht => ht.1
  have hdisj1 : Disjoint (lineSet σ J (col0 X) T) (midSet σ J (col0 X) T) :=
    Set.disjoint_left.2 fun t h1 h2 => h2.2.1 h1.2
  have hdisj2 : Disjoint (lineSet σ J (col0 X) T ∪ midSet σ J (col0 X) T) (bigSet σ J (col0 X) T) :=
    Set.disjoint_left.2 fun t h1 h2 => by
      rcases h1 with h1 | h1
      · exact h2.2 (orthL_of_stabL hx h1.2)
      · exact h2.2 h1.2.2
  have hunion : T = lineSet σ J (col0 X) T ∪ midSet σ J (col0 X) T ∪ bigSet σ J (col0 X) T := by
    ext t
    simp only [lineSet, midSet, bigSet, Set.mem_union, Set.mem_setOf_eq]
    by_cases h1 : StabL σ J (col0 X) t.1 <;> by_cases h2 : OrthL σ J (col0 X) t.1 <;> tauto
  have e1 : Eis s g = ∑' t : T, f t := hser.tsum_eq.symm
  rw [e1, tsum_congr_set_coe f hunion, Summable.tsum_union_disjoint hdisj2
      (hsub _ (Set.union_subset hLT hMT)) (hsub _ hBT),
    Summable.tsum_union_disjoint hdisj1 (hsub _ hLT) (hsub _ hMT)]
  rfl
