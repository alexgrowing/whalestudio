import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsCuspFunIffConstTerm
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TwoStepUnipotentCompactModSubring

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open Formalism.UG (cT cT_mul cT_one)

namespace GlobalTheory.EisCT

theorem matrix_unip_cover {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (s : A →+* A)
    (hs : ∀ a, s (s a) = a) (hsc : Continuous s) {n r : ℕ} (J Ji : Matrix (Fin n) (Fin n) A) (hJ : cT s J = J)
    (hJi : J * Ji = 1) (C D : Matrix (Fin n) (Fin r) A) (xx : cT s C * J * C = 0) (yy : cT s D * J * D = 0)
    (xy : cT s C * J * D = 1) (h : A) (hh : h + h = 1) (S₀ : Subring (Matrix (Fin n) (Fin n) A))
    (hS : ∀ M ∈ S₀, cT s M ∈ S₀) (hJS : J ∈ S₀) (hJiS : Ji ∈ S₀) (hCD : C * cT s D ∈ S₀)
    (hhS : Matrix.scalar (Fin n) h ∈ S₀) (K : Set (Matrix (Fin n) (Fin n) A)) (hK : IsCompact K)
    (hKs : ∀ M, ∃ y ∈ S₀, M - y ∈ K) :
    ∃ K' : Set (GL (Fin n) A), IsCompact K' ∧ (∀ g ∈ K', cT s g.1 * J * g.1 = J) ∧
      ∀ g : GL (Fin n) A, cT s g.1 * J * g.1 = J → (g.1 - 1) * C = 0 →
        (∃ B : Matrix (Fin r) (Fin n) A, (g.1 - 1) * (1 - D * (cT s C * J)) = C * B) →
        ∃ γ : GL (Fin n) A, cT s γ.1 * J * γ.1 = J ∧ (γ.1 - 1) * C = 0 ∧
          (∃ B : Matrix (Fin r) (Fin n) A, (γ.1 - 1) * (1 - D * (cT s C * J)) = C * B) ∧ γ.1 ∈ S₀ ∧ (γ⁻¹).1 ∈ S₀ ∧ γ * g ∈ K' := by
  have cc : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) A), cT s (cT s Z) = Z := fun Z => Matrix.ext fun i j => hs _
  have hiJ : Ji * J = 1 := mul_eq_one_comm.1 hJi
  have yx : cT s D * J * C = 1 := by
    have := congrArg (cT s) xy
    rwa [cT_mul, cT_mul, cc, hJ, cT_one, ← Matrix.mul_assoc] at this
  have hcJi : cT s Ji = Ji := by
    have h1 := congrArg (cT s) hJi
    rw [cT_mul, hJ, cT_one] at h1
    rw [← Matrix.mul_one (cT s Ji), ← hJi, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  let st : Matrix (Fin n) (Fin n) A →+ Matrix (Fin n) (Fin n) A :=
    { toFun := fun X => Ji * cT s X * J
      map_zero' := by simp [cT]
      map_add' := fun X Y => by simp [cT, Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul] }
  have st_apply : ∀ X, st X = Ji * cT s X * J := fun _ => rfl
  have hU : ∀ g : Matrix (Fin n) (Fin n) A, st g * g = 1 ↔ cT s g * J * g = J := fun g => by
    rw [st_apply, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT s g)]
    constructor
    · intro h
      have := congrArg (J * ·) h
      simpa only [← Matrix.mul_assoc, hJi, Matrix.one_mul, Matrix.mul_one] using this
    · intro h
      rw [h, hiJ]
  have hst : st (C * (cT s D * J)) = D * (cT s C * J) := by
    rw [st_apply, cT_mul, cT_mul, cc, hJ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hiJ, Matrix.one_mul,
      Matrix.mul_assoc]
  obtain ⟨K', hK', h1, h2⟩ := GlobalTheory.TwoStepUnipotent.compact_mod_subring (Matrix (Fin n) (Fin n) A) st S₀
    (C * (cT s D * J)) (D * (cT s C * J)) (Matrix.scalar _ h) K
    ((continuous_const.matrix_mul (continuous_id.matrix_map hsc).matrix_transpose).matrix_mul continuous_const)
    (fun X Y => by
      simp only [st_apply, cT_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc J, hJi, Matrix.one_mul])
    (fun X => by
      simp only [st_apply, cT_mul, hJ, hcJi, cc, Matrix.mul_assoc]
      rw [hiJ, Matrix.mul_one, ← Matrix.mul_assoc, hiJ, Matrix.one_mul])
    (fun X hX => S₀.mul_mem (S₀.mul_mem hJiS (hS X hX)) hJS)
    (by rw [← Matrix.mul_assoc]; exact S₀.mul_mem hCD hJS) hhS
    (by rw [Matrix.mul_assoc, ← Matrix.mul_assoc (cT s D * J), yx, Matrix.one_mul]) hst
    (by rw [Matrix.mul_assoc, ← Matrix.mul_assoc (cT s D * J), yy]; simp)
    (by rw [Matrix.mul_assoc, ← Matrix.mul_assoc (cT s C * J), xx]; simp)
    (by rw [← map_add, hh, map_one])
    (fun x => (Matrix.scalar_commute _ (fun _ => Commute.all _ _) x).eq) hK hKs
  refine ⟨K', hK', fun g hg => (hU _).1 (h1 g hg).1, fun g u1 u2 ⟨B, u3⟩ => ?_⟩
  obtain ⟨γ, ⟨p1, p2, p3⟩, p4⟩ := h2 g ⟨(hU _).2 u1, by rw [← Matrix.mul_assoc, u2, Matrix.zero_mul], by
    rw [Matrix.mul_assoc, u3, ← Matrix.mul_assoc, Matrix.sub_mul, Matrix.mul_assoc C, yx]; simp⟩
  refine ⟨γ, (hU _).1 p1, ?_, ⟨cT s D * J * ((γ.1 - 1) * (1 - D * (cT s C * J))), ?_⟩, p4⟩
  · have := congrArg (· * C) p2
    simp only [Matrix.zero_mul] at this
    rwa [Matrix.mul_assoc, Matrix.mul_assoc C, yx, Matrix.mul_one] at this
  · rw [Matrix.mul_assoc, Matrix.sub_mul 1, Matrix.one_mul, sub_eq_zero] at p3
    rw [← Matrix.mul_assoc C, ← p3]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}

omit [NumberField E] in

theorem mem_unipRad_iff_dual {C D : Matrix (Fin n) (Fin r) E} (xy : cT (σ : E →+* E) C * J * D = 1) (g : GAd σ J) :
    g ∈ unipRad σ J C ↔ ((matHom _ σ J g).1 - 1) * adMat F C = 0 ∧
      ∃ B : Matrix (Fin r) (Fin n) (AF F ⊗[F] E),
        ((matHom _ σ J g).1 - 1) * adMat F (1 - D * (cT (σ : E →+* E) C * J)) = adMat F C * B := by
  constructor
  · intro hg
    simp only [Matrix.sub_mul _ (1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)), Matrix.one_mul,
      sub_eq_iff_eq_add, zero_add]
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨h1, -, h3⟩ := hg
      rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1
      have hT : cT (σ : E →+* E) C * J * (1 - D * (cT (σ : E →+* E) C * J)) = 0 := by
        rw [Matrix.mul_sub, ← Matrix.mul_assoc _ D, xy, Matrix.mul_one, Matrix.one_mul, sub_self]
      choose a ha using fun k => h3 (fun j => (1 - D * (cT (σ : E →+* E) C * J) : Matrix (Fin n) (Fin n) E) j k)
        (funext fun j => congrFun (congrFun hT j) k)
      refine ⟨h1, Matrix.of fun i k => a k i, ?_⟩
      rw [← sub_eq_iff_eq_add, ← Matrix.one_mul (adMat F (1 - _)), ← Matrix.mul_assoc, Matrix.mul_one, ← Matrix.sub_mul]
      ext i k
      exact congrFun (ha k) i
    | one => exact ⟨by simp, 0, by simp⟩
    | mul a b _ _ ha hb =>
      obtain ⟨a1, A, a2⟩ := ha
      obtain ⟨b1, B, b2⟩ := hb
      refine ⟨by rw [map_mul, Units.val_mul, Matrix.mul_assoc, b1, a1], B + A, ?_⟩
      rw [map_mul, Units.val_mul, Matrix.mul_assoc, b2, Matrix.mul_add, ← Matrix.mul_assoc, a1, a2, Matrix.mul_add,
        add_assoc]
    | inv a _ ha =>
      obtain ⟨a1, A, a2⟩ := ha
      have i1 : (matHom _ σ J a⁻¹).1 * adMat F C = adMat F C := by
        conv_lhs => rw [← a1]
        rw [map_inv, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      refine ⟨i1, -A, ?_⟩
      have := congrArg ((matHom _ σ J a⁻¹).1 * ·) a2
      rw [Matrix.mul_add, ← Matrix.mul_assoc _ (adMat F C), i1, ← Matrix.mul_assoc, ← Units.val_mul, ← map_mul,
        inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul] at this
      rw [Matrix.mul_neg]
      conv_rhs => rw [this]
      abel
  · rintro ⟨h1, B, h2⟩
    refine Subgroup.subset_closure ⟨h1, ?_, fun x hx => ⟨B *ᵥ fun i => inclR (F := F) (AF F) (x i), ?_⟩⟩
    · have hg : cT (sigR (AF F) σ) (matHom _ σ J g).1 * adMat F J * (matHom _ σ J g).1 = adMat F J := g.2
      have c1 : cT (sigR (AF F) σ) (adMat F C) = adMat F (cT (σ : E →+* E) C) := rfl
      rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1
      rw [adMat, Matrix.map_mul, ← adMat, ← c1, Matrix.mul_sub, Matrix.mul_one, sub_eq_zero]
      conv_lhs => rw [← h1, cT_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT _ (matHom _ σ J g).1)]
      exact congrArg _ hg
    · have e : adMat F (1 - D * (cT (σ : E →+* E) C * J)) *ᵥ (fun i => inclR (F := F) (AF F) (x i)) =
          fun i => inclR (F := F) (AF F) (x i) := by
        funext i
        have := RingHom.map_mulVec (inclR (F := F) (AF F)) (1 - D * (cT (σ : E →+* E) C * J)) x i
        rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero, sub_zero, Matrix.one_mulVec] at this
        exact this.symm
      rw [Matrix.mulVec_mulVec, ← h2, ← Matrix.mulVec_mulVec, e]

theorem unipRad_cover_of_dual (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) {C D : Matrix (Fin n) (Fin r) E}
    (xx : cT (σ : E →+* E) C * J * C = 0) (yy : cT (σ : E →+* E) D * J * D = 0)
    (xy : cT (σ : E →+* E) C * J * D = 1) :
    ∃ K : Set (GAd σ J), IsCompact K ∧ ∀ u ∈ unipRad σ J C, ∃ ν ∈ ratPts σ J, ν ∈ unipRad σ J C ∧ ν * u ∈ K := by
  obtain ⟨K, hK, hKs⟩ := GlobalTheory.AutFunCompare.tens_cocompact (F := F) (E := E)
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  let φ := inclR (F := F) (E := E) (AF F)
  have c1 : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) E), cT (sigR (AF F) σ) (adMat F Z) = adMat F (cT (σ : E →+* E) Z) :=
    fun Z => rfl
  have c2 : ∀ Z Z' : Matrix (Fin n) (Fin r) E, cT (sigR (AF F) σ) (adMat F Z) * adMat F J * adMat F Z' =
      adMat F (cT (σ : E →+* E) Z * J * Z') := fun Z Z' => by
    rw [c1]; simp only [adMat, Matrix.map_mul]
  obtain ⟨K', hK', h1, h2⟩ := matrix_unip_cover (sigR (AF F) σ)
    (fun a => by
      induction a using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (hσ x))
    (GlobalTheory.AdelicUnitaryTop.continuous_sigR (AF F) σ) (adMat F J) (adMat F J⁻¹)
    ((c1 J).trans (congrArg (adMat F) (Matrix.ext fun i j => hJ.1 i j)))
    (by rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (IsUnit.mk0 _ hJ.2), Matrix.map_one _ (map_zero _) (map_one _)])
    (adMat F C) (adMat F D)
    (by rw [c2, xx]; exact Matrix.map_zero _ (map_zero _)) (by rw [c2, yy]; exact Matrix.map_zero _ (map_zero _))
    (by rw [c2, xy]; exact Matrix.map_one _ (map_zero _) (map_one _)) (φ (1 / 2))
    (by rw [← map_add, add_halves, map_one]) (φ.mapMatrix (m := Fin n)).range
    (by rintro _ ⟨X, rfl⟩; exact ⟨_, (c1 X).symm⟩) ⟨_, rfl⟩ ⟨_, rfl⟩
    ⟨C * cT (σ : E →+* E) D, by rw [c1]; exact Matrix.map_mul⟩
    ⟨Matrix.scalar _ (1 / 2), by ext i j; by_cases h : i = j <;> simp [h]⟩
    (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => K)
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK)
    (fun X => by
      choose y hy using fun i j => hKs (X i j)
      exact ⟨_, ⟨Matrix.of y, rfl⟩, fun i _ j _ => hy i j⟩)
  have e : 1 - adMat F D * (cT (sigR (AF F) σ) (adMat F C) * adMat F J) =
      adMat F (1 - D * (cT (σ : E →+* E) C * J)) := by
    rw [c1]
    simp only [adMat]
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_mul, Matrix.map_mul]
  rw [e] at h2
  refine ⟨matHom _ σ J ⁻¹' K', (isEmbedding_matHom _ σ J).isInducing.isCompact_preimage' hK'
    fun g hg => ⟨⟨g, h1 g hg⟩, rfl⟩, fun u hu => ?_⟩
  obtain ⟨u1, u2⟩ := (mem_unipRad_iff_dual xy u).1 hu
  obtain ⟨γ, p1, p2, p3, ⟨a, ha⟩, ⟨b, hb⟩, p4⟩ := h2 (matHom _ σ J u) u.2 u1 u2
  refine ⟨⟨γ, p1⟩, ?_, (mem_unipRad_iff_dual xy _).2 ⟨p2, p3⟩, p4⟩
  have inj : Function.Injective (φ.mapMatrix (m := Fin n)) :=
    Matrix.map_injective GlobalTheory.AutFunCompare.inclA_injective
  have hab : a * b = 1 := inj (by rw [map_mul, ha, hb, map_one, Units.mul_inv])
  refine ⟨⟨a, b, hab, mul_eq_one_comm.1 hab⟩, inj ?_, Units.ext ha⟩
  rw [← ha] at p1
  rw [map_mul, map_mul]
  exact p1

theorem unipotent_radical_compact_cover : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), HidaSetting σ J X Y L a h →
    ∃ C : Set (GAd σ J), IsCompact C ∧
      ∀ u ∈ unipRad σ J (col0 X), ∃ ν ∈ ratPts σ J, ν ∈ unipRad σ J (col0 X) ∧ ν * u ∈ C := by
  intro F E _ _ _ _ _ σ n J r X Y L a h hS
  obtain ⟨hc, -, hJ, -, hW, -, -⟩ := hS
  have key : ∀ (Z Z' : Matrix (Fin n) (Fin (r + 1)) E) (i j : Fin 1),
      (cT (σ : E →+* E) (col0 Z) * J * col0 Z') i j = (cT (σ : E →+* E) Z * J * Z') 0 0 := fun _ _ _ _ => rfl
  refine unipRad_cover_of_dual (D := col0 Y) (sigma_sigma hc) hJ ?_ ?_ ?_
  · ext i j; rw [key, hW.xx]; rfl
  · ext i j; rw [key, hW.yy]; rfl
  · ext i j; rw [key, hW.xy, Subsingleton.elim i j]; simp

end GlobalTheory.EisCT

end
