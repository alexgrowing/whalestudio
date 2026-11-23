import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.IndexExponentDegree
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StandardRankOneLatticeOfLocal
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RelIndexMulVec

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

noncomputable section

namespace GlobalTheory.IdxHom

open GlobalTheory.CharValCompare Matrix Kronecker

variable {E : Type} [Field E] {a b : ℕ}

def crd (g : Sp E a ≃ₗ[E] Sp E a) (g' : Sp E b ≃ₗ[E] Sp E b) : HomE E a b →+ (Fin a × Fin b → E) where
  toFun x := (LinearMap.toMatrix' ((g'.symm : Sp E b →ₗ[E] Sp E b) ∘ₗ x ∘ₗ (g : Sp E a →ₗ[E] Sp E a))).vec
  map_zero' := by simp
  map_add' x y := by
    rw [LinearMap.add_comp, LinearMap.comp_add, map_add, Matrix.vec_add]

theorem crd_apply (g : Sp E a ≃ₗ[E] Sp E a) (g' : Sp E b ≃ₗ[E] Sp E b) (x : HomE E a b) :
    crd g g' x = (LinearMap.toMatrix' ((g'.symm : Sp E b →ₗ[E] Sp E b) ∘ₗ x ∘ₗ (g : Sp E a →ₗ[E] Sp E a))).vec := rfl

theorem crd_injective (g : Sp E a ≃ₗ[E] Sp E a) (g' : Sp E b ≃ₗ[E] Sp E b) : Function.Injective (crd g g') := by
  intro x y h
  rw [crd_apply, crd_apply, Matrix.vec_inj] at h
  have h1 := LinearMap.toMatrix'.injective h
  refine LinearMap.ext fun v => ?_
  have := LinearMap.congr_fun h1 (g.symm v)
  simpa using this

theorem crd_surjective (g : Sp E a ≃ₗ[E] Sp E a) (g' : Sp E b ≃ₗ[E] Sp E b) : Function.Surjective (crd g g') := by
  intro v
  obtain ⟨A, rfl⟩ := Matrix.vec_bijective.2 v
  refine ⟨(g' : Sp E b →ₗ[E] Sp E b) ∘ₗ Matrix.toLin' A ∘ₗ (g.symm : Sp E a →ₗ[E] Sp E a), ?_⟩
  rw [crd_apply]
  congr 1
  rw [← LinearMap.toMatrix'_toLin' A]
  congr 1
  refine LinearMap.ext fun v => ?_
  simp

def chg (g₁ g₂ : Sp E a ≃ₗ[E] Sp E a) (g₁' g₂' : Sp E b ≃ₗ[E] Sp E b) : Matrix (Fin a × Fin b) (Fin a × Fin b) E :=
  (LinearMap.toMatrix' ((g₂.symm : Sp E a →ₗ[E] Sp E a) ∘ₗ (g₁ : Sp E a →ₗ[E] Sp E a)))ᵀ ⊗ₖ
    LinearMap.toMatrix' ((g₁'.symm : Sp E b →ₗ[E] Sp E b) ∘ₗ (g₂' : Sp E b →ₗ[E] Sp E b))

theorem chg_mulVec (g₁ g₂ : Sp E a ≃ₗ[E] Sp E a) (g₁' g₂' : Sp E b ≃ₗ[E] Sp E b) (x : HomE E a b) :
    chg g₁ g₂ g₁' g₂' *ᵥ crd g₂ g₂' x = crd g₁ g₁' x := by
  rw [chg, crd_apply, crd_apply, Matrix.kronecker_mulVec_vec, Matrix.transpose_transpose,
    ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp]
  congr 2
  refine LinearMap.ext fun v => ?_
  simp

theorem det_chg (g₁ g₂ : Sp E a ≃ₗ[E] Sp E a) (g₁' g₂' : Sp E b ≃ₗ[E] Sp E b) :
    (chg g₁ g₂ g₁' g₂').det = ((dt g₂)⁻¹ * dt g₁) ^ b * ((dt g₁')⁻¹ * dt g₂') ^ a := by
  rw [chg, Matrix.det_kronecker, Matrix.det_transpose, LinearMap.det_toMatrix', LinearMap.det_toMatrix',
    LinearMap.det_comp, LinearMap.det_comp, LinearEquiv.det_coe_symm, LinearEquiv.det_coe_symm, Fintype.card_fin,
    Fintype.card_fin, dt_eq, dt_eq, dt_eq, dt_eq]

variable [NumberField E]

theorem ordE_chg (P : HeightOneSpectrum (𝓞 E)) (g₁ g₂ : Sp E a ≃ₗ[E] Sp E a) (g₁' g₂' : Sp E b ≃ₗ[E] Sp E b) :
    ordE P (chg g₁ g₂ g₁' g₂').det =
      (b * ordE P (dt g₁) - a * ordE P (dt g₁')) - (b * ordE P (dt g₂) - a * ordE P (dt g₂')) := by
  have h : ∀ {n : ℕ} (f : Sp E n ≃ₗ[E] Sp E n), P.valuation E (dt f) = WithZero.exp (-ordE P (dt f)) := by
    intro n f
    rw [ordE, neg_neg, WithZero.exp_log ((Valuation.ne_zero_iff _).2 (dt_ne f))]
  rw [det_chg, ordE, map_mul, map_pow, map_pow, map_mul, map_mul, map_inv₀, map_inv₀, h g₁, h g₂, h g₁', h g₂',
    ← WithZero.exp_neg, ← WithZero.exp_neg, ← WithZero.exp_add, ← WithZero.exp_add, ← WithZero.exp_nsmul,
    ← WithZero.exp_nsmul, ← WithZero.exp_add, WithZero.log_exp, nsmul_eq_mul, nsmul_eq_mul]
  ring

variable [StarRing E]

theorem mem_homAt_iff {P : HeightOneSpectrum (𝓞 E)} {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)}
    {g : Sp E a ≃ₗ[E] Sp E a} {g' : Sp E b ≃ₗ[E] Sp E b} (hg : IsFr P N g) (hg' : IsFr P N' g') (x : HomE E a b) :
    x ∈ homAt {P} N N' ↔ ∀ i, IntAt P (crd g g' x i) := by
  change (∀ Q ∈ ({P} : Finset _), ∀ y ∈ localization₂ Q.asIdeal N, x y ∈ localization₂ Q.asIdeal N') ↔ _
  simp only [Finset.mem_singleton, forall_eq]
  constructor
  · rintro h ⟨j, i⟩
    have h1 := h _ ((hg _).2 (single_mem_stdAt P j))
    rw [← g'.apply_symm_apply (x _), hg', stdAt, mem_localization_standardLattice] at h1
    have h2 := h1 i
    simpa [crd_apply, LinearMap.toMatrix'_apply] using h2
  · intro h y hy
    obtain ⟨z, rfl⟩ := g.surjective y
    rw [hg, stdAt, mem_localization_standardLattice] at hy
    rw [← g'.apply_symm_apply (x _), hg', stdAt, mem_localization_standardLattice]
    intro i
    have : g'.symm (x (g z)) =
        LinearMap.toMatrix' ((g'.symm : Sp E b →ₗ[E] Sp E b) ∘ₗ x ∘ₗ (g : Sp E a →ₗ[E] Sp E a)) *ᵥ z := by
      rw [LinearMap.toMatrix'_mulVec]
      rfl
    rw [this, Matrix.mulVec, dotProduct]
    exact intAt_sum _ _ fun j _ => (h (j, i)).mul (hy j)

theorem relIndex_homAt : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (a b : ℕ) (P : HeightOneSpectrum (𝓞 E)) (N₁ N₂ : Submodule (𝓞 E) (Sp E a)) (N₁' N₂' : Submodule (𝓞 E) (Sp E b)), Submodule.IsLattice E N₁ → Submodule.IsLattice E N₂ → Submodule.IsLattice E N₁' → Submodule.IsLattice E N₂' → homAt {P} N₂ N₂' ≤ homAt {P} N₁ N₁' → (((homAt {P} N₂ N₂').toAddSubgroup.relIndex (homAt {P} N₁ N₁').toAddSubgroup : ℕ) : ℚ) = ((Ideal.absNorm P.asIdeal : ℕ) : ℚ) ^ (volExp P N₁ N₁' - volExp P N₂ N₂') := by
  intro E _ _ _ a b P N₁ N₂ N₁' N₂' h₁ h₂ h₁' h₂' hle
  obtain ⟨g₁, hg₁⟩ := exists_isFr P h₁
  obtain ⟨g₂, hg₂⟩ := exists_isFr P h₂
  obtain ⟨g₁', hg₁'⟩ := exists_isFr P h₁'
  obtain ⟨g₂', hg₂'⟩ := exists_isFr P h₂'
  have h0 : ∀ x, x ∈ (homAt {P} N₁ N₁').toAddSubgroup.map (crd g₁ g₁') ↔ ∀ i, IntAt P (x i) := by
    intro x
    obtain ⟨y, rfl⟩ := crd_surjective g₁ g₁' x
    rw [AddSubgroup.mem_map_iff_mem (crd_injective _ _), Submodule.mem_toAddSubgroup, mem_homAt_iff hg₁ hg₁']
  rw [← AddSubgroup.relIndex_map_map_of_injective _ _ (crd_injective g₁ g₁'),
    GlobalTheory.IdxDet.relIndex_mulVec E (Fin a × Fin b) P (chg g₁ g₂ g₁' g₂') _ _ ?_ h0 ?_ (AddSubgroup.map_mono hle),
    ordE_chg, volExp, volExp, ordDet_eq hg₁, ordDet_eq hg₂, ordDet_eq hg₁', ordDet_eq hg₂']
  · rw [det_chg]
    exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero (inv_ne_zero (dt_ne _)) (dt_ne _)))
      (pow_ne_zero _ (mul_ne_zero (inv_ne_zero (dt_ne _)) (dt_ne _)))
  · intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨_, (h0 _).2 ((mem_homAt_iff hg₂ hg₂' y).1 hy), (chg_mulVec _ _ _ _ y).symm⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨y, rfl⟩ := crd_surjective g₂ g₂' v
      exact ⟨y, (mem_homAt_iff hg₂ hg₂' y).2 ((h0 _).1 hv), (chg_mulVec _ _ _ _ y).symm⟩

end GlobalTheory.IdxHom
