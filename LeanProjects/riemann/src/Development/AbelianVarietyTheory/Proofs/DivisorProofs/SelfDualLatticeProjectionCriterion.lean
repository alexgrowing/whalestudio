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

noncomputable section

namespace GlobalTheory.HypAdapt.Cmpl

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}

omit [NumberField F] [NumberField E] in
theorem hE_sub (J : Matrix (Fin n) (Fin n) E) (x y y' : Fin n → E) : hE σ J x (y - y') = hE σ J x y - hE σ J x y' := by
  rw [hE_eq, hE_eq, hE_eq, mulVec_sub, dotProduct_sub]

omit [NumberField F] [NumberField E] in
theorem hE_zero_right (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) : hE σ J x 0 = 0 := by
  rw [hE_eq, mulVec_zero, dotProduct_zero]

omit [NumberField F] [NumberField E] in
theorem eq_zero_of_hE_one {k : ℕ} {w : Fin k → E} (h : ∀ u, hE σ (1 : Matrix (Fin k) (Fin k) E) u w = 0) : w = 0 := by
  funext i
  have := h (Pi.single i 1)
  rw [hE_eq, one_mulVec] at this
  have e : (fun j => σ ((Pi.single i (1 : E) : Fin k → E) j)) = Pi.single i 1 := by
    funext j; by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  rw [e, single_one_dotProduct] at this
  exact this

end GlobalTheory.HypAdapt.Cmpl

end

open GlobalTheory.HypAdapt GlobalTheory.HypAdapt.Cmpl Matrix in

theorem GlobalTheory.HypAdapt.Cmpl.exists_selfDual_complement : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n m r : ℕ) (J : Matrix (Fin n) (Fin n) E), J.det ≠ 0 →
    ∀ L₀ : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L₀ → (∀ v, IsSelfDualAt σ J L₀ v) → (∀ (K : Submodule E (Fin n → E)) (y : Fin n → E), (∀ z ∈ L₀, z ∈ K → hE σ J z y ∈ (algebraMap (𝓞 E) E).range) →
        ∃ z ∈ L₀, ∀ x ∈ K, hE σ J x z = hE σ J x y) →
    ∀ (X Y : Matrix (Fin n) (Fin r) E) (I : Matrix (Fin n) (Fin m) E) (Q : Matrix (Fin m) (Fin n) E),
      cT (σ : E →+* E) X * J * X = 0 → cT (σ : E →+* E) X * J * I = 0 → Q * X = 0 → Q * I = 1 →
      (cT (σ : E →+* E) I * J * I).det ≠ 0 → (cT (σ : E →+* E) I * J * I) * Q = cT (σ : E →+* E) I * J →
      X * (cT (σ : E →+* E) Y * J) + I * Q + Y * (cT (σ : E →+* E) X * J) = 1 →
      ∃ L₀' : Submodule (𝓞 E) (Fin m → E), Submodule.IsLattice E L₀' ∧
        ∀ v, IsSelfDualAt σ (cT (σ : E →+* E) I * J * I) L₀' v := by
  intro F E _ _ _ _ _ σ n m r J hJ L₀ hL hd hext X Y I Q XX XI QX QI hG hQ h1
  set G := cT (σ : E →+* E) I * J * I with hGdef
  set K : Submodule E (Fin n → E) := LinearMap.ker (cT (σ : E →+* E) X * J).mulVecLin with hK
  have memK : ∀ z, z ∈ K ↔ (cT (σ : E →+* E) X * J) *ᵥ z = 0 := fun z => LinearMap.mem_ker
  set L₁ : Submodule (𝓞 E) (Fin n → E) := L₀ ⊓ K.restrictScalars (𝓞 E) with hL₁
  refine ⟨L₁.map (Q.mulVecLin.restrictScalars (𝓞 E)), ?_⟩
  have eX := hE_mulVec σ J (Matrix.one_mul (cT (σ : E →+* E) X * J))
  have eI := hE_mulVec σ J hQ.symm.symm
  have hX0 : ∀ a, ∀ z ∈ K, hE σ J (X *ᵥ a) z = 0 := fun a z hz => by
    rw [eX, (memK z).1 hz, hE_zero_right]
  have XK : ∀ a, X *ᵥ a ∈ K := fun a => (memK _).2 (by rw [mulVec_mulVec, XX, zero_mulVec])
  have IK : ∀ a, I *ᵥ a ∈ K := fun a => (memK _).2 (by rw [mulVec_mulVec, XI, zero_mulVec])
  have hz : ∀ z ∈ K, z = X *ᵥ ((cT (σ : E →+* E) Y * J) *ᵥ z) + I *ᵥ (Q *ᵥ z) := fun z hzK => by
    have e3 : (Y * (cT (σ : E →+* E) X * J)) *ᵥ z = 0 := by rw [← mulVec_mulVec, (memK z).1 hzK, mulVec_zero]
    conv_lhs => rw [← one_mulVec z, ← h1]
    rw [add_mulVec, add_mulVec, e3, add_zero]
    simp only [mulVec_mulVec]
  have hJz : ∀ z ∈ K, ∀ y ∈ K, hE σ J z y = hE σ G (Q *ᵥ z) (Q *ᵥ y) := fun z hzK y hyK => by
    rw [hz z hzK, hE_add, hX0 _ y hyK, zero_add, eI, ← hz z hzK]
  have d0 := (GlobalTheory.AdelicU.SelfDual.forall_isSelfDualAt_iff hJ hL).1 hd
  have hl : Submodule.IsLattice E (L₁.map (Q.mulVecLin.restrictScalars (𝓞 E))) := by
    have : IsNoetherian (𝓞 E) L₀ := isNoetherian_of_fg_of_noetherian L₀ hL.fg
    have hfg : L₁.FG := by
      rw [hL₁, ← Submodule.map_comap_subtype]
      exact (IsNoetherian.noetherian _).map _
    refine ⟨hfg.map _, eq_top_iff.2 fun u _ => ?_⟩
    have hIu : I *ᵥ u ∈ Submodule.span E (L₀ : Set (Fin n → E)) := hL.span_eq_top ▸ Submodule.mem_top
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E (L₀ : Set (Fin n → E)) _ hIu
    rw [Submodule.span_eq] at ht
    have e1 : t • (I *ᵥ u) = algebraMap (𝓞 E) E (t : 𝓞 E) • (I *ᵥ u) := by
      rw [Submonoid.smul_def, algebraMap_smul]
    have hc : algebraMap (𝓞 E) E (t : 𝓞 E) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).2 (nonZeroDivisors.coe_ne_zero t)
    have hm : algebraMap (𝓞 E) E (t : 𝓞 E) • u ∈ L₁.map (Q.mulVecLin.restrictScalars (𝓞 E)) := by
      refine ⟨t • (I *ᵥ u), ⟨ht, ?_⟩, ?_⟩
      · rw [e1]; exact K.smul_mem _ (IK u)
      · change Q *ᵥ (t • (I *ᵥ u)) = _
        rw [e1, mulVec_smul, mulVec_mulVec, QI, one_mulVec]
    have : u = (algebraMap (𝓞 E) E (t : 𝓞 E))⁻¹ • (algebraMap (𝓞 E) E (t : 𝓞 E) • u) := by
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hm)
  refine ⟨hl, (GlobalTheory.AdelicU.SelfDual.forall_isSelfDualAt_iff hG hl).2 fun y => ⟨?_, fun h => ?_⟩⟩
  · rintro ⟨z, ⟨hz0, hzK⟩, rfl⟩ x ⟨z', ⟨hz0', hzK'⟩, rfl⟩
    change hE σ G (Q *ᵥ z') (Q *ᵥ z) ∈ _
    rw [← hJz z' hzK' z hzK]
    exact (d0 z).1 hz0 z' hz0'
  · obtain ⟨z'', hz'', he⟩ := hext K (I *ᵥ y) fun z hz0 hzK => by
      rw [hJz z hzK _ (IK y), mulVec_mulVec, QI, one_mulVec]
      exact h _ ⟨z, ⟨hz0, hzK⟩, rfl⟩
    have hd0 : ∀ x ∈ K, hE σ J x (I *ᵥ y - z'') = 0 := fun x hx => by rw [hE_sub, he x hx, sub_self]
    have c1 : (cT (σ : E →+* E) X * J) *ᵥ (I *ᵥ y - z'') = 0 :=
      eq_zero_of_hE_one σ fun u => by rw [← eX]; exact hd0 _ (XK u)
    have c2 : Q *ᵥ (I *ᵥ y - z'') = 0 := by
      have : G *ᵥ (Q *ᵥ (I *ᵥ y - z'')) = 0 := by
        refine eq_zero_of_hE_one σ fun u => ?_
        rw [hE_eq, one_mulVec, ← hE_eq, ← eI]; exact hd0 _ (IK u)
      rw [← one_mulVec (Q *ᵥ _), ← nonsing_inv_mul G (Ne.isUnit hG), ← mulVec_mulVec, this, mulVec_zero]
    have hz''K : z'' ∈ K := by
      have : z'' = I *ᵥ y - (I *ᵥ y - z'') := by abel
      rw [this]; exact K.sub_mem (IK y) ((memK _).2 c1)
    refine ⟨z'', ⟨hz'', hz''K⟩, ?_⟩
    change Q *ᵥ z'' = y
    rw [mulVec_sub, mulVec_mulVec, QI, one_mulVec, sub_eq_zero] at c2
    exact c2.symm
