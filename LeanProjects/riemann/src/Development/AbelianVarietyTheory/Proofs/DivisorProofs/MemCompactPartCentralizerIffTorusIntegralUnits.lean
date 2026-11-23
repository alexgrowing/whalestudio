import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusOfSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralSummandGoodPlaceIndicator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCommutingEqMulNormOneTorus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactClosureZpowersIffBoundedEntriesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralMatrixIffBoundedPowers
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

noncomputable section

namespace GlobalTheory.KapOrb.CptInt

open GlobalTheory.UnitLemma

theorem isIntegral_iff_of_mulVec {K : UQ} (B : InvAlg K) {n : ℕ} (φ : B.A ≃ₗ[K.E] (Fin n → K.E)) (a : B.A)
    (M : Matrix (Fin n) (Fin n) K.E) (h : ∀ y, φ (a * y) = M *ᵥ φ y) : IsIntegral K.O a ↔ IsIntegral K.O M := by
  let b : Module.Basis (Fin n) K.E B.A := Module.Basis.ofEquivFun φ
  let f : B.A →ₐ[K.O] Matrix (Fin n) (Fin n) K.E := (Algebra.leftMulMatrix b).restrictScalars K.O
  have hinj : Function.Injective f := Algebra.leftMulMatrix_injective b
  have hf : f a = M := by
    ext i j
    change Algebra.leftMulMatrix b a i j = M i j
    rw [Algebra.leftMulMatrix_eq_repr_mul, ← Module.Basis.equivFun_apply, Module.Basis.equivFun_ofEquivFun, h]
    simp [b, Module.Basis.coe_ofEquivFun, Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [← hf]
  exact (isIntegral_algHom_iff f hinj).symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem continuous_cj (w : Pl E) : Continuous (cj w) := by
  unfold cj
  split_ifs with hc
  · exact hc.choose_spec.1
  · exact continuous_id

theorem isClosed_UL (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) :
    IsClosed ((UL n w : Subgroup (GLw n w)) : Set (GLw n w)) := by
  unfold UL; rw [if_neg hw]
  have : ((UJ (cj w) (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) : Subgroup _) : Set (GLw n w)) =
      (fun g : GLw n w => cT (cj w) (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * 1 *
        (g : Matrix (Fin n) (Fin n) (w.adicCompletion E))) ⁻¹' {1} := rfl
  rw [this]
  refine IsClosed.preimage ?_ isClosed_singleton
  unfold cT
  exact ((((Units.continuous_val.matrix_map (continuous_cj w)).matrix_transpose).matrix_mul continuous_const).matrix_mul
    Units.continuous_val)

def linModel (w : Pl E) {K : UQ} (e : K.E ≃+* w.adicCompletion E) (B : InvAlg K) {n : ℕ}
    (ψ : B.A ≃+ (Fin n → w.adicCompletion E)) (hψ : ∀ (c : K.E) (y : B.A), ψ (c • y) = e c • ψ y) :
    B.A ≃ₗ[K.E] (Fin n → K.E) where
  toFun y i := e.symm (ψ y i)
  invFun v := ψ.symm fun i => e (v i)
  map_add' y z := by
    funext i
    simp
  map_smul' c y := by
    funext i
    simp [hψ c y]
  left_inv y := by
    simp
  right_inv v := by
    funext i
    simp

theorem linModel_mul (w : Pl E) {K : UQ} (e : K.E ≃+* w.adicCompletion E) (B : InvAlg K) {n : ℕ}
    (ψ : B.A ≃+ (Fin n → w.adicCompletion E)) (hψ : ∀ (c : K.E) (y : B.A), ψ (c • y) = e c • ψ y) (a : B.A)
    (g : GLw n w) (ha : ∀ y, ψ (a * y) = g.val *ᵥ ψ y) (y : B.A) :
    linModel w e B ψ hψ (a * y) = ((g : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ
      linModel w e B ψ hψ y := by
  funext i
  change e.symm (ψ (a * y) i) = _
  rw [ha]
  exact RingHom.map_mulVec e.symm.toRingHom _ _ i

end GlobalTheory.KapOrb.CptInt

namespace GlobalTheory.KapOrb.CptInt

open GlobalTheory.UnitLemma

theorem mem_cptPart_iff_torusOf_mem_intUnits : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (Q : (w.adicCompletion E)[X]) (u x : B.A) (n : ℕ) (γ : GLw n w) (hγ : γ ∈ UL n w) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)), Fits w e B Q u → IsModelMap w e B u x γ ψ → ∀ h ∈ twCent (MonoidHom.id (UL n w)) ⟨γ, hγ⟩, (h ∈ cptPart (twCent (MonoidHom.id (UL n w)) ⟨γ, hγ⟩) ↔ torusOf w B ψ h.1 ∈ GlobalTheory.UnitLemma.intUnits K.O B.A) := by
  intro E _ _ _ w hw K e hbr B Q u x n γ hγ ψ hfit hmod h hh
  set T := twCent (MonoidHom.id (UL n w)) ⟨γ, hγ⟩ with hTdef
  have hcomm : ∀ t ∈ T, (t : GLw n w) * γ = γ * t := by
    intro t ht
    have := congrArg Subtype.val (show t * ⟨γ, hγ⟩ = ⟨γ, hγ⟩ * (MonoidHom.id (UL n w)) t from ht)
    simpa using this
  have spec : ∀ t ∈ T, ∀ y, ψ ((torusOf w B ψ (t : GLw n w) : B.A) * y) = (t : GLw n w).val *ᵥ ψ y :=
    fun t ht => (GlobalTheory.KapTorus.torusOf_mem_of_mem_UL_commute E w hw K e B Q u x n γ ψ hfit hmod t t.2 (hcomm t ht)).2
  have specInv : ∀ t ∈ T, ∀ y, ψ ((((torusOf w B ψ (t : GLw n w))⁻¹ : B.Aˣ) : B.A) * y) =
      ((t : GLw n w)⁻¹).val *ᵥ ψ y := by
    intro t ht y
    have h1 := spec t ht ((((torusOf w B ψ (t : GLw n w))⁻¹ : B.Aˣ) : B.A) * y)
    rw [← mul_assoc, Units.mul_inv, one_mul] at h1
    rw [h1, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hcl := isClosed_UL w hw n
  have hint : ∀ z, z ∈ (algebraMap K.O K.E).range ↔ Valued.v (e z) ≤ 1 := hbr.2.1
  have hmat : ∀ (g : GLw n w) (k : ℕ) i j,
      e ((((g : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) ^ k) i j) =
        ((g ^ k : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j := by
    intro g k i j
    have : ((g : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) ^ k =
        ((g ^ k : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm := by
      rw [Units.val_pow_eq_pow_val]
      exact (map_pow (e.symm.toRingHom.mapMatrix) _ k).symm
    rw [this, Matrix.map_apply, RingEquiv.apply_symm_apply]
  set φ := linModel w e B ψ hmod.1 with hφ
  have key : ∀ s ∈ T, IsCompact (closure (Subgroup.zpowers s : Set (UL n w))) ↔
      torusOf w B ψ (s : GLw n w) ∈ intUnits K.O B.A := by
    intro s hs
    have hI1 : IsIntegral K.O ((torusOf w B ψ (s : GLw n w) : B.Aˣ) : B.A) ↔ ∃ m : ℤ, ∀ k : ℕ, ∀ i j,
        Valued.v ((((s : GLw n w) ^ k : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤
          WithZero.exp m := by
      rw [isIntegral_iff_of_mulVec B φ _ _ (linModel_mul w e B ψ hmod.1 _ _ (spec s hs)), GlobalTheory.IntMatBound.isIntegral_iff_bounded K e hint n]
      simp only [hmat]
    have hI2 : IsIntegral K.O ((((torusOf w B ψ (s : GLw n w))⁻¹ : B.Aˣ) : B.A)) ↔ ∃ m : ℤ, ∀ k : ℕ, ∀ i j,
        Valued.v ((((s : GLw n w)⁻¹ ^ k : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤
          WithZero.exp m := by
      rw [isIntegral_iff_of_mulVec B φ _ _ (linModel_mul w e B ψ hmod.1 _ _ (specInv s hs)), GlobalTheory.IntMatBound.isIntegral_iff_bounded K e hint n]
      simp only [hmat]
    rw [GlobalTheory.T.isCompact_closure_zpowers_iff_bounded_entries w n (UL n w) hcl s]
    show _ ↔ IsIntegral K.O _ ∧ IsIntegral K.O _
    rw [hI1, hI2]
    simp only [SubgroupClass.coe_zpow]
    constructor
    · rintro ⟨m, hm⟩
      refine ⟨⟨m, fun k i j => ?_⟩, ⟨m, fun k i j => ?_⟩⟩
      · have := hm (k : ℤ) i j
        rwa [zpow_natCast] at this
      · have := hm (-(k : ℤ)) i j
        rwa [_root_.zpow_neg, zpow_natCast, ← inv_pow] at this
    · rintro ⟨⟨m1, h1⟩, ⟨m2, h2⟩⟩
      refine ⟨max m1 m2, fun k i j => ?_⟩
      rcases Int.eq_nat_or_neg k with ⟨l, rfl | rfl⟩
      · rw [zpow_natCast]
        exact (h1 l i j).trans (WithZero.exp_le_exp.2 (le_max_left _ _))
      · rw [_root_.zpow_neg, zpow_natCast, ← inv_pow]
        exact (h2 l i j).trans (WithZero.exp_le_exp.2 (le_max_right _ _))
  have tmul : ∀ s ∈ T, ∀ t ∈ T, torusOf w B ψ ((s * t : UL n w) : GLw n w) =
      torusOf w B ψ (s : GLw n w) * torusOf w B ψ (t : GLw n w) := by
    intro s hs t ht
    apply torusOf_spec
    intro y
    rw [Units.val_mul, mul_assoc, spec s hs, spec t ht, Matrix.mulVec_mulVec]
    simp
  have tinv : ∀ s ∈ T, torusOf w B ψ ((s⁻¹ : UL n w) : GLw n w) = (torusOf w B ψ (s : GLw n w))⁻¹ := by
    intro s hs
    apply torusOf_spec
    intro y
    rw [specInv s hs]
    simp
  have tone : torusOf w B ψ ((1 : UL n w) : GLw n w) = 1 := by
    apply torusOf_spec
    intro y
    simp
  let H' : Subgroup (UL n w) :=
    { carrier := {s | s ∈ T ∧ torusOf w B ψ (s : GLw n w) ∈ intUnits K.O B.A}
      one_mem' := ⟨T.one_mem, by rw [tone]; exact (intUnits K.O B.A).one_mem⟩
      mul_mem' := by
        rintro s t ⟨hs, hs'⟩ ⟨ht, ht'⟩
        exact ⟨T.mul_mem hs ht, by rw [tmul s hs t ht]; exact (intUnits K.O B.A).mul_mem hs' ht'⟩
      inv_mem' := by
        rintro s ⟨hs, hs'⟩
        exact ⟨T.inv_mem hs, by rw [tinv s hs]; exact (intUnits K.O B.A).inv_mem hs'⟩ }
  constructor
  · intro hc
    have hle : cptPart T ≤ H' := by
      rw [cptPart, Subgroup.closure_le]
      rintro s ⟨hs, hsc⟩
      exact ⟨hs, (key s hs).1 hsc⟩
    exact (hle hc).2
  · intro hi
    exact Subgroup.subset_closure ⟨hh, (key h hh).2 hi⟩

end GlobalTheory.KapOrb.CptInt
