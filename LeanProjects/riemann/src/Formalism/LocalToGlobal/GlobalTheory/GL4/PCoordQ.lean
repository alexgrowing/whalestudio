import Formalism.LocalToGlobal.GlobalTheory.GL4.CTEqConjTranspose
import Formalism.LocalToGlobal.GlobalTheory.GL4.PFrGen
import Formalism.GL3MeanSquares.HookFormulaTorsion.HadamardUnitDiagonalDetLeOne

noncomputable section

open NumberField Matrix

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Cc

variable {E : Type} [Field E] [NumberField E]

def incl (n : ℕ) : (Fin n → 𝓞 E) →ₗ[𝓞 E] (Fin n → E) := (Algebra.linearMap (𝓞 E) E).compLeft (Fin n)

theorem incl_apply (n : ℕ) (m : Fin n → 𝓞 E) (i : Fin n) : incl n m i = (m i : E) := rfl

theorem incl_injective (n : ℕ) : Function.Injective (incl (E := E) n) := by
  intro a b h
  funext i
  exact RingOfIntegers.coe_injective (congrFun h i)

def psi {n : ℕ} (G : Matrix (Fin n) (Fin n) E) : (Fin n → 𝓞 E) →ₗ[𝓞 E] (Fin n → E) :=
  ((Matrix.mulVecLin G⁻¹).restrictScalars (𝓞 E)).comp (incl n)

theorem psi_apply {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (m : Fin n → 𝓞 E) : psi G m = G⁻¹ *ᵥ incl n m := rfl

theorem incl_mulVec {n : ℕ} (Gm : Matrix (Fin n) (Fin n) (𝓞 E)) (m : Fin n → 𝓞 E) :
    incl n (Gm *ᵥ m) = (Gm.map ((↑) : 𝓞 E → E)) *ᵥ incl n m := by
  funext i
  rw [incl_apply]
  exact (RingHom.map_mulVec (algebraMap (𝓞 E) E) Gm m i)

theorem psi_mulVec {n : ℕ} (Gm : Matrix (Fin n) (Fin n) (𝓞 E)) (hdet : (Gm.map ((↑) : 𝓞 E → E)).det ≠ 0)
    (m : Fin n → 𝓞 E) : psi (Gm.map ((↑) : 𝓞 E → E)) (Gm *ᵥ m) = incl n m := by
  rw [psi_apply, incl_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet),
    Matrix.one_mulVec]

theorem psi_injective {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (hdet : G.det ≠ 0) : Function.Injective (psi G) := by
  intro a b h
  apply incl_injective n
  have := congrArg (fun z ↦ G *ᵥ z) h
  simp only [psi_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet),
    Matrix.one_mulVec] at this
  exact this

theorem det_map_ne {n : ℕ} (Gm : Matrix (Fin n) (Fin n) (𝓞 E)) (hdet : (Gm.map ((↑) : 𝓞 E → E)).det ≠ 0) :
    Gm.det ≠ 0 := by
  intro h
  apply hdet
  rw [show (Gm.map ((↑) : 𝓞 E → E)) = (algebraMap (𝓞 E) E).mapMatrix Gm from rfl, ← RingHom.map_det, h, map_zero]

theorem card_quot {n : ℕ} (Gm : Matrix (Fin n) (Fin n) (𝓞 E)) (h : Gm.det ≠ 0) :
    Nat.card ((Fin n → 𝓞 E) ⧸ LinearMap.range (Matrix.mulVecLin Gm)) = (Algebra.norm ℤ Gm.det).natAbs := by
  have hinj : Function.Injective (Matrix.mulVecLin Gm) := fun a b hab ↦ by
    have : Gm *ᵥ (a - b) = 0 := by
      rw [Matrix.mulVec_sub]; exact sub_eq_zero.2 hab
    exact sub_eq_zero.1 (Matrix.eq_zero_of_mulVec_eq_zero h this)
  set N : Submodule ℤ (Fin n → 𝓞 E) := (LinearMap.range (Matrix.mulVecLin Gm)).restrictScalars ℤ with hN
  let e : (Fin n → 𝓞 E) ≃ₗ[ℤ] N := (LinearEquiv.ofInjective (Matrix.mulVecLin Gm) hinj).restrictScalars ℤ
  have key := Submodule.natAbs_det_equiv N e
  have hq : Nat.card ((Fin n → 𝓞 E) ⧸ N) = Nat.card ((Fin n → 𝓞 E) ⧸ LinearMap.range (Matrix.mulVecLin Gm)) :=
    Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv ℤ (LinearMap.range (Matrix.mulVecLin Gm))).toEquiv
  rw [← hq, ← key]
  have hmap : (N.subtype ∘ₗ AddMonoidHom.toIntLinearMap (e : (Fin n → 𝓞 E) →+ N)) =
      (Matrix.mulVecLin Gm).restrictScalars ℤ := by
    ext x
    rfl
  rw [hmap, LinearMap.det_restrictScalars, ← Matrix.toLin'_apply', LinearMap.det_toLin']

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Cc

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Cc

variable {E : Type} [Field E] [NumberField E]

abbrev P0 (n : ℕ) : Submodule (𝓞 E) (Fin n → E) := LinearMap.range (incl (E := E) n)

def Between {n : ℕ} (G : Matrix (Fin n) (Fin n) E) : Set (Submodule (𝓞 E) (Fin n → E)) :=
  {C | P0 n ≤ C ∧ C ≤ LinearMap.range (psi G) ∧ C.FG}

theorem between_finite_card {n : ℕ} (Gm : Matrix (Fin n) (Fin n) (𝓞 E))
    (hdet : (Gm.map ((↑) : 𝓞 E → E)).det ≠ 0) :
    (Between (Gm.map ((↑) : 𝓞 E → E))).Finite ∧
    (Between (Gm.map ((↑) : 𝓞 E → E))).ncard ≤ (Algebra.norm ℤ Gm.det).natAbs ^ n := by
  classical
  set G := Gm.map ((↑) : 𝓞 E → E) with hG
  set Rg := LinearMap.range (Matrix.mulVecLin Gm) with hRg
  have hcard := card_quot Gm (det_map_ne Gm hdet)
  have hpos : (Algebra.norm ℤ Gm.det).natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero]
    exact (Algebra.norm_ne_zero_iff).2 (det_map_ne Gm hdet)
  have : Finite ((Fin n → 𝓞 E) ⧸ Rg) := Nat.finite_of_card_ne_zero (hcard ▸ hpos)
  let θ : Submodule (𝓞 E) ((Fin n → 𝓞 E) ⧸ Rg) → Submodule (𝓞 E) (Fin n → E) :=
    fun H ↦ (H.comap Rg.mkQ).map (psi G)
  let Gen : Set (Submodule (𝓞 E) ((Fin n → 𝓞 E) ⧸ Rg)) :=
    {H | ∃ s : Fin n → (Fin n → 𝓞 E) ⧸ Rg, Submodule.span (𝓞 E) (Set.range s) = H}
  have hsub : Between G ⊆ θ '' Gen := by
    rintro C ⟨h0, h1, hfg⟩
    have hRC : Rg ≤ C.comap (psi G) := by
      rintro _ ⟨m, rfl⟩
      show psi G (Gm *ᵥ m) ∈ C
      rw [psi_mulVec Gm hdet]
      exact h0 ⟨m, rfl⟩
    refine ⟨(C.comap (psi G)).map Rg.mkQ, ?_, ?_⟩
    · obtain ⟨b, hb, hgen⟩ := Fr.genMod_fg (E := E) (Nat.card ((Fin n → 𝓞 E) ⧸ Rg)) Nat.card_pos.ne' n C hfg
      have hb' : ∀ a, ∃ m, psi G m = b a := fun a ↦ h1 (hb a)
      choose mb hmb using hb'
      refine ⟨fun a ↦ Rg.mkQ (mb a), le_antisymm ?_ ?_⟩
      · rw [Submodule.span_le]
        rintro _ ⟨a, rfl⟩
        refine Submodule.mem_map_of_mem ?_
        show psi G (mb a) ∈ C
        rw [hmb]
        exact hb a
      · rintro _ ⟨m, hm, rfl⟩
        obtain ⟨c, z, hz, hx⟩ := hgen (psi G m) hm
        obtain ⟨mz, hmz⟩ := h1 hz
        have hN : (Nat.card ((Fin n → 𝓞 E) ⧸ Rg)) • Rg.mkQ mz = 0 := card_nsmul_eq_zero'
        have hm_eq : m = ∑ a, c a • mb a + (Nat.card ((Fin n → 𝓞 E) ⧸ Rg)) • mz := by
          apply psi_injective G hdet
          rw [map_add, map_sum, map_nsmul, hx, hmz, ← Nat.cast_smul_eq_nsmul E]
          congr 1
          refine Finset.sum_congr rfl fun a _ ↦ ?_
          rw [map_smul, hmb]
        rw [hm_eq, map_add, map_sum, map_nsmul, hN, add_zero]
        exact Submodule.sum_mem _ fun a _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self a))
    · show (((C.comap (psi G)).map Rg.mkQ).comap Rg.mkQ).map (psi G) = C
      rw [Submodule.comap_map_mkQ, sup_eq_right.2 hRC, Submodule.map_comap_eq, inf_eq_right.2 h1]
  have hGfin : Gen.Finite := by
    refine (Set.finite_range fun s : Fin n → (Fin n → 𝓞 E) ⧸ Rg ↦ Submodule.span (𝓞 E) (Set.range s)).subset ?_
    rintro H ⟨s, rfl⟩
    exact ⟨s, rfl⟩
  have hGcard : Gen.ncard ≤ Nat.card ((Fin n → 𝓞 E) ⧸ Rg) ^ n := by
    have := Formalism.HermitianLattices.LatticeEstimates.moduli_intermediate_bound (𝓞 E) ((Fin n → 𝓞 E) ⧸ Rg) n
    rw [← Nat.card_coe_set_eq]
    exact this
  refine ⟨(hGfin.image θ).subset hsub, ?_⟩
  calc (Between G).ncard ≤ (θ '' Gen).ncard := Set.ncard_le_ncard hsub (hGfin.image θ)
    _ ≤ Gen.ncard := Set.ncard_image_le hGfin
    _ ≤ _ := by rw [← hcard]; exact hGcard

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Cc

end
