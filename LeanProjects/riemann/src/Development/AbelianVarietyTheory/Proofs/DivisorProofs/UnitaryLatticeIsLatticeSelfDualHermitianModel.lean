import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelLat
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

noncomputable section

namespace GlobalTheory.InertUnitOrb.SelfDualLat

theorem stdH_eq_dot (K : UQ) {n : ℕ} (a b : Fin n → K.E) :
    stdH K n a b = a ⬝ᵥ (fun k => K.c (b k)) := rfl

theorem stdH_mulVec (K : UQ) {n : ℕ} (P : Matrix (Fin n) (Fin n) K.E)
    (hP : Pᵀ * P.map K.c = 1) (u v : Fin n → K.E) :
    stdH K n (P *ᵥ u) (P *ᵥ v) = stdH K n u v := by
  have hv : (fun k => K.c ((P *ᵥ v) k)) = P.map K.c *ᵥ (fun k => K.c (v k)) := by
    funext k
    exact RingHom.map_mulVec (K.c : K.E →+* K.E) P v k
  rw [stdH_eq_dot, stdH_eq_dot, hv, dotProduct_mulVec, ← vecMul_transpose, vecMul_vecMul, hP, vecMul_one]

theorem intVec_eq_range (K : UQ) (n : ℕ) :
    intVec K n = LinearMap.range ((Algebra.linearMap K.O K.E).compLeft (Fin n)) := by
  ext v
  constructor
  · intro hv
    have h := fun i => RingHom.mem_range.mp (hv i)
    choose o ho using h
    exact ⟨o, funext fun i => ho i⟩
  · rintro ⟨o, rfl⟩ i
    exact ⟨o i, rfl⟩

theorem intVec_fg (K : UQ) (n : ℕ) : (intVec K n).FG := by
  rw [intVec_eq_range, LinearMap.range_eq_map]
  exact Submodule.FG.map _ Module.Finite.fg_top

theorem single_mem_intVec (K : UQ) {n : ℕ} (i : Fin n) : (Pi.single i (1 : K.E) : Fin n → K.E) ∈ intVec K n := by
  intro j
  by_cases h : j = i
  · subst h; exact ⟨1, by simp⟩
  · exact ⟨0, by simp [Pi.single_apply, h]⟩

theorem unitLat_isLat_selfDual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (x : B.Aˣ), B.σ (x : B.A) = x → (∀ y z, stdH K n (ψ y) (ψ z) = B.herm x y z) → ∀ q : UL n w, IsLat K.O K.E (unitLat e B ψ q) ∧ ∀ y, y ∈ unitLat e B ψ q ↔ ∀ z ∈ unitLat e B ψ q, B.herm x y z ∈ (algebraMap K.O K.E).range := by
  intro E _ _ _ _ w hns K e he hint n B ψ x hx hψ q
  set Qm : Matrix (Fin n) (Fin n) (w.adicCompletion E) :=
    (((q⁻¹ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hQm
  have hmem : ∀ g : GLw n w, g ∈ UL n w → g ∈ UJ (cj w) 1 := by
    intro g hg
    simpa [UL, hns] using hg
  have hQ : cT (cj w) Qm * 1 * Qm = 1 := hmem _ (q⁻¹).2
  have h2 : (Qm.map (cj w))ᵀ * Qm = 1 := by simpa [cT] using hQ
  set P : Matrix (Fin n) (Fin n) K.E := Qm.map e.symm with hPdef
  have hPc : P.map K.c = (Qm.map (cj w)).map e.symm := by
    ext i j
    apply e.injective
    simp [hPdef, he]
  have hP1 : (P.map K.c)ᵀ * P = 1 := by
    have h3 := congrArg (e.symm.toRingHom.mapMatrix) h2
    simp only [map_mul, map_one, RingHom.mapMatrix_apply] at h3
    rw [hPc, hPdef, ← Matrix.transpose_map]
    simpa using h3
  have hPR : P * (P.map K.c)ᵀ = 1 := mul_eq_one_comm.mp hP1
  have hPT : Pᵀ * P.map K.c = 1 := by
    have h4 := congrArg Matrix.transpose hP1
    simpa [Matrix.transpose_mul] using h4
  let G : (Fin n → K.E) →ₗ[K.E] B.A := ψ.symm.toLinearMap ∘ₗ Matrix.toLin' (P.map K.c)ᵀ
  have hGP : ∀ y, G (P *ᵥ ψ y) = y := by
    intro y
    simp [G, Matrix.toLin'_apply, mulVec_mulVec, hP1]
  have hPG : ∀ a, P *ᵥ ψ (G a) = a := by
    intro a
    simp [G, Matrix.toLin'_apply, mulVec_mulVec, hPR]
  have hmemL : ∀ y, y ∈ unitLat e B ψ q ↔ P *ᵥ ψ y ∈ intVec K n := fun y => Iff.rfl
  have hmap : unitLat e B ψ q = (intVec K n).map (G.restrictScalars K.O) := by
    ext y
    rw [hmemL]
    constructor
    · intro hy
      exact ⟨P *ᵥ ψ y, hy, hGP y⟩
    · rintro ⟨a, ha, rfl⟩
      rw [LinearMap.restrictScalars_apply, hPG]
      exact ha
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hmap]
    exact (intVec_fg K n).map _
  · rw [eq_top_iff]
    have key : Submodule.map G ⊤ ≤ Submodule.span K.E (unitLat e B ψ q : Set B.A) := by
      rw [← (Pi.basisFun K.E (Fin n)).span_eq, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      apply Submodule.subset_span
      show G _ ∈ unitLat e B ψ q
      rw [hmemL, Pi.basisFun_apply, hPG]
      exact single_mem_intVec K i
    intro y _
    rw [← hGP y]
    exact key (Submodule.mem_map_of_mem trivial)
  · intro y
    rw [hmemL]
    constructor
    · intro hy z hz
      rw [hmemL] at hz
      rw [← hψ, ← stdH_mulVec K P hPT]
      unfold stdH
      apply Subring.sum_mem
      intro k _
      apply Subring.mul_mem _ (hy k)
      obtain ⟨o, ho⟩ := hz k
      obtain ⟨o', ho'⟩ := K.c_int o
      exact ⟨o', by rw [← ho, ho']⟩
    · intro h i
      have h5 := h (G (Pi.single i 1)) (by rw [hmemL, hPG]; exact single_mem_intVec K i)
      rw [← hψ, ← stdH_mulVec K P hPT, hPG] at h5
      simpa [stdH, Pi.single_apply, apply_ite] using h5

end GlobalTheory.InertUnitOrb.SelfDualLat
