import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAuxiliaryVectorOrthogonalImage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardAdelicCharacterLocalComponentNeOneStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceAnnihilatorRelativelyCompactStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PosLinVec

theorem hA_single {D : D7} (A : HSp D) (x : Fin A.rank → AE D) (i : Fin A.rank) (s : AE D) :
    hA A x (Pi.single i (cA D s)) = (A.gram.map (incA D)).mulVec x i * s := by
  rw [hA_eq, show (fun j => cA D ((Pi.single i (cA D s) : Fin A.rank → AE D) j)) = Pi.single i s from
    funext fun j => by by_cases e : j = i <;> simp [e, GlobalTheory.RootExch.cA_cA], single_dotProduct, mul_comm]

theorem vec_of_scalar {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {n : ℕ}
    (c : R →+* R) (hc : Continuous c) (ε u w : R) (huw : w * u = 1) (J : Matrix (Fin n) (Fin n) R) (hJ : IsUnit J)
    (h : (Fin n → R) → (Fin n → R) → R) (hh : ∀ x i s, h x (Pi.single i (c s)) = J.mulVec x i * s)
    (P : R → Prop)
    (H : ∀ V ∈ nhds (0 : R), ∃ C : Set R, IsCompact C ∧ ∀ a, ε * a = a → (∀ s ∈ V, ε * s = s → P (a * s)) → a ∈ C) :
    ∀ V ∈ nhds (0 : Fin n → R), ∃ C : Set (Fin n → R), IsCompact C ∧ ∀ t₀, ε • t₀ = t₀ →
      (∀ t ∈ V, c ε • t = t → P (u * h t₀ t)) → t₀ ∈ C := by
  intro V hV
  have hc' : ∀ i : Fin n, Continuous fun s : R => (Pi.single i (c s) : Fin n → R) := fun i =>
    (continuous_single (A := fun _ : Fin n => R) i).comp hc
  have hVi : ∀ i : Fin n, (fun s : R => (Pi.single i (c s) : Fin n → R)) ⁻¹' V ∈ nhds (0 : R) := fun i =>
    (hc' i).continuousAt.preimage_mem_nhds (by simpa only [map_zero, Pi.single_zero] using hV)
  choose C hC hmem using fun i => H _ (hVi i)
  obtain ⟨K, hK⟩ := hJ.exists_left_inv
  let g : (Fin n → R) → (Fin n → R) := fun a => w • K.mulVec a
  have hg0 : Continuous fun a : Fin n → R => K.mulVec a := continuous_const.matrix_mulVec continuous_id
  have hg : Continuous g := continuous_pi fun i => continuous_const.mul ((continuous_apply i).comp hg0)
  refine ⟨g '' Set.pi Set.univ C, (isCompact_univ_pi hC).image hg, fun t₀ ht h' => ?_⟩
  refine ⟨u • J.mulVec t₀, fun i _ => hmem i _ ?_ fun s hs hεs => ?_, ?_⟩
  · conv_rhs => rw [← ht]
    simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    ring
  · have := h' _ hs (by rw [← Pi.single_smul, smul_eq_mul, ← map_mul, hεs])
    rw [hh] at this
    rw [Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact this
  · simp only [g]
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hK, Matrix.one_mulVec, smul_smul, huw, one_smul]

theorem annihilator_subset_compact : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ ε : AE D, IsSplitIdem D ε → ∀ (A : HSp D) (θ : D.host.E), θ ≠ 0 → ∀ V ∈ nhds (0 : Fin A.rank → AE D), ∃ C : Set (Fin A.rank → AE D), IsCompact C ∧ ∀ t₀, ε • t₀ = t₀ → (∀ t ∈ V, cA D ε • t = t → ψ (Algebra.trace (AF D.host.F) (AE D) (incA D θ * hA A t₀ t)) = 1) → t₀ ∈ C := by
  intro D ψ hψ ε hε A θ hθ
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  exact vec_of_scalar (cA D) GlobalTheory.FockCompare.ThetaCont.continuous_conj ε (incA D θ) (incA D θ⁻¹)
    (by rw [← RingHom.map_mul, inv_mul_cancel₀ hθ, RingHom.map_one]) (A.gram.map (incA D))
    ((GlobalTheory.BesselCompare.gram_isUnit A).map (incA D).mapMatrix) (hA A) (hA_single A)
    (fun a => ψ (Algebra.trace (AF D.host.F) (AE D) a) = 1)
    (GlobalTheory.T.splitPlace_annihilator_relativelyCompact D ψ (GlobalTheory.T.standardAdelicCharacter_localComponent_ne_one D ψ hψ) ε hε)

end GlobalTheory.PosLinVec
