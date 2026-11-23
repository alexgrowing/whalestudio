import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.ValSetAlgSubset
import Formalism.LocalToGlobal.ProjectiveLattices.IntAll
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceLatticeFractionalMultipleAgreeStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ArchimedeanMatrixUnitaryContinuousMultiplicativeStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PrincipalLevelEqHalfMarkingStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicElementLatticeFullAndCompletionStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

private theorem fib_gram_eq {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (x : Matrix (Fin r) (Fin r) ℂ) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ G x = xᵀ * (G.map τ * x.map (starRingEnd ℂ)) := by
  ext a b
  simp [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.mul_apply, Finset.mul_sum, mul_assoc]

private theorem fib_cancel {R G : Type} [CommRing R] [Group G] {n : ℕ} (f : G →* GL (Fin n) R) (g g' : G) (N : ℕ)
    (p v w w' y : Fin n → R) (e : p - (f g).1 *ᵥ v = N • w) (e' : p - (f g').1 *ᵥ v = N • w')
    (ey : (f g).1 *ᵥ y = w - w') : (f (g⁻¹ * g')).1 *ᵥ v - v = N • y := by
  have e2 : (f g').1 *ᵥ v - (f g).1 *ᵥ v = N • ((f g).1 *ᵥ y) := by
    rw [ey, smul_sub, ← e, ← e']; abel
  have hi : ∀ z, (f g⁻¹).1 *ᵥ ((f g).1 *ᵥ z) = z := fun z => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
      Matrix.one_mulVec]
  have e3 := congrArg (fun z => (f g⁻¹).1 *ᵥ z) e2
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, hi] at e3
  rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
  exact e3

theorem mem_level_of_mark_of_frame_eq : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ (Kf : Subgroup (GA D V)), IsLevelK V l.M Kf → ∀ h h' k γ γ', C.Mark h k γ → C.Mark h' k γ' → C.fr (γ * h) k = C.fr (γ' * h') k → (γ * h)⁻¹ * (γ' * h') ∈ Kf := by
  intro D H Dw l Xo c σ V r C hC Kf hK h h' k γ γ' hm hm' hfr
  obtain rfl : V.rank = r := C.hr
  obtain ⟨-, hL, hM⟩ := hm
  obtain ⟨-, hL', hM'⟩ := hm'
  generalize γ * h = g at *
  generalize γ' * h' = g' at *
  obtain ⟨hA, hG, -⟩ := GlobalTheory.T.archimedeanMatrix_unitary_continuous_multiplicative D V C.θ hC.inf
  rw [hK]
  refine ⟨hG _ fun τ hτ => ?_, ?_⟩
  · have hΨ : τ ∈ (C.M.X k).Ψ := by
      rw [(hC.base.type k).2, hC.iota.rt, hC.iota.rt0]; exact hτ
    have hx : (C.x₀ τ).det ≠ 0 := by
      intro h0
      have h1 := congrArg Matrix.det (hC.orth k τ hΨ)
      simp only [fib_gram_eq, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul,
        Matrix.det_diagonal] at h1
      refine Finset.prod_ne_zero_iff.2 (fun a _ => ?_) h1.symm
      unfold sgn
      split_ifs <;> simp
    have h1 : archM V (C.θ τ) g * C.x₀ τ = archM V (C.θ τ) g' * C.x₀ τ := congrFun hfr ⟨τ, hΨ⟩
    have hu : IsUnit (C.x₀ τ) := (Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit hx)
    have h2 := hu.mul_right_cancel h1
    rw [(hA τ).2.1, ← h2, ← (hA τ).2.1, inv_mul_cancel, (hA τ).1]
  · have hlat : (latG V g : Set (Fin V.rank → D.host.E)) = latG V g' := by
      have e := hL.symm.trans hL'
      have e1 : (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast C.hr.symm) = id := rfl
      rwa [e1, Set.image_id, Set.image_id] at e
    have hhat : latGHat V g' = latGHat V g := by
      rw [(GlobalTheory.T.adelicElementLattice_full_and_completion D V g).2.2.2.2.1, (GlobalTheory.T.adelicElementLattice_full_and_completion D V g').2.2.2.2.1, hlat]
    have himg := (GlobalTheory.T.adelicElementLattice_full_and_completion D V g).2.2.2.1
    rw [← (GlobalTheory.T.adelicElementLattice_full_and_completion D V 1).2.2.2.2.1] at himg
    refine ((GlobalTheory.T.principalLevel_eq_halfMarking_stabilizer D H l V).1 _).2 ((((GlobalTheory.T.congruence_lattice_fractionalMultiple_agree D V) _).2 _ _).2 ?_)
    intro a ha
    rw [← hC.iota.emb.2, LinearMap.range_eq_map, ← Submodule.map_smul''] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    obtain ⟨w, hw, e⟩ := hM b hb
    obtain ⟨w', hw', e'⟩ := hM' b hb
    rw [hhat] at hw'
    have hd : w - w' ∈ (latGHat V g : Set _) := sub_mem hw hw'
    rw [himg] at hd
    obtain ⟨y, hy, ey⟩ := hd
    exact ⟨y, hy, fib_cancel (finHom V) g g' l.M _ _ w w' y e e' ey⟩

end GlobalTheory.Member
