import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.ValSetAlgSubset
import Formalism.LocalToGlobal.ProjectiveLattices.IntAll
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CramerMemAdelicCompletionOfElementSet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinitePartPreservesFormDetNormOneStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RationalPointsAdelicUnitaryEqUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicElementLatticeFullAndCompletionStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceLatticeFractionalMultipleAgreeStatement

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member.LatMove

variable {D : D7} (V : HSp D)

theorem mem_hat_iff (g : GA D V) (w : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    w ∈ latGHat V g ↔ ∃ z ∈ latGHat V 1, (finHom V g).1 *ᵥ z = w := by
  have h1 := (GlobalTheory.T.adelicElementLattice_full_and_completion D V g).2.2.2.1
  have h2 := (GlobalTheory.T.adelicElementLattice_full_and_completion D V 1).2.2.2.2.1
  rw [h2, ← SetLike.mem_coe, h1]
  rfl

theorem mem_lat_iff (g : GA D V) (v : Fin V.rank → D.host.E) :
    v ∈ latG V g ↔ finVec V v ∈ latGHat V g := by
  have h0 := (GlobalTheory.T.adelicElementLattice_full_and_completion D V g).2.2.1
  have h1 := (GlobalTheory.T.adelicElementLattice_full_and_completion D V g).2.2.2.1
  rw [← SetLike.mem_coe, h0, ← SetLike.mem_coe, h1]
  rfl

theorem fin_mul (g h : GA D V) (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    (finHom V (g * h)).1 *ᵥ z = (finHom V g).1 *ᵥ ((finHom V h).1 *ᵥ z) := by
  rw [map_mul, Units.val_mul, Matrix.mulVec_mulVec]

theorem fin_one (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    (finHom V 1).1 *ᵥ z = z := by
  rw [map_one, Units.val_one, Matrix.one_mulVec]

theorem move_mem (g h : GA D V) (w : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E)
    (hw : w ∈ latGHat V h) : (finHom V g).1 *ᵥ w ∈ latGHat V (g * h) := by
  obtain ⟨z, hz, rfl⟩ := (mem_hat_iff V h w).1 hw
  exact (mem_hat_iff V _ _).2 ⟨z, hz, fin_mul V g h z⟩

theorem move_iff (g h : GA D V) (w : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    w ∈ latGHat V h ↔ (finHom V g).1 *ᵥ w ∈ latGHat V (g * h) := by
  refine ⟨move_mem V g h w, fun hw => ?_⟩
  have := move_mem V g⁻¹ _ _ hw
  rwa [← fin_mul, inv_mul_cancel, fin_one, inv_mul_cancel_left] at this

theorem lat_eq_of_hat_eq {h h' : GA D V} (e : latGHat V h = latGHat V h') : latG V h = latG V h' := by
  ext v
  rw [mem_lat_iff, mem_lat_iff, e]

theorem finCong_one {N : ℕ} {k : GA D V} (hk : FinCong V N k) : FinCong V 1 k := by
  intro z hz
  obtain ⟨y, hy, e⟩ := hk z hz
  exact ⟨N • y, AddSubgroup.nsmul_mem _ hy N, by rw [one_nsmul, e]⟩

theorem hat_eq_of_finCong {N : ℕ} {k : GA D V} (hk : FinCong V N k) : latGHat V k = latGHat V 1 := by
  have h1 := (GlobalTheory.T.congruence_lattice_fractionalMultiple_agree D V k).1.2 (finCong_one V hk)
  have h2 : ∀ z ∈ latGHat V 1, (finHom V k⁻¹).1 *ᵥ z ∈ latGHat V 1 := by
    have hh := (GlobalTheory.T.adelicElementLattice_full_and_completion D V 1).2.2.2.2.1
    rw [hh] at h1 ⊢
    rw [map_inv]
    exact GlobalTheory.AdLat.inv_mulVec_mem_hat D.host.F D.host.E V.rank (latG V 1) (finHom V k) (cF D)
      (GlobalTheory.T.adelicElementLattice_full_and_completion D V 1).1 (GlobalTheory.T.adelicElementLattice_full_and_completion D V 1).2.1 h1 (GlobalTheory.T.finitePart_preserves_form_det_norm_one D V k).2.1
  ext w
  rw [mem_hat_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact h1 z hz
  · intro hw
    exact ⟨_, h2 w hw, by rw [← fin_mul, mul_inv_cancel, fin_one]⟩

end GlobalTheory.Member.LatMove

open GlobalTheory.Member.LatMove in

theorem GlobalTheory.Member.latG_move : ∀ (D : D7) (V : HSp D), (∀ γ γ' h, IsRat V γ γ' → (∀ v, v ∈ latG V h ↔ (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v ∈ latG V (γ * h)) ∧ ∀ w, w ∈ latGHat V h ↔ (finHom V γ).1 *ᵥ w ∈ latGHat V (γ * h)) ∧ (∀ h h', finHom V h = finHom V h' → latG V h = latG V h' ∧ latGHat V h = latGHat V h') ∧ (∀ (N : ℕ) h k, FinCong V N k → latG V (h * k) = latG V h ∧ latGHat V (h * k) = latGHat V h) ∧ ∀ h h', latG V h = latG V h' → FinCong V 1 (h⁻¹ * h') := by
  intro D V
  refine ⟨fun γ γ' h hγ => ⟨fun v => ?_, fun w => move_iff V γ h w⟩, fun h h' e => ?_, fun N h k hk => ?_,
    fun h h' e => ?_⟩
  · rw [mem_lat_iff, mem_lat_iff, move_iff V γ h, ((GlobalTheory.T.rational_points_adelicUnitary_eq_unitary D V).2.2.2.2 γ γ' hγ).1 v]
  · have : latGHat V h = latGHat V h' := by
      ext w
      rw [mem_hat_iff V h, mem_hat_iff V h', e]
    exact ⟨lat_eq_of_hat_eq V this, this⟩
  · have : latGHat V (h * k) = latGHat V h := by
      ext w
      rw [move_iff V h⁻¹ (h * k), move_iff V h⁻¹ h, inv_mul_cancel_left, inv_mul_cancel,
        hat_eq_of_finCong V hk]
    exact ⟨lat_eq_of_hat_eq V this, this⟩
  · have e' : latGHat V h = latGHat V h' := by
      rw [(GlobalTheory.T.adelicElementLattice_full_and_completion D V h).2.2.2.2.1, (GlobalTheory.T.adelicElementLattice_full_and_completion D V h').2.2.2.2.1, e]
    refine (GlobalTheory.T.congruence_lattice_fractionalMultiple_agree D V (h⁻¹ * h')).1.1 fun z hz => ?_
    have h1 := move_mem V h' 1 z hz
    rw [mul_one, ← e'] at h1
    have h2 := move_mem V h⁻¹ h _ h1
    rwa [← fin_mul, inv_mul_cancel] at h2
