import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmAtSmulRight
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDualStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SpanRealProjectionRationalPointsEqTop
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ContinuousOfHeisenbergLevelAndSmooth
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharacterHalfSymplecticFormRealPointStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealSymplecticFormAlternatingInvariantDefiniteStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SymplecticAdelicFormBiadditiveAlternatingRationaStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ScaledFiniteMatrixMemLatticeStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NotLinearIndependentStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RationalPointsFinitePartSelfDualLatticeIffStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FockVacuumAnnihilationEquationRealCoordinatesStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockCompare

noncomputable section

namespace GlobalTheory.VacUnique

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem apply_real_add (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {u : WO S T} (hu : u.map (infPart D) = 0)
    {f : WO S T → ℂ} {ε : ℂ} (hf : heisO ψ S T u f = ε • f) (z : RW T S) :
    f (iotaW σ T S z + u) = ε * f (iotaW σ T S z) := by
  have e : ψ (symplOH S T (iotaW σ T S z) u) * f (iotaW σ T S z + u) = ε * f (iotaW σ T S z) := congrFun hf _
  rw [GlobalTheory.T.stdCharacter_halfSymplecticForm_realPoint D θ ψ h.inf hψ S T _ _ (Or.inl (h.real_iota T S z)), piW_of_inf θ hu, LinearMap.map_zero] at e
  simpa using e

theorem exists_decomp (h : Chart θ σ) {Λ : AddSubgroup (WO S T)}
    (h2 : ∀ γ : WO S T, γ.map (infPart D) = 0 → ∃ ρ ∈ ratL T S, ∃ u ∈ Λ, (γ - ρ - u).map (finPart D) = 0)
    (w : WO S T) : ∃ γ z, ∃ u ∈ Λ, w = ratW T S γ + (iotaW σ T S z + u) := by
  have h0 : (w - iotaW σ T S (piW θ T S w) : WO S T).map (infPart D) = 0 := by
    have hp : piW θ T S (w - iotaW σ T S (piW θ T S w)) = 0 := by
      rw [AddMonoidHom.map_sub, h.pi_iota, sub_self]
    funext i j
    exact ThetaCont.infPart_eq_zero h _ fun τ => congrFun (congrFun (congrFun hp τ) i) j
  obtain ⟨_, ⟨γ, rfl⟩, u, hu, hr⟩ := h2 _ h0
  refine ⟨γ, piW θ T S w + piW θ T S (w - iotaW σ T S (piW θ T S w) - ratW T S γ - u), u, hu, ?_⟩
  rw [AddMonoidHom.map_add, h.iota_pi (x := w - iotaW σ T S (piW θ T S w) - ratW T S γ - u) hr]
  abel

theorem apply_add_infRat (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (v : Matrix (Fin T.rank) (Fin S.rank) D.host.E) {ε : ℂ} (he : heisO ψ S T (finRat S T (-v)) f = ε • f) (z : RW T S) :
    f (iotaW σ T S (z + infRat S T v)) =
      (ψ (-symplOH S T (ratW T S v) (finRat S T (-v))) * ε) *
        Complex.exp (-(Real.pi * Complex.I) * (-omO S T (infRat S T v) z : ℝ)) * f (iotaW σ T S z) := by
  have e : iotaW σ T S (z + infRat S T v) = ratW T S v + (iotaW σ T S z + finRat S T (-v)) := by
    rw [ratW_eq h, AddMonoidHom.map_add, AddMonoidHom.map_neg]
    abel
  have e2 : symplOH S T (ratW T S v) (iotaW σ T S z + finRat S T (-v)) =
      symplOH S T (ratW T S v) (iotaW σ T S z) + symplOH S T (ratW T S v) (finRat S T (-v)) := by
    unfold symplOH
    rw [(GlobalTheory.T.symplecticAdelicForm_biadditive_alternating_rational D S T).2.1, mul_add]
  rw [e, hf.quasi, apply_real_add h hψ (finRat_inf S T _) he, e2, neg_add, AddChar.map_add_eq_mul,
    AddChar.map_neg_eq_inv ψ (symplOH S T (ratW T S v) (iotaW σ T S z)),
    GlobalTheory.T.stdCharacter_halfSymplecticForm_realPoint D θ ψ h.inf hψ S T _ _ (Or.inr (h.real_iota T S z)), piW_ratW h.inf, h.pi_iota, ← Complex.exp_neg]
  push_cast
  ring_nf

theorem infRat_injective (S T : HSp D) : Function.Injective (infRat S T) := by
  intro x y e
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.F) := inferInstance
    exact ⟨((GlobalTheory.CMTypePlaces.places_bijective D).2 w).choose⟩
  funext i j
  exact (tauE D τ).injective (congrFun (congrFun (congrFun e τ) i) j)

theorem vacUniqueO : ∀ D : D7, VacUniqueO D := by
  classical
  intro D ψ θ hψ hθ S T sS sT _ _ hS hT ΛS ΛT hΛS hΛT f f' hf hf'
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.self_dual_lattice_pairing_dual D ψ S T ΛS ΛT hψ hΛS hΛT
  have hden := GlobalTheory.T.scaled_finite_matrix_mem_lattice D S T ΛS ΛT hΛS.1 hΛT.1
  have hlat := hf.2.lat
  have hlat' := hf'.2.lat
  have hinf := fun u => latO_inf (u := u) S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
    fun _ => True
  generalize latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) = Λ
    at h1 h2 h3 hden hlat hlat' hinf
  choose ε hε1 hε2 using h3 f hlat

  have det : ∀ (g g' : WO S T → ℂ) (c : ℂ), IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' →
      IsLatVac (heisO ψ S T) Λ g → IsLatVac (heisO ψ S T) Λ g' →
      (∀ z, g' (iotaW σ T S z) = c * g (iotaW σ T S z)) → g' = c • g := by
    intro g g' c hg hg' hl hl' hz
    funext w
    obtain ⟨γ, z, u, hu, rfl⟩ := exists_decomp h h2 w
    rw [Pi.smul_apply, smul_eq_mul, hg.quasi, hg'.quasi, apply_real_add h hψ (hinf u hu) (hε2 u hu g hl),
      apply_real_add h hψ (hinf u hu) (hε2 u hu g' hl'), hz]
    ring
  obtain ⟨⟨p, hp⟩, hn⟩ := hf.2.norm
  have n1 : nrm2 p.1 p.2 f = 1 := hn p hp
  have n2 : nrm2 p.1 p.2 f' = 1 := hf'.2.norm.2 p hp
  have hne : (fun z : RW T S => f (iotaW σ T S z)) ≠ 0 := by
    intro h0
    have e := det f f 0 hf.2.theta hf.2.theta hlat hlat fun z => by rw [zero_mul]; exact congrFun h0 z
    rw [e] at n1
    simp [nrm2] at n1
  obtain ⟨j1, j2, j3, j4⟩ := GlobalTheory.T.realSymplecticForm_alternating_invariant_definite D S T sS sT hS hT
  have hsp : Submodule.span ℝ (Set.range (infRat S T)) = ⊤ := by
    have := span_piW_ratW_eq_top D θ σ h T S
    simpa only [piW_ratW hθ] using this
  have a1 := GlobalTheory.T.fockVacuum_annihilation_equation_real_coordinates D θ σ h ψ hψ S T sS sT f hf.2.theta hf.2.fock
  have a2 := GlobalTheory.T.fockVacuum_annihilation_equation_real_coordinates D θ σ h ψ hψ S T sS sT f' hf'.2.theta hf'.2.fock
  let c : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ := fun v =>
    if hv : finRat S T (-v) ∈ Λ then ψ (-symplOH S T (ratW T S v) (finRat S T (-v))) * ε _ hv else 1
  have hc : ∀ v, ‖c v‖ = 1 := fun v => by
    simp only [c]
    split_ifs with hv
    · rw [norm_mul, hψ.1.2.1]
      rcases hε1 _ hv with e | e <;> rw [e] <;> simp
    · exact norm_one
  have law : ∀ g : WO S T → ℂ, IsThetaFunO ψ S T g → IsLatVac (heisO ψ S T) Λ g →
      ∀ v ∈ Λ.comap (finRat S T), ∀ z, g (iotaW σ T S (z + infRat S T v)) =
        c v * Complex.exp (-(Real.pi * Complex.I) * (omO S T z (infRat S T v) : ℂ)) * g (iotaW σ T S z) := by
    intro g hg hl v hv z
    have hv' : finRat S T (-v) ∈ Λ := (Λ.comap (finRat S T)).neg_mem hv
    rw [apply_add_infRat h hψ hg v (hε2 _ hv' g hl) z, ← j2]
    simp only [c, dif_pos hv']
  have hli := GlobalTheory.T.not_linearIndependent_alt (RW T S) (jO S T sS sT) (omO S T) j1 j2 j3 j4 (Matrix (Fin T.rank) (Fin S.rank) D.host.E)
    (infRat S T) (infRat_injective S T) hsp (Λ.comap (finRat S T))
    (fun x => by
      obtain ⟨N, hN, hx⟩ := hden x
      exact ⟨N, hN, by rwa [AddSubgroup.mem_comap, AddMonoidHom.map_nsmul]⟩)
    (GlobalTheory.T.rationalPoints_finitePart_selfDual_lattice_iff D S T ψ Λ hψ hinf h1 h2 hden) c hc
    ![fun z => f (iotaW σ T S z), fun z => f' (iotaW σ T S z)]
    (fun k => by fin_cases k; exacts [a1.1, a2.1]) (fun k => by fin_cases k; exacts [a1.2, a2.2])
    (fun k => by fin_cases k; exacts [law f hf.2.theta hlat, law f' hf'.2.theta hlat'])
  rw [LinearIndependent.pair_iff' hne] at hli
  push_neg at hli
  obtain ⟨a, ha⟩ := hli
  have e := det f f' a hf.2.theta hf'.2.theta hlat hlat' fun z => (congrFun ha z).symm
  refine ⟨a, ?_, e⟩
  have n3 : nrm2 p.1 p.2 (a • f) = ‖a‖ ^ 2 * nrm2 p.1 p.2 f := by
    simp only [nrm2, Pi.smul_apply, norm_smul, mul_pow]
    exact integral_const_mul _ _
  rw [e, n3, n1, mul_one] at n2
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg a) two_ne_zero).1 n2

end GlobalTheory.VacUnique

end
