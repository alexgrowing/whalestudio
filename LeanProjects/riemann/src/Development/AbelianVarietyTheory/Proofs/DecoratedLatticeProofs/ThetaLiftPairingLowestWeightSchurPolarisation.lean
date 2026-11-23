import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockCoefficientExtremalEqDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaPairingInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanLiftUnitaryGroupProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

namespace GlobalTheory.CoefSchur

theorem sesq_eq_of_diag {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F G : E →ₗ[ℂ] E →ₗ⋆[ℂ] ℂ) (h : ∀ x, F x x = G x x) : F = G := by
  have h0 : ∀ x, (F - G) x x = 0 := fun x => by simp [h x]
  suffices hD : ∀ x y, (F - G) x y = 0 by
    ext x y
    have := hD x y
    simpa [sub_eq_zero] using this
  intro x y
  have h1 := h0 (x + y)
  have h2 := h0 (x + Complex.I • y)
  simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ,
    LinearMap.smul_apply, smul_eq_mul, h0, Complex.conj_I, mul_zero, add_zero, zero_add] at h1 h2
  have hI := Complex.I_sq
  linear_combination (-(Complex.I) / 2 * Complex.I) * h1 + (Complex.I / 2) * h2 + ((F - G) x y) * hI

theorem schur_sesq {G : Type*} [Group G] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [Nontrivial E] (ρ : G →* Module.End ℂ E)
    (hu : ∀ h x y, ⟪ρ h x, ρ h y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hirr : ∀ U : Submodule ℂ E, (∀ h, Submodule.map (ρ h) U ≤ U) → U = ⊥ ∨ U = ⊤)
    (B : E →ₗ[ℂ] E →ₗ⋆[ℂ] ℂ) (hB : ∀ h x y, B (ρ h x) (ρ h y) = B x y) :
    ∃ c : ℂ, ∀ x y, B x y = c * ⟪y, x⟫_ℂ := by
  classical
  let b := stdOrthonormalBasis ℂ E
  let A : E →ₗ[ℂ] E := ∑ i, (B.flip (b i)).smulRight (b i)
  have hA : ∀ x y, B x y = ⟪y, A x⟫_ℂ := by
    intro x y
    conv_lhs => rw [← b.sum_repr' y]
    simp [A, map_sum, inner_sum, inner_smul_right, inner_conj_symm, mul_comm]
  have hcomm : ∀ h x, A (ρ h x) = ρ h (A x) := by
    intro h x
    apply ext_inner_left ℂ
    intro y
    have hy : ρ h (ρ h⁻¹ y) = y := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    calc ⟪y, A (ρ h x)⟫_ℂ = B (ρ h x) y := (hA _ _).symm
      _ = B (ρ h x) (ρ h (ρ h⁻¹ y)) := by rw [hy]
      _ = B x (ρ h⁻¹ y) := hB _ _ _
      _ = ⟪ρ h⁻¹ y, A x⟫_ℂ := hA _ _
      _ = ⟪ρ h (ρ h⁻¹ y), ρ h (A x)⟫_ℂ := (hu _ _ _).symm
      _ = ⟪y, ρ h (A x)⟫_ℂ := by rw [hy]
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue A
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  have hinv : ∀ h, Submodule.map (ρ h) (Module.End.eigenspace A c) ≤ Module.End.eigenspace A c := by
    rintro h _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at hx
    rw [Module.End.mem_eigenspace_iff, hcomm, hx, map_smul]
  have htop : Module.End.eigenspace A c = ⊤ := by
    rcases hirr _ hinv with h | h
    · exfalso
      have hmem : v ∈ Module.End.eigenspace A c := Module.End.mem_eigenspace_iff.mpr hv.apply_eq_smul
      rw [h, Submodule.mem_bot] at hmem
      exact hv.2 hmem
    · exact h
  refine ⟨c, fun x y => ?_⟩
  have hx : x ∈ Module.End.eigenspace A c := htop ▸ Submodule.mem_top
  rw [Module.End.mem_eigenspace_iff] at hx
  rw [hA, hx, inner_smul_right]

end GlobalTheory.CoefSchur

namespace GlobalTheory.CoefSchur

section
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {μ : Measure (WO S T)} {𝓧 : Set (WO S T)}

theorem integrable_mul_conj (hW : IsWeilDatumO ψ S T χS χT om) (hC : IsCovolOne (ratL T S) μ 𝓧)
    {a b : WO S T → ℂ} (ha : IsThetaFunO ψ S T a) (hb : IsThetaFunO ψ S T b) :
    Integrable (fun x => a x * (starRingEnd ℂ) (b x)) (μ.restrict 𝓧) := by
  refine (GlobalTheory.RawLift.FockCoef.integrable_pair hW hC hb ha).congr
    (Filter.Eventually.of_forall fun x => ?_)
  show star (b x) * a x = a x * (starRingEnd ℂ) (b x)
  rw [starRingEnd_apply, mul_comm]

theorem thetaFunctionPairing_weilAction_invariant (hW : IsWeilDatumO ψ S T χS χT om) (hC : IsCovolOne (ratL T S) μ 𝓧)
    (p : GA D S × GA D T) {a b : WO S T → ℂ} (ha : IsThetaFunO ψ S T a)
    (hb : IsThetaFunO ψ S T b) : l2 μ 𝓧 (om p a) (om p b) = l2 μ 𝓧 a b := by
  have key : ∀ f g : WO S T → ℂ, l2 μ 𝓧 f g = GlobalTheory.RawLift.thetaIP μ 𝓧 g f := by
    intro f g
    simp only [l2, Lift.pet, GlobalTheory.RawLift.thetaIP]
    congr 1
    funext x
    rw [starRingEnd_apply, mul_comm]
  rw [key, key, GlobalTheory.WeilPairing.thetaInner_weilRep D ψ S T χS χT om μ 𝓧 hW hC p b a hb ha]

noncomputable def thetaForm (hW : IsWeilDatumO ψ S T χS χT om) (hC : IsCovolOne (ratL T S) μ 𝓧)
    {E : Type*} [AddCommGroup E] [Module ℂ E] (a b : E →ₗ[ℂ] (WO S T → ℂ))
    (ha : ∀ x, IsThetaFunO ψ S T (a x)) (hb : ∀ y, IsThetaFunO ψ S T (b y)) :
    E →ₗ[ℂ] E →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun x y => l2 μ 𝓧 (a x) (b y))
    (fun x x' y => by
      simp only [map_add, l2, Lift.pet, Pi.add_apply, add_mul]
      exact integral_add (integrable_mul_conj hW hC (ha x) (hb y))
        (integrable_mul_conj hW hC (ha x') (hb y)))
    (fun c x y => by
      simp only [map_smul, l2, Lift.pet, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
      exact integral_const_mul c _)
    (fun x y y' => by
      simp only [map_add, l2, Lift.pet, Pi.add_apply, mul_add]
      exact integral_add (integrable_mul_conj hW hC (ha x) (hb y))
        (integrable_mul_conj hW hC (ha x) (hb y')))
    (fun c x y => by
      simp only [map_smul, l2, Lift.pet, Pi.smul_apply, smul_eq_mul, map_mul]
      rw [← integral_const_mul]
      congr 1
      funext z
      ring)

theorem thetaForm_apply (hW : IsWeilDatumO ψ S T χS χT om) (hC : IsCovolOne (ratL T S) μ 𝓧)
    {E : Type*} [AddCommGroup E] [Module ℂ E] (a b : E →ₗ[ℂ] (WO S T → ℂ))
    (ha : ∀ x, IsThetaFunO ψ S T (a x)) (hb : ∀ y, IsThetaFunO ψ S T (b y)) (x y : E) :
    thetaForm hW hC a b ha hb x y = l2 μ 𝓧 (a x) (b y) := rfl

end

end GlobalTheory.CoefSchur

namespace GlobalTheory.CoefSchur

theorem realElt_one {D : D7} (θ : InfFam D) (hθ : IsInfFam θ) (T : HSp D) :
    realElt θ T 1 = 1 := by
  classical
  obtain ⟨L, -, hL2, -, -, -, hLat, -, -⟩ := GlobalTheory.RealLift.exists_real_lift D θ T hθ
  have h1UH : ∀ τ, (1 : Matrix (Fin T.rank) (Fin T.rank) ℂ) ∈ Formalism.QuantumDeterminants.UH (gramAt D T τ) := by
    intro τ; simp [Formalism.QuantumDeterminants.UH]
  have h1UG : (1 : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) ∈ GlobalTheory.HolDict.UG (gramAt D T) :=
    fun τ => h1UH τ
  have hL1 : L 1 = 1 := by
    have := hL2 1 h1UG 1 h1UG
    rw [mul_one] at this
    exact mul_left_cancel (a := L 1) (by rw [mul_one]; exact this.symm)
  have hat : ∀ τ, atTau θ T τ 1 = 1 := by
    intro τ; rw [hLat τ 1 (h1UH τ), Pi.mulSingle_one, hL1]
  simp [realElt, hat]

theorem thetaLiftPairing_lowestWeight_schur_polarisation_alt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsInfFam θ → IsWeilDatumO ψ S T χS χT om → ∀ (Sp : D.what₂.Tau → SPar) (M : DSModel T Sp), ∀ (μ : Measure (WO S T)) (𝓧 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓧 → ∀ c : CoefA S, c.Is → ∀ pt : PolF D T.rank S.rank →ₗ[ℂ] (WO S T → ℂ), (∀ P, IsThetaFunO ψ S T (pt P)) → ∀ (Δ : PolF D T.rank S.rank) (io : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D T.rank S.rank), IsIoW θ M c om (fun P => pt P) Δ io → (∀ w : c.W, ∃ N : ℂ, ∀ g : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ, (∀ ρ, g ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D T ρ)) → ∀ (e e' : ∀ ρ, lowT M ρ), l2 μ 𝓧 (om (1, realElt θ T g) (pt (io (PiTensorProduct.tprod ℂ e) w))) (pt (io (PiTensorProduct.tprod ℂ e') w)) = N * (∏ ρ, ⟪((e' ρ : M.sm ρ) : M.H ρ), M.rep ρ (g ρ) ((e ρ : M.sm ρ) : M.H ρ)⟫_ℂ)) → ∀ g : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ, (∀ ρ, g ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D T ρ)) → ∀ (e e' : ∀ ρ, lowT M ρ) (w w' : c.W), l2 μ 𝓧 (om (1, realElt θ T g) (pt (io (PiTensorProduct.tprod ℂ e) w))) (pt (io (PiTensorProduct.tprod ℂ e') w')) = l2 μ 𝓧 (pt Δ) (pt Δ) * (∏ ρ, ⟪((e' ρ : M.sm ρ) : M.H ρ), M.rep ρ (g ρ) ((e ρ : M.sm ρ) : M.H ρ)⟫_ℂ) * ⟪w', w⟫_ℂ := by
  intro D ψ θ S T χS χT om hθ hW Sp M μ 𝓧 hC c hc pt hpt Δ io hio hN g hg e e' w w'
  obtain ⟨hio1, -, v₀, w₀, hv₀, hw₀, hΔ⟩ := hio
  haveI : Nontrivial c.W := hc.2.2.2.1
  have hr1 := realElt_one θ hθ T
  have hom1 : om (1, realElt θ T 1) = 1 := by rw [hr1]; exact map_one om
  have hth : ∀ p P, IsThetaFunO ψ S T (om p (pt P)) := fun p P => hW.om_pres p _ (hpt P)
  let b₀ : c.W →ₗ[ℂ] (WO S T → ℂ) := pt.comp (io (PiTensorProduct.tprod ℂ v₀))
  let B := thetaForm hW hC b₀ b₀ (fun _ => hpt _) (fun _ => hpt _)
  have hBinf : ∀ u ∈ GinfC S, ∀ x y, B (c.ρ u x) (c.ρ u y) = B x y := by
    intro u hu x y
    have hio1' : ∀ (x : LowT M) (w : c.W), om (u, 1) (pt (io x w)) = pt (io x (c.ρ u w)) := hio1 u hu
    simp only [B, thetaForm_apply, b₀, LinearMap.comp_apply]
    rw [← hio1', ← hio1']
    exact thetaFunctionPairing_weilAction_invariant hW hC _ (hpt _) (hpt _)
  have hBinv : ∀ h x y, B (c.ρ h x) (c.ρ h y) = B x y := by
    intro h x y
    obtain ⟨L, -, -, -, -, -, -, hdec, -⟩ := GlobalTheory.RealLift.exists_real_lift D θ S hθ
    obtain ⟨a, ha, u, hu, rfl⟩ := hdec h
    rw [map_mul, Module.End.mul_apply, Module.End.mul_apply, hc.1 a ha, Module.End.one_apply,
      Module.End.one_apply]
    exact hBinf u hu x y
  obtain ⟨lam, hlam⟩ := schur_sesq c.ρ hc.2.1 hc.2.2.2.2 B hBinv
  have hlam0 : lam = l2 μ 𝓧 (pt Δ) (pt Δ) := by
    have := hlam w₀ w₀
    simp only [B, thetaForm_apply, b₀, LinearMap.comp_apply, hΔ] at this
    rw [this, inner_self_eq_norm_sq_to_K, hw₀]; simp
  have hP0 : ∏ ρ, ⟪((v₀ ρ : M.sm ρ) : M.H ρ), M.rep ρ ((1 : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) ρ) ((v₀ ρ : M.sm ρ) : M.H ρ)⟫_ℂ = 1 := by
    apply Finset.prod_eq_one
    intro ρ _
    have hfr : M.fr ρ * (1 : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) ρ * (M.fr ρ)⁻¹ = 1 := by
      rw [Pi.one_apply, mul_one]
      exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit ρ))
    have hσ : M.σ ρ 1 = 1 := (M.ds ρ).2.2.1.1.1
    rw [DSModel.rep, hfr, hσ, ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K, hv₀ ρ]; simp
  have h1mem : ∀ ρ, (1 : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D T ρ) := by
    intro ρ; simp [Formalism.QuantumDeterminants.UH]
  have hdiag : ∀ x : c.W, ∀ g : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ,
      (∀ ρ, g ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D T ρ)) → ∀ e e' : ∀ ρ, lowT M ρ,
      l2 μ 𝓧 (om (1, realElt θ T g) (pt (io (PiTensorProduct.tprod ℂ e) x)))
        (pt (io (PiTensorProduct.tprod ℂ e') x)) = l2 μ 𝓧 (pt Δ) (pt Δ) *
        (∏ ρ, ⟪((e' ρ : M.sm ρ) : M.H ρ), M.rep ρ (g ρ) ((e ρ : M.sm ρ) : M.H ρ)⟫_ℂ) * ⟪x, x⟫_ℂ := by
    intro x g hg e e'
    obtain ⟨N, hNx⟩ := hN x
    have h1 := hNx 1 h1mem v₀ v₀
    rw [hP0, mul_one, hom1, Module.End.one_apply] at h1
    have hBx : B x x = N := h1
    rw [hlam, hlam0] at hBx
    rw [hNx g hg e e', ← hBx]; ring
  let F : c.W →ₗ[ℂ] c.W →ₗ⋆[ℂ] ℂ := thetaForm hW hC
    ((om (1, realElt θ T g)).comp (pt.comp (io (PiTensorProduct.tprod ℂ e))))
    (pt.comp (io (PiTensorProduct.tprod ℂ e'))) (fun _ => hth _ _) (fun _ => hpt _)
  let G : c.W →ₗ[ℂ] c.W →ₗ⋆[ℂ] ℂ := (l2 μ 𝓧 (pt Δ) (pt Δ) *
    ∏ ρ, ⟪((e' ρ : M.sm ρ) : M.H ρ), M.rep ρ (g ρ) ((e ρ : M.sm ρ) : M.H ρ)⟫_ℂ) • (innerₛₗ ℂ).flip
  have hFG := sesq_eq_of_diag F G (fun x => by
    simp only [F, G, thetaForm_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      LinearMap.flip_apply, smul_eq_mul]
    exact hdiag x g hg e e')
  have := LinearMap.congr_fun₂ hFG w w'
  simp only [F, G, thetaForm_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.flip_apply, smul_eq_mul] at this
  exact this

end GlobalTheory.CoefSchur
