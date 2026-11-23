import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DropPlInsert
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalVAlgebraMapMem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSameImagesMatrix
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitFrameSelfDualLatticeCompletion
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLatticeIffIntegralMatrixSplitChart
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHyperspecialIffGIntOfSuppAtSplit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FockVectorsChainIsVacuumOffThetaLevels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionLiftPairStepVectorInvLevelChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHomLatticeMultipleMemOpenLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHomLatticeFinitelyGenerated

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

noncomputable section

namespace GlobalTheory.DownLift.SplitGen

variable {D : D7}

abbrev lat0 (S T : HSp D) : AddSubgroup (WO S T) := latO S T (L0c D S) (L0c D T) fun _ => True

def InvForm (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D) (ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ u : WO S T, IsHalf (cA D e) u → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f

def HalfVac (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D) (f : WO S T → ℂ) : Prop :=
  IsThetaFunO ψ S T f ∧ ∀ u ∈ lat0 S T, IsHalf e u ∨ IsHalf (cA D e) u → heisO ψ S T u f = f

def locSpan (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D) (f : WO S T → ℂ) : Submodule ℂ (WO S T → ℂ) :=
  Submodule.span ℂ {φ | ∃ u : WO S T, IsHalf (e + cA D e) u ∧ φ = heisO ψ S T u f}

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {e : AE D}

theorem isHalf_place_left (he : IsSplitIdem D e) {u : WO S T} (hu : IsHalf e u) : IsHalf (e + cA D e) u := fun i j => by
  rw [← hu i j, ← mul_assoc, add_mul, he.1, mul_comm (cA D e) e, he.2.1, add_zero]

theorem isHalf_place_right (he : IsSplitIdem D e) {u : WO S T} (hu : IsHalf (cA D e) u) : IsHalf (e + cA D e) u := by
  have := isHalf_place_left (GlobalTheory.SplitScalar.isSplitIdem_conj he) hu
  rwa [GlobalTheory.DualPairCheck.cA_cA, add_comm] at this

theorem place_fin (he : IsSplitIdem D e) {u : WO S T} (hu : IsHalf (e + cA D e) u) : u.map (infPart D) = 0 := by
  ext i j
  show infPart D (u i j) = 0
  rw [← hu i j, RingHom.map_mul, RingHom.map_add, GlobalTheory.SplitScalar.infPart_splitIdem he,
    GlobalTheory.SplitScalar.infPart_splitIdem (GlobalTheory.SplitScalar.isSplitIdem_conj he), add_zero, zero_mul]

theorem theta_heis (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {u : WO S T}
    (hu : u.map (infPart D) = 0) : IsThetaFunO ψ S T (heisO ψ S T u f) := by
  have := GlobalTheory.FinTranslate.isTheta_sum_heisO_fin D ψ S T hψ.1 f hf Unit {()} (fun _ => u) (fun _ => 1) fun _ _ => hu
  rwa [Finset.sum_singleton, one_smul] at this

theorem theta_of_mem_locSpan (hψ : IsStdChar D ψ (-1)) (he : IsSplitIdem D e) {f φ : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hφ : φ ∈ locSpan ψ S T e f) : IsThetaFunO ψ S T φ := by
  induction hφ using Submodule.span_induction with
  | mem x hx => obtain ⟨u, hu, rfl⟩ := hx; exact theta_heis hψ hf (place_fin he hu)
  | zero => simpa using theta_smul (0 : ℂ) hf
  | add x y _ _ hx hy => exact theta_add hx hy
  | smul c x _ hx => exact theta_smul c hx

theorem self_mem_locSpan (f : WO S T → ℂ) : f ∈ locSpan ψ S T e f :=
  Submodule.subset_span ⟨0, GlobalTheory.SplitScalar.isHalf_zero _, (GlobalTheory.SplitScalar.heisO_zero ψ S T f).symm⟩

theorem heis_mem_locSpan {f φ : WO S T → ℂ} (hφ : φ ∈ locSpan ψ S T e f) {u : WO S T} (hu : IsHalf (e + cA D e) u) :
    heisO ψ S T u φ ∈ locSpan ψ S T e f := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    rw [GlobalTheory.SplitScalar.heisO_heisO]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, GlobalTheory.SplitScalar.isHalf_add hu hw, rfl⟩)
  | zero => rw [← GlobalTheory.SplitScalar.heisL_apply, map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [heisO_add']; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [GlobalTheory.SplitScalar.heisO_smul]; exact Submodule.smul_mem _ _ hx

theorem locSpan_trans {f g φ : WO S T → ℂ} (hg : g ∈ locSpan ψ S T e f) (hφ : φ ∈ locSpan ψ S T e g) :
    φ ∈ locSpan ψ S T e f :=
  (Submodule.span_le.2 (by rintro _ ⟨u, hu, rfl⟩; exact heis_mem_locSpan hg hu) :
    locSpan ψ S T e g ≤ locSpan ψ S T e f) hφ

theorem lat_facts (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (he : IsSplitIdem D e) :
    (∀ u ∈ lat0 S T, e • u ∈ lat0 S T) ∧
    (∀ x ∈ lat0 S T, IsHalf e x → ∀ y ∈ lat0 S T, IsHalf (cA D e) y → ψ (symplO S T x y) = 1) ∧
    (∀ y, IsHalf (cA D e) y → (∀ x ∈ lat0 S T, IsHalf e x → ψ (symplO S T x y) = 1) → y ∈ lat0 S T) ∧
    (∀ x, IsHalf e x → (∀ y ∈ lat0 S T, IsHalf (cA D e) y → ψ (symplO S T x y) = 1) → x ∈ lat0 S T) ∧
    (∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), ∀ u ∈ lat0 S T, IsHalf e u →
      ∃ r ∈ R, ∃ v ∈ lat0 S T, IsHalf e v ∧ u = r + k • v) ∧
    (∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), ∀ u ∈ lat0 S T, IsHalf (cA D e) u →
      ∃ r ∈ R, ∃ v ∈ lat0 S T, IsHalf (cA D e) v ∧ u = r + k • v) := by
  have he' := GlobalTheory.SplitScalar.isSplitIdem_conj he
  have hcc := GlobalTheory.DualPairCheck.cA_cA (D := D) e
  have hS := GlobalTheory.PlaceModel.isSelfDualC_latFrame S
  have hT := GlobalTheory.PlaceModel.isSelfDualC_latFrame T
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hfin := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg (fun _ => True)
  rw [GlobalTheory.PlaceModel.coe_latFrame, GlobalTheory.PlaceModel.coe_latFrame] at hdual hfin
  have hst : ∀ {a : AE D}, a * a = a → ∀ u ∈ lat0 S T, a • u ∈ lat0 S T := fun ha =>
    GlobalTheory.SplitScalar.idem_smul_mem ha
  have key : ∀ {a : AE D}, a * a = a → ∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), ∀ u ∈ lat0 S T, IsHalf a u →
      ∃ r ∈ R, ∃ v ∈ lat0 S T, IsHalf a v ∧ u = r + k • v := fun {a} ha k hk => by
    obtain ⟨R, hR, h⟩ := hfin k hk
    refine ⟨(hR.image fun r => a • r).toFinset, fun u hu hu' => ?_⟩
    obtain ⟨r, hr, w, hw, h'⟩ := h u hu
    refine ⟨_, (Set.Finite.mem_toFinset _).2 ⟨r, hr, rfl⟩, a • w, hst ha w hw, GlobalTheory.SplitScalar.isHalf_smul ha w, ?_⟩
    rw [← (GlobalTheory.SplitScalar.isHalf_iff _ _).1 hu', h', smul_add, smul_comm a k w]
  refine ⟨hst he.1, fun x hx _ y hy _ => (hdual x (GlobalTheory.SplitScalar.latO_fin hx)).1 hx y hy, fun y hy h => ?_,
    fun x hx h => ?_, key he.1, key he'.1⟩
  · by_contra hn
    obtain ⟨l, hl, hl', hne⟩ := GlobalTheory.SplitScalar.exists_dual_half he' hdual (by rw [hcc]; exact hst he.1) hy hn
    exact hne (h l hl (by rwa [hcc] at hl'))
  · by_contra hn
    obtain ⟨l, hl, hl', hne⟩ := GlobalTheory.SplitScalar.exists_dual_half he hdual (hst he'.1) hx hn
    exact GlobalTheory.SplitScalar.psi_skew_ne hne (h l hl hl')

theorem lat_level (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    ∃ k : ℕ, 0 < k ∧ ∀ u ∈ lat0 S T, heisO ψ S T (k • u) f = f := by
  have hS := GlobalTheory.PlaceModel.isSelfDualC_latFrame S
  have hT := GlobalTheory.PlaceModel.isSelfDualC_latFrame T
  obtain ⟨U, hU, hUf⟩ := hf.level
  obtain ⟨k, hk, h⟩ := (GlobalTheory.LatLevel.level_of_generators D S T _ _ hS hT (GlobalTheory.LatFinGen.latO_finitely_generated D S T _ _ hS hT)).1 U hU
  rw [GlobalTheory.PlaceModel.coe_latFrame, GlobalTheory.PlaceModel.coe_latFrame] at h
  exact ⟨k, hk, fun u hu => hUf _ (h u hu) (GlobalTheory.SplitScalar.latO_fin (nsmul_mem hu k))⟩

theorem invForm_heis_vac (hψ : IsStdChar D ψ (-1)) (he : IsSplitIdem D e) {ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ}
    (hℓ : InvForm ψ S T e ℓ) {φ : WO S T → ℂ} (hφ : HalfVac ψ S T e φ) {x : WO S T} (hx : IsHalf e x)
    (hn : x ∉ lat0 S T) : ℓ (heisO ψ S T x φ) = 0 := by
  obtain ⟨-, -, -, h4, -⟩ := lat_facts hψ S T he
  by_contra h0
  refine hn (h4 x hx fun y hy hy' => ?_)
  have h2 := hℓ y hy' _ (theta_heis hψ hφ.1 (GlobalTheory.SplitScalar.half_fin he hx))
  rw [GlobalTheory.SplitScalar.heisO_comm, hφ.2 y hy (Or.inr hy'), map_smul, smul_eq_mul] at h2
  have h3 : ψ (symplO S T y x) = 1 := mul_right_cancel₀ h0 (by rw [h2, one_mul])
  by_contra h5
  exact GlobalTheory.SplitScalar.psi_skew_ne h5 h3

theorem exists_invForm (hψ : IsStdChar D ψ (-1)) (he : IsSplitIdem D e) {φ : WO S T → ℂ} (hφ : HalfVac ψ S T e φ)
    (h0 : φ ≠ 0) : ∃ ℓ, InvForm ψ S T e ℓ ∧ ℓ φ ≠ 0 := by
  obtain ⟨-, -, h3, -⟩ := lat_facts hψ S T he
  obtain ⟨ℓ, h1, h2⟩ := GlobalTheory.SplitHecke.exists_invariant_form' (Λ := lat0 S T) (ψ := ψ)
    (GlobalTheory.SplitScalar.isSplitIdem_conj he) (fun y hy hn => by
      rw [GlobalTheory.DualPairCheck.cA_cA]
      by_contra hc
      push_neg at hc
      exact hn (h3 y hy hc)) h0 (fun u hu hh => hφ.2 u hu (Or.inr hh))
    (fun u hu hh => hφ.2 u hu (Or.inl (by rwa [GlobalTheory.DualPairCheck.cA_cA] at hh)))
  exact ⟨ℓ, h2, h1⟩

theorem splitHalf_coordinate_source_matrix_identity {K : Type} [Field K] {a b : ℕ} (c : K) (B : Matrix (Fin b) (Fin b) K) (C G k : Matrix (Fin a) (Fin a) K)
    (m : Matrix (Fin a) (Fin b) K) (h : C * G = kᵀ * C) :
    (1 : Matrix (Fin b) (Fin b) K) * (c • (B * mᵀ * C)) * G = c • (B * (k * m)ᵀ * C) := by
  rw [Matrix.one_mul, Matrix.smul_mul, Matrix.mul_assoc _ C, h, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

theorem coord_tgt {K : Type} [Field K] {a b : ℕ} (c : K) (B H g : Matrix (Fin b) (Fin b) K) (C : Matrix (Fin a) (Fin a) K)
    (m : Matrix (Fin a) (Fin b) K) (h : H * B = B * gᵀ) : H * (c • (B * mᵀ * C)) * (1 : Matrix (Fin a) (Fin a) K) = c • (B * (m * g)ᵀ * C) := by
  rw [Matrix.mul_one, Matrix.mul_smul, Matrix.transpose_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h]
  simp only [Matrix.mul_assoc]

open GlobalTheory.SplitHecke GlobalTheory.SplitLinear in

theorem exists_coord (S T : HSp D) (he : IsSplitIdem D e) :
    ∃ (v : HeightOneSpectrum (𝓞 D.host.F)) (τ : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v) →+ WO S T),
      (∀ m, IsHalf e (τ m)) ∧ (∀ x, IsHalf e x → ∃ m, τ m = x) ∧
      (∀ m, τ m ∈ lat0 S T ↔ ∃ z : Matrix (Fin S.rank) (Fin T.rank) (Ov D v), m = z.map (algebraMap (Ov D v) (Fv D.host.F v))) ∧
      (∀ k : GL (Fin S.rank) (Ov D v), ∃ g : GA D S, SuppAt e S g ∧ g ∈ KsphC S ∅ ∧
        ∀ m : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v), actO S T g⁻¹ 1⁻¹ (τ m) =
          τ ((((k : Matrix (Fin S.rank) (Fin S.rank) (Ov D v)).map (algebraMap (Ov D v) (Fv D.host.F v)) :
            Matrix (Fin S.rank) (Fin S.rank) (Fv D.host.F v)) * m : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v))))  ∧
      ∀ γ : GL (Fin T.rank) (Fv D.host.F v), ∃ h : GA D T, SuppAt e T h ∧
        ∀ m : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v), actO S T 1⁻¹ h⁻¹ (τ m) =
          τ (m * (γ : Matrix (Fin T.rank) (Fin T.rank) (Fv D.host.F v)) :
            Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v)) := by
  obtain ⟨v, π, hπ⟩ := GlobalTheory.SplitChart.exists_chart e he
  obtain ⟨βS, hS⟩ := GlobalTheory.SplitFrame.exists_frame e v π he hπ S
  obtain ⟨βT, hT⟩ := GlobalTheory.SplitFrame.exists_frame e v π he hπ T
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.SplitHomLattice.mem_latO_iff_intM e v π he hπ S T βS βT hS hT
  obtain ⟨σ, q1, q2⟩ := exists_section (S := S) (T := T) he.1 hπ
  let A : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v) →+ Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v) :=
    AddMonoidHom.mk' (fun m => c⁻¹ • (βT.1 * mᵀ * (βS⁻¹).1)) fun a b => by
      rw [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul, smul_add]
  have hA : ∀ m, A m = c⁻¹ • (βT.1 * mᵀ * (βS⁻¹).1) := fun _ => rfl
  have one : ∀ V : HSp D, (mt V 1).map π = 1 := fun V => by
    rw [GlobalTheory.AdelicLatMove.mt_one, Matrix.map_one _ π.map_zero π.map_one]
  refine ⟨v, σ.comp A, fun m => q2 _, fun x hx => ⟨(c • ((βT⁻¹).1 * Matrix.map x π * βS.1))ᵀ, ?_⟩, fun m => ?_,
    fun k => ?_, fun γ => ?_⟩
  · refine chart_inj hπ (q2 _) hx ?_
    rw [AddMonoidHom.comp_apply, q1, hA, Matrix.transpose_transpose, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
      inv_mul_cancel₀ hc0, one_smul]
    simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  · have e1 : c • ((βT⁻¹).1 * A m * βS.1) = mᵀ := by
      rw [hA, Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hc0, one_smul]
      simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
      rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [AddMonoidHom.comp_apply, hc _ (q2 _), q1, e1]
    refine ⟨fun h => ?_, ?_⟩
    · obtain ⟨z, hz⟩ := intM_iff.1 h.transpose
      exact ⟨z, hz.symm⟩
    · rintro ⟨z, rfl⟩
      exact (intM_iff.2 ⟨z, rfl⟩).transpose
  · let k' : GL (Fin S.rank) (Fv D.host.F v) :=
      ⟨((k : Matrix _ _ (Ov D v)).map (algebraMap (Ov D v) (Fv D.host.F v)))ᵀ,
        (((k⁻¹ : GL _ _) : Matrix _ _ (Ov D v)).map (algebraMap (Ov D v) (Fv D.host.F v)))ᵀ,
        by rw [← Matrix.transpose_mul, ← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _),
          Matrix.transpose_one],
        by rw [← Matrix.transpose_mul, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _),
          Matrix.transpose_one]⟩
    obtain ⟨g, hg, hρ⟩ := GlobalTheory.SplitOnto.exists_suppAt_rho_eq e v π he hπ S βS k'
    refine ⟨g, hg, (GlobalTheory.SplitHecke.Stab.mem_KsphC_iff_gInt e v π he hπ S βS hS g hg).2 (by
      rw [hρ]
      exact ⟨(intM_iff.2 ⟨_, rfl⟩).transpose, (intM_iff.2 ⟨_, rfl⟩).transpose⟩), fun m => ?_⟩
    have e1 : (βS⁻¹).1 * (mt S g).map π = k'.1 * (βS⁻¹).1 := by
      rw [← hρ, rho_val, Matrix.mul_assoc _ βS.1, Units.mul_inv, Matrix.mul_one]
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, section_act hπ q1 q2, inv_one, one]
    exact congrArg σ (splitHalf_coordinate_source_matrix_identity _ _ _ _ _ m e1)
  · let γ' : GL (Fin T.rank) (Fv D.host.F v) :=
      ⟨γ.1ᵀ, (γ⁻¹).1ᵀ, by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one],
        by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]⟩
    obtain ⟨h, hh, hρ⟩ := GlobalTheory.SplitOnto.exists_suppAt_rho_eq e v π he hπ T βT γ'
    refine ⟨h⁻¹, suppAt_of (GlobalTheory.SplitScalar.off_smul_mt_inv hh), fun m => ?_⟩
    have e1 : (mt T h).map π * βT.1 = βT.1 * γ'.1 := by
      rw [← hρ, rho_val, Matrix.mul_assoc (βT⁻¹).1, ← Matrix.mul_assoc βT.1, Units.mul_inv, Matrix.one_mul]
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, section_act hπ q1 q2, inv_inv, one]
    exact congrArg σ (coord_tgt _ _ _ _ _ m e1)

section Average

open GlobalTheory.SplitScalar

theorem exists_reps {G : Type} [AddCommGroup G] (A : AddSubgroup G) (p : G → Prop) (R₀ : Finset G)
    (h : ∀ u, p u → ∃ r ∈ R₀, u - r ∈ A) : ∃ R : Finset G, (∀ u ∈ R, p u) ∧ ∀ u, p u → ∃! v, v ∈ R ∧ u - v ∈ A := by
  classical
  let s : G ⧸ A → G := fun q => if hq : ∃ u, p u ∧ (u : G ⧸ A) = q then hq.choose else 0
  have hs : ∀ q, (∃ u, p u ∧ (u : G ⧸ A) = q) → p (s q) ∧ (s q : G ⧸ A) = q := fun q hq => by
    simp only [s, dif_pos hq]
    exact hq.choose_spec
  refine ⟨((R₀.image fun r : G => (QuotientAddGroup.mk r : G ⧸ A)).filter fun q => ∃ u, p u ∧ (u : G ⧸ A) = q).image s, fun u hu => ?_,
    fun u hu => ⟨s u, ⟨?_, ?_⟩, ?_⟩⟩
  · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hu
    exact (hs q (Finset.mem_filter.1 hq).2).1
  · obtain ⟨r, hr, hur⟩ := h u hu
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.2
      ⟨Finset.mem_image.2 ⟨r, hr, (QuotientAddGroup.eq_iff_sub_mem.2 hur).symm⟩, u, hu, rfl⟩)
  · exact QuotientAddGroup.eq_iff_sub_mem.1 (hs _ ⟨u, hu, rfl⟩).2.symm
  · rintro w ⟨hw, huw⟩
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hw
    rw [QuotientAddGroup.eq_iff_sub_mem.2 huw, (hs q (Finset.mem_filter.1 hq).2).2]

def invNat (D : D7) (k : ℕ) : AE D := incA D ((k : D.host.E)⁻¹)

theorem cA_invNat (k : ℕ) : cA D (invNat D k) = invNat D k := by
  rw [invNat, GlobalTheory.DualPairCheck.cA_incA, star_inv₀, star_natCast]

theorem nsmul_invNat {k : ℕ} (hk : 0 < k) (u : WO S T) : k • invNat D k • u = u := by
  rw [← Nat.cast_smul_eq_nsmul (AE D), smul_smul, invNat, ← map_natCast (incA D), ← map_mul,
    mul_inv_cancel₀ (Nat.cast_ne_zero.2 hk.ne'), map_one, one_smul]

theorem invNat_nsmul {k : ℕ} (hk : 0 < k) (u : WO S T) : invNat D k • k • u = u := by
  rw [smul_comm, nsmul_invNat hk]

theorem isHalf_mul {a : AE D} (b : AE D) {u : WO S T} (hu : IsHalf a u) : IsHalf a (b • u) := by
  rw [isHalf_iff] at *
  rw [smul_comm, hu]

theorem sympl_invNat (k : ℕ) (x y : WO S T) : symplO S T (invNat D k • x) y = symplO S T x (invNat D k • y) := by
  rw [symplO_smul, cA_invNat]

def latUp (S T : HSp D) (k : ℕ) : AddSubgroup (WO S T) := (lat0 S T).comap (nsmulAddMonoidHom k)

def latDown (S T : HSp D) (k : ℕ) : AddSubgroup (WO S T) := (lat0 S T).comap (DistribSMul.toAddMonoidHom _ (invNat D k))

theorem mem_latUp {k : ℕ} {u : WO S T} : u ∈ latUp S T k ↔ k • u ∈ lat0 S T := Iff.rfl

theorem mem_latDown {k : ℕ} {u : WO S T} : u ∈ latDown S T k ↔ invNat D k • u ∈ lat0 S T := Iff.rfl

theorem sympl_down_up {k : ℕ} (hk : 0 < k) (x y : WO S T) : symplO S T x y = symplO S T (invNat D k • x) (k • y) := by
  rw [sympl_invNat, invNat_nsmul hk]

theorem psi_flip {x y : WO S T} (h : ψ (symplO S T x y) = 1) : ψ (symplO S T y x) = 1 := by
  by_contra h'
  exact psi_skew_ne h' h

theorem psi_down_up (hψ : IsStdChar D ψ (-1)) (he : IsSplitIdem D e) {k : ℕ} (hk : 0 < k) {x y : WO S T}
    (hx : x ∈ latDown S T k) (hx' : IsHalf e x) (hy : y ∈ latUp S T k) (hy' : IsHalf (cA D e) y) :
    ψ (symplO S T x y) = 1 := by
  rw [sympl_down_up hk]
  exact (lat_facts hψ S T he).2.1 _ hx (isHalf_mul _ hx') _ hy (isHalf_nsmul hy' k)

theorem exists_dual_up (hψ : IsStdChar D ψ (-1)) (he : IsSplitIdem D e) {k : ℕ} (hk : 0 < k) {x : WO S T}
    (hx : x ∉ latDown S T k) (hx' : IsHalf e x) :
    ∃ y ∈ latUp S T k, IsHalf (cA D e) y ∧ ψ (symplO S T x y) ≠ 1 := by
  by_contra hc
  push Not at hc
  refine hx (mem_latDown.2 ((lat_facts hψ S T he).2.2.2.1 _ (isHalf_mul _ hx') fun y hy hy' => ?_))
  rw [sympl_invNat]
  exact hc _ (by rwa [mem_latUp, nsmul_invNat hk]) (isHalf_mul _ hy')

theorem reps_up (hψ : IsStdChar D ψ (-1)) (he : IsSplitIdem D e) {k : ℕ} (hk : 0 < k) :
    ∃ R : Finset (WO S T), (∀ u ∈ R, u ∈ latUp S T k ∧ IsHalf (cA D e) u) ∧
      ∀ u ∈ latUp S T k, IsHalf (cA D e) u → ∃! v, v ∈ R ∧ u - v ∈ latDown S T k := by
  classical
  obtain ⟨R₀, h₀⟩ := (lat_facts hψ S T he).2.2.2.2.2 (k * k) (Nat.mul_pos hk hk)
  obtain ⟨R, h1, h2⟩ := exists_reps (latDown S T k) (fun u => u ∈ latUp S T k ∧ IsHalf (cA D e) u)
    (R₀.image fun r => invNat D k • r) fun u hu => by
      obtain ⟨r, hr, w, hw, -, h⟩ := h₀ _ (mem_latUp.1 hu.1) (isHalf_nsmul hu.2 k)
      refine ⟨_, Finset.mem_image_of_mem _ hr, ?_⟩
      have : u - invNat D k • r = k • w := by
        rw [← invNat_nsmul hk u, h, smul_add, add_sub_cancel_left, mul_smul, invNat_nsmul hk]
      rwa [this, mem_latDown, invNat_nsmul hk]
  exact ⟨R, h1, fun u hu hu' => h2 u ⟨hu, hu'⟩⟩

theorem reps_lat (hψ : IsStdChar D ψ (-1)) (he : IsSplitIdem D e) {k : ℕ} (hk : 0 < k) :
    ∃ R : Finset (WO S T), (∀ u ∈ R, u ∈ lat0 S T ∧ IsHalf e u) ∧
      ∀ u ∈ lat0 S T, IsHalf e u → ∃! v, v ∈ R ∧ u - v ∈ latDown S T k := by
  obtain ⟨R₀, h₀⟩ := (lat_facts hψ S T he).2.2.2.2.1 k hk
  obtain ⟨R, h1, h2⟩ := exists_reps (latDown S T k) (fun u => u ∈ lat0 S T ∧ IsHalf e u) R₀ fun u hu => by
      obtain ⟨r, hr, w, hw, -, h⟩ := h₀ _ hu.1 hu.2
      refine ⟨_, hr, ?_⟩
      rwa [h, add_sub_cancel_left, mem_latDown, invNat_nsmul hk]
  exact ⟨R, h1, fun u hu hu' => h2 u ⟨hu, hu'⟩⟩

theorem level_down (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    ∃ k : ℕ, 0 < k ∧ ∀ u ∈ latDown S T k, heisO ψ S T u f = f := by
  obtain ⟨k, hk, h⟩ := lat_level hψ hf
  exact ⟨k, hk, fun u hu => by
    have := h _ (mem_latDown.1 hu)
    rwa [nsmul_invNat hk] at this⟩

theorem sum_up (hψ : IsStdChar D ψ (-1)) (he : IsSplitIdem D e) {k : ℕ} (hk : 0 < k) {R : Finset (WO S T)}
    (hR : ∀ u ∈ R, u ∈ latUp S T k ∧ IsHalf (cA D e) u)
    (hR' : ∀ u ∈ latUp S T k, IsHalf (cA D e) u → ∃! v, v ∈ R ∧ u - v ∈ latDown S T k) {g : WO S T → ℂ}
    (hg : IsThetaFunO ψ S T g) (hfix : ∀ u ∈ latDown S T k, IsHalf e u ∨ IsHalf (cA D e) u → heisO ψ S T u g = g) :
    IsThetaFunO ψ S T (∑ u ∈ R, heisO ψ S T u g) ∧
      (∀ a ∈ latUp S T k, IsHalf (cA D e) a → heisO ψ S T a (∑ u ∈ R, heisO ψ S T u g) = ∑ u ∈ R, heisO ψ S T u g) ∧
      (∀ a ∈ latDown S T k, IsHalf e a → heisO ψ S T a (∑ u ∈ R, heisO ψ S T u g) = ∑ u ∈ R, heisO ψ S T u g) ∧
      ∀ ℓ, InvForm ψ S T e ℓ → ℓ (∑ u ∈ R, heisO ψ S T u g) = R.card * ℓ g := by
  have he' := isSplitIdem_conj he
  refine ⟨theta_sum _ _ g hg fun u hu => theta_heis hψ hg (half_fin he' (hR u hu).2),
    fun a ha ha' => sum_reps_invariant he' hR hR' (fun d hd _ hd' => hfix d hd (Or.inr hd')) ha ha',
    fun a ha ha' => ?_, fun ℓ hℓ => ?_⟩
  · rw [heisO_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [heisO_comm, psi_down_up hψ he hk ha ha' (hR u hu).1 (hR u hu).2, one_smul, hfix a ha (Or.inl ha')]
  · rw [map_sum, Finset.sum_congr rfl fun u hu => hℓ u (hR u hu).2 g hg, Finset.sum_const, nsmul_eq_mul]

theorem exists_vac (hψ : IsStdChar D ψ (-1)) (he : IsSplitIdem D e) {h : WO S T → ℂ} (hh : IsThetaFunO ψ S T h) :
    ∃ φ ∈ locSpan ψ S T e h, HalfVac ψ S T e φ ∧ ∀ ℓ, InvForm ψ S T e ℓ → ℓ φ = ℓ h := by
  obtain ⟨k, hk, hfix⟩ := level_down hψ hh
  obtain ⟨R', hR', hRu'⟩ := reps_up (S := S) (T := T) hψ he hk
  obtain ⟨R, hR, hRu⟩ := reps_lat (S := S) (T := T) hψ he hk
  obtain ⟨t1, t2, t3, t4⟩ := sum_up hψ he hk hR' hRu' hh fun u hu _ => hfix u hu
  have m1 : (∑ u ∈ R', heisO ψ S T u h) ∈ locSpan ψ S T e h := Submodule.sum_mem _ fun u hu =>
    heis_mem_locSpan (self_mem_locSpan h) (isHalf_place_right he (hR' u hu).2)
  generalize (∑ u ∈ R', heisO ψ S T u h) = g at t1 t2 t3 t4 m1
  have m2 : (∑ u ∈ R, heisO ψ S T u g) ∈ locSpan ψ S T e h := Submodule.sum_mem _ fun u hu =>
    heis_mem_locSpan m1 (isHalf_place_left he (hR u hu).2)
  have hc : (R'.card : ℂ) ≠ 0 := by
    obtain ⟨v, hv, -⟩ := hRu' 0 (zero_mem _) (isHalf_zero _)
    exact Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨v, hv.1⟩)
  refine ⟨(R'.card : ℂ)⁻¹ • ∑ u ∈ R, heisO ψ S T u g, Submodule.smul_mem _ _ m2,
    ⟨theta_smul _ (theta_of_mem_locSpan hψ he hh m2), fun a ha ha' => ?_⟩, fun ℓ hℓ => ?_⟩
  · rw [heisO_smul]
    congr 1
    rcases ha' with ha' | ha'
    · exact sum_reps_invariant he hR hRu (fun d hd _ hd' => t3 d hd hd') ha ha'
    · rw [heisO_sum]
      refine Finset.sum_congr rfl fun u hu => ?_
      rw [heisO_comm, psi_flip ((lat_facts hψ S T he).2.1 u (hR u hu).1 (hR u hu).2 a ha ha'), one_smul,
        t2 a (nsmul_mem ha k) ha']
  · obtain ⟨v₀, ⟨hv₀, hv₀'⟩, hu₀⟩ := hRu 0 (zero_mem _) (isHalf_zero _)
    rw [zero_sub, neg_mem_iff] at hv₀'
    rw [map_smul, map_sum, Finset.sum_eq_single_of_mem v₀ hv₀, t3 v₀ hv₀' (hR _ hv₀).2, t4 ℓ hℓ, smul_eq_mul,
      inv_mul_cancel_left₀ hc]
    intro u hu hne
    obtain ⟨y, hy, hy', hψy⟩ := exists_dual_up hψ he hk
      (fun hd => hne (hu₀ u ⟨hu, by rwa [zero_sub, neg_mem_iff]⟩)) (hR u hu).2
    have h2 := hℓ y hy' _ (theta_heis hψ t1 (half_fin he (hR u hu).2))
    rw [heisO_comm, t2 y hy hy', map_smul, smul_eq_mul] at h2
    by_contra h0
    exact psi_skew_ne hψy (mul_right_cancel₀ h0 (by rw [h2, one_mul]))

theorem eq_zero_of_invForm (hψ : IsStdChar D ψ (-1)) (he : IsSplitIdem D e) {h : WO S T → ℂ}
    (hh : IsThetaFunO ψ S T h) (h0 : ∀ ℓ, InvForm ψ S T e ℓ → ∀ x, IsHalf e x → ℓ (heisO ψ S T x h) = 0) : h = 0 := by
  have he' := isSplitIdem_conj he
  have hcc := GlobalTheory.DualPairCheck.cA_cA (D := D) e
  obtain ⟨k, hk, hfix⟩ := level_down hψ hh
  obtain ⟨R, hR, hRu⟩ := reps_up (S := S) (T := T) hψ he hk
  have key : ∀ b ∈ latUp S T k, IsHalf e b → ∑ u ∈ R, heisO ψ S T u (heisO ψ S T b h) = 0 := by
    intro b hb hb'
    obtain ⟨t1, t2, t3, t4⟩ := sum_up hψ he hk hR hRu (theta_heis hψ hh (half_fin he hb')) fun u hu hu' => by
      rw [heisO_comm, hfix u hu]
      rcases hu' with hu' | hu'
      · rw [half_orth he hu' hb', AddChar.map_zero_eq_one, one_smul]
      · rw [psi_down_up hψ he' hk hu hu' hb (by rwa [hcc]), one_smul]
    by_contra hne
    obtain ⟨ℓ, h1, h2⟩ := GlobalTheory.SplitHecke.exists_invariant_form'
      (Λ := (latDown S T k).comap (DistribSMul.toAddMonoidHom _ e) ⊓ (latUp S T k).comap (DistribSMul.toAddMonoidHom _ (cA D e)))
      (ψ := ψ) he' (fun y hy hn => by
        have e1 : cA D e • y = y := (isHalf_iff _ _).1 hy
        have e2 : e • y = 0 := by rw [← e1, smul_smul, he.2.1, zero_smul]
        have hn' : k • y ∉ lat0 S T := fun hm => hn ⟨by
          show e • y ∈ latDown S T k
          rw [e2]; exact zero_mem _, by
          show cA D e • y ∈ latUp S T k
          rw [e1]; exact hm⟩
        rw [hcc]
        by_contra hc
        push Not at hc
        refine hn' ((lat_facts hψ S T he).2.2.1 _ (isHalf_nsmul hy k) fun x hx hx' => ?_)
        have e3 : e • k • x = k • x := (isHalf_iff _ _).1 (isHalf_nsmul hx' k)
        have := hc (k • x) ⟨by
          show e • k • x ∈ latDown S T k
          rw [e3, mem_latDown, invNat_nsmul hk]; exact hx, by
          show cA D e • k • x ∈ latUp S T k
          rw [← e3, smul_smul, mul_comm, he.2.1, zero_smul]; exact zero_mem _⟩ (isHalf_nsmul hx' k)
        rwa [sympl_down_up hk, invNat_nsmul hk] at this) hne
      (fun u hu hh => t2 u (by
        have : cA D e • u ∈ latUp S T k := hu.2
        rwa [(isHalf_iff _ _).1 hh] at this) hh)
      (fun u hu hh => by
        rw [hcc] at hh
        refine t3 u ?_ hh
        have : e • u ∈ latDown S T k := hu.1
        rwa [(isHalf_iff _ _).1 hh] at this)
    exact h1 (by rw [t4 ℓ h2, h0 ℓ h2 b hb', mul_zero])
  let B : AddSubgroup (WO S T) := latUp S T k ⊓ GlobalTheory.PlaceModel.half S T e
  let χ : WO S T → (Multiplicative B →* ℂ) := fun y =>
    { toFun := fun b => ψ (symplO S T y (b.toAdd : B))
      map_one' := by simp [symplO_zero_right]
      map_mul' := fun a b => by
        simp only [toAdd_mul, AddSubgroup.coe_add, GlobalTheory.LatVac.symplO_add_right, AddChar.map_add_eq_mul] }
  have inj : Function.Injective fun y : R => χ y := by
    rintro ⟨y, hy⟩ ⟨y', hy'⟩ hyy
    refine Subtype.ext ((hRu y (hR y hy).1 (hR y hy).2).unique ⟨hy, by rw [sub_self]; exact zero_mem _⟩ ⟨hy', ?_⟩)
    by_contra hn
    obtain ⟨b, hb, hb', hne⟩ := exists_dual_up hψ he' hk hn (isHalf_sub (hR y hy).2 (hR y' hy').2)
    rw [hcc] at hb'
    have := DFunLike.congr_fun hyy (Multiplicative.ofAdd ⟨b, hb, (GlobalTheory.PlaceModel.isHalf_iff S T).1 hb'⟩)
    change ψ (symplO S T y b) = ψ (symplO S T y' b) at this
    apply hne
    rw [symplO_sub_left, sub_eq_add_neg, AddChar.map_add_eq_mul, this, ← AddChar.map_add_eq_mul, add_neg_cancel,
      AddChar.map_zero_eq_one]
  have li := (linearIndependent_monoidHom (Multiplicative B) ℂ).comp _ inj
  obtain ⟨y₀, ⟨hy₀, hy₀'⟩, -⟩ := hRu 0 (zero_mem _) (isHalf_zero _)
  rw [zero_sub, neg_mem_iff] at hy₀'
  funext w
  have := Fintype.linearIndependent_iff.1 li (fun y => heisO ψ S T y h w) (funext fun b => by
    have hb : IsHalf e (b.toAdd : B).1 := (GlobalTheory.PlaceModel.isHalf_iff S T).2 (b.toAdd : B).2.2
    have h1 := key _ (b.toAdd : B).2.1 hb
    rw [Finset.sum_apply]
    change ∑ y : R, heisO ψ S T y h w * ψ (symplO S T y (b.toAdd : B).1) = 0
    generalize (b.toAdd : B).1 = x at hb h1
    have hx : symplO S T (-x) x = 0 := half_orth he (by simpa using isHalf_sub (isHalf_zero e) hb) hb
    have h3 : ∀ u, heisO ψ S T (-x) (heisO ψ S T u (heisO ψ S T x h)) = ψ (symplO S T u x) • heisO ψ S T u h := fun u => by
      rw [heisO_comm _ _ _ u, heisO_smul, ← heisO_add_of_orth ψ S T hx, neg_add_cancel, heisO_zero]
    have h4 := congrArg (heisO ψ S T (-x)) h1
    rw [heisO_sum, ← heisL_apply _ _ _ _ 0, map_zero, Finset.sum_congr rfl fun u _ => h3 u] at h4
    have h2 := congrFun h4 w
    rw [Finset.sum_apply, ← Finset.sum_coe_sort] at h2
    exact (Finset.sum_congr rfl fun y _ => mul_comm _ _).trans h2) ⟨y₀, hy₀⟩
  rwa [hfix y₀ hy₀'] at this

end Average

section Generation

open GlobalTheory.SplitScalar

variable {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem invForm_om (hW : IsWeilDatumO ψ S T χS χT om) (he : IsSplitIdem D e) {g : GA D S} {h : GA D T} (hg : SuppAt e S g)
    (hh : SuppAt e T h) : ∃ c : ℂ, c ≠ 0 ∧ ∀ ℓ, InvForm ψ S T e ℓ → ∀ φ, IsThetaFunO ψ S T φ → ∀ x, IsHalf e x →
      ℓ (heisO ψ S T x (om (g, h) φ)) = c * ℓ (heisO ψ S T (actO S T g⁻¹ h⁻¹ x) φ) := by
  obtain ⟨r, hr, H⟩ := hW.om_split e he g h hg hh _ _ (GlobalTheory.VecInv.isDetAt_detAt e he.1 S g)
    (GlobalTheory.VecInv.isDetAt_detAt e he.1 T h)
  refine ⟨_, mul_ne_zero (Complex.ofReal_ne_zero.2 hr.ne') (Circle.coe_ne_zero (splitFacO χS χT
    (GlobalTheory.VecInv.detAt e he.1 S g) (GlobalTheory.VecInv.detAt e he.1 T h))), fun ℓ hℓ φ hφ x hx => ?_⟩
  rw [← H ℓ hℓ _ (theta_heis hW.std hφ (half_fin he (GlobalTheory.SplitHecke.isHalf_actO _ _ hx))), hW.om_heis g h _ _ hφ,
    GlobalTheory.AdelicLatMove.actO_actO_inv]

def vacGen (ψ : AddChar (AF D.host.F) ℂ) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (e : AE D)
    (f : WO S T → ℂ) : Set (WO S T → ℂ) :=
  {F | ∃ (h : GA D T) (φ : WO S T → ℂ), φ ∈ locSpan ψ S T e f ∧ HalfVac ψ S T e φ ∧ F = om (1, h) φ}

open GlobalTheory.SplitHecke in

theorem mem_span_vacGen (hW : IsWeilDatumO ψ S T χS χT om) (hr : T.rank ≤ S.rank) (he : IsSplitIdem D e)
    {f₀ f : WO S T → ℂ} (hf₀ : HalfVac ψ S T e f₀) (h0 : f₀ ≠ 0) (hf : IsThetaFunO ψ S T f)
    (hK : ∀ g, SuppAt e S g → g ∈ KsphC S ∅ → om (g, 1) f = f ∧ om (g, 1) f₀ = f₀) :
    f ∈ Submodule.span ℂ (vacGen ψ om e f) := by
  classical
  have hψ := hW.std
  obtain ⟨v, τ, c1, c2, c3, c4, c5⟩ := exists_coord S T he
  haveI : Finite (IsLocalRing.ResidueField (Ov D v)) := Formalism.UG.P.glint_finite_residueField v
  let M : {ℓ // InvForm ψ S T e ℓ} → (WO S T → ℂ) →ₗ[ℂ] (Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v) → ℂ) :=
    fun ℓ => LinearMap.pi fun m => ℓ.1 ∘ₗ heisL ψ S T (τ m)
  have hM : ∀ ℓ φ m, M ℓ φ m = ℓ.1 (heisO ψ S T (τ m) φ) := fun _ _ _ => rfl
  obtain ⟨k, hk, hfix⟩ := lat_level hψ hf
  have hk0 : (k : Ov D v) ≠ 0 := fun h => by
    have h1 := congrArg (algebraMap (Ov D v) (Fv D.host.F v)) h
    rw [map_natCast, map_zero, ← map_natCast (algebraMap D.host.F (Fv D.host.F v)),
      map_eq_zero_iff _ (algebraMap D.host.F (Fv D.host.F v)).injective] at h1
    exact hk.ne' (Nat.cast_eq_zero.1 h1)
  obtain ⟨ℓ₀, hℓ₀, hne⟩ := exists_invForm hψ he hf₀ h0
  suffices key : ∃ F ∈ Submodule.span ℂ (vacGen ψ om e f), ∀ ℓ, M ℓ F = M ℓ f by
    obtain ⟨F, hF, hMF⟩ := key
    have hFθ : IsThetaFunO ψ S T F := by
      clear hMF
      induction hF using Submodule.span_induction with
      | mem x hx => obtain ⟨h, φ, -, hφ, rfl⟩ := hx; exact hW.om_pres _ _ hφ.1
      | zero => simpa using theta_smul (0 : ℂ) hf
      | add x y _ _ hx hy => exact theta_add hx hy
      | smul c x _ hx => exact theta_smul c hx
    have : F - f = 0 := eq_zero_of_invForm hψ he (theta_sub hFθ hf) fun ℓ hℓ x hx => by
      obtain ⟨m, rfl⟩ := c2 x hx
      rw [← hM ⟨ℓ, hℓ⟩, map_sub, hMF, sub_self, Pi.zero_apply]
    exact (sub_eq_zero.1 this).subst (motive := fun x => x ∈ Submodule.span ℂ (vacGen ψ om e f)) hF
  refine exists_same_images_matrix hr hk0 M f (Submodule.span ℂ (vacGen ψ om e f))
    (fun ℓ => ⟨fun x z => ?_, fun x hx => ?_, fun κ x => ?_⟩) fun z γ => ?_
  · have e1 : ((k : Ov D v) • z).map (algebraMap (Ov D v) (Fv D.host.F v)) =
        k • z.map (algebraMap (Ov D v) (Fv D.host.F v)) := by
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_natCast, nsmul_eq_mul]
    rw [hM, hM, e1, map_add, map_nsmul, heisO_add_of_orth ψ S T (half_orth he (c1 _) (isHalf_nsmul (c1 _) k)),
      hfix _ ((c3 _).2 ⟨z, rfl⟩)]
  · rw [map_natCast, Nat.cast_smul_eq_nsmul, ← c3, map_nsmul]
    refine (lat_facts hψ S T he).2.2.2.1 _ (isHalf_nsmul (c1 x) k) fun y hy hy' => ?_
    have h2 := ℓ.2 _ (isHalf_nsmul hy' k) _ (theta_heis hψ hf (half_fin he (c1 x)))
    rw [heisO_comm, hfix y hy, map_smul, smul_eq_mul] at h2
    have h3 := psi_flip (mul_right_cancel₀ hx (h2.trans (one_mul _).symm))
    rwa [← invNat_nsmul hk (τ x), ← sympl_down_up hk] at h3
  · obtain ⟨g, g1, g2, g3⟩ := c4 κ
    obtain ⟨c, -, hc⟩ := invForm_om hW he g1 (GlobalTheory.SplitLinear.suppAt_one e T)
    have h1 := hc ℓ₀ hℓ₀ f₀ hf₀.1 (τ 0) (c1 0)
    rw [g3, Matrix.mul_zero, map_zero, (hK g g1 g2).2, heisO_zero] at h1
    have h2 := hc ℓ.1 ℓ.2 f hf (τ x) (c1 x)
    rw [g3, (hK g g1 g2).1, ← mul_right_cancel₀ hne ((one_mul _).trans h1), one_mul] at h2
    exact h2.symm
  · obtain ⟨h, h1, h2⟩ := c5 γ
    obtain ⟨c, hc0, hc⟩ := invForm_om hW he (GlobalTheory.SplitLinear.suppAt_one e S) h1
    obtain ⟨φ, p1, p2, p3⟩ := exists_vac hψ he (theta_heis hψ hf (half_fin he (c1 z)))
    refine ⟨c⁻¹ • om (1, h) φ, Submodule.smul_mem _ _ (Submodule.subset_span ⟨h, φ, locSpan_trans
      (heis_mem_locSpan (self_mem_locSpan f) (isHalf_place_left he (c1 z))) p1, p2, rfl⟩), fun ℓ => funext fun m => ?_⟩
    rw [map_smul, Pi.smul_apply, hM, hc ℓ.1 ℓ.2 φ p2.1 _ (c1 m), h2, smul_eq_mul, inv_mul_cancel_left₀ hc0, Pi.smul_apply,
      hM, smul_eq_mul]
    by_cases hm : τ (m * (γ : Matrix (Fin T.rank) (Fin T.rank) (Fv D.host.F v)) :
        Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v)) ∈ lat0 S T
    · rw [Set.indicator_of_mem (by exact (c3 _).1 hm), mul_one, p2.2 _ hm (Or.inl (c1 _)), p3 ℓ.1 ℓ.2]
    · rw [Set.indicator_of_notMem (by exact fun h' => hm ((c3 _).2 h')), mul_zero, invForm_heis_vac hψ he ℓ.2 p2 (c1 _) hm]

end Generation

section Transfer

open GlobalTheory.SplitScalar

variable {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem cA_place (e : AE D) : cA D (e + cA D e) = e + cA D e := by
  rw [RingHom.map_add, GlobalTheory.DualPairCheck.cA_cA, add_comm]

theorem kill_locSpan {f φ : WO S T → ℂ} (L : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ))
    (hL : ∀ u, IsHalf (e + cA D e) u → L (heisO ψ S T u f) = heisO ψ S T u (L f)) (h0 : L f = 0)
    (hφ : φ ∈ locSpan ψ S T e f) : L φ = 0 := by
  refine (Submodule.span_le.2 ?_ : locSpan ψ S T e f ≤ LinearMap.ker L) hφ
  rintro _ ⟨u, hu, rfl⟩
  show L _ = 0
  rw [hL u hu, h0, ← heisL_apply, map_zero]

theorem actO_off {a : AE D} {κ : GA D S} (hκ : a • mt S κ⁻¹ = a • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)))
    {u : WO S T} (hu : IsHalf a u) : actO S T κ 1 u = u := by
  rw [actO, GlobalTheory.AdelicLatMove.mt_one, Matrix.one_mul, ← (isHalf_iff _ _).1 hu, Matrix.smul_mul, ← Matrix.mul_smul, hκ,
    Matrix.mul_smul, Matrix.mul_one]

theorem off_inv {a : AE D} {κ : GA D S} (hκ : a • mt S κ = a • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D))) :
    a • mt S κ⁻¹ = a • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := by
  have := congrArg (· * mt S κ⁻¹) hκ
  simp only [Matrix.smul_mul, Matrix.one_mul] at this
  rw [← this, ← GlobalTheory.AdelicLatMove.mt_mul, mul_inv_cancel, GlobalTheory.AdelicLatMove.mt_one]

theorem invForm_heis_heis (hψ : IsStdChar D ψ (-1)) (he : IsSplitIdem D e) {x u : WO S T} (hx : IsHalf e x)
    (hu : IsHalf (e + cA D e) u) : ∃ c : ℂ, ∀ ℓ, InvForm ψ S T e ℓ → ∀ φ, HalfVac ψ S T e φ →
      ℓ (heisO ψ S T x (heisO ψ S T u φ)) = c * ℓ φ := by
  classical
  have h1 : IsHalf e (x + e • u) := isHalf_add hx (isHalf_smul he.1 u)
  have h2 : IsHalf (cA D e) (cA D e • u) := isHalf_smul (isSplitIdem_conj he).1 u
  have h3 : x + u = cA D e • u + (x + e • u) := by
    rw [add_left_comm, ← add_smul, add_comm (cA D e), (isHalf_iff _ _).1 hu]
  refine ⟨ψ (symplOH S T x u) * ψ (-symplOH S T (cA D e • u) (x + e • u)) * if x + e • u ∈ lat0 S T then 1 else 0,
    fun ℓ hℓ φ hφ => ?_⟩
  have h4 := hℓ _ h2 _ (theta_heis hψ hφ.1 (half_fin he h1))
  rw [heisO_heisO, ← h3, map_smul, smul_eq_mul] at h4
  have h5 : ℓ (heisO ψ S T (x + u) φ) = ψ (-symplOH S T (cA D e • u) (x + e • u)) * ℓ (heisO ψ S T (x + e • u) φ) := by
    rw [← h4, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]
  rw [heisO_heisO, map_smul, smul_eq_mul, h5]
  split_ifs with hm
  · rw [hφ.2 _ hm (Or.inl h1)]; ring
  · rw [invForm_heis_vac hψ he hℓ hφ h1 hm]; ring

theorem halfVac_heis_off (hψ : IsStdChar D ψ (-1)) (he : IsSplitIdem D e) {φ : WO S T → ℂ} (hφ : HalfVac ψ S T e φ)
    {w : WO S T} (hw : w.map (infPart D) = 0) (hw' : ∀ i j, (e + cA D e) * w i j = 0) :
    HalfVac ψ S T e (heisO ψ S T w φ) :=
  ⟨theta_heis hψ hφ.1 hw, fun u hu hu' => by
    rw [← GlobalTheory.Hk3.heisO_comm_off ψ S T (hu'.elim (isHalf_place_left he) (isHalf_place_right he))
      (by rwa [cA_place]), hφ.2 u hu hu']⟩

theorem halfVac_sum {ι : Type} (s : Finset ι) (a : ι → ℂ) {φ : ι → WO S T → ℂ} {f₀ : WO S T → ℂ}
    (h₀ : IsThetaFunO ψ S T f₀) (hφ : ∀ i ∈ s, HalfVac ψ S T e (φ i)) : HalfVac ψ S T e (∑ i ∈ s, a i • φ i) :=
  ⟨theta_sum _ _ f₀ h₀ fun i hi => theta_smul _ (hφ i hi).1, fun u hu hu' => by
    rw [heisO_sum]
    exact Finset.sum_congr rfl fun i hi => by rw [heisO_smul, (hφ i hi).2 u hu hu']⟩

theorem relation_vac (hψ : IsStdChar D ψ (-1)) (he : IsSplitIdem D e) {f₀ φ : WO S T → ℂ} (hf₀ : HalfVac ψ S T e f₀)
    (hφ : HalfVac ψ S T e φ) {ι : Type} (s : Finset ι) (u w : ι → WO S T) (hu : ∀ i ∈ s, IsHalf (e + cA D e) (u i))
    (hw : ∀ i ∈ s, (w i).map (infPart D) = 0 ∧ ∀ a b, (e + cA D e) * w i a b = 0)
    (hrel : ∀ a : ι → ℂ, ∑ i ∈ s, a i • heisO ψ S T (w i) f₀ = 0 → ∑ i ∈ s, a i • heisO ψ S T (w i) φ = 0)
    (a : ι → ℂ) (h : ∑ i ∈ s, a i • heisO ψ S T (u i) (heisO ψ S T (w i) f₀) = 0) :
    ∑ i ∈ s, a i • heisO ψ S T (u i) (heisO ψ S T (w i) φ) = 0 := by
  have v : ∀ {g}, HalfVac ψ S T e g → ∀ i ∈ s, HalfVac ψ S T e (heisO ψ S T (w i) g) := fun hg i hi =>
    halfVac_heis_off hψ he hg (hw i hi).1 (hw i hi).2
  refine eq_zero_of_invForm hψ he (theta_sum _ _ φ hφ.1 fun i hi =>
    theta_smul _ (theta_heis hψ (v hφ i hi).1 (place_fin he (hu i hi)))) fun ℓ hℓ x hx => ?_
  choose! c hc using fun i hi => invForm_heis_heis hψ he hx (hu i hi)
  have key : ∀ ℓ, InvForm ψ S T e ℓ → ∀ {g}, HalfVac ψ S T e g →
      ℓ (heisO ψ S T x (∑ i ∈ s, a i • heisO ψ S T (u i) (heisO ψ S T (w i) g))) =
        ℓ (∑ i ∈ s, (a i * c i) • heisO ψ S T (w i) g) := fun ℓ hℓ g hg => by
    rw [heisO_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [heisO_smul, map_smul, map_smul, hc i hi ℓ hℓ _ (v hg i hi), smul_eq_mul, smul_eq_mul, mul_assoc]
  rw [key ℓ hℓ hφ, hrel, map_zero]
  by_contra hne
  obtain ⟨ℓ', h1, h2⟩ := exists_invForm hψ he (halfVac_sum s _ hf₀.1 (v hf₀)) hne
  apply h2
  rw [← key ℓ' h1 hf₀, h, ← heisL_apply, map_zero, map_zero]

end Transfer

theorem rel_of_finsupp {X V ι : Type} [AddCommGroup V] [Module ℂ V] (p : X → Prop) (F G : X → V)
    (H : ∀ c : X →₀ ℂ, (∀ u ∈ c.support, p u) → (c.sum fun u z => z • F u) = 0 → (c.sum fun u z => z • G u) = 0)
    (s : Finset ι) (a : ι → ℂ) (w : ι → X) (hw : ∀ i ∈ s, p (w i)) (h : ∑ i ∈ s, a i • F (w i) = 0) :
    ∑ i ∈ s, a i • G (w i) = 0 := by
  classical
  have hc : ∀ K : X → V, ((∑ i ∈ s, Finsupp.single (w i) (a i)).sum fun u z => z • K u) = ∑ i ∈ s, a i • K (w i) :=
    fun K => by
      rw [← Finsupp.linearCombination_apply, map_sum]
      simp only [Finsupp.linearCombination_single]
  rw [← hc]
  refine H _ (fun u hu => ?_) (by rw [hc, h])
  obtain ⟨i, hi, h⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum hu)
  rw [Finset.mem_singleton.1 (Finsupp.support_single_subset h)]
  exact hw i hi

section Real

open GlobalTheory.SplitScalar

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m} {t : T}
  {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))} {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F}

theorem mem_dropPl {w : HeightOneSpectrum (𝓞 D.host.F)} : w ∈ dropPl Sb v ↔ w ≠ v ∧ w ∈ Sb := by
  unfold dropPl
  convert Finset.mem_erase

theorem suppIn_of_drop {V : HSp D} {g : GA D V} (h : SuppIn (dropPl Sb v) V g) : SuppIn Sb V g :=
  ⟨h.1, fun w hw => h.2 w fun h' => hw (mem_dropPl.1 h').2⟩

theorem smul_mt_of_drop (hε : IsPlaceIdem D v ε) (hee : e + cA D e = algebraMap (AF D.host.F) (AE D) ε) {V : HSp D}
    {g : GA D V} (h : SuppIn (dropPl Sb v) V g) :
    (e + cA D e) • mt V g = (e + cA D e) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  rw [← sub_eq_zero, ← smul_sub, hee]
  ext a b
  exact h.2 v (fun h' => (mem_dropPl.1 h').1 rfl) ε hε a b

theorem typeIn_drop (hW : R.thP_ωP) (he : IsSplitIdem D e) (hε : IsPlaceIdem D v ε)
    (hee : e + cA D e = algebraMap (AF D.host.F) (AE D) ε) {f φ : WO (Vc D i) (Wc D i) → ℂ} (hf : TypeIn R i t Sb f)
    (hφ : φ ∈ locSpan R.ψ _ _ e f) : TypeIn R i t (dropPl Sb v) φ := by
  refine ⟨theta_of_mem_locSpan (hW i t).std he hf.1 hφ, fun κ hκ hs => ?_⟩
  rw [← sub_eq_zero]
  refine kill_locSpan (R.ωP i t (κ, 1) - (levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹ • LinearMap.id) (fun u hu => ?_)
    (sub_eq_zero.2 (hf.2 κ hκ (suppIn_of_drop hs))) hφ
  rw [LinearMap.sub_apply, LinearMap.sub_apply, (hW i t).om_heis κ 1 u f hf.1,
    actO_off (off_inv (smul_mt_of_drop hε hee hs)) hu, ← heisL_apply _ _ _ _ (_ - _), map_sub]
  simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul, heisL_apply]

theorem cleanIn_drop (hW : R.thP_ωP) (hε : IsPlaceIdem D v ε)
    (hee : e + cA D e = algebraMap (AF D.host.F) (AE D) ε) {f φ : WO (Vc D i) (Wc D i) → ℂ}
    (hθ : IsThetaFunO R.ψ _ _ f) (hf : CleanIn R i t Sb f) (hφ : φ ∈ locSpan R.ψ _ _ e f) :
    CleanIn R i t (dropPl Sb v) φ := by
  rintro PP a ha tr s hs ⟨w, hw, hw'⟩ κ hκ hsupp
  let L : Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ) :=
    ∑ g, (mirC R i PP a tr s g * (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ g))⁻¹) • R.ωP i t ((κ g)⁻¹, 1)
  have hL : ∀ x, L x = avgW R i t PP a tr s κ x := fun x => by
    simp only [L, avgW, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [← hL]
  refine kill_locSpan L (fun u hu => ?_) ((hL f).trans
    (hf PP a ha tr s hs ⟨w, (mem_dropPl.1 hw).2, hw'⟩ κ hκ fun g hg => suppIn_of_drop (hsupp g hg))) hφ
  rw [hL, hL, avgW, avgW, heisO_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [heisO_smul]
  by_cases hg : mirC R i PP a tr s g = 0
  · rw [hg, zero_mul, zero_smul, zero_smul]
  · rw [(hW i t).om_heis _ 1 u f hθ, actO_off (by rw [inv_inv]; exact smul_mt_of_drop hε hee (hsupp g hg)) hu]

theorem relation_drop {ψ : AddChar (AF D.host.F) ℂ} {S T' : HSp D} (hψ : IsStdChar D ψ (-1)) (he : IsSplitIdem D e)
    (hε : IsPlaceIdem D v ε) (hee : e + cA D e = algebraMap (AF D.host.F) (AE D) ε) {f₀ f φ : WO S T' → ℂ}
    (h₀ : HalfVac ψ S T' e f₀)
    (hf : ∀ c : WO S T' →₀ ℂ, (∀ u ∈ c.support, OffPl Sb u) → (c.sum fun u z => z • heisO ψ S T' u f₀) = 0 →
      (c.sum fun u z => z • heisO ψ S T' u f) = 0)
    (hφ : φ ∈ locSpan ψ S T' e f) (hφ' : HalfVac ψ S T' e φ) (c : WO S T' →₀ ℂ)
    (hc : ∀ u ∈ c.support, OffPl (dropPl Sb v) u) (h : (c.sum fun u z => z • heisO ψ S T' u f₀) = 0) :
    (c.sum fun u z => z • heisO ψ S T' u φ) = 0 := by
  have hp : (e + cA D e) * (e + cA D e) = e + cA D e := by
    rw [add_mul, mul_add, mul_add, he.1, he.2.1, mul_comm (cA D e) e, he.2.1, (isSplitIdem_conj he).1, add_zero, zero_add]
  have hu : ∀ u : WO S T', IsHalf (e + cA D e) ((e + cA D e) • u) := isHalf_smul hp
  have hz : ∀ (u : WO S T') a b, (e + cA D e) * (u - (e + cA D e) • u) a b = 0 := fun u a b => by
    rw [Matrix.sub_apply, mul_sub, hu u a b, Matrix.smul_apply, smul_eq_mul, sub_self]
  have hoff : ∀ u ∈ c.support, OffPl Sb (u - (e + cA D e) • u) := fun u hu' => by
    refine ⟨?_, fun w hw ε' hε' a b => ?_⟩
    · ext a b
      have h1 : infPart D (u a b) = 0 := congrFun (congrFun (hc u hu').1 a) b
      show infPart D (u a b - (e + cA D e) * u a b) = 0
      rw [RingHom.map_sub, RingHom.map_mul, h1, mul_zero, sub_self]
    · by_cases hwv : w = v
      · have h1 : ε' = ε := GlobalTheory.IdemSupport.placeIdem_unique hε' (hwv ▸ hε)
        exact (congrArg (· * _) ((congrArg _ h1).trans hee.symm)).trans (hz u a b)
      · have h1 := (hc u hu').2 w (mem_dropPl.2 ⟨hwv, hw⟩) ε' hε' a b
        show algebraMap (AF D.host.F) (AE D) ε' * (u a b - (e + cA D e) * u a b) = 0
        linear_combination (1 - (e + cA D e)) * h1
  have hsplit : ∀ (u : WO S T') g, heisO ψ S T' u g =
      heisO ψ S T' ((e + cA D e) • u) (heisO ψ S T' (u - (e + cA D e) • u) g) := fun u g => by
    rw [← heisO_add_of_orth _ _ _ (GlobalTheory.Hk3.symplO_half_off _ _ (hu u) (by rw [cA_place]; exact hz u)), add_sub_cancel]
  have hs : ∀ g, (c.sum fun u z => z • heisO ψ S T' u g) = ∑ u ∈ c.support,
      c u • heisO ψ S T' ((e + cA D e) • u) (heisO ψ S T' (u - (e + cA D e) • u) g) := fun g =>
    Finset.sum_congr rfl fun u _ => congrArg (c u • ·) (hsplit u g)
  refine (hs φ).trans (relation_vac hψ he h₀ hφ' c.support (fun u => (e + cA D e) • u) (fun u => u - (e + cA D e) • u)
    (fun u _ => hu u) (fun u hu' => ⟨(hoff u hu').1, hz u⟩) (fun a ha => ?_) c ((hs f₀).symm.trans h))
  have h1 := rel_of_finsupp (OffPl Sb) (fun u => heisO ψ S T' u f₀) (fun u => heisO ψ S T' u f) hf c.support a
    (fun u => u - (e + cA D e) • u) hoff ha
  let L : Module.End ℂ (WO S T' → ℂ) := ∑ u ∈ c.support, a u • heisL ψ S T' (u - (e + cA D e) • u)
  have hL : ∀ x, L x = ∑ u ∈ c.support, a u • heisO ψ S T' (u - (e + cA D e) • u) x := fun x => by
    simp only [L, LinearMap.sum_apply, LinearMap.smul_apply, heisL_apply]
  refine (hL φ).symm.trans (kill_locSpan L (fun w hw => ?_) ((hL f).trans h1) hφ)
  rw [hL, hL, heisO_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [heisO_smul]
  exact congrArg (a u • ·) (GlobalTheory.Hk3.heisO_comm_off ψ S T' (u := u - (e + cA D e) • u) hw
    (by rw [cA_place]; exact hz u) f)

theorem likeOff_drop (hψ : IsStdChar D R.ψ (-1)) (he : IsSplitIdem D e) (hε : IsPlaceIdem D v ε)
    (hee : e + cA D e = algebraMap (AF D.host.F) (AE D) ε) (h₀ : HalfVac R.ψ _ _ e (R.vP i t))
    {f φ : WO (Vc D i) (Wc D i) → ℂ} (hf : LikeOff R i t Sb f) (hφ : φ ∈ locSpan R.ψ _ _ e f)
    (hφ' : HalfVac R.ψ _ _ e φ) : LikeOff R i t (dropPl Sb v) φ :=
  ⟨hφ'.1, relation_drop hψ he hε hee h₀ hf.2 hφ hφ'⟩

theorem place_eq (he : IsSplitIdem D e) (hε : IsPlaceIdem D v ε) (hne : e * algebraMap (AF D.host.F) (AE D) ε ≠ 0) :
    e + cA D e = algebraMap (AF D.host.F) (AE D) ε := by
  obtain ⟨h1, h2, w, ε', hε', h3⟩ := he
  by_cases hw : w = v
  · subst hw
    rw [h3, GlobalTheory.IdemSupport.placeIdem_unique hε' hε]
  · refine absurd ?_ hne
    have : e = e * algebraMap (AF D.host.F) (AE D) ε' := by rw [← h3, mul_add, h1, h2, add_zero]
    rw [this, mul_assoc, ← map_mul, GlobalTheory.PlaceDatum.placeIdem_mul hε' hε hw, map_zero, mul_zero]

theorem suppIn_of_suppAt (he : IsSplitIdem D e) (hε : IsPlaceIdem D v ε)
    (hee : e + cA D e = algebraMap (AF D.host.F) (AE D) ε) (hv : v ∈ Sb) {V : HSp D} {g : GA D V} (hg : SuppAt e V g) :
    SuppIn Sb V g :=
  ⟨place_fin (S := V) (T := V) he hg, fun w hw ε' hε' a b => by
    rw [← hg a b, hee, ← mul_assoc, ← map_mul, GlobalTheory.PlaceDatum.placeIdem_mul hε' hε (fun h => hw (h ▸ hv)), map_zero,
      zero_mul]⟩

theorem off_levels {F : Face D A} (hC : GlobalTheory.Hk3.Core R F) (he : IsSplitIdem D e) (hε : IsPlaceIdem D v ε)
    (hee : e + cA D e = algebraMap (AF D.host.F) (AE D) ε) (hoff : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ¬ Over PP v) :
    HalfVac R.ψ _ _ e (R.vP i t) ∧ ∀ κ, SuppAt e (Vc D i) κ → κ ∈ KsphC (Vc D i) ∅ →
      κ ∈ levG (Vc D i) (R.βV i) (R.datVt i t) ∧ levChi (Vc D i) (R.βV i) (R.datVt i t) κ = 1 ∧
        R.ωP i t (κ, 1) (R.vP i t) = R.vP i t := by
  obtain ⟨w, hw⟩ := (GlobalTheory.IdemModTwo.isSplitIdem_iff e).1 he
  obtain ⟨P, hP, -⟩ := GlobalTheory.IdemPrime.exists_isIdemAt D w e hw
  have hI : IsPrimeIdem P e (e + cA D e) := Or.inl ⟨hP, rfl⟩
  have hPv : P.under (𝓞 D.host.F) = v := by
    obtain ⟨w', ε', hε', hf', hw'⟩ := GlobalTheory.VacLat.place_of_primeIdem hI
    by_contra hne
    have h1 := GlobalTheory.PlaceDatum.placeIdem_mul hε' hε (fun h => hne (by rw [← h, hw']))
    have h2 : e * (e + cA D e) = e := by rw [mul_add, he.1, he.2.1, add_zero]
    have h3 : (e + cA D e) * (e + cA D e) = 0 := by
      nth_rewrite 1 [hf']
      rw [hee, ← map_mul, h1, map_zero]
    have h4 : e = 0 := by linear_combination e * h3 - (e + cA D e + 1) * h2
    have h5 : algebraMap (AF D.host.F) (AE D) ε = 0 := by rw [← hee, h4, map_zero, add_zero]
    have hinj : Function.Injective (algebraMap (AF D.host.F) (AE D)) :=
      Algebra.TensorProduct.includeLeft_injective (S := D.host.F) (algebraMap D.host.F D.host.E).injective
    obtain ⟨α, rfl, hα, -⟩ := hε
    have h6 : α = 0 := congrArg Prod.snd (hinj (h5.trans (map_zero _).symm))
    rw [h6, map_zero] at hα
    exact zero_ne_one hα
  have hG : GlobalTheory.Hk3.Good R t P := fun PP hPP => by
    refine ⟨fun h => hoff PP hPP ?_, fun h => hoff PP hPP ?_⟩
    · rw [h]
      exact congrArg HeightOneSpectrum.asIdeal hPv
    · rw [(GlobalTheory.IdemSupport.isConjPl_iff _ _).1 h, GlobalTheory.IdemSupport.under_cP] at hPv
      exact congrArg HeightOneSpectrum.asIdeal hPv
  have hvac := (GlobalTheory.VacGood.fock_vacua_good R F hC t P hG).2.2 i 1
  have hone : R.ptP i t 1 = R.vP i t := by
    unfold RealDat.ptP pureTensorO pureTensorL
    have : (1 : MvPolynomial (FVar D (Wc D i).rank (Vc D i).rank) ℂ) = MvPolynomial.basisMonomials _ ℂ 0 := by
      simp
    rw [this, Module.Basis.constr_basis]
    simp [opPow]
  rw [hone] at hvac
  refine ⟨⟨hvac.1, hvac.2 e _ hI⟩, fun κ hκ hK => ?_⟩
  obtain ⟨c, hb⟩ := hC.lev.βV i
  have h1 : ((1 ^ c : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [one_pow, Nat.cast_one]; exact fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have key : ∀ L : LevDat D.host.E ℂ (Vc D i).rank, (∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ∈ R.Pg ∨ PP ∈ R.Q t) →
      κ ∈ levG (Vc D i) (R.βV i) L ∧ levChi (Vc D i) (R.βV i) L κ = 1 := fun L hL => by
    obtain ⟨k1, k2, -⟩ := (GlobalTheory.LevSplit.lev_split _ _ _ _ L hb).2 P e _ hI h1 fun PP h => hG PP (hL PP h)
    exact ⟨(k1 κ hκ).2 hK, k2 κ ((k1 κ hκ).2 hK) hκ⟩
  obtain ⟨a1, a2⟩ := key (R.datVt i t) fun _ h => h
  obtain ⟨hl, -⟩ := key (flag1L (R.datVt i t)) fun _ h => h
  obtain ⟨-, a3⟩ := key (flagL (R.datVt i t)) fun _ h => h
  refine ⟨a1, a2, ?_⟩
  have hκ' : IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) 1 1 :=
    ⟨Subgroup.one_mem _, by rw [map_one]; exact Subgroup.one_mem _, by rw [map_one]; exact Formalism.L2.DIV.rTup_one⟩
  rw [GlobalTheory.VecInv.omega_lifts_vP R hC.lev hC.models.inf hC.thP.ωP hC.thP.vP i t 1 κ 1 ⟨hl.1, hl.2.1, Subgroup.mem_bot.1 hl.2.2⟩ hκ',
    a3, inv_one, one_smul]

end Real

theorem gen_split : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (v : HeightOneSpectrum (𝓞 D.host.F)), v ∈ Sb → (∃ ε e, IsPlaceIdem D v ε ∧ IsSplitIdem D e ∧ e * algebraMap (AF D.host.F) (AE D) ε ≠ 0) → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ¬ GlobalTheory.DownLift.GenFinite.Over PP v) → ∀ (f : WO (Vc D i) (Wc D i) → ℂ), GlobalTheory.DownLift.GenFinite.TypeIn R i t Sb f → GlobalTheory.DownLift.GenFinite.CleanIn R i t Sb f → GlobalTheory.DownLift.GenFinite.LikeOff R i t Sb f → f ∈ Submodule.span ℂ (GlobalTheory.DownLift.GenFinite.StepGen R i t (GlobalTheory.DownLift.GenFinite.dropPl Sb v)) := by
  rintro D G _ _ Pl0 T A Ks _ _ _ R F hG - i t Sb v hv ⟨ε, e, hε, he, hne⟩ hoff f h1 h2 h3
  have hC := hG.core
  have hW := hC.thP.ωP i t
  have hee := place_eq he hε hne
  obtain ⟨hvac, hK⟩ := off_levels (i := i) hC he hε hee hoff
  by_cases h0 : R.vP i t = 0
  · have := h3.2 (Finsupp.single 0 1) (fun u hu => by
      rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hu)]
      exact ⟨Matrix.map_zero _ (map_zero _), fun _ _ _ _ _ _ => mul_zero _⟩) (by
      rw [Finsupp.sum_single_index (by exact zero_smul _ _), one_smul, GlobalTheory.SplitScalar.heisO_zero, h0])
    rw [Finsupp.sum_single_index (by exact zero_smul _ _), one_smul, GlobalTheory.SplitScalar.heisO_zero] at this
    rw [this]
    exact Submodule.zero_mem _
  refine Submodule.span_mono ?_ (mem_span_vacGen hW ((D.sp.W_rank _ (Nat.le_add_left _ _) i.2).le.trans (r_le_V i)) he
    hvac h0 h1.1 fun g hg hg' => ⟨?_, (hK g hg hg').2.2⟩)
  · rintro _ ⟨h, φ, p1, p2, rfl⟩
    exact ⟨h, φ, typeIn_drop hC.thP.ωP he hε hee h1 p1, cleanIn_drop hC.thP.ωP hε hee h1.1 h2 p1,
      likeOff_drop hW.std he hε hee hvac h3 p1 p2, rfl⟩
  · rw [h1.2 g (hK g hg hg').1 (suppIn_of_suppAt he hε hee hv hg), (hK g hg hg').2.1, inv_one, one_smul]

end GlobalTheory.DownLift.SplitGen

end
