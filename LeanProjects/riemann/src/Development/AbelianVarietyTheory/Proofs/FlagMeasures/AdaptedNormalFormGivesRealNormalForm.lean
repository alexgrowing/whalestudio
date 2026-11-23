import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPointGramMinorsAgreeProof
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesPairingStabilizerBlockDiagonal
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SameBlockAppend
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometryHermFrameUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealMatrixMemBesselUnipotentOfFrameStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelLinearMapMatrixExistsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelHyperbolicBasisScaledStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DualVectorsNormalFormMemSecondFlagStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBlockAntidiagonalScaledPairingMatrixStatement

noncomputable section
open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.L2.SG.KappaOffDiagonal

namespace GlobalTheory.TypeAsm.FramePf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem L_ratIso : ∀ {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) {r : ℕ} (e f e' f' : Fin r → V) (z z' : V),
    (∀ a b, H.B (e a) (e b) = 0) → (∀ a b, H.B (f a) (f b) = 0) →
    (∀ a b, H.B (e a) (f b) = if a = b then 1 else 0) →
    (∀ a, H.B (e a) z = 0) → (∀ a, H.B (f a) z = 0) → H.B z z ≠ 0 →
    (∀ a b, H.B (e' a) (e' b) = 0) → (∀ a b, H.B (f' a) (f' b) = 0) →
    (∀ a b, H.B (e' a) (f' b) = if a = b then 1 else 0) →
    (∀ a, H.B (e' a) z' = 0) → (∀ a, H.B (f' a) z' = 0) →
    (∀ a, e' a - e a ∈ Submodule.span K (e '' {b | b < a})) →
    z' - z ∈ Submodule.span K (Set.range e) →
    ∃ m : V ≃ₗ[K] V, (∀ x y, H.B (m x) (m y) = H.B x y) ∧ (∀ a, m (e' a) = e a) ∧ (∀ a, m (f' a) = f a) ∧
      m z' = z ∧ (∀ a, m (e a) - e a ∈ Submodule.span K (e '' {b | b < a})) ∧
      (∀ y, (∀ a, H.B (e a) y = 0) → m y - y ∈ Submodule.span K (Set.range e)) ∧
      (∀ a, m.symm (e a) - e a ∈ Submodule.span K (e '' {b | b < a})) ∧
      (∀ y, (∀ a, H.B (e a) y = 0) → m.symm y - y ∈ Submodule.span K (Set.range e)) := GlobalTheory.T.exists_isometry_hermFrame_unipotent

theorem L_nset : ∀ {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) {k r : ℕ} (σ : K →+* ℂ) (Φ : V → Fin (2 * r + k + 1) → ℂ),
    GlobalTheory.DegVol.IsReal H k r σ Φ → ∀ (e f : Fin r → V) (ρ ρ' : Fin r → ℂ), (∀ a, ρ a ≠ 0) → (∀ a, ρ' a ≠ 0) →
    (∀ a, Φ (e a) = ρ a • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a)) →
    (∀ a, Φ (f a) = ρ' a • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI k r a)) →
    (∀ a b, H.B (e a) (f b) = if a = b then 1 else 0) →
    ∀ m : V →ₗ[K] V, (∀ x y, H.B (m x) (m y) = H.B x y) →
    (∀ a, m (e a) - e a ∈ Submodule.span K (e '' {b | b < a})) →
    (∀ y, (∀ a, H.B (e a) y = 0) → m y - y ∈ Submodule.span K (Set.range e)) →
    ∀ n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, (∀ y, n *ᵥ Φ y = Φ (m y)) →
    n ∈ Formalism.QuantumDeterminants.Nset k r := GlobalTheory.T.realMatrix_mem_besselUnipotent_of_frame

theorem L_mat : ∀ (D : D7) (X : HidaSetting D) (C : Choice X 1) (τ : D.what₂.Tau) (m : (VS D).V →ₗ[D.host.E] (VS D).V),
    ∃ n : MatKR D.R.k D.R.rS, ∀ y, n *ᵥ GlobalTheory.TypeAsm.phiV C τ y = GlobalTheory.TypeAsm.phiV C τ (m y) := GlobalTheory.T.besselModel_linearMap_matrix_exists

theorem L_frame : ∀ (D : D7) (X : HidaSetting D) (C : Choice X 1) (τ : D.what₂.Tau) (a : Fin D.R.rS),
    GlobalTheory.TypeAsm.phiV C τ (X.eX a) =
                 (((2 * D.host.v) ^ (D.R.rS - a.val) : ℝ) : ℂ) • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) ∧
    GlobalTheory.TypeAsm.phiV C τ (X.fY a) =
                 ((((2 * D.host.v) ^ (D.R.rS - a.val))⁻¹ : ℝ) : ℂ) • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI D.R.k D.R.rS a) := GlobalTheory.T.besselModel_hyperbolicBasis_scaled

theorem L_duals : ∀ {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) {r j : ℕ} (hj : j ≤ r) (e e' s : Fin r → V),
    (Matrix.of fun a b : Fin j => H.B (e (Fin.castLE hj a)) (e' (Fin.castLE hj b))).det ≠ 0 →
    (∀ a b, H.B (e' a) (e' b) = 0) →
    (∀ a b : Fin r, j ≤ a.val → b.val < j → H.B (e a) (e' b) = 0) →
    (∀ a b : Fin r, j ≤ b.val → H.B (e a) (s b) = if a = b then 1 else 0) →
    (∀ a b : Fin r, a.val < j → j ≤ b.val → H.B (e' a) (s b) = 0) →
    (∀ a b : Fin r, j ≤ a.val → j ≤ b.val → H.B (s a) (s b) = 0) →
    ∃ f : Fin r → V, (∀ a, j ≤ a.val → f a = s a) ∧
      (∀ a, a.val < j → f a ∈ Submodule.span K (e' '' {b | b.val < j})) ∧
      (∀ a b, H.B (e a) (f b) = if a = b then 1 else 0) ∧ (∀ a b, H.B (f a) (f b) = 0) ∧
      (∀ a, a.val < j → e' a ∈ Submodule.span K (f '' {b | b.val < j})) := GlobalTheory.T.dualVectors_normalForm_mem_secondFlag

theorem L_block : ∀ {K : Type} [Field K] {j r : ℕ} (hj : j ≤ r) (w : Formalism.MainNotions.S.Loc.Pt K j),
    ∃ β : Fin r → ℕ, Monotone β ∧ (∀ a b : Fin r, j ≤ b.val → (β a = β b ↔ j ≤ a.val)) ∧
      ∀ (σ : K →+* ℂ) (sgn : Fin j → ℤˣ) (ρ : ℝ), 0 < ρ →
      GlobalTheory.Amp.BlockAnti (fun a : Fin j => β (Fin.castLE hj a))
        (Matrix.of fun a b : Fin j => (((ρ ^ (r - b.val))⁻¹ * (ρ ^ (r - a.val))⁻¹ : ℝ) : ℂ) *
          σ (w.mat b a * ((sgn a : ℤ) : K))) := GlobalTheory.T.exists_blockAntidiagonal_scaled_pairing_matrix

theorem herm_eI {k r : ℕ} (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) v (Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a)) = v (Formalism.QuantumDeterminants.esI k r a) := by
  unfold Formalism.QuantumDeterminants.herm Formalism.QuantumDeterminants.bvec
  have hs : star (Pi.single (Formalism.QuantumDeterminants.eI k r a) (1 : ℂ) : Fin (2 * r + k + 1) → ℂ) =
      (Pi.single (Formalism.QuantumDeterminants.eI k r a) (1 : ℂ) : Fin (2 * r + k + 1) → ℂ) := by
    ext j; by_cases h : j = Formalism.QuantumDeterminants.eI k r a <;> simp [Pi.single_apply, h]
  rw [hs, single_one_dotProduct, Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (Formalism.QuantumDeterminants.esI k r a)]
  · simp [Formalism.QuantumDeterminants.Hpk, Formalism.QuantumDeterminants.eI, Formalism.QuantumDeterminants.esI]
    omega
  · intro b _ hb
    have : Formalism.QuantumDeterminants.Hpk k r (Formalism.QuantumDeterminants.eI k r a) b = 0 := by
      unfold Formalism.QuantumDeterminants.Hpk
      have hb' : b.val ≠ 2 * r + k - a.val := fun h => hb (Fin.ext (by simp [Formalism.QuantumDeterminants.esI, h]))
      have ha := a.isLt
      have hbl := b.isLt
      have hv : (Formalism.QuantumDeterminants.eI k r a).val = a.val := rfl
      split_ifs with h1 h2 h3 <;> first | rfl | (exfalso; simp only [hv] at *; omega)
    rw [this, zero_mul]
  · simp

theorem uh_mul {n : ℕ} {H A B : Matrix (Fin n) (Fin n) ℂ} (hA : A ∈ Formalism.QuantumDeterminants.UH H) (hB : B ∈ Formalism.QuantumDeterminants.UH H) :
    A * B ∈ Formalism.QuantumDeterminants.UH H := by
  unfold Formalism.QuantumDeterminants.UH at *
  simp only [Set.mem_setOf_eq] at *
  rw [Matrix.conjTranspose_mul, show Bᴴ * Aᴴ * H * (A * B) = Bᴴ * (Aᴴ * H * A) * B by simp only [Matrix.mul_assoc], hA, hB]

theorem uh_inv {n : ℕ} {H A B : Matrix (Fin n) (Fin n) ℂ} (hA : A ∈ Formalism.QuantumDeterminants.UH H) (hAB : A * B = 1) :
    B ∈ Formalism.QuantumDeterminants.UH H := by
  unfold Formalism.QuantumDeterminants.UH at *
  simp only [Set.mem_setOf_eq] at *
  calc Bᴴ * H * B = Bᴴ * (Aᴴ * H * A) * B := by rw [hA]
    _ = (A * B)ᴴ * H * (A * B) := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = H := by rw [hAB]; simp

theorem mat_ext_of {V : Type} {n : ℕ} (Φ : V → Fin n → ℂ) (hsp : Submodule.span ℂ (Set.range Φ) = ⊤)
    (A B : Matrix (Fin n) (Fin n) ℂ) (h : ∀ y, A *ᵥ Φ y = B *ᵥ Φ y) : A = B := by
  have : Matrix.toLin' A = Matrix.toLin' B := by
    apply LinearMap.ext_on hsp
    rintro _ ⟨y, rfl⟩
    simp only [Matrix.toLin'_apply]
    exact h y
  exact Matrix.toLin'.injective this

theorem span_map_mem {K V : Type} [Field K] [AddCommGroup V] [Module K V] {n : ℕ} (σ : K →+* ℂ)
    (Φ : V → Fin n → ℂ) (hadd : ∀ x y, Φ (x + y) = Φ x + Φ y) (hsm : ∀ (c : K) x, Φ (c • x) = σ c • Φ x)
    (S : Set V) (T : Submodule ℂ (Fin n → ℂ)) (hS : ∀ x ∈ S, Φ x ∈ T) :
    ∀ y ∈ Submodule.span K S, Φ y ∈ T := by
  have h0 : Φ 0 = 0 := by
    have := hsm 0 0
    rw [zero_smul, map_zero, zero_smul] at this
    exact this
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => rw [h0]; exact T.zero_mem
  | add x y _ _ hx hy => rw [hadd]; exact T.add_mem hx hy
  | smul c x _ hx => rw [hsm]; exact T.smul_mem _ hx

theorem herm_smul_l {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (v w : Fin n → ℂ) (α : ℂ) :
    Formalism.QuantumDeterminants.herm H (α • v) w = α * Formalism.QuantumDeterminants.herm H v w := by
  simp [Formalism.QuantumDeterminants.herm, Matrix.mulVec_smul, dotProduct_smul]

theorem herm_smul_r {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (v w : Fin n → ℂ) (α : ℂ) :
    Formalism.QuantumDeterminants.herm H v (α • w) = star α * Formalism.QuantumDeterminants.herm H v w := by
  simp [Formalism.QuantumDeterminants.herm, star_smul, smul_dotProduct]

theorem herm_uh {n : ℕ} {H g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH H) (v w : Fin n → ℂ) :
    Formalism.QuantumDeterminants.herm H (g *ᵥ v) (g *ᵥ w) = Formalism.QuantumDeterminants.herm H v w := by
  unfold Formalism.QuantumDeterminants.herm
  have hg' : gᴴ * H * g = H := hg
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    hg']

theorem entry_eq {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    g i j = (g *ᵥ Formalism.QuantumDeterminants.bvec j) i := by
  simp [Formalism.QuantumDeterminants.bvec, Matrix.mulVec_single]

end GlobalTheory.TypeAsm.FramePf
namespace GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open FramePf

set_option maxHeartbeats 4000000 in

theorem frameC_holds : FrameC := by
  intro D large₂ X Y u C hStd t N hAd
  obtain ⟨-, hG0, hG1⟩ := hAd
  have hherm : ∀ x y : (VS D).V, star ((HV D).B x y) = (HV D).B y x := (HV D).herm
  have hBdef : ∀ x y : (VS D).V, (HV D).B x y = (VS D).hT y x := fun _ _ => rfl
  have hF0e : ∀ a : Fin D.R.rS, (F0 X u).e a.castSucc = X.eX a := fun a => by
    show (lf D (X.Fu u)).fl.fvec a.castSucc = _
    rw [fv_cast]; exact congrFun (X.Fu_e u) a
  have hF0z : (F0 X u).e (Fin.last _) = X.zu u := by
    show (lf D (X.Fu u)).fl.fvec (Fin.last _) = _
    rw [fv_last]; exact X.flagZVector u
  have hFte : ∀ a : Fin D.R.rS, (Ft t).e a.castSucc = t.lin (X.eX a) := fun a => by
    show (frq X t.rep).fl.fvec a.castSucc = _
    rw [GramPf.frq_fvec, fv_cast, X.Fu_e u]
  have hFtz : (Ft t).e (Fin.last _) = t.lin (X.zu u) := by
    show (frq X t.rep).fl.fvec (Fin.last _) = _
    rw [GramPf.frq_fvec, fv_last, X.flagZVector u]
  have hF0Xa : ∀ l : ℕ, (F0 X u).Xa l = Submodule.span D.host.E (X.eX '' {b | b.val < l}) := fun l => by
    unfold Formalism.HermitianLatticeCounting.S6.FlagD.Xa
    rw [show (fun b : Fin D.R.rS => (F0 X u).e b.castSucc) = X.eX from funext hF0e]
  have hFtXa : ∀ l : ℕ, (Ft t).Xa l =
      (Submodule.span D.host.E (X.eX '' {b | b.val < l})).map (t.lin : (VS D).V →ₗ[D.host.E] (VS D).V) := fun l => by
    unfold Formalism.HermitianLatticeCounting.S6.FlagD.Xa
    rw [Submodule.map_span, show (fun b : Fin D.R.rS => (Ft t).e b.castSucc) = t.lin ∘ X.eX from funext hFte,
      Set.image_comp]
    rfl
  have hlinI : ∀ x y, (HV D).B (t.lin x) (t.lin y) = (HV D).B x y := fun x y => t.rep.2.2.1 y x
  have hlinI' : ∀ x y, (HV D).B (t.lin.symm x) (t.lin.symm y) = (HV D).B x y := fun x y => by
    rw [← hlinI, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

  have hc1 : N.c * star N.c = 1 := N.c_norm
  have hc0 : N.c ≠ 0 := fun h => by simp [h] at hc1
  have hsame : ∀ a : Fin D.R.rS, N.j ≤ a.val → N.F'.e a.castSucc = N.c • N.F.e a.castSucc :=
    fun a ha => N.same a.castSucc ha
  have hsamez : N.F'.e (Fin.last _) = N.c • N.F.e (Fin.last _) := N.same (Fin.last _) (by simpa using N.j_le)
  have hXX : ∀ x y : (VS D).V, ∀ a b : D.host.E, (HV D).B (a • x) (b • y) = a * star b * (HV D).B x y := by
    intro x y a b
    rw [LinearMap.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, smul_eq_mul, starRingEnd_apply]
    ring
  have hP : (Matrix.of fun a b : Fin N.j => (HV D).B (N.F.e (Fin.castLE N.j_le a).castSucc)
      (N.F'.e (Fin.castLE N.j_le b).castSucc)).det ≠ 0 := by
    have e1 : (Matrix.of fun a b : Fin N.j => (HV D).B (N.F.e (Fin.castLE N.j_le a).castSucc)
        (N.F'.e (Fin.castLE N.j_le b).castSucc)) = N.w.mat * Matrix.diagonal fun b => ((N.sgn b : ℤ) : D.host.E) := by
      refine Matrix.ext fun a b => ?_
      rw [Matrix.mul_diagonal, Matrix.of_apply, ← N.pair a b]
      rfl
    rw [e1, Matrix.det_mul, Matrix.det_diagonal]
    refine mul_ne_zero (GlobalTheory.SgLoc.PtAlg.isUnit_det N.w).ne_zero (Finset.prod_ne_zero_iff.2 fun b _ => ?_)
    rcases Int.units_eq_one_or (N.sgn b) with h | h <;> simp [h]

  have hBl : ∀ (x y : (VS D).V) (a : D.host.E), (HV D).B (a • x) y = a * (HV D).B x y := fun x y a => by
    have := hXX x y a 1; simpa using this
  have hBr : ∀ (x y : (VS D).V) (b : D.host.E), (HV D).B x (b • y) = star b * (HV D).B x y := fun x y b => by
    have := hXX x y 1 b; simpa using this
  obtain ⟨fN, hfN1, hfN2, hfN3, hfN4, hfN5⟩ := L_duals (HV D) N.j_le (fun a => N.F.e a.castSucc)
    (fun a => N.F'.e a.castSucc) N.ist hP (fun a b => N.F'.iso a b)
    (fun a b ha _ => by
      have := N.F'.iso a b
      rw [hsame a ha, hBl] at this
      exact (mul_eq_zero.1 this).resolve_left hc0)
    (fun a b hb => N.ist_e a b hb) (fun a b ha hb => N.ist_e' a b ha hb) (fun a b ha hb => N.ist_iso a b ha hb)
  have hP' : (Matrix.of fun a b : Fin N.j => (HV D).B (N.F'.e (Fin.castLE N.j_le a).castSucc)
      (N.F.e (Fin.castLE N.j_le b).castSucc)).det ≠ 0 := by
    have e1 : (Matrix.of fun a b : Fin N.j => (HV D).B (N.F'.e (Fin.castLE N.j_le a).castSucc)
        (N.F.e (Fin.castLE N.j_le b).castSucc)) = (Matrix.of fun a b : Fin N.j => (HV D).B (N.F.e (Fin.castLE N.j_le a).castSucc)
        (N.F'.e (Fin.castLE N.j_le b).castSucc))ᴴ := by
      refine Matrix.ext fun a b => ?_
      rw [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.of_apply, hherm]
    rw [e1, Matrix.det_conjTranspose]
    exact fun h => hP (star_eq_zero.1 h)
  obtain ⟨fM, hfM1, hfM2, hfM3, hfM4, hfM5⟩ := L_duals (HV D) N.j_le (fun a => N.F'.e a.castSucc)
    (fun a => N.F.e a.castSucc) (fun b => N.c • N.ist b) hP' (fun a b => N.F.iso a b)
    (fun a b ha _ => by
      show (HV D).B (N.F'.e a.castSucc) (N.F.e b.castSucc) = 0
      rw [hsame a ha, hBl, N.F.iso a b, mul_zero])
    (fun a b hb => by
      show (HV D).B (N.F'.e a.castSucc) (N.c • N.ist b) = _
      rw [hBr]
      by_cases ha : N.j ≤ a.val
      · rw [hsame a ha, hBl, N.ist_e a b hb, ← mul_assoc, mul_comm (star N.c), hc1, one_mul]
      · rw [N.ist_e' a b (by omega) hb, mul_zero, if_neg (fun h : a = b => ha (h ▸ hb))])
    (fun a b ha hb => by
      show (HV D).B (N.F.e a.castSucc) (N.c • N.ist b) = 0
      rw [hBr, N.ist_e a b hb, if_neg (fun h => by subst h; omega), mul_zero])
    (fun a b ha hb => by
      show (HV D).B (N.c • N.ist a) (N.c • N.ist b) = 0
      rw [hBl, hBr, N.ist_iso a b ha hb, mul_zero, mul_zero])

  have hspanB : ∀ (S : Set (VS D).V) (z : (VS D).V), (∀ x ∈ S, (HV D).B x z = 0) →
      ∀ y ∈ Submodule.span D.host.E S, (HV D).B y z = 0 := by
    intro S z hS y hy
    induction hy using Submodule.span_induction with
    | mem x hx => exact hS x hx
    | zero => simp
    | add x y _ _ hx hy => rw [LinearMap.map_add, LinearMap.add_apply, hx, hy, add_zero]
    | smul c x _ hx => rw [hBl, hx, mul_zero]
  have hset : ∀ a : Fin D.R.rS, {b : Fin D.R.rS | b < a} = {b | b.val < a.castSucc.val} := fun a => rfl
  have hsetU : {b : Fin D.R.rS | b.val < (Fin.last D.R.rS).val} = Set.univ := by
    ext b; simp [b.isLt]
  have hzz0 : (HV D).B (X.zu u) (X.zu u) ≠ 0 := by
    rw [hBdef, X.zu_norm u]
    exact neg_ne_zero.2 (tu_ne D u)
  have hXef : ∀ a b, (HV D).B (X.eX a) (X.fY b) = if a = b then 1 else 0 := fun a b => by
    rw [← hherm]; show star ((VS D).hT (X.eX a) (X.fY b)) = _
    rw [X.ef]; split_ifs <;> simp
  have hXez : ∀ a, (HV D).B (X.eX a) (X.zu u) = 0 := fun a => by
    rw [← hherm]; show star ((VS D).hT (X.eX a) (X.zu u)) = _
    rw [(X.zu_orth u a).1, star_zero]
  have hXfz : ∀ a, (HV D).B (X.fY a) (X.zu u) = 0 := fun a => by
    rw [← hherm]; show star ((VS D).hT (X.fY a) (X.zu u)) = _
    rw [(X.zu_orth u a).2, star_zero]
  have hiz : ∀ a : Fin D.R.rS, N.j ≤ a.val → (HV D).B (N.F.e (Fin.last _)) (N.ist a) = 0 :=
    fun a ha => N.normalForm_dual_orthogonal_last a ha
  have hfNz : ∀ a, (HV D).B (fN a) (N.F.e (Fin.last _)) = 0 := by
    intro a
    by_cases ha : N.j ≤ a.val
    · rw [hfN1 a ha, ← hherm, hiz a ha, star_zero]
    · refine hspanB _ _ ?_ _ (hfN2 a (by omega))
      rintro _ ⟨b, -, rfl⟩
      have := N.F'.zperp b
      rw [hsamez, hBr] at this
      exact (mul_eq_zero.1 this).resolve_left (star_ne_zero.2 hc0)
  have hfMz : ∀ a, (HV D).B (fM a) (N.F'.e (Fin.last _)) = 0 := by
    intro a
    by_cases ha : N.j ≤ a.val
    · rw [hfM1 a ha, hsamez, hBl, hBr, ← hherm, hiz a ha, star_zero, mul_zero, mul_zero]
    · refine hspanB _ _ ?_ _ (hfM2 a (by omega))
      rintro _ ⟨b, -, rfl⟩
      show (HV D).B (N.F.e b.castSucc) (N.F'.e (Fin.last _)) = 0
      rw [hsamez, hBr, N.F.zperp b, mul_zero]
  obtain ⟨m2, hm2I, hm2e, hm2f, hm2z, hm2l, hm2p, hm2l', hm2p'⟩ := L_ratIso (HV D) X.eX X.fY
    (fun a => N.F.e a.castSucc) fN (X.zu u) (N.F.e (Fin.last _))
    (fun a b => X.ee b a) (fun a b => X.ff b a) hXef hXez hXfz hzz0
    (fun a b => N.F.iso a b) hfN4 hfN3 (fun a => N.F.zperp a) hfNz
    (fun a => by
      have := hG0 a.castSucc
      rw [hF0e, hF0Xa] at this
      rw [hset a]; exact this)
    (by
      have := hG0 (Fin.last _)
      rw [hF0z, hF0Xa, hsetU, Set.image_univ] at this
      exact this)

  have hlowT : ∀ (y w : (VS D).V) (l : ℕ), y - t.lin w ∈ (Ft t).Xa l →
      t.lin.symm y - w ∈ Submodule.span D.host.E (X.eX '' {b | b.val < l}) := by
    intro y w l h
    rw [hFtXa] at h
    obtain ⟨x, hx, hxe⟩ := Submodule.mem_map.1 h
    have e1 : t.lin.symm y - w = x := by
      rw [← t.lin.symm_apply_apply x]
      erw [hxe]
      rw [map_sub, LinearEquiv.symm_apply_apply]
    rw [e1]; exact hx
  obtain ⟨mA, hmAI, hmAe, hmAf, hmAz, hmAl, hmAp, hmAl', hmAp'⟩ := L_ratIso (HV D) X.eX X.fY
    (fun a => t.lin.symm (N.F'.e a.castSucc)) (fun a => t.lin.symm (fM a)) (X.zu u) (t.lin.symm (N.F'.e (Fin.last _)))
    (fun a b => X.ee b a) (fun a b => X.ff b a) hXef hXez hXfz hzz0
    (fun a b => by rw [hlinI']; exact N.F'.iso a b) (fun a b => by rw [hlinI']; exact hfM4 a b)
    (fun a b => by rw [hlinI']; exact hfM3 a b) (fun a => by rw [hlinI']; exact N.F'.zperp a)
    (fun a => by rw [hlinI']; exact hfMz a)
    (fun a => by
      have := hG1 a.castSucc
      rw [hFte] at this
      rw [hset a]; exact hlowT _ _ _ this)
    (by
      have := hlowT _ _ _ (hFtz ▸ hG1 (Fin.last _))
      rw [hsetU, Set.image_univ] at this
      exact this)

  obtain ⟨β, hβm, hβj, hβB⟩ := L_block N.j_le N.w
  have hmat := L_mat D X C
  choose nOf hnOf using hmat
  have hρ : 0 < 2 * D.host.v := by
    have := GramPf.rdE_pos' D
    simp only [Formalism.BasicNotions.Host.v]; linarith
  refine ⟨β, fun τ => nOf τ mA.symm.toLinearMap,
    fun τ => nOf τ mA.toLinearMap * nOf τ t.lin.symm.toLinearMap * nOf τ m2.symm.toLinearMap,
    fun τ => nOf τ m2.toLinearMap, fun τ => ?_⟩
  have hR : GlobalTheory.DegVol.IsReal (HV D) D.R.k D.R.rS (embS D τ) (phiV C τ) :=
    ⟨GramPf.phiV_add C τ, GramPf.phiV_smul C τ, GramPf.phiV_herm C τ, GramPf.phiV_span C τ⟩
  have hρa : ∀ a : Fin D.R.rS, ((((2 * D.host.v) ^ (D.R.rS - a.val) : ℝ)) : ℂ) ≠ 0 := fun a => by
    exact_mod_cast (pow_pos hρ _).ne'
  have hρa' : ∀ a : Fin D.R.rS, (((((2 * D.host.v) ^ (D.R.rS - a.val))⁻¹ : ℝ)) : ℂ) ≠ 0 := fun a => by
    exact_mod_cast (inv_pos.2 (pow_pos hρ _)).ne'
  have hNs : ∀ m : (VS D).V ≃ₗ[D.host.E] (VS D).V, (∀ x y, (HV D).B (m x) (m y) = (HV D).B x y) →
      (∀ a, m (X.eX a) - X.eX a ∈ Submodule.span D.host.E (X.eX '' {b | b < a})) →
      (∀ y, (∀ a, (HV D).B (X.eX a) y = 0) → m y - y ∈ Submodule.span D.host.E (Set.range X.eX)) →
      nOf τ m.toLinearMap ∈ Formalism.QuantumDeterminants.Nset D.R.k D.R.rS := fun m hI hl hp =>
    L_nset (HV D) (embS D τ) (phiV C τ) hR X.eX X.fY _ _ hρa hρa' (fun a => (L_frame D X C τ a).1)
      (fun a => (L_frame D X C τ a).2) hXef m.toLinearMap hI hl hp _ (hnOf τ _)
  have hsymI : ∀ m : (VS D).V ≃ₗ[D.host.E] (VS D).V, (∀ x y, (HV D).B (m x) (m y) = (HV D).B x y) →
      ∀ x y, (HV D).B (m.symm x) (m.symm y) = (HV D).B x y := fun m hI x y => by
    rw [← hI, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hN2 := hNs m2 hm2I hm2l hm2p
  have hN2' := hNs m2.symm (hsymI m2 hm2I) hm2l' hm2p'
  have hN1 := hNs mA.symm (hsymI mA hmAI) hmAl' hmAp'
  have hN1' := hNs mA hmAI hmAl hmAp
  have hinv : ∀ m : (VS D).V ≃ₗ[D.host.E] (VS D).V,
      nOf τ m.toLinearMap * nOf τ m.symm.toLinearMap = 1 ∧ nOf τ m.symm.toLinearMap * nOf τ m.toLinearMap = 1 := by
    intro m
    constructor
    · refine mat_ext_of (phiV C τ) (GramPf.phiV_span C τ) _ _ fun y => ?_
      rw [← Matrix.mulVec_mulVec, hnOf, hnOf, Matrix.one_mulVec]
      simp
    · refine mat_ext_of (phiV C τ) (GramPf.phiV_span C τ) _ _ fun y => ?_
      rw [← Matrix.mulVec_mulVec, hnOf, hnOf, Matrix.one_mulVec]
      simp
  have hγ1 : gamT C t τ * nOf τ t.lin.symm.toLinearMap = 1 := by
    refine mat_ext_of (phiV C τ) (GramPf.phiV_span C τ) _ _ fun y => ?_
    rw [← Matrix.mulVec_mulVec, hnOf, GramPf.gamT_act, Matrix.one_mulVec]
    simp
  have hγ2 : nOf τ t.lin.symm.toLinearMap * gamT C t τ = 1 := by
    refine mat_ext_of (phiV C τ) (GramPf.phiV_span C τ) _ _ fun y => ?_
    rw [← Matrix.mulVec_mulVec, GramPf.gamT_act, hnOf, Matrix.one_mulVec]
    simp

  have hm2e' : ∀ a, m2 (N.F.e a.castSucc) = X.eX a := hm2e
  have hm2f' : ∀ a, m2 (fN a) = X.fY a := hm2f
  have hmAe' : ∀ a, mA (t.lin.symm (N.F'.e a.castSucc)) = X.eX a := hmAe
  have hmAf' : ∀ a, mA (t.lin.symm (fM a)) = X.fY a := hmAf
  have hΦ : ∀ y, nOf τ m2.toLinearMap *ᵥ phiV C τ y = phiV C τ (m2 y) := fun y => hnOf τ _ y
  have hgΦ : ∀ y, (nOf τ mA.toLinearMap * nOf τ t.lin.symm.toLinearMap * nOf τ m2.symm.toLinearMap) *ᵥ
      (nOf τ m2.toLinearMap *ᵥ phiV C τ y) = phiV C τ (mA (t.lin.symm y)) := fun y => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc (nOf τ mA.toLinearMap * nOf τ t.lin.symm.toLinearMap), (hinv m2).2,
      Matrix.mul_one, ← Matrix.mulVec_mulVec, hnOf, hnOf]
    rfl
  refine ⟨hN1, hN2, ?_, ?_⟩
  · rw [Matrix.inv_eq_right_inv hγ1]
    rw [show nOf τ mA.symm.toLinearMap * (nOf τ mA.toLinearMap * nOf τ t.lin.symm.toLinearMap * nOf τ m2.symm.toLinearMap) *
        nOf τ m2.toLinearMap = (nOf τ mA.symm.toLinearMap * nOf τ mA.toLinearMap) * nOf τ t.lin.symm.toLinearMap *
        (nOf τ m2.symm.toLinearMap * nOf τ m2.toLinearMap) by simp only [Matrix.mul_assoc],
      (hinv mA).2, (hinv m2).2, Matrix.one_mul, Matrix.mul_one]

  have hnL : nOf τ t.lin.symm.toLinearMap ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) :=
    uh_inv (GramPf.gamT_mem C t τ) hγ1
  have hgU : nOf τ mA.toLinearMap * nOf τ t.lin.symm.toLinearMap * nOf τ m2.symm.toLinearMap ∈
      Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := uh_mul (uh_mul hN1'.1 hnL) hN2'.1
  have hn2U : nOf τ m2.toLinearMap ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := hN2.1
  set g := nOf τ mA.toLinearMap * nOf τ t.lin.symm.toLinearMap * nOf τ m2.symm.toLinearMap with hgdef
  set n2 := nOf τ m2.toLinearMap with hn2def
  have hGi : g * (n2 * gamT C t τ * nOf τ mA.symm.toLinearMap) = 1 := by
    rw [hgdef, show nOf τ mA.toLinearMap * nOf τ t.lin.symm.toLinearMap * nOf τ m2.symm.toLinearMap *
        (n2 * gamT C t τ * nOf τ mA.symm.toLinearMap) = nOf τ mA.toLinearMap * (nOf τ t.lin.symm.toLinearMap *
        ((nOf τ m2.symm.toLinearMap * n2) * gamT C t τ) * nOf τ mA.symm.toLinearMap) by simp only [Matrix.mul_assoc],
      hn2def, (hinv m2).2, Matrix.one_mul, hγ2, Matrix.one_mul, (hinv mA).1]
  have hGinv : g⁻¹ = n2 * gamT C t τ * nOf τ mA.symm.toLinearMap := Matrix.inv_eq_right_inv hGi
  have hGl : g⁻¹ * g = 1 := by rw [hGinv]; exact mul_eq_one_comm.1 hGi
  have hσc : embS D τ N.c * starRingEnd ℂ (embS D τ N.c) = 1 := by
    rw [← Formalism.L2.SG.LoopTerm.embS_star', ← map_mul, hc1, map_one]
  have hσc0 : embS D τ N.c ≠ 0 := fun h => by rw [h, zero_mul] at hσc; exact zero_ne_one hσc
  have hsm : ∀ (c : D.host.E) (y : (VS D).V), n2 *ᵥ phiV C τ (c • y) = embS D τ c • (n2 *ᵥ phiV C τ y) := by
    intro c y; rw [GramPf.phiV_smul, Matrix.mulVec_smul]

  have hA1 : ∀ a : Fin D.R.rS, n2 *ᵥ phiV C τ (N.F.e a.castSucc) =
      (((2 * D.host.v) ^ (D.R.rS - a.val) : ℝ) : ℂ) • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) := fun a => by
    rw [hΦ, hm2e']; exact (L_frame D X C τ a).1
  have hA2 : ∀ a : Fin D.R.rS, g *ᵥ (n2 *ᵥ phiV C τ (N.F'.e a.castSucc)) =
      (((2 * D.host.v) ^ (D.R.rS - a.val) : ℝ) : ℂ) • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) := fun a => by
    rw [hgΦ, hmAe']; exact (L_frame D X C τ a).1
  have hA3 : ∀ b : Fin D.R.rS, N.j ≤ b.val → n2 *ᵥ phiV C τ (N.ist b) =
      ((((2 * D.host.v) ^ (D.R.rS - b.val))⁻¹ : ℝ) : ℂ) • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI D.R.k D.R.rS b) := fun b hb => by
    rw [hΦ, ← hfN1 b hb, hm2f']; exact (L_frame D X C τ b).2
  have hA4 : ∀ b : Fin D.R.rS, N.j ≤ b.val → g *ᵥ (n2 *ᵥ phiV C τ (N.c • N.ist b)) =
      ((((2 * D.host.v) ^ (D.R.rS - b.val))⁻¹ : ℝ) : ℂ) • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI D.R.k D.R.rS b) := fun b hb => by
    rw [hgΦ, show N.c • N.ist b = fM b from (hfM1 b hb).symm, hmAf']; exact (L_frame D X C τ b).2
  have hZ1 : n2 *ᵥ phiV C τ (N.F.e (Fin.last _)) = zB X (C.Qi τ) u τ := by rw [hΦ, hm2z]; rfl
  have hZ2 : g *ᵥ (n2 *ᵥ phiV C τ (N.F'.e (Fin.last _))) = zB X (C.Qi τ) u τ := by rw [hgΦ, hmAz]; rfl
  have hXst : ∀ b : Fin D.R.rS, b.val < N.j → phiV C τ (X.fY b) ∈ GlobalTheory.Amp.XstJ D.R.k D.R.rS N.j := fun b hb => by
    rw [(L_frame D X C τ b).2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨b, hb⟩, rfl⟩)

  have hfun : (fun y => n2 *ᵥ phiV C τ y) = fun y => phiV C τ (m2 y) := funext hΦ
  have hzT := Formalism.L2.SG.Pf.zTr C u τ
  refine ⟨?_, hzT.1, hzT.1, ?_, ⟨(embS D τ N.c)⁻¹, ?_⟩, fun a => ⟨hA1 a, hA2 a⟩, fun b hb => hA3 b hb, hZ1, hZ2⟩
  · rw [hfun]
    refine ⟨fun x y => by beta_reduce; rw [map_add, GramPf.phiV_add],
      fun c x => by beta_reduce; rw [map_smul, GramPf.phiV_smul],
      fun x y => by beta_reduce; rw [GramPf.phiV_herm, hm2I], ?_⟩
    rw [show (Set.range fun y => phiV C τ (m2 y)) = Set.range (phiV C τ) from
      m2.surjective.range_comp (phiV C τ)]
    exact GramPf.phiV_span C τ
  · rw [hzT.2]
    show (0 : ℝ) < ((D.mem u).A.T : ℝ)
    exact_mod_cast (D.mem u).A.T_prime.pos

  have hcancel : ∀ (v : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (α : ℂ), α ≠ 0 →
      embS D τ N.c • α • (g *ᵥ v) = α • v → g *ᵥ v = (embS D τ N.c)⁻¹ • v := by
    intro v α hα h
    have h3 : (embS D τ N.c * α) • (g *ᵥ v) = α • v := by rw [mul_smul]; exact h
    calc g *ᵥ v = (embS D τ N.c * α)⁻¹ • ((embS D τ N.c * α) • (g *ᵥ v)) := by
          rw [smul_smul, inv_mul_cancel₀ (mul_ne_zero hσc0 hα), one_smul]
      _ = _ := by rw [h3, smul_smul, mul_inv, mul_assoc, inv_mul_cancel₀ hα, mul_one]
  refine ⟨hgU, ?_, ?_, hβm, hβj, fun a ha => ⟨?_, ?_⟩, fun a ha => ⟨?_, ?_⟩, ?_⟩
  · have h1 : (Complex.normSq (embS D τ N.c) : ℂ) = 1 := by rw [← Complex.mul_conj]; exact hσc
    have h2 : Complex.normSq (embS D τ N.c) = 1 := by exact_mod_cast h1
    rw [Complex.normSq_eq_norm_sq] at h2
    rw [norm_inv, (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2, inv_one]
  · have h1 := hZ2
    rw [hsamez, hsm, Matrix.mulVec_smul, hZ1] at h1
    calc g *ᵥ zB X (C.Qi τ) u τ = (embS D τ N.c)⁻¹ • (embS D τ N.c • g *ᵥ zB X (C.Qi τ) u τ) := by
          rw [smul_smul, inv_mul_cancel₀ hσc0, one_smul]
      _ = _ := by rw [h1]
  · have hE : Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) = ((((2 * D.host.v) ^ (D.R.rS - a.val) : ℝ) : ℂ))⁻¹ •
        (g *ᵥ (n2 *ᵥ phiV C τ (N.F'.e a.castSucc))) := by
      rw [hA2, smul_smul, inv_mul_cancel₀ (hρa a), one_smul]
    rw [hE, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hGl, Matrix.one_mulVec, hΦ]
    refine Submodule.smul_mem _ _ ?_
    exact span_map_mem (embS D τ) (fun y => phiV C τ (m2 y))
      (fun x y => by beta_reduce; rw [map_add, GramPf.phiV_add])
      (fun c x => by beta_reduce; rw [map_smul, GramPf.phiV_smul]) (fN '' {b | b.val < N.j}) _
      (by rintro _ ⟨b, hb, rfl⟩; beta_reduce; rw [hm2f']; exact hXst b hb) _ (hfN5 a ha)
  · have hE : Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) = ((((2 * D.host.v) ^ (D.R.rS - a.val) : ℝ) : ℂ))⁻¹ •
        (n2 *ᵥ phiV C τ (N.F.e a.castSucc)) := by
      rw [hA1, smul_smul, inv_mul_cancel₀ (hρa a), one_smul]
    rw [hE, Matrix.mulVec_smul, hgΦ]
    refine Submodule.smul_mem _ _ ?_
    exact span_map_mem (embS D τ) (fun y => phiV C τ (mA (t.lin.symm y)))
      (fun x y => by beta_reduce; rw [map_add, map_add, GramPf.phiV_add])
      (fun c x => by beta_reduce; rw [map_smul, map_smul, GramPf.phiV_smul]) (fM '' {b | b.val < N.j}) _
      (by rintro _ ⟨b, hb, rfl⟩; beta_reduce; rw [hmAf']; exact hXst b hb) _ (hfM5 a ha)
  · refine hcancel _ _ (hρa a) ?_
    have h1 := hA2 a
    rw [hsame a ha, hsm, Matrix.mulVec_smul, hA1, Matrix.mulVec_smul] at h1
    exact h1
  · refine hcancel _ _ (hρa' a) ?_
    have h1 := hA4 a ha
    rw [hsm, Matrix.mulVec_smul, hA3 a ha, Matrix.mulVec_smul] at h1
    exact h1
  · have hM : (GlobalTheory.Amp.Zr D.R.k D.R.rS g).submatrix (Fin.castLE N.j_le) (Fin.castLE N.j_le) =
        Matrix.of fun a b : Fin N.j => ((((2 * D.host.v) ^ (D.R.rS - b.val))⁻¹ *
          ((2 * D.host.v) ^ (D.R.rS - a.val))⁻¹ : ℝ) : ℂ) * embS D τ (N.w.mat b a * ((N.sgn a : ℤ) : D.host.E)) := by
      refine Matrix.ext fun a b => ?_
      rw [Matrix.submatrix_apply, Matrix.of_apply]
      rw [show GlobalTheory.Amp.Zr D.R.k D.R.rS g (Fin.castLE N.j_le a) (Fin.castLE N.j_le b) =
          Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) (g *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI D.R.k D.R.rS (Fin.castLE N.j_le b)))
            (Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI D.R.k D.R.rS (Fin.castLE N.j_le a))) by
        rw [herm_eI, ← entry_eq]; rfl]
      have hEb : Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI D.R.k D.R.rS (Fin.castLE N.j_le b)) =
          ((((2 * D.host.v) ^ (D.R.rS - (Fin.castLE N.j_le b).val) : ℝ) : ℂ))⁻¹ •
          (n2 *ᵥ phiV C τ (N.F.e (Fin.castLE N.j_le b).castSucc)) := by
        rw [hA1, smul_smul, inv_mul_cancel₀ (hρa _), one_smul]
      have hEa : Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI D.R.k D.R.rS (Fin.castLE N.j_le a)) =
          ((((2 * D.host.v) ^ (D.R.rS - (Fin.castLE N.j_le a).val) : ℝ) : ℂ))⁻¹ •
          (g *ᵥ (n2 *ᵥ phiV C τ (N.F'.e (Fin.castLE N.j_le a).castSucc))) := by
        rw [hA2, smul_smul, inv_mul_cancel₀ (hρa _), one_smul]
      rw [hEb, hEa, Matrix.mulVec_smul, herm_smul_l, herm_smul_r, herm_uh hgU, hΦ, hΦ, GramPf.phiV_herm, hm2I,
        show (HV D).B (N.F.e (Fin.castLE N.j_le b).castSucc) (N.F'.e (Fin.castLE N.j_le a).castSucc) =
          N.w.mat b a * ((N.sgn a : ℤ) : D.host.E) from N.pair b a]
      simp only [Fin.coe_castLE, ← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal]
      push_cast
      ring
    rw [hM]
    exact hβB (embS D τ) N.sgn (2 * D.host.v) hρ

end GlobalTheory.TypeAsm
