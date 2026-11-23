import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StabOrd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmPureTensorOReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexOrder

namespace GlobalTheory.KJRealOnb

variable {D : D7}

theorem det_ne_zero_of_onb {k : ℕ} {G B : Matrix (Fin k) (Fin k) ℂ} (hG : IsCartanInv G 1)
    (hB : ∃ p, IsONBasis G 1 B p) : G.det ≠ 0 ∧ B.det ≠ 0 := by
  have hP : G.PosDef := by simpa using hG.2.2
  have hGd : G.det ≠ 0 := hP.det_pos.ne'
  refine ⟨hGd, fun h0 => ?_⟩
  obtain ⟨p, ε, hε, h1, -⟩ := hB
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, h0, mul_zero, Matrix.det_diagonal] at h2
  refine (Finset.prod_ne_zero_iff.2 fun a _ => ?_) h2.symm
  rcases hε a with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]

theorem det_inB (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (g : GA D V)
    (τ : D.what₂.Tau) (hB : (B τ).det ≠ 0) : (inB θ V B g τ).det = (compAt θ τ (mt V g)).det := by
  unfold inB
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul, Matrix.mul_nonsing_inv _ (Ne.isUnit hB), Matrix.det_one, one_mul]

theorem comp_eq_mul_inB (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (g : GA D V)
    (hB : ∀ τ, (B τ).det ≠ 0) : (fun τ => compAt θ τ (mt V g) * B τ) = fun τ => B τ * inB θ V B g τ := by
  funext τ
  unfold inB
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (Ne.isUnit (hB τ)), Matrix.one_mul]

end GlobalTheory.KJRealOnb

namespace GlobalTheory.KJReal

open GlobalTheory.KJRealOnb in

theorem om_pureTensorO_onb : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (x : DefSp S) (y : DefSp T) (μ : (AE D)ˣ →* Circle) (om : Om S T), IsInfFam θ → x.Is → y.Is → x.s = (fun _ => 1) → y.s = (fun _ => 1) → Even S.rank → Even T.rank → IsWeilDatumO ψ S T μ μ om → ∀ e : D.what₂.Tau → ℤ, (∀ τ, HasInfExp D μ τ (e τ)) → ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 1) f) → ∀ k ∈ GinfC S, ∀ k' ∈ GinfC T, ∀ P, om (k, k') (pureTensorO ψ θ S T x.s y.s x.B y.B f P) = (∏ τ, (inB θ S x.B k τ).det ^ (-e τ - T.rank / 2 : ℤ) * (inB θ T y.B k' τ).det ^ (e τ + S.rank / 2 : ℤ)) • pureTensorO ψ θ S T x.s y.s x.B y.B f (mvZ (fun τ => (inB θ S x.B k τ)⁻¹) (inB θ T y.B k') P) := by
  intro D ψ θ S T x y μ om hθ hx hy hxs hys eS eT hom e he f hf hv k hk k' hk' P
  obtain ⟨mS, hmS⟩ := eS
  obtain ⟨mT, hmT⟩ := eT
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  have hψ := hom.std
  have cS : ∀ τ, IsCartanInv (gramAt D S τ) 1 := fun τ => by have h := hx.cart τ; rw [hxs] at h; exact h
  have cT : ∀ τ, IsCartanInv (gramAt D T τ) 1 := fun τ => by have h := hy.cart τ; rw [hys] at h; exact h
  have dS : ∀ τ, (gramAt D S τ).det ≠ 0 ∧ (x.B τ).det ≠ 0 := fun τ =>
    det_ne_zero_of_onb (cS τ) (by have h := hx.onb τ; rw [hxs] at h; exact h)
  have dT : ∀ τ, (gramAt D T τ).det ≠ 0 ∧ (y.B τ).det ≠ 0 := fun τ =>
    det_ne_zero_of_onb (cT τ) (by have h := hy.onb τ; rw [hys] at h; exact h)
  obtain ⟨xr, hxr, hxv⟩ := GlobalTheory.OneMapRef.RealMove.exists_root hθ S (fun τ => (dS τ).1) k hk
  obtain ⟨yr, hyr, hyv⟩ := GlobalTheory.OneMapRef.RealMove.exists_root hθ T (fun τ => (dT τ).1) k' hk'
  have hvac := GlobalTheory.WeilVacChar.vacuum_character D ψ hψ S T θ hθ μ μ om η hη hom (fun _ => 1) (fun _ => 1)
    cS cT k hk k' hk' (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) xr yr hxr hyr f hf hv
  have expT : ∀ τ, HasInfExp D (μ * (η ^ T.rank)⁻¹) τ ((e τ - mT : ℤ) : ℚ) := fun τ => by
    have h1 := GlobalTheory.OneMapRef.RealMove.hasInfExp_twist (he τ) (hη.2.2.2 τ) T.rank
    convert h1 using 1
    rw [hmT]; push_cast; ring
  have expS : ∀ τ, HasInfExp D (μ * (η ^ S.rank)⁻¹) τ ((e τ - mS : ℤ) : ℚ) := fun τ => by
    have h1 := GlobalTheory.OneMapRef.RealMove.hasInfExp_twist (he τ) (hη.2.2.2 τ) S.rank
    convert h1 using 1
    rw [hmS]; push_cast; ring
  have vx := hxv _ (fun τ => e τ - mT) expT
  have vy := hyv _ (fun τ => e τ - mS) expS
  have hmain := (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T μ μ om hom hθ (fun _ => 1) (fun _ => 1) x.B
    (fun τ => compAt θ τ (mt S k) * x.B τ) (fun _ => 1) (fun _ => 1) y.B
    (fun τ => compAt θ τ (mt T k') * y.B τ) k k' (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) (fun τ => rfl) (fun τ => rfl) f hf P).2
  rw [hxs, hys, hmain, hvac, GlobalTheory.FiniteFock.pureTensorO_smul, comp_eq_mul_inB θ S x.B k (fun τ => (dS τ).2),
    comp_eq_mul_inB θ T y.B k' (fun τ => (dT τ).2),
    GlobalTheory.FockBaseChange.pureTensorO_subst D ψ θ S T hψ hθ x.B (inB θ S x.B k) y.B (inB θ T y.B k') f hf P]
  congr 1
  · rw [Circle.coe_mul, Circle.coe_inv, vx, vy, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have inv := congrArg Matrix.det (GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) τ k)
    rw [Matrix.det_mul, Matrix.det_one] at inv
    have g0 := left_ne_zero_of_mul_eq_one inv
    have inv' := congrArg Matrix.det (GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) τ k')
    rw [Matrix.det_mul, Matrix.det_one] at inv'
    have g0' := left_ne_zero_of_mul_eq_one inv'
    rw [GlobalTheory.KJReal.detPlus_one_one, eq_inv_of_mul_eq_one_right inv, det_inB θ S x.B k τ (dS τ).2,
      det_inB θ T y.B k' τ (dT τ).2]
    have a1 : -e τ - (T.rank : ℤ) / 2 = -e τ - mT := by omega
    have a2 : e τ + (S.rank : ℤ) / 2 = e τ + mS := by omega
    rw [a1, a2]
    exact GlobalTheory.KJReal.exp_identity _ _ g0 g0' (e τ) mS mT S.rank T.rank (by rw [hmS]; push_cast; ring)
      (by rw [hmT]; push_cast; ring)

end GlobalTheory.KJReal
