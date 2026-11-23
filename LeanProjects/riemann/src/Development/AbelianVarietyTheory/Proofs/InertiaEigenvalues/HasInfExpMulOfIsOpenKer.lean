import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumRealPlacesFockVacuumCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumCharacterPositiveDefiniteSource
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorChangeOrthonormalBasesSubst
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open GlobalTheory.VacuumCharacter
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealFockAction

variable {D : D7}

theorem eq_one_of_isOpen_ker {θ : InfFam D} (hθ : IsInfFam θ) {χ : (AE D)ˣ →* Circle}
    (hχ : IsOpen (χ.ker : Set (AE D)ˣ)) (x : (AE D)ˣ) (hx : finPart D (x : AE D) = 1) : χ x = 1 := by
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := D.host.F) (E := D.host.E)
  obtain ⟨σ, hσ⟩ := GlobalTheory.FockCompare.exists_chart hθ
  let a : (D.what₂.Tau → ℂ) → AE D := fun z => 1 + σ fun τ => Complex.exp (z τ) - 1
  have a1 : ∀ z, finPart D (a z) = 1 := fun z => by
    simp only [a]; rw [RingHom.map_add, hσ.fin, RingHom.map_one, add_zero]
  have a2 : ∀ z τ, θ τ (infPart D (a z)) = Complex.exp (z τ) := fun z τ => by
    simp only [a]; rw [RingHom.map_add, RingHom.map_add, hσ.comp, RingHom.map_one, RingHom.map_one]; ring
  have a3 : ∀ z, a z * a (-z) = 1 := fun z => adele_ext hθ
    (by rw [RingHom.map_mul, a1, a1, RingHom.map_one, one_mul]) fun τ => by
      rw [RingHom.map_mul, RingHom.map_mul, a2, a2, RingHom.map_one, RingHom.map_one, ← Complex.exp_add]
      simp
  have ac : Continuous a := continuous_const.add (hσ.cont.comp (by fun_prop))
  let e : (D.what₂.Tau → ℂ) → (AE D)ˣ := fun z => ⟨a z, a (-z), a3 z, (mul_comm _ _).trans (a3 z)⟩
  have ec : Continuous e := Units.continuous_iff.2 ⟨ac, ac.comp continuous_neg⟩
  have hcl : IsClopen (e ⁻¹' (χ.ker : Set (AE D)ˣ)) :=
    IsClopen.preimage ⟨Subgroup.isClosed_of_isOpen _ hχ, hχ⟩ ec
  have e0 : e 0 = 1 := Units.ext (adele_ext hθ ((a1 0).trans (RingHom.map_one _).symm) fun τ => by
    refine (a2 0 τ).trans ?_
    rw [Units.val_one, RingHom.map_one, RingHom.map_one]
    simp)
  have hall := hcl.eq_univ ⟨0, by rw [Set.mem_preimage, e0]; exact one_mem χ.ker⟩
  have ex : e (fun τ => Complex.log (θ τ (infPart D (x : AE D)))) = x :=
    Units.ext (adele_ext hθ ((a1 _).trans hx.symm) fun τ => (a2 _ τ).trans
      (Complex.exp_log ((x.isUnit.map (infPart D)).map (θ τ)).ne_zero))
  rw [← ex]
  exact MonoidHom.mem_ker.1 (hall ▸ Set.mem_univ _ : _ ∈ e ⁻¹' (χ.ker : Set (AE D)ˣ))

theorem hasInfExp_mul_of_isOpen_ker {χ ν : (AE D)ˣ →* Circle} {τ : D.what₂.Tau} {a : ℚ} (hχ : HasInfExp D χ τ a)
    (hν : IsOpen (ν.ker : Set (AE D)ˣ)) : HasInfExp D (χ * ν) τ a := by
  obtain ⟨n, hn, h1, h2⟩ := hχ
  refine ⟨n, hn, h1, fun θ hθ x hx hτ => ?_⟩
  rw [MonoidHom.mul_apply, eq_one_of_isOpen_ker hθ hν x hx, mul_one, h2 θ hθ x hx hτ]

theorem onb_laws {k : ℕ} {G s B : Matrix (Fin k) (Fin k) ℂ} {p : ℕ} (h : IsONBasis G s B p) (hp : p ≤ k) :
    (s * B = B * diagonal fun a : Fin k => if decide (a.val < p) then (1 : ℂ) else -1) ∧
      s.trace = 2 * p - k := by
  obtain ⟨ε, hε, h1, h2⟩ := h
  have e : (fun a => (ε a : ℂ)) = fun a : Fin k => if decide (a.val < p) then (1 : ℂ) else -1 := funext fun a => by
    rcases hε a with h | h
    · simp [h.1, h.2]
    · simp [h.1, not_lt.2 h.2]
  have hd : B.det ≠ 0 := fun h0 => by
    have h3 := congrArg Matrix.det h1
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_diagonal] at h3
    obtain ⟨a, -, ha⟩ := Finset.prod_eq_zero_iff.1 h3.symm
    rcases hε a with h | h <;> simp [h.1] at ha
  rw [e] at h2
  refine ⟨h2, ?_⟩
  have h4 : s = B * (diagonal fun a : Fin k => if decide (a.val < p) then (1 : ℂ) else -1) * B⁻¹ := by
    rw [← h2, Matrix.mul_nonsing_inv_cancel_right _ _ (isUnit_iff_ne_zero.2 hd)]
  rw [h4, Matrix.trace_mul_cycle, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hd), Matrix.one_mul,
    Matrix.trace_diagonal]
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hp
  rw [Fin.sum_univ_add]
  simp
  ring

theorem onb_posDef {k : ℕ} {G B : Matrix (Fin k) (Fin k) ℂ} (h : IsONBasis G 1 B k) : Bᴴ * G * B = 1 := by
  obtain ⟨ε, hε, h1, -⟩ := h
  rw [h1, ← Matrix.diagonal_one]
  congr 1
  funext a
  rcases hε a with h | h
  · simp [h.1]
  · exact absurd a.2 (not_lt.2 h.2)

theorem conj_unitary {n : ℕ} {G B g : Matrix (Fin n) (Fin n) ℂ} (h : Bᴴ * G * B = 1) (hg : gᴴ * G * g = G) :
    B⁻¹ * g * B ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  have hB : B * (Bᴴ * G) = 1 := mul_eq_one_comm.1 h
  have hi : B⁻¹ = Bᴴ * G := Matrix.inv_eq_right_inv hB
  have h0 : B * B⁻¹ = 1 := by rw [hi, hB]
  have h1 : (B⁻¹)ᴴ * Bᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h0, Matrix.conjTranspose_one]
  have hG : (B⁻¹)ᴴ * B⁻¹ = G := by
    calc _ = (B⁻¹)ᴴ * (Bᴴ * G) := by rw [← hi]
      _ = _ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  calc _ = Bᴴ * (gᴴ * ((B⁻¹)ᴴ * B⁻¹) * g) * B := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hG, hg, h]

variable {S T : HSp D}

theorem pureTensorO_subst {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} {p : D.what₂.Tau → ℕ}
    (hS : ∀ τ, IsCartanInv (gramAt D S τ) 1) (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    (ht : ∀ τ, sT τ * BT τ = BT τ * diagonal fun a : Fin T.rank => if decide (a.val < p τ) then (1 : ℂ) else -1)
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (u : GLR D S.rank)
    (hu : ∀ τ, (u τ).val ∈ Matrix.unitaryGroup (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (P : PolF D T.rank S.rank) :
    pureTensorO ψ θ S T (fun _ => 1) sT (fun τ => BS τ * (u τ).val) BT f P =
      pureTensorO ψ θ S T (fun _ => 1) sT BS BT f (fockSubst p u P) := by
  classical
  have hadd : ∀ g g', IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' → IsThetaFunO ψ S T (g + g') :=
    fun _ _ => GlobalTheory.OrientedHeis.theta_add
  have hsm : ∀ (a : ℂ) g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T (a • g) :=
    fun a _ => GlobalTheory.OrientedHeis.theta_smul a
  have hth : ∀ B B' v g, IsThetaFunO ψ S T g →
      IsThetaFunO ψ S T (aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (sT τ)) B B' v g) :=
    fun _ _ _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ h
  have hX : ∀ B B' v Q,
      pureTensorL (aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (sT τ)) B B') f (MvPolynomial.X v * Q) =
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (sT τ)) B B' v
        (pureTensorL (aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (sT τ)) B B') f Q) := fun B B' v Q => by
    refine GlobalTheory.FockIndep.pure_X_mul (P := IsThetaFunO ψ S T) hadd hsm (hth B B') ?_ ?_ ?_ hf Q v
    · exact fun i j _ h => GlobalTheory.FockIndep.aPlus_comm' (sS := fun _ => 1) hψ hθ i.1 _ hS hT j.1 _ h
    · exact fun _ _ _ h h' => GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ h h'
    · exact fun _ a _ h => GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ a h
  have hA : ∀ v g, IsThetaFunO ψ S T g →
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (sT τ)) (fun τ => BS τ * (u τ).val) BT v g =
      ∑ a, ∑ b, (if decide (v.2.1.val < p v.1) = true then
          (1 : Matrix (Fin T.rank) (Fin T.rank) ℂ) a v.2.1 * (u v.1).val⁻¹ v.2.2 b
        else (1 : Matrix (Fin T.rank) (Fin T.rank) ℂ)⁻¹ v.2.1 a * (u v.1).val b v.2.2) •
        aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (sT τ)) BS BT (v.1, a, b) g := fun v g hg => by
    unfold aPlusAll
    have := GlobalTheory.FockBasis.aPlus_unitMap_mul hψ hθ v.1 _ hg (ht v.1) (k := 1)
      ⟨one_mem _, by rw [Matrix.one_mul, Matrix.mul_one]⟩ (BS v.1) (hu v.1) v.2.1 v.2.2
    rw [Matrix.mul_one] at this
    exact this
  have key := GlobalTheory.FockBasis.pure_subst (P := IsThetaFunO ψ S T) _ _
    (GlobalTheory.FockIndep.pure_mem (P := IsThetaFunO ψ S T) hadd hsm (hth _ _) hf) (hX _ _) (hX _ _) hA P
  unfold pureTensorO
  rw [key]
  congr 2
  unfold fockSubst
  congr 1
  funext ⟨τ, i, j⟩
  rw [Finset.sum_eq_single i]
  · by_cases h : i.val < p τ <;> simp [h]
  · intro a _ ha
    simp [Matrix.one_apply_ne ha, Matrix.one_apply_ne ha.symm]
  · simp

theorem om_vac {B : Base S T} {ψ : Twist D Circle} {ω : PairRep S T} (hB : B.Good) (hψ : ψ.Good)
    (hω : B.IsWeil ψ.chi ω) {f : WO S T → ℂ} (hf : IsThetaFunO B.F.ψ S T f)
    (hv : ∀ τ, IsFockVacAt (heisO B.F.ψ S T) B.F.θ τ (cplxO 1 (B.F.sT τ)) f) {u : GA D S} (hu : u ∈ GinfC S) :
    ω (u, 1) f = (((detFam B.w.c (realGL B.F.θ S u))⁻¹ : ℂˣ) : ℂ) • f := by
  have hθ := hB.frame.vac.2.inf
  have hS := fun τ => GlobalTheory.FockBasis.isCartanInv_one (onb_posDef (hB.frame.onbS τ))
  have hT := hB.frame.cartT
  have one : ∀ τ, compAt B.F.θ τ (Formalism.L2.Theta.mt T 1) = 1 := fun τ => GlobalTheory.PointAtPlaceHom.infMat_one T _
  have hpq : ∀ τ, B.w.p τ + B.w.q τ = T.rank := fun τ => by
    obtain ⟨e, -⟩ := hB.sigOK (tauE D τ)
    rw [← hB.sig τ] at e
    simpa using (Fintype.card_congr e).symm
  obtain ⟨x, hx, hxv⟩ := exists_root hθ S (fun τ => by
    have := (hS τ).2.2.det_pos.ne'
    rwa [Matrix.mul_one] at this) u hu
  have hy : IsDetRoot T 1 1 := by
    show _ = _
    rw [Units.val_one, RingHom.map_one, mul_one]
    exact (Matrix.det_one).symm
  choose p hp hd using fun τ => detPlus_one (n := S.rank) (B.F.sT τ) (hT τ).1
  have ep : ∀ τ, p τ = B.w.p τ := fun τ => by
    have h1 := hB.frame.onbT τ
    rw [← hB.sig τ] at h1
    have h2 := (onb_laws h1 (hpq τ ▸ Nat.le_add_right _ _)).2
    rw [hp] at h2
    have h3 : (p τ : ℂ) = B.w.p τ := by linear_combination h2 / 2
    exact_mod_cast h3
  rw [GlobalTheory.T.weilDatum_realPlaces_fockVacuum_character D B.F.ψ hω.std S T B.F.θ hθ _ _ ω B.eta hB.eta hω (fun _ => 1) B.F.sT hS hT u hu 1 (one_mem _)
    (fun τ => by rw [one_mul, mul_one]) (fun τ => by rw [one, one_mul, mul_one]) x 1 hx hy f hf hv]
  congr 1
  have hexp : ∀ τ, HasInfExp D (B.mu * ψ.chi * B.eta⁻¹ * (B.eta ^ T.rank)⁻¹) τ ((B.w.c τ - p τ : ℤ) : ℚ) := fun τ => by
    have h1 := hasInfExp_twist (hasInfExp_twist (hasInfExp_mul_of_isOpen_ker
      (hasInfExp_mul_of_isOpen_ker (hB.inf τ) hB.de.isOpen) hψ.isOpen) (hB.eta.2.2.2 τ) 1) (hB.eta.2.2.2 τ) T.rank
    rw [pow_one] at h1
    convert h1 using 1
    · rfl
    rw [← hpq τ, ep]
    push_cast
    ring
  rw [MonoidHom.map_one, mul_one, Circle.coe_inv, hxv _ _ hexp, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib,
    Units.val_inv_eq_inv_val]
  simp only [detFam, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_prod, Units.val_zpow_eq_zpow_val,
    GeneralLinearGroup.val_det_apply]
  rw [← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have inv := congrArg Matrix.det (GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := B.F.θ) τ u)
  rw [Matrix.det_mul, Matrix.det_one] at inv
  have g0 := left_ne_zero_of_mul_eq_one inv
  rw [one, (hd τ _ 1 (by rw [one_mul, mul_one])).1, eq_inv_of_mul_eq_one_right inv, mul_one, ← smul_add,
    add_add_sub_cancel, ← two_smul ℂ, smul_smul, show (1 / 2 * 2 : ℂ) = 1 by norm_num, one_smul, Matrix.det_one, one_pow,
    one_mul, show (realGL B.F.θ S u τ).val = compAt B.F.θ τ (Formalism.L2.Theta.mt S u) from rfl, zpow_sub₀ g0, zpow_natCast,
    inv_pow]
  have := pow_ne_zero (p τ) g0
  have := zpow_ne_zero (B.w.c τ) g0
  field_simp

theorem om_fock_vecAt : ∀ (D : D7) (S T : HSp D) (B : Base S T) (ψ : Twist D Circle) (ω : PairRep S T) (Q : Finset (Pl D.host.E)) (φ : ∀ PP : ↥Q, Matrix (Fin T.rank) (Fin S.rank) (kP PP.1) → ℂ), B.Good → ψ.Good → B.admitted Q → B.IsWeil ψ.chi ω → ∀ u ∈ GinfC S, ∀ P, ω (u, 1) (B.F.fock (B.vecAt Q φ) P) = B.F.fock (B.vecAt Q φ) (B.act u P) := by
  intro D S T B ψ ω Q φ hB hψ hQ hω u hu P
  have hθ := hB.frame.vac.2.inf
  have hBS := fun τ => onb_posDef (hB.frame.onbS τ)
  have hth := Base.isThetaAt_vecAt hB hQ φ
  have hf := GlobalTheory.GalLift.Vec.theta_of_thetaAt hB.frame.vac.1 hθ hth hB.frame.vac.2.theta
  have ho := hQ.1.isOrthSum.1
  have hv := fun τ => GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hB.frame.vac.1.1.1 hθ ho.infPart_eq ho.conj.infPart_eq hth
    hB.frame.vac.2.theta hf (hB.frame.vac.2.fock τ)
  have one : ∀ τ, compAt B.F.θ τ (Formalism.L2.Theta.mt T 1) = 1 := fun τ => GlobalTheory.PointAtPlaceHom.infMat_one T _
  have eu : ∀ τ, (inBasis B.F.BS (realGL B.F.θ S u) τ).val =
      (B.F.BS τ).val⁻¹ * compAt B.F.θ τ (Formalism.L2.Theta.mt S u) * (B.F.BS τ).val := fun τ => by
    rw [← Matrix.coe_units_inv]
    rfl
  have hle : ∀ τ, B.w.p τ ≤ T.rank := fun τ => by
    obtain ⟨e, -⟩ := hB.sigOK (tauE D τ)
    rw [← hB.sig τ] at e
    have := Fintype.card_congr e
    simp only [Fintype.card_fin, Fintype.card_sum] at this
    omega
  unfold Frame.fock
  rw [(GlobalTheory.OrientedHeis.om_pureTensorO D _ _ S T _ _ ω hω hθ (fun _ => 1) (fun _ => 1) (fun τ => (B.F.BS τ).val)
    (fun τ => (B.F.BS τ).val * (inBasis B.F.BS (realGL B.F.θ S u) τ).val) B.F.sT B.F.sT B.F.BT B.F.BT u 1
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) (fun τ => by rw [one, one_mul, mul_one])
    (fun τ => by rw [eu, ← Matrix.coe_units_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul])
    (fun τ => by rw [one, one_mul]) _ hf P).2, om_vac hB hψ hω hf hv hu, GlobalTheory.FiniteFock.pureTensorO_smul,
    pureTensorO_subst (p := B.w.p) hB.frame.vac.1 hθ (fun τ => GlobalTheory.FockBasis.isCartanInv_one (hBS τ)) hB.frame.cartT
      (fun τ => (onb_laws (by have := hB.frame.onbT τ; rwa [← hB.sig τ] at this) (hle τ)).1) _ _
      (fun τ => by rw [eu]; exact conj_unitary (hBS τ) (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ S u τ)) hf,
    Base.act, MonoidHom.comp_apply, fockGL_apply, LinearMap.map_smul]

end GlobalTheory.RealFockAction

end
