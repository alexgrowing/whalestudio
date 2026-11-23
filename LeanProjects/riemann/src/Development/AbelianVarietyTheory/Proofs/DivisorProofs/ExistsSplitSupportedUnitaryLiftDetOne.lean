import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSymplecticBasisToMatrixOffDiagDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Lev Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ParahoricLiftDet

open GlobalTheory.ParahoricLift GlobalTheory.LevSplit Formalism.L2.NTheta Formalism.MainNotions.S Formalism.IndefR.Mult MeasureTheory

variable {D : D7} {n : ℕ}

theorem finite_maximalSpectrum_kP (P : Pl D.host.E) : Finite (MaximalSpectrum (kP P)) := by
  have hP : P.asIdeal.IsMaximal := P.isMaximal
  letI := Ideal.Quotient.field P.asIdeal
  exact Finite.of_subsingleton

theorem exists_detOne_lift (P : Pl D.host.E) (k : GL (Fin n) (kP P)) (hk : Matrix.GeneralLinearGroup.det k = 1) :
    ∃ Y : Matrix (Fin n) (Fin n) (𝓞 D.host.E), Y.map (Ideal.Quotient.mk P.asIdeal) = k.1 ∧ Y.det = 1 := by
  haveI := finite_maximalSpectrum_kP P
  have hk' : k.1.det = 1 := by
    have := congrArg Units.val hk
    rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at this
  obtain ⟨Y, hY⟩ := GlobalTheory.specialLinearGroup_map_surjective (n := Fin n) (f := Ideal.Quotient.mk P.asIdeal)
    Ideal.Quotient.mk_surjective ⟨k.1, hk'⟩
  exact ⟨Y.1, congrArg Subtype.val hY, Y.2⟩

theorem idem_mul_pow {A : Type} [CommRing A] {p : A} (hp : p * p = p) (m : ℕ) : p * p ^ m = p := by
  induction m with
  | zero => rw [pow_zero, mul_one]
  | succ k ih => rw [pow_succ, ← mul_assoc, ih, hp]

theorem idem_mul_det {A : Type} [CommRing A] {m : ℕ} {p : A} (hp : p * p = p) {a b : Matrix (Fin m) (Fin m) A}
    (h : p • a = p • b) : p * a.det = p * b.det := by
  have h1 := congrArg Matrix.det h
  rw [Matrix.det_smul, Matrix.det_smul, Fintype.card_fin] at h1
  have hpow : p * p ^ m = p := idem_mul_pow hp m
  calc p * a.det = p * p ^ m * a.det := by rw [hpow]
    _ = p * p ^ m * b.det := by rw [mul_assoc, h1, ← mul_assoc]
    _ = p * b.det := by rw [hpow]

set_option maxHeartbeats 1000000 in

theorem exists_local_lift_det : ∀ {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ}, IsBaseFrame V β Λ N → ∀ {P : Pl D.host.E} {e : AE D},
    Formalism.L2.NTheta.IsIdemAt e P → ∀ (k : GL (Fin V.rank) (kP P)), Matrix.GeneralLinearGroup.det k = 1 →
    ∃ κ : GA D V, SuppAt e V κ ∧ κ ∈ GfC V ∧ finE V κ ∈ St β ∧ redFn β P (finE V κ) = k ∧
      (∀ P', P' ≠ P → ¬ Lev.IsConjPl P P' → redFn β P' (finE V κ) = 1) ∧ IsDetAt e V κ 1 := by
  intro D V β Λ N hB P e he k hk
  have := P.isPrime
  obtain ⟨p, hp, hpp, hres⟩ := exists_idem_int he
  obtain ⟨Y₀, hY₀, hdet1⟩ := exists_detOne_lift P k hk
  have hdet : Ideal.Quotient.mk P.asIdeal Y₀.det ≠ 0 := by
    rw [hdet1, map_one]; exact one_ne_zero
  obtain ⟨u, hu⟩ := finSw_div_int he (d := Y₀.det) fun h => hdet (Ideal.Quotient.eq_zero_iff_mem.2 h)
  obtain ⟨Y, hY⟩ : ∃ Y, Y = Y₀.map (oToS D.host.F D.host.E) := ⟨_, rfl⟩
  have hYdet : Y.det = 1 := by
    rw [hY, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet1, map_one]
  have hu' : u * Y.det = p := by
    rw [hY, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact Subtype.ext (hu.trans hp.symm)
  have hmm := conj_inv_part β p u Y hu' hpp
  rw [hp] at hmm
  obtain ⟨κ, hs, hκ⟩ := split_lift_fin V he.1 _ _ hmm
  have hP : IsPrimeIdem P e (e + cA D e) := Or.inl ⟨he, rfl⟩
  obtain ⟨-, -, T3, -⟩ := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V
  have hsf := supp_fin V (f := e + cA D e) hs
  have hκd := hκ
  rw [← hp] at hκ
  have hf : finSw D (e + cA D e) = p + Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) p := by
    rw [RingHom.map_add, finSw_cA, hp]
  have hSt : finE V κ ∈ St β :=
    mem_St_of_part D.sp.cm.sig V.gram Λ β hB.1 (hatL_selfDual hB) p u hpp (sigR_int p.2) Y hu' (finE V κ)
      (finE_mem_UA V κ) _ hf hsf hκ

  have hD : e * (mt V κ).det = e := by
    have he2 : finSw D e * finSw D e = finSw D e := by rw [← RingHom.map_mul, he.1.1]
    have h1 := idem_mul_det he2 hκd
    have e1 : (finE V κ).1 = (mt V κ).map (finSw D) := rfl
    have e2 : (β.1 * Y.map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype * (β⁻¹).1).det = 1 := by
      rw [Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul, Units.inv_mul, Matrix.det_one,
        one_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hYdet, map_one]
    rw [e1, e2, ← RingHom.mapMatrix_apply, ← RingHom.map_det, mul_one, ← RingHom.map_mul] at h1
    have h2 : finPart D (e * (mt V κ).det) = finPart D e := (swp_bij (F := D.host.F) (E := D.host.E)).1 h1
    refine GlobalTheory.SplitScalar.adele_ext ?_ h2
    rw [RingHom.map_mul, GlobalTheory.PlaceModelSum.infPart_split he.1, zero_mul]
  refine ⟨κ, hs, (T3 P e _ hP).2.2.1 κ hs, hSt, Units.ext ?_, fun P' h1 h2 => ?_, ?_⟩
  · rw [redFn_of_smul_eq β P _ hSt p hres Y hκ, hY, ← hY₀]
    exact Matrix.ext fun i j => resS_oToS P _
  · obtain ⟨y, y', hy, hyy, a1, a2⟩ := exists_sep h1 fun h => h2 (isConjPl_symm h)
    obtain ⟨w, hw⟩ := idem_div_int hP y y' hyy a1 a2
    refine redFn_eq_one β P' _ hSt (w * oToS D.host.F D.host.E y) ?_ ?_
    · rw [RingHom.map_mul, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 hy, mul_zero]
    · have e1 : ((w * oToS D.host.F D.host.E y : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) =
          finSw D (e + cA D e) := hw
      rw [e1]
      exact hsf
  · show ((1 : (AE D)ˣ) : AE D) = e * (mt V κ).det + (1 - e)
    rw [hD, Units.val_one]
    ring

end GlobalTheory.ParahoricLiftDet

end
