import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IntBasisAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusSectionAcrisBreuilKisin

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem secU_holds : CoreU → SecU := by
  intro hU l _ K bk N
  obtain ⟨n₀, hn₀⟩ := GlobalTheory.AcrisPow.main l K bk (2 * N + 1) 1
  refine ⟨n₀ + 2 * N * n₀, fun d A A' hA => ?_⟩
  set ψ : bk.S →+* Per.Acris l := (algebraMap (Ainf l) (Per.Acris l)).comp bk.ev with hψ
  obtain ⟨htor, hcomp, ⟨v, hv⟩, hφ, -⟩ := GlobalTheory.AcrisFrobE.main l K bk
  have hφψ : ∀ s, phiA l (ψ s) = ψ (frobS l bk.a s) := fun s => by
    simp only [hψ, RingHom.comp_apply, hφ, bk.ev_frob]
  have hu : phiA l (ψ X) = ψ X ^ l := by rw [hφψ, frobS_X, map_pow]
  have hdiff : ∀ s : bk.S, ∃ t : Per.Acris l,
      ψ (frobS l bk.a s) - ψ (frobS l bk.a (PowerSeries.C (PowerSeries.constantCoeff s))) = ψ X ^ l * t := by
    intro s
    obtain ⟨t, ht⟩ := (PowerSeries.X_dvd_iff (φ := s - PowerSeries.C (PowerSeries.constantCoeff s))).2 (by simp)
    refine ⟨ψ (frobS l bk.a t), ?_⟩
    rw [← map_sub, ← map_sub, ht, map_mul, frobS_X, map_mul, map_pow]
  obtain ⟨w, hw⟩ := bk.coeff_zero
  have hE0 : PowerSeries.constantCoeff bk.E = bk.Ep.coeff 0 := by simp
  set w0 : Per.Acris l := ψ (frobS l bk.a (PowerSeries.C (w : Wq l bk.a))) with hw0def
  have hw0u : IsUnit w0 := ((w.isUnit.map PowerSeries.C).map (frobS l bk.a)).map ψ
  have hP0 : ψ (frobS l bk.a (PowerSeries.C (PowerSeries.constantCoeff bk.E))) = (l : Per.Acris l) * w0 := by
    rw [hE0, hw, map_mul, map_natCast, map_mul, map_natCast, map_mul, map_natCast]
  set u : Per.Acris l := ψ X with hudef
  set P : Per.Acris l := ψ (frobS l bk.a bk.E) with hPdef
  set a : Per.Acris l := ((v⁻¹ : (Per.Acris l)ˣ) : Per.Acris l) with hadef
  set b : Per.Acris l := ((hw0u.unit⁻¹ : (Per.Acris l)ˣ) : Per.Acris l) with hbdef
  have hav : a * v = 1 := Units.inv_mul v
  have hbw : b * w0 = 1 := by rw [hbdef]; exact hw0u.val_inv_mul
  set fB : bk.S →+* Per.Acris l := ψ.comp (frobS l bk.a) with hfB
  set fB0 : bk.S →+* Per.Acris l := fB.comp (PowerSeries.C.comp PowerSeries.constantCoeff) with hfB0
  have hmap : ∀ f : bk.S →+* Per.Acris l, (A.map f) * (A'.map f) = (f bk.E) ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) := by
    intro f
    rw [← Matrix.map_mul, hA]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hfE : fB bk.E = (l : Per.Acris l) * v := hv
  have hfE0 : fB0 bk.E = (l : Per.Acris l) * w0 := hP0
  have hcoef : ∀ (c y : Per.Acris l), c * y = 1 → c ^ N * c ^ N * ((l : Per.Acris l) * y) ^ (2 * N) = (l : Per.Acris l) ^ (2 * N) := by
    intro c y h
    calc c ^ N * c ^ N * ((l : Per.Acris l) * y) ^ (2 * N) = (l : Per.Acris l) ^ (2 * N) * (c * y) ^ (2 * N) := by ring
      _ = _ := by rw [h, one_pow, mul_one]
  have hα : (a ^ N • A.map fB) * (a ^ N • A'.map fB) = ((l : Per.Acris l) ^ (2 * N)) • 1 := by
    rw [smul_mul_assoc, mul_smul_comm, hmap, hfE, smul_smul, smul_smul, hcoef a v hav]
  have hβ : (b ^ N • A.map fB0) * (b ^ N • A'.map fB0) = ((l : Per.Acris l) ^ (2 * N)) • 1 := by
    rw [smul_mul_assoc, mul_smul_comm, hmap, hfE0, smul_smul, smul_smul, hcoef b w0 hbw]
  choose G hG using fun i j => hdiff (A i j)
  obtain ⟨z, hz⟩ := hdiff bk.E
  obtain ⟨t, ht⟩ := sub_dvd_pow_sub_pow w0 v N
  have hΓ : (l : Per.Acris l) • (a ^ N • A.map fB - b ^ N • A.map fB0) =
      u ^ l • ((((l : Per.Acris l) * a ^ N) • Matrix.of G) + (-(a ^ N * b ^ N * z * t)) • A.map fB0) := by
    ext i j
    have h1 : fB (A i j) - fB0 (A i j) = u ^ l * G i j := hG i j
    have h2 : (l : Per.Acris l) * v - (l : Per.Acris l) * w0 = u ^ l * z := by rw [← hfE, ← hfE0]; exact hz
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.map_apply, Matrix.of_apply,
      smul_eq_mul]
    have h4 : (a * v) ^ N = 1 := by rw [hav, one_pow]
    have h5 : (b * w0) ^ N = 1 := by rw [hbw, one_pow]
    linear_combination ((l : Per.Acris l) * a ^ N) * h1 + (-(a ^ N * b ^ N * t * fB0 (A i j))) * h2 +
      ((l : Per.Acris l) * a ^ N * b ^ N * fB0 (A i j)) * ht + ((l : Per.Acris l) * fB0 (A i j) * b ^ N) * h4 +
      (-((l : Per.Acris l) * fB0 (A i j) * a ^ N)) * h5
  obtain ⟨Q, Q', hQQ, ⟨Y, hY⟩, ⟨Y', hY'⟩, hQ⟩ := hU (Per.Acris l) d l l N htor hcomp (phiA l) u hu
    (Fact.out : l.Prime).pos _ _ _ _ _ hα hβ hΓ n₀ (fun n hn => hn₀ (n + 1) (by omega))
  refine ⟨Q, Q', ⟨hQQ, fun i j => ⟨Y i j, ?_⟩, fun i j => ⟨Y' i j, ?_⟩, ?_⟩⟩
  · rw [hY]; rfl
  · rw [hY']; rfl
  · have key : b ^ N • (Q * A.map fB0) = a ^ N • (A.map fB * Q.map (phiA l)) := by
      rw [← mul_smul_comm, hQ, smul_mul_assoc]
    have e1 : P ^ N = (P ^ N * w0 ^ N) * b ^ N := by
      rw [mul_assoc, ← mul_pow, mul_comm w0 b, hbw, one_pow, mul_one]
    have e2 : (P ^ N * w0 ^ N) * a ^ N = ((l : Per.Acris l) * w0) ^ N := by
      rw [hv]
      calc ((l : Per.Acris l) * v) ^ N * w0 ^ N * a ^ N = ((l : Per.Acris l) * w0) ^ N * (a * v) ^ N := by ring
        _ = _ := by rw [hav, one_pow, mul_one]
    show P ^ N • (Q * A.map fB0) =
      ψ (frobS l bk.a (PowerSeries.C (PowerSeries.constantCoeff bk.E))) ^ N • (A.map fB * Q.map (phiA l))
    rw [hP0, e1, ← smul_smul, key, smul_smul, e2]

end UpperTheory.Gal.ClosedPhiFromClosedTrace

end
