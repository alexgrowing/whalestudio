import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutEtaB
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepBI
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PLocalLatticeIndex

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
open PositivityTheory.ThKW PositivityTheory.ThKW.AutEtaA
open UpperTheory.TP.W

private theorem exists_unit {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) :
    ∃ u : (FiniteAdeleRing (𝓞 E) E)ˣ, Valued.v ((u : FiniteAdeleRing (𝓞 E) E) P) = WithZero.exp (-1 : ℤ) ∧
      ∀ Q, Q ≠ P → (u : FiniteAdeleRing (𝓞 E) E) Q = 1 := by
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer E P
  have hv : Valued.v (algebraMap E (P.adicCompletion E) π) = WithZero.exp (-1 : ℤ) :=
    (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P π).trans hπ
  have h0 : algebraMap E (P.adicCompletion E) π ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  let x : (P.adicCompletion E)ˣ := Units.mk0 _ h0
  refine ⟨Units.map (RingHom.snd _ _).toMonoidHom (Neutral.B1.localIdele E P x), ?_, fun Q hQ => ?_⟩
  · show Valued.v (((Neutral.B1.localIdele E P x : _) : AdeleRing (𝓞 E) E).2 P) = _
    rw [Neutral.B1.localIdele_snd_self]
    exact hv
  · exact (Neutral.B1.localIdele_isSupportedAt E P x).2 Q hQ

private theorem fin_lift {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (y : Af F ⊗[F] E) : finPartF F E (PositivityTheory.ThKW.LatB.liftF F E y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a t => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

private theorem inf_lift {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (y : Af F ⊗[F] E) : infPartF F E (PositivityTheory.ThKW.LatB.liftF F E y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a t => exact TensorProduct.zero_tmul _ _
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

private theorem exists_idele (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) :
    ∃ z : (AEF F E)ˣ, wv F E P z = WithZero.exp (-1 : ℤ) ∧ ∀ Q, Q ≠ P → wv F E Q z = 1 := by
  obtain ⟨u, hu1, hu2⟩ := exists_unit P
  obtain ⟨a, ha⟩ := (finAdEquiv F E).surjective (u : FiniteAdeleRing (𝓞 E) E)
  obtain ⟨b, hb⟩ := (finAdEquiv F E).surjective ((u⁻¹ : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E)
  have hab : a * b = 1 := (finAdEquiv F E).injective (by rw [map_mul, ha, hb, Units.mul_inv, map_one])
  have key : (PositivityTheory.ThKW.LatB.liftF F E a + (1 - finIdem F E)) * (PositivityTheory.ThKW.LatB.liftF F E b + (1 - finIdem F E)) = 1 := by
    rw [← sub_eq_zero]
    refine GlobalTheory.SplitDetCharF.adele_tensor_ext _ ?_ ?_
    · simp only [map_sub, map_mul, map_add, map_one, inf_lift, infPartF_finIdem, zero_add, sub_zero, mul_one, sub_self, map_zero]
    · simp only [map_sub, map_mul, map_add, map_one, fin_lift, PositivityTheory.ThKW.TauSpanIdentities.finPartF_finIdem, sub_self, add_zero, hab, map_zero]
  let z : (AEF F E)ˣ := ⟨_, _, key, by rw [mul_comm]; exact key⟩
  have hev : ∀ Q, ev F E Q (z : AEF F E) = (u : FiniteAdeleRing (𝓞 E) E) Q := by
    intro Q
    have h1 : finPartF F E (z : AEF F E) = a := by
      show finPartF F E (PositivityTheory.ThKW.LatB.liftF F E a + (1 - finIdem F E)) = a
      rw [map_add, map_sub, map_one, fin_lift, PositivityTheory.ThKW.TauSpanIdentities.finPartF_finIdem, sub_self, add_zero]
    show evalV E Q (finAdEquiv F E (finPartF F E (z : AEF F E))) = _
    rw [h1, ha]
    rfl
  refine ⟨z, ?_, fun Q hQ => ?_⟩
  · rw [wv_apply, hev, hu1]
  · rw [wv_apply, hev, hu2 Q hQ, map_one]

theorem UpperTheory.exists_sign_heckeChar_at_nonfixed_place :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (lam : ℕ →* ℂ)
        (κ : (AEF F E)ˣ →* Circle), IsKap σ lam κ → ∀ P : HeightOneSpectrum (𝓞 E), ¬ Fx σ P →
        ∃ s : Circle, s * s = 1 ∧ lam (Ideal.absNorm P.asIdeal) = (s : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ∧
          ∀ (x : (AEF F E)ˣ) (m : ℤ), (∀ Q, Q ≠ P → wv F E Q x = 1) → wv F E P x = WithZero.exp m → κ x = s ^ m := by
  intro F E _ _ _ _ _ σ lam κ hκ P hP
  obtain ⟨z, hz1, hz2⟩ := exists_idele F E P
  refine ⟨κ z, hκ.sq z, hκ.gen P hP z hz1 hz2, fun x m hx1 hx2 => ?_⟩
  have hpow : ∀ Q, wv F E Q (z ^ m) = wv F E Q z ^ m := fun Q =>
    map_zpow' (wv F E Q) (fun y => eq_inv_of_mul_eq_one_left (by rw [← map_mul, inv_mul_cancel, map_one])) z m
  have h1 : κ (x * z ^ m) = 1 := by
    refine hκ.ker _ fun Q _ => ?_
    by_cases hQ : Q = P
    · subst hQ
      rw [map_mul, hpow, hx2, hz1, ← WithZero.exp_zsmul, ← WithZero.exp_add]
      simp
    · rw [map_mul, hpow, hx1 Q hQ, hz2 Q hQ, _root_.one_zpow, one_mul]
  rw [map_mul, map_zpow] at h1
  have h2 : κ z ^ m * κ z ^ m = 1 := by
    rw [← mul_zpow, hκ.sq z, _root_.one_zpow]
  exact mul_right_cancel (h1.trans h2.symm)
