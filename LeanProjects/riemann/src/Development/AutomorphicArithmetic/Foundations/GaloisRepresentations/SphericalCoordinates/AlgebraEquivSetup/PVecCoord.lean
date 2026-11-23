import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.VecCoord
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

private lemma one_tmul_smul_eq_add_of_algebraMap_eq_add {M R : Type} [AddCommGroup M] [CommRing R] [Algebra ℚ R] (r : R) (q : ℚ) (y : M) :
    (r ⊗ₜ[ℚ] (q ⊗ₜ[ℤ] y : ℚ ⊗[ℤ] M)) = (q • r) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] y : ℚ ⊗[ℤ] M) := by
  rw [TensorProduct.smul_tmul, TensorProduct.smul_tmul']
  simp

theorem UpperTheory.Gal.W2.Seed.pVecCoord :
    LatCoord → EvEx → VecCoord := by
  intro hLat hEv E _ _ _ A n p _ S T
  obtain ⟨ν, hν1, hν2, hν3⟩ := hLat E A n p S T.μ T.mu
  choose ev hev using fun (w : Plc E) (hw : (p : 𝓞 E) ∉ w.asIdeal) => hEv p E T.toAdT w hw
  let co : ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → (AfP p ⊗[ℚ] VQ S.D →+ (Fin n → w.adicCompletion E)) := fun w hw =>
    { toFun := fun v i => ev w hw (ν v i)
      map_zero' := by ext i; simp
      map_add' := fun x y => by ext i; simp }
  let vec : ∀ w : Plc E, AfP p ⊗[ℚ] VQ S.D →+ (Fin n → w.adicCompletion E) := fun w =>
    if hw : (p : 𝓞 E) ∉ w.asIdeal then co w hw else 0
  have hvec : ∀ w (hw : (p : 𝓞 E) ∉ w.asIdeal) v i, vec w v i = ev w hw (ν v i) := fun w hw v i => by
    simp only [vec, dif_pos hw]; rfl
  have hE : ∀ w (hw : (p : 𝓞 E) ∉ w.asIdeal) (c : 𝓞 E), ev w hw ((1 : AfP p) ⊗ₜ[ℚ] (c : E)) = algebraMap (𝓞 E) (w.adicCompletion E) c := by
    intro w hw c
    rw [← T.Φ_E, hev]
    rfl
  have hν4 : ∀ (r : AfP p) (q : ℚ) (y : Fin n → 𝓞 E) i, ν (r ⊗ₜ[ℚ] ((q ⊗ₜ[ℤ] (y : S.D.La) : VQ S.D))) i = (q • r) ⊗ₜ[ℚ] (y i : E) := by
    intro r q y i
    exact (congrArg (fun z => ν z i) (one_tmul_smul_eq_add_of_algebraMap_eq_add (M := S.D.La) r q y)).trans (hν1 _ y i)
  refine ⟨vec, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v h
    apply ν.injective
    rw [map_zero]
    funext i
    obtain ⟨x, hx⟩ := T.Φ_surj (ν v i)
    rw [Pi.zero_apply, ← hx, T.Φ_ker]
    intro w hw
    have := congrFun (h w hw) i
    rw [hvec w hw, ← hx, hev] at this
    exact this
  · intro v
    rw [hν3]
    constructor
    · intro h w hw i
      obtain ⟨x, hx⟩ := T.Φ_surj (ν v i)
      have := (T.Φ_int x).1 (hx ▸ h i) w hw
      rw [hvec w hw, ← hx, hev]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 this
    · intro h i
      obtain ⟨x, hx⟩ := T.Φ_surj (ν v i)
      rw [← hx, T.Φ_int]
      intro w hw
      have := h w hw i
      rw [hvec w hw, ← hx, hev] at this
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 this
  · intro y hy
    let x : Fin n → Af E := fun i => ⟨fun w => y w i, Filter.Eventually.of_forall fun w => hy w i⟩
    refine ⟨ν.symm (fun i => T.Φ (x i)), fun w hw => ?_⟩
    funext i
    rw [hvec w hw, ν.apply_symm_apply, hev]
    rfl
  · intro w hw y i
    rw [hvec w hw, ← hE w hw]
    congr 1
    exact hν1 1 y i
  · intro w hw g v
    funext i
    rw [hvec w hw, hν2, T.j_mx, RingHom.map_mulVec]
    have hG : GeneralLinearGroup.map (pLoc E w) T.a * comp w g * (GeneralLinearGroup.map (pLoc E w) T.a)⁻¹ =
        GeneralLinearGroup.map (pLoc E w) (T.a * mat g * T.a⁻¹) := by
      simp [UpperTheory.Gal.CertificateRingHomMap.comp]
    have hM : (((T.a * mat g * T.a⁻¹ : GL (Fin n) (Af E)).val).map T.Φ).map (ev w hw) =
        (GeneralLinearGroup.map (pLoc E w) (T.a * mat g * T.a⁻¹)).val := by
      exact Matrix.ext fun a b => hev w hw _
    have hV : (ev w hw) ∘ (ν v) = vec w v := funext fun k => (hvec w hw v k).symm
    rw [hM, hV, hG]
  · intro w hw c v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, smul_add]
    | tmul r u =>
      induction u using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => rw [TensorProduct.tmul_add, map_add, map_add, hx, hy, map_add, smul_add]
      | tmul q y =>
        let y' : Fin n → 𝓞 E := y
        have key : UpperTheory.Gal.Int.Geo.mulF S.D c (r ⊗ₜ[ℚ] (q ⊗ₜ[ℤ] y)) =
            r ⊗ₜ[ℚ] ((q ⊗ₜ[ℤ] ((c • y' : Fin n → 𝓞 E) : S.D.La) : VQ S.D)) := by
          simp only [UpperTheory.Gal.Int.Geo.mulF, LinearMap.baseChange_tmul, actQ]
          rfl
        funext i
        have e2 : ν (r ⊗ₜ[ℚ] (q ⊗ₜ[ℤ] y)) i = (q • r) ⊗ₜ[ℚ] (y' i : E) := hν4 r q y' i
        have e3 : (((c • y') i : 𝓞 E) : E) = (c : E) * (y' i : E) := by simp [Pi.smul_apply]
        rw [key, Pi.smul_apply, hvec w hw, hvec w hw, hν4, e2, e3, ← hE w hw, smul_eq_mul, ← map_mul (ev w hw),
          Algebra.TensorProduct.tmul_mul_tmul, one_mul]
