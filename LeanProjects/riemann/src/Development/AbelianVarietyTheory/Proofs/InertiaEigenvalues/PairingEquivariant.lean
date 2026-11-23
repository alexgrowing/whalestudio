import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAlgebraMapPadicInt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepOnEqOfEqOne
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime.PairEquiv

section General

variable {A : Type} [CommRing A] {Y Y' : Type} [AddCommGroup Y] [Module A Y] [AddCommGroup Y'] [Module A Y'] {n r : ℕ}

theorem vecPair_matAct {β : Y →+ Y' →+ ZMod n} (hβ : Bal A β) (T : Matrix (Fin r) (Fin r) A) (x : Fin r → Y)
    (y : Fin r → Y') : vecPair r β (matAct T x) y = vecPair r β x (matAct T.transpose y) := by
  rw [vecPair_apply, vecPair_apply]
  change ∑ c, β (∑ a, T c a • x a) (y c) = ∑ a, β (x a) (∑ c, T c a • y c)
  simp only [map_sum, AddMonoidHom.finsetSum_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => hβ _ _ _

theorem vecPair_smul {β : Y →+ Y' →+ ZMod n} (hβ : Bal A β) (k : A) (x : Fin r → Y)
    (y : Fin r → Y') : vecPair r β (k • x) y = vecPair r β x (k • y) := by
  rw [vecPair_apply, vecPair_apply]
  exact Finset.sum_congr rfl fun a _ => hβ _ _ _

theorem tors_of_finite [IsLocalRing A] [Finite A] (b : Y) :
    ∃ m, ∀ x ∈ IsLocalRing.maximalIdeal A ^ m, x • b = 0 := by
  obtain ⟨m, hm⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top] at hm
  refine ⟨m, fun x hx => ?_⟩
  rw [hm, Ideal.zero_eq_bot, Ideal.mem_bot] at hx
  rw [hx, zero_smul]

theorem map_padicInt_eq_val {l : ℕ} [Fact l.Prime] (f : ℤ_[l] →+* A) {m : ℕ} (h : (l : A) ^ m = 0) (a : ℤ_[l]) :
    f a = ((PadicInt.toZModPow m a).val : A) := by
  have h1 : a - ((PadicInt.toZModPow m a).val : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZModPow m) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h1
  obtain ⟨c, hc⟩ := h1
  have h2 := congrArg f hc
  rw [map_sub, map_natCast, map_mul, map_pow, map_natCast, h, zero_mul, sub_eq_zero] at h2
  exact h2

end General

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem transpose_mul_Tdual (i : X.Tw) (s : X.Sig i) (g : GE N) :
    (Tmat i s g).transpose * Tdual i s g = ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) • 1 := by
  have h3 : IsUnit (Tmat i s g).det := by
    rw [← Tgl_coe]; exact Matrix.isUnits_det_units _
  rw [Tdual, Matrix.mul_smul, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ h3, Matrix.transpose_one]

theorem pairing_equivariant : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Setup bkP i s κ Q → Kills i A → IsDual i s ρ → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] (Y' : Type) [AddCommGroup Y'] [Module A Y'] [TopologicalSpace Y'] [DiscreteTopology Y'] (β : Y →+ Y' →+ ZMod (X.l i ^ (nu X i + 1))), Bal A β → ContAction (repOn (Tgl i s) κ Y) ∧ ContAction (repOn ρ κ⁻¹ Y') ∧ (∀ g x y, vecPair D.R.r β (repOn (Tgl i s) κ Y g x) (repOn ρ κ⁻¹ Y' g y) = ((cycMod D.host.E N.Om (X.l i) (nu X i + 1) g : (ZMod (X.l i ^ (nu X i + 1)))ˣ) : ZMod (X.l i ^ (nu X i + 1))) * vecPair D.R.r β x y) ∧ ∀ v, v ∉ placesOver D.host.E (X.l i) → v ∉ Spl i → v ∉ Q → ∀ B : ValuationSubring N.Om, IsPlaceOver B v → ∀ τ ∈ Ine (F := D.host.E) B, repOn (Tgl i s) κ Y τ = 1 ∧ repOn ρ κ⁻¹ Y' τ = 1 := by
  intro D N X bkP i s A _ _ _ _ κ Q ρ hS hK hρ Y _ _ _ _ Y' _ _ _ _ β hβ
  have := hS.2.1
  have hκ := hS.2.2.2.1
  refine ⟨?_, ?_, fun g x y => ?_, fun v hl hv hQ B hB τ hτ => ?_⟩
  · refine GlobalTheory.PrimeToInertia.contAction_repOn (X.twistBaseCoefficientRing_isAdic i) _ ?_ κ hκ tors_of_finite
    simp_rw [Tgl_coe]; exact GlobalTheory.PrimeToInertia.continuous_Tmat i s
  · refine GlobalTheory.PrimeToInertia.contAction_repOn (X.twistBaseCoefficientRing_isAdic i) _ ?_ κ⁻¹ ?_ tors_of_finite
    · simp_rw [hρ _]; exact GlobalTheory.PrimeToInertia.continuous_Tdual i s
    · convert hκ using 2
      ext g
      simp [MonoidHom.mem_ker]
  · have hl : ((X.l i : ℕ) : A) ^ (nu X i + 1) = 0 := by
      have := hK ((X.l i : X.O0 i) ^ nu X i * (X.l i : X.O0 i))
        (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (GlobalTheory.PrimeToInertia.l_mem i))
      rwa [map_mul, map_pow, map_natCast, ← pow_succ] at this
    have he : algebraMap (X.O0 i) A ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) =
        (((cycMod D.host.E N.Om (X.l i) (nu X i + 1) g : (ZMod (X.l i ^ (nu X i + 1)))ˣ) : ZMod (X.l i ^ (nu X i + 1))).val : A) :=
      map_padicInt_eq_val ((algebraMap (X.O0 i) A).comp (algebraMap ℤ_[X.l i] (X.O0 i))) hl _
    change vecPair _ β ((κ g : A) • matAct ((Tgl i s g : Matrix _ _ (X.O0 i)).map (algebraMap (X.O0 i) A)) x)
      (((κ g)⁻¹ : Aˣ).val • matAct ((ρ g : Matrix _ _ (X.O0 i)).map (algebraMap (X.O0 i) A)) y) = _
    rw [vecPair_smul hβ, smul_smul, Units.mul_inv, one_smul, vecPair_matAct hβ, ← Module.End.mul_apply, ← matAct_mul,
      ← Matrix.transpose_map, ← Matrix.map_mul, hρ, Tgl_coe, transpose_mul_Tdual]
    have e : matAct ((((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) • (1 : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i))).map
        (algebraMap (X.O0 i) A)) y =
        ((cycMod D.host.E N.Om (X.l i) (nu X i + 1) g : (ZMod (X.l i ^ (nu X i + 1)))ˣ) : ZMod (X.l i ^ (nu X i + 1))).val • y := by
      funext a
      rw [← Nat.cast_smul_eq_nsmul A, ← he]
      change ∑ b, algebraMap (X.O0 i) A (((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) * (1 : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) a b) • y b = _
      simp [Matrix.one_apply, apply_ite (algebraMap (X.O0 i) A), ite_smul]
    rw [e, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]
  · have h1 := GlobalTheory.SelFun.Colim.tgl_eq_one bkP i s hS.1.1 v hl hv B hB τ hτ
    have h2 := hS.2.2.2.2.2.2.2 v hQ B hB τ hτ
    have h3 : cycZ D.host.E N.Om (X.l i) τ = 1 := by
      refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
      rw [cycZ_toZModPow_eq hl hB (q := 1) (fun x hx => by simpa using hτ.2 x hx) n]
      simp
    have h4 : eps0 X i τ = 1 := by
      rw [eps0, MonoidHom.comp_apply, h3, map_one]
    have h5 : ρ τ = 1 := by
      apply Units.ext
      rw [hρ, Tdual, h4, ← Tgl_coe, h1]
      simp
    exact ⟨LinearMap.ext (GlobalTheory.SelFun.Colim.repOn_eq_of_eq_one _ _ h1 h2),
      LinearMap.ext (GlobalTheory.SelFun.Colim.repOn_eq_of_eq_one _ _ h5 (by simp [h2]))⟩

end GlobalTheory.NewPrime.PairEquiv
