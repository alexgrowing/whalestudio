import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameInertiaElementActsByScalar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwoMulCocycleValuesZeroOnSmallSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedRepresentationKillsSmallSubgroupStatement

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime.FormNonzero

theorem cob_of_vanish {G Λ V : Type} [Group G] [CommRing Λ] [AddCommGroup V] [Module Λ V] (π : Representation Λ G V)
    (L : Subgroup G) (hL : ∀ h ∈ L, ∀ m, π h m = m) (z : G) (d : Λ) (hd : IsUnit (d - 1)) (hz : ∀ m, π z m = d • m)
    (hc : ∀ g, g * z * g⁻¹ * z⁻¹ ∈ L) (f : G → V) (hf : ∀ g h, f (g * h) = f g + π g (f h)) (h0 : ∀ h ∈ L, f h = 0) :
    Cob π f := by
  obtain ⟨u, hu⟩ := hd
  refine ⟨((u⁻¹ : Λˣ) : Λ) • f z, fun g => ?_⟩
  have e1 : f (g * z) = f (z * g) := by
    have : g * z = (g * z * g⁻¹ * z⁻¹) * (z * g) := by group
    rw [this, hf, h0 _ (hc g), hL _ (hc g), zero_add]
  rw [hf, hf, hz] at e1
  rw [map_smul, ← smul_sub]
  have e2 : π g (f z) - f z = (d - 1) • f g := by
    rw [sub_smul, one_smul, sub_eq_sub_iff_add_eq_add, add_comm (π g (f z)), e1, add_comm]
  rw [e2, smul_smul, ← hu, Units.inv_mul, one_smul]

theorem repOn_scalar {G O Λ : Type} [Group G] [CommRing O] [CommRing Λ] [Algebra O Λ] {r : ℕ} (ρ : G →* GL (Fin r) O)
    (κ : G →* Λˣ) (Y : Type) [AddCommGroup Y] [Module Λ Y] (z : G) (d : O) (hκ : κ z = 1)
    (hz : (ρ z : Matrix (Fin r) (Fin r) O) = d • (1 : Matrix (Fin r) (Fin r) O)) (m : Fin r → Y) :
    repOn ρ κ Y z m = algebraMap O Λ d • m := by
  funext a
  simp only [repOn, matAct, MonoidHom.coe_mk, OneHom.coe_mk, hκ, hz, Units.val_one, one_smul, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.map_apply, Matrix.smul_apply, Pi.smul_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [Matrix.one_apply_ne hb.symm]
  · simp

theorem exists_bform_ne_zero : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), 0 < nu X i → ∀ (M : ℕ) (L : Subgroup (GE N)) (z : GE N), nu X i + 1 ≤ M → IsTameInertiaElementAtTwistPrime X i z → Small2 i s M L z → ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] [TopologicalSpace A] [DiscreteTopology A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Setup bkP i s κ Q → Kills i A → IsDual i s ρ → AntiHom X.cc κ → κ z = 1 → (∀ g ∈ L, κ g = 1) → ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) A) Z, Univ bkP i s κ Q Φ Z → ∀ (x₀ : Fin a → A) (j : Fin a) (c : A) (y : Z1 (repOn ρ κ⁻¹ A)), matAct Φ x₀ = 0 → x₀ j ∣ c → ¬ Cob (repOn ρ κ⁻¹ A) (fun g => ((X.l i : A) ^ nu X i * c) • y.1 g) → ∃ h ∈ L, bform (X := X) (fun g => rect (Z g) x₀) y.1 h ≠ 0 := by
  intro D N X bkP i s hl M L z hM hz hL A _ _ _ _ _ _ κ Q ρ hS hK hρ hanti hκz hκL a Φ Z hU x₀ j c y hx₀ hj hy
  by_contra hcon
  push Not at hcon
  apply hy
  obtain ⟨d, hd, hd2, hd1, he⟩ := GlobalTheory.TwSys.TameScalar.exists_scalar_tmat_of_tame_inertia D N X bkP i s z hS.1.1 hz
  obtain ⟨x, hx, -⟩ := (hU A).1 x₀ hx₀
  have hcl := GlobalTheory.T.two_mul_cocycle_values_zero_on_small_subgroup D N X bkP i s hl M L z hM hz hL A κ Q ρ hS hK hρ hanti hκz hκL x y
    (fun h hh => by rw [hx]; exact hcon h hh)
  let I : Ideal A := Ideal.span {t | ∃ h ∈ L, ∃ b, t = x.1 h b}
  have hjI : x₀ j ∈ I := by
    letI : TopologicalSpace (A ⧸ I) := ⊥
    haveI : DiscreteTopology (A ⧸ I) := ⟨rfl⟩
    have hker : matAct Φ (fun k => I.mkQ (x₀ k)) = 0 := by
      funext k
      have := congrArg I.mkQ (congrFun hx₀ k)
      simpa only [matAct, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul, Pi.zero_apply, map_zero] using this
    obtain ⟨x', hx', -⟩ := (hU (A ⧸ I)).1 _ hker
    have h0 := (hU (A ⧸ I)).2.1 _ hker (by
      rw [← hx']
      refine cob_of_vanish _ L (fun h hh m => ?_) z (algebraMap (X.O0 i) A d) (by simpa using hd1.map (algebraMap (X.O0 i) A))
        (repOn_scalar _ _ _ z _ hκz (by rw [Tgl_coe, hd])) hL.1.2.2.2.1 _ x'.2.2 (fun h hh => ?_)
      · rw [(GlobalTheory.T.twisted_representation_kills_small_subgroup D N X i s hl M L z hM hL A κ ρ hK hρ (A ⧸ I) h hh).1, hκL h hh, Units.val_one, one_smul]
      · funext b
        have e : x'.1 h b = I.mkQ (x.1 h b) := by
          rw [hx, hx']
          simp only [rect, map_sum, map_smul]
        rw [e, Pi.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact Ideal.subset_span ⟨h, hh, b, rfl⟩)
    have := congrFun h0 j
    rwa [Pi.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
  have hcI : c ∈ I := by
    obtain ⟨t, rfl⟩ := hj
    exact I.mul_mem_right _ hjI
  have hkill : ∀ t ∈ I, ∀ h' ∈ L, ∀ b, (X.l i : A) ^ nu X i * t * y.1 h' b = 0 := by
    intro t ht h' hh' b
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨h, hh, b', rfl⟩ := ht
      exact hcl h hh h' hh' b' b
    | zero => simp
    | add t t' _ _ h1 h2 => rw [mul_add, add_mul, h1, h2, add_zero]
    | smul u t _ h1 => rw [smul_eq_mul]; linear_combination u * h1
  have hρz : (ρ z : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) = ((d⁻¹ : (X.O0 i)ˣ) : X.O0 i) • 1 := by
    have hinv : (Tmat i s z)⁻¹ = ((d⁻¹ : (X.O0 i)ˣ) : X.O0 i) • 1 := by
      apply Matrix.inv_eq_left_inv
      rw [hd, Matrix.smul_mul, one_mul, smul_smul, Units.inv_mul, one_smul]
    rw [hρ z, Tdual, he, hinv, Units.val_one, one_smul, Matrix.transpose_smul, Matrix.transpose_one]
  have hdi := GlobalTheory.TwSys.TameScalar.isUnit_sub_one _ (GlobalTheory.TwSys.TameScalar.isUnit_inv_sq_sub_one d hd2)
  refine cob_of_vanish _ L (fun h hh m => ?_) z (algebraMap (X.O0 i) A ((d⁻¹ : (X.O0 i)ˣ) : X.O0 i))
    (by simpa only [map_sub, map_one] using hdi.map (algebraMap (X.O0 i) A))
    (repOn_scalar _ _ _ z _ (by simp [hκz]) hρz) hL.1.2.2.2.1 _ (fun g h => ?_) (fun h hh => ?_)
  · rw [(GlobalTheory.T.twisted_representation_kills_small_subgroup D N X i s hl M L z hM hL A κ⁻¹ ρ hK hρ A h hh).2.1]
    simp [hκL h hh]
  · rw [y.2.2, smul_add, map_smul]
  · funext b
    exact hkill c hcI h hh b

end GlobalTheory.NewPrime.FormNonzero
