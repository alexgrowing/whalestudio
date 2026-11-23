import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameInertiaElementActsByScalar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanTopOfResidue
import Development.AutomorphicArithmetic.CyclotomicBounds.CyclotomicOrders.ExistsCycZPowNeOne
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.PolarTraceMulVecMulVecEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedRepresentationKillsSmallSubgroup

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
open Matrix

namespace GlobalTheory.NewPrime.FormVanish

def twMat {Γ O A : Type} [Group Γ] [CommRing O] [CommRing A] [Algebra O A] {r : ℕ} (ρ : Γ →* GL (Fin r) O) (κ : Γ →* Aˣ) :
    Γ →* Matrix (Fin r) (Fin r) A where
  toFun g := ((κ g : Aˣ) : A) • (ρ g : Matrix (Fin r) (Fin r) O).map (algebraMap O A)
  map_one' := by simp
  map_mul' g h := by
    simp only [map_mul, Units.val_mul, Matrix.map_mul]
    rw [smul_mul_smul_comm]

theorem twMat_apply {Γ O A : Type} [Group Γ] [CommRing O] [CommRing A] [Algebra O A] {r : ℕ} (ρ : Γ →* GL (Fin r) O)
    (κ : Γ →* Aˣ) (g : Γ) :
    twMat ρ κ g = ((κ g : Aˣ) : A) • (ρ g : Matrix (Fin r) (Fin r) O).map (algebraMap O A) := rfl

theorem repOn_twMat {Γ O A : Type} [Group Γ] [CommRing O] [CommRing A] [Algebra O A] {r : ℕ} (ρ : Γ →* GL (Fin r) O)
    (κ : Γ →* Aˣ) (g : Γ) (v : Fin r → A) : repOn ρ κ A g v = twMat ρ κ g *ᵥ v := by
  funext a
  simp [repOn, matAct, twMat_apply, mulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem eq_one_of_mulVec {A : Type} [CommRing A] {r : ℕ} (M : Matrix (Fin r) (Fin r) A) (h : ∀ v, M *ᵥ v = v) : M = 1 := by
  ext a b
  have := congrFun (h (Pi.single b 1)) a
  simpa [Matrix.one_apply, Pi.single_apply] using this

theorem auxiliaryCharacter_complexConj_invariant {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw)
    (g : GE N) : eps0 X i (cConj X g) = eps0 X i g := by
  have e : MulSemiringAction.toRingAut (GE N) N.Om (cConj X g) =
      (X.cc : RingAut N.Om) * MulSemiringAction.toRingAut (GE N) N.Om g * (X.cc : RingAut N.Om)⁻¹ := by
    ext x; rfl
  have : cycZ D.host.E N.Om (X.l i) (cConj X g) = cycZ D.host.E N.Om (X.l i) g := by
    simp only [cycZ, MonoidHom.comp_apply]
    rw [e, map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  simp only [eps0, MonoidHom.comp_apply]
  rw [this]

theorem two_mul_values_eq_zero : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), 0 < nu X i → ∀ (M : ℕ) (L : Subgroup (GE N)) (z : GE N), nu X i + 1 ≤ M → IsTameInertiaElementAtTwistPrime X i z → Small2 i s M L z → ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] [TopologicalSpace A] [DiscreteTopology A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Setup bkP i s κ Q → Kills i A → IsDual i s ρ → AntiHom X.cc κ → κ z = 1 → (∀ g ∈ L, κ g = 1) → ∀ (x : Z1 (repOn (Tgl i s) κ A)) (y : Z1 (repOn ρ κ⁻¹ A)), (∀ h ∈ L, bform (X := X) x.1 y.1 h = 0) → ∀ h ∈ L, ∀ h' ∈ L, ∀ a b, (X.l i : A) ^ nu X i * x.1 h a * y.1 h' b = 0 := by
  intro D N X bkP i s hl M L z hM hz hL A _ _ _ _ _ _ κ Q ρ hS hK hρ hκ hκz hκL x y hb
  obtain ⟨J, hJ⟩ := hS.1.2.2.1
  obtain ⟨d, hd, hd2, -, hε⟩ := GlobalTheory.TwSys.TameScalar.exists_scalar_tmat_of_tame_inertia D N X bkP i s z hS.1.1 hz
  obtain ⟨g₀, u, hu⟩ := UpperTheory.KStar.exists_eps_eq_pow_nu X i
  set φ := algebraMap (X.O0 i) A with hφ
  set T := twMat (Tgl i s) κ with hT
  set T' := twMat ρ κ⁻¹ with hT'
  let χ : GE N →* A := (powMonoidHom D.R.t).comp (φ.toMonoidHom.comp ((Units.coeHom _).comp (eps0 X i)))
  have hχ : ∀ g, χ g = φ ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) ^ D.R.t := fun g => rfl
  let J' : GL (Fin D.R.r) A := Units.map φ.mapMatrix.toMonoidHom J
  have hJ1 : (J' : Matrix (Fin D.R.r) (Fin D.R.r) A) = (J : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map φ := rfl
  have hJ2 : ((J'⁻¹ : GL (Fin D.R.r) A) : Matrix (Fin D.R.r) (Fin D.R.r) A) =
      ((J⁻¹ : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map φ := rfl
  let d' : Aˣ := Units.map φ.toMonoidHom d
  have hd' : (d' : A) = φ d := rfl
  have e₁ : ∀ g, T g = ((κ g : Aˣ) : A) • (Tmat i s g).map φ := fun g => by rw [hT, twMat_apply, Tgl_coe]
  have sd : ∀ g, T' (cConj X g) = (J' : Matrix (Fin D.R.r) (Fin D.R.r) A) * (χ g • T g) *
      ((J'⁻¹ : GL (Fin D.R.r) A) : Matrix (Fin D.R.r) (Fin D.R.r) A) := fun g => by
    rw [hT', twMat_apply, hρ, hJ g _ (cConj_apply X g), Matrix.map_mul, Matrix.map_mul, e₁, hJ1, hJ2,
      MonoidHom.inv_apply, antiHom_cConj X hκ, inv_inv, ← smul_mul_assoc, ← mul_smul_comm, hχ]
    congr 2
    ext a b
    simp [hφ, mul_left_comm]
  have z₁ : T z = (d' : A) • (1 : Matrix (Fin D.R.r) (Fin D.R.r) A) := by
    rw [e₁, hd, hκz]
    ext a b
    simp [hd', Matrix.one_apply, apply_ite φ]
  have z₂ : T' z = ((d'⁻¹ : Aˣ) : A) • (1 : Matrix (Fin D.R.r) (Fin D.R.r) A) := by
    have h1 : (Tmat i s z)⁻¹ = ((d⁻¹ : (X.O0 i)ˣ) : X.O0 i) • (1 : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) := by
      apply Matrix.inv_eq_left_inv
      rw [hd, smul_mul_smul_comm, Units.inv_mul, mul_one, one_smul]
    have h2 : ((d'⁻¹ : Aˣ) : A) = φ ((d⁻¹ : (X.O0 i)ˣ) : X.O0 i) := rfl
    rw [hT', twMat_apply, hρ, Tdual, hε, h1, MonoidHom.inv_apply, hκz, h2]
    generalize ((d⁻¹ : (X.O0 i)ˣ) : X.O0 i) = e
    ext a b
    by_cases hab : a = b
    · subst hab; simp [hφ]
    · simp [hab]
  have hχz : χ z = 1 := by rw [hχ, hε]; simp
  have z₃ : T' (cConj X z) = (d' : A) • (1 : Matrix (Fin D.R.r) (Fin D.R.r) A) := by
    rw [sd, hχz, one_smul, z₁, Matrix.mul_smul, mul_one, Matrix.smul_mul, Units.mul_inv]
  have z₄ : T (cConj X z) = ((d'⁻¹ : Aˣ) : A) • (1 : Matrix (Fin D.R.r) (Fin D.R.r) A) := by
    have h1 := sd (cConj X z)
    have h3 : χ (cConj X z) = 1 := by rw [← hχz, hχ, hχ, auxiliaryCharacter_complexConj_invariant]
    rw [cConj_cConj, z₂, h3, one_smul] at h1
    have h4 : T (cConj X z) = ((J'⁻¹ : GL (Fin D.R.r) A) : Matrix (Fin D.R.r) (Fin D.R.r) A) *
        ((J' : Matrix (Fin D.R.r) (Fin D.R.r) A) * T (cConj X z) *
          ((J'⁻¹ : GL (Fin D.R.r) A) : Matrix (Fin D.R.r) (Fin D.R.r) A)) * J' := by
      rw [← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, mul_assoc, Units.inv_mul, mul_one]
    rw [h4, ← h1, Matrix.mul_smul, mul_one, Matrix.smul_mul, Units.inv_mul]
  have key := KStar.Tree.twist_mul_coord_eq_zero (GE N) A D.R.r T T' χ (cConj X) J' L z d' x.1 y.1
    (by
      have := GlobalTheory.NewPrime.Burnside.span_twist_eq_top D N X bkP i s A κ Q hS
      rwa [← funext e₁] at this) sd hL.1.2.1
    (fun h hh => (hL.1.2.2.1 h _ (cConj_apply X h)).1 hh)
    (fun h hh => ⟨eq_one_of_mulVec _ fun v => by
        rw [← repOn_twMat, (GlobalTheory.NewPrime.SmallActs.small_acts D N X i s hl M L z hM hL A κ ρ hK hρ A h hh).1, hκL h hh,
          Units.val_one, one_smul],
      eq_one_of_mulVec _ fun v => by
        rw [← repOn_twMat, (GlobalTheory.NewPrime.SmallActs.small_acts D N X i s hl M L z hM hL A κ⁻¹ ρ hK hρ A h hh).2.1,
          MonoidHom.inv_apply, hκL h hh, inv_one, Units.val_one, one_smul]⟩) z₁ z₂ z₄ z₃
    (by simpa [hd'] using hd2.map φ)
    (fun g h => by rw [← repOn_twMat]; exact x.2.2 g h) (fun g h => by rw [← repOn_twMat]; exact y.2.2 g h)
    (fun h hh => sub_eq_zero.1 (hb h hh)) g₀
  have hχ0 : χ g₀ ^ D.R.r - 1 = (X.l i : A) ^ nu X i * φ ((u : (X.O0 i)ˣ) : X.O0 i) := by
    have e := congrArg φ hu
    rw [map_sub, map_pow, map_one, map_mul, map_pow, map_natCast] at e
    rw [hχ, ← pow_mul, e]
  intro h hh h' hh' a b
  have e := key h hh h' hh' a b
  rw [hχ0] at e
  refine ((u.isUnit.map φ).mul_right_eq_zero).1 ?_
  linear_combination e

end GlobalTheory.NewPrime.FormVanish
