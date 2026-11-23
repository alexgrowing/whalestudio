import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryLiftDetOneApproxPair
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorFieldOrSplitIdempotent

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.SaGen.NotCompact

open GlobalTheory.CompanionTheory.SaGen.LiftPlane (det_qr qr_mulVec iB_mul_one_tmul sigR_incl hform_incV)

section Ring

variable {R : Type} [CommRing R] {M : ℕ}

theorem hform_add_right (c : R →+* R) (Jm : Matrix (Fin M) (Fin M) R) (x y z : Fin M → R) :
    Formalism.UG.hform c Jm x (y + z) = Formalism.UG.hform c Jm x y + Formalism.UG.hform c Jm x z := by
  simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hform_smul_right (c : R →+* R) (Jm : Matrix (Fin M) (Fin M) R) (x y : Fin M → R) (k : R) :
    Formalism.UG.hform c Jm x (k • y) = k * Formalism.UG.hform c Jm x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_add_left (c : R →+* R) (Jm : Matrix (Fin M) (Fin M) R) (x y z : Fin M → R) :
    Formalism.UG.hform c Jm (x + y) z = Formalism.UG.hform c Jm x z + Formalism.UG.hform c Jm y z := by
  simp only [Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem hform_smul_left (c : R →+* R) (Jm : Matrix (Fin M) (Fin M) R) (x y : Fin M → R) (k : R) :
    Formalism.UG.hform c Jm (k • x) y = c k * Formalism.UG.hform c Jm x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_conj (c : R →+* R) (hc : ∀ x, c (c x) = x) (Jm : Matrix (Fin M) (Fin M) R)
    (hJ : ∀ i j, c (Jm j i) = Jm i j) (x y : Fin M → R) :
    c (Formalism.UG.hform c Jm x y) = Formalism.UG.hform c Jm y x := by
  simp only [Formalism.UG.hform, map_sum, map_mul, hc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]
  ring

theorem mul_vmv (A : Matrix (Fin M) (Fin M) R) (x y : Fin M → R) :
    A * Matrix.vecMulVec x y = Matrix.vecMulVec (A.mulVec x) y := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]

theorem vmv_mul (A : Matrix (Fin M) (Fin M) R) (x y : Fin M → R) :
    Matrix.vecMulVec x y * A = Matrix.vecMulVec x (Matrix.vecMul y A) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.vecMul, dotProduct, Finset.mul_sum, mul_assoc]

theorem qr_unitary (c : R →+* R) (hc : ∀ x, c (c x) = x) (Jm : Matrix (Fin M) (Fin M) R)
    (hJ : ∀ i j, c (Jm j i) = Jm i j) (u : Fin M → R) (k : R) (hk : k + c k = 0)
    (hu : Formalism.UG.hform c Jm u u = 0) :
    Formalism.UG.cT c (qr c Jm u k) * Jm * qr c Jm u k = Jm := by
  obtain ⟨v, hv⟩ : ∃ v : Fin M → R, v = fun j => ∑ i, c (u i) * Jm i j := ⟨_, rfl⟩
  have hq : qr c Jm u k = 1 + k • Matrix.vecMulVec u v := by rw [hv]; rfl
  have hcv : ∀ i, c (v i) = Jm.mulVec u i := by
    intro i
    simp only [hv, map_sum, map_mul, hc, Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hJ]
    ring
  have hvu : dotProduct v u = 0 := by
    rw [← hu]
    simp only [hv, dotProduct, Formalism.UG.hform, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hvJ : Matrix.vecMul (fun i => c (u i)) Jm = v := by
    rw [hv]
    ext j
    simp only [Matrix.vecMul, dotProduct]
  have hcT : Formalism.UG.cT c (qr c Jm u k) = 1 + c k • Matrix.vecMulVec (Jm.mulVec u) (fun i => c (u i)) := by
    rw [hq]
    ext i j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, smul_eq_mul, map_add, map_mul, hcv]
    have h1 : c ((1 : Matrix (Fin M) (Fin M) R) j i) = (1 : Matrix (Fin M) (Fin M) R) i j := by
      by_cases h : i = j
      · subst h; simp
      · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h), map_zero]
    rw [h1]
    ring
  have hA : Matrix.vecMulVec (Jm.mulVec u) (fun i => c (u i)) * Jm = Matrix.vecMulVec (Jm.mulVec u) v := by
    rw [vmv_mul, hvJ]
  have hN : Matrix.vecMulVec (Jm.mulVec u) v * Matrix.vecMulVec u v = 0 := by
    have h0 : (Matrix.vecMulVec (Jm.mulVec u) v).mulVec u = 0 := by
      ext i
      have h1 : ∑ j, Jm.mulVec u i * v j * u j = Jm.mulVec u i * dotProduct v u := by
        simp only [dotProduct, Finset.mul_sum, mul_assoc]
      simp only [Matrix.mulVec.eq_1 (Matrix.vecMulVec _ _), dotProduct, Matrix.vecMulVec_apply, Pi.zero_apply]
      rw [h1, hvu, mul_zero]
    rw [mul_vmv, h0]
    ext i j
    simp [Matrix.vecMulVec_apply]
  rw [hcT, hq]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hA,
    mul_vmv Jm, hN, smul_zero, add_zero]
  rw [add_assoc, ← add_smul, add_comm (c k) k, hk, zero_smul, add_zero]

end Ring

section Lift

variable {F E K : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [NontriviallyNormedField K] [Algebra F K]

def pB (P : PlaceMap F K) : AF F ⊗[F] E →ₐ[F] K ⊗[F] E :=
  Algebra.TensorProduct.map P.proj (AlgHom.id F E)

theorem pB_iB (P : PlaceMap F K) (y : K ⊗[F] E) : pB P (iB P y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul k e => simp [pB, iB, P.proj_inj]
  | add y z hy hz => rw [map_add, map_add, hy, hz]

def cd (ψ : E →ₗ[F] F) : AF F ⊗[F] E →ₗ[AF F] AF F :=
  (TensorProduct.AlgebraTensorModule.rid F (AF F) (AF F)).toLinearMap ∘ₗ ψ.baseChange (AF F)

def phi (K : Type) [CommRing K] [Algebra F K] (ψ : E →ₗ[F] F) : K ⊗[F] E →ₗ[K] K :=
  (TensorProduct.AlgebraTensorModule.rid F K K).toLinearMap ∘ₗ ψ.baseChange K

theorem cd_tmul (ψ : E →ₗ[F] F) (a : AF F) (e : E) : cd ψ (a ⊗ₜ[F] e) = ψ e • a := by
  simp [cd]

theorem phi_tmul (ψ : E →ₗ[F] F) (k : K) (e : E) : phi K ψ (k ⊗ₜ[F] e) = ψ e • k := by
  simp [phi]

theorem continuous_cd (ψ : E →ₗ[F] F) : Continuous (cd ψ) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  exact IsModuleTopology.continuous_of_linearMap (cd ψ)

theorem pB_eq_sum (P : PlaceMap F K) (B : Module.Basis (Fin 2) F E) (x : AF F ⊗[F] E) :
    pB P x = ∑ i, P.proj (cd (B.coord i) x) • inclR K (B i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    have h : ∀ i, P.proj (cd (B.coord i) (a ⊗ₜ[F] e)) • inclR K (B i) =
        P.proj a ⊗ₜ[F] (B.coord i e • B i) := by
      intro i
      rw [cd_tmul, map_smul]
      change (B.coord i e • P.proj a) • ((1 : K) ⊗ₜ[F] B i) = _
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, TensorProduct.smul_tmul]
    simp only [h, ← TensorProduct.tmul_sum]
    have h2 : ∑ i, B.coord i e • B i = e := B.sum_repr e
    rw [h2]
    simp [pB]
  | add x y hx hy =>
    simp only [map_add, add_smul, Finset.sum_add_distrib, hx, hy]

theorem continuous_phi_pB (P : PlaceMap F K) (B : Module.Basis (Fin 2) F E) (ψ : E →ₗ[F] F) (w : K ⊗[F] E) :
    Continuous fun x : AF F ⊗[F] E => phi K ψ (w * pB P x) := by
  have h : (fun x : AF F ⊗[F] E => phi K ψ (w * pB P x)) =
      fun x => ∑ i, P.proj (cd (B.coord i) x) * phi K ψ (w * inclR K (B i)) := by
    funext x
    rw [pB_eq_sum P B, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_smul_comm, map_smul, smul_eq_mul]
  rw [h]
  exact continuous_finset_sum _ fun i _ =>
    (P.cont_proj.comp (continuous_cd (B.coord i))).mul continuous_const

variable {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}

theorem pB_lift (P : PlaceMap F K) {L : HA K σ J →* HA (AF F) σ J} (hL : IsLift P σ J L) (x : HA K σ J)
    (j l : Fin M) :
    pB P (((HA.mat (AF F) σ J (L x)).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) j l) =
      ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)) j l := by
  have h1 : ((HA.mat (AF F) σ J (L x)).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) j l =
      iB P ((((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)) - 1) j l) +
        (1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) j l := by
    rw [← hL x j l, Matrix.sub_apply, sub_add_cancel]
  have h2 : pB P ((1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) j l) =
      (1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)) j l := by
    by_cases h : j = l
    · subst h
      simp
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h, map_zero]
  rw [h1, map_add, pB_iB, h2, Matrix.sub_apply, sub_add_cancel]

theorem lift_fixes (P : PlaceMap F K) {L : HA K σ J →* HA (AF F) σ J} (hL : IsLift P σ J L) (x : HA K σ J)
    (t : Fin M → E)
    (hz : ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)).mulVec (incV K t) = incV K t) :
    ((HA.mat (AF F) σ J (L x)).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)).mulVec (vA t) = vA t := by
  have h0 : (((HA.mat (AF F) σ J (L x)).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) - 1).mulVec (vA t) = 0 := by
    ext i
    have hs : ∑ j, (((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)) - 1) i j * inclR K (t j) =
        ((((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)) - 1).mulVec (incV K t)) i := rfl
    simp only [Matrix.mulVec, dotProduct, hL x i, vA, iB_mul_one_tmul, ← map_sum, Pi.zero_apply]
    rw [hs, Matrix.sub_mulVec, hz, Matrix.one_mulVec, sub_self]
    simp
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
  exact h0

theorem exists_point (hc : ∀ t, sigR K σ (sigR K σ t) = t) (hJ : ∀ i j, σ (J j i) = J i j)
    (u : Fin M → K ⊗[F] E) (k : K ⊗[F] E) (hk : k + sigR K σ k = 0) (hu : hR K σ J u u = 0) :
    ∃ g : HA K σ J, ((HA.mat K σ J g).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)) = qr (sigR K σ) (JR K J) u k ∧
      ((HA.mat K σ J g).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)).det = 1 := by
  have hdet : (qr (sigR K σ) (JR K J) u k).det = 1 := by
    rw [det_qr]
    have hu' : Formalism.UG.hform (sigR K σ) (JR K J) u u = 0 := hu
    rw [hu', mul_zero, add_zero]
  have hJ' : ∀ i j, sigR K σ (JR K J j i) = JR K J i j := fun i j => map_mem_HermR K σ J hJ i j
  refine ⟨(⟨Matrix.GeneralLinearGroup.mk'' _ (isUnit_iff_exists_inv.2 ⟨1, (mul_one _).trans hdet⟩),
    qr_unitary _ hc _ hJ' u k hk hu⟩ : HR K σ J), rfl, hdet⟩

theorem sum_form (c : K ⊗[F] E →+* K ⊗[F] E) (Jm X : Matrix (Fin M) (Fin M) (K ⊗[F] E)) (z : Fin M → K ⊗[F] E) :
    ∑ j, ∑ l, ((∑ i, c (z i) * Jm i j) * z l) * X j l = Formalism.UG.hform c Jm z (X.mulVec z) := by
  simp only [Formalism.UG.hform, Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := fun i j => c (z i) * Jm i j * ∑ l, X j l * z l)]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring

end Lift

theorem not_isCompact_planeSupp : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ {K : Type} [NontriviallyNormedField K] [Algebra F K] (P : PlaceMap F K) (L : HA K σ J →* HA (AF F) σ J), IsLift P σ J L → (∀ x : HA K σ J, ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)).det = 1 → L x ∈ SUSupp σ J (P.inj 1)) → ∀ ε : AF F, ε * P.inj 1 = P.inj 1 → ∀ a b : Fin M → E, IsoPlane K σ J (incV K a) (incV K b) → ¬ IsCompact (PlaneSupp σ J ε a b) := by
  intro F E _ _ _ _ _ σ hCM M J hJ K _ _ P L hL hdet ε hε a b hiso hcomp
  obtain ⟨-, x, y, z, huu, huz⟩ := hiso
  obtain ⟨θ₀, d, B, -, -, hσθ, -, -, hB1⟩ := GlobalTheory.CompanionTheory.SaGen.Dichotomy.exists_theta hCM
  have hc : ∀ t, sigR K σ (sigR K σ t) = t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul k e => simp [sigR, GlobalTheory.CompanionTheory.SaGen.Dichotomy.sigma_sigma hCM]
    | add s t hs ht => rw [map_add, map_add, hs, ht]
  have hJm : ∀ i j, sigR K σ (JR K J j i) = JR K J i j := fun i j => map_mem_HermR K σ J hJ.1 i j
  obtain ⟨u, hu⟩ : ∃ u : Fin M → K ⊗[F] E, u = x • incV K a + y • incV K b := ⟨_, rfl⟩
  rw [← hu] at huu huz
  have huz' : Formalism.UG.hform (sigR K σ) (JR K J) u z = 1 := huz
  have hzu : Formalism.UG.hform (sigR K σ) (JR K J) z u = 1 := by
    rw [← hform_conj _ hc _ hJm u z, huz', map_one]
  let ψ : E →ₗ[F] F := B.coord 1
  have hψ : ψ θ₀ = 1 := by
    change B.coord 1 θ₀ = 1
    rw [← hB1]
    simp
  let kk : K → K ⊗[F] E := fun r => r ⊗ₜ[F] θ₀
  have hkk : ∀ r, kk r + sigR K σ (kk r) = 0 := by
    intro r
    have : sigR K σ (kk r) = r ⊗ₜ[F] (σ θ₀) := by simp [kk, sigR]
    rw [this, hσθ, TensorProduct.tmul_neg]
    simp [kk]
  have hphi : ∀ r, phi K ψ (kk r) = r := by
    intro r
    simp [kk, phi_tmul, hψ]
  let w : Fin M → Fin M → K ⊗[F] E := fun j l => (∑ i, sigR K σ (z i) * JR K J i j) * z l
  let Φ : HA (AF F) σ J → K := fun g => ∑ j, ∑ l, phi K ψ (w j l *
    pB P (((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) j l))
  have hΦ : Continuous Φ := by
    refine continuous_finset_sum _ fun j _ => continuous_finset_sum _ fun l _ => ?_
    have hent : Continuous fun g : HA (AF F) σ J =>
        ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) j l :=
      (Units.continuous_val.comp continuous_subtype_val).matrix_elem j l
    exact (continuous_phi_pB P B ψ (w j l)).comp hent
  obtain ⟨C, hC⟩ := (hcomp.image hΦ).isBounded.exists_norm_le
  obtain ⟨s, hs⟩ := NormedField.exists_lt_norm K C
  set C₀ := phi K ψ (Formalism.UG.hform (sigR K σ) (JR K J) z z) with hC₀
  obtain ⟨g, hg, hgd⟩ := exists_point hc hJ.1 u (kk (s - C₀)) (hkk _) huu
  have hval : Φ (L g) = s := by
    have h1 : Φ (L g) = phi K ψ (Formalism.UG.hform (sigR K σ) (JR K J) z
        (((HA.mat K σ J g).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)).mulVec z)) := by
      rw [← sum_form]
      simp only [Φ, pB_lift P hL, map_sum, w]
    rw [h1, hg, qr_mulVec, huz', mul_one, hform_add_right, hform_smul_right, hzu, mul_one, map_add, hphi, ← hC₀]
    ring
  have hmem : L g ∈ PlaneSupp σ J ε a b := by
    obtain ⟨h1, h2⟩ := hdet g hgd
    refine ⟨⟨h1, fun i j => ?_⟩, fun t hat hbt => ?_⟩
    · rw [← h2 i j, ← mul_assoc, ← map_mul, hε]
    · apply lift_fixes P hL
      rw [hg, qr_mulVec]
      have h0 : Formalism.UG.hform (sigR K σ) (JR K J) u (incV K t) = 0 := by
        rw [hu, hform_add_left, hform_smul_left, hform_smul_left, hform_incV, hform_incV, hat, hbt]
        simp
      rw [h0, mul_zero, zero_smul, add_zero]
  have := hC (Φ (L g)) ⟨L g, hmem, rfl⟩
  rw [hval] at this
  exact absurd this (not_le.2 hs)

end GlobalTheory.CompanionTheory.SaGen.NotCompact
