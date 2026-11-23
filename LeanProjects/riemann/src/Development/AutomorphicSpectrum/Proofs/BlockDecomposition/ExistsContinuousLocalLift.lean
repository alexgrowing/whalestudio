import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.SaGen.ExLift

section Ring

variable {R S : Type} [CommRing R] [CommRing S] {M : ℕ}

def liftM (i : R →+ S) (X : Matrix (Fin M) (Fin M) R) : Matrix (Fin M) (Fin M) S :=
  1 + (X - 1).map i

theorem map_addM (i : R →+ S) (A B : Matrix (Fin M) (Fin M) R) :
    (A + B).map i = A.map i + B.map i := by
  ext a b
  simp

theorem map_mulM (i : R →+ S) (hi : ∀ x y, i (x * y) = i x * i y) (A B : Matrix (Fin M) (Fin M) R) :
    (A * B).map i = A.map i * B.map i := by
  ext a b
  simp [Matrix.mul_apply, map_sum, hi]

theorem map_zeroM (i : R →+ S) : (0 : Matrix (Fin M) (Fin M) R).map i = 0 := by
  ext a b
  simp

theorem liftM_one (i : R →+ S) : liftM i (1 : Matrix (Fin M) (Fin M) R) = 1 := by
  unfold liftM
  rw [sub_self, map_zeroM, add_zero]

theorem liftM_mul (i : R →+ S) (hi : ∀ x y, i (x * y) = i x * i y) (X Y : Matrix (Fin M) (Fin M) R) :
    liftM i (X * Y) = liftM i X * liftM i Y := by
  have h : X * Y - 1 = (X - 1) + (Y - 1) + (X - 1) * (Y - 1) := by noncomm_ring
  unfold liftM
  rw [h, map_addM, map_addM, map_mulM i hi]
  noncomm_ring

theorem cT_addM (c : R →+* R) (A B : Matrix (Fin M) (Fin M) R) :
    Formalism.UG.cT c (A + B) = Formalism.UG.cT c A + Formalism.UG.cT c B := by
  ext a b
  simp [Formalism.UG.cT]

theorem liftM_unitary (i : R →+ S) (hi : ∀ x y, i (x * y) = i x * i y) (c : R →+* R) (d : S →+* S)
    (hc : ∀ x, d (i x) = i (c x)) (J₁ : Matrix (Fin M) (Fin M) R) (J₂ : Matrix (Fin M) (Fin M) S)
    (hl : ∀ A : Matrix (Fin M) (Fin M) R, J₂ * A.map i = (J₁ * A).map i)
    (hr : ∀ A : Matrix (Fin M) (Fin M) R, A.map i * J₂ = (A * J₁).map i)
    (X : Matrix (Fin M) (Fin M) R) (hX : Formalism.UG.cT c X * J₁ * X = J₁) :
    Formalism.UG.cT d (liftM i X) * J₂ * liftM i X = J₂ := by
  obtain ⟨A, rfl⟩ : ∃ A, X = 1 + A := ⟨X - 1, by abel⟩
  have hA : (1 + A) - 1 = A := by abel
  set B := Formalism.UG.cT c A with hB
  have h0 : J₁ * A + B * J₁ + B * J₁ * A = 0 := by
    rw [cT_addM, Formalism.UG.cT_one, ← hB] at hX
    have e : (1 + B) * J₁ * (1 + A) - J₁ = J₁ * A + B * J₁ + B * J₁ * A := by noncomm_ring
    rw [← e, hX, sub_self]
  have hd : Formalism.UG.cT d (liftM i (1 + A)) = 1 + B.map i := by
    unfold liftM
    rw [hA, cT_addM, Formalism.UG.cT_one]
    congr 1
    ext a b
    simp [Formalism.UG.cT, hB, hc]
  rw [hd]
  unfold liftM
  rw [hA]
  have e : (1 + B.map i) * J₂ * (1 + A.map i) =
      J₂ + J₂ * A.map i + B.map i * J₂ + B.map i * J₂ * A.map i := by noncomm_ring
  rw [e, hr B, hl A, ← map_mulM i hi, add_assoc, add_assoc, ← map_addM, ← map_addM, ← add_assoc (J₁ * A), h0,
    map_zeroM, add_zero]

def liftH (i : R →+ S) (hi : ∀ x y, i (x * y) = i x * i y) :
    Matrix (Fin M) (Fin M) R →* Matrix (Fin M) (Fin M) S where
  toFun := liftM i
  map_one' := liftM_one i
  map_mul' := liftM_mul i hi

end Ring

section Tens

variable {F E K : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [Field K] [Algebra F K]
  [TopologicalSpace K]

theorem iB_tmul (P : PlaceMap F K) (a : K) (e : E) :
    iB P (a ⊗ₜ[F] e : K ⊗[F] E) = P.inj a ⊗ₜ[F] e := rfl

theorem iB_mul (P : PlaceMap F K) (x y : K ⊗[F] E) : iB P (x * y) = iB P x * iB P y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [add_mul, map_add, ha, hb]
  | tmul a e =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add p q hp hq => simp only [mul_add, map_add, hp, hq]
    | tmul b f => simp only [Algebra.TensorProduct.tmul_mul_tmul, iB_tmul, map_mul]

theorem iB_sig (P : PlaceMap F K) (σ : E →ₐ[F] E) (x : K ⊗[F] E) :
    sigR (AF F) σ (iB P x) = iB P (sigR K σ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a e => rfl

theorem incl_mul_iB (P : PlaceMap F K) (t : E) (y : K ⊗[F] E) :
    inclR (AF F) t * iB P y = iB P (inclR K t * y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [mul_add, map_add, ha, hb]
  | tmul a e =>
    change ((1 : AF F) ⊗ₜ[F] t) * (P.inj a ⊗ₜ[F] e) = iB P (((1 : K) ⊗ₜ[F] t) * (a ⊗ₜ[F] e))
    simp only [Algebra.TensorProduct.tmul_mul_tmul, iB_tmul, one_mul]

theorem iB_eq_coord [Module.Finite F E] (P : PlaceMap F K) {d : ℕ} (b : Module.Basis (Fin d) F E) (y : K ⊗[F] E) :
    iB P y = (Algebra.TensorProduct.basis (AF F) b).equivFun.symm
      (fun k => P.inj ((Algebra.TensorProduct.basis K b).equivFun y k)) := by
  apply (Algebra.TensorProduct.basis (AF F) b).equivFun.injective
  rw [LinearEquiv.apply_symm_apply]
  funext k
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add p q hp hq => simp only [map_add, Pi.add_apply, hp, hq]
  | tmul a e =>
    rw [iB_tmul]
    simp only [Module.Basis.equivFun_apply, Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply,
      Finsupp.mapRange_apply, smul_eq_mul]
    rw [show a * algebraMap F K (b.repr e k) = b.repr e k • a by rw [Algebra.smul_def, Algebra.commutes],
      map_smul, Algebra.smul_def, Algebra.commutes]

theorem continuous_iB [IsTopologicalRing K] [Module.Finite F E] (P : PlaceMap F K) :
    Continuous (iB P : K ⊗[F] E →ₗ[F] AF F ⊗[F] E) := by
  haveI : IsModuleTopology K (K ⊗[F] E) := ⟨rfl⟩
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (K ⊗[F] E) := IsModuleTopology.toContinuousAdd K _
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _
  let b := Module.finBasis F E
  have h1 : Continuous (Algebra.TensorProduct.basis K b).equivFun.toLinearMap :=
    IsModuleTopology.continuous_of_linearMap _
  have h2 : Continuous (Algebra.TensorProduct.basis (AF F) b).equivFun.symm.toLinearMap :=
    IsModuleTopology.continuous_of_linearMap _
  have h3 : Continuous fun y : K ⊗[F] E =>
      (fun k => P.inj ((Algebra.TensorProduct.basis K b).equivFun y k) : Fin _ → AF F) :=
    continuous_pi fun k => P.cont_inj.comp ((continuous_apply k).comp h1)
  have h4 := h2.comp h3
  convert h4 using 1
  funext y
  exact iB_eq_coord P b y

end Tens

section Group

variable {F E K : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [Field K] [Algebra F K]
  [TopologicalSpace K]

def iBa (P : PlaceMap F K) : K ⊗[F] E →+ AF F ⊗[F] E := (iB P).toAddMonoidHom

theorem iBa_mul (P : PlaceMap F K) (x y : K ⊗[F] E) : iBa (E := E) P (x * y) = iBa P x * iBa P y := iB_mul P x y

theorem JR_mul_map (P : PlaceMap F K) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (A : Matrix (Fin M) (Fin M) (K ⊗[F] E)) :
    JR (AF F) J * A.map (iBa P) = (JR K J * A).map (iBa P) := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, JR]
  exact Finset.sum_congr rfl fun k _ => incl_mul_iB P (J a k) (A k b)

theorem map_mul_JR (P : PlaceMap F K) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (A : Matrix (Fin M) (Fin M) (K ⊗[F] E)) :
    A.map (iBa P) * JR (AF F) J = (A * JR K J).map (iBa P) := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, JR]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm, mul_comm (A a k)]
  exact incl_mul_iB P (J k b) (A a k)

def liftGL (P : PlaceMap F K) (M : ℕ) : GL (Fin M) (K ⊗[F] E) →* GL (Fin M) (AF F ⊗[F] E) :=
  Units.map (liftH (iBa P) (iBa_mul P))

theorem liftGL_mem (P : PlaceMap F K) (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (x : HR K σ J) : liftGL P M x.1 ∈ HR (AF F) σ J :=
  liftM_unitary (iBa P) (iBa_mul P) (sigR K σ) (sigR (AF F) σ) (iB_sig P σ) (JR K J) (JR (AF F) J)
    (JR_mul_map P J) (map_mul_JR P J) _ x.2

def liftHA (P : PlaceMap F K) (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    HA K σ J →* HA (AF F) σ J :=
  ((liftGL P M).comp (HR K σ J).subtype).codRestrict (HR (AF F) σ J) (liftGL_mem P σ J)

theorem liftHA_isLift (P : PlaceMap F K) (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    IsLift P σ J (liftHA P σ J) := by
  intro x i j
  change ((1 + (((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)) - 1).map (iBa P)) - 1) i j = _
  rw [add_sub_cancel_left]
  rfl

theorem continuous_liftHA [IsTopologicalRing K] [Module.Finite F E] (P : PlaceMap F K) (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) : Continuous (liftHA P σ J) := by
  haveI : IsModuleTopology K (K ⊗[F] E) := ⟨rfl⟩
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (K ⊗[F] E) := IsModuleTopology.isTopologicalRing K _
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hi : Continuous (iBa (E := E) P) := continuous_iB P
  have hm : Continuous (liftH (M := M) (iBa P) (iBa_mul (E := E) P)) := by
    refine continuous_matrix fun a b => ?_
    change Continuous fun X : Matrix (Fin M) (Fin M) (K ⊗[F] E) =>
      (1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) a b + iBa P (X a b - (1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)) a b)
    exact continuous_const.add (hi.comp ((continuous_id.matrix_elem a b).sub continuous_const))
  have hu : Continuous (liftGL (E := E) P M) := Continuous.units_map _ hm
  exact Continuous.subtype_mk (hu.comp continuous_subtype_val) _

end Group

end GlobalTheory.CompanionTheory.SaGen.ExLift

namespace GlobalTheory.CompanionTheory.SaGen.ExLift

theorem exists_continuous_lift : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ {K : Type} [NontriviallyNormedField K] [Algebra F K] (P : PlaceMap F K),
      ∃ L : HA K σ J →* HA (AF F) σ J, Continuous L ∧ IsLift P σ J L := by
  intro F E _ _ _ _ _ σ _ M J _ K _ _ P
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  exact ⟨liftHA P σ J, continuous_liftHA P σ J, liftHA_isLift P σ J⟩

end GlobalTheory.CompanionTheory.SaGen.ExLift
