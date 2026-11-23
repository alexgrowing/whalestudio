import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular

noncomputable section

open NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

def sharp (r : ℕ) (P : E[X]) : E[X] :=
  C (IsCMField.complexConj E (P.coeff 0))⁻¹ *
    reflect r (P.map (IsCMField.complexConj E : E →+* E))

def IsSelfRecip (r : ℕ) (P : E[X]) : Prop :=
  P.Monic ∧ Irreducible P ∧ P.natDegree = r ∧ P.coeff 0 ≠ 0 ∧ P = sharp E r P

def SelfRecip (r : ℕ) : Type := {P : E[X] // IsSelfRecip E r P}

variable {E}

theorem isSelfRecip_X_sub_C {a : E} (ha : a * IsCMField.complexConj E a = 1) :
    IsSelfRecip E 1 (X - C a) := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  have hc : (IsCMField.complexConj E a)⁻¹ = a := (eq_inv_of_mul_eq_one_left ha).symm
  refine ⟨monic_X_sub_C a, irreducible_X_sub_C a, natDegree_X_sub_C a, by simpa using ha0, ?_⟩
  have h1 : reflect 1 (X : E[X]) = 1 := by
    simpa using reflect_monomial (R := E) 1 1
  have h2 : C a * C (IsCMField.complexConj E a) = (1 : E[X]) := by rw [← C_mul, ha, C_1]
  simp only [sharp, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, map_neg, inv_neg, hc,
    Polynomial.map_sub, map_X, map_C, reflect_sub, h1, reflect_C, RingHom.coe_coe, pow_one]
  linear_combination (-X) * h2

instance : Nonempty (SelfRecip E 1) := ⟨⟨X - C (-1), isSelfRecip_X_sub_C (by simp)⟩⟩

variable {r : ℕ} (P : SelfRecip E r)

instance : Fact (Irreducible P.1) := ⟨P.2.2.1⟩

def Fld : Type := AdjoinRoot P.1

instance : Field (Fld P) := inferInstanceAs (Field (AdjoinRoot P.1))

instance : Algebra E (Fld P) := inferInstanceAs (Algebra E (AdjoinRoot P.1))

instance : Algebra (maximalRealSubfield E) (Fld P) where
  toSMul := inferInstance
  algebraMap := (algebraMap E (Fld P)).comp (algebraMap (maximalRealSubfield E) E)
  commutes' _ _ := mul_comm _ _
  smul_def' s y := Algebra.smul_def (s : E) y

instance : IsScalarTower (maximalRealSubfield E) E (Fld P) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance : FiniteDimensional E (Fld P) :=
  (AdjoinRoot.powerBasis (f := P.1) P.2.1.ne_zero).finite

theorem finrank_fld : Module.finrank E (Fld P) = r :=
  (AdjoinRoot.powerBasis (f := P.1) P.2.1.ne_zero).finrank.trans P.2.2.2.1

def alpha : Fld P := AdjoinRoot.root P.1

theorem root_ne_zero : AdjoinRoot.root P.1 ≠ 0 := by
  intro h
  have h1 := AdjoinRoot.eval₂_root P.1
  rw [h, eval₂_at_zero] at h1
  exact P.2.2.2.2.1 ((map_eq_zero _).1 h1)

theorem eval₂_conj_inv_root :
    P.1.eval₂ ((AdjoinRoot.of P.1).comp (IsCMField.complexConj E : E →+* E))
      (AdjoinRoot.root P.1)⁻¹ = 0 := by
  obtain ⟨-, -, hdeg, h0, hs⟩ := P.2
  have h1 := AdjoinRoot.eval₂_root P.1
  letI : Invertible (AdjoinRoot.root P.1)⁻¹ := invertibleOfNonzero (inv_ne_zero (root_ne_zero P))
  have h2 := eval₂_reflect_mul_pow (AdjoinRoot.of P.1) (AdjoinRoot.root P.1)⁻¹ r
    (P.1.map (IsCMField.complexConj E : E →+* E)) (natDegree_map_le.trans hdeg.le)
  rw [invOf_eq_inv, inv_inv, eval₂_map] at h2
  have h3 : eval₂ (AdjoinRoot.of P.1) (AdjoinRoot.root P.1) (sharp E r P.1) = 0 := by
    rw [← hs]; exact h1
  rw [sharp, eval₂_mul, eval₂_C, mul_eq_zero] at h3
  rcases h3 with h3 | h3
  · exact absurd h3 ((_root_.map_ne_zero _).2 (inv_ne_zero ((_root_.map_ne_zero _).2 h0)))
  · rw [← h2, h3, zero_mul]

def invol : Fld P →ₐ[maximalRealSubfield E] Fld P where
  toRingHom := AdjoinRoot.lift ((AdjoinRoot.of P.1).comp (IsCMField.complexConj E : E →+* E))
    (AdjoinRoot.root P.1)⁻¹ (eval₂_conj_inv_root P)
  commutes' s := by
    change AdjoinRoot.lift _ _ (eval₂_conj_inv_root P)
      (AdjoinRoot.of P.1 (algebraMap _ E s)) = AdjoinRoot.of P.1 (algebraMap _ E s)
    rw [AdjoinRoot.lift_of, RingHom.comp_apply, RingHom.coe_coe, AlgEquiv.commutes]

theorem invol_algebraMap (e : E) :
    invol P (algebraMap E (Fld P) e) = algebraMap E (Fld P) (IsCMField.complexConj E e) :=
  AdjoinRoot.lift_of (eval₂_conj_inv_root P)

theorem invol_alpha : invol P (alpha P) = (alpha P)⁻¹ :=
  AdjoinRoot.lift_root (eval₂_conj_inv_root P)

theorem invol_invol (y : Fld P) : invol P (invol P y) = y := by
  have : ((invol P : Fld P →+* Fld P).comp (invol P : Fld P →+* Fld P)) = RingHom.id _ := by
    refine AdjoinRoot.ringHom_ext (RingHom.ext fun e => ?_) ?_
    · change invol P (invol P (algebraMap E (Fld P) e)) = algebraMap E (Fld P) e
      simp [invol_algebraMap]
    · change invol P (invol P (alpha P)) = alpha P
      simp [invol_alpha]
  exact DFunLike.congr_fun this y

def plus : Subalgebra (maximalRealSubfield E) (Fld P) :=
  AlgHom.equalizer (invol P) (AlgHom.id _ _)

section Local

variable (k : Type) [CommRing k] [Algebra (maximalRealSubfield E) k]

def inclPlus : k ⊗[maximalRealSubfield E] plus P →ₐ[k] k ⊗[maximalRealSubfield E] Fld P :=
  Algebra.TensorProduct.map (AlgHom.id k k) (plus P).val

def inclBase : k ⊗[maximalRealSubfield E] E →ₐ[k] k ⊗[maximalRealSubfield E] Fld P :=
  Algebra.TensorProduct.map (AlgHom.id k k) (IsScalarTower.toAlgHom (maximalRealSubfield E) E (Fld P))

def involBase : k ⊗[maximalRealSubfield E] Fld P →ₐ[k] k ⊗[maximalRealSubfield E] Fld P :=
  Algebra.TensorProduct.map (AlgHom.id k k) (invol P)

def traceBase : k ⊗[maximalRealSubfield E] Fld P →ₗ[k] k ⊗[maximalRealSubfield E] E :=
  ((Algebra.trace E (Fld P)).restrictScalars (maximalRealSubfield E)).baseChange k

def traceForm (x : k ⊗[maximalRealSubfield E] plus P) (y y' : k ⊗[maximalRealSubfield E] Fld P) :
    k ⊗[maximalRealSubfield E] E :=
  traceBase P k (inclPlus P k x * y * involBase P k y')

def normHom : (k ⊗[maximalRealSubfield E] Fld P)ˣ →* (k ⊗[maximalRealSubfield E] Fld P)ˣ :=
  MonoidHom.id _ * Units.map (involBase P k).toMonoidHom

def norms : Subgroup (k ⊗[maximalRealSubfield E] plus P)ˣ :=
  (normHom P k).range.comap (Units.map (inclPlus P k).toMonoidHom)

abbrev NormClass : Type := (k ⊗[maximalRealSubfield E] plus P)ˣ ⧸ norms P k

def gramForm (G : Matrix (Fin r) (Fin r) E) (u u' : Fin r → k ⊗[maximalRealSubfield E] E) :
    k ⊗[maximalRealSubfield E] E :=
  ∑ i, ∑ j, u i * ((1 : k) ⊗ₜ[maximalRealSubfield E] G i j) * GlobalTheory.HermLocal.ccBase E k (u' j)

def Isometric (G : Matrix (Fin r) (Fin r) E) (x : k ⊗[maximalRealSubfield E] plus P) : Prop :=
  ∃ φ : (k ⊗[maximalRealSubfield E] Fld P) ≃+ (Fin r → k ⊗[maximalRealSubfield E] E),
    (∀ (e : k ⊗[maximalRealSubfield E] E) y, φ (inclBase P k e * y) = e • φ y) ∧
    ∀ y y', gramForm k G (φ y) (φ y') = traceForm P k x y y'

theorem Isometric.of_norm {G : Matrix (Fin r) (Fin r) E}
    {x n : (k ⊗[maximalRealSubfield E] plus P)ˣ} (hn : n ∈ norms P k)
    (h : Isometric P k G x) : Isometric P k G (x * n : (k ⊗[maximalRealSubfield E] plus P)ˣ) := by
  obtain ⟨c, hc⟩ := hn
  have hc' : (c : k ⊗[maximalRealSubfield E] Fld P) * involBase P k c = inclPlus P k n :=
    congrArg Units.val hc
  obtain ⟨φ, h1, h2⟩ := h
  refine ⟨(AddAut.mulLeft c).trans φ, fun e y => ?_, fun y y' => ?_⟩
  · change φ (c * (inclBase P k e * y)) = e • φ (c * y)
    rw [← h1, mul_left_comm]
  · change gramForm k G (φ (c * y)) (φ (c * y')) = _
    rw [h2, traceForm, traceForm, Units.val_mul, map_mul (inclPlus P k), map_mul (involBase P k), ← hc']
    congr 1
    ring

def classes (G : Matrix (Fin r) (Fin r) E) : Set (NormClass P k) :=
  {q | ∃ x : (k ⊗[maximalRealSubfield E] plus P)ˣ, (x : NormClass P k) = q ∧ Isometric P k G x}

def toLocalPlus : maximalRealSubfield E ⊗[maximalRealSubfield E] plus P →ₐ[maximalRealSubfield E]
    k ⊗[maximalRealSubfield E] plus P :=
  Algebra.TensorProduct.map (Algebra.ofId _ k) (AlgHom.id _ _)

def toLocalFld : maximalRealSubfield E ⊗[maximalRealSubfield E] Fld P →ₐ[maximalRealSubfield E]
    k ⊗[maximalRealSubfield E] Fld P :=
  Algebra.TensorProduct.map (Algebra.ofId _ k) (AlgHom.id _ _)

theorem norms_le : norms P (maximalRealSubfield E) ≤
    (norms P k).comap (Units.map (toLocalPlus P k).toMonoidHom) := by
  rintro n ⟨c, hc⟩
  have hc' : (c : maximalRealSubfield E ⊗[maximalRealSubfield E] Fld P) * involBase P _ c =
      inclPlus P _ n := congrArg Units.val hc
  have e1 : ∀ y, toLocalFld P k (involBase P _ y) = involBase P k (toLocalFld P k y) := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [toLocalFld, involBase]
    | add a b ha hb => simp only [map_add, ha, hb]
  have e2 : ∀ y, toLocalFld P k (inclPlus P _ y) = inclPlus P k (toLocalPlus P k y) := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [toLocalFld, toLocalPlus, inclPlus]
    | add a b ha hb => simp only [map_add, ha, hb]
  refine ⟨Units.map (toLocalFld P k).toMonoidHom c, Units.ext ?_⟩
  change toLocalFld P k c * involBase P k (toLocalFld P k c) = inclPlus P k (toLocalPlus P k n)
  rw [← e1, ← e2, ← map_mul, hc']

def toLocal : NormClass P (maximalRealSubfield E) →* NormClass P k :=
  QuotientGroup.map _ _ (Units.map (toLocalPlus P k).toMonoidHom) (norms_le P k)

end Local

def IsLocalInteger (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
    (z : v.adicCompletion (maximalRealSubfield E) ⊗[maximalRealSubfield E] plus P) : Prop :=
  ((algebraMap (v.adicCompletion (maximalRealSubfield E))
      (v.adicCompletion (maximalRealSubfield E) ⊗[maximalRealSubfield E] plus P)).comp
    (v.adicCompletionIntegers (maximalRealSubfield E)).subtype).IsIntegralElem z

def IsUnitClass (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
    (q : NormClass P (v.adicCompletion (maximalRealSubfield E))) : Prop :=
  ∃ u : (v.adicCompletion (maximalRealSubfield E) ⊗[maximalRealSubfield E] plus P)ˣ,
    IsLocalInteger P v u ∧ IsLocalInteger P v (u⁻¹ : _ˣ) ∧
      (u : NormClass P (v.adicCompletion (maximalRealSubfield E))) = q

abbrev LocalFamily : Type :=
  (∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)),
      NormClass P (v.adicCompletion (maximalRealSubfield E))) ×
    ∀ w : InfinitePlace (maximalRealSubfield E), NormClass P w.Completion

def adelicClasses (G : Matrix (Fin r) (Fin r) E) : Set (LocalFamily P) :=
  {x | (∀ v, x.1 v ∈ classes P _ G) ∧ (∀ w, x.2 w ∈ classes P _ G) ∧
    {v | ¬ IsUnitClass P v (x.1 v)}.Finite}

def diagonal (q : NormClass P (maximalRealSubfield E)) : LocalFamily P :=
  (fun _ => toLocal P _ q, fun _ => toLocal P _ q)

def RationalEqAdelic : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) →
    ∀ (r : ℕ) (G : Matrix (Fin r) (Fin r) E),
      (∀ a b, IsCMField.complexConj E (G a b) = G b a) → G.det ≠ 0 →
      ∀ P : SelfRecip E r,
        Set.BijOn (diagonal P) (classes P (maximalRealSubfield E) G) (adelicClasses P G)

end GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField

end
