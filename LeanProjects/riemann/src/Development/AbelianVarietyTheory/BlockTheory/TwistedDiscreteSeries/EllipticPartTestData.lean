import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots

section Poly

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (r : ℕ)

def sharp (P : E[X]) : E[X] := C (σ (P.eval 0))⁻¹ * reflect r (P.map (σ : E →+* E))

def PPol : Type := {P : E[X] // P.Monic ∧ Irreducible P ∧ P.natDegree = r ∧ P.eval 0 ≠ 0 ∧ P = sharp σ r P}

variable {σ r} (P : PPol σ r)

instance : Fact (Irreducible P.1) := ⟨P.2.2.1⟩

def Fld : Type := AdjoinRoot P.1

instance : Field (Fld P) := inferInstanceAs (Field (AdjoinRoot P.1))
instance : Algebra E (Fld P) := inferInstanceAs (Algebra E (AdjoinRoot P.1))
instance : Algebra F (Fld P) := inferInstanceAs (Algebra F (AdjoinRoot P.1))
instance : IsScalarTower F E (Fld P) := inferInstanceAs (IsScalarTower F E (AdjoinRoot P.1))
instance : Module.Finite E (Fld P) := (AdjoinRoot.powerBasis P.2.2.1.ne_zero).finite
instance [NumberField E] : NumberField (Fld P) := NumberField.of_module_finite E _

def alpha : Fld P := AdjoinRoot.root P.1

theorem eval_alpha : eval₂ (algebraMap E (Fld P)) (alpha P) P.1 = 0 := AdjoinRoot.eval₂_root P.1

theorem alpha_ne_zero : alpha P ≠ 0 := fun h => by
  have := eval_alpha P
  rw [h, eval₂_at_zero, map_eq_zero, coeff_zero_eq_eval_zero] at this
  exact P.2.2.2.2.1 this

theorem eval_inv_alpha :
    eval₂ (((IsScalarTower.toAlgHom F E (Fld P)).comp σ : E →ₐ[F] Fld P) : E →+* Fld P) (alpha P)⁻¹ P.1 = 0 := by
  have h0 := eval_alpha P
  rw [P.2.2.2.2.2, sharp, eval₂_mul, eval₂_C, mul_eq_zero, map_eq_zero, inv_eq_zero, map_eq_zero] at h0
  have h1 := h0.resolve_left P.2.2.2.2.1
  letI : Invertible (alpha P)⁻¹ := invertibleOfNonzero (inv_ne_zero (alpha_ne_zero P))
  have h2 := (eval₂_reflect_eq_zero_iff (algebraMap E (Fld P)) (alpha P)⁻¹ r (P.1.map (σ : E →+* E))
    (natDegree_map_le.trans P.2.2.2.1.le)).1 (by rwa [invOf_eq_inv, inv_inv])
  rw [eval₂_map] at h2
  exact h2

def star' : Fld P →ₐ[F] Fld P :=
  AdjoinRoot.liftAlgHom P.1 ((IsScalarTower.toAlgHom F E (Fld P)).comp σ) (alpha P)⁻¹ (eval_inv_alpha P)

theorem star'_alpha : star' P (alpha P) = (alpha P)⁻¹ := AdjoinRoot.liftAlgHom_root ..

theorem star'_algebraMap (e : E) : star' P (algebraMap E (Fld P) e) = algebraMap E (Fld P) (σ e) :=
  AdjoinRoot.liftAlgHom_of ..

abbrev one₁ : Matrix (Fin 1) (Fin 1) (Fld P) := 1

def alphaRat : Formalism.UG.UJ (star' P : Fld P →+* Fld P) (one₁ P) :=
  ⟨Matrix.GeneralLinearGroup.scalar (Fin 1) (Units.mk0 (alpha P) (alpha_ne_zero P)), by
    change Formalism.UG.cT _ _ * _ * _ = _
    ext i j
    simp [Formalism.UG.cT, Matrix.mul_apply, Subsingleton.elim i 0, Subsingleton.elim j 0, star'_alpha, alpha_ne_zero]⟩

variable (k : Type) [CommRing k] [Algebra F k]

abbrev Tor : Type := HA k (star' P) (one₁ P)

instance algBase : Algebra (k ⊗[F] E) (k ⊗[F] Fld P) :=
  (Algebra.TensorProduct.map (AlgHom.id F k) (IsScalarTower.toAlgHom F E (Fld P))).toRingHom.toAlgebra

def trBase : k ⊗[F] Fld P →ₗ[F] k ⊗[F] E := LinearMap.lTensor k ((Algebra.trace E (Fld P)).restrictScalars F)

def hx (x y y' : k ⊗[F] Fld P) : k ⊗[F] E := trBase P k (x * y * sigR k (star' P) y')

def plusUnits : Subgroup (k ⊗[F] Fld P)ˣ :=
  MonoidHom.eqLocus (Units.map (sigR k (star' P)).toMonoidHom) (MonoidHom.id _)

def norms : Subgroup (k ⊗[F] Fld P)ˣ :=
  (MonoidHom.id (k ⊗[F] Fld P)ˣ * Units.map (sigR k (star' P)).toMonoidHom).range

abbrev Cls : Type := plusUnits P k ⧸ (norms P k).subgroupOf (plusUnits P k)

variable {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

def IsIsom (x : k ⊗[F] Fld P) (φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)) : Prop :=
  ∀ y y', Formalism.UG.hform (sigR k σ) (JR k J) (φ y') (φ y) = hx P k x y y'

def XSet : Set (Cls P k) :=
  {q | ∃ (x : plusUnits P k) (φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)),
    QuotientGroup.mk x = q ∧ IsIsom P k J x.1.1 φ}

variable {P k J}

def mulMat (φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)) :
    k ⊗[F] Fld P →* Matrix (Fin n) (Fin n) (k ⊗[F] E) :=
  ((LinearMap.toMatrixAlgEquiv' (R := k ⊗[F] E) (n := Fin n)).toAlgHom.comp
    ((φ.conjAlgEquiv (k ⊗[F] E)).toAlgHom.comp (Algebra.lmul (k ⊗[F] E) (k ⊗[F] Fld P)))).toRingHom.toMonoidHom

theorem mulMat_mulVec (φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)) (z y : k ⊗[F] Fld P) :
    mulMat φ z *ᵥ φ y = φ (z * y) := by
  change LinearMap.toMatrix' (φ.conj (LinearMap.mul _ _ z)) *ᵥ φ y = _
  rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  simp [LinearEquiv.conj_apply]

def torUnit : Tor P k →* (k ⊗[F] Fld P)ˣ :=
  Matrix.GeneralLinearGroup.det.comp (HR k (star' P) (one₁ P)).subtype

theorem torUnit_norm (t : Tor P k) : (torUnit t).1 * sigR k (star' P) (torUnit t).1 = 1 := by
  have h : Formalism.UG.cT _ t.1.1 * JR k (one₁ P) * t.1.1 = JR k (one₁ P) := t.2
  have h0 := congrFun (congrFun h 0) 0
  have e : (torUnit t).1 = t.1.1 0 0 := Matrix.det_fin_one _
  rw [e, mul_comm]
  simpa [Formalism.UG.cT, Matrix.mul_apply, JR] using h0

theorem unitary_of_hform {A : Type} [CommRing A] (s : A →+* A) (G M : Matrix (Fin n) (Fin n) A)
    (h : ∀ a b, Formalism.UG.hform s G (M *ᵥ a) (M *ᵥ b) = Formalism.UG.hform s G a b) : Formalism.UG.cT s M * G * M = G := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  simp only [Formalism.UG.hform, Matrix.mulVec_single_one, Pi.single_apply, apply_ite s, map_one, map_zero, ite_mul,
    mul_ite, one_mul, mul_one, zero_mul, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
  rw [← this, Finset.sum_comm]
  simp [Formalism.UG.cT, Matrix.mul_apply, Finset.sum_mul]

def torEmb {x : k ⊗[F] Fld P} {φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)} (h : IsIsom P k J x φ) :
    Tor P k →* HA k σ J :=
  ((Units.map (mulMat φ)).comp torUnit).codRestrict (HR k σ J) fun t => unitary_of_hform _ _ _ fun a b => by
    obtain ⟨a, rfl⟩ := φ.surjective a
    obtain ⟨b, rfl⟩ := φ.surjective b
    change Formalism.UG.hform _ _ (mulMat φ (torUnit t).1 *ᵥ _) (mulMat φ (torUnit t).1 *ᵥ _) = _
    rw [mulMat_mulVec, mulMat_mulVec, h, h, hx, hx]
    refine congrArg (trBase P k) ?_
    rw [map_mul]
    linear_combination (x * b * sigR k (star' P) a) * torUnit_norm t

def gam {x : k ⊗[F] Fld P} {φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)} (h : IsIsom P k J x φ) : HA k σ J :=
  torEmb h (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.diagH (star' P) (one₁ P) k (alphaRat P))

variable [TopologicalSpace k]

def centMeas {x : k ⊗[F] Fld P} {φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)} (h : IsIsom P k J x φ)
    (dt : Measure (Tor P k)) : Measure (cent (gam h)) :=
  (dt.map (torEmb h)).comap Subtype.val

variable (dg : Measure (HA k σ J)) (dt : Measure (Tor P k)) (f : HA k σ J → ℂ)

def orbCls (q : XSet P k J) : ℂ :=
  orbInt dg (gam q.2.choose_spec.choose_spec.2) (centMeas q.2.choose_spec.choose_spec.2 dt) f

def Phi : ℂ := ∑ᶠ q : XSet P k J, orbCls dg dt f q

def PhiOK : Prop :=
  (XSet P k J).Finite ∧ ∀ (x : plusUnits P k) (φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E))
    (h : IsIsom P k J x.1.1 φ),
      HasOrbInt dg (gam h) (centMeas h dt) f (orbCls dg dt f ⟨QuotientGroup.mk x, x, φ, rfl, h⟩)

end Poly

section Weyl

variable {r : ℕ}

def glChar (μ : Fin r → ℤ) (a : Fin r → ℂ) : ℂ :=
  (Matrix.of fun i j => a i ^ (μ j + (j.rev : ℕ))).det / (Matrix.of fun i j : Fin r => a i ^ (j.rev : ℕ)).det

theorem glChar_perm (μ : Fin r → ℤ) (a : Fin r → ℂ) (s : Equiv.Perm (Fin r)) : glChar μ (a ∘ s) = glChar μ a := by
  have h1 := Matrix.det_permute s (Matrix.of fun i j => a i ^ (μ j + (j.rev : ℕ)))
  have h2 := Matrix.det_permute s (Matrix.of fun i j : Fin r => a i ^ (j.rev : ℕ))
  have hs : ((Equiv.Perm.sign s : ℤ) : ℂ) ≠ 0 := by exact_mod_cast (Equiv.Perm.sign s).ne_zero
  exact (congrArg₂ (· / ·) h1 h2).trans (mul_div_mul_left _ _ hs)

def hiWt (lam : Fin r → ℤ) : Fin r → ℤ := fun j => lam j - ((((r - 1) / 2 : ℕ) : ℤ) - (j : ℕ))

example (l : ℤ) (a : ℂ) : glChar (hiWt ![l]) ![a] = a ^ l := by simp [glChar, hiWt]

example : hiWt ![1, 0, -1] = 0 := by decide

theorem exists_roots {Q : ℂ[X]} (hm : Q.Monic) (hd : Q.natDegree = r) : ∃ a : Fin r → ℂ, Q = ∏ i, (X - C (a i)) := by
  have hc : Q.roots.card = Q.natDegree := IsAlgClosed.card_roots_eq_natDegree
  obtain ⟨l, hl⟩ := Quotient.exists_rep Q.roots
  have hl' : (l : Multiset ℂ) = Q.roots := hl
  have hlen : l.length = r := by rw [← hd, ← hc, ← hl', Multiset.coe_card]
  subst hlen
  refine ⟨l.get, ?_⟩
  rw [← prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm hc, ← hl', Multiset.map_coe, Multiset.prod_coe,
    ← Fin.prod_univ_fun_getElem]
  rfl

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}

def cxRoots (τ : E →+* ℂ) (P : PPol σ r) : Fin r → ℂ :=
  (exists_roots (P.2.1.map τ) ((natDegree_map_eq_of_injective τ.injective _).trans P.2.2.2.1)).choose

theorem cxRoots_spec (τ : E →+* ℂ) (P : PPol σ r) : P.1.map τ = ∏ i, (X - C (cxRoots τ P i)) :=
  (exists_roots (P.2.1.map τ) ((natDegree_map_eq_of_injective τ.injective _).trans P.2.2.2.1)).choose_spec

end Weyl

section Global

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ}

def IsTorusMeas (P : PPol σ r) (dta : ∀ w : InfinitePlace F, Measure (Tor P w.Completion))
    (dtf : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Tor P (Fv F v))) (dt : Measure (Tor P (AF F))) : Prop :=
  IsRestrictedProd (star' P) (one₁ P) (stdLattice (Fld P) 1) dta dtf dt

theorem exists_isTorusMeas (P : PPol σ r) : ∃ dta dtf dt, IsTorusMeas P dta dtf dt :=
  haveI := isLattice_stdLattice (E := Fld P) (n := 1)
  ⟨_, _, exists_isRestrictedProd (star' P) (one₁ P) (stdLattice (Fld P) 1)⟩

def torVol (P : PPol σ r) (dt : Measure (Tor P (AF F))) : ENNReal :=
  quotMeasure (ratPts (star' P) (one₁ P)) dt univ

open Classical in

def PhiReal (P : PPol σ r) {w : InfinitePlace F} (τ : EmbOver E w) (lam : Fin r → ℤ)
    (dt : Measure (Tor P w.Completion)) : ℂ :=
  if CompactSpace (Tor P w.Completion) then conj (glChar (hiWt lam) (cxRoots τ.1 P)) / (dt.real univ : ℂ) else 0

def unipBlock (k : Type) [Field k] (r a : ℕ) : Set (GL (Fin r) k) :=
  {g | ∀ i j : Fin r, ¬ ((i : ℕ) < a ∧ a ≤ (j : ℕ)) → g.1 i j = (1 : Matrix (Fin r) (Fin r) k) i j}

def NoFixed {J : Matrix (Fin r) (Fin r) E} {L : Submodule (𝓞 E) (Fin r → E)} (T : TypeData σ J L) : Prop :=
  T.S.Nonempty ∧ ∀ a, 0 < a → a < r → ∃ v : T.S, ∀ y : T.W v, (∀ g ∈ unipBlock (ResF v.1) r a, T.τ v g y = y) → y = 0

def Gap (lam : Fin r → ℤ) : Prop := ∀ i j : Fin r, (j : ℕ) = i + 1 → (r : ℤ) ≤ lam i - lam j

def IsLatticeConj {r' : ℕ} {J : Matrix (Fin r) (Fin r) E} {J' : Matrix (Fin r') (Fin r') E}
    (L : Submodule (𝓞 E) (Fin r → E)) (L' : Submodule (𝓞 E) (Fin r' → E)) {v : HeightOneSpectrum (𝓞 F)}
    (j : GLoc σ J v ≃ₜ* GLoc σ J' v) : Prop :=
  ∃ a : (Fin r → Fv F v ⊗[F] E) ≃ₗ[Fv F v ⊗[F] E] (Fin r' → Fv F v ⊗[F] E),
    (∀ y y', hLin σ J' (Fv F v) (a y) (a y') = hLin σ J (Fv F v) y y') ∧
    (∀ y, a y ∈ latLoc F L' v ↔ y ∈ latLoc F L v) ∧
    ∀ g y, (matHom _ σ J' (j g)).1 *ᵥ a y = a ((matHom _ σ J g).1 *ᵥ y)

example {J : Matrix (Fin r) (Fin r) E} (L : Submodule (𝓞 E) (Fin r → E)) (v : HeightOneSpectrum (𝓞 F)) :
    IsLatticeConj (σ := σ) (J := J) (v := v) L L (ContinuousMulEquiv.refl _) :=
  ⟨LinearEquiv.refl _ _, fun _ _ => rfl, fun _ => Iff.rfl, fun _ _ => rfl⟩

example : Nonempty (PPol σ 1) :=
  ⟨⟨X - C 1, monic_X_sub_C 1, irreducible_X_sub_C 1, natDegree_X_sub_C 1, by simp, by
    have : reflect 1 (X - 1 : E[X]) = 1 - X := by
      rw [reflect_sub, ← pow_one (X : E[X]), reflect_monomial, reflect_one]; simp
    simp [sharp, this]⟩⟩

end Global

section Record

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsTestData (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w))
    (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V))
    (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ) : Prop :=
  Odd V.rank ∧ (∀ ρ, Gap (lam ρ)) ∧ (∀ ρ i, M.lam ρ i = lam ρ i) ∧ NoFixed T ∧
    IsRestrictedProd D.sp.cm.sig V.gram (frameLat V) μa μf μ ∧ IsTestArchG M μa fa ∧ IsTestFin T U μf ff

section Terms

variable (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w))
  (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ)
  (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ) (P : PPol D.sp.cm.sig V.rank)
  (dta : ∀ w : InfinitePlace D.host.F, Measure (Tor P w.Completion))
  (dtf : ∀ v : HeightOneSpectrum (𝓞 D.host.F), Measure (Tor P (Fv D.host.F v)))
  (dt : Measure (Tor P (AF D.host.F)))

def term : ℂ :=
  ((torVol P dt).toReal : ℂ) * (∏ᶠ v, Phi (J := V.gram) (μf v) (dtf v) (ff v)) *
    ∏ ρ : D.what₂.Tau, PhiReal P (embOverOf D ρ) (lam ρ) (dta (placeOf D ρ))

def termOrb : ℂ :=
  ((torVol P dt).toReal : ℂ) * (∏ᶠ v, Phi (J := V.gram) (μf v) (dtf v) (ff v)) *
    ∏ w : InfinitePlace D.host.F, Phi (J := V.gram) (μa w) (dta w) (fa w)

def FinOK : Prop :=
  torVol P dt ≠ ⊤ ∧ (∀ v, PhiOK (J := V.gram) (μf v) (dtf v) (ff v)) ∧
    ∀ᶠ v in cofinite, Phi (J := V.gram) (μf v) (dtf v) (ff v) = 1

end Terms

def ellKernel (V : HSp D) (f : GA D V → ℂ) (x : GA D V) : ℂ :=
  ∑ᶠ δ : {δ : GRat D.sp.cm.sig V.gram // Irreducible δ.1.1.charpoly}, f (x⁻¹ * ratEmb D.sp.cm.sig V.gram δ.1 * x)

def GeomExpansion : Prop :=
  ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w))
    (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ),
    IsTestData V lam M T U μa μf μ fa ff →
    ∀ (dta : ∀ (P : PPol D.sp.cm.sig V.rank) (w : InfinitePlace D.host.F), Measure (Tor P w.Completion))
      (dtf : ∀ (P : PPol D.sp.cm.sig V.rank) (v : HeightOneSpectrum (𝓞 D.host.F)), Measure (Tor P (Fv D.host.F v)))
      (dt : ∀ P : PPol D.sp.cm.sig V.rank, Measure (Tor P (AF D.host.F))),
      (∀ P, IsTorusMeas P (dta P) (dtf P) (dt P)) →
      (∀ P, FinOK V μf ff P (dtf P) (dt P)) ∧
      (Function.support fun P => term V lam μf ff P (dta P) (dtf P) (dt P)).Finite ∧
      HasTrace (RopG V μ (tensor D.sp.cm.sig V.gram fa ff)) (∑ᶠ P, term V lam μf ff P (dta P) (dtf P) (dt P))

def EllipticPart : Prop :=
  ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w))
    (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V))
    (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ),
    IsTestData V lam M T U μa μf μ fa ff →
    ∀ (dta : ∀ (P : PPol D.sp.cm.sig V.rank) (w : InfinitePlace D.host.F), Measure (Tor P w.Completion))
      (dtf : ∀ (P : PPol D.sp.cm.sig V.rank) (v : HeightOneSpectrum (𝓞 D.host.F)), Measure (Tor P (Fv D.host.F v)))
      (dt : ∀ P : PPol D.sp.cm.sig V.rank, Measure (Tor P (AF D.host.F))),
      (∀ P, IsTorusMeas P (dta P) (dtf P) (dt P)) →
      (∀ P, FinOK V μf ff P (dtf P) (dt P) ∧ ∀ w, PhiOK (J := V.gram) (μa w) (dta P w) (fa w)) ∧
      (Function.support fun P => termOrb V μa μf fa ff P (dta P) (dtf P) (dt P)).Finite ∧
      Integrable (descend (GQ V) (ellKernel V (tensor D.sp.cm.sig V.gram fa ff))) (autMeasure V μ) ∧
      ∫ q, descend (GQ V) (ellKernel V (tensor D.sp.cm.sig V.gram fa ff)) q ∂autMeasure V μ =
        ∑ᶠ P, termOrb V μa μf fa ff P (dta P) (dtf P) (dt P)

def TraceEq : Prop :=
  ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w))
    (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ),
    IsTestData V lam M T U μa μf μ fa ff →
    ∀ (V' : HSp D) (hr : V'.rank = V.rank) (S' : D.what₂.Tau → SPar) (M' : DSModel V' S'),
      (∀ ρ i, M'.lam ρ i = lam ρ (i.cast hr)) →
      ∀ j : ∀ v, GLoc D.sp.cm.sig V.gram v ≃ₜ* GLoc D.sp.cm.sig V'.gram v,
        (∀ v, IsLatticeConj (frameLat V) (frameLat V') (j v)) →
        ∀ (μa' : ∀ w, Measure (GArch D.sp.cm.sig V'.gram w)) (μ' : Measure (GA D V')) [μ'.IsHaarMeasure]
          [μ'.IsMulRightInvariant] (fa' : ∀ w, GArch D.sp.cm.sig V'.gram w → ℂ),
          IsRestrictedProd D.sp.cm.sig V'.gram (frameLat V') μa' (fun v => (μf v).map (j v)) μ' →
          IsTestArchG M' μa' fa' →
          ∃ c : ℂ, HasTrace (RopG V μ (tensor D.sp.cm.sig V.gram fa ff)) c ∧
            HasTrace (RopG V' μ' (tensor D.sp.cm.sig V'.gram fa' (transfer j ff))) c

def TraceComparison : Prop := GeomExpansion ∧ EllipticPart ∧ TraceEq

end Record

end GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots
