import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.SPartTensor

section Generic

variable {F E A R : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [Algebra F A] [CommRing R] [Algebra F R]

def tP (p : A →ₐ[F] R) : A ⊗[F] E →+* R ⊗[F] E := (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom

def tQ (s : R →ₗ[F] A) : R ⊗[F] E →+ A ⊗[F] E := (LinearMap.rTensor E s).toAddMonoidHom

@[simp] theorem rTensor_tmul₂ (p : A →ₐ[F] R) (a : A) (x : E) : tP p (a ⊗ₜ[F] x) = p a ⊗ₜ[F] x := rfl

@[simp] theorem tQ_tmul (s : R →ₗ[F] A) (r : R) (x : E) : tQ s (r ⊗ₜ[F] x) = s r ⊗ₜ[F] x := rfl

theorem rTensor_includeRight (p : A →ₐ[F] R) (x : E) : tP p (inclR (F := F) A x) = inclR (F := F) R x := by
  change tP p ((1 : A) ⊗ₜ[F] x) = (1 : R) ⊗ₜ[F] x
  rw [rTensor_tmul₂, map_one]

theorem rTensor_lTensor_comm₂ (p : A →ₐ[F] R) (σ : E →ₐ[F] E) (x : A ⊗[F] E) :
    tP p (sigR A σ x) = sigR R σ (tP p x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a y => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tQ_sigR (s : R →ₗ[F] A) (σ : E →ₐ[F] E) (y : R ⊗[F] E) :
    tQ s (sigR R σ y) = sigR A σ (tQ s y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a y => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem rTensor_rTensor_of_rightInverse (p : A →ₐ[F] R) (s : R →ₗ[F] A) (h : ∀ r, p (s r) = r) (y : R ⊗[F] E) :
    tP p (tQ s y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a y => rw [tQ_tmul, rTensor_tmul₂, h]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tQ_tP (p : A →ₐ[F] R) (s : R →ₗ[F] A) (b : A) (h : ∀ a, s (p a) = b * a) (x : A ⊗[F] E) :
    tQ s (tP p x) = (b ⊗ₜ[F] (1 : E)) * x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a y => rw [rTensor_tmul₂, tQ_tmul, h, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | add x y hx hy => simp only [map_add, hx, hy, mul_add]

theorem tQ_mul (s : R →ₗ[F] A) (h : ∀ r r', s (r * r') = s r * s r') (y y' : R ⊗[F] E) :
    tQ s (y * y') = tQ s y * tQ s y' := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, add_mul]
  | tmul a z =>
    induction y' using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy, mul_add]
    | tmul b w =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, tQ_tmul, tQ_tmul, tQ_tmul, h,
        Algebra.TensorProduct.tmul_mul_tmul]

end Generic

section Adelic

variable {F : Type} [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))

abbrev RS : Type := Ainf F × (∀ v : S, Fv F v.1)

def finOf (c : ∀ v : S, Fv F v.1) : Af F := ∑ v : S, singleFin v.1 (c v)

variable {S}

theorem evalV_finOf (c : ∀ v : S, Fv F v.1) (u : HeightOneSpectrum (𝓞 F)) (h : u ∈ S) :
    evalV F u (finOf S c) = c ⟨u, h⟩ := by
  unfold finOf
  rw [map_sum, Finset.sum_eq_single (⟨u, h⟩ : S)
    (fun b _ hb => evalV_singleFin_ne (fun e => hb (Subtype.ext e.symm)) _) (by simp)]
  exact evalV_singleFin_self u _

theorem evalV_finOf_not (c : ∀ v : S, Fv F v.1) (u : HeightOneSpectrum (𝓞 F)) (h : u ∉ S) :
    evalV F u (finOf S c) = 0 := by
  unfold finOf
  rw [map_sum]
  exact Finset.sum_eq_zero fun b _ => evalV_singleFin_ne (fun e => h (by rw [e]; exact b.2)) _

theorem af_ext {x y : Af F} (h : ∀ u, evalV F u x = evalV F u y) : x = y :=
  by first | exact RestrictedProduct.ext _ _ h | exact Subtype.ext (funext h)

variable (S)

def pS : AF F →ₐ[F] RS S :=
  (fstA F).prod (Pi.algHom F _ fun v : S => (evalV F v.1).comp (sndA F))

def sS : RS S →ₗ[F] AF F where
  toFun r := (r.1, finOf S r.2)
  map_add' r r' := by
    refine Prod.ext rfl ?_
    change finOf S (r.2 + r'.2) = finOf S r.2 + finOf S r'.2
    simp [finOf, Finset.sum_add_distrib]
  map_smul' a r := by
    refine Prod.ext rfl ?_
    change finOf S (a • r.2) = a • finOf S r.2
    simp [finOf, Finset.smul_sum]

variable {S}

theorem pS_sS (r : RS S) : pS S (sS S r) = r := by
  refine Prod.ext rfl (funext fun v => ?_)
  exact evalV_finOf r.2 v.1 v.2

theorem sS_mul (r r' : RS S) : sS S (r * r') = sS S r * sS S r' := by
  refine Prod.ext rfl (af_ext fun u => ?_)
  change evalV F u (finOf S (r.2 * r'.2)) = evalV F u (finOf S r.2 * finOf S r'.2)
  rw [map_mul]
  by_cases h : u ∈ S
  · rw [evalV_finOf _ u h, evalV_finOf _ u h, evalV_finOf _ u h]; rfl
  · rw [evalV_finOf_not _ u h, evalV_finOf_not _ u h, zero_mul]

theorem sS_pS (a : AF F) : sS S (pS S a) = sS S 1 * a := by
  refine Prod.ext (one_mul _).symm (af_ext fun u => ?_)
  change evalV F u (finOf S fun v : S => evalV F v.1 a.2) = evalV F u (finOf S 1 * a.2)
  rw [map_mul]
  by_cases h : u ∈ S
  · rw [evalV_finOf _ u h, evalV_finOf _ u h]; simp
  · rw [evalV_finOf_not _ u h, evalV_finOf_not _ u h, zero_mul]

theorem evInf_sS_one (w : InfinitePlace F) : evInf F w (sS S 1) = 1 := by
  change (GlobalTheory.AutFunCompare.evW w) (1 : Ainf F) = 1
  exact map_one _

theorem evFin_sS_one_mem {v : HeightOneSpectrum (𝓞 F)} (h : v ∈ S) : evFin F v (sS S 1) = 1 :=
  evalV_finOf _ v h

theorem evFin_sS_one_not {v : HeightOneSpectrum (𝓞 F)} (h : v ∉ S) : evFin F v (sS S 1) = 0 :=
  evalV_finOf_not _ v h

end Adelic

theorem sPartOf {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (e : AF F ⊗[F] E)
    (hinj : ∀ a : AF F ⊗[F] E, (∀ w, compInf F E w a = 0) → (∀ v, compFin F E v a = 0) → a = 0)
    (h1 : ∀ w, compInf F E w e = 1) (h2 : ∀ v ∈ S, compFin F E v e = 1) (h3 : ∀ v, v ∉ S → compFin F E v e = 0) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra F R) (_ : IsArtinianRing R) (_ : IsReduced R)
      (P : AF F ⊗[F] E →+* R ⊗[F] E) (Q : R ⊗[F] E →+ AF F ⊗[F] E),
      (∀ x, P (inclR (F := F) (AF F) x) = inclR R x) ∧ (∀ x, P (sigR (AF F) σ x) = sigR R σ (P x)) ∧
      (∀ y, Q (sigR R σ y) = sigR (AF F) σ (Q y)) ∧ (∀ y, P (Q y) = y) ∧ (∀ x, Q (P x) = e * x) ∧
      ∀ y y', Q (y * y') = Q y * Q y' := by
  have hE : e = (sS S 1 : AF F) ⊗ₜ[F] (1 : E) := by
    rw [← sub_eq_zero]
    refine hinj _ (fun w => ?_) (fun v => ?_)
    · rw [RingHom.map_sub, h1 w, sub_eq_zero]
      change (1 : _) = evInf F w (sS S 1) ⊗ₜ[F] (1 : E)
      rw [evInf_sS_one]; rfl
    · rw [RingHom.map_sub, sub_eq_zero]
      change _ = evFin F v (sS S 1) ⊗ₜ[F] (1 : E)
      by_cases h : v ∈ S
      · rw [h2 v h, evFin_sS_one_mem h]; rfl
      · rw [h3 v h, evFin_sS_one_not h, TensorProduct.zero_tmul]
  haveI : IsArtinianRing (Ainf F) := inferInstanceAs (IsArtinianRing (∀ v : InfinitePlace F, v.Completion))
  haveI : IsReduced (Ainf F) := inferInstanceAs (IsReduced (∀ v : InfinitePlace F, v.Completion))
  refine ⟨RS S, inferInstance, inferInstance, inferInstance, inferInstance, tP (pS S), tQ (sS S),
    rTensor_includeRight _, rTensor_lTensor_comm₂ _ _, tQ_sigR _ _, rTensor_rTensor_of_rightInverse _ _ pS_sS, fun x => ?_, tQ_mul _ sS_mul⟩
  rw [hE]
  exact tQ_tP _ _ _ sS_pS x

theorem sPart : (∀ (D : D7) (a : AE D), (∀ w, compInf D.host.F D.host.E w a = 0) → (∀ v, cv D v a = 0) → a = 0) →
    ∀ (D : D7) (S : Finset (Pl D)) (e : AE D), IsIdem S e →
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra D.host.F R) (_ : IsArtinianRing R) (_ : IsReduced R)
      (P : AE D →+* R ⊗[D.host.F] D.host.E) (Q : R ⊗[D.host.F] D.host.E →+ AE D),
      (∀ x, P (incA D x) = inclR R x) ∧ (∀ x, P (cA D x) = sigR R D.sp.cm.sig (P x)) ∧
      (∀ y, Q (sigR R D.sp.cm.sig y) = cA D (Q y)) ∧ (∀ y, P (Q y) = y) ∧ (∀ x, Q (P x) = e * x) ∧
      ∀ y y', Q (y * y') = Q y * Q y' := by
  intro hinj D S e he
  exact sPartOf D.sp.cm.sig S e (hinj D) he.1 (fun v h => (he.2 v).trans (if_pos h))
    (fun v h => (he.2 v).trans (if_neg h))

end GlobalTheory.CompanionTheory.SPartTensor
