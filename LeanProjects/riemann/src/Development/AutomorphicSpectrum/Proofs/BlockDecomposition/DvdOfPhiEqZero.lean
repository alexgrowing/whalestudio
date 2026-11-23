import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTUnitsLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonsplitCentraliserNormElement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetGramRatOneNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjSelfReciprocalOfDvdEllipticPolynomial
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField

noncomputable section
namespace GlobalTheory.CompanionTheory.LocAssembly

def tensorLift {R A B T : Type} [CommRing R] [CommRing A] [CommRing B] [CommRing T] [Algebra R A] [Algebra R B]
    (a : A →+* T) (b : B →+* T) (h : ∀ x : R, a (algebraMap R A x) = b (algebraMap R B x)) : A ⊗[R] B →+* T :=
  letI : Algebra R T := (a.comp (algebraMap R A)).toAlgebra
  (Algebra.TensorProduct.lift (⟨a, fun _ => rfl⟩ : A →ₐ[R] T) (⟨b, fun x => (h x).symm⟩ : B →ₐ[R] T)
    (fun _ _ => Commute.all _ _)).toRingHom

theorem tensorLift_tmul {R A B T : Type} [CommRing R] [CommRing A] [CommRing B] [CommRing T] [Algebra R A]
    [Algebra R B] (a : A →+* T) (b : B →+* T) (h : ∀ x : R, a (algebraMap R A x) = b (algebraMap R B x))
    (x : A) (y : B) : tensorLift a b h (x ⊗ₜ y) = a x * b y := by
  letI : Algebra R T := (a.comp (algebraMap R A)).toAlgebra
  exact Algebra.TensorProduct.lift_tmul _ _ _ x y

theorem exists_common {ι A : Type} [Finite ι] [CommRing A] {R : ι → Type} [∀ i, CommRing (R i)]
    (φ : ∀ i, A →+* R i) (hs : ∀ i, Function.Surjective (φ i)) (q : ι → A) (hq : ∀ i, φ i (q i) = 0)
    (hc : Pairwise (Function.onFun IsCoprime q)) (z : ∀ i, R i) : ∃ f : A, ∀ i, φ i f = z i := by
  choose x hx using fun i => hs i (z i)
  have hcop : Pairwise (Function.onFun IsCoprime fun i => Ideal.span {q i}) := by
    intro i i' hne
    simp only [Function.onFun]
    rw [Ideal.isCoprime_span_singleton_iff]
    exact hc hne
  obtain ⟨f, hf⟩ := Ideal.exists_forall_sub_mem_ideal hcop x
  refine ⟨f, fun i => ?_⟩
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.1 (hf i)
  rw [← hx i, ← sub_eq_zero, ← map_sub, hd, map_mul, hq, zero_mul]

theorem aeval_intertwine {K : Type} [Field K] {n : ℕ} (B C H : Matrix (Fin n) (Fin n) K) (h : B * H = H * C)
    (p : K[X]) : aeval B p * H = H * aeval C p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, add_mul, mul_add, hp, hq]
  | monomial d a =>
    have hpow : B ^ d * H = H * C ^ d := by
      induction d with
      | zero => simp
      | succ d ih => rw [pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, ← pow_succ]
    simp only [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, Matrix.smul_mul,
      Matrix.mul_smul, hpow]

theorem tmul_split {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (a : A) (y : B) :
    (a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] y) = a ⊗ₜ[R] y := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
  {k : Type} [CommRing k] [Algebra (maximalRealSubfield E) k]
  {K : Type} [Field K] [Algebra E K]

def phi (j : K ≃+* k ⊗[maximalRealSubfield E] E) {r : ℕ} (Q : SelfRecip E r) :
    K[X] →+* k ⊗[maximalRealSubfield E] Fld Q :=
  eval₂RingHom ((inclBase Q k).toRingHom.comp j.toRingHom) ((1 : k) ⊗ₜ alpha Q)

section
variable (j : K ≃+* k ⊗[maximalRealSubfield E] E) {r : ℕ} (Q : SelfRecip E r)

theorem phi_C (x : K) : phi j Q (C x) = inclBase Q k (j x) := eval₂_C _ _

theorem phi_X : phi j Q X = (1 : k) ⊗ₜ alpha Q := eval₂_X _ _

variable (hj1 : ∀ e : E, j (algebraMap E K e) = (1 : k) ⊗ₜ e)
include hj1

theorem phi_map (p : E[X]) : phi j Q (p.map (algebraMap E K)) = (1 : k) ⊗ₜ (AdjoinRoot.mk Q.1 p : Fld Q) := by
  let g : Fld Q →+* k ⊗[maximalRealSubfield E] Fld Q :=
    (Algebra.TensorProduct.includeRight : Fld Q →ₐ[maximalRealSubfield E] k ⊗[maximalRealSubfield E] Fld Q).toRingHom
  have e : ((inclBase Q k).toRingHom.comp j.toRingHom).comp (algebraMap E K) = g.comp (algebraMap E (Fld Q)) :=
    RingHom.ext fun e => by
      change inclBase Q k (j (algebraMap E K e)) = _
      rw [hj1]
      simp [inclBase, g]
  change eval₂ ((inclBase Q k).toRingHom.comp j.toRingHom) ((1 : k) ⊗ₜ alpha Q) (p.map (algebraMap E K)) = _
  rw [eval₂_map, e]
  refine (Polynomial.hom_eval₂ p (algebraMap E (Fld Q)) g (alpha Q)).symm.trans ?_
  change (1 : k) ⊗ₜ eval₂ (algebraMap E (Fld Q)) (alpha Q) p = _
  rw [← aeval_def]
  congr 1
  exact AdjoinRoot.aeval_eq p

theorem phi_surjective : Function.Surjective (phi j Q) := by
  intro y
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | add a b ha hb =>
    obtain ⟨x, rfl⟩ := ha
    obtain ⟨y, rfl⟩ := hb
    exact ⟨x + y, map_add _ _ _⟩
  | tmul a y =>
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective y
    refine ⟨C (j.symm (a ⊗ₜ 1)) * p.map (algebraMap E K), ?_⟩
    rw [map_mul, phi_C, phi_map j Q hj1, RingEquiv.apply_symm_apply]
    have h1 : inclBase Q k (a ⊗ₜ (1 : E)) = a ⊗ₜ[maximalRealSubfield E] (1 : Fld Q) := by simp [inclBase]
    rw [h1]
    exact tmul_split a _

omit hj1 in
theorem eval₂_root_map : eval₂ ((AdjoinRoot.of (Q.1.map (algebraMap E K))).comp (algebraMap E K))
    (AdjoinRoot.root (Q.1.map (algebraMap E K))) Q.1 = 0 := by
  have h := AdjoinRoot.eval₂_root (Q.1.map (algebraMap E K))
  rwa [eval₂_map] at h

omit hj1 in

def psiB : Fld Q →+* AdjoinRoot (Q.1.map (algebraMap E K)) :=
  AdjoinRoot.lift ((AdjoinRoot.of (Q.1.map (algebraMap E K))).comp (algebraMap E K))
    (AdjoinRoot.root (Q.1.map (algebraMap E K))) (eval₂_root_map Q)

omit hj1 in
theorem psiB_algebraMap (e : E) : psiB (K := K) Q (algebraMap E (Fld Q) e) = AdjoinRoot.of _ (algebraMap E K e) :=
  AdjoinRoot.lift_of (eval₂_root_map Q)

omit hj1 in
theorem psiB_alpha : psiB (K := K) Q (alpha Q) = AdjoinRoot.root _ :=
  AdjoinRoot.lift_root (eval₂_root_map Q)

def psi : k ⊗[maximalRealSubfield E] Fld Q →+* AdjoinRoot (Q.1.map (algebraMap E K)) :=
  tensorLift
    ((AdjoinRoot.of (Q.1.map (algebraMap E K))).comp
      (j.symm.toRingHom.comp (Algebra.TensorProduct.includeLeftRingHom : k →+* k ⊗[maximalRealSubfield E] E)))
    (psiB Q)
    (fun x => by
      have h1 : (algebraMap (maximalRealSubfield E) k x) ⊗ₜ[maximalRealSubfield E] (1 : E) =
          (1 : k) ⊗ₜ algebraMap (maximalRealSubfield E) E x := by
        rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
      have h2 : j.symm ((1 : k) ⊗ₜ algebraMap (maximalRealSubfield E) E x) =
          algebraMap E K (algebraMap (maximalRealSubfield E) E x) := by
        rw [RingEquiv.symm_apply_eq, hj1]
      have h3 : algebraMap (maximalRealSubfield E) (Fld Q) x =
          algebraMap E (Fld Q) (algebraMap (maximalRealSubfield E) E x) := rfl
      change AdjoinRoot.of _ (j.symm ((algebraMap (maximalRealSubfield E) k x) ⊗ₜ 1)) = psiB Q _
      rw [h1, h2, h3, psiB_algebraMap])

theorem psi_tmul (a : k) (y : Fld Q) : psi j Q hj1 (a ⊗ₜ[maximalRealSubfield E] y) =
    AdjoinRoot.of _ (j.symm (a ⊗ₜ 1)) * psiB Q y :=
  tensorLift_tmul _ _ _ a y

theorem psi_inclBase (y : k ⊗[maximalRealSubfield E] E) :
    psi j Q hj1 (inclBase Q k y) = AdjoinRoot.of _ (j.symm y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a e =>
    have h0 : inclBase Q k (a ⊗ₜ e) = a ⊗ₜ[maximalRealSubfield E] algebraMap E (Fld Q) e := by
      simp [inclBase]
    have h2 : j.symm ((1 : k) ⊗ₜ e) = algebraMap E K e := by rw [RingEquiv.symm_apply_eq, hj1]
    have h3 : j.symm (a ⊗ₜ e) = j.symm (a ⊗ₜ 1) * j.symm ((1 : k) ⊗ₜ e) := by
      rw [← map_mul, tmul_split]
    rw [h0, psi_tmul, psiB_algebraMap, h3, map_mul, h2]

theorem psi_phi (g : K[X]) : psi j Q hj1 (phi j Q g) = AdjoinRoot.mk _ g := by
  have : (psi j Q hj1).comp (phi j Q) = AdjoinRoot.mk (Q.1.map (algebraMap E K)) := by
    refine Polynomial.ringHom_ext (fun x => ?_) ?_
    · rw [RingHom.comp_apply, phi_C, psi_inclBase, RingEquiv.symm_apply_apply]
      rfl
    · rw [RingHom.comp_apply, phi_X, psi_tmul, psiB_alpha]
      have h2 : j.symm ((1 : k) ⊗ₜ[maximalRealSubfield E] (1 : E)) = 1 := by
        rw [RingEquiv.symm_apply_eq, map_one]; rfl
      rw [h2, map_one, one_mul]
      exact AdjoinRoot.mk_X.symm
  exact DFunLike.congr_fun this g

theorem dvd_of_phi_eq_zero {g : K[X]} (h : phi j Q g = 0) : Q.1.map (algebraMap E K) ∣ g := by
  have := psi_phi j Q hj1 g
  rw [h, map_zero] at this
  exact AdjoinRoot.mk_eq_zero.1 this.symm

omit hj1 in

theorem involBase_phi (cK : K →+* K)
    (hj2 : ∀ x, j (cK x) = Algebra.TensorProduct.map (AlgHom.id (maximalRealSubfield E) k)
      ((IsCMField.complexConj E : E ≃ₐ[maximalRealSubfield E] E) : E →ₐ[maximalRealSubfield E] E) (j x))
    (R : K[X]) (hR : phi j Q R = (1 : k) ⊗ₜ (alpha Q)⁻¹) (f : K[X]) :
    involBase Q k (phi j Q f) = phi j Q ((f.map cK).comp R) := by
  let ι : K →+* k ⊗[maximalRealSubfield E] Fld Q := (inclBase Q k).toRingHom.comp j.toRingHom
  let ib : k ⊗[maximalRealSubfield E] Fld Q →+* k ⊗[maximalRealSubfield E] Fld Q := (involBase Q k).toRingHom
  have hιc : ∀ y, involBase Q k (ι y) = ι (cK y) := by
    intro y
    change involBase Q k (inclBase Q k (j y)) = inclBase Q k (j (cK y))
    rw [hj2]
    generalize j y = t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [inclBase, involBase, invol_algebraMap]
    | add a b ha hb => simp only [map_add, ha, hb]
  have e1 : ib.comp ι = ι.comp cK := RingHom.ext fun y => hιc y
  have e2 : ib ((1 : k) ⊗ₜ alpha Q) = (1 : k) ⊗ₜ (alpha Q)⁻¹ := by
    change (1 : k) ⊗ₜ invol Q (alpha Q) = _
    rw [invol_alpha]
  change ib (eval₂ ι _ f) = eval₂ ι _ _
  rw [Polynomial.hom_eval₂, e1, e2, eval₂_comp, eval₂_map]
  exact congrArg (fun x => eval₂ (ι.comp cK) x f) hR.symm

end

theorem aeval_map_mat' {n : ℕ} (M : Matrix (Fin n) (Fin n) E) (p : E[X]) :
    aeval (M.map (algebraMap E K)) (p.map (algebraMap E K)) = (aeval M p).map (algebraMap E K) := by
  rw [aeval_map_algebraMap]
  have := aeval_algHom_apply (AlgHom.mapMatrix (Algebra.ofId E K)) M p
  have e : (⇑(Algebra.ofId E K) : E → _) = algebraMap E _ := rfl
  simpa [AlgHom.mapMatrix_apply, e] using this

theorem final_calc {K : Type} [Field K] {n : ℕ} (A H' : Matrix (Fin n) (Fin n) K) (cK : K →+* K) (f m R : K[X])
    (T : Matrix (Fin n) (Fin n) K) (hint : cT cK A * H' = H' * aeval A R)
    (hkey : aeval A ((f.map cK).comp R) * aeval A m * aeval A f = T) :
    H' * T = cT cK (aeval A f) * (H' * aeval A m) * aeval A f := by
  have e := aeval_intertwine _ _ _ hint (f.map cK)
  rw [← aeval_comp] at e
  rw [← hkey, GlobalTheory.NormInert.cT_aeval, ← Matrix.mul_assoc (aeval (cT cK A) _) H', e]
  simp only [Matrix.mul_assoc]

theorem assembly (j : K ≃+* k ⊗[maximalRealSubfield E] E) (hj1 : ∀ e : E, j (algebraMap E K e) = (1 : k) ⊗ₜ e)
    (cK : K →+* K)
    (hj2 : ∀ x, j (cK x) = Algebra.TensorProduct.map (AlgHom.id (maximalRealSubfield E) k)
      ((IsCMField.complexConj E : E ≃ₐ[maximalRealSubfield E] E) : E →ₐ[maximalRealSubfield E] E) (j x))
    {n : ℕ} (γ₀ : GL (Fin n) E) (hell : γ₀.val.charpoly ∈ Ell E n) (H₀ : Matrix (Fin n) (Fin n) E)
    (hinv : cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀)
    (m : K[X]) (t : E[X])
    (hz : ∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly →
      ∃ z : (k ⊗[maximalRealSubfield E] Fld Q)ˣ,
        phi j Q m * ((z : k ⊗[maximalRealSubfield E] Fld Q) * involBase Q k (z : k ⊗[maximalRealSubfield E] Fld Q)) =
          phi j Q (t.map (algebraMap E K))) :
    ∃ c : GL (Fin n) K, c.val * (γ₀.val.map (algebraMap E K)) = (γ₀.val.map (algebraMap E K)) * c.val ∧
      (H₀ * aeval γ₀.val t).map (algebraMap E K) =
        cT cK c.val * ((H₀.map (algebraMap E K)) * aeval (γ₀.val.map (algebraMap E K)) m) * c.val := by
  have hcK : ∀ e : E, cK (algebraMap E K e) = algebraMap E K (IsCMField.complexConj E e) := by
    intro e
    apply j.injective
    rw [hj2, hj1, hj1]
    simp
  set P := γ₀.val.charpoly with hPdef
  have hPsep : P.Separable := hell.2.2.1
  have hP0 : P ≠ 0 := hell.1.ne_zero
  have hself : ∀ Q : E[X], Q.Monic → Irreducible Q → Q ∣ P → IsSelfRecip E Q.natDegree Q :=
    GlobalTheory.SelfRecipFactor.isSelfRecip_of_dvd_ell E n P hell
  have hXP : IsCoprime X P := by
    rw [Polynomial.irreducible_X.coprime_iff_not_dvd]
    intro hX
    exact (hself X monic_X irreducible_X hX).2.2.2.1 (by simp)
  obtain ⟨a, b, hab⟩ := hXP
  set S := (UniqueFactorizationMonoid.normalizedFactors P).toFinset with hS
  have hmem : ∀ Q ∈ S, Q.Monic ∧ Irreducible Q ∧ Q ∣ P := by
    intro Q hQ
    rw [hS, Multiset.mem_toFinset] at hQ
    have hirr := UniqueFactorizationMonoid.irreducible_of_normalized_factor Q hQ
    refine ⟨?_, hirr, UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hQ⟩
    have hn := UniqueFactorizationMonoid.normalize_normalized_factor Q hQ
    rw [← hn]; exact Polynomial.monic_normalize hirr.ne_zero
  have hcopS : (S : Set E[X]).Pairwise (Function.onFun IsCoprime fun Q : E[X] => Q) := by
    intro Q hQ Q' hQ' hne
    simp only [Function.onFun]
    rw [(hmem Q hQ).2.1.coprime_iff_not_dvd]
    intro hd
    exact hne (eq_of_monic_of_associated (hmem Q hQ).1 (hmem Q' hQ').1
      ((hmem Q hQ).2.1.associated_of_dvd (hmem Q' hQ').2.1 hd))
  have hcopK : (S : Set E[X]).Pairwise (Function.onFun IsCoprime fun Q : E[X] => Q.map (algebraMap E K)) := by
    intro Q hQ Q' hQ' hne
    have := (hcopS hQ hQ' hne).map (mapRingHom (algebraMap E K))
    simpa [Function.onFun] using this
  have hassoc : Associated (∏ Q ∈ S, Q) P := by
    have hnd := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hP0).1 hPsep.squarefree
    rw [Finset.prod_eq_multiset_prod, hS, Multiset.toFinset_val, hnd.dedup, Multiset.map_id']
    exact UniqueFactorizationMonoid.prod_normalizedFactors hP0
  let Qs : ∀ Q : S, SelfRecip E Q.1.natDegree := fun Q =>
    ⟨Q.1, hself Q.1 (hmem Q.1 Q.2).1 (hmem Q.1 Q.2).2.1 (hmem Q.1 Q.2).2.2⟩
  have hQsP : ∀ Q : S, (Qs Q).1 ∣ P := fun Q => (hmem Q.1 Q.2).2.2
  choose z hzQ using fun Q : S => hz _ (Qs Q) (hQsP Q)
  have hcommon : ∀ y : ∀ Q : S, k ⊗[maximalRealSubfield E] Fld (Qs Q), ∃ f : K[X], ∀ Q : S, phi j (Qs Q) f = y Q := by
    intro y
    refine exists_common (fun Q : S => phi j (Qs Q)) (fun Q => phi_surjective j (Qs Q) hj1)
      (fun Q : S => Q.1.map (algebraMap E K)) (fun Q => ?_) (fun Q Q' hne => ?_) y
    · have h0 : (AdjoinRoot.mk (Qs Q).1 (Qs Q).1 : Fld (Qs Q)) = 0 := AdjoinRoot.mk_self
      have := phi_map j (Qs Q) hj1 (Qs Q).1
      rw [h0] at this
      exact this.trans (TensorProduct.tmul_zero _ _)
    · exact hcopK Q.2 Q'.2 (fun h => hne (Subtype.ext h))
  set A : Matrix (Fin n) (Fin n) K := γ₀.val.map (algebraMap E K) with hA
  have hCH : aeval A (P.map (algebraMap E K)) = 0 := by
    rw [hPdef, hA, ← Matrix.charpoly_map]
    exact Matrix.aeval_self_charpoly _
  have hvan : ∀ h : K[X], (∀ Q : S, phi j (Qs Q) h = 0) → aeval A h = 0 := by
    intro h hh
    have h1 : (∏ Q ∈ S, Q.map (algebraMap E K)) ∣ h :=
      Finset.prod_dvd_of_coprime hcopK fun Q hQ => dvd_of_phi_eq_zero j (Qs ⟨Q, hQ⟩) hj1 (hh ⟨Q, hQ⟩)
    rw [← Polynomial.map_prod] at h1
    obtain ⟨d, hd⟩ := (Polynomial.map_dvd (algebraMap E K) hassoc.symm.dvd).trans h1
    rw [hd, map_mul, hCH, zero_mul]
  obtain ⟨f, hf⟩ := hcommon fun Q => (z Q : k ⊗[maximalRealSubfield E] Fld (Qs Q))
  obtain ⟨g, hg⟩ := hcommon fun Q => ((z Q)⁻¹ : (k ⊗[maximalRealSubfield E] Fld (Qs Q))ˣ)
  have hfg : aeval A f * aeval A g = 1 := by
    have := hvan (f * g - 1) fun Q => by
      rw [map_sub, map_mul, hf, hg, Units.mul_inv, map_one, sub_self]
    rw [map_sub, map_mul, map_one] at this
    exact sub_eq_zero.1 this
  have hgf : aeval A g * aeval A f = 1 := by rw [← map_mul, mul_comm, map_mul, hfg]
  set R : K[X] := a.map (algebraMap E K) with hRdef
  have hBA : aeval A R * A = 1 := by
    have := congrArg (fun p : E[X] => aeval A (p.map (algebraMap E K))) hab
    simp only [Polynomial.map_add, Polynomial.map_mul, map_add, map_mul, hCH, Polynomial.map_X, aeval_X,
      Polynomial.map_one, map_one, mul_zero, add_zero, zero_mul] at this
    exact this
  have hAB : A * aeval A R = 1 := by
    rw [show A * aeval A R = aeval A (X * R) by simp, mul_comm, map_mul, aeval_X, hBA]
  have hphiR : ∀ Q : S, phi j (Qs Q) R = (1 : k) ⊗ₜ (alpha (Qs Q))⁻¹ := by
    intro Q
    rw [hRdef, phi_map j (Qs Q) hj1]
    congr 1
    have := congrArg (AdjoinRoot.mk (Qs Q).1) hab
    rw [map_add, map_mul, map_mul, map_one, AdjoinRoot.mk_X, AdjoinRoot.mk_eq_zero.2 (hQsP Q), mul_zero, add_zero] at this
    exact eq_inv_of_mul_eq_one_left this
  set H' : Matrix (Fin n) (Fin n) K := H₀.map (algebraMap E K) with hH'
  have hcTmap : (cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val).map (algebraMap E K) = cT cK A := by
    ext x y
    simp [cT, hA, hcK]
  have hmap : cT cK A * H' * A = H' := by
    have := congrArg (Matrix.map · (algebraMap E K)) hinv
    simp only [Matrix.map_mul] at this
    rw [hcTmap] at this
    exact this
  have hint : cT cK A * H' = H' * aeval A R := by
    calc cT cK A * H' = cT cK A * H' * (A * aeval A R) := by rw [hAB, Matrix.mul_one]
      _ = H' * aeval A R := by rw [← Matrix.mul_assoc, hmap]
  have hkey : aeval A ((f.map cK).comp R * m * f - t.map (algebraMap E K)) = 0 := by
    refine hvan _ fun Q => ?_
    have h1 := involBase_phi j (Qs Q) cK hj2 R (hphiR Q) f
    rw [map_sub, map_mul, map_mul, ← h1, hf, ← hzQ Q]
    ring
  rw [map_sub, map_mul, map_mul, sub_eq_zero] at hkey
  refine ⟨⟨aeval A f, aeval A g, hfg, hgf⟩, ?_, ?_⟩
  · change aeval A f * A = A * aeval A f
    rw [show A * aeval A f = aeval A (X * f) by simp,
      show aeval A f * A = aeval A (f * X) by simp, mul_comm]
  · change _ = cT cK (aeval A f) * (H' * aeval A m) * aeval A f
    rw [Matrix.map_mul, ← aeval_map_mat']
    exact final_calc A H' cK f m R _ hint hkey

section Concrete

theorem unique_over (w : Pl E) (hw : ¬ IsSplitAt w) {v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))}
    (hv : w.under (𝓞 (maximalRealSubfield E)) = v) (u : Pl E) (hu : u.under (𝓞 (maximalRealSubfield E)) = v) : u = w := by
  by_contra h
  exact hw ⟨u, h, hu.trans hv.symm⟩

theorem toCompl_bijective (w : Pl E) (hw : ¬ IsSplitAt w) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
    (hv : w.under (𝓞 (maximalRealSubfield E)) = v) : Function.Bijective (GlobalTheory.LFun.toCompl hv) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun y hy => ?_, GlobalTheory.LFun.InertChart.toCompl_surjective hv⟩
  have h1 := GlobalTheory.AutFunCompare.map_tensNU_self _ _ (GlobalTheory.AdelicU.singleFin_mul v)
    (GlobalTheory.AdelicU.evalV_singleFin_self v) y
  have h2 : GlobalTheory.LFun.finAdEquiv (maximalRealSubfield E) E
      (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU _ (GlobalTheory.AdelicU.singleFin_mul v) y) = 0 :=
    FiniteAdeleRing.ext _ fun u => by
      by_cases e : u.under (𝓞 (maximalRealSubfield E)) = v
      · rw [GlobalTheory.LFun.finAdEquiv_apply e, h1]
        obtain rfl := unique_over w hw hv u e
        exact hy
      · rw [GlobalTheory.LFun.finAdEquiv_apply rfl, GlobalTheory.AutFunCompare.map_tensNU_zero _ _ _
          (GlobalTheory.AdelicU.evalV_singleFin_ne e), map_zero]
        rfl
  rw [← h1, (map_eq_zero_iff _ (GlobalTheory.LFun.finAdEquiv (maximalRealSubfield E) E).injective).1 h2, map_zero]

def locJ (_hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
    (hv : w.under (𝓞 (maximalRealSubfield E)) = v) :
    w.adicCompletion E ≃+* v.adicCompletion (maximalRealSubfield E) ⊗[maximalRealSubfield E] E :=
  (RingEquiv.ofBijective (GlobalTheory.LFun.toCompl hv) (toCompl_bijective w hw v hv)).symm

theorem toCompl_locJ (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hv : w.under (𝓞 (maximalRealSubfield E)) = v)
    (x : w.adicCompletion E) : GlobalTheory.LFun.toCompl hv (locJ hU w hw v hv x) = x :=
  (RingEquiv.ofBijective (GlobalTheory.LFun.toCompl hv) (toCompl_bijective w hw v hv)).apply_symm_apply x

theorem locJ_toCompl (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hv : w.under (𝓞 (maximalRealSubfield E)) = v)
    (y : v.adicCompletion (maximalRealSubfield E) ⊗[maximalRealSubfield E] E) :
    locJ hU w hw v hv (GlobalTheory.LFun.toCompl hv y) = y :=
  (RingEquiv.ofBijective (GlobalTheory.LFun.toCompl hv) (toCompl_bijective w hw v hv)).symm_apply_apply y

theorem locJ_algebraMap (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hv : w.under (𝓞 (maximalRealSubfield E)) = v) (e : E) :
    locJ hU w hw v hv (algebraMap E _ e) = (1 : v.adicCompletion (maximalRealSubfield E)) ⊗ₜ e := by
  have h := GlobalTheory.LFun.toCompl_tmul hv 1 e
  rw [map_one, one_mul] at h
  rw [← h, locJ_toCompl]

theorem locJ_cj (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hv : w.under (𝓞 (maximalRealSubfield E)) = v)
    (x : w.adicCompletion E) :
    locJ hU w hw v hv (cj w x) = Algebra.TensorProduct.map
      (AlgHom.id (maximalRealSubfield E) (v.adicCompletion (maximalRealSubfield E)))
      ((IsCMField.complexConj E : E ≃ₐ[maximalRealSubfield E] E) : E →ₐ[maximalRealSubfield E] E)
      (locJ hU w hw v hv x) := by
  have hmain := GlobalTheory.ConjAtPlace.main E hU w
  have hσ := (hmain.2.2.2.1 hw).1
  have hF : ∀ a, cj w (GlobalTheory.LFun.complMap hv a) = GlobalTheory.LFun.complMap hv a := by
    have := (HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield E) v).equalizer
      (hmain.1.comp (GlobalTheory.LFun.InertChart.continuous_complMap hv)) (GlobalTheory.LFun.InertChart.continuous_complMap hv)
      (funext fun x => by
        simp only [Function.comp_apply, GlobalTheory.LFun.complMap_algebraMap, hσ]
        exact congrArg _ ((IsCMField.complexConj E).commutes x))
    exact fun a => congrFun this a
  have hcomp : ∀ y, cj w (GlobalTheory.LFun.toCompl hv y) = GlobalTheory.LFun.toCompl hv
      (Algebra.TensorProduct.map (AlgHom.id (maximalRealSubfield E) (v.adicCompletion (maximalRealSubfield E)))
        ((IsCMField.complexConj E : E ≃ₐ[maximalRealSubfield E] E) : E →ₐ[maximalRealSubfield E] E) y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => simp [GlobalTheory.LFun.toCompl_tmul, hF, hσ]
    | add a b ha hb => simp only [map_add, ha, hb]
  conv_lhs => rw [← toCompl_locJ hU w hw v hv x, hcomp, locJ_toCompl]

def locPhi (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
    (hv : w.under (𝓞 (maximalRealSubfield E)) = v) {r : ℕ} (Q : SelfRecip E r) :
    (w.adicCompletion E)[X] →+* v.adicCompletion (maximalRealSubfield E) ⊗[maximalRealSubfield E] Fld Q :=
  phi (locJ hU w hw v hv) Q

end Concrete

end GlobalTheory.CompanionTheory.LocAssembly
