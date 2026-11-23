import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RingKrullDimOfEtaleMvPolynomial
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.ConePrime
open GlobalTheory.ZH.CrdCalc GlobalTheory.TangentOrigin

section Alg
variable {k J A B : Type} [CommRing k] [CommRing A] [CommRing B]

def coneHom (c : k →+* A) (r : J → A) : MvPolynomial J k →+* Polynomial A :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp c) fun j => Polynomial.C (r j) * Polynomial.X

theorem eval₂_coneHom (c : k →+* A) (r : J → A) (e : A →+* B) (t : B) (f : MvPolynomial J k) :
    Polynomial.eval₂ e t (coneHom c r f) = MvPolynomial.eval₂Hom (e.comp c) (fun j => e (r j) * t) f := by
  have : (Polynomial.eval₂RingHom e t).comp (coneHom c r) =
      MvPolynomial.eval₂Hom (e.comp c) (fun j => e (r j) * t) := by
    ext <;> simp [coneHom]
  exact RingHom.congr_fun this f

theorem map_coneHom (c : k →+* A) (r : J → A) (e : A →+* B) (f : MvPolynomial J k) :
    Polynomial.map e (coneHom c r f) = coneHom (e.comp c) (fun j => e (r j)) f := by
  have : (Polynomial.mapRingHom e).comp (coneHom c r) = coneHom (e.comp c) (fun j => e (r j)) := by
    apply MvPolynomial.ringHom_ext <;> simp [coneHom]
  exact RingHom.congr_fun this f

theorem coneHom_mul (c : k →+* A) (r : J → A) (u : A) (f : MvPolynomial J k) :
    coneHom c (fun j => r j * u) f = (coneHom c r f).comp (Polynomial.C u * Polynomial.X) := by
  have : coneHom c (fun j => r j * u) =
      (Polynomial.compRingHom (Polynomial.C u * Polynomial.X)).comp (coneHom c r) := by
    apply MvPolynomial.ringHom_ext <;> simp [coneHom, _root_.mul_assoc]
  exact RingHom.congr_fun this f

theorem coneHom_of_isHomogeneous (c : k →+* A) (r : J → A) {f : MvPolynomial J k} {n : ℕ}
    (hf : f.IsHomogeneous n) :
    coneHom c r f = Polynomial.monomial n (MvPolynomial.eval₂Hom c r f) := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hn : d.sum (fun _ e => e) = n := by
    have := hf (MvPolynomial.mem_support_iff.1 hd)
    rw [← this, Finsupp.weight_apply]
    simp
  rw [← hn, ← Polynomial.C_mul_X_pow_eq_monomial]
  simp only [coneHom, MvPolynomial.eval₂Hom_monomial, Finsupp.prod, Finsupp.sum, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, map_mul, map_prod, map_pow, RingHom.comp_apply, _root_.mul_assoc]

theorem coeff_coneHom (c : k →+* A) (r : J → A) (f : MvPolynomial J k) (n : ℕ) :
    (coneHom c r f).coeff n = MvPolynomial.eval₂Hom c r (MvPolynomial.homogeneousComponent n f) := by
  conv_lhs => rw [← f.sum_homogeneousComponent]
  rw [map_sum, Polynomial.finset_sum_coeff]
  simp only [coneHom_of_isHomogeneous c r (MvPolynomial.homogeneousComponent_isHomogeneous _ f),
    Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.homogeneousComponent_eq_zero _ _ (by simpa using h), map_zero]

theorem isHomogeneous_ker_coneHom (c : k →+* A) (r : J → A) :
    (RingHom.ker (coneHom c r)).IsHomogeneous (MvPolynomial.homogeneousSubmodule J k) := by
  intro n f hf
  rw [RingHom.mem_ker] at hf
  have e : ((DirectSum.decompose (MvPolynomial.homogeneousSubmodule J k) f n : MvPolynomial.homogeneousSubmodule J k n) : MvPolynomial J k) = MvPolynomial.homogeneousComponent n f :=
    MvPolynomial.decomposition.decompose'_apply f n
  rw [e]
  rw [RingHom.mem_ker, coneHom_of_isHomogeneous c r (MvPolynomial.homogeneousComponent_isHomogeneous _ f),
    ← coeff_coneHom, hf]
  simp

end Alg

theorem eq_zero_of_forall_algHom {k A : Type} [Field k] [IsAlgClosed k] [CommRing A] [Algebra k A]
    [_root_.IsReduced A] [Algebra.FiniteType k A] (a : A) (h : ∀ e : A →ₐ[k] k, e a = 0) : a = 0 := by
  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k)
  have hrad : (⊥ : Ideal A).IsRadical := by
    rw [Ideal.isRadical_bot_iff]; infer_instance
  have hj : (⊥ : Ideal A).jacobson = ⊥ := IsJacobsonRing.out inferInstance hrad
  rw [← Ideal.mem_bot, ← hj, Ideal.jacobson, Ideal.mem_sInf]
  rintro m ⟨-, hm⟩
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite k (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)
  have hb : Function.Bijective (algebraMap k (A ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let i : k ≃ₐ[k] (A ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ m)) hb
  have := h ((i.symm : (A ⧸ m) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k m))
  rw [AlgHom.comp_apply] at this
  have h2 : Ideal.Quotient.mkₐ k m a = 0 := by
    apply i.symm.injective
    rw [map_zero]; exact this
  exact Ideal.Quotient.eq_zero_iff_mem.mp h2

theorem finiteType_of_closure {k J A : Type} [Field k] [Fintype J] [CommRing A] [Algebra k A] (r : J → A)
    (h : Subring.closure (Set.range (algebraMap k A) ∪ Set.range r) = ⊤) : Algebra.FiniteType k A := by
  refine ⟨Subalgebra.fg_def.2 ⟨Set.range r, Set.finite_range r, ?_⟩⟩
  apply Subalgebra.toSubring_injective
  rw [Algebra.adjoin_eq_ring_closure, h]
  rfl

theorem ringKrullDim_quotient_ker {k J A : Type} [Field k] [Fintype J] [CommRing A] [IsDomain A] [Algebra k A]
    (r : J → A) (i : J) (hi : r i = 1)
    (h : Subring.closure (Set.range (algebraMap k A) ∪ Set.range r) = ⊤) (g : ℕ) (hg : ringKrullDim A = g) :
    ringKrullDim (MvPolynomial J k ⧸ RingHom.ker (coneHom (algebraMap k A) r)) = (g + 1 : ℕ) := by
  haveI := finiteType_of_closure r h
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  let φ : MvPolynomial J k →ₐ[k] Polynomial A :=
    { coneHom (algebraMap k A) r with commutes' := fun a => by simp [coneHom] }
  let T := φ.range
  have e : (MvPolynomial J k ⧸ RingHom.ker (coneHom (algebraMap k A) r)) ≃+* T :=
    (Ideal.quotientKerEquivRange φ).toRingEquiv
  rw [ringKrullDim_eq_of_ringEquiv e]
  haveI : Algebra.FiniteType k T := Algebra.FiniteType.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hX : ∀ j, Polynomial.C (r j) * Polynomial.X ∈ T := fun j => ⟨MvPolynomial.X j, by simp [φ, coneHom]⟩
  have hX1 : (Polynomial.X : Polynomial A) ∈ T := by simpa [hi] using hX i
  haveI : Algebra.IsAlgebraic T (Polynomial A) := by
    have hT : ∀ q ∈ T, IsAlgebraic T q := fun q hq => isAlgebraic_algebraMap (⟨q, hq⟩ : T)
    have hC : ∀ a : A, IsAlgebraic T (Polynomial.C a) := by
      intro a
      have ha : a ∈ Subring.closure (Set.range (algebraMap k A) ∪ Set.range r) := by rw [h]; trivial
      have : Subring.closure (Set.range (algebraMap k A) ∪ Set.range r) ≤
          (Subalgebra.algebraicClosure T (Polynomial A)).toSubring.comap Polynomial.C := by
        rw [Subring.closure_le]
        rintro _ (⟨b, rfl⟩ | ⟨j, rfl⟩)
        · exact hT _ (T.algebraMap_mem b)
        · exact IsAlgebraic.of_mul (y := Polynomial.X) (mem_nonZeroDivisors_of_ne_zero Polynomial.X_ne_zero)
            (hT _ hX1) (by rw [mul_comm]; exact hT _ (hX j))
      exact this ha
    refine ⟨fun q => ?_⟩
    induction q using Polynomial.induction_on' with
    | add p q hp hq => exact hp.add hq
    | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      exact (hC a).mul ((hT _ hX1).pow n)
  obtain ⟨n, h1, h2⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := k) (A := Polynomial A)
  rw [Polynomial.ringKrullDim_of_isNoetherianRing, hg] at h1
  rw [← trdeg_add_eq k T, trdeg_eq_zero (R := T) (A := Polynomial A), add_zero] at h2
  rw [ReciprocityTheory.CA.ringKrullDim_eq_of_trdeg_eq_field n h2, ← h1]
  simp

section Geo
variable {k : Type} [Field k] {X : Scheme.{0}}

def constHom (p : X ⟶ Sp k) (U : X.Opens) : k →+* Γ(X, U) :=
  (p.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom

theorem valHom_constHom {R : Type} [CommRing R] (p : X ⟶ Sp k) (x : Sp R ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (a : k) : valHom x U h (constHom p U a) =
      evalPt (x ≫ p) ⊤ le_rfl ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a) :=
  evalPt_constFn p x U h a

theorem valHom_comp_constHom (p : X ⟶ Sp k) (x : Sp k ⟶ X) (hx : x ≫ p = 𝟙 _) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) : (valHom x U h).comp (constHom p U) = RingHom.id k := by
  ext a
  have e : 𝟙 (Sp k) = spMap (RingHom.id k) := (Spec.map_id _).symm
  rw [RingHom.comp_apply, valHom_constHom]
  simp only [hx, e]
  exact evalPt_spMap _ a

theorem exists_point (p : X ⟶ Sp k) {U : X.Opens} (hU : IsAffineOpen U) (e : Γ(X, U) →+* k)
    (he : ∀ a, e (constHom p U a) = a) :
    ∃ (x : Sp k ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ U), x ≫ p = 𝟙 _ ∧ valHom x U h = e := by
  obtain ⟨x, h, hx⟩ := exists_evalPt_eq hU e
  refine ⟨x, h, ?_, hx⟩
  have e' : 𝟙 (Sp k) = spMap (RingHom.id k) := (Spec.map_id _).symm
  rw [e']
  refine eq_spMap_of_evalPt _ _ fun a => ?_
  rw [← valHom_constHom p x U h]
  exact (RingHom.congr_fun hx _).trans (he a)

theorem exists_generic [IsIntegral X] : ∃ (K : Type) (_ : Field K) (y : Sp K ⟶ X),
    ∀ U : X.Opens, (U : Set X).Nonempty → ⊤ ≤ y ⁻¹ᵁ U := by
  refine ⟨X.residueField (genericPoint X), inferInstance, X.fromSpecResidueField (genericPoint X),
    fun U hU z _ => ?_⟩
  have : (X.fromSpecResidueField (genericPoint X)) z = genericPoint X :=
    Scheme.fromSpecResidueField_apply _ z
  change (X.fromSpecResidueField (genericPoint X)) z ∈ U
  rw [this]
  exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 (by simpa using hU)

theorem valHom_injective [IsIntegral X] {K : Type} [Field K] (y : Sp K ⟶ X)
    (hy : ∀ U : X.Opens, (U : Set X).Nonempty → ⊤ ≤ y ⁻¹ᵁ U) (U : X.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U) :
    Function.Injective (valHom y U h) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  by_contra h0
  have hne : ((X.basicOpen f : X.Opens) : Set X).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hb
    exact h0 ((basicOpen_eq_bot_iff f).1 (TopologicalSpace.Opens.ext hb))
  have := (isUnit_valR_iff y U h f).2 (hy _ hne)
  rw [valR_eq y U h, hf] at this
  exact not_isUnit_zero this

variable {H : LB X} {J : Type} {s : J → H.Sec}

theorem coneHom_eq_zero_iff [IsIntegral X] (p : X ⟶ Sp k) {K : Type} [Field K] (y : Sp K ⟶ X)
    (hy : ∀ U : X.Opens, (U : Set X).Nonempty → ⊤ ≤ y ⁻¹ᵁ U) {v : J → K} (hv : Crd H s y v) (i : J)
    (hi : ⊤ ≤ y ⁻¹ᵁ Out.nonzeroLocus (s i)) (r : J → Γ(X, Out.nonzeroLocus (s i)))
    (hr : ∀ j, IsRatio (s j) (s i) _ (r j)) (f : MvPolynomial J k) :
    coneHom (constHom p _) r f = 0 ↔
      coneHom ((evalPt (y ≫ p) ⊤ le_rfl).comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom) v f = 0 := by
  have hu : v i ≠ 0 := ((crd_isUnit_iff i hv).2 hi).ne_zero
  have e1 : (valHom y _ hi).comp (constHom p _) =
      (evalPt (y ≫ p) ⊤ le_rfl).comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom :=
    RingHom.ext fun a => valHom_constHom p y _ hi a
  have e2 : v = fun j => valHom y _ hi (r j) * v i :=
    funext fun j => by rw [← valR_eq]; exact crd_ratio hv (hr j) hi
  rw [← e1, e2, coneHom_mul, ← map_coneHom, Polynomial.comp_C_mul_X_eq_zero_iff (mem_nonZeroDivisors_of_ne_zero hu),
    Polynomial.map_eq_zero_iff (valHom_injective y hy _ hi)]

theorem vanishingIdeal_eq_ker [IsAlgClosed k] [Fintype J] [IsIntegral X] (p : X ⟶ Sp k) (hH : H.IsLB) {J₀ : Set J}
    (him : ImmBy p H s J₀) (i : J) (haff : IsAffineOpen (Out.nonzeroLocus (s i)))
    (hne : ((Out.nonzeroLocus (s i) : X.Opens) : Set X).Nonempty)
    (r : J → Γ(X, Out.nonzeroLocus (s i))) (hr : ∀ j, IsRatio (s j) (s i) _ (r j))
    (hc : Subring.closure (Set.range (constFn p (Out.nonzeroLocus (s i))) ∪ Set.range r) = ⊤) :
    MvPolynomial.vanishingIdeal k (cone p H s) = RingHom.ker (coneHom (constHom p _) r) := by
  ext f
  rw [MvPolynomial.mem_vanishingIdeal_iff, RingHom.mem_ker]
  constructor
  · intro hf
    letI : Algebra k Γ(X, Out.nonzeroLocus (s i)) := (constHom p _).toAlgebra
    haveI := finiteType_of_closure (k := k) r hc
    ext n
    refine eq_zero_of_forall_algHom (k := k) _ fun e => ?_
    obtain ⟨x, h, hx, hxe⟩ := exists_point p haff e.toRingHom e.commutes
    obtain ⟨v, hv⟩ := crd_exists hH s x
    obtain ⟨u, hu⟩ := (crd_isUnit_iff i hv).2 h
    have : Polynomial.map e.toRingHom (coneHom (constHom p _) r f) = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      refine ((Set.finite_singleton (0 : k)).infinite_compl).mono fun t ht' => ?_
      have ht : t ≠ 0 := ht'
      have h1 := hf _ ⟨x, hx, crd_smul (Units.mk0 t ht * u⁻¹) hv⟩
      rw [Set.mem_setOf_eq, Polynomial.IsRoot.def, Polynomial.eval_map, eval₂_coneHom, ← hxe,
        valHom_comp_constHom p x hx, ← h1]
      have : (fun j => valHom x _ h (r j) * t) = fun j => ((Units.mk0 t ht * u⁻¹ : kˣ) : k) * v j := by
        funext j
        rw [crd_ratio hv (hr j) h, valR_eq x _ h, ← hu, Units.val_mul, Units.val_mk0]
        linear_combination (-(valHom x _ h (r j) * t)) * u.inv_mul
      rw [this]
      rfl
    exact (Polynomial.coeff_map e.toRingHom n).symm.trans (by rw [this]; rfl)
  · rintro hf v ⟨x, hx, hv⟩
    obtain ⟨K, _, y, hy⟩ := exists_generic (X := X)
    obtain ⟨w, hw⟩ := crd_exists hH s y
    have : x (IsLocalRing.closedPoint k) ∈ ⨆ i ∈ J₀, Out.nonzeroLocus (s i) := by rw [him.1]; trivial
    simp only [TopologicalSpace.Opens.mem_iSup] at this
    obtain ⟨i', hi', hm⟩ := this
    obtain ⟨-, r', hr', -⟩ := him.2 i' hi'
    have h0 := (coneHom_eq_zero_iff p y hy hw i' (hy _ ⟨_, hm⟩) r' hr' f).2
      ((coneHom_eq_zero_iff p y hy hw i (hy _ hne) r hr f).1 hf)
    have h := (top_le_iff x _).2 hm
    have h1 := eval₂_coneHom (constHom p _) r' (valHom x _ h) (v i') f
    rw [h0, Polynomial.eval₂_zero, valHom_comp_constHom p x hx] at h1
    have e2 : v = fun j => valHom x _ h (r' j) * v i' :=
      funext fun j => by rw [← valR_eq]; exact crd_ratio hv (hr' j) h
    rw [← e2] at h1
    exact h1.symm

end Geo

theorem isPrime_vanishingIdeal_cone : (∀ (k : Type) [Field k] [IsAlgClosed k] (X : Scheme.{0}) (p : X ⟶ Sp k) (H : LB X) (J : Type) [Fintype J] (s : J → H.Sec) (J₀ : Set J), H.IsLB → ImmBy p H s J₀ → IsIntegral X → ∀ g : ℕ, SmoothOfRelativeDimension g p → (MvPolynomial.vanishingIdeal k (cone p H s)).IsPrime ∧ (MvPolynomial.vanishingIdeal k (cone p H s)).IsHomogeneous (MvPolynomial.homogeneousSubmodule J k) ∧ (∃ i, MvPolynomial.X i ∉ MvPolynomial.vanishingIdeal k (cone p H s)) ∧ ringKrullDim (MvPolynomial J k ⧸ MvPolynomial.vanishingIdeal k (cone p H s)) = (g + 1 : ℕ)) := by
  intro k _ _ X p H J _ s J₀ hH him hX g hg
  have : genericPoint X ∈ ⨆ i ∈ J₀, Out.nonzeroLocus (s i) := by rw [him.1]; trivial
  simp only [TopologicalSpace.Opens.mem_iSup] at this
  obtain ⟨i, hi, hm⟩ := this
  obtain ⟨haff, r, hr, hc⟩ := him.2 i hi
  haveI : Nonempty (Out.nonzeroLocus (s i)) := ⟨⟨_, hm⟩⟩
  rw [vanishingIdeal_eq_ker p hH him i haff ⟨_, hm⟩ r hr hc]
  have hri : r i = 1 := by
    obtain ⟨K, _, y, hy⟩ := exists_generic (X := X)
    obtain ⟨w, hw⟩ := crd_exists hH s y
    have h := hy _ ⟨_, hm⟩
    have hu : w i ≠ 0 := ((crd_isUnit_iff i hw).2 h).ne_zero
    apply valHom_injective y hy _ h
    have := crd_ratio hw (hr i) h
    rw [valR_eq y _ h] at this
    rw [map_one]
    exact mul_right_cancel₀ hu (by rw [← this, _root_.one_mul])
  refine ⟨RingHom.ker_isPrime _, isHomogeneous_ker_coneHom _ _, ⟨i, ?_⟩, ?_⟩
  · simp [RingHom.mem_ker, coneHom, hri]
  · letI : Algebra k Γ(X, Out.nonzeroLocus (s i)) := (constHom p _).toAlgebra
    exact ringKrullDim_quotient_ker (k := k) r i hri hc g
      (GlobalTheory.SmoothDim.ringKrullDim_affineOpen k X p g hg _ haff ⟨_, hm⟩)

end GlobalTheory.ZH.ConePrime
end
