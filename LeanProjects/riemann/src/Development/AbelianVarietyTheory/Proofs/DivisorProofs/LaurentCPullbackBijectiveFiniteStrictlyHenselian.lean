import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentVarUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentMapIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HZeroPullbackTwistBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyProdRingProjectionsBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyZeroStrictlyHenselianEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAlgebraStrictlyHenselianInductionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfRingEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyLaurentVanishingFiniteAlgebra
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

noncomputable section

namespace GlobalTheory.EtC.SpecMapPullbackFunctoriality

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 (sp A) := by
  simp only [spMap, CommRingCat.ofHom_id, Spec.map_id]
  exact sch.map_id _

abbrev PC (q : ℕ) (T : Type) [CommRing T] : Prop :=
  ∀ i : ℤ, Function.Bijective (pull _ (spMap (LaurentPolynomial.C : T →+* LaurentPolynomial T)) (tw q i) 0)

open CategoryTheory Limits AlgebraicGeometry Opposite Polynomial in
private lemma laurentMap_coeff' {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (e : LaurentPolynomial A) (n : ℤ) :
    (_root_.GlobalTheory.EtC.GmStep.laurentMap f e).coeff n = f (e.coeff n) := by
  rw [_root_.GlobalTheory.EtC.GmStep.laurentMap_coeff]; rfl

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
private lemma pull_spMap_comp_apply (R : Type) [CommRing R] {A B C : Type} [CommRing A]
    [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) (F : _root_.GlobalTheory.EtC.Shv R) (n : ℤ)
    (x : _root_.GlobalTheory.EtC.H R (_root_.GlobalTheory.EtC.sp A) F n) :
    _root_.GlobalTheory.EtC.pull R (_root_.GlobalTheory.EtC.spMap (g.comp f)) F n x =
      _root_.GlobalTheory.EtC.pull R (_root_.GlobalTheory.EtC.spMap g) F n
        (_root_.GlobalTheory.EtC.pull R (_root_.GlobalTheory.EtC.spMap f) F n x) := by
  rw [_root_.GlobalTheory.EtC.HInvIso.spMap_comp', _root_.GlobalTheory.EtC.pull_comp]

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
private lemma pull_bijective_of_ringHom_inverse (R : Type) [CommRing R] {A B : Type} [CommRing A]
    [CommRing B] (f : A →+* B) (g : B →+* A) (hgf : g.comp f = RingHom.id A)
    (hfg : f.comp g = RingHom.id B) (F : _root_.GlobalTheory.EtC.Shv R) (n : ℤ) :
    Function.Bijective (_root_.GlobalTheory.EtC.pull R (_root_.GlobalTheory.EtC.spMap f) F n) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨_root_.GlobalTheory.EtC.pull R (_root_.GlobalTheory.EtC.spMap g) F n, fun x => ?_, fun y => ?_⟩
  · rw [← pull_spMap_comp_apply, hgf, _root_.GlobalTheory.EtC.HInvIso.spMap_id',
      _root_.GlobalTheory.EtC.pull_id]
  · rw [← pull_spMap_comp_apply, hfg, _root_.GlobalTheory.EtC.HInvIso.spMap_id',
      _root_.GlobalTheory.EtC.pull_id]

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
private lemma laurentConstant_of_ringEquiv (q : ℕ) {T T' : Type} [CommRing T] [CommRing T']
    (e : T ≃+* T') (h : _root_.GlobalTheory.EtC.SpecMapPullbackFunctoriality.PC q T) :
    _root_.GlobalTheory.EtC.SpecMapPullbackFunctoriality.PC q T' := by
  intro i
  have hinv : ∀ {U V : Type} [CommRing U] [CommRing V] (f : U ≃+* V),
      (_root_.GlobalTheory.EtC.GmStep.laurentMap (f.symm : V →+* U)).comp
        (_root_.GlobalTheory.EtC.GmStep.laurentMap (f : U →+* V)) = RingHom.id _ := by
    intro U V _ _ f
    refine RingHom.ext fun p => LaurentPolynomial.ext fun n => ?_
    simp [laurentMap_coeff']
  have hu := pull_bijective_of_ringHom_inverse (ZMod q) (e : T →+* T') (e.symm : T' →+* T)
    (by ext; simp) (by ext; simp) (_root_.GlobalTheory.EtC.tw q i) 0
  have hv := pull_bijective_of_ringHom_inverse (ZMod q) (_root_.GlobalTheory.EtC.GmStep.laurentMap (e : T →+* T'))
    (_root_.GlobalTheory.EtC.GmStep.laurentMap (e.symm : T' →+* T)) (hinv e)
    (by simpa using hinv e.symm) (_root_.GlobalTheory.EtC.tw q i) 0
  have hsq : (LaurentPolynomial.C : T' →+* LaurentPolynomial T').comp (e : T →+* T') =
      (_root_.GlobalTheory.EtC.GmStep.laurentMap (e : T →+* T')).comp LaurentPolynomial.C :=
    (_root_.GlobalTheory.EtC.GmStep.laurentMap_comp_C _).symm
  have hfun : (_root_.GlobalTheory.EtC.pull (ZMod q) (_root_.GlobalTheory.EtC.spMap
        (LaurentPolynomial.C : T' →+* LaurentPolynomial T')) (_root_.GlobalTheory.EtC.tw q i) 0) ∘
      (_root_.GlobalTheory.EtC.pull (ZMod q) (_root_.GlobalTheory.EtC.spMap (e : T →+* T'))
        (_root_.GlobalTheory.EtC.tw q i) 0) =
      (_root_.GlobalTheory.EtC.pull (ZMod q) (_root_.GlobalTheory.EtC.spMap
        (_root_.GlobalTheory.EtC.GmStep.laurentMap (e : T →+* T'))) (_root_.GlobalTheory.EtC.tw q i) 0) ∘
      (_root_.GlobalTheory.EtC.pull (ZMod q) (_root_.GlobalTheory.EtC.spMap
        (LaurentPolynomial.C : T →+* LaurentPolynomial T)) (_root_.GlobalTheory.EtC.tw q i) 0) := by
    funext x
    simp only [Function.comp_apply]
    rw [← pull_spMap_comp_apply, ← pull_spMap_comp_apply, hsq]
  exact (Function.Bijective.of_comp_iff _ hu).mp (hfun ▸ hv.comp (h i))

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
private lemma subsingleton_cohomology_of_subsingleton_ring (q : ℕ) (S : Type) [CommRing S]
    [Subsingleton S] (i n : ℤ) :
    Subsingleton (_root_.GlobalTheory.EtC.H (ZMod q) (_root_.GlobalTheory.EtC.sp S) (_root_.GlobalTheory.EtC.tw q i) n) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨x, hx⟩ := (_root_.GlobalTheory.EtC.ProdCoh.ht_prod_bijective q S S n i).2 (a, b)
  have hfs : RingHom.fst S S = RingHom.snd S S := RingHom.ext fun _ => Subsingleton.elim _ _
  simp only [Prod.mk.injEq] at hx
  rw [← hx.1, ← hx.2, hfs]

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
private lemma laurentMap_fst_prod_snd_bijective (T₁ T₂ : Type) [CommRing T₁] [CommRing T₂] :
    Function.Bijective (RingHom.prod (_root_.GlobalTheory.EtC.GmStep.laurentMap (RingHom.fst T₁ T₂))
      (_root_.GlobalTheory.EtC.GmStep.laurentMap (RingHom.snd T₁ T₂))) := by
  have hsurj : ∀ {U V : Type} [CommRing U] [CommRing V] (f : U →+* V) (s : V → U),
      (∀ v, f (s v) = v) → Function.Surjective (_root_.GlobalTheory.EtC.GmStep.laurentMap f) := by
    intro U V _ _ f s hs p
    induction p using LaurentPolynomial.induction_on' with
    | add p r hp hr =>
      obtain ⟨a, rfl⟩ := hp
      obtain ⟨b, rfl⟩ := hr
      exact ⟨a + b, map_add _ _ _⟩
    | C_mul_T n a =>
      refine ⟨LaurentPolynomial.C (s a) * LaurentPolynomial.T n, ?_⟩
      rw [map_mul, _root_.GlobalTheory.EtC.GmStep.laurentMap_C, _root_.GlobalTheory.EtC.GmStep.laurentMap_T, hs]
  refine ⟨fun x y hxy => ?_, fun p => ?_⟩
  · simp only [RingHom.prod_apply, Prod.mk.injEq] at hxy
    refine LaurentPolynomial.ext fun n => ?_
    have h1 := congrArg (fun g => g.coeff n) hxy.1
    have h2 := congrArg (fun g => g.coeff n) hxy.2
    simp only [laurentMap_coeff'] at h1 h2
    exact Prod.ext h1 h2
  · obtain ⟨y₁, hy₁⟩ := hsurj (RingHom.fst T₁ T₂) (fun a => (a, 0)) (fun _ => rfl) p.1
    obtain ⟨y₂, hy₂⟩ := hsurj (RingHom.snd T₁ T₂) (fun a => (0, a)) (fun _ => rfl) p.2
    refine ⟨LaurentPolynomial.C (1, 0) * y₁ + LaurentPolynomial.C (0, 1) * y₂, ?_⟩
    simp only [RingHom.prod_apply, map_add, map_mul, _root_.GlobalTheory.EtC.GmStep.laurentMap_C, hy₁, hy₂]
    refine Prod.ext ?_ ?_ <;> simp

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
private lemma laurentConstant_prod (q : ℕ) (T₁ T₂ : Type) [CommRing T₁] [CommRing T₂]
    (h₁ : _root_.GlobalTheory.EtC.SpecMapPullbackFunctoriality.PC q T₁)
    (h₂ : _root_.GlobalTheory.EtC.SpecMapPullbackFunctoriality.PC q T₂) :
    _root_.GlobalTheory.EtC.SpecMapPullbackFunctoriality.PC q (T₁ × T₂) := by
  intro i
  set Φ := RingHom.prod (_root_.GlobalTheory.EtC.GmStep.laurentMap (RingHom.fst T₁ T₂))
    (_root_.GlobalTheory.EtC.GmStep.laurentMap (RingHom.snd T₁ T₂))
  obtain ⟨eΦ, heΦ⟩ : ∃ e : LaurentPolynomial (T₁ × T₂) ≃+* LaurentPolynomial T₁ × LaurentPolynomial T₂,
      ∀ x, e x = Φ x := ⟨RingEquiv.ofBijective Φ (laurentMap_fst_prod_snd_bijective T₁ T₂), fun _ => rfl⟩
  have hΦbij := pull_bijective_of_ringHom_inverse (ZMod q) Φ (eΦ.symm : _ →+* _)
    (RingHom.ext fun x => by
      rw [RingHom.comp_apply, ← heΦ, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]; rfl)
    (RingHom.ext fun x => by
      rw [RingHom.comp_apply, ← heΦ, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]; rfl)
    (_root_.GlobalTheory.EtC.tw q i) 0
  have hfst : (RingHom.fst (LaurentPolynomial T₁) (LaurentPolynomial T₂)).comp
      (Φ.comp LaurentPolynomial.C) = LaurentPolynomial.C.comp (RingHom.fst T₁ T₂) := by
    ext a
    simp [Φ, _root_.GlobalTheory.EtC.GmStep.laurentMap_C]
  have hsnd : (RingHom.snd (LaurentPolynomial T₁) (LaurentPolynomial T₂)).comp
      (Φ.comp LaurentPolynomial.C) = LaurentPolynomial.C.comp (RingHom.snd T₁ T₂) := by
    ext a
    simp [Φ, _root_.GlobalTheory.EtC.GmStep.laurentMap_C]
  have hfun : (fun y => (_root_.GlobalTheory.EtC.pull (ZMod q) (_root_.GlobalTheory.EtC.spMap
          (RingHom.fst (LaurentPolynomial T₁) (LaurentPolynomial T₂))) (_root_.GlobalTheory.EtC.tw q i) 0 y,
        _root_.GlobalTheory.EtC.pull (ZMod q) (_root_.GlobalTheory.EtC.spMap
          (RingHom.snd (LaurentPolynomial T₁) (LaurentPolynomial T₂))) (_root_.GlobalTheory.EtC.tw q i) 0 y)) ∘
      _root_.GlobalTheory.EtC.pull (ZMod q) (_root_.GlobalTheory.EtC.spMap (Φ.comp LaurentPolynomial.C))
        (_root_.GlobalTheory.EtC.tw q i) 0 =
      Prod.map (_root_.GlobalTheory.EtC.pull (ZMod q) (_root_.GlobalTheory.EtC.spMap
          (LaurentPolynomial.C : T₁ →+* LaurentPolynomial T₁)) (_root_.GlobalTheory.EtC.tw q i) 0)
        (_root_.GlobalTheory.EtC.pull (ZMod q) (_root_.GlobalTheory.EtC.spMap
          (LaurentPolynomial.C : T₂ →+* LaurentPolynomial T₂)) (_root_.GlobalTheory.EtC.tw q i) 0) ∘
      (fun x => (_root_.GlobalTheory.EtC.pull (ZMod q) (_root_.GlobalTheory.EtC.spMap
          (RingHom.fst T₁ T₂)) (_root_.GlobalTheory.EtC.tw q i) 0 x,
        _root_.GlobalTheory.EtC.pull (ZMod q) (_root_.GlobalTheory.EtC.spMap
          (RingHom.snd T₁ T₂)) (_root_.GlobalTheory.EtC.tw q i) 0 x)) := by
    funext x
    simp only [Function.comp_apply, Prod.map_apply]
    rw [← pull_spMap_comp_apply, ← pull_spMap_comp_apply,
      ← pull_spMap_comp_apply, ← pull_spMap_comp_apply, hfst, hsnd]
  have hD : Function.Bijective (_root_.GlobalTheory.EtC.pull (ZMod q)
      (_root_.GlobalTheory.EtC.spMap (Φ.comp LaurentPolynomial.C)) (_root_.GlobalTheory.EtC.tw q i) 0) :=
    (Function.Bijective.of_comp_iff' (_root_.GlobalTheory.EtC.ProdCoh.ht_prod_bijective q
      (LaurentPolynomial T₁) (LaurentPolynomial T₂) 0 i) _).mp
      (hfun ▸ ((h₁ i).prodMap (h₂ i)).comp
        (_root_.GlobalTheory.EtC.ProdCoh.ht_prod_bijective q T₁ T₂ 0 i))
  have hcomp : _root_.GlobalTheory.EtC.pull (ZMod q)
      (_root_.GlobalTheory.EtC.spMap (Φ.comp LaurentPolynomial.C)) (_root_.GlobalTheory.EtC.tw q i) 0 =
      (_root_.GlobalTheory.EtC.pull (ZMod q) (_root_.GlobalTheory.EtC.spMap Φ) (_root_.GlobalTheory.EtC.tw q i) 0) ∘
        (_root_.GlobalTheory.EtC.pull (ZMod q) (_root_.GlobalTheory.EtC.spMap
          (LaurentPolynomial.C : T₁ × T₂ →+* LaurentPolynomial (T₁ × T₂))) (_root_.GlobalTheory.EtC.tw q i) 0) := by
    funext x
    exact pull_spMap_comp_apply _ _ _ _ _ x
  exact (Function.Bijective.of_comp_iff' hΦbij _).mp (hcomp ▸ hD)

open CategoryTheory Limits AlgebraicGeometry Opposite Polynomial in
private lemma exists_cyclotomic_root_of_strictlyHenselian (q : ℕ) [NeZero q] (A : Type)
    [CommRing A] (hA : _root_.GlobalTheory.EtC.SH A) (hq : IsUnit (q : A)) :
    ∃ ζ : A, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0 := by
  obtain ⟨hH, hsep⟩ := hA
  have hqk : ((q : ℕ) : IsLocalRing.ResidueField A) ≠ 0 := by
    have := hq.map (IsLocalRing.residue A)
    simpa using this.ne_zero
  have hs : (cyclotomic q (IsLocalRing.ResidueField A)).Separable :=
    (separable_X_pow_sub_C (1 : IsLocalRing.ResidueField A) hqk one_ne_zero).of_dvd
      (by simpa using cyclotomic.dvd_X_pow_sub_one q (IsLocalRing.ResidueField A))
  have hdeg : (cyclotomic q (IsLocalRing.ResidueField A)).degree ≠ 0 := by
    rw [degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  obtain ⟨x, hx⟩ := IsSepClosed.exists_root _ hdeg hs
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  have key : ∀ p : A[X], IsLocalRing.residue A (p.eval a) =
      (p.map (IsLocalRing.residue A)).eval (IsLocalRing.residue A a) := by
    intro p
    rw [Polynomial.eval_map, Polynomial.eval₂_hom]
  obtain ⟨ζ, hζ, -⟩ := HenselianLocalRing.is_henselian (cyclotomic q A) (cyclotomic.monic q A) a
    (by
      rw [← IsLocalRing.residue_eq_zero_iff, key, map_cyclotomic]
      exact hx)
    (by
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit, key, ← derivative_map, map_cyclotomic]
      have := hs.aeval_derivative_ne_zero (x := IsLocalRing.residue A a)
        (by simpa [aeval_def] using hx)
      simpa [aeval_def] using this)
  refine ⟨ζ, ?_⟩
  rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
  exact hζ

open CategoryTheory Limits AlgebraicGeometry Opposite Polynomial in
private lemma isIdempotentElem_eq_zero_or_one_of_isLocalRing {T : Type} [CommRing T]
    [IsLocalRing T] (e : T) (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with h | h
  · exact Or.inr (h.mul_left_cancel (by rw [he.eq, mul_one]))
  · exact Or.inl (h.mul_right_eq_zero.mp (by rw [sub_mul, one_mul, he.eq, sub_self]))

open CategoryTheory Limits AlgebraicGeometry Opposite Polynomial in
private lemma laurent_isIdempotentElem_eq_zero_or_one_of_isLocalRing (T : Type) [CommRing T] [IsLocalRing T]
    (e : LaurentPolynomial T) (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  set m := IsLocalRing.maximalIdeal T
  have main : ∀ e : LaurentPolynomial T, IsIdempotentElem e →
      _root_.GlobalTheory.EtC.GmStep.laurentMap (Ideal.Quotient.mk m) e = 0 → e = 0 := by
    intro e he h0
    have hall : ∀ (p : Ideal T), p.IsPrime → ∀ n, e.coeff n ∈ p := by
      intro p hp n
      rcases IsIdempotentElem.iff_eq_zero_or_one.mp
          (he.map (_root_.GlobalTheory.EtC.GmStep.laurentMap (Ideal.Quotient.mk p))) with h | h
      · have := congrArg (fun g => g.coeff n) h
        simp only [laurentMap_coeff'] at this
        exact Ideal.Quotient.eq_zero_iff_mem.mp (this.trans rfl)
      · exfalso
        have hpm : p ≤ m := IsLocalRing.le_maximalIdeal hp.ne_top
        have hcomp : _root_.GlobalTheory.EtC.GmStep.laurentMap (Ideal.Quotient.mk m) e =
            _root_.GlobalTheory.EtC.GmStep.laurentMap (Ideal.Quotient.factor hpm)
              (_root_.GlobalTheory.EtC.GmStep.laurentMap (Ideal.Quotient.mk p) e) := by
          ext n
          simp only [laurentMap_coeff']
          rfl
        rw [h, map_one, h0] at hcomp
        exact zero_ne_one hcomp
    have hnil : _root_.GlobalTheory.EtC.GmStep.laurentMap (Ideal.Quotient.mk (nilradical T)) e = 0 := by
      ext n
      rw [laurentMap_coeff']
      refine (Ideal.Quotient.eq_zero_iff_mem.mpr ?_).trans rfl
      rw [nilradical_eq_sInf, Ideal.mem_sInf]
      exact fun p hp => hall p hp n
    have hker := _root_.GlobalTheory.EtC.GmStep.laurentMap_ker (Ideal.Quotient.mk (nilradical T))
      (by rw [Ideal.mk_ker]) (RingHom.mem_ker.mpr hnil)
    exact he.eq_zero_of_isNilpotent hker
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp
      (he.map (_root_.GlobalTheory.EtC.GmStep.laurentMap (Ideal.Quotient.mk m))) with h | h
  · exact Or.inl (main e he h)
  · refine Or.inr (sub_eq_zero.mp ?_).symm
    exact main (1 - e) he.one_sub (by rw [map_sub, map_one, h, sub_self])

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
theorem _root_.GlobalTheory.EtC.SpecMapPullbackFunctoriality.laurent_C_pull_bijective : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], _root_.GlobalTheory.EtC.SH A → IsUnit (q : A) →
    ∀ (T : Type) [CommRing T] [Algebra A T], Module.Finite A T → ∀ i : ℤ,
    Function.Bijective (_root_.GlobalTheory.EtC.pull _ (_root_.GlobalTheory.EtC.spMap (LaurentPolynomial.C : T →+* LaurentPolynomial T)) (_root_.GlobalTheory.EtC.tw q i) 0) := by
  intro q _ A _ hA hq T _ _ hT
  refine _root_.GlobalTheory.EtC.GmStep.FinSH.induction_principle A hA
    (fun T _ _ => _root_.GlobalTheory.EtC.SpecMapPullbackFunctoriality.PC q T) ?_ ?_ ?_ ?_ T hT
  · intro T T' _ _ _ _ a h
    exact laurentConstant_of_ringEquiv q a.toRingEquiv h
  · intro T _ _ hT0 i
    haveI := _root_.GlobalTheory.EtC.LaurentFinite.laurent_subsingleton T
    haveI := subsingleton_cohomology_of_subsingleton_ring q T i 0
    haveI := subsingleton_cohomology_of_subsingleton_ring q (LaurentPolynomial T) i 0
    exact ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
  · intro T₁ T₂ _ _ _ _ _ _ h₁ h₂
    exact laurentConstant_prod q T₁ T₂ h₁ h₂
  · intro T _ _ _ hTs i
    have hqT : IsUnit (q : T) := by simpa using hq.map (algebraMap A T)
    obtain ⟨hH, -⟩ := id hTs
    exact _root_.GlobalTheory.EtC.h_zero_pull_bijective q T (LaurentPolynomial T)
      LaurentPolynomial.C hqT (exists_cyclotomic_root_of_strictlyHenselian q T hTs hqT)
      inferInstance (fun e he => isIdempotentElem_eq_zero_or_one_of_isLocalRing e he)
      (fun e he => laurent_isIdempotentElem_eq_zero_or_one_of_isLocalRing T e he) i

end GlobalTheory.EtC.SpecMapPullbackFunctoriality
