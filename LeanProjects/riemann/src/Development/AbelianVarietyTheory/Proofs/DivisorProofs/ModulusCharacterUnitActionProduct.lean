import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullSpMapComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentMapIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSurjectionCechDescentTateTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyNegativeVanishingDegreeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimplicialCochainClassesBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyOneCechCocycleOfPullbackZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimplicialCochainCoboundaryOfClassZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecWidePushoutIsoWidePullbackYonedaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyZeroLaurentSurjectiveStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC Simplicial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.EtC.KerLaurent

theorem laurent_ext {R S : Type} [CommRing R] [CommRing S] {φ ψ : LaurentPolynomial R →+* S}
    (hC : ∀ a, φ (LaurentPolynomial.C a) = ψ (LaurentPolynomial.C a))
    (hT : φ (LaurentPolynomial.T 1) = ψ (LaurentPolynomial.T 1)) : φ = ψ := by
  have h1 : LaurentPolynomial.T (1 : ℤ) * LaurentPolynomial.T (-1) = (1 : LaurentPolynomial R) := by
    rw [← LaurentPolynomial.T_add]; simp
  have hTm : φ (LaurentPolynomial.T (-1)) = ψ (LaurentPolynomial.T (-1)) := by
    have a := congrArg φ h1
    have b := congrArg ψ h1
    rw [map_mul, map_one] at a b
    rw [hT] at a
    calc φ (LaurentPolynomial.T (-1)) = φ (LaurentPolynomial.T (-1)) * (ψ (LaurentPolynomial.T 1) * ψ (LaurentPolynomial.T (-1))) := by
          rw [b, mul_one]
      _ = (ψ (LaurentPolynomial.T 1) * φ (LaurentPolynomial.T (-1))) * ψ (LaurentPolynomial.T (-1)) := by ring
      _ = ψ (LaurentPolynomial.T (-1)) := by rw [a, one_mul]
  have hTn : ∀ n : ℤ, φ (LaurentPolynomial.T n) = ψ (LaurentPolynomial.T n) := by
    intro n
    induction n using Int.induction_on with
    | zero => rw [LaurentPolynomial.T_zero, map_one, map_one]
    | succ k ih => rw [LaurentPolynomial.T_add, map_mul, map_mul, ih, hT]
    | pred k ih => rw [sub_eq_add_neg, LaurentPolynomial.T_add, map_mul, map_mul, ih, hTm]
  refine RingHom.ext fun p => ?_
  induction p using LaurentPolynomial.induction_on' with
  | add p r hp hr => rw [map_add, map_add, hp, hr]
  | C_mul_T n a => rw [map_mul, map_mul, hC, hTn]

def ev1 (R : Type) [CommRing R] : LaurentPolynomial R →+* R := LaurentPolynomial.eval₂ (RingHom.id R) 1

def flat (R : Type) [CommRing R] : LaurentPolynomial R →+* LaurentPolynomial R :=
  (LaurentPolynomial.C : R →+* LaurentPolynomial R).comp (ev1 R)

theorem laurentPolynomialEvalAtOne_C (R : Type) [CommRing R] (a : R) : ev1 R (LaurentPolynomial.C a) = a := by
  simp [ev1, LaurentPolynomial.eval₂_C]

theorem eval_one_T (R : Type) [CommRing R] (n : ℤ) : ev1 R (LaurentPolynomial.T n) = 1 := by
  simp [ev1, LaurentPolynomial.eval₂_T]

theorem flat_comp_C (R : Type) [CommRing R] :
    (flat R).comp (LaurentPolynomial.C : R →+* LaurentPolynomial R) = LaurentPolynomial.C :=
  RingHom.ext fun a => by simp [flat, laurentPolynomialEvalAtOne_C]

theorem laurentPolynomialEvalAtOne_comp_mapRingHom {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) :
    (ev1 S).comp (laurentMap f) = f.comp (ev1 R) := by
  refine laurent_ext (fun a => ?_) ?_
  · have h := RingHom.congr_fun (GmPhiNat.laurentMap_C f) a
    simp only [RingHom.comp_apply] at h ⊢
    rw [h, laurentPolynomialEvalAtOne_C, laurentPolynomialEvalAtOne_C]
  · simp only [RingHom.comp_apply]
    rw [GmPhiNat.laurentMap_T, eval_one_T, eval_one_T, map_one]

theorem flat_laurentMap {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) :
    (laurentMap f).comp (flat R) = (flat S).comp (laurentMap f) := by
  change ((laurentMap f).comp LaurentPolynomial.C).comp (ev1 R) = LaurentPolynomial.C.comp ((ev1 S).comp (laurentMap f))
  rw [GmPhiNat.laurentMap_C, laurentPolynomialEvalAtOne_comp_mapRingHom]
  rfl

variable (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A']

abbrev fB : Spec (CommRingCat.of A') ⟶ Spec (CommRingCat.of A) := Spec.map (CommRingCat.ofHom (algebraMap A A'))

abbrev fT : Spec (CommRingCat.of (LaurentPolynomial A')) ⟶ Spec (CommRingCat.of (LaurentPolynomial A)) :=
  Spec.map (CommRingCat.ofHom (laurentMap (algebraMap A A')))

def constArr : Arrow.mk (yoneda.map (fT A A')) ⟶ Arrow.mk (yoneda.map (fB A A')) :=
  Arrow.homMk (yoneda.map (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : A' →+* LaurentPolynomial A'))))
    (yoneda.map (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : A →+* LaurentPolynomial A)))) (by
      simp only [Arrow.mk_hom, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rw [GmPhiNat.laurentMap_C])

def oneArr : Arrow.mk (yoneda.map (fB A A')) ⟶ Arrow.mk (yoneda.map (fT A A')) :=
  Arrow.homMk (yoneda.map (Spec.map (CommRingCat.ofHom (ev1 A')))) (yoneda.map (Spec.map (CommRingCat.ofHom (ev1 A)))) (by
      simp only [Arrow.mk_hom, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rw [laurentPolynomialEvalAtOne_comp_mapRingHom])

def cP : cech (fT A A') ⟶ cech (fB A A') := Arrow.mapCechNerve (constArr A A')

def cS : cech (fB A A') ⟶ cech (fT A A') := Arrow.mapCechNerve (oneArr A A')

abbrev inc : Fin (1 + 1) → (A' →+* A' ⊗[A] A') :=
  ![Algebra.TensorProduct.includeLeftRingHom, (Algebra.TensorProduct.includeRight : A' →ₐ[A] A' ⊗[A] A').toRingHom]

theorem inc_comp (j : Fin (1 + 1)) : (inc A A' j).comp (algebraMap A A') = (inc A A' 0).comp (algebraMap A A') := by
  refine RingHom.ext fun a => ?_
  fin_cases j
  · rfl
  · change (Algebra.TensorProduct.includeRight : A' →ₐ[A] A' ⊗[A] A') (algebraMap A A' a) =
      (Algebra.TensorProduct.includeLeft : A' →ₐ[A] A' ⊗[A] A') (algebraMap A A' a)
    rw [AlgHom.commutes, AlgHom.commutes]

theorem laurent_univ (R : Type) [CommRing R] (g : Fin (1 + 1) → (LaurentPolynomial A' →+* R))
    (hg : ∀ j, (g j).comp (laurentMap (algebraMap A A')) = (g 0).comp (laurentMap (algebraMap A A'))) :
    ∃! φ : LaurentPolynomial (A' ⊗[A] A') →+* R, ∀ j, φ.comp (laurentMap (inc A A' j)) = g j := by
  have hLC : ∀ {S S' : Type} [CommRing S] [CommRing S'] (f : S →+* S') (a : S),
      laurentMap f (LaurentPolynomial.C a) = LaurentPolynomial.C (f a) :=
    fun f a => RingHom.congr_fun (GmPhiNat.laurentMap_C f) a
  have hgC : ∀ (j : Fin (1 + 1)) (a : A), g j (LaurentPolynomial.C (algebraMap A A' a)) =
      g 0 (LaurentPolynomial.C (algebraMap A A' a)) := by
    intro j a
    have := RingHom.congr_fun (hg j) (LaurentPolynomial.C a)
    simp only [RingHom.comp_apply, hLC] at this
    exact this
  have hgT : ∀ j : Fin (1 + 1), g j (LaurentPolynomial.T 1) = g 0 (LaurentPolynomial.T 1) := by
    intro j
    have := RingHom.congr_fun (hg j) (LaurentPolynomial.T 1)
    simp only [RingHom.comp_apply, GmPhiNat.laurentMap_T] at this
    exact this
  letI : Algebra A R := ((g 0).comp ((LaurentPolynomial.C : A' →+* LaurentPolynomial A').comp (algebraMap A A'))).toAlgebra
  let g0 : A' →ₐ[A] R := ⟨(g 0).comp LaurentPolynomial.C, fun r => rfl⟩
  let g1 : A' →ₐ[A] R := ⟨(g 1).comp LaurentPolynomial.C, fun r => by
    change g 1 (LaurentPolynomial.C (algebraMap A A' r)) = g 0 (LaurentPolynomial.C (algebraMap A A' r))
    exact hgC 1 r⟩
  let ψ0 : A' ⊗[A] A' →ₐ[A] R := Algebra.TensorProduct.lift g0 g1 (fun _ _ => Commute.all _ _)
  let u : Rˣ := Units.map (g 0 : LaurentPolynomial A' →* R) (laurentVarUnit A')
  have hu : (u : R) = g 0 (LaurentPolynomial.T 1) := rfl
  let ψ : LaurentPolynomial (A' ⊗[A] A') →+* R := LaurentPolynomial.eval₂ ψ0.toRingHom u
  have hψC : ∀ x, ψ (LaurentPolynomial.C x) = ψ0 x := fun x => LaurentPolynomial.eval₂_C _ _ _
  have hψT : ψ (LaurentPolynomial.T 1) = g 0 (LaurentPolynomial.T 1) := by
    simp [ψ, LaurentPolynomial.eval₂_T, hu]
  refine ⟨ψ, fun j => ?_, fun φ hφ => ?_⟩
  · refine laurent_ext (fun a => ?_) ?_
    · simp only [RingHom.comp_apply, hLC, hψC]
      fin_cases j
      · change ψ0 (a ⊗ₜ 1) = g 0 (LaurentPolynomial.C a)
        simp [ψ0, g0]
      · change ψ0 (1 ⊗ₜ a) = g 1 (LaurentPolynomial.C a)
        simp [ψ0, g1]
    · simp only [RingHom.comp_apply, GmPhiNat.laurentMap_T, hψT, hgT j]
  · have hC : ∀ x, φ (LaurentPolynomial.C x) = ψ (LaurentPolynomial.C x) := by
      intro x
      rw [hψC]
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        have e : a ⊗ₜ[A] b = (a ⊗ₜ[A] (1 : A')) * ((1 : A') ⊗ₜ[A] b) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        have h0 := RingHom.congr_fun (hφ 0) (LaurentPolynomial.C a)
        have h1 := RingHom.congr_fun (hφ 1) (LaurentPolynomial.C b)
        simp only [RingHom.comp_apply, hLC] at h0 h1
        rw [e, map_mul, map_mul, map_mul]
        change φ (LaurentPolynomial.C (a ⊗ₜ[A] 1)) * φ (LaurentPolynomial.C (1 ⊗ₜ[A] b)) = _
        rw [show (a ⊗ₜ[A] (1 : A')) = inc A A' 0 a from rfl, show ((1 : A') ⊗ₜ[A] b) = inc A A' 1 b from rfl, h0, h1]
        simp [ψ0, g0, g1]
      | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
    refine laurent_ext hC ?_
    have h0 := RingHom.congr_fun (hφ 0) (LaurentPolynomial.T 1)
    simp only [RingHom.comp_apply, GmPhiNat.laurentMap_T] at h0
    rw [h0, hψT]

theorem level_one : ∃ e : yoneda.obj (Spec (CommRingCat.of (LaurentPolynomial (A' ⊗[A] A')))) ≅ (cech (fT A A')).obj (op ⦋1⦌),
    e.hom ≫ (cP A A' ≫ cS A A').app (op ⦋1⦌) = yoneda.map (Spec.map (CommRingCat.ofHom (flat (A' ⊗[A] A')))) ≫ e.hom := by
  obtain ⟨e, he⟩ := GlobalTheory.T.spec_widePushout_iso_widePullback_yoneda (LaurentPolynomial A) (LaurentPolynomial A') (LaurentPolynomial (A' ⊗[A] A'))
    (laurentMap (algebraMap A A')) 1 (fun j => laurentMap (inc A A' j))
    (fun j => by rw [← GmPhiNat.laurentMap_comp, ← GmPhiNat.laurentMap_comp, inc_comp]) (laurent_univ A A')
  refine ⟨e, ?_⟩
  have he' : ∀ j : Fin (1 + 1), e.hom ≫ WidePullback.π (fun _ => (Arrow.mk (yoneda.map (fT A A'))).hom) j =
      yoneda.map (Spec.map (CommRingCat.ofHom (laurentMap (inc A A' j)))) := he
  have hπ : ∀ j : Fin (1 + 1), (e.hom ≫ (cP A A' ≫ cS A A').app (op ⦋1⦌)) ≫ WidePullback.π _ j =
      (yoneda.map (Spec.map (CommRingCat.ofHom (flat (A' ⊗[A] A')))) ≫ e.hom) ≫ WidePullback.π _ j := by
    intro j
    change (e.hom ≫ (WidePullback.lift _ _ _ ≫ WidePullback.lift _ _ _)) ≫ WidePullback.π _ j = _
    simp only [Category.assoc, WidePullback.lift_π, WidePullback.lift_π_assoc]
    rw [← Category.assoc e.hom, he' j, he j]
    simp only [constArr, oneArr, Arrow.homMk_left, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    exact flat_laurentMap (inc A A' j)
  apply WidePullback.hom_ext
  · exact hπ
  · have h0 : ∀ k : yoneda.obj (Spec (CommRingCat.of (LaurentPolynomial (A' ⊗[A] A')))) ⟶ (cech (fT A A')).obj (op ⦋1⦌),
        k ≫ WidePullback.base (fun _ : Fin (1 + 1) => (Arrow.mk (yoneda.map (fT A A'))).hom) =
          (k ≫ WidePullback.π _ 0) ≫ (Arrow.mk (yoneda.map (fT A A'))).hom := fun k => by
      rw [← WidePullback.π_arrow _ 0]; exact (Category.assoc _ _ _).symm
    erw [h0, h0, hπ 0]
    rfl

theorem cobd_pull {R : Type} [CommRing R] {E E' : Spc} {F : Shv R} {n : ℕ} (φ : E' ⟶ E)
    (σ : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F) :
    cobd ((free R).map (φ.app (op ⦋n⦌)) ≫ σ) = (free R).map (φ.app (op ⦋n + 1⦌)) ≫ cobd σ := by
  simp only [cobd, Preadditive.comp_sum, Preadditive.comp_zsmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Category.assoc, ← Functor.map_comp, SimplicialObject.δ_naturality, Functor.map_comp, Category.assoc]

theorem cobd_of_h1_zero {R : Type} [CommRing R] (F : Shv R) {Y X : Scheme.{0}} (f : Y ⟶ X) (hE : Eqv R (cechAug f) F)
    (hX : ∀ x : H R (sch.obj X) F 1, x = 0) (σ : (free R).obj ((cech f).obj (op ⦋1⦌)) ⟶ F) (hσ : cobd σ = 0) :
    ∃ τ, σ = cobd τ := by
  obtain ⟨y, hy⟩ := (GlobalTheory.T.simplicialCochain_classes_basic_properties R F (cech f) 1).1 σ hσ
  obtain ⟨x, rfl⟩ := (hE 1).2 y
  rw [hX x, map_zero] at hy
  exact GlobalTheory.T.simplicialCochain_coboundary_of_class_zero R F _ σ hy

theorem cobd_of_retract {R : Type} [CommRing R] {F : Shv R} {E E' : Spc} (P : E' ⟶ E) (S : E ⟶ E')
    (hinv : ∀ σ : (free R).obj (E'.obj (op ⦋1⦌)) ⟶ F, (free R).map ((P ≫ S).app (op ⦋1⦌)) ≫ σ = σ)
    (hE : ∀ σ : (free R).obj (E.obj (op ⦋1⦌)) ⟶ F, cobd σ = 0 → ∃ τ, σ = cobd τ)
    (σ : (free R).obj (E'.obj (op ⦋1⦌)) ⟶ F) (hσ : cobd σ = 0) : ∃ τ, σ = cobd τ := by
  obtain ⟨τ, hτ⟩ := hE ((free R).map (S.app _) ≫ σ) (by rw [cobd_pull, hσ, Limits.comp_zero])
  refine ⟨(free R).map (P.app _) ≫ τ, ?_⟩
  rw [cobd_pull, ← hτ, ← Category.assoc, ← Functor.map_comp, ← NatTrans.comp_app, hinv]

theorem fixed_of_iso {R : Type} [CommRing R] {F : Shv R} {P : PSh} {X : Scheme.{0}} (e : yoneda.obj X ≅ P) (u : P ⟶ P)
    (g : X ⟶ X) (he : e.hom ≫ u = yoneda.map g ≫ e.hom) (hs : ∀ s : Sec F X, Sec.res g s = s)
    (σ : (free R).obj P ⟶ F) : (free R).map u ≫ σ = σ := by
  have key : (free R).map (yoneda.map g) ≫ ((free R).map e.hom ≫ σ) = (free R).map e.hom ≫ σ := by
    apply CupSpec.free_ext
    intro U x
    have h1 : ∀ y : U ⟶ X, freeGen R (yoneda.obj X) U y = Sec.res y (freeGen R (yoneda.obj X) X (𝟙 X)) := by
      intro y
      rw [CupSpec.freeGen_res]
      congr 1
    change Sec.map ((free R).map e.hom ≫ σ) (Sec.map ((free R).map (yoneda.map g)) (freeGen R _ U x)) = _
    rw [CupSpec.freeGen_map]
    change Sec.map ((free R).map e.hom ≫ σ) (freeGen R _ U (x ≫ g)) = _
    rw [h1, h1 x, ← CupSpec.map_res, ← CupSpec.map_res]
    have h2 : ∀ s : Sec F X, Sec.res (x ≫ g) s = Sec.res x (Sec.res g s) := by
      intro s; simp only [Sec.res, op_comp, Functor.map_comp]; rfl
    rw [h2, hs]
  have : (free R).map e.hom ≫ ((free R).map u ≫ σ) = (free R).map e.hom ≫ σ := by
    rw [← Category.assoc, ← Functor.map_comp, he, Functor.map_comp, Category.assoc, key]
  exact (cancel_epi _).1 this

theorem tateTwistCohomology_zero_laurent_from_base (q : ℕ) [NeZero q] (T : Type) [CommRing T] (hq : IsUnit (q : T)) (i : ℤ)
    (y : Ht q (sp (LaurentPolynomial T)) 0 i) :
    ∃ z : Ht q (sp T) 0 i, pull _ (spMap (LaurentPolynomial.C : T →+* LaurentPolynomial T)) _ 0 z = y :=
  GlobalTheory.T.tateTwistCohomology_zero_laurent_surjective q T hq i y

theorem sec_flat (q : ℕ) [NeZero q] (T : Type) [CommRing T] (hq : IsUnit (q : T)) (i : ℤ)
    (s : Sec (tw q i) (Spec (CommRingCat.of (LaurentPolynomial T)))) :
    Sec.res (Spec.map (CommRingCat.ofHom (flat T))) s = s := by
  obtain ⟨-, e, he, -⟩ := GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero (ZMod q) (tw q i)
  apply (e _).injective
  rw [← he]
  obtain ⟨y, hy⟩ := tateTwistCohomology_zero_laurent_from_base q T hq i (e _ s)
  rw [← hy]
  change pull _ (spMap (flat T)) _ 0 (pull _ (spMap LaurentPolynomial.C) _ 0 y) = _
  rw [← GmPhiNat.pull_spMap_comp, flat_comp_C]

end GlobalTheory.EtC.KerLaurent

namespace GlobalTheory.EtC.KerLaurent
variable (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A']

theorem cobd_laurent (q : ℕ) [NeZero q] (hint : Algebra.IsIntegral A A')
    (hker : RingHom.ker (algebraMap A A') ≤ nilradical A) (hq : IsUnit (q : A))
    (hA : ∀ j : ℤ, Subsingleton (Ht q (sp A) 1 j)) (i : ℤ)
    (σ : (free (ZMod q)).obj ((cech (fT A A')).obj (op ⦋1⦌)) ⟶ tw q i) (hσ : cobd σ = 0) : ∃ τ, σ = cobd τ := by
  have hi : (algebraMap A A').IsIntegral := fun a => hint.isIntegral a
  obtain ⟨hf1, hf2⟩ := GmStep.spec_integral_surj (algebraMap A A') hi hker
  have hqA : IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤)) := by
    have := hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
    simpa using this
  have hE := GlobalTheory.EtC.b4 q (fB A A') hqA i
  haveI := hA i
  have hqT : IsUnit (q : A' ⊗[A] A') := by simpa using hq.map (algebraMap A (A' ⊗[A] A'))
  refine cobd_of_retract (cP A A') (cS A A') (fun σ' => ?_)
    (cobd_of_h1_zero _ (fB A A') hE (fun x => Subsingleton.elim _ _)) σ hσ
  obtain ⟨e, he⟩ := level_one A A'
  exact fixed_of_iso e _ _ he (sec_flat q _ hqT i) σ'

end GlobalTheory.EtC.KerLaurent

open GlobalTheory.EtC.KerLaurent in

theorem GlobalTheory.EtC.kerLaurent : ∀ (q : ℕ) [NeZero q] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'],
    Algebra.IsIntegral A A' → RingHom.ker (algebraMap A A') ≤ nilradical A → IsUnit (q : A) →
    (∀ j : ℤ, Subsingleton (Ht q (sp A) 1 j)) → ∀ (i : ℤ) (x : Ht q (sp (LaurentPolynomial A)) 1 i),
    pull _ (spMap (laurentMap (algebraMap A A'))) _ 1 x = 0 → x = 0 := by
  intro q _ A A' _ _ _ hint hker hq hA i x hx
  have hi : (algebraMap A A').IsIntegral := fun a => hint.isIntegral a
  have hlm : GmStep.laurentMap (algebraMap A A') = laurentMap (algebraMap A A') :=
    laurent_ext (fun a => by
      rw [GmStep.laurentMap_C]
      exact (RingHom.congr_fun (GmPhiNat.laurentMap_C _) a).symm)
      (by rw [GmStep.laurentMap_T, GmPhiNat.laurentMap_T])
  obtain ⟨hf1, hf2⟩ := GmStep.spec_integral_surj (laurentMap (algebraMap A A'))
    (hlm ▸ GmStep.laurentMap_isIntegral _ hi) (hlm ▸ GmStep.laurentMap_ker _ hker)
  have hE := GlobalTheory.EtC.b4 q (fT A A') (GmPhiNat.isUnit_gamma q A hq) i
  obtain ⟨σ, hσ, hcls⟩ := GlobalTheory.T.etaleCohomology_one_cechCocycle_of_pullback_zero (ZMod q) (tw q i) _ _ (fT A A') x hx
  obtain ⟨τ, rfl⟩ := cobd_laurent A A' q hint hker hq hA i σ hσ
  have h0 := (GlobalTheory.T.simplicialCochain_classes_basic_properties (ZMod q) (tw q i) (cech (fT A A')) 0).2.2.2.1 τ _ hcls
  exact (hE 1).1 (by rw [map_zero]; exact h0)
