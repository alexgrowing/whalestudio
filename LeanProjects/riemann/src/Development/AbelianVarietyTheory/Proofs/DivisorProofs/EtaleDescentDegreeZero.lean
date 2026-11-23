import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullSpMapComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSurjectionCechDescentTateTwistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimplicialCochainClassesBasicProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafBasicProperti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecWidePushoutIsoWidePullbackYoneda
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyPullbackEqZeroOfCechOneCocycle
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex Simplicial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.EtC.DescZero

variable {R : Type} [CommRing R]

end GlobalTheory.EtC.DescZero

namespace GlobalTheory.EtC.DescZero

theorem spec_integral_surj (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B) (hi : φ.IsIntegral)
    (hk : RingHom.ker φ ≤ nilradical A) :
    IsIntegralHom (Spec.map (CommRingCat.ofHom φ)) ∧ Surjective (Spec.map (CommRingCat.ofHom φ)) := by
  refine ⟨IsIntegralHom.SpecMap_iff.2 hi, ⟨fun (x : PrimeSpectrum A) => ?_⟩⟩
  letI := φ.toAlgebra
  haveI : Algebra.IsIntegral A B := ⟨hi⟩
  have hle : (⊥ : Ideal B).comap (algebraMap A B) ≤ x.asIdeal := by
    rw [← RingHom.ker_eq_comap_bot]
    exact hk.trans (nilradical_le_prime x.asIdeal)
  obtain ⟨Q, -, hQ, hQx⟩ := Ideal.exists_ideal_over_prime_of_isIntegral x.asIdeal ⊥ hle
  have : x ∈ Set.range (PrimeSpectrum.comap φ) := ⟨⟨Q, hQ⟩, PrimeSpectrum.ext hQx⟩
  exact this

def incl2 (A B : Type) [CommRing A] [CommRing B] [Algebra A B] : Fin 2 → (B →+* B ⊗[A] B) :=
  ![(Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B).toRingHom,
    (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom]

end GlobalTheory.EtC.DescZero

namespace GlobalTheory.EtC.DescZero

def cπ {Y X : Scheme.{0}} (f : Y ⟶ X) (n : ℕ) (k : Fin (n + 1)) : (cech f).obj (op ⦋n⦌) ⟶ (sch.obj Y).obj (op ⦋0⦌) :=
  WidePullback.π (fun _ : Fin (n + 1) => yoneda.map f) k

theorem cech_δ0_π {Y X : Scheme.{0}} (f : Y ⟶ X) :
    SimplicialObject.δ (cech f) (0 : Fin 2) ≫ cπ f 0 0 = cπ f (0 + 1) 1 :=
  WidePullback.lift_π _ _ _ _ 0

theorem cech_δ1_π {Y X : Scheme.{0}} (f : Y ⟶ X) :
    SimplicialObject.δ (cech f) (1 : Fin 2) ≫ cπ f 0 0 = cπ f (0 + 1) 0 :=
  WidePullback.lift_π _ _ _ _ 0

theorem cechDiag_π {Y X : Scheme.{0}} (f : Y ⟶ X) :
    (GlobalTheory.CechOne.cechDiag f).app (op ⦋0⦌) ≫ cπ f 0 0 = 𝟙 _ :=
  WidePullback.lift_π _ _ _ _ 0

end GlobalTheory.EtC.DescZero

namespace GlobalTheory.EtC.DescZero

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial in
open scoped TensorProduct in
private lemma spec_map_surjective_of_integral_ker_le_nilradical (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A']
    [Algebra.IsIntegral A A'] (hker : RingHom.ker (algebraMap A A') ≤ nilradical A) :
    Surjective (Spec.map (CommRingCat.ofHom (algebraMap A A'))) := by
  constructor
  intro x
  let p : PrimeSpectrum A := x
  obtain ⟨Q, -, hQ, hQx⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p.asIdeal (⊥ : Ideal A')
    (by rw [← RingHom.ker_eq_comap_bot]; exact hker.trans (nilradical_le_prime _))
  exact ⟨(⟨Q, hQ⟩ : PrimeSpectrum A'), PrimeSpectrum.ext hQx⟩

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial in
open scoped TensorProduct in
private lemma sec_res_comp_divisor {R : Type} [CommRing R] {F : _root_.GlobalTheory.EtC.Shv R} {W V U : Scheme}
    (h : W ⟶ V) (g : V ⟶ U) (s : _root_.GlobalTheory.EtC.Sec F U) :
    _root_.GlobalTheory.EtC.Sec.res (h ≫ g) s =
      _root_.GlobalTheory.EtC.Sec.res h (_root_.GlobalTheory.EtC.Sec.res g s) := by
  simp [_root_.GlobalTheory.EtC.Sec.res]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial in
open scoped TensorProduct in
private lemma disc_face_eq_id (P : _root_.GlobalTheory.EtC.PSh) (n : ℕ) (i : Fin (n + 2)) :
    SimplicialObject.δ (_root_.GlobalTheory.EtC.disc.obj P) i = 𝟙 _ := by
  first | rfl | simp [SimplicialObject.δ, _root_.GlobalTheory.EtC.disc]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial in
open scoped TensorProduct in
private lemma cobd_eq_zero_of_scheme {R : Type} [CommRing R] {F : _root_.GlobalTheory.EtC.Shv R} (X : Scheme)
    (t : (_root_.GlobalTheory.EtC.free R).obj ((_root_.GlobalTheory.EtC.sch.obj X) _⦋0⦌) ⟶ F) :
    _root_.GlobalTheory.EtC.cobd t = 0 := by
  have h : ∀ i : Fin 2, SimplicialObject.δ (_root_.GlobalTheory.EtC.sch.obj X) i = 𝟙 _ :=
    fun i => disc_face_eq_id (yoneda.obj X) 0 i
  unfold _root_.GlobalTheory.EtC.cobd
  simp [Fin.sum_univ_two, h]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial in
open scoped TensorProduct in
private lemma isCls_secClass_of_val_eq_res {R : Type} [CommRing R] (F : _root_.GlobalTheory.EtC.Shv R)
    (X : Scheme) (s : _root_.GlobalTheory.EtC.Sec F X)
    (t : (_root_.GlobalTheory.EtC.free R).obj ((_root_.GlobalTheory.EtC.sch.obj X) _⦋0⦌) ⟶ F)
    (ht : ∀ (U : Scheme) (x : U ⟶ X), _root_.GlobalTheory.EtC.val t U x = _root_.GlobalTheory.EtC.Sec.res x s) :
    _root_.GlobalTheory.EtC.IsCls t (_root_.GlobalTheory.EtC.secClass F s) := by
  obtain ⟨hex, -, -, -, -⟩ :=
    _root_.GlobalTheory.EtC.isCls_basic R F (_root_.GlobalTheory.EtC.sch.obj X) 0
  obtain ⟨x, hx⟩ := hex t (cobd_eq_zero_of_scheme X t)
  suffices hxs : x = _root_.GlobalTheory.EtC.secClass F s by rw [← hxs]; exact hx
  obtain ⟨z, hz, hzv⟩ := hx
  rw [← hz]
  refine ((_root_.GlobalTheory.EtC.secClass_props R F X).1 s z).1 ?_
  have key : ∀ h, (z : Cochain _ _ ((0 : ℕ) : ℤ)).v (-((0 : ℕ) : ℤ)) 0 h =
      (_root_.GlobalTheory.EtC.chainsXIso R (_root_.GlobalTheory.EtC.sch.obj X) 0).hom ≫ t ≫
        _root_.GlobalTheory.EtC.resι R F := by
    intro h
    rw [hzv]
    exact Cochain.single_v _ _ _
  erw [_root_.GlobalTheory.EtC.CupSpec.ev_def, key, Iso.inv_hom_id_assoc]
  have hval := ht X (𝟙 X)
  calc _ = _root_.GlobalTheory.EtC.Sec.map (_root_.GlobalTheory.EtC.resι R F)
        (_root_.GlobalTheory.EtC.val t X (𝟙 X)) := rfl
    _ = _ := by rw [hval]; simp [_root_.GlobalTheory.EtC.Sec.res]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial in
open scoped TensorProduct in
private lemma cobd_eq_zero_of_face_comp_eq {R : Type} [CommRing R] {F : _root_.GlobalTheory.EtC.Shv R}
    {E : _root_.GlobalTheory.EtC.Spc} (T : (_root_.GlobalTheory.EtC.free R).obj (E _⦋0⦌) ⟶ F)
    (h : (_root_.GlobalTheory.EtC.free R).map (SimplicialObject.δ E 0) ≫ T =
      (_root_.GlobalTheory.EtC.free R).map (SimplicialObject.δ E 1) ≫ T) :
    _root_.GlobalTheory.EtC.cobd T = 0 := by
  unfold _root_.GlobalTheory.EtC.cobd
  simp [Fin.sum_univ_two, h]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial in
open scoped TensorProduct in
private lemma cech_face_comp_cπ_eq_cπ_rev {Y X : Scheme.{0}} (f : Y ⟶ X) (i : Fin 2) :
    SimplicialObject.δ (_root_.GlobalTheory.EtC.cech f) i ≫ _root_.GlobalTheory.EtC.DescZero.cπ f 0 0 =
      _root_.GlobalTheory.EtC.DescZero.cπ f 1 i.rev := by
  fin_cases i <;>
  · simp only [_root_.GlobalTheory.EtC.DescZero.cπ, _root_.GlobalTheory.EtC.cech, SimplicialObject.δ, Arrow.cechNerve]
    erw [WidePullback.lift_π]
    rfl

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial in
open scoped TensorProduct in
private lemma res_eq_of_tensorSquare_res_eq_lemma_6 {R : Type} [CommRing R] {F : _root_.GlobalTheory.EtC.Shv R}
    (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A']
    (s : _root_.GlobalTheory.EtC.Sec F (Spec (CommRingCat.of A')))
    (hs : _root_.GlobalTheory.EtC.Sec.res
        (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : A' →ₐ[A] A' ⊗[A] A').toRingHom)) s =
      _root_.GlobalTheory.EtC.Sec.res
        (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : A' →ₐ[A] A' ⊗[A] A').toRingHom)) s)
    {U : Scheme} (y₀ y₁ : U ⟶ Spec (CommRingCat.of A'))
    (hy : y₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap A A')) =
      y₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap A A'))) :
    _root_.GlobalTheory.EtC.Sec.res y₀ s = _root_.GlobalTheory.EtC.Sec.res y₁ s := by
  let u := pullback.lift y₀ y₁ hy ≫ (pullbackSpecIso A A' A').hom
  have hu₀ : u ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft : A' →ₐ[A] A' ⊗[A] A').toRingHom) = y₀ := by
    simp only [u, Category.assoc]
    erw [pullbackSpecIso_hom_fst]
    exact pullback.lift_fst _ _ _
  have hu₁ : u ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : A' →ₐ[A] A' ⊗[A] A').toRingHom) = y₁ := by
    simp only [u, Category.assoc]
    erw [pullbackSpecIso_hom_snd]
    exact pullback.lift_snd _ _ _
  clear_value u
  rw [← hu₀, ← hu₁, sec_res_comp_divisor, sec_res_comp_divisor, hs]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial in
open scoped TensorProduct in
private lemma cπ_comp_eq_cπ_comp {Y X : Scheme.{0}} (f : Y ⟶ X) (n : ℕ) (k l : Fin (n + 1))
    (U : Scheme.{0}) (e : ((_root_.GlobalTheory.EtC.cech f).obj (op ⦋n⦌)).obj (op U)) :
    (show U ⟶ Y from (_root_.GlobalTheory.EtC.DescZero.cπ f n k).app (op U) e) ≫ f =
      (show U ⟶ Y from (_root_.GlobalTheory.EtC.DescZero.cπ f n l).app (op U) e) ≫ f := by
  have h := (WidePullback.π_arrow (fun _ : Fin (n + 1) => yoneda.map f) k).trans
    (WidePullback.π_arrow (fun _ : Fin (n + 1) => yoneda.map f) l).symm
  exact congr_arg (fun φ => φ.app (op U) e) h

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial in
open scoped TensorProduct in
private lemma cechDiag_comp_cπ_eq_id {Y X : Scheme.{0}} (f : Y ⟶ X) :
    (_root_.GlobalTheory.CechOne.cechDiag f).app (op ⦋0⦌) ≫ _root_.GlobalTheory.EtC.DescZero.cπ f 0 0 = 𝟙 _ := by
  simp only [_root_.GlobalTheory.CechOne.cechDiag, _root_.GlobalTheory.EtC.DescZero.cπ]
  erw [WidePullback.lift_π]
  rfl

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial in
open scoped TensorProduct in

theorem _root_.GlobalTheory.EtC.DescZero.desc_zero : ∀ (q : ℕ) [NeZero q] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'],
    Algebra.IsIntegral A A' → RingHom.ker (algebraMap A A') ≤ nilradical A → IsUnit (q : A) →
    ∀ (j : ℤ) (b : _root_.GlobalTheory.EtC.Ht q (_root_.GlobalTheory.EtC.sp A') 0 j),
      _root_.GlobalTheory.EtC.pull _ (_root_.GlobalTheory.EtC.spMap (Algebra.TensorProduct.includeLeft : A' →ₐ[A] A' ⊗[A] A').toRingHom) _ 0 b =
        _root_.GlobalTheory.EtC.pull _ (_root_.GlobalTheory.EtC.spMap (Algebra.TensorProduct.includeRight : A' →ₐ[A] A' ⊗[A] A').toRingHom) _ 0 b →
      ∃ a : _root_.GlobalTheory.EtC.Ht q (_root_.GlobalTheory.EtC.sp A) 0 j, _root_.GlobalTheory.EtC.pull _ (_root_.GlobalTheory.EtC.spMap (algebraMap A A')) _ 0 a = b := by
  intro q _ A A' _ _ _ hint hker hq j b hb
  let f : Spec (CommRingCat.of A') ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A A'))
  haveI : IsIntegralHom f := by rw [IsIntegralHom.SpecMap_iff]; exact hint.isIntegral
  haveI : Surjective f := spec_map_surjective_of_integral_ker_le_nilradical A A' hker
  have hbij : Function.Bijective
      (_root_.GlobalTheory.EtC.pull (ZMod q) (_root_.GlobalTheory.EtC.cechAug f) (_root_.GlobalTheory.EtC.tw q j) 0) :=
    _root_.GlobalTheory.EtC.b4 q f
      (by simpa using hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) j 0
  set F := _root_.GlobalTheory.EtC.tw q j with hF
  obtain ⟨-, hbijc, -, hres, -⟩ := _root_.GlobalTheory.EtC.secClass_props (ZMod q) F (Spec (CommRingCat.of A'))
  obtain ⟨s, rfl⟩ := hbijc.2 b
  have hs : _root_.GlobalTheory.EtC.Sec.res
        (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : A' →ₐ[A] A' ⊗[A] A').toRingHom)) s =
      _root_.GlobalTheory.EtC.Sec.res
        (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : A' →ₐ[A] A' ⊗[A] A').toRingHom)) s := by
    apply (_root_.GlobalTheory.EtC.secClass_props (ZMod q) F _).2.1.1
    rw [← hres, ← hres]
    exact hb
  have hfreeY := _root_.GlobalTheory.EtC.FreeHom.main (ZMod q)
    ((_root_.GlobalTheory.EtC.sch.obj (Spec (CommRingCat.of A'))) _⦋0⦌) F
  obtain ⟨t, ht⟩ := hfreeY.2.1
    (fun U x => _root_.GlobalTheory.EtC.Sec.res (show U ⟶ Spec (CommRingCat.of A') from x) s)
    (fun V U g x => sec_res_comp_divisor g (show U ⟶ Spec (CommRingCat.of A') from x) s)
  have hrep := isCls_secClass_of_val_eq_res F _ s t ht
  obtain ⟨hex, -, -, -, hpull⟩ :=
    _root_.GlobalTheory.EtC.isCls_basic (ZMod q) F (_root_.GlobalTheory.EtC.cech f) 0
  obtain ⟨T, hTdef⟩ : ∃ T, T =
      (_root_.GlobalTheory.EtC.free (ZMod q)).map (_root_.GlobalTheory.EtC.DescZero.cπ f 0 0) ≫ t :=
    ⟨_, rfl⟩
  have hT : _root_.GlobalTheory.EtC.cobd T = 0 := by
    refine cobd_eq_zero_of_face_comp_eq T ?_
    have hfree := _root_.GlobalTheory.EtC.FreeHom.main (ZMod q)
      ((_root_.GlobalTheory.EtC.cech f) _⦋1⦌) F
    apply hfree.1
    intro U e
    simp only [hTdef, ← Functor.map_comp_assoc, cech_face_comp_cπ_eq_cπ_rev]
    rw [hfreeY.2.2.2.1, hfreeY.2.2.2.1, ht, ht]
    exact res_eq_of_tensorSquare_res_eq_lemma_6 A A' s hs _ _
      (cπ_comp_eq_cπ_comp f 1 (Fin.rev 0) (Fin.rev 1) U e)
  obtain ⟨x, hx⟩ := hex T hT
  have hcx : _root_.GlobalTheory.EtC.pull (ZMod q) (_root_.GlobalTheory.CechOne.cechDiag f) F 0 x =
      _root_.GlobalTheory.EtC.secClass F s := by
    refine (_root_.GlobalTheory.EtC.isCls_basic (ZMod q) F
      (_root_.GlobalTheory.EtC.sch.obj (Spec (CommRingCat.of A'))) 0).2.2.1 t _ _ ?_ hrep
    have h := hpull _ (_root_.GlobalTheory.CechOne.cechDiag f) T x hx
    have hcomp : (_root_.GlobalTheory.EtC.free (ZMod q)).map
        ((_root_.GlobalTheory.CechOne.cechDiag f).app (op ⦋0⦌)) ≫ T = t := by
      rw [hTdef, ← Functor.map_comp_assoc]
      erw [cechDiag_comp_cπ_eq_id]
      rw [CategoryTheory.Functor.map_id, Category.id_comp]
    rw [hcomp] at h
    exact h
  obtain ⟨a, ha⟩ := hbij.2 x
  refine ⟨a, ?_⟩
  change _root_.GlobalTheory.EtC.pull (ZMod q) (_root_.GlobalTheory.EtC.sch.map f) F 0 a = _
  rw [← _root_.GlobalTheory.CechOne.cechDiag_aug, _root_.GlobalTheory.EtC.pull_comp, ha, hcx]

end GlobalTheory.EtC.DescZero

end
