import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsMonHomIffOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAlgClosedJoinOfTwoFieldExtensions
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfFieldExtensionBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianSchemeDescentSmoothDimensionStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RigidifiedSymmetricKernelTrivialDescendFieldExtStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilPairingFieldExtensionIffStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ThetaDescent

theorem map_prod_pow {M N : Type*} [Monoid M] [Monoid N] (P : M →* N) {n : ℕ} (p : Fin n → M) (a : Fin n → ℕ) :
    P (List.ofFn fun i => p i ^ a i).prod = (List.ofFn fun i => P (p i) ^ a i).prod := by
  simp only [map_list_prod, List.map_ofFn, Function.comp_def, map_pow]

theorem existsUnique_transfer {M M₀ N C : Type*} [Monoid M] [Monoid M₀] [Monoid N] (P : M →* N) (R : M₀ →* N)
    (hP : Function.Bijective P) (hR : Function.Injective R) {n : ℕ} (p : Fin n → M) (p₀ : Fin n → M₀)
    (h : ∀ i, P (p i) = R (p₀ i)) (k : ℕ) (e : C → Fin n → ℕ)
    (H : ∀ y : M, y ^ k = 1 → ∃! c : C, (List.ofFn fun i => p i ^ e c i).prod = y)
    (y₀ : M₀) (hy : y₀ ^ k = 1) : ∃! c : C, (List.ofFn fun i => p₀ i ^ e c i).prod = y₀ := by
  obtain ⟨y, hyR⟩ := hP.2 (R y₀)
  have hyk : y ^ k = 1 := hP.1 (by rw [map_pow, hyR, ← map_pow, hy, map_one, map_one])
  have key : ∀ c : C, (List.ofFn fun i => p₀ i ^ e c i).prod = y₀ ↔ (List.ofFn fun i => p i ^ e c i).prod = y := by
    intro c
    rw [← hR.eq_iff, ← hP.1.eq_iff, hyR, map_prod_pow, map_prod_pow]
    simp only [h]
  simpa only [key] using H y hyk

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

theorem pushHom_left (h : IsGrpPullback G' G f φ) (T : Over S') (x : T ⟶ G') :
    (pushHom h T x).left = x.left ≫ φ := rfl

theorem pushHom_bijective (h : IsGrpPullback G' G f φ) (T : Over S') : Function.Bijective (pushHom h T) := by
  refine ⟨fun x y hxy => ?_, fun z => ?_⟩
  · have e := congrArg (fun u => u.left) hxy
    simp only [pushHom_left] at e
    exact Over.OverMorphism.ext (h.1.hom_ext e (by rw [Over.w x, Over.w y]))
  · refine ⟨Over.homMk (h.1.lift z.left T.hom (Over.w z)) (h.1.lift_snd _ _ _), ?_⟩
    ext1
    rw [pushHom_left]
    exact h.1.lift_fst _ _ _

theorem preHom_injective {T T' : Over S} (U : T' ⟶ T) [Epi U.left] :
    Function.Injective (preHom (G := G) U) := by
  intro x y hxy
  ext1
  rw [← cancel_epi U.left, ← Over.comp_left, ← Over.comp_left]
  exact congrArg (fun u => u.left) hxy

theorem weilIs_congr {Z : Scheme.{0}} {s s' : Z ⟶ S} (e : s = s') (L : LB G.left) (k : ℤ)
    (x y : Over.mk s ⟶ G) (x' y' : Over.mk s' ⟶ G) (hx : x.left = x'.left) (hy : y.left = y'.left)
    (c : Γ(Z, ⊤)ˣ) : Out.WeilIs G L k x y c ↔ Out.WeilIs G L k x' y' c := by
  subst e
  obtain rfl : x = x' := Over.OverMorphism.ext hx
  obtain rfl : y = y' := Over.OverMorphism.ext hy
  exact Iff.rfl

theorem unitS_spMap {o R : Type} [CommRing o] [CommRing R] (β : o →+* R) (u : oˣ) (n : ℤ) :
    unitS (spMap β) u ^ n = unitOn (Units.map β.toMonoidHom u ^ n) := by
  unfold unitS unitOn
  simp only [← map_zpow]
  ext1
  simp only [Units.coe_map]
  exact (congrArg (fun g => CommRingCat.Hom.hom g ((u ^ n : oˣ) : o)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm

theorem epi_spMap {K Ω : Type} [Field K] [Field Ω] (j : K →+* Ω) : Epi (spMap j) := by
  have := (GlobalTheory.FieldBaseChange.epi_and_isMonHom_iff K Ω j).1 (Sp K) (Sp Ω) (𝟙 _) (𝟙 _) (spMap j)
    (IsPullback.of_vert_isIso ⟨by simp⟩)
  exact this.1

end GlobalTheory.ThetaDescent

namespace GlobalTheory

open ThetaDescent

theorem exists_thetaObj_of_descended_data : ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (β₀ : o →+* K₀) (β : o →+* K) (t : TObj g k J b (spMap β)) (A₀ : Over (Sp K₀)) [GrpObj A₀] (φ : t.A.left ⟶ A₀.left) (L₀ : LB A₀.left) (pt₀ : Fin (2 * g) → (Out.baseOver (Sp K₀) ⟶ A₀)) (act₀ : J → (A₀ ⟶ A₀)), i.comp β₀ = β → IsGrpPullback t.A A₀ (spMap i) φ → L₀.IsLB → LBIso t.L (L₀.pull φ) → (∀ a, (t.pt a).left ≫ φ = spMap i ≫ (pt₀ a).left) → (∀ j, (t.act j).left ≫ φ = φ ≫ (act₀ j).left) → ∃ t₀ : TObj g k J b (spMap β₀), TMap t t₀ (spMap i) := by
  intro o _ g k J b K₀ K _ _ i β₀ β t A₀ _ φ L₀ pt₀ act₀ hβ hpb hL₀ hLiso hpt hact
  obtain ⟨hab, hdim⟩ := GlobalTheory.T.abelian_scheme_descent_smooth_dimension K₀ K i A₀ t.A φ hpb t.ab
  obtain ⟨hrig, hsym, hkt⟩ := GlobalTheory.T.rigidified_symmetric_kernelTrivial_descend_fieldExt K₀ K i A₀ t.A φ L₀ t.L hab hpb hL₀ t.isLB hLiso
  have hamp := GlobalTheory.AmpleDescent.relAmple_of_fieldExtension K₀ K i A₀ t.A φ L₀ t.L hab hpb hL₀ t.isLB hLiso t.ample
  have hmon := (GlobalTheory.FieldBaseChange.epi_and_isMonHom_iff K₀ K i).2
  refine ⟨{ A := A₀, ab := hab, dim := hdim g t.dim, L := L₀, isLB := hL₀
            rigid := hrig t.rigid, sym := hsym (TObj.sym t), ample := hamp, ktriv := hkt t.ktriv
            pt := pt₀, torsion := ?_, bij := ?_, pairing := ?_, act := act₀
            hom := fun j => (hmon A₀ A₀ t.A t.A φ φ (act₀ j) (t.act j) hpb hpb (hact j).symm).1 (t.hom j) },
    φ, hpb, hLiso, hpt, hact⟩
  ·
    intro a
    obtain ⟨U0, hU0⟩ : ∃ U0 : Over.mk ((Out.baseOver (Sp K)).hom ≫ spMap i) ⟶ Out.baseOver (Sp K₀),
        U0.left = spMap i := ⟨Over.homMk (spMap i) (by simp), rfl⟩
    have hE : Epi U0.left := by rw [hU0]; exact epi_spMap i
    apply preHom_injective U0
    have e1 : preHom U0 (pt₀ a) = pushHom hpb _ (t.pt a) := by
      ext1
      show (U0 ≫ pt₀ a).left = _
      rw [Over.comp_left, hU0, pushHom_left, hpt a]
    rw [map_pow, map_one, e1, ← map_pow, t.torsion a, map_one]
  ·
    intro K' _ _ x y hy
    obtain ⟨χ, rfl⟩ : ∃ χ : K₀ →+* K', spMap χ = x := ⟨(Spec.preimage x).hom, by
      show Spec.map (CommRingCat.ofHom _) = x
      rw [CommRingCat.ofHom_hom, Spec.map_preimage]⟩
    obtain ⟨Ω, _, _, jK, jL, hcomm⟩ : ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (jK : K →+* Ω) (jL : K' →+* Ω),
        jK.comp i = jL.comp χ := by
      let _ : Algebra K₀ K := i.toAlgebra
      let _ : Algebra K₀ K' := χ.toAlgebra
      have : Nontrivial (K ⊗[K₀] K') :=
        Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain K₀ K K' i.injective χ.injective
      obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[K₀] K')
      let _ := Ideal.Quotient.field m
      refine ⟨AlgebraicClosure (K ⊗[K₀] K' ⧸ m), inferInstance, inferInstance,
        ((algebraMap (K ⊗[K₀] K' ⧸ m) (AlgebraicClosure (K ⊗[K₀] K' ⧸ m))).comp (Ideal.Quotient.mk m)).comp
          (Algebra.TensorProduct.includeLeft : K →ₐ[K₀] K ⊗[K₀] K').toRingHom,
        ((algebraMap (K ⊗[K₀] K' ⧸ m) (AlgebraicClosure (K ⊗[K₀] K' ⧸ m))).comp (Ideal.Quotient.mk m)).comp
          (Algebra.TensorProduct.includeRight : K' →ₐ[K₀] K ⊗[K₀] K').toRingHom, ?_⟩
      ext r
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      have h1 := (Algebra.TensorProduct.includeLeft : K →ₐ[K₀] K ⊗[K₀] K').commutes r
      have h2 := (Algebra.TensorProduct.includeRight : K' →ₐ[K₀] K ⊗[K₀] K').commutes r
      exact congrArg (fun z => algebraMap (K ⊗[K₀] K' ⧸ m) (AlgebraicClosure (K ⊗[K₀] K' ⧸ m))
        (Ideal.Quotient.mk m z)) (h1.trans h2.symm)
    have hw : spMap jL ≫ spMap χ = spMap jK ≫ spMap i := by
      show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hcomm]
    have hE : Epi (Over.Hom.left (Over.homMk (spMap jL) hw :
        Over.mk (spMap jK ≫ spMap i) ⟶ Over.mk (spMap χ))) := epi_spMap jL
    refine existsUnique_transfer (pushHom hpb (Over.mk (spMap jK)))
      (preHom (G := A₀) (Over.homMk (spMap jL) hw : Over.mk (spMap jK ≫ spMap i) ⟶ Over.mk (spMap χ)))
      (pushHom_bijective hpb _) (preHom_injective _)
      (fun a => (Over.homMk (spMap jK) (by simp) : Over.mk (spMap jK) ⟶ Out.baseOver (Sp K)) ≫ t.pt a)
      (fun a => (Over.homMk (spMap χ) (by simp) : Over.mk (spMap χ) ⟶ Out.baseOver (Sp K₀)) ≫ pt₀ a)
      ?_ k (fun (c : Ix g k) a => (c a).val) (fun z hz => t.bij Ω (spMap jK) z hz) y hy
    intro a
    ext1
    rw [pushHom_left]
    show ((Over.homMk (spMap jK) (by simp) : Over.mk (spMap jK) ⟶ Out.baseOver (Sp K)) ≫ t.pt a).left ≫ φ = ((Over.homMk (spMap jL) hw : Over.mk (spMap jK ≫ spMap i) ⟶ Over.mk (spMap χ)) ≫
      (Over.homMk (spMap χ) (by simp) : Over.mk (spMap χ) ⟶ Out.baseOver (Sp K₀)) ≫ pt₀ a).left
    simp only [Over.comp_left, Over.homMk_left, Category.assoc]
    rw [hpt a, ← Category.assoc, ← Category.assoc, hw]
  ·
    intro a a'
    subst hβ
    have := t.ab.comm
    have h1 := (GlobalTheory.weilIs_grpPullback_of_comm' (Sp K₀) (Sp K) A₀ t.A (spMap i) φ L₀ t.L hL₀ t.isLB hpb hLiso
      (Out.baseOver (Sp K)) (k : ℤ) (t.pt a) (t.pt a') (pushHom hpb _ (t.pt a)) (pushHom hpb _ (t.pt a')) _
      (pushHom_left hpb _ _) (pushHom_left hpb _ _)).1 (t.pairing a a')
    have e1 : unitS (spMap (i.comp β₀)) b.ζ ^ (Out.stdSymp g a a') =
        unitOn (Units.map i.toMonoidHom (Units.map β₀.toMonoidHom b.ζ ^ (Out.stdSymp g a a'))) := by
      rw [unitS_spMap, map_zpow]
      rfl
    rw [e1] at h1
    have hxa : ∀ c, (pushHom hpb (Out.baseOver (Sp K)) (t.pt c)).left =
        ((Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ 𝟙 (Sp K₀)) ⟶ Over.mk (𝟙 (Sp K₀))) ≫ pt₀ c).left := by
      intro c
      rw [pushHom_left, hpt c]
      rfl
    have h2 := (weilIs_congr (s' := spMap i ≫ 𝟙 (Sp K₀)) (by simp) L₀ (k : ℤ) _ _ _ _ (hxa a) (hxa a') _).1 h1
    have h3 := (GlobalTheory.T.weilPairing_fieldExtension_iff (Sp K₀) A₀ K₀ K i (𝟙 _) L₀ k (pt₀ a) (pt₀ a')
      (Units.map β₀.toMonoidHom b.ζ ^ Out.stdSymp g a a') hab hL₀).1 h2
    rw [unitS_spMap]
    exact h3

end GlobalTheory
