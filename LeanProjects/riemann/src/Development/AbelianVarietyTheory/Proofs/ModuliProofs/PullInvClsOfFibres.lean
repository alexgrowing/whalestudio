import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescentOfIsReduced
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsRigidifiedTwist
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianSchemeIdPowFiniteEtaleSurjective

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.OddDescent

open CechPic

theorem dense_of_denseP {R : Type} [CommRing R] {P : Set (Ideal R)} (h : DenseP P) :
    Dense {p : PrimeSpectrum R | p.asIdeal ∈ P} := by
  rw [dense_iff_closure_eq, ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
  have hv : PrimeSpectrum.vanishingIdeal {p : PrimeSpectrum R | p.asIdeal ∈ P} = ⊥ := by
    rw [eq_bot_iff]
    intro f hf
    rw [Ideal.mem_bot]
    refine h f fun p hp hpp => ?_
    exact (PrimeSpectrum.mem_vanishingIdeal _ _).1 hf ⟨p, hpp⟩ hp
  rw [hv, PrimeSpectrum.zeroLocus_bot]

theorem mem_range_spMap {R K : Type} [CommRing R] [Field K] (x : R →+* K) (p : PrimeSpectrum R)
    (h : RingHom.ker x = p.asIdeal) : p ∈ Set.range (spMap x) := by
  refine ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K), ?_⟩
  apply PrimeSpectrum.ext
  change (PrimeSpectrum.comap x ⟨⊥, Ideal.isPrime_bot⟩).asIdeal = p.asIdeal
  rw [PrimeSpectrum.comap_asIdeal, ← h, RingHom.ker_eq_comap_bot]

private theorem pow_left_comp_eq_of_isGrpPullback {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Over S'} (x : T ⟶ G')
    (x₀ : Over.mk (T.hom ≫ f) ⟶ G) (hx : x₀.left = x.left ≫ φ) (m : ℕ) :
    (x ^ m).left ≫ φ = (x₀ ^ m).left := by
  induction m with
  | zero =>
    let y₀ : Over.mk (T.hom ≫ f) ⟶ G :=
      Over.homMk ((1 : T ⟶ G').left ≫ φ) (by
        rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]
        rfl)
    have hy : y₀ * y₀ = y₀ := by
      ext1
      rw [h.2 T 1 1 y₀ y₀ rfl rfl, _root_.mul_one]
      rfl
    have h1 : y₀ = 1 := mul_eq_left.mp hy
    simp only [pow_zero]
    exact congrArg CommaMorphism.left h1
  | succ n ih =>
    rw [pow_succ, pow_succ, h.2 T (x ^ n) x (x₀ ^ n) x₀ ih.symm hx]

section Pull
variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
  {φ : G'.left ⟶ G.left}

theorem pow_left_comp (h : IsGrpPullback G' G f φ) (m : ℕ) :
    ((𝟙 G') ^ m).left ≫ φ = φ ≫ ((𝟙 G) ^ m).left := by
  let ψ : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk φ h.1.w
  have e1 := pow_left_comp_eq_of_isGrpPullback h (𝟙 G') ψ (by simp [ψ]) m
  rw [e1]
  have e2 : ψ ≫ (𝟙 G) ^ m = ψ ^ m := by rw [MonObj.comp_pow, Category.comp_id]
  rw [← e2, Over.comp_left]
  rfl

private theorem eq_inv_of_left_eq_inv_comp_of_isGrpPullback (h : IsGrpPullback G' G f φ) {T : Over S'} (x : T ⟶ G')
    (x₀ : Over.mk (T.hom ≫ f) ⟶ G) (hx : x₀.left = x.left ≫ φ) (y₀ : Over.mk (T.hom ≫ f) ⟶ G)
    (hy : y₀.left = (x⁻¹).left ≫ φ) : y₀ = x₀⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  ext1
  rw [h.2 T x⁻¹ x y₀ x₀ hy hx, inv_mul_cancel]
  have e := pow_left_comp_eq_of_isGrpPullback h x x₀ hx 0
  simp only [pow_zero] at e
  exact e

theorem inv_left_comp (h : IsGrpPullback G' G f φ) :
    (GrpObj.inv : G' ⟶ G').left ≫ φ = φ ≫ (GrpObj.inv : G ⟶ G).left := by
  let ψ : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk φ h.1.w
  let y₀ : Over.mk (G'.hom ≫ f) ⟶ G :=
    Over.homMk ((GrpObj.inv : G' ⟶ G').left ≫ φ) (by
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]
      rfl)
  have e := eq_inv_of_left_eq_inv_comp_of_isGrpPullback h (𝟙 G') ψ (by simp [ψ]) y₀ (by simp [y₀, GrpObj.inv_eq_inv])
  have e2 : ψ ≫ (GrpObj.inv : G ⟶ G) = ψ⁻¹ := by rw [GrpObj.inv_eq_inv, GrpObj.comp_inv, Category.comp_id]
  change y₀.left = ψ.left ≫ (GrpObj.inv : G ⟶ G).left
  rw [← Over.comp_left, e2, e]

private theorem pic_eq_zero_of_pull_ι_eq_zero_of_opens_eq_whole {X : Scheme.{0}} (V : X.Opens) (hV : V = ⊤)
    (c : CechPic.Pic X) (h : CechPic.pull V.ι c = 0) : c = 0 := by
  subst hV
  have e := congrArg (CechPic.pull X.topIso.inv) h
  rw [← CechPic.pull_comp, Scheme.toIso_inv_ι, CechPic.pull_id, map_zero] at e
  exact e

end Pull

theorem pull_inv_cls_of_sym {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] {L : LB A.left} (hL : L.IsLB)
    (h : Out.Sym A L) : CechPic.pull (GrpObj.inv : A ⟶ A).left (cls L hL) = cls L hL := by
  obtain ⟨U, hU, t, ht⟩ := h (Classical.arbitrary _)
  have hpt : ∀ a b : ↥(Sp K), a = b := fun a b => @Subsingleton.elim (PrimeSpectrum K) _ a b
  have hV : A.hom ⁻¹ᵁ U = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    rw [Scheme.Hom.mem_preimage, hpt (A.hom y) (Classical.arbitrary _)]
    exact hU
  have hN := LB.isLB_linComb hL ![(A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left, (A.hom ⁻¹ᵁ U).ι] ![1, -1]
  have h0 := (cls_eq_zero_iff hN).2 ⟨t, ht⟩
  rw [cls_linComb hL] at h0
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul,
    neg_smul, pull_comp] at h0
  rw [← sub_eq_add_neg, ← map_sub] at h0
  exact sub_eq_zero.1 (pic_eq_zero_of_pull_ι_eq_zero_of_opens_eq_whole _ hV _ h0)

theorem sym_of_pull_inv_cls {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left} (hL : L.IsLB)
    (h : CechPic.pull (GrpObj.inv : A ⟶ A).left (cls L hL) = cls L hL) : Out.Sym A L := by
  unfold Out.Sym
  intro s
  refine ⟨⊤, by simp, ?_⟩
  have hN := LB.isLB_linComb hL ![(A.hom ⁻¹ᵁ ⊤).ι ≫ (GrpObj.inv : A ⟶ A).left, (A.hom ⁻¹ᵁ ⊤).ι] ![1, -1]
  refine (cls_eq_zero_iff hN).1 ?_
  rw [cls_linComb hL]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul,
    neg_smul, pull_comp, h]
  exact add_neg_cancel _

theorem eSec_inv {S : Scheme.{0}} (A : Over S) [GrpObj A] :
    eSec A ≫ (GrpObj.inv : A ⟶ A).left = eSec A := by
  unfold eSec
  rw [← Over.comp_left, GrpObj.one_inv]

theorem linComb_eq_prod {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] {n : ℕ}
    (y : Fin n → (T ⟶ A)) (a : Fin n → ℕ) : Out.linComb y a = ∏ i, y i ^ a i := by
  unfold Out.linComb
  exact List.prod_ofFn

theorem comp_linComb {S : Scheme.{0}} {A T T' : Over S} [GrpObj A] {n : ℕ} (u : T' ⟶ T)
    (y : Fin n → (T ⟶ A)) (a : Fin n → ℕ) : u ≫ Out.linComb y a = Out.linComb (fun i => u ≫ y i) a := by
  unfold Out.linComb
  let ψ : (T ⟶ A) →* (T' ⟶ A) :=
    { toFun := fun g => u ≫ g, map_one' := MonObj.comp_one u,
      map_mul' := fun g₁ g₂ => MonObj.comp_mul u g₁ g₂ }
  change ψ (List.ofFn fun i => y i ^ a i).prod = _
  rw [map_list_prod, List.map_ofFn]
  congr 2
  funext i
  exact MonObj.comp_pow (y i) (a i) u

theorem exists_torsionHom {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] {n m : ℕ} [NeZero m]
    (y : Fin n → (T ⟶ A)) (hy : ∀ i, y i ^ m = 1) :
    ∃ i : Multiplicative (Fin n → ZMod m) →* (T ⟶ A),
      (∀ c, i c = Out.linComb y fun k => (c.toAdd k).val) ∧ ∀ c, i c ^ m = 1 := by
  refine ⟨{ toFun := fun c => ∏ k, y k ^ (c.toAdd k).val, map_one' := ?_, map_mul' := ?_ },
    fun c => (linComb_eq_prod y _).symm, fun c => ?_⟩
  · simp
  · intro c c'
    simp only [toAdd_mul, Pi.add_apply]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [ZMod.val_add, ← _root_.pow_add, ← pow_eq_pow_mod _ (hy k)]
  · simp only [MonoidHom.coe_mk, OneHom.coe_mk]
    rw [← Finset.prod_pow]
    refine Finset.prod_eq_one fun k _ => ?_
    rw [← _root_.pow_mul, _root_.mul_comm, _root_.pow_mul, hy k, _root_.one_pow]

theorem comp_id_pow {S : Scheme.{0}} {A T : Over S} [GrpObj A] (x : T ⟶ A) (m : ℕ) :
    x ≫ (𝟙 A) ^ m = x ^ m := by
  rw [MonObj.comp_pow, Category.comp_id]

theorem id_pow_inv {S : Scheme.{0}} (A : Over S) [GrpObj A] (m : ℕ) :
    ((𝟙 A) ^ m).left ≫ (GrpObj.inv : A ⟶ A).left = (GrpObj.inv : A ⟶ A).left ≫ ((𝟙 A) ^ m).left := by
  rw [← Over.comp_left, ← Over.comp_left, MonObj.comp_pow, Category.comp_id, GrpObj.inv_eq_inv,
    GrpObj.comp_inv, Category.comp_id, inv_pow]

theorem pull_inv_cls_of_fibres (hsee : ∀ (R : Type) [CommRing R] [IsReduced R] (A : Over (Sp R)) [GrpObj A] (M N : LB A.left) (Sg : Set (Sp R)), IsAbelianScheme A → M.IsLB → Out.RelAmple A M → N.IsLB → Dense Sg → Out.Rigidified A N → (∀ p ∈ Sg, ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ Sp R) (X : Scheme.{0}) (φ : X ⟶ A.left) (π : X ⟶ Sp K), p ∈ Set.range x ∧ IsPullback φ π A.hom x ∧ ∃ t : (N.pull φ).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen)
    {R : Type} [CommRing R] [IsReduced R] (A : Over (Sp R)) [GrpObj A] {M N : LB A.left} {Sg : Set (Sp R)}
    (hA : IsAbelianScheme A) (hM : M.IsLB) (hamp : Out.RelAmple A M) (hN : N.IsLB) (hSg : Dense Sg)
    (h : ∀ p ∈ Sg, ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ Sp R) (B : Over (Sp K)) (_ : GrpObj B)
      (φ : B.left ⟶ A.left), p ∈ Set.range x ∧ IsGrpPullback B A x φ ∧
        CechPic.pull (GrpObj.inv : B ⟶ B).left (CechPic.pull φ (cls N hN)) = CechPic.pull φ (cls N hN)) :
    CechPic.pull (GrpObj.inv : A ⟶ A).left (cls N hN) = cls N hN := by
  have hN' := LB.isLB_linComb hN ![(GrpObj.inv : A ⟶ A).left, 𝟙 A.left] ![1, -1]
  have hc : ∀ {Y : Scheme.{0}} (r : Y ⟶ A.left), pull r (cls _ hN') =
      pull (r ≫ (GrpObj.inv : A ⟶ A).left) (cls N hN) - pull r (cls N hN) := by
    intro Y r
    rw [cls_linComb hN, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, pull_id, map_add, map_neg,
      ← pull_comp, sub_eq_add_neg]
  have hR : Out.Rigidified A (LB.LinComb N ![(GrpObj.inv : A ⟶ A).left, 𝟙 A.left] ![1, -1]) := by
    unfold Out.Rigidified
    refine (cls_eq_zero_iff (pull_isLB hN' _)).1 ?_
    rw [cls_pull hN', hc, eSec_inv, sub_self]
  obtain ⟨t, ht⟩ := hsee R A M _ Sg hA hM hamp hN' hSg hR (by
    intro p hp
    obtain ⟨K, hK, x, B, hB, φ, hpx, hφ, he⟩ := h p hp
    refine ⟨K, hK, x, B.left, φ, B.hom, hpx, hφ.1, ?_⟩
    refine (cls_eq_zero_iff (pull_isLB hN' φ)).1 ?_
    rw [cls_pull hN', hc, ← inv_left_comp hφ, pull_comp, he, sub_self])
  have h0 := (cls_eq_zero_iff hN').2 ⟨t, ht⟩
  rw [cls_linComb hN, Fin.sum_univ_two] at h0
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, pull_id] at h0
  exact add_neg_eq_zero.1 h0

theorem exists_descended_of (hsee : ∀ (R : Type) [CommRing R] [IsReduced R] (A : Over (Sp R)) [GrpObj A] (M N : LB A.left) (Sg : Set (Sp R)), IsAbelianScheme A → M.IsLB → Out.RelAmple A M → N.IsLB → Dense Sg → Out.Rigidified A N → (∀ p ∈ Sg, ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ Sp R) (X : Scheme.{0}) (φ : X ⟶ A.left) (π : X ⟶ Sp K), p ∈ Set.range x ∧ IsPullback φ π A.hom x ∧ ∃ t : (N.pull φ).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen)
    (hlin : Out.Laws → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (A : Over (Sp R)) [GrpObj A] (m : ℕ) (M : LB A.left) (Sg : Set (Sp R)) (C : Type) [CommGroup C] (i : C →* (𝟙_ (Over (Sp R)) ⟶ A)), IsAbelianScheme A → Odd m → IsUnit (m : R) → M.IsLB → Out.Rigidified A M → Out.RelAmple A M → Dense Sg → (∀ c, i c ^ m = 1) → (∀ p ∈ Sg, ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : Sp K ⟶ Sp R) (Pl : Out.PolAV (Sp K)) (φ : Pl.A.left ⟶ A.left), p ∈ Set.range x ∧ IsGrpPullback Pl.A A x φ ∧ LBIso (lbPow Pl.L (m ^ 2)) (M.pull φ)) → Out.Sym A M ∧ ∃ u : ∀ c, LB.Gen (LB.LinComb M (K := Fin 2) ![𝟙 A.left, ((toUnit A ≫ i c) * 𝟙 A).left] ![1, -1]), (∀ c, (u c).IsGen) ∧ ∀ c c', LB.Gen.Corr M _ _ _ _ (u (c * c')) (LB.mulGen M _ _ _ _ (u c) (LB.pullGen M _ _ (u c') ((toUnit A ≫ i c) * 𝟙 A).left)))
    (hfa : Out.Laws → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : LB P.A.left) (m : ℕ), Odd m → N.IsLB → LBIso (lbPow P.L (m ^ 2)) (N.pull ((𝟙 P.A) ^ m).left) → LBIso P.L (LB.LinComb N (K := Fin 2) ![𝟙 P.A.left, (GrpObj.inv : P.A ⟶ P.A).left] ![(1 - (m : ℤ)) / 2, ((m : ℤ) + 1) / 2]))
    (hcube : ∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) :
    Out.Laws → Out.Laws2 → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (A : Over (Sp R)) [GrpObj A] (g m : ℕ) (M : LB A.left) (pt : Fin (2 * g) → (𝟙_ (Over (Sp R)) ⟶ A)), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Odd m → IsUnit (m : R) → M.IsLB → Out.RelAmple A M → (∀ i, pt i ^ m = 1) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R) (y : Over.mk x ⟶ A), y ^ m = 1 → ∃! c : Ix g m, Out.linComb (fun i => toUnit (Over.mk x) ≫ pt i) (fun i => (c i).val) = y) → DenseP {q | ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : R →+* K) (Pl : Out.PolAV (Sp K)) (φ : Pl.A.left ⟶ A.left), RingHom.ker x = q ∧ IsGrpPullback Pl.A A (spMap x) φ ∧ LBIso (lbPow Pl.L (m ^ 2)) (M.pull φ)} → ∃ L : LB A.left, L.IsLB ∧ Out.Rigidified A L ∧ Out.Sym A L ∧ Out.RelAmple A L ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (Pl : Out.PolAV (Sp K)) (φ : Pl.A.left ⟶ A.left), IsGrpPullback Pl.A A (spMap x) φ → LBIso (lbPow Pl.L (m ^ 2)) (M.pull φ) → LBIso Pl.L (L.pull φ) := by
  intro hL1 hL2 R _ _ _ A _ g m M pt hA hsm hm hmu hM hamp hpt hbas hdense
  have : IsCommMonObj A := hA.1
  have hm0 : m ≠ 0 := by
    rintro rfl
    obtain ⟨k, hk⟩ := hm
    omega
  have : NeZero m := ⟨hm0⟩
  have hSg := dense_of_denseP hdense
  obtain ⟨M', hM', hrig', -, hfld', hamp'⟩ := RigidifyTwist.exists_rigidified_twist (Sp R) A M hM
  have hampM' : Out.RelAmple A M' := hamp' hA.3 hamp
  have hLP : ∀ {K : Type} [Field K] (Pl : Out.PolAV (Sp K)) (n : ℕ), (lbPow Pl.L n).IsLB := by
    intro K _ Pl n
    exact isLB_lbPow Pl.7 n
  have hfM' : ∀ {K : Type} [Field K] (x : R →+* K) (Pl : Out.PolAV (Sp K)) (φ : Pl.A.left ⟶ A.left),
      IsGrpPullback Pl.A A (spMap x) φ → LBIso (lbPow Pl.L (m ^ 2)) (M.pull φ) →
      pull φ (cls M' hM') = (m ^ 2) • cls Pl.L Pl.7 := by
    intro K _ x Pl φ hφ hiso
    rw [← cls_pull hM' φ (pull_isLB hM' φ),
      (cls_eq_iff (pull_isLB hM' φ) (pull_isLB hM φ)).2 (hfld' K (spMap x) Pl.A.left φ Pl.A.hom hφ.1.w),
      ← (cls_eq_iff (hLP Pl _) (pull_isLB hM φ)).2 hiso, cls_lbPow Pl.7]
  have hsymc : pull (GrpObj.inv : A ⟶ A).left (cls M' hM') = cls M' hM' := by
    refine pull_inv_cls_of_fibres hsee A hA hM hamp hM' hSg ?_
    rintro p ⟨K, hK, hKa, x, Pl, φ, hker, hφ, hiso⟩
    refine ⟨K, hK, spMap x, Pl.A, inferInstance, φ, mem_range_spMap x p hker, hφ, ?_⟩
    rw [hfM' x Pl φ hφ hiso, map_nsmul, pull_inv_cls_of_sym Pl.A Pl.7 Pl.9]
  obtain ⟨i, hi1, hi2⟩ := exists_torsionHom pt hpt
  obtain ⟨-, u, hu, hcoc⟩ := hlin hL1 R A m M' _ _ i hA hm hmu hM' hrig' hampM' hSg hi2 (by
    rintro p ⟨K, hK, hKa, x, Pl, φ, hker, hφ, hiso⟩
    refine ⟨K, hK, hKa, spMap x, Pl, φ, mem_range_spMap x p hker, hφ, ?_⟩
    refine (cls_eq_iff (hLP Pl _) (pull_isLB hM' φ)).1 ?_
    rw [cls_pull hM' φ, hfM' x Pl φ hφ hiso, cls_lbPow Pl.7])
  have hmuΓ : IsUnit (m : Γ(Sp R, ⊤)) := by
    have h := hmu.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    rwa [map_natCast] at h
  obtain ⟨hmon, hfin, het, hsurj⟩ := abelianScheme_id_pow_finite_etale_surjective (Sp R) A m hA hmuΓ
  obtain ⟨N, hN, hMN⟩ := LinDescent.exists_descent_of_isReduced (Sp R) A A ((𝟙 A) ^ m) _ i M' hM' hmon hfin
    het hsurj (by
      intro k _ _ t
      have key : ∀ c, toUnit (Over.mk t) ≫ i c =
          Out.linComb (fun j => toUnit (Over.mk t) ≫ pt j) (fun j => (c.toAdd j).val) := by
        intro c
        rw [hi1 c, comp_linComb]
      refine ⟨fun x => ⟨fun hx => ?_, ?_⟩, fun c hc => ?_⟩
      · rw [comp_id_pow] at hx
        obtain ⟨c, hc, -⟩ := hbas k t x hx
        exact ⟨Multiplicative.ofAdd c, by rw [key, toAdd_ofAdd]; exact hc.symm⟩
      · rintro ⟨c, rfl⟩
        rw [comp_id_pow, ← MonObj.comp_pow, hi2 c, MonObj.comp_one]
      · obtain ⟨c₀, -, huniq⟩ := hbas k t 1 (one_pow m)
        have e1 := huniq c.toAdd ((key c).symm.trans hc)
        have e0 := huniq 0 (by
          show Out.linComb _ _ = 1
          rw [linComb_eq_prod]
          simp)
        have e2 : c.toAdd = 0 := e1.trans e0.symm
        simpa using congrArg Multiplicative.ofAdd e2) u hu hcoc
  have hcM' : cls M' hM' = pull ((𝟙 A) ^ m).left (cls N hN) := by
    rw [(cls_eq_iff hM' (pull_isLB hN _)).2 hMN, cls_pull hN]
  have hab : (1 - (m : ℤ)) / 2 + ((m : ℤ) + 1) / 2 = 1 := by
    obtain ⟨k, rfl⟩ := hm
    push_cast
    omega
  have hL := LB.isLB_linComb hN ![𝟙 A.left, (GrpObj.inv : A ⟶ A).left] ![(1 - (m : ℤ)) / 2, ((m : ℤ) + 1) / 2]
  have hcL : ∀ {Y : Scheme.{0}} (r : Y ⟶ A.left), pull r (cls _ hL) =
      ((1 - (m : ℤ)) / 2) • pull r (cls N hN) +
        (((m : ℤ) + 1) / 2) • pull (r ≫ (GrpObj.inv : A ⟶ A).left) (cls N hN) := by
    intro Y r
    rw [cls_linComb hN, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pull_id, map_add, map_zsmul, ← pull_comp]
  have hfibc : ∀ {K : Type} [Field K] [IsAlgClosed K] (x : R →+* K) (Pl : Out.PolAV (Sp K))
      (φ : Pl.A.left ⟶ A.left), IsGrpPullback Pl.A A (spMap x) φ → LBIso (lbPow Pl.L (m ^ 2)) (M.pull φ) →
      pull φ (cls _ hL) = cls Pl.L Pl.7 := by
    intro K _ _ x Pl φ hφ hiso
    have hNφ := pull_isLB hN φ
    have h2 : LBIso (lbPow Pl.L (m ^ 2)) ((N.pull φ).pull ((𝟙 Pl.A) ^ m).left) := by
      refine (cls_eq_iff (hLP Pl _) (pull_isLB hNφ _)).1 ?_
      rw [cls_lbPow Pl.7, cls_pull hNφ, cls_pull hN, ← pull_comp, pow_left_comp hφ, pull_comp, ← hcM',
        hfM' x Pl φ hφ hiso]
    have h3 := hfa hL1 hcube K Pl (N.pull φ) m hm hNφ h2
    rw [hcL φ, (cls_eq_iff Pl.7 (LB.isLB_linComb hNφ _ _)).2 h3, cls_linComb hNφ, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, cls_pull hN, ← pull_comp, inv_left_comp hφ,
      Category.id_comp]
  refine ⟨_, hL, ?_, ?_, ?_, ?_⟩
  · unfold Out.Rigidified
    refine (cls_eq_zero_iff (pull_isLB hL _)).1 ?_
    rw [cls_pull hL, hcL, eSec_inv, ← add_smul, hab, one_smul]
    have := hmon
    have he : eSec A ≫ ((𝟙 A) ^ m).left = eSec A := by
      unfold eSec
      rw [← Over.comp_left, IsMonHom.one_hom]
    rw [← he, pull_comp, ← hcM', ← cls_pull hM' _ (pull_isLB hM' _)]
    unfold Out.Rigidified at hrig'
    exact (cls_eq_zero_iff (pull_isLB hM' _)).2 hrig'
  · refine sym_of_pull_inv_cls A hL (pull_inv_cls_of_fibres hsee A hA hM hamp hL hSg ?_)
    rintro p ⟨K, hK, hKa, x, Pl, φ, hker, hφ, hiso⟩
    refine ⟨K, hK, spMap x, Pl.A, inferInstance, φ, mem_range_spMap x p hker, hφ, ?_⟩
    rw [hfibc x Pl φ hφ hiso, pull_inv_cls_of_sym Pl.A Pl.7 Pl.9]
  · have hLψ : LBIso M' ((LB.LinComb N ![𝟙 A.left, (GrpObj.inv : A ⟶ A).left]
        ![(1 - (m : ℤ)) / 2, ((m : ℤ) + 1) / 2]).pull ((𝟙 A) ^ m).left) := by
      refine (cls_eq_iff hM' (pull_isLB hL _)).1 ?_
      rw [cls_pull hL, hcL, id_pow_inv A m, pull_comp, ← hcM', hsymc, ← add_smul, hab, one_smul]
    have := het
    have hr2 := relAmple_finite_pow_iso (Sp R) A A ((𝟙 A) ^ m) M' 1 one_pos hA hA hM' hfin
    have hr1 := relAmple_finite_pow_iso (Sp R) A A ((𝟙 A) ^ m) _ 1 one_pos hA hA hL hfin
    exact hr1.2.2.1 inferInstance hsurj (hr2.2.2.2 _ (pull_isLB hL _) hLψ hampM')
  · intro K _ _ x Pl φ hφ hiso
    refine (cls_eq_iff Pl.7 (pull_isLB hL φ)).1 ?_
    rw [cls_pull hL, hfibc x Pl φ hφ hiso]

end GlobalTheory.OddDescent
