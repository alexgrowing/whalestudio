import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemHomogeneousIdealOfEvalZero
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace GlobalTheory.CompanionTheory.GeoAlgInd

open MvPolynomial

def shiftE {d : ℕ} (D : ℕ) (α : Fin d →₀ ℕ) : Fin (d + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Fin.cons (D - α.degree) α : Fin (d + 1) → ℕ)

theorem shiftE_zero {d : ℕ} (D : ℕ) (α : Fin d →₀ ℕ) : shiftE D α 0 = D - α.degree := rfl

theorem shiftE_succ {d : ℕ} (D : ℕ) (α : Fin d →₀ ℕ) (k : Fin d) : shiftE D α k.succ = α k := rfl

def homogP {K : Type} [Field K] {d : ℕ} (D : ℕ) (P : MvPolynomial (Fin d) K) : MvPolynomial (Fin (d + 1)) K :=
  ∑ α ∈ P.support, monomial (shiftE D α) (coeff α P)

theorem degree_le_of_mem {K : Type} [Field K] {d D : ℕ} {P : MvPolynomial (Fin d) K} (hD : P.totalDegree ≤ D)
    {α : Fin d →₀ ℕ} (hα : α ∈ P.support) : α.degree ≤ D := by
  have h := le_totalDegree hα
  rw [Finsupp.sum_fintype _ _ (by simp)] at h
  rw [Finsupp.degree_eq_sum]
  exact h.trans hD

theorem homogenize_isHomogeneous₂ {K : Type} [Field K] {d D : ℕ} {P : MvPolynomial (Fin d) K} (hD : P.totalDegree ≤ D) :
    (homogP D P).IsHomogeneous D := by
  refine IsHomogeneous.sum _ _ _ fun α hα => isHomogeneous_monomial _ ?_
  have h := degree_le_of_mem hD hα
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_succ, shiftE_zero]
  simp only [shiftE_succ]
  rw [← Finsupp.degree_eq_sum]
  omega

theorem aeval_homogP {K : Type} [Field K] {d D : ℕ} {P : MvPolynomial (Fin d) K} (hD : P.totalDegree ≤ D)
    {R : Type} [CommRing R] [Algebra K R] (u : R) (t : Fin d → R) :
    aeval (Fin.cons u (fun k => u * t k) : Fin (d + 1) → R) (homogP D P) = u ^ D * aeval t P := by
  conv_rhs => rw [← support_sum_monomial_coeff P]
  rw [homogP, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  have h := degree_le_of_mem hD hα
  rw [aeval_monomial, aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp),
    Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, shiftE_zero, shiftE_succ, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  rw [← Finsupp.degree_eq_sum]
  have e : u ^ D = u ^ (D - α.degree) * u ^ α.degree := by rw [← pow_add]; congr 1; omega
  rw [e]; ring

section Scalars

variable {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

theorem map_map_apply {Y : Scheme.{0}} {A B C : Y.Opens} (f : Opposite.op C ⟶ Opposite.op B)
    (g : Opposite.op B ⟶ Opposite.op A) (s : Γ(Y, C)) :
    Y.presheaf.map g (Y.presheaf.map f s) = Y.presheaf.map (f ≫ g) s := by
  rw [Functor.map_comp, CommRingCat.comp_apply]

theorem ι_appTop_toZero (z : 𝒜 0) :
    (Proj.basicOpen 𝒜 1).ι.appTop ((Proj.toSpecZero 𝒜).appTop ((Scheme.ΓSpecIso _).inv z)) =
      (Proj.basicOpen 𝒜 1).topIso.inv
        (Proj.awayToSection 𝒜 1 (HomogeneousLocalization.fromZeroRingHom 𝒜 _ z)) := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
  have h1 : (Proj.basicOpen 𝒜 1).ι ≫ (Proj 𝒜).topIso.inv ≫
      ((Proj 𝒜).isoOfEq (Proj.basicOpen_one 𝒜)).inv = 𝟙 _ := by
    rw [← cancel_mono (Proj.basicOpen 𝒜 1).ι]
    simp
  have h : (Proj.basicOpen 𝒜 1).ι ≫ Proj.toSpecZero 𝒜 = Proj.basicOpenToSpec 𝒜 1 ≫
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom 𝒜 _)) := by
    rw [Proj.toSpecZero, reassoc_of% h1]
  rw [h, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    ← CommRingCat.comp_apply (Scheme.ΓSpecIso _).inv, ← Scheme.ΓSpecIso_inv_naturality,
    CommRingCat.comp_apply, Scheme.Hom.appTop, Proj.basicOpenToSpec_app_top]
  simp

theorem awayToSection_one_zero (z : 𝒜 0) :
    Proj.awayToSection 𝒜 1 (HomogeneousLocalization.fromZeroRingHom 𝒜 _ z) =
      (Proj 𝒜).presheaf.map (homOfLE le_top).op
        ((Proj.toSpecZero 𝒜).appTop ((Scheme.ΓSpecIso _).inv z)) := by
  have h := congrArg (fun s => (Proj.basicOpen 𝒜 1).topIso.hom s) (ι_appTop_toZero 𝒜 z)
  simp only [CategoryTheory.Iso.inv_hom_id_apply] at h
  rw [← h, Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom]
  exact map_map_apply _ _ _

theorem awayToSection_zero {f : A} {m : ℕ} (hf : f ∈ 𝒜 m) (z : 𝒜 0) :
    Proj.awayToSection 𝒜 f (HomogeneousLocalization.fromZeroRingHom 𝒜 _ z) =
      (Proj 𝒜).presheaf.map (homOfLE le_top).op
        ((Proj.toSpecZero 𝒜).appTop ((Scheme.ΓSpecIso _).inv z)) := by
  have h := congrArg (fun φ => φ.hom (HomogeneousLocalization.fromZeroRingHom 𝒜 _ z))
    (Proj.awayMap_awayToSection 𝒜 hf (one_mul f).symm)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom,
    HomogeneousLocalization.awayMap_fromZeroRingHom] at h
  rw [h, awayToSection_one_zero, map_map_apply]
  rfl

end Scalars

abbrev cst {K : Type} [Field K] {N : ℕ} (g : MvPolynomial (Fin (N + 1)) K) :
    K →+* HomogeneousLocalization.Away (grK K N) g :=
  (HomogeneousLocalization.fromZeroRingHom (grK K N) _).comp (algebraMap K (grK K N 0))

theorem evV_cst {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N)
    (q : X ⟶ Spec (CommRingCat.of K)) (hq : i ≫ PSpace.str K N = q) {g : MvPolynomial (Fin (N + 1)) K} {m : ℕ}
    (hg : g ∈ grK K N m) (V : X.Opens) (h : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) g) (a : K) :
    evV i g V h (cst g a) = strV q V a := by
  subst hq
  simp only [evV, cst, RingHom.comp_apply]
  rw [awayToSection_zero _ hg]
  have e1 : (i ≫ PSpace.str K N).appLE ⊤ V le_top =
      (spMap (algebraMap K (grK K N 0))).appTop ≫ (Proj.toSpecZero (grK K N)).appTop ≫ i.appLE ⊤ V le_top := by
    rw [PSpace.str, ← Scheme.Hom.comp_appTop_assoc]
    exact (Scheme.Hom.appLE_comp_appLE i _ ⊤ ⊤ V (by simp) le_top).symm
  have e2 : (Proj (grK K N)).presheaf.map (homOfLE (le_top : Proj.basicOpen (grK K N) g ≤ ⊤)).op ≫
      i.appLE _ V h = i.appLE ⊤ V le_top := Scheme.Hom.map_appLE _ _ _
  have key : CommRingCat.ofHom (algebraMap K (grK K N 0)) ≫ (Scheme.ΓSpecIso _).inv ≫
      (Proj.toSpecZero (grK K N)).appTop ≫ (Proj (grK K N)).presheaf.map (homOfLE le_top).op ≫ i.appLE _ V h =
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (i ≫ PSpace.str K N).appLE ⊤ V le_top := by
    rw [e2, e1, ← Category.assoc, ← Category.assoc (Scheme.ΓSpecIso _).inv, Scheme.ΓSpecIso_inv_naturality]
  exact congrArg (fun φ => φ.hom a) key

def tau {K : Type} [Field K] {N e d : ℕ} (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K)
    (hy : ∀ k, (y k).IsHomogeneous e) (k : Fin d) : HomogeneousLocalization.Away (grK K N) (y 0) :=
  HomogeneousLocalization.Away.mk _ ((mem_homogeneousSubmodule e (y 0)).2 (hy 0)) 1 (y k.succ)
    (by simpa using (mem_homogeneousSubmodule e (y k.succ)).2 (hy k.succ))

def tauL {K : Type} [Field K] {N e d : ℕ} (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K)
    (hy : ∀ k, (y k).IsHomogeneous e) (k : Fin d) : Localization (Submonoid.powers (y 0)) :=
  (tau y hy k).val

theorem val_cst {K : Type} [Field K] {N : ℕ} (g : MvPolynomial (Fin (N + 1)) K) (a : K) :
    (cst g a).val = algebraMap K (Localization (Submonoid.powers g)) a := by
  rw [IsScalarTower.algebraMap_apply K (MvPolynomial (Fin (N + 1)) K) (Localization (Submonoid.powers g)),
    ← Localization.mk_one_eq_algebraMap]
  exact HomogeneousLocalization.val_mk _

theorem val_mul {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {f a : A} {m : ℕ} (hf : f ∈ 𝒜 m) (ha : a ∈ 𝒜 (1 • m)) :
    algebraMap A (Localization (Submonoid.powers f)) a =
      algebraMap A (Localization (Submonoid.powers f)) f * (HomogeneousLocalization.Away.mk 𝒜 hf 1 a ha).val := by
  have h : (HomogeneousLocalization.Away.mk 𝒜 hf 1 a ha).val * algebraMap A (Localization (Submonoid.powers f)) (f ^ 1) =
      algebraMap A (Localization (Submonoid.powers f)) a := by
    rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
    exact IsLocalization.mk'_spec _ _ _
  rw [pow_one] at h
  rw [← h, mul_comm]

theorem val_eval {K : Type} [Field K] {N e d : ℕ} (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K)
    (hy : ∀ k, (y k).IsHomogeneous e) (Q : MvPolynomial (Fin d) K) :
    (eval₂Hom (cst (y 0)) (tau y hy) Q).val =
      aeval (tauL y hy) Q := by
  have h : (algebraMap (HomogeneousLocalization.Away (grK K N) (y 0)) (Localization (Submonoid.powers (y 0)))).comp
      (eval₂Hom (cst (y 0)) (tau y hy)) =
      (aeval (tauL y hy)).toRingHom := by
    refine ringHom_ext (fun a => ?_) (fun k => ?_)
    · simp only [RingHom.comp_apply, eval₂Hom_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C]
      exact val_cst (y 0) a
    · simp only [RingHom.comp_apply, eval₂Hom_X', AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
      rfl
  exact RingHom.congr_fun h Q

theorem away_key {K : Type} [Field K] {N e d : ℕ} (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K)
    (hy : ∀ k, (y k).IsHomogeneous e) (P : MvPolynomial (Fin d) K) {D : ℕ} (hD : P.totalDegree ≤ D)
    (hf : aeval y (homogP D P) ∈ grK K N (D • e)) :
    HomogeneousLocalization.Away.mk (grK K N) ((mem_homogeneousSubmodule e (y 0)).2 (hy 0)) D
      (aeval y (homogP D P)) hf = eval₂Hom (cst (y 0)) (tau y hy) P := by
  apply HomogeneousLocalization.val_injective
  have hc : (algebraMap (MvPolynomial (Fin (N + 1)) K) (Localization (Submonoid.powers (y 0))) ∘ y : Fin (d + 1) → _) =
      (Fin.cons (algebraMap (MvPolynomial (Fin (N + 1)) K) (Localization (Submonoid.powers (y 0))) (y 0)) (fun k => algebraMap (MvPolynomial (Fin (N + 1)) K) (Localization (Submonoid.powers (y 0))) (y 0) * tauL y hy k) : Fin (d + 1) → _) :=
    funext (Fin.cases rfl fun k => val_mul (grK K N) _ _)
  have h1 : algebraMap (MvPolynomial (Fin (N + 1)) K) (Localization (Submonoid.powers (y 0))) (aeval y (homogP D P)) =
      algebraMap (MvPolynomial (Fin (N + 1)) K) (Localization (Submonoid.powers (y 0))) (y 0) ^ D * aeval (tauL y hy) P := by
    rw [← aeval_homogP hD, ← hc, aeval_algebraMap_apply]
  rw [HomogeneousLocalization.Away.val_mk, val_eval, Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq_mul, h1,
    map_pow, mul_comm]

theorem algebraicIndependent_tV : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N d e : ℕ} (i : X ⟶ PSpace K N) (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) {V : X.Opens} (hV : V ≤ ⨅ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)), IsIntegral X → 0 < e → ∀ (q : X ⟶ Spec (CommRingCat.of K)), i ≫ PSpace.str K N = q → (AlgebraicIndependent K fun k => Ideal.Quotient.mk (homIdeal i) (y k)) → (V : Set X).Nonempty → letI := (strV q V).toAlgebra; AlgebraicIndependent K (tV i y hy V hV) := by
  intro K _ X N d e i y hy V hV hX he q hq hind hne
  letI := (strV q V).toAlgebra
  rw [algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero]
  intro P hP
  have h0 : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (y 0) :=
    hV.trans (iInf_le (fun k => i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)) 0)
  have hy0 : y 0 ∈ grK K N e := (mem_homogeneousSubmodule e (y 0)).2 (hy 0)
  have hFh : (homogP P.totalDegree P).IsHomogeneous P.totalDegree := homogenize_isHomogeneous₂ le_rfl
  have hf : aeval y (homogP P.totalDegree P) ∈ grK K N (P.totalDegree • e) := by
    rw [mem_homogeneousSubmodule, smul_eq_mul, mul_comm]
    exact hFh.aeval y hy
  have hev : evV i (y 0) V h0 (HomogeneousLocalization.Away.mk (grK K N) hy0 P.totalDegree
      (aeval y (homogP P.totalDegree P)) hf) = 0 := by
    rw [away_key y hy P le_rfl hf]
    have h : (evV i (y 0) V h0).comp (eval₂Hom (cst (y 0)) (tau y hy)) =
        (aeval (tV i y hy V hV) : MvPolynomial (Fin d) K →ₐ[K] Γ(X, V)).toRingHom := by
      refine ringHom_ext (fun a => ?_) (fun k => ?_)
      · simp only [RingHom.comp_apply, eval₂Hom_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C]
        exact evV_cst i q hq hy0 V h0 a
      · simp only [RingHom.comp_apply, eval₂Hom_X', AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
        rfl
    exact (RingHom.congr_fun h P).trans hP
  have hmem : aeval y (homogP P.totalDegree P) ∈ homIdeal i :=
    GlobalTheory.CompanionTheory.GeoVan.mem_homIdeal_of_vanish i hX he hy0 hf V hne h0 hev
  have hz : aeval (fun k => Ideal.Quotient.mk (homIdeal i) (y k)) (homogP P.totalDegree P) = 0 := by
    have h := aeval_algebraMap_apply (MvPolynomial (Fin (N + 1)) K ⧸ homIdeal i) y (homogP P.totalDegree P)
    exact h.trans (Ideal.Quotient.eq_zero_iff_mem.2 hmem)
  have hF : homogP P.totalDegree P = 0 :=
    (injective_iff_map_eq_zero _).1 ((algebraicIndependent_iff_injective_aeval).1 hind) _ hz
  have h := aeval_homogP (le_refl P.totalDegree) (1 : MvPolynomial (Fin d) K) MvPolynomial.X
  rw [hF] at h
  simpa using h.symm

end GlobalTheory.CompanionTheory.GeoAlgInd
