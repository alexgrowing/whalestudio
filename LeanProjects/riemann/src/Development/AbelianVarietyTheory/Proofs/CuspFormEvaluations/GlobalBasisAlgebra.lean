import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Formalism.LocalToGlobal.ProjectiveLattices.IsChartIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrTanAlg

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameTangent

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

section Alg

theorem global_basis_algebra {E : Type} [Field E] [NumberField E] {K S M : Type} [Field K] [CharZero K]
    [CommRing S] [Algebra K S] [AddCommGroup M] [Module S M] {J : Type} [Fintype J] [DecidableEq J]
    (χ : J → (E →+* K)) (hχ : Function.Injective χ)
    (hcard : Fintype.card J = Module.finrank ℚ E) (ρ : 𝓞 E →+* Module.End S M) {mult : J → ℕ}
    (U : (Σ σ, Fin (mult σ)) → M)
    (hU : ∀ σ i (a : 𝓞 E), ρ a (U ⟨σ, i⟩) = algebraMap K S (χ σ (a : E)) • U ⟨σ, i⟩)
    (hb : ∀ σ (W : M), (∀ a : 𝓞 E, ρ a W = algebraMap K S (χ σ (a : E)) • W) →
      ∃! c : Fin (mult σ) → S, ∑ i, c i • U ⟨σ, i⟩ = W)
    (W : M) : ∃! a : (Σ σ, Fin (mult σ)) → S, ∑ ℓ, a ℓ • U ℓ = W := by
  classical
  have hcardI : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) = Fintype.card J := by
    rw [hcard, ← RingOfIntegers.rank, Module.finrank_eq_card_chooseBasisIndex]
  let b : Module.Basis J ℤ (𝓞 E) := (RingOfIntegers.basis E).reindex (Fintype.equivOfCardEq hcardI)
  let κ : K →+* S := algebraMap K S
  let χ' : J → (𝓞 E →+* K) := fun σ => (χ σ).comp (algebraMap (𝓞 E) E)
  have hχ' : ∀ σ (y : 𝓞 E), χ' σ y = χ σ (y : E) := fun σ y => rfl
  let A : Matrix J J K := fun σ j => χ' σ (b j)

  have hA : IsUnit A.det := by
    rw [isUnit_iff_ne_zero]
    intro hdet
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
    refine hc0 ?_
    have hψ : Function.Injective fun σ => ((χ' σ : 𝓞 E →+* K) : 𝓞 E →* K) := by
      intro σ τ h
      apply hχ
      apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
      ext y
      exact DFunLike.congr_fun h y
    have hli := (linearIndependent_monoidHom (𝓞 E) K).comp _ hψ
    rw [Fintype.linearIndependent_iff] at hli
    have hcj : ∀ j, ∑ σ, c σ * χ' σ (b j) = 0 := fun j => by
      simpa [Matrix.vecMul, dotProduct, A] using congrFun hc j
    have hsum : ∀ y : 𝓞 E, ∑ σ, c σ * χ' σ y = 0 := by
      intro y
      calc ∑ σ, c σ * χ' σ y = ∑ σ, c σ * χ' σ (∑ j, b.repr y j • b j) := by rw [b.sum_repr y]
        _ = ∑ j, (b.repr y j : K) * ∑ σ, c σ * χ' σ (b j) := by
            simp only [map_sum, zsmul_eq_mul, map_mul, map_intCast, Finset.mul_sum]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun σ _ => by ring
        _ = 0 := by simp [hcj]
    funext σ
    refine hli c ?_ σ
    funext y
    simpa [Finset.sum_apply] using hsum y
  let B : Matrix J J K := A⁻¹
  have hAB : ∀ σ τ, ∑ k, A σ k * B k τ = if σ = τ then 1 else 0 := fun σ τ => by
    have := congrFun (congrFun (Matrix.mul_nonsing_inv A hA) σ) τ
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  have hBA : ∀ j k, ∑ τ, B j τ * A τ k = if j = k then 1 else 0 := fun j k => by
    have := congrFun (congrFun (Matrix.nonsing_inv_mul A hA) j) k
    simpa [Matrix.mul_apply, Matrix.one_apply] using this

  let P : J → M → M := fun σ V => ∑ j, κ (B j σ) • ρ (b j) V
  have hPadd : ∀ τ (F : J → M), P τ (∑ σ, F σ) = ∑ σ, P τ (F σ) := by
    intro τ F
    simp only [P, map_sum, Finset.smul_sum]
    exact Finset.sum_comm
  have hρ : ∀ (y : 𝓞 E) (V : M), ρ y V = ∑ τ, κ (χ' τ y) • P τ V := by
    intro y V
    have e1 : ∀ τ, χ' τ y = ∑ k, (b.repr y k : K) * A τ k := fun τ => by
      conv_lhs => rw [← b.sum_repr y]
      simp only [map_sum, zsmul_eq_mul, map_mul, map_intCast, A]
    have hy : ∀ j, ∑ τ, χ' τ y * B j τ = (b.repr y j : K) := by
      intro j
      calc ∑ τ, χ' τ y * B j τ = ∑ τ, ∑ k, (b.repr y k : K) * (B j τ * A τ k) := by
            simp only [e1, Finset.sum_mul]
            exact Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun k _ => by ring
        _ = ∑ k, (b.repr y k : K) * ∑ τ, B j τ * A τ k := by
            rw [Finset.sum_comm]
            simp only [Finset.mul_sum]
        _ = (b.repr y j : K) := by
            simp only [hBA, mul_ite, _root_.mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    calc ρ y V = ρ (∑ j, b.repr y j • b j) V := by rw [b.sum_repr y]
      _ = ∑ j, κ (b.repr y j : K) • ρ (b j) V := by
          simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply,
            map_intCast, Int.cast_smul_eq_zsmul]
      _ = ∑ j, κ (∑ τ, χ' τ y * B j τ) • ρ (b j) V := by simp only [hy]
      _ = ∑ τ, κ (χ' τ y) • P τ V := by
          simp only [P, Finset.smul_sum, smul_smul, map_sum, Finset.sum_smul, map_mul]
          exact Finset.sum_comm
  have hPeig : ∀ σ V (a : 𝓞 E), ρ a (P σ V) = algebraMap K S (χ σ (a : E)) • P σ V := by
    intro σ V a
    calc ρ a (P σ V) = ∑ k, κ (B k σ) • ρ (a * b k) V := by
          simp only [P, map_sum, map_smul, map_mul, Module.End.mul_apply]
      _ = ∑ k, ∑ ν, κ (B k σ * (χ' ν a * A ν k)) • P ν V := by
          simp only [hρ, Finset.smul_sum, smul_smul, ← map_mul, A]
      _ = ∑ ν, κ (χ' ν a * ∑ k, A ν k * B k σ) • P ν V := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun ν _ => ?_
          rw [Finset.mul_sum, map_sum, Finset.sum_smul]
          exact Finset.sum_congr rfl fun k _ => by congr 2; ring
      _ = algebraMap K S (χ σ (a : E)) • P σ V := by
          rw [Finset.sum_eq_single σ]
          · rw [hAB, if_pos rfl, _root_.mul_one]
            rfl
          · intro ν _ hν
            rw [hAB, if_neg hν, mul_zero, map_zero, zero_smul]
          · intro h
            exact absurd (Finset.mem_univ σ) h
  have hPZ : ∀ σ τ (Z : M), (∀ a : 𝓞 E, ρ a Z = algebraMap K S (χ σ (a : E)) • Z) →
      P τ Z = if σ = τ then Z else 0 := by
    intro σ τ Z hZ
    calc P τ Z = ∑ j, κ (A σ j * B j τ) • Z := by
          simp only [P, hZ, smul_smul]
          exact Finset.sum_congr rfl fun j _ => by rw [mul_comm, map_mul]; rfl
      _ = κ (∑ j, A σ j * B j τ) • Z := by rw [map_sum, Finset.sum_smul]
      _ = if σ = τ then Z else 0 := by
          rw [hAB]; split_ifs <;> simp
  have hPsum : ∑ τ, P τ W = W := by
    have := hρ 1 W
    simp only [map_one, Module.End.one_apply, one_smul] at this
    exact this.symm
  have hYeig : ∀ (a : (Σ σ, Fin (mult σ)) → S) σ (c : 𝓞 E),
      ρ c (∑ i, a ⟨σ, i⟩ • U ⟨σ, i⟩) = algebraMap K S (χ σ (c : E)) • ∑ i, a ⟨σ, i⟩ • U ⟨σ, i⟩ := by
    intro a σ c
    rw [map_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hU, smul_comm]
  have hproj : ∀ (a : (Σ σ, Fin (mult σ)) → S), ∑ ℓ, a ℓ • U ℓ = W →
      ∀ τ, ∑ i, a ⟨τ, i⟩ • U ⟨τ, i⟩ = P τ W := by
    intro a ha τ
    rw [← ha, Fintype.sum_sigma, hPadd, Finset.sum_eq_single τ]
    · rw [hPZ τ τ _ (hYeig a τ), if_pos rfl]
    · intro σ _ hστ
      rw [hPZ σ τ _ (hYeig a σ), if_neg hστ]
    · intro h
      exact absurd (Finset.mem_univ τ) h
  have hex : ∀ σ, ∃! c : Fin (mult σ) → S, ∑ i, c i • U ⟨σ, i⟩ = P σ W := fun σ => hb σ (P σ W) (hPeig σ W)
  choose c hc using fun σ => (hex σ).exists
  refine ⟨fun ℓ => c ℓ.1 ℓ.2, ?_, ?_⟩
  · show ∑ ℓ, c ℓ.1 ℓ.2 • U ℓ = W
    rw [Fintype.sum_sigma]
    simp only [hc]
    exact hPsum
  · intro a' ha'
    funext ℓ
    obtain ⟨σ, i⟩ := ℓ
    have := (hex σ).unique (hproj a' ha' σ) (hc σ)
    exact congrFun this i

end Alg

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  exact (Spec.map_comp _ _).symm

theorem spec_ext_two {R A : Type} [CommRing R] [CommRing A] (p1 p2 : R →+* A)
    (hs : Function.Surjective p1) (hn : ∀ x, p1 x = 0 → x * x = 0)
    (hk : ∀ x, p1 x = 0 → p2 x = 0 → x = 0) {X : Scheme.{0}} (f g : Sp R ⟶ X)
    (h1 : spMap p1 ≫ f = spMap p1 ≫ g) (h2 : spMap p2 ≫ f = spMap p2 ≫ g) : f = g := by
  classical
  have hinj : Function.Injective (p1.prod p2) := by
    intro a b hab
    have e1 : p1 a = p1 b := congrArg Prod.fst hab
    have e2 : p2 a = p2 b := congrArg Prod.snd hab
    exact sub_eq_zero.mp (hk (a - b) (by rw [map_sub, e1, sub_self]) (by rw [map_sub, e2, sub_self]))
  have : IsSchemeTheoreticallyDominant (spMap (p1.prod p2)) := by
    refine ⟨le_bot_iff.mp (Scheme.IdealSheafData.le_of_isAffine ?_)⟩
    refine ((spMap (p1.prod p2)).ideal_ker_le _).trans fun z hz => ?_
    have hz' : (Spec.map (CommRingCat.ofHom (p1.prod p2))).appTop.hom z = 0 := RingHom.mem_ker.mp hz
    have e := congrArg (fun h => h.hom z) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (p1.prod p2)))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, hz', map_zero] at e
    have h0 : (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom z = 0 :=
      hinj (e.symm.trans (map_zero (p1.prod p2)).symm)
    have hz0 : z = 0 := by
      have := congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom h0
      simpa using this
    rw [hz0]
    exact zero_mem _
  have hπ : spMap (p1.prod p2) ≫ f = spMap (p1.prod p2) ≫ g := by
    have e1 : Spec.map (CommRingCat.ofHom (RingHom.fst A A)) ≫ spMap (p1.prod p2) = spMap p1 :=
      (spMap_comp' (p1.prod p2) (RingHom.fst A A)).trans (congrArg spMap (RingHom.ext fun _ => rfl))
    have e2 : Spec.map (CommRingCat.ofHom (RingHom.snd A A)) ≫ spMap (p1.prod p2) = spMap p2 :=
      (spMap_comp' (p1.prod p2) (RingHom.snd A A)).trans (congrArg spMap (RingHom.ext fun _ => rfl))
    rw [← cancel_epi (coprodSpec A A)]
    apply coprod.hom_ext
    · rw [coprodSpec_inl_assoc, coprodSpec_inl_assoc, reassoc_of% e1, reassoc_of% e1, h1]
    · rw [coprodSpec_inr_assoc, coprodSpec_inr_assoc, reassoc_of% e2, reassoc_of% e2, h2]
  have hsurj : ∀ x : PrimeSpectrum R, ∃ y : PrimeSpectrum A, PrimeSpectrum.comap p1 y = x := by
    intro x
    have hker : RingHom.ker p1 ≤ x.asIdeal := fun m hm =>
      x.isPrime.mem_of_pow_mem 2 (by rw [pow_two, hn m (RingHom.mem_ker.mp hm)]; exact zero_mem _)
    have := x.isPrime
    refine ⟨⟨Ideal.map p1 x.asIdeal, Ideal.map_isPrime_of_surjective hs hker⟩, PrimeSpectrum.ext ?_⟩
    change Ideal.comap p1 (Ideal.map p1 x.asIdeal) = x.asIdeal
    rw [Ideal.comap_map_of_surjective p1 hs, ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hker]
  have hbase : f.base = g.base := by
    ext x
    obtain ⟨y, rfl⟩ := hsurj x
    exact congrArg (fun h : Sp A ⟶ X => h.base y) h1
  refine Scheme.Hom.ext hbase fun U => ?_
  have : Mono ((spMap (p1.prod p2)).app (g ⁻¹ᵁ U)) :=
    ConcreteCategory.mono_of_injective _ ((spMap (p1.prod p2)).app_injective _)
  rw [← cancel_mono ((spMap (p1.prod p2)).app (g ⁻¹ᵁ U)), Category.assoc, Scheme.Hom.naturality,
    ← Category.assoc, ← Scheme.Hom.comp_app, ← Scheme.Hom.comp_app, Scheme.Hom.congr_app hπ U]
  have hid : ∀ {V : (TopologicalSpace.Opens ↥(Sp (A × A)))ᵒᵖ} (k : V ⟶ V), (Sp (A × A)).presheaf.map k = 𝟙 _ :=
    fun k => by rw [show k = 𝟙 _ from Quiver.Hom.unop_inj (Subsingleton.elim _ _), CategoryTheory.Functor.map_id]
  simp [← Functor.map_comp]
  erw [hid, Category.comp_id]

section Scal

variable {X0 : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X0)

theorem homAt_comp {A B C : Type} [CommRing A] [Algebra S A] [CommRing B] [Algebra S B] [CommRing C] [Algebra S C]
    (f : A →ₐ[S] B) (g : B →ₐ[S] C) : homAt x0 g ≫ homAt x0 f = homAt x0 (g.comp f) := by
  ext1
  simp only [Formalism.L2.Pj.homAt, Over.comp_left, Over.homMk_left]
  rw [spMap_comp']
  rfl

theorem homAt_id {A : Type} [CommRing A] [Algebra S A] : homAt x0 (AlgHom.id S A) = 𝟙 _ := by
  ext1
  simp only [Formalism.L2.Pj.homAt, Over.homMk_left, Over.id_left]
  exact Spec.map_id _

abbrev tm {M N : Type} [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
    [Module Sᵐᵒᵖ M] [IsCentralScalar S M] [Module Sᵐᵒᵖ N] [IsCentralScalar S N] (L : M →ₗ[S] N) :
    TrivSqZeroExt S M →ₐ[S] TrivSqZeroExt S N := TrivSqZeroExt.map L

variable {G : Over X0} [GrpObj G]

def smT (a : S) (v : overAt x0 (DualNumber S) ⟶ G) : overAt x0 (DualNumber S) ⟶ G :=
  homAt x0 (tm (a • (LinearMap.id : S →ₗ[S] S))) ≫ v

theorem smT_left (a : S) (v : overAt x0 (DualNumber S) ⟶ G) : (smT x0 a v).left = spMap (epsMul a) ≫ v.left := rfl

theorem smT_mul (a : S) (u w : overAt x0 (DualNumber S) ⟶ G) : smT x0 a (u * w) = smT x0 a u * smT x0 a w := by
  simp only [smT, MonObj.comp_mul]

theorem smT_one' (a : S) : smT x0 a (1 : overAt x0 (DualNumber S) ⟶ G) = 1 := by
  simp only [smT, MonObj.comp_one]

theorem smT_smT (a b : S) (v : overAt x0 (DualNumber S) ⟶ G) : smT x0 a (smT x0 b v) = smT x0 (a * b) v := by
  unfold smT
  rw [← Category.assoc, homAt_comp]
  congr 2
  refine AlgHom.ext fun z => TrivSqZeroExt.ext ?_ ?_ <;> (simp [tm] <;> ring)

theorem smT_unit (v : overAt x0 (DualNumber S) ⟶ G) : smT x0 1 v = v := by
  unfold smT
  have e : tm ((1 : S) • (LinearMap.id : S →ₗ[S] S)) = AlgHom.id S (DualNumber S) :=
    AlgHom.ext fun z => TrivSqZeroExt.ext (by simp [tm]) (by simp [tm])
  rw [e, homAt_id, Category.id_comp]

theorem smT_add (v : overAt x0 (DualNumber S) ⟶ G) (h0 : smT x0 0 v = 1) (a b : S) :
    smT x0 (a + b) v = smT x0 a v * smT x0 b v := by
  let m : DualNumber S →ₐ[S] TrivSqZeroExt S (S × S) := TrivSqZeroExt.map (LinearMap.prod LinearMap.id LinearMap.id)
  let i1 : DualNumber S →ₐ[S] TrivSqZeroExt S (S × S) := TrivSqZeroExt.map (LinearMap.inl S S S)
  let i2 : DualNumber S →ₐ[S] TrivSqZeroExt S (S × S) := TrivSqZeroExt.map (LinearMap.inr S S S)
  let q1 : TrivSqZeroExt S (S × S) →ₐ[S] DualNumber S := TrivSqZeroExt.map (LinearMap.fst S S S)
  let q2 : TrivSqZeroExt S (S × S) →ₐ[S] DualNumber S := TrivSqZeroExt.map (LinearMap.snd S S S)
  let qa : TrivSqZeroExt S (S × S) →ₐ[S] DualNumber S :=
    TrivSqZeroExt.map (LinearMap.coprod (a • LinearMap.id) (b • LinearMap.id))
  have h0' : homAt x0 (tm ((0 : S) • (LinearMap.id : S →ₗ[S] S))) ≫ v = 1 := h0
  have key : homAt x0 m ≫ v = homAt x0 i1 ≫ v * homAt x0 i2 ≫ v := by
    have e1 : homAt x0 q1 ≫ (homAt x0 m ≫ v) = homAt x0 q1 ≫ (homAt x0 i1 ≫ v * homAt x0 i2 ≫ v) := by
      have c1 : q1.comp m = AlgHom.id S _ :=
        AlgHom.ext fun z => TrivSqZeroExt.ext (by simp [q1, m]) (by simp [q1, m])
      have c2 : q1.comp i1 = AlgHom.id S _ :=
        AlgHom.ext fun z => TrivSqZeroExt.ext (by simp [q1, i1]) (by simp [q1, i1])
      have c3 : q1.comp i2 = tm ((0 : S) • (LinearMap.id : S →ₗ[S] S)) :=
        AlgHom.ext fun z => TrivSqZeroExt.ext (by simp [q1, i2, tm]) (by simp [q1, i2, tm])
      simp only [MonObj.comp_mul, ← Category.assoc, homAt_comp, c1, c2, c3, homAt_id, Category.id_comp, h0',
        _root_.mul_one]
    have e2 : homAt x0 q2 ≫ (homAt x0 m ≫ v) = homAt x0 q2 ≫ (homAt x0 i1 ≫ v * homAt x0 i2 ≫ v) := by
      have c1 : q2.comp m = AlgHom.id S _ :=
        AlgHom.ext fun z => TrivSqZeroExt.ext (by simp [q2, m]) (by simp [q2, m])
      have c2 : q2.comp i1 = tm ((0 : S) • (LinearMap.id : S →ₗ[S] S)) :=
        AlgHom.ext fun z => TrivSqZeroExt.ext (by simp [q2, i1, tm]) (by simp [q2, i1, tm])
      have c3 : q2.comp i2 = AlgHom.id S _ :=
        AlgHom.ext fun z => TrivSqZeroExt.ext (by simp [q2, i2]) (by simp [q2, i2])
      simp only [MonObj.comp_mul, ← Category.assoc, homAt_comp, c1, c2, c3, homAt_id, Category.id_comp, h0',
        _root_.one_mul]
    apply Over.OverMorphism.ext
    refine spec_ext_two (q1 : TrivSqZeroExt S (S × S) →+* DualNumber S) (q2 : TrivSqZeroExt S (S × S) →+* DualNumber S)
      ?_ ?_ ?_ _ _ (congrArg Over.Hom.left e1) (congrArg Over.Hom.left e2)
    · intro z
      exact ⟨TrivSqZeroExt.inl z.fst + TrivSqZeroExt.inr (z.snd, 0),
        TrivSqZeroExt.ext (by simp [q1]) (by simp [q1])⟩
    · intro z hz
      have h1 : z.fst = 0 := by simpa [q1] using congrArg TrivSqZeroExt.fst hz
      exact TrivSqZeroExt.ext (by simp [h1]) (by simp [h1])
    · intro z hz1 hz2
      have h1 : z.fst = 0 := by simpa [q1] using congrArg TrivSqZeroExt.fst hz1
      have h2 : z.snd.1 = 0 := by simpa [q1] using congrArg TrivSqZeroExt.snd hz1
      have h3 : z.snd.2 = 0 := by simpa [q2] using congrArg TrivSqZeroExt.snd hz2
      exact TrivSqZeroExt.ext h1 (Prod.ext h2 h3)
  have ca : qa.comp m = tm ((a + b) • (LinearMap.id : S →ₗ[S] S)) :=
    AlgHom.ext fun z => TrivSqZeroExt.ext (by simp [qa, m, tm]) (by simp [qa, m, tm, add_smul])
  have cb1 : qa.comp i1 = tm (a • (LinearMap.id : S →ₗ[S] S)) :=
    AlgHom.ext fun z => TrivSqZeroExt.ext (by simp [qa, i1, tm]) (by simp [qa, i1, tm])
  have cb2 : qa.comp i2 = tm (b • (LinearMap.id : S →ₗ[S] S)) :=
    AlgHom.ext fun z => TrivSqZeroExt.ext (by simp [qa, i2, tm]) (by simp [qa, i2, tm])
  have e := congrArg (homAt x0 qa ≫ ·) key
  simp only [MonObj.comp_mul, ← Category.assoc, homAt_comp, ca, cb1, cb2] at e
  exact e

section Comb

variable [IsCommMonObj G]

def combT {m : ℕ} (v : Fin m → (overAt x0 (DualNumber S) ⟶ G)) (a : Fin m → S) : overAt x0 (DualNumber S) ⟶ G :=
  ∏ j, smT x0 (a j) (v j)

def smHom (a : S) : (overAt x0 (DualNumber S) ⟶ G) →* (overAt x0 (DualNumber S) ⟶ G) where
  toFun := smT x0 a
  map_one' := smT_one' x0 a
  map_mul' := smT_mul x0 a

theorem tan_pull {P : Over X0} (ψ : P ⟶ overAt x0 (DualNumber S))
    (hψ : ψ ≫ homAt x0 (tm ((0 : S) • (LinearMap.id : S →ₗ[S] S))) = ψ) (W : overAt x0 (DualNumber S) ⟶ G)
    (h : smT x0 0 W = 1) : ψ ≫ W = 1 := by
  have h' : homAt x0 (tm ((0 : S) • (LinearMap.id : S →ₗ[S] S))) ≫ W = 1 := h
  calc ψ ≫ W = (ψ ≫ homAt x0 (tm ((0 : S) • (LinearMap.id : S →ₗ[S] S)))) ≫ W := by rw [hψ]
    _ = 1 := by rw [Category.assoc, h', MonObj.comp_one]

theorem smT_post (a : S) (v : overAt x0 (DualNumber S) ⟶ G) (φ : G ⟶ G) :
    smT x0 a (v ≫ φ) = smT x0 a v ≫ φ := by
  simp only [smT, Category.assoc]

end Comb

end Scal

section TanSAB

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0)

theorem isCombAtG_iff {m : ℕ} (v : Fin m → (tEpsG x0 ⟶ t.G)) (cf : Fin m → S) (w : Sp (DualNumber S) ⟶ t.G.left) :
    IsCombAtG t x0 (fun j => (v j).left) cf w ↔ (combT x0 v cf).left = w := by
  constructor
  · rintro ⟨u, hu, hw⟩
    have e : u = fun j => smT x0 (cf j) (v j) :=
      funext fun j => Over.OverMorphism.ext ((hu j).trans (smT_left x0 (cf j) (v j)).symm)
    subst e
    rw [← hw, List.prod_ofFn]
    rfl
  · intro h
    refine ⟨fun j => smT x0 (cf j) (v j), fun j => smT_left x0 (cf j) (v j), ?_⟩
    rw [List.prod_ofFn]
    exact h

private theorem eps_zero_lemma :
    epsMul (0 : S) = (algebraMap S (DualNumber S)).comp (TrivSqZeroExt.fstHom S S S).toRingHom :=
  RingHom.ext fun z => TrivSqZeroExt.ext (by simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl])
    (by simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl])

private theorem fst_eps_lemma_2 :
    (TrivSqZeroExt.fstHom S S S).toRingHom.comp (epsMul (0 : S)) = (TrivSqZeroExt.fstHom S S S).toRingHom :=
  RingHom.ext fun z => by simp [epsMul]

private theorem one_left_lemma_3 {G : Over X0} [GrpObj G] :
    (1 : tEpsG x0 ⟶ G).left = spMap (algebraMap S (DualNumber S)) ≫ (1 : Over.mk x0 ⟶ G).left := by
  have h : (Over.homMk (spMap (algebraMap S (DualNumber S))) rfl : tEpsG x0 ⟶ Over.mk x0) ≫
      (1 : Over.mk x0 ⟶ G) = 1 := MonObj.comp_one _
  exact (congrArg Over.Hom.left h).symm

variable {t x0}

def ovT {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t x0 v) : tEpsG x0 ⟶ t.G := Over.homMk v hv.1

theorem smT_zero_ovT {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t x0 v) : smT x0 0 (ovT hv) = 1 := by
  ext1
  have e : spMap (epsMul (0 : S)) ≫ v = spMap (algebraMap S (DualNumber S)) ≫ (1 : Over.mk x0 ⟶ t.G).left := by
    rw [eps_zero_lemma, ← spMap_comp', Category.assoc, hv.2]
  exact (smT_left x0 0 (ovT hv)).trans (e.trans (one_left_lemma_3 x0 (G := t.G)).symm)

theorem isTanAtG_of (W : tEpsG x0 ⟶ t.G) (h : smT x0 0 W = 1) : IsTanAtG t x0 W.left := by
  refine ⟨Over.w W, ?_⟩
  have h' := congrArg Over.Hom.left h
  rw [smT_left] at h'
  have hs : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _ := by
    rw [spMap_comp', show (TrivSqZeroExt.fstHom S S S).toRingHom.comp (algebraMap S (DualNumber S)) = RingHom.id S from
      RingHom.ext fun s => by simp]
    exact Spec.map_id _
  calc spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ W.left
        = spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (epsMul (0 : S)) ≫ W.left := by
          rw [← Category.assoc, spMap_comp', fst_eps_lemma_2]
    _ = spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ (1 : tEpsG x0 ⟶ t.G).left := congrArg _ h'
    _ = (1 : Over.mk x0 ⟶ t.G).left := by
          rw [one_left_lemma_3 x0, ← Category.assoc, hs, Category.id_comp]

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem isEigAt_iff [Algebra c.F S] {x : Sp S ⟶ Xo.X} (τ : E →+* ℂ)
    (W : tEpsG x ⟶ Xo.univ.t.G) :
    IsEigAt c τ W.left ↔ ∀ a : 𝓞 E, W ≫ Xo.univ.t.act.act a = smT x (algebraMap c.F S (embK c τ a)) W := by
  unfold IsEigAt
  refine forall_congr' fun a => ⟨fun h => ?_, fun h => ?_⟩
  · ext1
    rw [Over.comp_left, smT_left]
    exact h
  · have h' := congrArg Over.Hom.left h
    rw [Over.comp_left, smT_left] at h'
    exact h'

end TanSAB

section Tan

variable {X0 : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (G : Over X0) [GrpObj G] [IsCommMonObj G]

def tanSub : Subgroup (overAt x0 (DualNumber S) ⟶ G) where
  carrier := {W | smT x0 0 W = 1}
  mul_mem' {u w} hu hw := by
    have hu : smT x0 0 u = 1 := hu
    have hw : smT x0 0 w = 1 := hw
    show smT x0 0 (u * w) = 1
    rw [smT_mul, hu, hw, _root_.mul_one]
  one_mem' := smT_one' x0 0
  inv_mem' {W} hW := by
    have hW : smT x0 0 W = 1 := hW
    show smT x0 0 W⁻¹ = 1
    have h := map_inv (smHom x0 (G := G) 0) W
    change smT x0 0 W⁻¹ = (smT x0 0 W)⁻¹ at h
    rw [h, hW, inv_one]

abbrev TanM := Additive (tanSub x0 G)

variable {x0 G}

def tv (m : TanM x0 G) : overAt x0 (DualNumber S) ⟶ G := (Additive.toMul m : tanSub x0 G)

theorem tv_zero' (m : TanM x0 G) : smT x0 0 (tv m) = 1 := by
  exact (Additive.toMul m).prop

def mkT (W : overAt x0 (DualNumber S) ⟶ G) (h : smT x0 0 W = 1) : TanM x0 G := Additive.ofMul ⟨W, h⟩

theorem tv_mkT (W : overAt x0 (DualNumber S) ⟶ G) (h : smT x0 0 W = 1) : tv (mkT W h) = W := rfl

theorem tv_injective : Function.Injective (tv (x0 := x0) (G := G)) := by
  intro m m' h
  exact Additive.toMul.injective (Subtype.ext h)

theorem tv_add (m m' : TanM x0 G) : tv (m + m') = tv m * tv m' := rfl

theorem tv_zero : tv (0 : TanM x0 G) = 1 := rfl

theorem tv_sum {κ : Type} (s : Finset κ) (f : κ → TanM x0 G) : tv (∑ i ∈ s, f i) = ∏ i ∈ s, tv (f i) := by
  classical
  refine Finset.induction_on s (by rw [Finset.sum_empty, Finset.prod_empty]; exact tv_zero) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.prod_insert ha, tv_add, ih]

instance : Module S (TanM x0 G) where
  smul a m := mkT (smT x0 a (tv m)) (by rw [smT_smT, zero_mul]; exact tv_zero' m)
  one_smul m := tv_injective (smT_unit x0 (tv m))
  mul_smul a b m := tv_injective (smT_smT x0 a b (tv m)).symm
  smul_zero a := tv_injective (smT_one' x0 a)
  smul_add a m m' := tv_injective (smT_mul x0 a (tv m) (tv m'))
  add_smul a b m := tv_injective (smT_add x0 (tv m) (tv_zero' m) a b)
  zero_smul m := tv_injective (tv_zero' m)

theorem tv_smul (a : S) (m : TanM x0 G) : tv (a • m) = smT x0 a (tv m) := rfl

def postL (φ : G ⟶ G) [IsMonHom φ] : Module.End S (TanM x0 G) where
  toFun m := mkT (tv m ≫ φ) (by rw [smT_post, tv_zero' m, MonObj.one_comp])
  map_add' m m' := tv_injective (MonObj.mul_comp (tv m) (tv m') φ)
  map_smul' a m := tv_injective (smT_post x0 a (tv m) φ).symm

theorem tv_postL (φ : G ⟶ G) [IsMonHom φ] (m : TanM x0 G) : tv (postL φ m) = tv m ≫ φ := rfl

def actL {O : Type} [CommRing O] (ρ : OAct O G) : O →+* Module.End S (TanM x0 G) where
  toFun a := letI := ρ.hom a; postL (ρ.act a)
  map_one' := LinearMap.ext fun m => tv_injective (by
    rw [tv_postL, ρ.one, Category.comp_id]; rfl)
  map_mul' a b := LinearMap.ext fun m => tv_injective (by
    rw [Module.End.mul_apply, tv_postL, tv_postL, tv_postL, mul_comm a b, ρ.mul, Category.assoc])
  map_zero' := LinearMap.ext fun m => tv_injective (by
    have h0 : ρ.act 0 = 1 := by
      have h := ρ.add 0 0
      rw [add_zero] at h
      have h' : ρ.act 0 * ρ.act 0 = ρ.act 0 * 1 := by rw [_root_.mul_one]; exact h.symm
      exact mul_left_cancel h'
    rw [tv_postL, h0, MonObj.comp_one]; rfl)
  map_add' a b := LinearMap.ext fun m => tv_injective (by
    rw [LinearMap.add_apply, tv_add, tv_postL, tv_postL, tv_postL, ρ.add, MonObj.comp_mul])

theorem tv_actL {O : Type} [CommRing O] (ρ : OAct O G) (a : O) (m : TanM x0 G) :
    tv (actL ρ a m) = tv m ≫ ρ.act a := rfl

theorem tv_comb {κ : Type} [Fintype κ] (v : κ → TanM x0 G) (a : κ → S) :
    tv (∑ k, a k • v k) = ∏ k, smT x0 (a k) (tv (v k)) := by
  rw [tv_sum]
  exact Finset.prod_congr rfl fun k _ => tv_smul _ _

end Tan

theorem frame_tangent_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left), IsTanAt y.x w → ∃! a : Lt1 Dw → S, IsCombAt y.x (m := Fintype.card (Lt1 Dw)) (fun i => y.u ((Fintype.equivFin (Lt1 Dw)).symm i).1 ((Fintype.equivFin (Lt1 Dw)).symm i).2) (fun i => a ((Fintype.equivFin (Lt1 Dw)).symm i)) w := by
  intro E _ _ _ H Dw l Xo c S _ _ y w hw
  classical
  let U : Lt1 Dw → TanM y.x Xo.univ.t.G := fun ℓ => mkT (ovT (y.tan ℓ.1 ℓ.2)) (smT_zero_ovT _)
  let ρ : 𝓞 E →+* Module.End S (TanM y.x Xo.univ.t.G) := actL Xo.univ.t.act
  have hinj : Function.Injective fun τ : E →+* ℂ => embF c τ := by
    intro τ τ' h
    ext x
    exact congrArg (fun f : E →+* c.F => ((f x : c.F) : ℂ)) h
  have hcard : Fintype.card (E →+* ℂ) = Module.finrank ℚ E := NumberField.Embeddings.card E ℂ
  have hU : ∀ σ i (a : 𝓞 E), ρ a (U ⟨σ, i⟩) = algebraMap c.F S (embF c σ (a : E)) • U ⟨σ, i⟩ := by
    intro σ i a
    apply tv_injective
    rw [tv_actL, tv_smul, tv_mkT]
    exact (isEigAt_iff σ (ovT (y.tan σ i))).mp (y.eig σ i) a
  have hb : ∀ σ (V : TanM y.x Xo.univ.t.G), (∀ a : 𝓞 E, ρ a V = algebraMap c.F S (embF c σ (a : E)) • V) →
      ∃! c' : Fin (Dw.mult σ) → S, ∑ i, c' i • U ⟨σ, i⟩ = V := by
    intro σ V hV
    have htan : IsTanAt y.x (tv V).left := isTanAtG_of (tv V) (tv_zero' V)
    have heig : IsEigAt c σ (tv V).left := (isEigAt_iff σ (tv V)).mpr fun a => by
      have h := congrArg tv (hV a)
      rwa [tv_actL, tv_smul] at h
    obtain ⟨c', hc', huniq⟩ := y.basis σ _ htan heig
    refine ⟨c', ?_, fun c'' hc'' => huniq c'' ?_⟩
    · apply tv_injective
      rw [tv_comb]
      apply Over.OverMorphism.ext
      exact (isCombAtG_iff (t := Xo.univ.t) (x0 := y.x) (fun i => ovT (y.tan σ i)) c' (tv V).left).mp hc'
    · refine (isCombAtG_iff (t := Xo.univ.t) (x0 := y.x) (fun i => ovT (y.tan σ i)) c'' (tv V).left).mpr ?_
      exact congrArg Over.Hom.left ((tv_comb (fun i => U ⟨σ, i⟩) c'').symm.trans (congrArg tv hc''))
  have hiff : ∀ a : Lt1 Dw → S,
      IsCombAt y.x (m := Fintype.card (Lt1 Dw))
        (fun i => y.u ((Fintype.equivFin (Lt1 Dw)).symm i).1 ((Fintype.equivFin (Lt1 Dw)).symm i).2)
        (fun i => a ((Fintype.equivFin (Lt1 Dw)).symm i)) w ↔
      ∑ ℓ, a ℓ • U ℓ = mkT (ovT hw) (smT_zero_ovT hw) := by
    intro a
    have hprod : tv (∑ ℓ, a ℓ • U ℓ) = ∏ i : Fin (Fintype.card (Lt1 Dw)),
        smT y.x (a ((Fintype.equivFin (Lt1 Dw)).symm i))
          (ovT (y.tan ((Fintype.equivFin (Lt1 Dw)).symm i).1 ((Fintype.equivFin (Lt1 Dw)).symm i).2)) := by
      rw [tv_comb]
      exact (Equiv.prod_comp (Fintype.equivFin (Lt1 Dw)).symm (fun ℓ => smT y.x (a ℓ) (ovT (y.tan ℓ.1 ℓ.2)))).symm
    refine (isCombAtG_iff (t := Xo.univ.t) (x0 := y.x)
      (fun i => ovT (y.tan ((Fintype.equivFin (Lt1 Dw)).symm i).1 ((Fintype.equivFin (Lt1 Dw)).symm i).2))
      (fun i => a ((Fintype.equivFin (Lt1 Dw)).symm i)) w).trans ⟨fun h => ?_, fun h => ?_⟩
    · apply tv_injective
      rw [tv_mkT, hprod]
      exact Over.OverMorphism.ext h
    · have h' := congrArg (fun V => (tv V).left) h
      simp only [hprod, tv_mkT] at h'
      exact h'
  obtain ⟨a, ha, huniq⟩ := global_basis_algebra (fun τ : E →+* ℂ => embF c τ) hinj hcard ρ U hU hb
    (mkT (ovT hw) (smT_zero_ovT hw))
  exact ⟨a, (hiff a).mpr ha, fun a' ha' => huniq a' ((hiff a').mp ha')⟩

end GlobalTheory.FrameTangent
