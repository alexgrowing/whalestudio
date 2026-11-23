import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.AbLaw.CubeOpen

theorem triv_comp {X Y Z : Scheme.{0}} {M : LB X} {f : Y ⟶ X} (h : Z ⟶ Y) {k : Z ⟶ X}
    (hk : h ≫ f = k) (ht : Triv (M.pull f)) : Triv (M.pull k) := by
  subst hk
  obtain ⟨t, ht⟩ := ht
  exact ⟨_, LB.isGen_pullGen M _ _ t ht h⟩

theorem triv_pull_pull {X Y Z : Scheme.{0}} {M : LB X} (f : Y ⟶ X) (h : Z ⟶ Y)
    (ht : Triv (M.pull (h ≫ f))) : Triv ((M.pull f).pull h) := by
  obtain ⟨t, ht⟩ := ht
  have hle : ∀ j : PUnit.{1} → PUnit.{1} → M.ι,
      LB.wchart (M.pull f) (K := PUnit) (fun _ => h) j ≤
        LB.wchart M (K := PUnit) (fun _ => h ≫ f) (j PUnit.unit) :=
    fun j y hy => Set.mem_iInter.2 fun k =>
      Set.mem_iInter.1 (Set.mem_iInter.1 hy PUnit.unit) k
  refine ⟨⟨fun j => res (hle j) (LB.ts t (j PUnit.unit))⟩, (LB.isGen_iff _ _).2 fun i j => ?_⟩
  have key := congrArg (res (inf_le_inf (hle i) (hle j)))
    ((LB.isGen_iff M t).1 ht (i PUnit.unit) (j PUnit.unit))
  rw [LB.lcg_comp M (fun _ : PUnit.{1} => f) (fun _ => 1) h (i PUnit.unit) (j PUnit.unit)] at key
  erw [map_mul] at key
  simp only [LB.res_res] at key
  rw [LB.lcg_pull]
  change res _ (res (hle i) _) = _ * res _ (res (hle j) _)
  simp only [LB.res_res]
  exact key

theorem eq_bot_of_small {S : Type} [CommRing S] [IsLocalRing S] (J : Ideal S) (hJ : J.FG)
    (H : ∀ (I' : Ideal S) (e : S), e ∈ J → IsLocalRing.maximalIdeal S * J ≤ I' → I' ≤ J →
      J ≤ I' ⊔ Ideal.span {e} → J ≤ I') : J = ⊥ := by
  classical
  have key : ∀ s : Finset S, (s : Set S) ⊆ J →
      J ≤ IsLocalRing.maximalIdeal S * J ⊔ Ideal.span (s : Set S) →
      J ≤ IsLocalRing.maximalIdeal S * J := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _ h; simpa using h
    | insert a s _ ih =>
      intro hs h
      rw [Finset.coe_insert] at hs h
      have hs' : (s : Set S) ⊆ J := (Set.subset_insert _ _).trans hs
      refine ih hs' (H _ a (hs (Set.mem_insert _ _)) le_sup_left
        (sup_le Ideal.mul_le_right (Ideal.span_le.2 hs')) ?_)
      rwa [Ideal.span_insert, sup_comm (Ideal.span {a}), ← sup_assoc] at h
  obtain ⟨s, hs⟩ := id hJ
  refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal S) J hJ ?_
    (IsLocalRing.maximalIdeal_le_jacobson _)
  exact key s (hs ▸ Ideal.subset_span) (hs.ge.trans le_sup_right)

theorem exists_ann {R : Type} [CommRing R] (p : Ideal R) [p.IsPrime] (I : Ideal R) (hI : I.FG)
    (hIp : I ≤ p)
    (H : ∀ (T : Type) [CommRing T] [IsLocalRing T] (g : R →+* T) (e : T), (∀ r ∉ p, IsUnit (g r)) →
      (∀ a ∈ IsLocalRing.maximalIdeal T, a * e = 0) → e ∈ IsLocalRing.maximalIdeal T →
      I ≤ RingHom.ker ((Ideal.Quotient.mk (Ideal.span {e})).comp g) → I ≤ RingHom.ker g) :
    ∃ c ∉ p, ∀ x ∈ I, c * x = 0 := by
  let S := Localization.AtPrime p
  have hJm : I.map (algebraMap R S) ≤ IsLocalRing.maximalIdeal S := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.map_mono hIp
  have hbot : I.map (algebraMap R S) = ⊥ := by
    refine eq_bot_of_small _ (hI.map _) fun I' e he h₁ h₂ h₃ => ?_
    have hne : I' ≠ ⊤ := fun h =>
      (IsLocalRing.maximalIdeal.isMaximal S).ne_top (top_unique (h ▸ h₂.trans hJm))
    haveI : Nontrivial (S ⧸ I') := Ideal.Quotient.nontrivial_iff.2 hne
    haveI : IsLocalRing (S ⧸ I') :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I') Ideal.Quotient.mk_surjective
    haveI : IsLocalHom (Ideal.Quotient.mk I') :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    have := H (S ⧸ I') ((Ideal.Quotient.mk I').comp (algebraMap R S)) (Ideal.Quotient.mk I' e)
      (fun r hr => (IsLocalization.map_units S (⟨r, hr⟩ : p.primeCompl)).map (Ideal.Quotient.mk I')) ?_ ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      exact (Ideal.Quotient.eq_zero_iff_mem (I := I')).1 (this hx)
    · intro a ha
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      exact h₁ (Ideal.mul_mem_mul (fun hb => ha (hb.map _)) he)
    · exact fun hu => hJm he (IsUnit.of_map _ _ hu)
    · intro x hx
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (h₃ (Ideal.mem_map_of_mem _ hx))
      obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hz
      rw [RingHom.mem_ker, RingHom.comp_apply, RingHom.comp_apply, ← hyz, map_add,
        Ideal.Quotient.eq_zero_iff_mem.2 hy, zero_add, Ideal.Quotient.eq_zero_iff_mem, map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  have hx : ∀ x ∈ I, ∃ c ∉ p, c * x = 0 := fun x hx => by
    have h0 : algebraMap R S x = 0 := by
      have := Ideal.mem_map_of_mem (algebraMap R S) hx
      rwa [hbot, Ideal.mem_bot] at this
    obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl S x).1 h0
    exact ⟨c, c.2, hc⟩
  obtain ⟨s, rfl⟩ := hI
  choose! c hc using hx
  refine ⟨∏ y ∈ s, c y, ?_, ?_⟩
  · exact Submonoid.prod_mem p.primeCompl fun y hy => (hc y (Ideal.subset_span hy)).1
  · intro x hx
    have : Ideal.span (s : Set R) ≤ LinearMap.ker (LinearMap.mulLeft R (∏ y ∈ s, c y)) := by
      refine Ideal.span_le.2 fun y hy => ?_
      obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem c (show y ∈ s from hy)
      change (∏ y ∈ s, c y) * y = 0
      rw [hd, mul_comm (c y), _root_.mul_assoc, (hc y (Ideal.subset_span hy)).2, mul_zero]
    exact this hx

section BaseChange
variable {S S' : Scheme.{0}} (φ : S' ⟶ S) (A : Over S)

theorem isPullback_iso_comp {W P X Y Z : Scheme.{0}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback a b f g) (e : W ⟶ P) [IsIso e] : IsPullback (e ≫ a) (e ≫ b) f g :=
  h.of_iso (asIso e).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp) (by simp)

def sqMap : ((Over.pullback φ).obj A ⊗ (Over.pullback φ).obj A).left ⟶ (A ⊗ A).left :=
  (Functor.LaxMonoidal.μ (Over.pullback φ) A A).left ≫ pullback.fst (A ⊗ A).hom φ

theorem isPullback_sqMap :
    IsPullback (sqMap φ A) ((Over.pullback φ).obj A ⊗ (Over.pullback φ).obj A).hom (A ⊗ A).hom φ := by
  have h := IsPullback.of_hasPullback (A ⊗ A).hom φ
  have hw := Over.w (Functor.LaxMonoidal.μ (Over.pullback φ) A A)
  haveI : IsIso (Functor.LaxMonoidal.μ (Over.pullback φ) A A).left :=
    (Over.forget S').map_isIso (Functor.LaxMonoidal.μ (Over.pullback φ) A A)
  rw [← hw]
  exact isPullback_iso_comp h _

theorem lift_sqMap (a b : A ⟶ A) :
    (lift ((Over.pullback φ).map a) ((Over.pullback φ).map b)).left ≫ sqMap φ A =
      pullback.fst A.hom φ ≫ (lift a b).left := by
  rw [sqMap, ← Category.assoc, ← Over.comp_left, Functor.Monoidal.lift_μ]
  exact pullback.lift_fst _ _ _

end BaseChange

theorem triv_lift (hobs : ∀ (R : Type) [CommRing R] [IsLocalRing R] (ε : R), (∀ a ∈ IsLocalRing.maximalIdeal R, a * ε = 0) → ∀ (A : Over (Spec (CommRingCat.of R))) [GrpObj A], IsAbelianScheme A → ∀ M : LB (A ⊗ A).left, M.IsLB → (∃ t : LB.Gen (M.pull (lift (𝟙 A) 1).left), t.IsGen) → (∃ t : LB.Gen (M.pull (lift 1 (𝟙 A)).left), t.IsGen) → ∀ (X' : Scheme.{0}) (π : X' ⟶ (A ⊗ A).left) (f' : X' ⟶ Spec (CommRingCat.of (R ⧸ Ideal.span {ε}))), IsPullback π f' (A ⊗ A).hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ε})))) → ε ∈ IsLocalRing.maximalIdeal R → (∃ t : LB.Gen (M.pull π), t.IsGen) → ∃ t : LB.Gen M, t.IsGen)
    {S : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) (M : LB (A ⊗ A).left)
    (hM : M.IsLB) (h₁ : Triv (M.pull (lift (𝟙 A) 1).left)) (h₂ : Triv (M.pull (lift 1 (𝟙 A)).left))
    (T : Type) [CommRing T] [IsLocalRing T] (φ : Spec (CommRingCat.of T) ⟶ S) (e : T)
    (he : ∀ a ∈ IsLocalRing.maximalIdeal T, a * e = 0) (he' : e ∈ IsLocalRing.maximalIdeal T)
    (H : ∀ (X' : Scheme.{0}) (π : X' ⟶ (A ⊗ A).left)
      (f' : X' ⟶ Spec (CommRingCat.of (T ⧸ Ideal.span {e}))),
      IsPullback π f' (A ⊗ A).hom
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {e}))) ≫ φ) → Triv (M.pull π)) :
    Triv (M.pull (sqMap φ A)) := by
  have hp := IsPullback.of_hasPullback ((Over.pullback φ).obj A ⊗ (Over.pullback φ).obj A).hom
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {e}))))
  refine hobs T e he ((Over.pullback φ).obj A) (TLinPf.isAb_pullback φ A hA) (M.pull (sqMap φ A))
    (LB.isLB_pull hM _) ?_ ?_ _ _ _ hp he' ?_
  · refine triv_pull_pull _ _ (triv_comp (pullback.fst A.hom φ) ?_ h₁)
    rw [← lift_sqMap, Functor.map_one, CategoryTheory.Functor.map_id]
  · refine triv_pull_pull _ _ (triv_comp (pullback.fst A.hom φ) ?_ h₂)
    rw [← lift_sqMap, Functor.map_one, CategoryTheory.Functor.map_id]
  · exact triv_pull_pull _ _ (H _ _ _ (hp.paste_horiz (isPullback_sqMap φ A)))

theorem bijective_appTop (hG : GlobalFnsSt) {S S' X : Scheme.{0}} (B : Over S) [GrpObj B]
    (hB : IsAbelianScheme B) {φ : S' ⟶ S} {π : X ⟶ B.left} {f : X ⟶ S'}
    (h : IsPullback π f B.hom φ) : Function.Bijective f.appTop.hom := by
  have h₁ : Function.Bijective (pullback.snd B.hom φ).appTop.hom :=
    hG _ _ (TLinPf.isAb_pullback φ B hB)
  have h₂ : Function.Bijective h.isoPullback.hom.appTop.hom :=
    ConcreteCategory.bijective_of_isIso (h.isoPullback.hom.app ⊤)
  rw [← h.isoPullback_hom_snd, Scheme.Hom.comp_appTop]
  exact h₂.comp h₁

theorem triv_basicOpen_of_triv_fibre : GlobalFnsSt → (∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X), M.IsLB → Nonempty (Perf f M) → UniversallyClosed f → Surjective f → ∀ (K : Type) [Field K] (g₀ : R →+* K) (X₀ : Scheme.{0}) (π₀ : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π₀ f₀ f (Spec.map (CommRingCat.ofHom g₀)) → Function.Bijective f₀.appTop.hom → Triv (M.pull π₀) → ∃ (r : R) (I : Ideal R), g₀ r ≠ 0 ∧ I.FG ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) → IsUnit (g r) → (Triv (M.pull π) ↔ I ≤ RingHom.ker g)) → (∀ (R : Type) [CommRing R] [IsLocalRing R] (ε : R), (∀ a ∈ IsLocalRing.maximalIdeal R, a * ε = 0) → ∀ (A : Over (Spec (CommRingCat.of R))) [GrpObj A], IsAbelianScheme A → ∀ M : LB (A ⊗ A).left, M.IsLB → (∃ t : LB.Gen (M.pull (lift (𝟙 A) 1).left), t.IsGen) → (∃ t : LB.Gen (M.pull (lift 1 (𝟙 A)).left), t.IsGen) → ∀ (X' : Scheme.{0}) (π : X' ⟶ (A ⊗ A).left) (f' : X' ⟶ Spec (CommRingCat.of (R ⧸ Ideal.span {ε}))), IsPullback π f' (A ⊗ A).hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ε})))) → ε ∈ IsLocalRing.maximalIdeal R → (∃ t : LB.Gen (M.pull π), t.IsGen) → ∃ t : LB.Gen M, t.IsGen) → ∀ (R : Type) [CommRing R] (A : Over (Spec (CommRingCat.of R))) [GrpObj A], IsAbelianScheme A → ∀ M : LB (A ⊗ A).left, M.IsLB → Nonempty (Perf (A ⊗ A).hom M) → Triv (M.pull (lift (𝟙 A) 1).left) → Triv (M.pull (lift 1 (𝟙 A)).left) → ∀ (K : Type) [Field K] (g₀ : R →+* K) (X₀ : Scheme.{0}) (π₀ : X₀ ⟶ (A ⊗ A).left) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π₀ f₀ (A ⊗ A).hom (Spec.map (CommRingCat.ofHom g₀)) → Triv (M.pull π₀) → ∃ r : R, g₀ r ≠ 0 ∧ Triv (M.pull ((A ⊗ A).hom ⁻¹ᵁ (PrimeSpectrum.basicOpen r)).ι) := by
  intro hG hsee hobs R _ A _ hA M hM hP h₁ h₂ K _ g₀ X₀ π₀ f₀ h₀ ht₀
  have hB := Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  haveI := hB.proper
  haveI := hB.geomConnected
  obtain ⟨r, I, hr, hI, H⟩ := hsee R _ (A ⊗ A).hom M hM hP inferInstance inferInstance K g₀ X₀ π₀ f₀ h₀
    (bijective_appTop hG _ hB h₀) ht₀
  haveI : (RingHom.ker g₀).IsPrime := RingHom.ker_isPrime g₀
  obtain ⟨c, hc, hcI⟩ := exists_ann (RingHom.ker g₀) I hI
    ((H K g₀ X₀ π₀ f₀ h₀ (Ne.isUnit hr)).1 ht₀) (fun T _ _ g e hu he he' hle => by
      refine (H T g _ _ _ (isPullback_sqMap (Spec.map (CommRingCat.ofHom g)) A) (hu r hr)).1 ?_
      refine triv_lift hobs A hA M hM h₁ h₂ T _ e he he' fun X' π f' hp => ?_
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp] at hp
      exact (H _ _ X' π f' hp ((hu r hr).map (Ideal.Quotient.mk (Ideal.span {e})))).2 hle)
  refine ⟨r * c, by rw [map_mul]; exact mul_ne_zero hr hc, ?_⟩
  let L := Localization.Away (r * c)
  have hu : IsUnit (algebraMap R L (r * c)) := IsLocalization.Away.algebraMap_isUnit _
  rw [map_mul, IsUnit.mul_iff] at hu
  have hp := IsPullback.of_hasPullback (A ⊗ A).hom (Spec.map (CommRingCat.ofHom (algebraMap R L)))
  have ht := (H L (algebraMap R L) _ _ _ hp hu.1).2 fun x hx => by
    rw [RingHom.mem_ker, ← hu.2.mul_right_eq_zero, ← map_mul, hcI x hx, map_zero]
  haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R L))) :=
    IsOpenImmersion.of_isLocalization (r * c)
  have hsub : Set.range (((A ⊗ A).hom ⁻¹ᵁ (PrimeSpectrum.basicOpen (r * c))).ι ≫ (A ⊗ A).hom) ⊆
      Set.range (Spec.map (CommRingCat.ofHom (algebraMap R L))) := by
    rintro _ ⟨y, rfl⟩
    have := PrimeSpectrum.localization_away_comap_range L (r * c)
    change _ ∈ Set.range (PrimeSpectrum.comap (algebraMap R L))
    rw [this]
    exact y.2
  exact triv_comp (hp.lift _ _ (IsOpenImmersion.lift_fac _ _ hsub).symm) (hp.lift_fst _ _ _) ht

end GlobalTheory.AbLaw.CubeOpen
