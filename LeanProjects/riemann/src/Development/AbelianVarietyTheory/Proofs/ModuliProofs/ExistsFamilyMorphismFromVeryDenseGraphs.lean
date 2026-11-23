import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFlatProjectiveThroughPointsGoodFibresStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjRepGraphSegreCoordinatesFibreStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjProperRelAmpleOfProjectiveCoordinateRep
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MemIdealOfOfDense
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SpMapCompRingHomComp
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSchemeMapOfProjectiveCoordinates
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SegreCoordinates
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAwaySurjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionAndGeometricallyConnect
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsoOfProjectiveCoordinateRepresentation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SecCoordBcScaleUnique
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace GlobalTheory.ZM.GraphMor

theorem spMap_comp_hom {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem exists_chart_two {Y X₁ X₂ : Scheme.{0}} {σ₁ σ₂ : Type} {M₁ : LB X₁} {M₂ : LB X₂} (h₁ : M₁.IsLB) (h₂ : M₂.IsLB)
    (th₁ : σ₁ → M₁.Sec) (th₂ : σ₂ → M₂.Sec) (a₁ : Y ⟶ X₁) (a₂ : Y ⟶ X₂) (t : Y) :
    ∃ (A : Type) (_ : CommRing A) (y : Sp A ⟶ Y) (_ : IsOpenImmersion y) (v₁ : σ₁ → A) (v₂ : σ₂ → A),
      t ∈ Set.range y ∧ SecCoord M₁ th₁ (y ≫ a₁) v₁ ∧ SecCoord M₂ th₂ (y ≫ a₂) v₂ := by
  obtain ⟨W, hW, j, hj, ht, hc⟩ := RepUniq.exists_affine_secCoord h₁ th₁ a₁ t
  obtain ⟨t', rfl⟩ : t ∈ Set.range hW.fromSpec := by rw [hW.range_fromSpec]; exact ht
  obtain ⟨W', hW', j', hj', ht', hc'⟩ := RepUniq.exists_affine_secCoord h₂ th₂ (hW.fromSpec ≫ a₂) t'
  obtain ⟨t'', rfl⟩ : t' ∈ Set.range hW'.fromSpec := by rw [hW'.range_fromSpec]; exact ht'
  obtain ⟨β, hβ⟩ := RepUniq.exists_spMap (R := Γ(Y, W)) (A := Γ(Spec Γ(Y, W), W')) hW'.fromSpec
  have hb := Coord.baseChange hc β
  rw [← hβ] at hb
  exact ⟨Γ(Spec Γ(Y, W), W'), inferInstance, hW'.fromSpec ≫ hW.fromSpec,
    (inferInstance : IsOpenImmersion (hW'.fromSpec ≫ hW.fromSpec)), _, _, ⟨t'', rfl⟩, hb, hc'⟩

theorem exists_coord_field {X : Scheme.{0}} {σ : Type} {M : LB X} (h : M.IsLB) (th : σ → M.Sec) {K : Type} [Field K]
    (y : Sp K ⟶ X) : ∃ v, SecCoord M th y v := by
  let t : Sp K := (default : PrimeSpectrum K)
  obtain ⟨j, hj⟩ := LB.mem_of_cover h (y t)
  have hle : (⊤ : (Sp K).Opens) ≤ y ⁻¹ᵁ M.U j := fun t' _ => by
    obtain rfl : t' = t := Subsingleton.elim (α := PrimeSpectrum K) _ _
    exact hj
  refine ⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom ((y.appLE _ ⊤ hle).hom ((th i).f j)),
    RepUniq.secCoord_of_frame h ⟨j, hle, 1, isUnit_one, fun i => ?_⟩⟩
  simp [RepUniq.fn]

theorem hom_ext_chart {Y X : Scheme.{0}} (a b : Y ⟶ X)
    (h : ∀ t : Y, ∃ (T : Scheme.{0}) (y : T ⟶ Y) (_ : IsOpenImmersion y), t ∈ Set.range y ∧ y ≫ a = y ≫ b) : a = b := by
  refine Scheme.hom_ext_of_forall _ _ fun t => ?_
  obtain ⟨T, y, _, ht, e⟩ := h t
  refine ⟨y.opensRange, ht, ?_⟩
  rw [← y.isoOpensRange_inv_comp, Category.assoc, Category.assoc, e]

theorem exists_common_field {R K K' : Type} [CommRing R] [Field K] [Field K'] (x : R →+* K) (β : R →+* K')
    (h : RingHom.ker x = RingHom.ker β) :
    ∃ (L : Type) (_ : Field L) (a : K' →+* L) (b : K →+* L), spMap a ≫ spMap β = spMap b ≫ spMap x := by
  let t : Sp K := (default : PrimeSpectrum K)
  let t' : Sp K' := (default : PrimeSpectrum K')
  have e : spMap β t' = spMap x t := PrimeSpectrum.ext (by
    rw [VeryDenseFibres.spMap_apply_asIdeal, VeryDenseFibres.spMap_apply_asIdeal, h])
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := spMap β) (g := spMap x) t' t e
  let L : Type := (pullback (spMap β) (spMap x)).residueField z
  obtain ⟨a, ha⟩ := RepUniq.exists_spMap (R := K') (A := L)
    ((pullback (spMap β) (spMap x)).fromSpecResidueField z ≫ pullback.fst _ _)
  obtain ⟨b, hb⟩ := RepUniq.exists_spMap (R := K) (A := L)
    ((pullback (spMap β) (spMap x)).fromSpecResidueField z ≫ pullback.snd _ _)
  refine ⟨L, inferInstance, a, b, ?_⟩
  rw [← ha, ← hb, Category.assoc, Category.assoc, pullback.condition]

theorem smooth_of_veryDense {R : Type} [CommRing R] {Z : Scheme.{0}} (s : Z ⟶ Sp R) [IsProper s] [Flat s]
    [LocallyOfFinitePresentation s] {P : Set (Ideal R)} (hP : VeryDense P)
    (h : ∀ q ∈ P, ∃ (K : Type) (_ : Field K) (x : R →+* K), RingHom.ker x = q ∧ Smooth (pullback.snd s (spMap x))) :
    Smooth s := by
  rw [← Scheme.Hom.smoothLocus_eq_top_iff]
  refine VeryDenseFibres.eq_top_of_forall_mem s P (fun q hq => ?_) _ fun z hz => ?_
  · obtain ⟨p, h1, h2, h3, -⟩ := hP q 1 hq ((Ideal.ne_top_iff_one _).1 hq.ne_top)
    exact ⟨p, h1, h2, h3⟩
  · obtain ⟨K, _, x, hx, hs⟩ := h _ hz
    let w : Sp K := (default : PrimeSpectrum K)
    have hw : s z = spMap x w := PrimeSpectrum.ext (by rw [VeryDenseFibres.spMap_apply_asIdeal, hx])
    refine VeryDenseFibres.mem_smoothLocus_of_smooth_fiber s z ?_
    rw [hw]
    exact VeryDenseFibres.smooth_fiber_of_smooth_fiber s (spMap x) w
      (inferInstanceAs (Smooth (pullback.snd (pullback.snd s (spMap x)) ((Sp K).fromSpecResidueField w))))

theorem dense_of_veryDense {R : Type} [CommRing R] {P : Set (Ideal R)} (hP : VeryDense P) :
    Dense {q : Sp R | q.asIdeal ∈ P} := by
  refine (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).dense_iff.2 ?_
  rintro _ ⟨f, rfl⟩ ⟨q, hq⟩
  obtain ⟨p, h1, h2, -, h4⟩ := hP q.asIdeal f q.isPrime hq
  exact ⟨⟨p, h2⟩, h4, h1⟩

theorem exists_pair {S Y : Scheme.{0}} (Z₁ Z₂ : Over S) (a₁ : Y ⟶ Z₁.left) (a₂ : Y ⟶ Z₂.left)
    (h : a₁ ≫ Z₁.hom = a₂ ≫ Z₂.hom) :
    ∃ c : Y ⟶ (Z₁ ⊗ Z₂).left, c ≫ (fst Z₁ Z₂).left = a₁ ∧ c ≫ (snd Z₁ Z₂).left = a₂ :=
  ⟨pullback.lift a₁ a₂ h, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

theorem mem_of_components {R σ : Type} [CommRing R] {I : Ideal (MvPolynomial σ R)} {F : MvPolynomial σ R}
    (h : ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) : F ∈ I := by
  rw [← MvPolynomial.sum_homogeneousComponent F]
  exact Ideal.sum_mem _ fun e _ => h e

theorem eval_eq_zero_of_mem_idealOf {R σ : Type} [CommRing R] {Y : Scheme.{0}} {s : Y ⟶ Sp R} {M : LB Y}
    {th : σ → M.Sec} {F : MvPolynomial σ R} (hF : F ∈ idealOf s M th (𝟙 Y)) {T : Type} [CommRing T] {β : R →+* T}
    {y : Sp T ⟶ Y} {v : σ → T} (hy : y ≫ s = spMap β) (hv : SecCoord M th y v) : MvPolynomial.eval₂ β v F = 0 := by
  simp only [idealOf, Ideal.mem_iInf] at hF
  exact hF T inferInstance β y v ⟨hy, by rwa [Category.comp_id]⟩

theorem exists_hom_of_graphs : ∀ (R σ₁ σ₂ Hh : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] [Finite σ₁] [Finite σ₂] [Finite Hh] (Z₁ Z₂ : Over (Sp R)) (I₁ : Ideal (MvPolynomial σ₁ R)) (I₂ : Ideal (MvPolynomial σ₂ R)) (M₁ : LB Z₁.left) (M₂ : LB Z₂.left) (th₁ : σ₁ → M₁.Sec) (th₂ : σ₂ → M₂.Sec) (p₁ : Hh → σ₁ → R) (p₂ : Hh → σ₂ → R) (Q : Polynomial ℚ) (d : ℕ) (G : ∀ (K : Type) [Field K] (x : R →+* K), (pullback Z₁.hom (spMap x) ⟶ Z₂.left) → Prop), ProjRep I₁ Z₁.hom M₁ th₁ → ProjRep I₂ Z₂.hom M₂ th₂ → IsProper Z₁.hom → IsProper Z₂.hom → Smooth Z₁.hom → (∀ (K : Type) [Field K] (x : R →+* K) f, G K x f → f ≫ Z₂.hom = pullback.snd _ _ ≫ spMap x ∧ CutBy (graphIdeal (pullback.snd Z₁.hom (spMap x)) M₁ th₁ (pullback.fst _ _) M₂ th₂ f) Q d (fun h i => x (p₁ h i.1 * p₂ h i.2))) → VeryDense {q | ∃ (K : Type) (_ : Field K) (x : R →+* K) (f : _), RingHom.ker x = q ∧ G K x f} → ∃ F : Z₁ ⟶ Z₂, ∀ (K : Type) [Field K] (x : R →+* K) f, G K x f → f = pullback.fst _ _ ≫ F.left := by
  intro R σ₁ σ₂ Hh _ _ _ _ _ _ Z₁ Z₂ I₁ I₂ M₁ M₂ th₁ th₂ p₁ p₂ Q d G h₁ h₂ hp₁ hp₂ hsm hG hP
  obtain ⟨Γ', M, th, hΓ, -, hflat, hlfp, hfib⟩ := GlobalTheory.T.exists_flat_projective_through_points_goodFibres R (σ₁ × σ₂) Hh
    (fun h i => p₁ h i.1 * p₂ h i.2) Q d
    (fun K _ x I => ∃ f, G K x f ∧
      I = graphIdeal (pullback.snd Z₁.hom (spMap x)) M₁ th₁ (pullback.fst _ _) M₂ th₂ f)
    (by
      rintro K _ x _ ⟨f, hf, rfl⟩
      exact ⟨ideals_homogeneous.2.1 _ _ _ _ _ _ _ _ _ _ _ _ _ h₁.1 h₂.1, (hG K x f hf).2⟩)
    (fun q r hq hr => by
      obtain ⟨p, ⟨K, _, x, f, hx, hf⟩, hp⟩ := hP q r hq hr
      exact ⟨p, ⟨K, _, x, _, hx, f, hf, rfl⟩, hp⟩)
  have hpr : IsProper Γ'.hom := (projRep_projective_ample R _ _ Γ' M th hΓ).2.1

  have good : ∀ (K : Type) [Field K] (x : R →+* K) f, G K x f → ∃ φ : pullback Z₁.hom (spMap x) ⟶ Γ'.left,
      IsPullback φ (pullback.snd _ _) Γ'.hom (spMap x) ∧
      ∀ (T : Type) [CommRing T] (y : Sp T ⟶ pullback Z₁.hom (spMap x)) (v₁ : σ₁ → T) (v₂ : σ₂ → T),
        SecCoord M₁ th₁ (y ≫ pullback.fst _ _) v₁ → SecCoord M₂ th₂ (y ≫ f) v₂ →
        SecCoord M th (y ≫ φ) (fun i => v₁ i.1 * v₂ i.2) := by
    intro K _ x f hf
    obtain ⟨N, ty, hN, hc⟩ := GlobalTheory.T.projRep_graph_segre_coordinates_fibre R K σ₁ σ₂ x I₁ I₂ Z₁ Z₂ M₁ M₂ th₁ th₂ _ (pullback.snd _ _)
      (pullback.fst _ _) f h₁ h₂ (IsPullback.of_hasPullback _ _) (hG K x f hf).1
    obtain ⟨φ, hφ, -, hφc⟩ := hfib K x _ _ _ N ty ⟨f, hf, rfl⟩ hN
    exact ⟨φ, hφ, fun T _ y v₁ v₂ e₁ e₂ => (hφc T y _).1 (hc T y v₁ v₂ e₁ e₂)⟩
  have hsmΓ : Smooth Γ'.hom := smooth_of_veryDense Γ'.hom hP (by
    rintro _ ⟨K, _, x, f, rfl, hf⟩
    obtain ⟨φ, hφ, -⟩ := good K x f hf
    refine ⟨K, _, x, rfl, ?_⟩
    rw [← hφ.isoPullback_inv_snd]
    infer_instance)
  have hred : IsReduced Γ'.left := GlobalTheory.isReduced_of_smooth_of_isReduced Γ'.hom
  obtain ⟨I₃, M₃, th₃, h₃', hseg⟩ := SegreCoord.segre_coordinates R σ₁ σ₂ I₁ I₂ Z₁ Z₂ M₁ M₂ th₁ th₂ h₁ h₂
  have h₃ := ideals_homogeneous.2.2 R _ _ _ _ _ _ h₃'
  have w₁ : (fst Z₁ Z₂).left ≫ Z₁.hom = (Z₁ ⊗ Z₂).hom := Over.w _
  have w₂ : (snd Z₁ Z₂).left ≫ Z₂.hom = (Z₁ ⊗ Z₂).hom := Over.w _

  have hle : idealOf (Z₁ ⊗ Z₂).hom M₃ th₃ (𝟙 _) ≤ idealOf Γ'.hom M th (𝟙 _) := fun F hF => by
    refine mem_of_components fun e => ?_
    refine DenseFib.mem_idealOf_of_dense R _ _ _ M th _ _ e hred hflat hlfp hΓ.1 (dense_of_veryDense hP)
      (MvPolynomial.homogeneousComponent_isHomogeneous e F) ?_
    intro K' _ _ β y v hy hβ hv
    have hF' := ideals_homogeneous.1 R _ _ _ _ _ _ _ h₃.1 F hF e
    obtain ⟨K, _, x, f, hx, hf⟩ := hβ ⟨(default : PrimeSpectrum K'), rfl⟩
    rw [VeryDenseFibres.spMap_apply_asIdeal] at hx
    obtain ⟨L, _, a, b, hab⟩ := exists_common_field x β hx
    obtain ⟨φ, hφ, hc⟩ := good K x f hf
    have hw : (spMap a ≫ y) ≫ Γ'.hom = spMap b ≫ spMap x := by rw [Category.assoc, hy, hab]
    let z := hφ.lift _ _ hw
    obtain ⟨v₁, hv₁⟩ := exists_coord_field h₁.1 th₁ (z ≫ pullback.fst _ _)
    obtain ⟨v₂, hv₂⟩ := exists_coord_field h₂.1 th₂ (z ≫ f)
    have hz := hc L z v₁ v₂ hv₁ hv₂
    rw [hφ.lift_fst] at hz
    obtain ⟨u, hu⟩ := Coord.unique hΓ.1 hz (Coord.baseChange hv a)
    obtain ⟨c, g₁, g₂⟩ := exists_pair Z₁ Z₂ (pullback.fst _ _) f (pullback.condition.trans (hG K x f hf).1.symm)
    have hs := Coord.scale (hseg L (z ≫ c) v₁ v₂ (by rwa [Category.assoc, g₁]) (by rwa [Category.assoc, g₂])) u
    have hb : (z ≫ c) ≫ (Z₁ ⊗ Z₂).hom = spMap (a.comp β) := by
      rw [spMap_comp_hom, hab, ← w₁, Category.assoc, reassoc_of% g₁, pullback.condition, hφ.lift_snd_assoc]
    have h0 := eval_eq_zero_of_mem_idealOf hF' hb hs
    apply a.injective
    rw [map_zero, MvPolynomial.eval₂_comp_left, ← h0]
    congr 1
    exact funext hu
  obtain ⟨g, hg, -, hgc, -⟩ := RepMap.exists_map_of_coord R _ _ _ _ _ Γ'.hom M₃ M th₃ th h₃ hΓ.1
    (fun T _ β y v hy hv => ⟨(hΓ.2.1 T β y v hy hv).1, fun F hF => eval_eq_zero_of_mem_idealOf (hle hF) hy hv⟩)
  have fib : ∀ (K : Type) [Field K] (x : R →+* K) f, G K x f → ∃ φ : pullback Z₁.hom (spMap x) ⟶ Γ'.left,
      IsPullback φ (pullback.snd _ _) Γ'.hom (spMap x) ∧ φ ≫ g ≫ (fst Z₁ Z₂).left = pullback.fst _ _ ∧
      φ ≫ g ≫ (snd Z₁ Z₂).left = f := by
    intro K _ x f hf
    obtain ⟨φ, hφ, hc⟩ := good K x f hf
    obtain ⟨c, g₁, g₂⟩ := exists_pair Z₁ Z₂ (pullback.fst _ _) f (pullback.condition.trans (hG K x f hf).1.symm)
    have e : φ ≫ g = c := hom_ext_chart _ _ fun t => by
      obtain ⟨A, _, y, hy, v₁, v₂, ht, hv₁, hv₂⟩ := exists_chart_two h₁.1 h₂.1 th₁ th₂ (pullback.fst _ _) f t
      refine ⟨_, y, hy, ht, ?_⟩
      have c₁ := (hgc A _ _).1 (hc A y v₁ v₂ hv₁ hv₂)
      have c₂ := hseg A (y ≫ c) v₁ v₂ (by rwa [Category.assoc, g₁]) (by rwa [Category.assoc, g₂])
      obtain ⟨β, hβ⟩ := RepUniq.exists_spMap ((y ≫ c) ≫ (Z₁ ⊗ Z₂).hom)
      obtain ⟨k₁, k₂⟩ := h₃.2.1 A β _ _ hβ c₂
      rw [← Category.assoc]
      refine (h₃.2.2 A β _ k₁ k₂).unique ⟨?_, c₁⟩ ⟨hβ, c₂⟩
      rw [← hβ, Category.assoc, hg, Category.assoc, hφ.w, Category.assoc, ← w₁, reassoc_of% g₁, pullback.condition]
    exact ⟨φ, hφ, by rw [reassoc_of% e, g₁], by rw [reassoc_of% e, g₂]⟩
  have hπ : (g ≫ (fst Z₁ Z₂).left) ≫ Z₁.hom = Γ'.hom := by rw [Category.assoc, w₁, hg]
  have hππ : IsProper ((g ≫ (fst Z₁ Z₂).left) ≫ Z₁.hom) := hπ ▸ hpr
  have hiso : IsIso (g ≫ (fst Z₁ Z₂).left) := DenseFibreIso.main R _ _ Z₁.hom _ _ hP hp₁ inferInstance
    (IsProper.of_comp _ Z₁.hom) (hπ ▸ hflat) (by
      rintro _ ⟨K, _, x, f, rfl, hf⟩
      obtain ⟨φ, hφ, e₁, -⟩ := fib K x f hf
      refine ⟨K, _, x, rfl, ?_⟩
      have hq : IsPullback φ (𝟙 _) (g ≫ (fst Z₁ Z₂).left) (pullback.fst Z₁.hom (spMap x)) :=
        IsPullback.of_bot (by rwa [Category.id_comp, hπ]) (by rw [e₁, Category.id_comp])
          (IsPullback.of_hasPullback Z₁.hom (spMap x))
      rw [← hq.isoPullback_inv_snd]
      infer_instance)
  refine ⟨Over.homMk (inv (g ≫ (fst Z₁ Z₂).left) ≫ g ≫ (snd Z₁ Z₂).left) ?_, fun K _ x f hf => ?_⟩
  · rw [Category.assoc, Category.assoc, w₂, hg, ← hπ, IsIso.inv_hom_id_assoc]
  · obtain ⟨φ, -, e₁, e₂⟩ := fib K x f hf
    change f = pullback.fst _ _ ≫ inv (g ≫ (fst Z₁ Z₂).left) ≫ g ≫ (snd Z₁ Z₂).left
    rw [← e₁, Category.assoc, IsIso.hom_inv_id_assoc, e₂]

end GlobalTheory.ZM.GraphMor
end
