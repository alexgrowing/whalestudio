import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjectiveRepresentationPullbackCoordinates
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SpMapCompRingHomComp
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SegreCoordinates
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsProjCoordRepresentationHomogeneousIdealFlaStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsoOfProjectiveCoordinateRepresentation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionCoordinateVectorExistsLocallyStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSchemeMapOfProjectiveCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjProperRelAmpleOfProjectiveCoordinateRep
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjRepGraphSegreCoordinatesFibreStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAwayProjectiveFormsThroughPoints
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoFibreOfPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.LocalGraph
open GlobalTheory.ZM.SegreCoord GlobalTheory.AbLaw.Segre

open MvPolynomial in

theorem homogeneousComponent_mem_vanIdeal {R σ Hh : Type} [CommRing R] (d : ℕ) (p : Hh → σ → R)
    (F : MvPolynomial σ R) (hF : F ∈ vanIdeal d p) (e : ℕ) : homogeneousComponent e F ∈ vanIdeal d p := by
  classical
  letI := (MvPolynomial.gradedAlgebra : GradedAlgebra (homogeneousSubmodule σ R))
  have h : (vanIdeal d p).IsHomogeneous (homogeneousSubmodule σ R) :=
    Ideal.homogeneous_span _ _ fun x hx => ⟨d, hx.1⟩
  have := h e hF
  rwa [show ((DirectSum.decompose (homogeneousSubmodule σ R) F e : homogeneousSubmodule σ R e) : MvPolynomial σ R)
    = homogeneousComponent e F from MvPolynomial.decomposition.decompose'_apply F e] at this

open MvPolynomial in

theorem eval₂_eq_zero_of_forms_le {K σ : Type} [CommRing K] {I J : Ideal (MvPolynomial σ K)} {d : ℕ}
    (hI : ∀ F ∈ I, ∀ e, homogeneousComponent e F ∈ I)
    (hle : ∀ e ≥ d, ∀ F : MvPolynomial σ K, F.IsHomogeneous e → F ∈ I → F ∈ J)
    {T : Type} [CommRing T] (β : K →+* T) (v : σ → T) (hv : Ideal.span (Set.range v) = ⊤)
    (hJ : ∀ F ∈ J, eval₂ β v F = 0) : ∀ F ∈ I, eval₂ β v F = 0 := by
  intro F hF
  have key : ∀ e, eval₂ β v (homogeneousComponent e F) = 0 := by
    intro e
    have h1 : ∀ i, v i ^ d * eval₂ β v (homogeneousComponent e F) = 0 := by
      intro i
      have := hJ _ (hle (d + e) (by omega) (X i ^ d * homogeneousComponent e F)
        ((isHomogeneous_X_pow i d).mul (homogeneousComponent_isHomogeneous e F)) (I.mul_mem_left _ (hI F hF e)))
      rwa [eval₂_mul, eval₂_pow, eval₂_X] at this
    have h2 := Ideal.span_pow_eq_top _ hv d
    have h3 : Ideal.span ((fun x => x ^ d) '' Set.range v) ≤
        LinearMap.ker (LinearMap.toSpanSingleton T T (eval₂ β v (homogeneousComponent e F))) := by
      refine Ideal.span_le.2 ?_
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact h1 i
    rw [h2] at h3
    simpa using h3 (Submodule.mem_top (x := (1 : T)))
  rw [← sum_homogeneousComponent F, eval₂_sum]
  exact Finset.sum_eq_zero fun e _ => key e

open MvPolynomial in

theorem mem_of_forall_map_mem {S σ : Type} [CommRing S] (J : Ideal (MvPolynomial σ S)) (e : ℕ)
    (hJ : ∀ F ∈ J, homogeneousComponent e F ∈ J)
    (hp : Module.Projective S (↥(homogeneousSubmodule σ S e) ⧸
      (J.restrictScalars S).comap (homogeneousSubmodule σ S e).subtype))
    (F : MvPolynomial σ S) (hF : F.IsHomogeneous e)
    (h : ∀ r : S, r ≠ 0 → ∃ (K : Type) (_ : CommRing K) (x : S →+* K), x r ≠ 0 ∧ map x F ∈ J.map (map x)) :
    F ∈ J := by
  set N := (J.restrictScalars S).comap (homogeneousSubmodule σ S e).subtype with hN
  let π : MvPolynomial σ S →ₗ[S] (↥(homogeneousSubmodule σ S e) ⧸ N) :=
    N.mkQ ∘ₗ (homogeneousComponent e).codRestrict (homogeneousSubmodule σ S e) fun G => homogeneousComponent_mem e G
  have hπ : ∀ G, π G = 0 ↔ homogeneousComponent e G ∈ J := fun G => Submodule.Quotient.mk_eq_zero N
  have hFe : homogeneousComponent e F = F := by rw [homogeneousComponent_of_mem hF, if_pos rfl]
  rw [← hFe, ← hπ]
  by_contra hne
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_ne_zero S hne
  obtain ⟨K, _, x, hx, hm⟩ := h _ hl
  let Λ : MvPolynomial σ K →ₗ[K] K := (basisMonomials σ K).constr K fun m => x (l (π (monomial m 1)))
  have hΛ : ∀ G, Λ (map x G) = x (l (π G)) := by
    intro G
    induction G using MvPolynomial.induction_on' with
    | monomial m c =>
      have h1 : (monomial m (x c) : MvPolynomial σ K) = x c • basisMonomials σ K m := by
        simp [smul_monomial]
      have h2 : (monomial m c : MvPolynomial σ S) = c • monomial m 1 := by simp [smul_monomial]
      rw [map_monomial, h1, map_smul, h2, map_smul, map_smul, smul_eq_mul, smul_eq_mul, map_mul]
      simp only [Λ, Module.Basis.constr_basis]
    | add p q hp hq => simp only [map_add, hp, hq]
  have key : ∀ G ∈ J.map (map x), ∀ H, Λ (H * G) = 0 := by
    intro G hG
    induction hG using Submodule.span_induction with
    | mem G hG =>
      obtain ⟨G, hG, rfl⟩ := hG
      intro H
      induction H using MvPolynomial.induction_on' with
      | monomial m c =>
        have h1 : (monomial m c : MvPolynomial σ K) = c • map x (monomial m 1) := by simp [smul_monomial]
        rw [h1, smul_mul_assoc, map_smul, ← map_mul, hΛ, (hπ _).2 (hJ _ (J.mul_mem_left _ hG))]
        simp
      | add p q hp hq => rw [add_mul, map_add, hp, hq, add_zero]
    | zero => simp
    | add p q _ _ hp hq => intro H; rw [mul_add, map_add, hp, hq, add_zero]
    | smul c p _ hp => intro H; rw [smul_eq_mul, ← _root_.mul_assoc, hp]
  have := key _ hm 1
  rw [_root_.one_mul, hΛ] at this
  exact hx this

theorem hom_ext_near {W Z : Scheme.{0}} (f g : W ⟶ Z)
    (h : ∀ w : W, ∃ (V : Scheme.{0}) (y : V ⟶ W), IsOpenImmersion y ∧ w ∈ Set.range y ∧ y ≫ f = y ≫ g) : f = g := by
  refine Scheme.hom_ext_of_forall f g fun w => ?_
  obtain ⟨V, y, _, hw, e⟩ := h w
  refine ⟨y.opensRange, hw, ?_⟩
  rw [← cancel_epi y.isoOpensRange.hom, ← Category.assoc, ← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, e]

section Fibre
variable {R σ₁ σ₂ : Type} [CommRing R] [Finite σ₁] [Finite σ₂] {Z₁ Z₂ : Over (Sp R)}
  {I₁ : Ideal (MvPolynomial σ₁ R)} {I₂ : Ideal (MvPolynomial σ₂ R)} {M₁ : LB Z₁.left} {M₂ : LB Z₂.left}
  {th₁ : σ₁ → M₁.Sec} {th₂ : σ₂ → M₂.Sec}

theorem map_mem_graphIdeal {P W : Scheme.{0}} {p : P ⟶ Z₁.left} {q : P ⟶ Z₂.left} (sq : IsPullback p q Z₁.hom Z₂.hom)
    {K : Type} [CommRing K] (x : R →+* K) (s : W ⟶ Sp K) (a₁ : W ⟶ Z₁.left) (a₂ : W ⟶ Z₂.left)
    (e₁ : a₁ ≫ Z₁.hom = s ≫ spMap x) (e₂ : a₂ ≫ Z₂.hom = s ≫ spMap x) {F : MvPolynomial (σ₁ × σ₂) R}
    (hF : F ∈ graphIdeal (p ≫ Z₁.hom) M₁ th₁ p M₂ th₂ q) :
    MvPolynomial.map x F ∈ graphIdeal s M₁ th₁ a₁ M₂ th₂ a₂ := by
  rw [mem_graphIdeal] at hF ⊢
  intro T _ β y a b hy ha hb
  rw [MvPolynomial.eval₂_map]
  refine hF T _ (y ≫ sq.lift a₁ a₂ (e₁.trans e₂.symm)) a b ?_ ?_ ?_
  · rw [Category.assoc, sq.lift_fst_assoc, e₁, ← Category.assoc, hy, spc]
  · rwa [Category.assoc, sq.lift_fst]
  · rwa [Category.assoc, sq.lift_snd]

theorem fibre_graph (h₁ : ProjRep I₁ Z₁.hom M₁ th₁) (h₂ : ProjRep I₂ Z₂.hom M₂ th₂)
    {P : Scheme.{0}} {p : P ⟶ Z₁.left} {q : P ⟶ Z₂.left} (sq : IsPullback p q Z₁.hom Z₂.hom)
    {S : Type} [CommRing S] (a : R →+* S) {J : Ideal (MvPolynomial (σ₁ × σ₂) S)} {Y : Scheme.{0}} {sY : Y ⟶ Sp S}
    {N : LB Y} {ty : σ₁ × σ₂ → N.Sec} (hY : ProjRep J sY N ty) (g : Y ⟶ P) (hg : g ≫ p ≫ Z₁.hom = sY ≫ spMap a)
    (hc : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y) (v : σ₁ × σ₂ → T), SecCoord N ty y v →
      SecCoord (box p q M₁ M₂) (fun i : σ₁ × σ₂ => boxSec p q (th₁ i.1) (th₂ i.2)) (y ≫ g) v)
    {K : Type} [CommRing K] (x : R →+* K) (x' : S →+* K) (hx : x'.comp a = x) {W : Scheme.{0}} (s : W ⟶ Sp K)
    (a₁ : W ⟶ Z₁.left) (a₂ : W ⟶ Z₂.left) (pb : IsPullback a₁ s Z₁.hom (spMap x)) (e₂ : a₂ ≫ Z₂.hom = s ≫ spMap x)
    (hJ : ∀ (T : Type) [CommRing T] (β : K →+* T) (v : σ₁ × σ₂ → T), Ideal.span (Set.range v) = ⊤ →
      ((∀ F ∈ graphIdeal s M₁ th₁ a₁ M₂ th₂ a₂, MvPolynomial.eval₂ β v F = 0) ↔
        ∀ F ∈ J.map (MvPolynomial.map x'), MvPolynomial.eval₂ β v F = 0)) :
    ∃ e : W ⟶ Y, IsPullback e s sY (spMap x') ∧ e ≫ g ≫ p = a₁ ∧ e ≫ g ≫ q = a₂ := by
  obtain ⟨N', ty', hW, hcW⟩ := GlobalTheory.T.projRep_graph_segre_coordinates_fibre R K σ₁ σ₂ x I₁ I₂ Z₁ Z₂ M₁ M₂ th₁ th₂ W s a₁ a₂ h₁ h₂ pb e₂
  have hpb := IsPullback.of_hasPullback sY (spMap x')
  obtain ⟨t₁, hrep₁, hc₁⟩ := GlobalTheory.ZM.RepBC.projRep_baseChange S K _ x' J Y _ sY _ _ N ty hY hpb
  obtain ⟨e, he, -, hce⟩ := GlobalTheory.RepUniq.exists_iso_of_projRep K _ _ _ W _ s _ N' _ ty' t₁ hW hrep₁ hJ
  have h0 : IsPullback e.hom s (pullback.snd sY (spMap x')) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [he, Category.comp_id]⟩
  have h1 : IsPullback (e.hom ≫ pullback.fst sY (spMap x')) s sY (spMap x') := by simpa using h0.paste_horiz hpb
  have hP := projRep_box p q th₁ th₂ sq h₁ h₂
  have key : (e.hom ≫ pullback.fst sY (spMap x')) ≫ g = sq.lift a₁ a₂ (pb.w.trans e₂.symm) := by
    refine hom_ext_near _ _ fun w => ?_
    have hB := isLB_box a₁ a₂ h₁.1 h₂.1
    obtain ⟨T₀, _, y₀, v₀, hy₀, ⟨z, hz⟩, hv₀⟩ := (GlobalTheory.T.sectionCoordinateVector_exists_locally W _ _
      (fun i : σ₁ × σ₂ => boxSec a₁ a₂ (th₁ i.1) (th₂ i.2)) hB).2.2 w
    obtain ⟨T, _, φ, hφ, ⟨z', hz'⟩, u, v, hu, hv, -⟩ := split_near a₁ a₂ th₁ th₂ h₁.1 h₂.1 y₀ v₀ hv₀ z
    refine ⟨_, spMap φ ≫ y₀, inferInstance, ⟨z', by rw [Scheme.Hom.comp_apply, hz', hz]⟩, ?_⟩
    rw [← Category.assoc] at hu hv
    generalize spMap φ ≫ y₀ = y at hu hv
    obtain ⟨β, hβ⟩ : ∃ β : K →+* T, y ≫ s = spMap β := ⟨(Spec.preimage (y ≫ s)).hom, (Spec.map_preimage _).symm⟩
    have c := hcW T y u v hu hv
    refine (hP.2.2 T (β.comp x) (fun i => u i.1 * v i.2) (hW.2.1 T β y _ hβ c).1 ?_).unique ⟨?_, ?_⟩ ⟨?_, ?_⟩
    · intro F hF
      have := (hW.2.1 T β y _ hβ c).2 _ (map_mem_graphIdeal sq x s a₁ a₂ pb.w e₂ hF)
      rwa [MvPolynomial.eval₂_map] at this
    · rw [Category.assoc, Category.assoc, hg, ← Category.assoc _ sY, h1.w, Category.assoc, ← Category.assoc y, hβ,
        spc, spc, hx]
    · have := hc T _ _ ((hc₁ T _ _).1 ((hce T y _).1 c))
      simpa only [Category.assoc] using this
    · rw [Category.assoc, sq.lift_fst_assoc, pb.w, ← Category.assoc, hβ, spc]
    · exact secCoord_box p q th₁ th₂ _ u v (by rwa [Category.assoc, sq.lift_fst]) (by rwa [Category.assoc, sq.lift_snd])
  refine ⟨_, h1, ?_, ?_⟩
  · rw [← Category.assoc, key, sq.lift_fst]
  · rw [← Category.assoc, key, sq.lift_snd]
end Fibre

theorem isIso_snd_of_fibre {Y X W B B' : Scheme.{0}} (ψ : Y ⟶ X) (s : X ⟶ B) (b : B' ⟶ B) (e : W ⟶ Y) (sW : W ⟶ B')
    (h : IsPullback e sW (ψ ≫ s) b) (h' : IsPullback (e ≫ ψ) sW s b) : IsIso (pullback.snd ψ (pullback.fst s b)) := by
  have h1 : IsPullback e h'.isoPullback.hom ψ (pullback.fst s b) :=
    IsPullback.of_bot (by simpa using h) (by simp) (IsPullback.of_hasPullback s b)
  have : h1.isoPullback.hom ≫ pullback.snd ψ (pullback.fst s b) = h'.isoPullback.hom := h1.isoPullback_hom_snd
  exact IsIso.of_isIso_fac_left this

theorem ne_zero_of_point {R K : Type} [CommRing R] [Field K] (x : R →+* K) (f : R) {W : Scheme.{0}} (w : W)
    (s : W ⟶ Sp K) (t : W ⟶ Sp (Localization.Away f))
    (h : s ≫ spMap x = t ≫ spMap (algebraMap R (Localization.Away f))) : x f ≠ 0 := by
  intro h0
  have h1 : spMap x (s w) = spMap (algebraMap R (Localization.Away f)) (t w) := by
    rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]
  have h2 : spMap x (s w) ∈ Set.range (spMap (algebraMap R (Localization.Away f))) := ⟨_, h1.symm⟩
  have h3 := (PrimeSpectrum.localization_away_comap_range (Localization.Away f) f).le h2
  apply h3
  change x f ∈ (s w).asIdeal
  rw [h0]
  exact zero_mem _

theorem exists_hom_near_of_graphs : ∀ (R σ₁ σ₂ Hh : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] [Finite σ₁] [Finite σ₂] [Finite Hh] (Z₁ Z₂ : Over (Sp R)) (I₁ : Ideal (MvPolynomial σ₁ R)) (I₂ : Ideal (MvPolynomial σ₂ R)) (M₁ : LB Z₁.left) (M₂ : LB Z₂.left) (th₁ : σ₁ → M₁.Sec) (th₂ : σ₂ → M₂.Sec) (p₁ : Hh → σ₁ → R) (p₂ : Hh → σ₂ → R) (Q : Polynomial ℚ) (d : ℕ) (G : ∀ (K : Type) [Field K] (x : R →+* K), (pullback Z₁.hom (spMap x) ⟶ Z₂.left) → Prop), ProjRep I₁ Z₁.hom M₁ th₁ → ProjRep I₂ Z₂.hom M₂ th₂ → IsProper Z₁.hom → IsProper Z₂.hom → Smooth Z₁.hom → (∀ (K : Type) [Field K] (x : R →+* K) φ, G K x φ → φ ≫ Z₂.hom = pullback.snd _ _ ≫ spMap x ∧ CutBy (graphIdeal (pullback.snd Z₁.hom (spMap x)) M₁ th₁ (pullback.fst _ _) M₂ th₂ φ) Q d (fun h i => x (p₁ h i.1 * p₂ h i.2))) → DenseP {q | ∃ (K : Type) (_ : Field K) (x : R →+* K) (φ : _), RingHom.ker x = q ∧ G K x φ} → ∀ (K₀ : Type) [Field K₀] (x₀ : R →+* K₀) φ₀, G K₀ x₀ φ₀ → ∃ (f : R) (F : pullback Z₁.hom (spMap (algebraMap R (Localization.Away f))) ⟶ Z₂.left), x₀ f ≠ 0 ∧ F ≫ Z₂.hom = pullback.fst _ _ ≫ Z₁.hom ∧ ∀ (K : Type) [Field K] (x : R →+* K) φ, G K x φ → ∀ io : pullback Z₁.hom (spMap x) ⟶ pullback Z₁.hom (spMap (algebraMap R (Localization.Away f))), io ≫ pullback.fst _ _ = pullback.fst _ _ → φ = io ≫ F := by
  intro R σ₁ σ₂ Hh _ _ _ _ _ _ Z₁ Z₂ I₁ I₂ M₁ M₂ th₁ th₂ p₁ p₂ Q d G h₁ h₂ hp₁ _ hs₁ hG hD K₀ _ x₀ φ₀ hG₀
  obtain ⟨f₁, hf₁, hproj, hmap⟩ := GlobalTheory.ZM.FormsFamily.exists_away_projective_vanIdeal R (σ₁ × σ₂) Hh (fun h i => p₁ h i.1 * p₂ h i.2) Q d _ hD (by
    rintro q ⟨K, _, x, φ, hq, hx⟩
    exact ⟨K, inferInstance, x, _, hq, (hG K x φ hx).2⟩) _ ⟨K₀, inferInstance, x₀, φ₀, rfl, hG₀⟩
  rw [RingHom.mem_ker] at hf₁
  set S := Localization.Away f₁
  set a := algebraMap R S with ha
  set J := vanIdeal d (fun h (i : σ₁ × σ₂) => a (p₁ h i.1 * p₂ h i.2)) with hJ
  have hJh : ∀ F ∈ J, ∀ e, MvPolynomial.homogeneousComponent e F ∈ J := homogeneousComponent_mem_vanIdeal d _
  obtain ⟨Y, sY, N, ty, -, hY, -, hflat⟩ := GlobalTheory.T.exists_projCoordRepresentation_homogeneousIdeal_flat S _ J d hJh
  replace hflat : Flat sY := hflat fun e he => by have := hproj e he; infer_instance
  have hprop : IsProper sY := (GlobalTheory.ZM.projRep_projective_ample S _ J (Over.mk sY) N ty hY).2.1
  have sq := IsPullback.of_hasPullback Z₁.hom Z₂.hom
  generalize pullback.fst Z₁.hom Z₂.hom = p at sq
  generalize pullback.snd Z₁.hom Z₂.hom = q at sq
  have hP := projRep_box p q th₁ th₂ sq h₁ h₂
  have lift : ∀ (K : Type) [Field K] (x : R →+* K), x f₁ ≠ 0 → ∃ x' : S →+* K, x'.comp a = x := fun K _ x hx =>
    ⟨IsLocalization.Away.lift f₁ (g := x) hx.isUnit, IsLocalization.Away.lift_comp _ _⟩
  have hmap' : ∀ (K : Type) [Field K] (x : R →+* K) (x' : S →+* K), x'.comp a = x →
      J.map (MvPolynomial.map x') = vanIdeal d (fun h (i : σ₁ × σ₂) => x (p₁ h i.1 * p₂ h i.2)) := by
    rintro K _ _ x' rfl
    exact hmap K x'

  have hIJ : ∀ e ≥ d, ∀ F : MvPolynomial (σ₁ × σ₂) R, F.IsHomogeneous e →
      F ∈ graphIdeal (p ≫ Z₁.hom) M₁ th₁ p M₂ th₂ q → F ∈ J.comap (MvPolynomial.map a) := by
    intro e he F hF hm
    refine mem_of_forall_map_mem J e (fun F hF => hJh F hF e) (hproj e he) _ (hF.map a) fun r hr => ?_
    obtain ⟨n, r₀, hr₀⟩ := IsLocalization.Away.surj f₁ r
    by_contra hno
    have h0 : r₀ * f₁ = 0 := by
      refine hD _ ?_
      rintro _ ⟨K, _, x, φ, rfl, hx⟩ -
      rw [RingHom.mem_ker, map_mul]
      by_contra hne
      obtain ⟨x', hx'⟩ := lift K x (right_ne_zero_of_mul hne)
      refine hno ⟨K, inferInstance, x', fun h => left_ne_zero_of_mul hne ?_, ?_⟩
      · rw [← hx', RingHom.comp_apply, ← hr₀, map_mul, h, zero_mul]
      · rw [MvPolynomial.map_map, hx', hmap' K x x' hx']
        exact (((hG K x φ hx).2 e he).2 _ (hF.map x)).1
          (map_mem_graphIdeal sq x _ _ φ pullback.condition (hG K x φ hx).1 hm)
    have h1 : r * a f₁ ^ (n + 1) = 0 := by
      rw [pow_succ, ← _root_.mul_assoc, hr₀, ← map_mul, h0, map_zero]
    exact hr (((IsLocalization.Away.algebraMap_isUnit f₁).pow (n + 1)).mul_left_eq_zero.1 h1)
  obtain ⟨g, hg, -, hc, -⟩ := GlobalTheory.T.exists_scheme_map_of_projective_coordinates R _ _ _ Y _ (sY ≫ spMap a) _ N _ ty hP hY.1 fun T _ β y v hy hv => by
    obtain ⟨β', hβ'⟩ : ∃ β' : S →+* T, y ≫ sY = spMap β' := ⟨(Spec.preimage (y ≫ sY)).hom, (Spec.map_preimage _).symm⟩
    have hβ : β'.comp a = β := by
      rw [← Category.assoc, hβ', spc] at hy
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective hy)
    obtain ⟨u, hu⟩ := hY.2.1 T β' y v hβ' hv
    refine ⟨u, eval₂_eq_zero_of_forms_le
      (GlobalTheory.ZM.ideals_homogeneous.2.1 R σ₁ σ₂ _ _ _ _ M₁ th₁ p M₂ th₂ q h₁.1 h₂.1) hIJ β v u fun F hF => ?_⟩
    have := hu _ hF
    rwa [MvPolynomial.eval₂_map, hβ] at this

  have fib : ∀ (K : Type) [Field K] (x : R →+* K) (x' : S →+* K), x'.comp a = x → ∀ φ, G K x φ →
      ∃ e : pullback Z₁.hom (spMap x) ⟶ Y, IsPullback e (pullback.snd _ _) sY (spMap x') ∧
        e ≫ g ≫ p = pullback.fst _ _ ∧ e ≫ g ≫ q = φ := by
    intro K _ x x' hx' φ hx
    refine fibre_graph h₁ h₂ sq a hY g hg (fun T _ y v => (hc T y v).1) x x' hx' _ _ φ
      (IsPullback.of_hasPullback _ _) (hG K x φ hx).1 fun T _ β v hv => ?_
    rw [hmap' K x x' hx']
    have hcut := (hG K x φ hx).2
    exact ⟨eval₂_eq_zero_of_forms_le (homogeneousComponent_mem_vanIdeal d _)
        (fun e he F hF h => ((hcut e he).2 F hF).2 h) β v hv,
      eval₂_eq_zero_of_forms_le (GlobalTheory.ZM.ideals_homogeneous.2.1 K σ₁ σ₂ _ _ _ _ M₁ th₁ _ M₂ th₂ φ h₁.1 h₂.1)
        (fun e he F hF h => ((hcut e he).2 F hF).1 h) β v hv⟩
  obtain ⟨ψ, hψ₁, hψ₂⟩ : ∃ ψ : Y ⟶ pullback Z₁.hom (spMap a), ψ ≫ pullback.fst _ _ = g ≫ p ∧
      ψ ≫ pullback.snd _ _ = sY := ⟨pullback.lift (g ≫ p) sY (by rw [Category.assoc, hg]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨x₀', hx₀'⟩ := lift K₀ x₀ hf₁
  obtain ⟨e₀, pb₀, he₀, -⟩ := fib K₀ x₀ x₀' hx₀' φ₀ hG₀
  have hψ : IsProper ψ := by
    have : IsProper (ψ ≫ pullback.snd _ _) := hψ₂ ▸ hprop
    exact IsProper.of_comp ψ (pullback.snd _ _)
  obtain ⟨f₂, hf₂, hiso⟩ := GlobalTheory.NearFibreIso.main S Y _ (pullback.snd Z₁.hom (spMap a)) ψ K₀ x₀' inferInstance inferInstance hψ
    (hψ₂ ▸ hflat) (by
      refine isIso_snd_of_fibre ψ _ _ e₀ (pullback.snd _ _) (hψ₂ ▸ pb₀) ?_
      refine IsPullback.of_right ?_ (by rw [Category.assoc, hψ₂, pb₀.w]) (IsPullback.of_hasPullback Z₁.hom (spMap a))
      rw [Category.assoc, hψ₁, he₀, spc, hx₀']
      exact IsPullback.of_hasPullback _ _)
  obtain ⟨n, r, hr⟩ := IsLocalization.Away.surj f₁ f₂
  set S' := Localization.Away (f₁ * r)
  have hu : IsUnit (algebraMap R S' f₁ * algebraMap R S' r) := by
    rw [← map_mul]; exact IsLocalization.Away.algebraMap_isUnit _
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : S →+* S', c₁.comp a = algebraMap R S' :=
    ⟨IsLocalization.Away.lift f₁ (isUnit_of_mul_isUnit_left hu), IsLocalization.Away.lift_comp _ _⟩
  have hu₂ : IsUnit (c₁ f₂) := by
    have := isUnit_of_mul_isUnit_right hu
    rw [← hc₁, RingHom.comp_apply, ← hr, map_mul] at this
    exact isUnit_of_mul_isUnit_left this
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : Localization.Away f₂ →+* S', c₂.comp (algebraMap S _) = c₁ :=
    ⟨IsLocalization.Away.lift f₂ hu₂, IsLocalization.Away.lift_comp _ _⟩
  obtain ⟨j, hj₁, hj₂⟩ : ∃ j : pullback Z₁.hom (spMap (algebraMap R S')) ⟶ pullback Z₁.hom (spMap a),
      j ≫ pullback.fst _ _ = pullback.fst _ _ ∧ j ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap c₁ :=
    ⟨pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap c₁)
      (by rw [Category.assoc, spc, hc₁, pullback.condition]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨u, hu₁⟩ : ∃ u : pullback Z₁.hom (spMap (algebraMap R S')) ⟶
      pullback (pullback.snd Z₁.hom (spMap a)) (spMap (algebraMap S (Localization.Away f₂))),
      u ≫ pullback.fst _ _ = j :=
    ⟨pullback.lift j (pullback.snd _ _ ≫ spMap c₂) (by rw [Category.assoc, spc, hc₂, hj₂]), pullback.lift_fst _ _ _⟩
  obtain ⟨t, ht₁, ht₂⟩ : ∃ t : pullback (pullback.snd Z₁.hom (spMap a)) (spMap (algebraMap S (Localization.Away f₂))) ⟶ Y,
      t ≫ ψ = pullback.fst _ _ ∧ ∀ (V : Scheme.{0}) (e : V ⟶ Y) (k : V ⟶ _), e ≫ ψ = k ≫ pullback.fst _ _ → e = k ≫ t := by
    refine ⟨inv (pullback.snd ψ (pullback.fst _ _)) ≫ pullback.fst _ _, ?_, fun V e k h => ?_⟩
    · rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]
    · rw [← pullback.lift_snd e k h, Category.assoc, IsIso.hom_inv_id_assoc, pullback.lift_fst]
  have hxr : x₀ r ≠ 0 := by
    rw [← hx₀', RingHom.comp_apply, ← hr, map_mul, map_pow]
    refine mul_ne_zero hf₂ (pow_ne_zero _ ?_)
    rwa [← hx₀'] at hf₁
  refine ⟨f₁ * r, u ≫ t ≫ g ≫ q, by rw [map_mul]; exact mul_ne_zero hf₁ hxr, ?_, fun K _ x φ hx io hio => ?_⟩
  · simp only [Category.assoc]
    rw [← sq.w, ← Category.assoc g, ← hψ₁, Category.assoc, reassoc_of% ht₁, reassoc_of% hu₁, reassoc_of% hj₁]
  · refine hom_ext_near _ _ fun w => ⟨_, 𝟙 _, inferInstance, ⟨w, rfl⟩, ?_⟩
    have hne := ne_zero_of_point x (f₁ * r) w (pullback.snd _ _) (io ≫ pullback.snd _ _)
      (by rw [Category.assoc, ← pullback.condition, ← pullback.condition, reassoc_of% hio])
    rw [map_mul] at hne
    obtain ⟨x', hx'⟩ := lift K x (left_ne_zero_of_mul hne)
    obtain ⟨e, -, he₁, he₂⟩ := fib K x x' hx' φ hx
    have : IsOpenImmersion (spMap a) := inferInstanceAs (IsOpenImmersion (spMap (algebraMap R (Localization.Away f₁))))
    have h3 := ht₂ _ e (io ≫ u) (by
      rw [← cancel_mono (pullback.fst Z₁.hom (spMap a))]
      simp only [Category.assoc]
      rw [hψ₁, he₁, reassoc_of% hu₁, hj₁, hio])
    rw [← he₂, h3]
    simp only [Category.assoc]

end GlobalTheory.ZM.LocalGraph
end
