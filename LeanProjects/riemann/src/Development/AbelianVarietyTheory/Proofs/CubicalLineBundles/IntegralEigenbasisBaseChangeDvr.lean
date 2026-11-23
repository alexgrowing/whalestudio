import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.LieFreePf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasisBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CommonEigenvectorsFlatBaseChange
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT.LieIntBC

open Matrix
open ReciprocityTheory.ChartRestriction.G.Chart (tvec tmap tvec_inj isTan_tvec univChartLoc tanBC_alg tvec_tmap fB IsUnivChart sp JetR)
open Formalism.L2.Pj.LieRel
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

theorem flat_of_inj {A B : Type} [CommRing A] [IsDomain A] [IsBezout A] [CommRing B] [IsDomain B] [Algebra A B]
    (hi : Function.Injective (algebraMap A B)) : Module.Flat A B := by
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  rintro x ⟨⟨a, ha⟩, hx⟩
  have hx' : algebraMap A B a * x = 0 := (Algebra.smul_def a x).symm.trans hx
  have ha' : algebraMap A B a ≠ 0 := fun h => nonZeroDivisors.ne_zero ha (hi (h.trans (map_zero _).symm))
  exact (mul_eq_zero.mp hx').resolve_left ha'

theorem eig_flat {V V' : Type} [CommRing V] [IsNoetherianRing V] [CommRing V'] [Algebra V V'] [Module.Flat V V']
    {n m : ℕ} {J : Type} (L : J → (Fin n → V) →ₗ[V] (Fin n → V)) (χ : J → V)
    (L' : J → (Fin n → V') →ₗ[V'] (Fin n → V'))
    (hL : ∀ a c, L' a (algebraMap V V' ∘ c) = algebraMap V V' ∘ L a c)
    (b : Fin m → Fin n → V) (hb : ∀ k a, L a (b k) = χ a • b k)
    (hbb : ∀ c, (∀ a, L a c = χ a • c) → ∃! r : Fin m → V, c = ∑ k, r k • b k)
    (w : Fin n → V') (hw : ∀ a, L' a w = algebraMap V V' (χ a) • w) :
    ∃! r : Fin m → V', w = ∑ k, r k • (algebraMap V V' ∘ b k) := by
  let M : J → Matrix (Fin n) (Fin n) V := fun a => Matrix.of fun j => L a (Pi.single j 1)
  have hM : ∀ a c, c ᵥ* M a = L a c := fun a c => by
    funext j
    rw [LinearMap.pi_apply_eq_sum_univ (L a) c]
    simp only [M, Matrix.vecMul, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.of_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    refine congrArg (fun q => c k * L a q j) ?_
    funext s
    simp [Pi.single_apply, eq_comm]
  have hM' : ∀ a c, c ᵥ* (M a).map (algebraMap V V') = L' a c := fun a c => by
    funext j
    rw [LinearMap.pi_apply_eq_sum_univ (L' a) c]
    simp only [M, Matrix.vecMul, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.of_apply,
      Matrix.map_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    refine (congrFun (hL a (Pi.single k 1)) j).symm.trans ?_
    refine congrArg (fun q => L' a q j) ?_
    funext s
    by_cases h : k = s <;> simp [Pi.single_apply, h, eq_comm]
  refine (GlobalTheory.commonEigenvectors_flat_baseChange V J n m M χ).1 V b (fun k a => (hM a _).trans (hb k a))
    (fun z hz => ?_) V' w (fun a => (hM' a w).trans (hw a))
  simp only [Algebra.algebraMap_self, RingHom.id_apply, RingHom.coe_id, Matrix.map_id] at hz ⊢
  exact hbb z fun a => (hM a z).symm.trans (hz a)

theorem univChart_iso {S : Type} [CommRing S] {G G' : Over (Spec (CommRingCat.of S))} [GrpObj G] [GrpObj G']
    (e : G' ≅ G) [IsMonHom e.hom] {n : ℕ}
    {x : ∀ m : ℕ, sp (R₀ := S) (JetR S (Fin n) m) ⟶ G} (hx : IsUnivChart G n x) :
    IsUnivChart G' n (fun m => x m ≫ e.inv) := by
  have one : ∀ T : Over (Spec (CommRingCat.of S)), (1 : T ⟶ G') ≫ e.hom = 1 := fun T =>
    map_one (IsMonHom.monoidHom e.hom T)
  have one' : ∀ T : Over (Spec (CommRingCat.of S)), (1 : T ⟶ G) ≫ e.inv = 1 := fun T => by
    rw [← one, Category.assoc, e.hom_inv_id, Category.comp_id]
  refine ⟨fun m => ?_, fun m => ?_, fun A _ _ aug m hm y hy => ?_⟩
  · rw [← Category.assoc, hx.1]
  · rw [← Category.assoc, hx.2.1, one']
  · have := hx.2.2 A aug m hm (y ≫ e.hom) (by rw [← Category.assoc, hy, one])
    simpa only [← Category.assoc, Iso.eq_comp_inv] using this

theorem exists_charts {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] {G₀ : Over (Sp R)} [GrpObj G₀]
    [Smooth G₀.hom] {G : Over (Sp S)} [GrpObj G] (f : R →+* S) {φ : G.left ⟶ G₀.left}
    (h : IsGrpPullback G G₀ (spMap f) φ) :
    ∃ (n : ℕ) (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G₀) (x' : ∀ m : ℕ, sp (R₀ := S) (JetR S (Fin n) m) ⟶ G),
      IsUnivChart G₀ n x ∧ IsUnivChart G n x' ∧ ∀ c : Fin n → R,
        (tvec (x := x') (f ∘ c)).left ≫ φ = spMap (Formalism.L2.Pj.dualMap f) ≫ (tvec (x := x) c).left := by
  let _ := f.toAlgebra
  obtain ⟨n, x, hx⟩ := univChartLoc G₀
  obtain ⟨x', hx', hc⟩ := tanBC_alg (R' := S) G₀ n x hx
  obtain ⟨e, he, heφ⟩ := grpPullback_iso h (isGrpPullback_pullback G₀ (fB R S))
  refine ⟨n, x, _, hx, univChart_iso e hx', fun c => ?_⟩
  have e1 : tvec (x := fun m => x' m ≫ e.inv) (f ∘ c) = tvec (x := x') (f ∘ c) ≫ e.inv := (Category.assoc _ _ _).symm
  rw [e1, ← heφ, ← Category.assoc, ← Over.comp_left, Category.assoc, e.inv_hom_id, Category.comp_id]
  exact hc c

theorem sp_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'')
    (g : R →+* R') : spMap f ≫ spMap g = spMap (f.comp g) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem dual_alg {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) :
    spMap (Formalism.L2.Pj.dualMap ψ) ≫ spMap (algebraMap S (DualNumber S)) =
      spMap (algebraMap T (DualNumber T)) ≫ spMap ψ := by
  rw [sp_comp, sp_comp]
  congr 1
  ext s <;> simp [Formalism.L2.Pj.dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dual_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : S →+* T) (g : R →+* S) :
    spMap (Formalism.L2.Pj.dualMap f) ≫ spMap (Formalism.L2.Pj.dualMap g) = spMap (Formalism.L2.Pj.dualMap (f.comp g)) := by
  rw [sp_comp]
  congr 1
  refine RingHom.ext fun s => ?_
  ext <;> simp [Formalism.L2.Pj.dualMap]

end GlobalTheory.LamT.LieIntBC

namespace GlobalTheory.LamT

open LieIntBC Formalism.L2.Pj.LieRel
open ReciprocityTheory.ChartRestriction.G.Chart (tvec tmap tvec_inj isTan_tvec tvec_tmap)

theorem lieInt_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (T T' : CDVR) (ψ : T.V →+* T'.V) (i : T.Fr →+* T'.Fr), (algebraMap T'.V T'.Fr).comp ψ = i.comp (algebraMap T.V T.Fr) → ∀ (x : Sp T.Fr ⟶ Xo.X) (x' : Sp T'.Fr ⟶ Xo.X) (G : PAT H (Sp T.V)) (G' : PAT H (Sp T'.V)) (t : SAB H (Sp T.Fr)) (t' : SAB H (Sp T'.Fr)) (m1 : SABMap t Xo.univ.t x) (m2 : SABMap t G.t (spMap (algebraMap T.V T.Fr))) (m1' : SABMap t' Xo.univ.t x') (m2' : SABMap t' G'.t (spMap (algebraMap T'.V T'.Fr))) (n : SABMap G'.t G.t (spMap ψ)) (n' : SABMap t' t (spMap i)), x' = spMap i ≫ x → m1'.φ = n'.φ ≫ m1.φ → m2'.φ ≫ n.φ = n'.φ ≫ m2.φ → ∀ (io : c.F →+* T.Fr) (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber T.Fr) ⟶ Xo.univ.t.G.left)), LieInt T io m1 m2 u → LieInt T' (i.comp io) m1' m2' (fun τ k => spMap (Formalism.L2.Pj.dualMap i) ≫ u τ k) := by
  intro E _ _ _ H Dw l Xo c T T' ψ i hψ x x' G G' t t' m1 m2 m1' m2' n n' hx h1 h2 io u hu
  obtain ⟨ub, ht, he, hb, hu⟩ := hu
  have := G.t.semi.smooth
  have : ∀ a, IsMonHom (G.t.act.act a) := G.t.act.hom
  have : ∀ a, IsMonHom (G'.t.act.act a) := G'.t.act.hom
  have hψ' : ∀ z, algebraMap T'.V T'.Fr (ψ z) = i (algebraMap T.V T.Fr z) := fun z => RingHom.congr_fun hψ z
  have hinj : Function.Injective ψ := fun a b hab =>
    IsFractionRing.injective T.V T.Fr (i.injective (by rw [← hψ', ← hψ', hab]))
  let _ := ψ.toAlgebra
  have : Module.Flat T.V T'.V := flat_of_inj hinj
  obtain ⟨N, xc, xc', hxc, hxc', hcomp⟩ := exists_charts ψ n.cart
  have hM : ∀ (a : 𝓞 E) (cc : Fin N → T.V),
      tmap hxc' (G'.t.act.act a) (ψ ∘ cc) = ψ ∘ tmap hxc (G.t.act.act a) cc := by
    intro a cc
    apply tvec_inj hxc'
    rw [tvec_tmap hxc']
    refine Over.OverMorphism.ext (n.cart.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    rw [hcomp, tvec_tmap hxc, Over.comp_left, Over.comp_left, Category.assoc, n.act, ← Category.assoc, hcomp,
      Category.assoc]
  choose χ hχ using fun τ a => int_val c T io τ a
  have hχ' : ∀ τ a, algebraMap T'.V T'.Fr (ψ (χ τ a)) = (i.comp io) (embK c τ a) := fun τ a => by
    rw [hψ', hχ]; rfl
  have eig : ∀ τ cc, IsEigV c io G.t τ (cvV (tvec (x := xc) cc)) ↔
      ∀ a, tmap hxc (G.t.act.act a) cc = χ τ a • cc := fun τ cc =>
    ⟨fun h a => (eigV_iff hxc _ cc _).1 (h a _ (hχ τ a)), fun h a z hz => by
      obtain rfl : z = χ τ a := IsFractionRing.injective T.V T.Fr (hz.trans (hχ τ a).symm)
      exact (eigV_iff hxc _ cc _).2 (h a)⟩
  have eig' : ∀ τ cc, IsEigV c (i.comp io) G'.t τ (cvV (tvec (x := xc') cc)) ↔
      ∀ a, tmap hxc' (G'.t.act.act a) cc = ψ (χ τ a) • cc := fun τ cc =>
    ⟨fun h a => (eigV_iff hxc' _ cc _).1 (h a _ (hχ' τ a)), fun h a z hz => by
      obtain rfl : z = ψ (χ τ a) := IsFractionRing.injective T'.V T'.Fr (hz.trans (hχ' τ a).symm)
      exact (eigV_iff hxc' _ cc _).2 (h a)⟩
  choose b hbe using fun τ k => tan_eq_cvV hxc (ht τ k)
  obtain rfl : ub = fun τ k => cvV (tvec (x := xc) (b τ k)) := funext fun τ => funext fun k => hbe τ k
  have hbe' : ∀ τ k a, tmap hxc (G.t.act.act a) (b τ k) = χ τ a • b τ k := fun τ k => (eig τ _).1 (he τ k)
  refine ⟨fun τ k => cvV (tvec (x := xc') (ψ ∘ b τ k)), fun τ k => isTan_cvV (isTan_tvec hxc' _),
    fun τ k => (eig' τ _).2 fun a => ?_, fun τ w hw hwe => ?_, fun τ k => ?_⟩
  · rw [hM, hbe']
    funext j
    simp
  · obtain ⟨cc, rfl⟩ := tan_eq_cvV hxc' hw
    simp only [comb_iff hxc']
    refine eig_flat (fun a => tmap hxc (G.t.act.act a)) (χ τ) (fun a => tmap hxc' (G'.t.act.act a)) hM (b τ)
      (hbe' τ) (fun z hz => ?_) cc ((eig' τ cc).1 hwe)
    have := hb τ _ (isTan_cvV (isTan_tvec hxc z)) ((eig τ z).2 hz)
    simpa only [comb_iff hxc] using this
  · obtain ⟨u', hu1, hu2⟩ := hu τ k
    have w0 : u' ≫ t.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
      have : Mono (spMap (algebraMap T.V T.Fr)) := by
        have : Epi (CommRingCat.ofHom (algebraMap T.V T.Fr)) :=
          IsLocalization.epi (nonZeroDivisors T.V) T.Fr
        exact inferInstanceAs (Mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)).op))
      rw [← cancel_mono (spMap (algebraMap T.V T.Fr)), Category.assoc, ← m2.cart.1.w, ← Category.assoc]
      erw [hu2]
      rw [Category.assoc, Over.w]
      exact dual_alg _
    have w1 : (spMap (Formalism.L2.Pj.dualMap i) ≫ u') ≫ t.G.hom =
        spMap (algebraMap T'.Fr (DualNumber T'.Fr)) ≫ spMap i := by
      rw [Category.assoc, w0, dual_alg]
    have l1 : n'.cart.1.lift _ _ w1 ≫ n'.φ = spMap (Formalism.L2.Pj.dualMap i) ≫ u' := n'.cart.1.lift_fst _ _ _
    have l2 := n'.cart.1.lift_snd _ _ w1
    refine ⟨n'.cart.1.lift _ _ w1, ?_, n.cart.1.hom_ext ?_ ?_⟩
    · rw [h1, ← Category.assoc, l1, Category.assoc, hu1]
    · change (_ ≫ m2'.φ) ≫ n.φ = (_ ≫ _) ≫ n.φ
      rw [Category.assoc, h2, ← Category.assoc, l1, Category.assoc, hu2, cvV_left, cvV_left, Category.assoc, hcomp,
        ← Category.assoc, ← Category.assoc, dual_comp, dual_comp, hψ]
    · rw [Category.assoc, m2'.cart.1.w, ← Category.assoc, l2, Category.assoc, Over.w]
      exact (dual_alg _).symm

end GlobalTheory.LamT
