import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsPullWedge
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmTypeLatticeComparisonStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentPointCmEigenFrameStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeGramLinearCombinationStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeFormOfIsHodgeGram
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeGramPullbackIff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WedgeLatticeGenerator
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GagaLineGeneratorEmbedding
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AlternatingMapSumSmulEqDetSmul
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermStalkClosedPointToBaseChange
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolAVPullbackOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HolomorphicUniformizationTangentUnimodularRiemann
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolUnifCompareIsogenyStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
open MonoidalCategory CartesianMonoidalCategory MonObj

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat.HodgeFr

theorem spec_dual_comp {A B B' C : Type} [CommRing A] [CommRing B] [CommRing B'] [CommRing C] (g : B →+* C)
    (f : A →+* B) (g' : B' →+* C) (f' : A →+* B') (h : ∀ a, g (f a) = g' (f' a)) :
    Spec.map (CommRingCat.ofHom (dualMap g)) ≫ Spec.map (CommRingCat.ofHom (dualMap f)) =
      Spec.map (CommRingCat.ofHom (dualMap g')) ≫ Spec.map (CommRingCat.ofHom (dualMap f')) := by
  rw [LieTangent.spec_comp, LieTangent.spec_comp]
  congr 2
  refine RingHom.ext fun a => ?_
  ext <;> simp [h]

theorem spec_dual_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : B →+* C) (f : A →+* B) :
    Spec.map (CommRingCat.ofHom (dualMap g)) ≫ Spec.map (CommRingCat.ofHom (dualMap f)) =
      Spec.map (CommRingCat.ofHom (dualMap (g.comp f))) := by
  rw [LieTangent.spec_comp]
  congr 2
  refine RingHom.ext fun a => ?_
  ext <;> simp

theorem val_of_comb {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {E : Type} [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) {z : Spec (CommRingCat.of ℂ) ⟶ X}
    (hc : genPt ξ ⤳ centre z) {n : ℕ} (b : Fin n → E) (vb : Fin n → (epsAt z ⟶ G)) (hb : ∀ k, M.ValAt z (b k) (vb k))
    (t : Fin n → X.presheaf.stalk (centre z)) :
    ∃ w, M.ValAt z (∑ k, genMap ξ ⟨centre z, hc⟩ (t k) • b k) w ∧
      IsComb (fun k => (Scheme.stalkClosedPointTo z).hom (t k)) vb w := by
  let u : Fin n → (epsAt z ⟶ G) := fun k => LieTangent.epsScale z ((Scheme.stalkClosedPointTo z).hom (t k)) ≫ vb k
  have hu : ∀ k, M.ValAt z (genMap ξ ⟨centre z, hc⟩ (t k) • b k) (u k) := fun k => (hb k).smul hc (t k)
  have key : ∀ (m : ℕ) (x : Fin m → E) (w : Fin m → (epsAt z ⟶ G)), (∀ k, M.ValAt z (x k) (w k)) →
      M.ValAt z (∑ k, x k) (List.ofFn w).prod := by
    intro m
    induction m with
    | zero => intro x w _; simpa using LieModel.valAt_zero M hc
    | succ m ih =>
      intro x w h
      rw [Fin.sum_univ_succ, List.ofFn_succ, List.prod_cons]
      exact (h 0).add (ih _ _ fun k => h k.succ)
  exact ⟨_, key n _ u hu, u, fun k => rfl, rfl⟩

theorem tie_val {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {U : Set (Xo.XF c)}
    {Z : CptOver Y U} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
    {y : (Σ k, J k) → Ω} {𝔐 : HodgeCpt Y S y} {i : Z.Ω →+* Ω} {j : Z.V →+ 𝔐.Li} (ht : CptIn.IsTie Z 𝔐 i j)
    {z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X} {x : Spec (CommRingCat.of ℂ) ⟶ Y.X} (hx : x = z ≫ 𝔐.f) {e : Z.V}
    {v' : epsAt x ⟶ Y.t.G} {w : epsAt z ⟶ 𝔐.t.G} (h1 : Z.M.ValAt x e v') (h2 : 𝔐.M.ValAt z (j e) w) :
    w.left ≫ 𝔐.m.φ = v'.left := by
  subst hx
  obtain ⟨hc1, vx₀, hvx₀, e1₀⟩ := h1
  obtain ⟨hc2, ve, hve, e2⟩ := h2
  have hD : Dominates 𝔐.ξ (Z.ξ₀ ≫ Y.j) 𝔐.f i := ht.1
  have hcart := 𝔐.m.cart
  have hc1' : genPt (Z.ξ₀ ≫ Y.j) ⤳ 𝔐.f (centre z) := hc1
  let vx : epsAt (Y.X.fromSpecStalk (𝔐.f (centre z))) ⟶ Y.t.G := vx₀
  have hvx : Z.M.Extends ⟨𝔐.f (centre z), hc1'⟩ e vx := hvx₀
  have e5 : ((Scheme.stalkClosedPointTo (z ≫ 𝔐.f)).hom : Y.X.presheaf.stalk (𝔐.f (centre z)) →+* ℂ) =
      (Scheme.stalkClosedPointTo z).hom.comp (𝔐.f.stalkMap (centre z)).hom :=
    congrArg (fun t => t.hom) (Scheme.stalkClosedPointTo_comp z 𝔐.f)
  have e1 : v'.left = Spec.map (CommRingCat.ofHom (dualMap
      ((Scheme.stalkClosedPointTo z).hom.comp (𝔐.f.stalkMap (centre z)).hom))) ≫ vx.left := by
    refine e1₀.trans ?_
    exact congrArg (fun g : Y.X.presheaf.stalk (𝔐.f (centre z)) →+* ℂ =>
      Spec.map (CommRingCat.ofHom (dualMap g)) ≫ vx.left) e5
  have hst : Spec.map (CommRingCat.ofHom (𝔐.f.stalkMap (centre z)).hom) ≫ Y.X.fromSpecStalk (𝔐.f (centre z)) =
      𝔐.X.fromSpecStalk (centre z) ≫ 𝔐.f := by
    simpa using Scheme.Hom.SpecMap_stalkMap_fromSpecStalk 𝔐.f (x := centre z)
  let A : epsAt (𝔐.X.fromSpecStalk (centre z) ≫ 𝔐.f) ⟶ Y.t.G := Over.homMk (ve.left ≫ 𝔐.m.φ) (by
    have h0 := Over.w ve
    change (ve.left ≫ 𝔐.m.φ) ≫ Y.t.G.hom = Spec.map _ ≫ 𝔐.X.fromSpecStalk (centre z) ≫ 𝔐.f
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (ve.left ≫ ·) hcart.1.w).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ 𝔐.f) h0).trans ?_
    exact Category.assoc _ _ _)
  let B : epsAt (𝔐.X.fromSpecStalk (centre z) ≫ 𝔐.f) ⟶ Y.t.G :=
    LieTangent.epsBase (𝔐.f.stalkMap (centre z)).hom hst ≫ vx
  have hA : IsTanAt Y.t.G _ A := by
    have h1 : _ ≫ ve.left = (1 : Over.mk (𝔐.X.fromSpecStalk (centre z)) ⟶ 𝔐.t.G).left := hve.1
    have h2 := congrArg (fun q => q.left) (map_one (pushHom hcart (Over.mk (𝔐.X.fromSpecStalk (centre z)))))
    change Spec.map _ ≫ ve.left ≫ 𝔐.m.φ = _
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ 𝔐.m.φ) h1).trans h2)
  have hB : IsTanAt Y.t.G _ B := LieTangent.isTanAt_base _ hst hvx.1
  have hAB : A = B := by
    refine LieTangent.tan_ext (𝔐.tie.gen.inj ⟨centre z, hc2⟩) hA hB ?_
    change _ ≫ ve.left ≫ 𝔐.m.φ = _ ≫ Spec.map _ ≫ vx.left
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ 𝔐.m.φ) hve.2.symm).trans ?_
    refine (ht.2.2.2 e).trans ?_
    refine (congrArg (_ ≫ ·) hvx.2).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine Eq.trans ?_ (Category.assoc _ _ _)
    exact congrArg (· ≫ vx.left) (spec_dual_comp i (genMap (Z.ξ₀ ≫ Y.j) ⟨𝔐.f (centre z), hc1'⟩)
      (genMap 𝔐.ξ ⟨centre z, hc2⟩) (𝔐.f.stalkMap (centre z)).hom
      fun s => (PullReg.stalkMap_comp_genMap hD ⟨centre z, hc2⟩ hc1' s).symm)
  have hAB' : ve.left ≫ 𝔐.m.φ = Spec.map (CommRingCat.ofHom (dualMap (𝔐.f.stalkMap (centre z)).hom)) ≫ vx.left :=
    congrArg (fun q => q.left) hAB
  refine (congrArg (· ≫ 𝔐.m.φ) e2).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) hAB').trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine Eq.trans ?_ e1.symm
  refine congrArg (· ≫ vx.left) ?_
  exact spec_dual_comp' _ _

theorem exists_gram : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → ∀ (x : Sp ℂ ⟶ S) (n : ℕ) (v : Fin n → (epsAt x ⟶ t.G)), (∀ i, IsTanAt t.G x (v i)) → ∃ Γ : Matrix (Fin n) (Fin n) ℂ, IsHodgeGram t.G t.PP.L x v Γ := by
  intro E _ _ _ H S t hp hA hK x n v hv
  obtain ⟨Q, ψ, -, hQ, hQL, -⟩ := GlobalTheory.exists_polAV_pullback_of_isLocalRing E H S t hp hA hK ℂ x
  obtain ⟨rig, hrig⟩ := Q.rigid
  obtain ⟨u, Hm, χ, -, hAH, -, d₁, -⟩ := GlobalTheory.thetaUnifAV_all Q rig hrig
  have hl : ∀ a, ∃ t' : epsR ℂ ⟶ Q.A, t'.left ≫ ψ = (v a).left ∧ IsTangent t' := by
    intro a
    have sq : (v a).left ≫ t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x := Over.w (v a)
    let t' : epsR ℂ ⟶ Q.A := Over.homMk (hQ.1.lift _ _ sq) (hQ.1.lift_snd _ _ _)
    have h1 : t'.left ≫ ψ = (v a).left := hQ.1.lift_fst _ _ _
    refine ⟨t', h1, (ReciprocityTheory.ChartRestriction.G.Chart.tan_push hQ t').2 ?_⟩
    rw [h1]
    exact hv a
  choose t' h1 h2 using hl
  choose W hW _ using fun a => d₁ (t' a) (h2 a)
  exact ⟨Matrix.of fun a b => Real.pi * hermForm Hm (W a) (W b), Q, ψ, t', u, Hm, χ, W, hQ, hQL.symm, hAH,
    fun a => ⟨h1 a, hW a⟩, fun _ _ => rfl⟩

theorem gram_eq : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (x : Sp ℂ ⟶ S) (n : ℕ) (v : Fin n → (epsAt x ⟶ G)) (Γ Γ' : Matrix (Fin n) (Fin n) ℂ), L.IsLB → (∀ i, IsTanAt G x (v i)) → IsHodgeGram G L x v Γ → (∀ p q, HodgeIP G L x (v p) (v q) (Γ' p q)) → Γ' = Γ.transpose := by
  intro S G _ L x n v Γ Γ' hL hv hG hIP
  obtain ⟨Q, ψ, v', u, Hm, χ, W, hp, hiso, hAH, hvW, hΓ⟩ := hG
  have hM := pull_isLB hL ψ
  obtain ⟨w, hw⟩ := LBIso.symm hiso
  obtain ⟨ht₁, ht₂, -⟩ := GlobalTheory.AnyUnif.tangent_and_unimodular GlobalTheory.thetaUnifAV_all Q u
  have htan : ∀ a, IsTangent (v' a) := fun a =>
    (ReciprocityTheory.ChartRestriction.G.Chart.tan_push hp (v' a)).2 (by rw [(hvW a).1]; exact hv a)
  ext p q
  obtain ⟨-, -, -, A, _, φ, g, u', Hm', χ', a', b', a, b, h1, h2, h3, h4, h5, h6, e⟩ :=
    hodgeInnerProduct_iff_hodgeForm.1 (hIP p q)
  have key := GlobalTheory.T.hol_unif_compare_isogeny S G L x Q.A A ψ φ Q.g g (GlobalTheory.TorsionTauCompare.transport Q.isLB hM hw u) u' Hm Hm' χ χ'
    hL Q.isAb hp h1 ht₁ ht₂ (GlobalTheory.TorsionTauCompare.isAH_transport Q.isLB hM hw u hAH) h2 (v' q) (v' p) a' b' (W q) (W p) a b
    (htan q) (htan p) (h3.trans (hvW q).1.symm) (h4.trans (hvW p).1.symm) (hvW q).2 (hvW p).2 h5 h6
  rw [e, key, Matrix.transpose_apply, hΓ]

theorem frame_change : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') (E F : Type) [AddCommGroup E] [Module Ω E] [AddCommGroup F] [Module Ω' F] (j : E →+ F) (L : Lat ξ E) (V : Lat ξ' F) (p' : Cpt ξ') (h : genPt ξ ⤳ f p'.1) (n : ℕ) (b : Fin n → E) (bp : Fin n → F), Dominates ξ' ξ f i → IsCptGen ξ' → IsExtOver i j → L.IsFrameAt b ⟨f p'.1, h⟩ → V p' = L.pull ξ' f j p' → V.IsFrameAt bp p' → ∃ T S : Matrix (Fin n) (Fin n) (X'.presheaf.stalk p'.1), T * S = 1 ∧ (∀ a, j (b a) = ∑ k, genMap ξ' p' (T a k) • bp k) ∧ ∀ k, bp k = ∑ a, genMap ξ' p' (S k a) • j (b a) := by
  intro X X' Ω Ω' _ _ ξ ξ' f i E F _ _ _ _ j L V p' h n b bp hD hξ hj hb hV hbp
  have hreg : ∀ c ∈ regAt ξ ⟨f p'.1, h⟩, i c ∈ regAt ξ' p' := by
    rintro _ ⟨s, rfl⟩
    exact ⟨_, PullReg.stalkMap_comp_genMap hD p' h s⟩
  have hle : V p' = Submodule.span (regAt ξ' p') (Set.range fun a => j (b a)) := by
    rw [hV]
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨h₁, e, he, rfl⟩
      have he' : e ∈ L ⟨f p'.1, h⟩ := he
      rw [hb.2] at he'
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 he'
      rw [map_sum]
      refine Submodule.sum_mem _ fun k _ => ?_
      have e1 : j (c k • b k) = (⟨i (c k), hreg _ (c k).2⟩ : regAt ξ' p') • j (b k) := hj.1 (c k : Ω) (b k)
      rw [e1]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    · rintro _ ⟨a, rfl⟩
      refine Submodule.subset_span ⟨h, b a, ?_, rfl⟩
      rw [hb.2]
      exact Submodule.subset_span ⟨a, rfl⟩
  have hjb := hj.2 n b hb.1
  have hT : ∀ a, ∃ t : Fin n → X'.presheaf.stalk p'.1, j (b a) = ∑ k, genMap ξ' p' (t k) • bp k := by
    intro a
    have h1 : j (b a) ∈ V p' := by
      rw [hle]
      exact Submodule.subset_span ⟨a, rfl⟩
    rw [hbp.2] at h1
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h1
    choose t ht using fun k => (c k).2
    refine ⟨t, ?_⟩
    rw [← hc]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ht k]
    rfl
  have hS : ∀ k, ∃ t : Fin n → X'.presheaf.stalk p'.1, bp k = ∑ a, genMap ξ' p' (t a) • j (b a) := by
    intro k
    have h1 : bp k ∈ V p' := by
      rw [hbp.2]
      exact Submodule.subset_span ⟨k, rfl⟩
    rw [hle] at h1
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h1
    choose t ht using fun k => (c k).2
    refine ⟨t, ?_⟩
    rw [← hc]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ht k]
    rfl
  choose T hT using hT
  choose S hS using hS
  refine ⟨Matrix.of T, Matrix.of S, ?_, hT, hS⟩
  have h1 : ∀ a, j (b a) = ∑ c, genMap ξ' p' ((Matrix.of T * Matrix.of S) a c) • j (b c) := by
    intro a
    calc j (b a) = ∑ k, genMap ξ' p' (T a k) • ∑ c, genMap ξ' p' (S k c) • j (b c) := by
          rw [hT a]
          exact Finset.sum_congr rfl fun k _ => by rw [← hS k]
      _ = ∑ c, ∑ k, (genMap ξ' p' (T a k) * genMap ξ' p' (S k c)) • j (b c) := by
          simp only [Finset.smul_sum, smul_smul]
          exact Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [Matrix.mul_apply, map_sum, Finset.sum_smul]
          simp only [map_mul, Matrix.of_apply]
  ext a c
  have h2 : ∑ c, genMap ξ' p' ((1 : Matrix (Fin n) (Fin n) _) a c) • j (b c) = j (b a) := by
    simp [Matrix.one_apply, ite_smul]
  have h3 : ∑ c, (genMap ξ' p' ((Matrix.of T * Matrix.of S) a c) - genMap ξ' p' ((1 : Matrix (Fin n) (Fin n) _) a c)) • j (b c) = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [← h1, h2, sub_self]
  have h4 := Fintype.linearIndependent_iff.1 hjb _ h3 c
  exact hξ.inj p' (sub_eq_zero.1 h4)

theorem val_const' {X : Scheme.{0}} {Ω : Type} [Field Ω] {O : Type} [CommRing O] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (g : X ⟶ Sp O) {σ₀ : O →+* Ω} (hs : ξ ≫ g = spMap σ₀) {σ : O →+* ℂ} (z : Spec (CommRingCat.of ℂ) ⟶ X)
    (hz : z ≫ g = spMap σ) (h : genPt ξ ⤳ centre z) (c : O) : ValAt ξ z (σ₀ c) (σ c) := by
  refine ⟨h, GagaRat.cst g (centre z) c, ?_, ?_⟩
  · have hg : genPt (ξ ≫ g) ⤳ g (centre z) := h.map g.continuous
    rw [GagaRat.cst, GagaRat.genMap_stalkMap' ξ g ⟨centre z, h⟩ hg]
    have e : ((Sp O).presheaf.stalkSpecializes hg).hom (GagaRat.cgerm (g (centre z)) c) =
        GagaRat.cgerm (genPt (ξ ≫ g)) c :=
      congrArg (fun t => t.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom c))
        (TopCat.Presheaf.germ_stalkSpecializes (Sp O).presheaf (U := ⊤) trivial hg)
    show (Scheme.stalkClosedPointTo (ξ ≫ g)).hom (((Sp O).presheaf.stalkSpecializes hg).hom (GagaRat.cgerm (g (centre z)) c)) = _
    rw [e]
    exact GagaRat.closedPointTo_cgerm (ξ ≫ g) σ₀ hs c
  · have e := congrArg (fun t => t.hom (GagaRat.cgerm (g (centre z)) c)) (Scheme.stalkClosedPointTo_comp z g)
    exact e.symm.trans (GagaRat.closedPointTo_cgerm (z ≫ g) σ hz c)

theorem exists_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (U : Set (Xo.XF c)) (Z : CptOver Y U) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (i : Z.Ω →+* Ω) (j : Z.V →+ 𝔐.Li) (s : c.F →+* ℂ) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), genPt 𝔐.ξ ⤳ centre z → CptIn.IsTie Z 𝔐 i j → 𝔐.Interior z → (∀ a : c.F, ValAt 𝔐.ξ z (𝔐.cst a) (s a)) → ∃ y₀ : Sp ℂ ⟶ Xo.XF c, z ≫ 𝔐.f = y₀ ≫ Y.j ∧ Set.range y₀ ⊆ U ∧ y₀ ≫ pullback.snd _ _ = spMap s ∧ ∃ h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y₀ ≫ Y.j), (⟨_, h⟩ : Cpt (Z.ξ₀ ≫ Y.j)) ∈ Z.genFib := by

  intro E _ _ _ H D l Xo c _ Y U Z S Ω _ K _ J y 𝔐 i j s z hc ht hint hcst
  have hD : Dominates 𝔐.ξ (Z.ξ₀ ≫ Y.j) 𝔐.f i := ht.1
  have hz₀ : z ≫ 𝔐.f ≫ Y.s = spMap (s.comp (algebraMap (𝓞 c.F) c.F)) := by
    have hp : z ≫ 𝔐.f ≫ Y.s = spMap (Spec.preimage (z ≫ 𝔐.f ≫ Y.s)).hom := by
      unfold spMap
      rw [CommRingCat.ofHom_hom, Spec.map_preimage]
    have hv := val_const' (𝔐.f ≫ Y.s) 𝔐.cst_over z hp hc
    have e : (Spec.preimage (z ≫ 𝔐.f ≫ Y.s)).hom = s.comp (algebraMap (𝓞 c.F) c.F) :=
      RingHom.ext fun a => CxVal.unique (hv a) (hcst _)
    rw [hp, e]
  have hsq : (z ≫ 𝔐.f) ≫ Y.s = spMap s ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [Category.assoc, hz₀]
    unfold spMap
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let w := pullback.lift (z ≫ 𝔐.f) (spMap s) hsq
  have hw1 : w ≫ pullback.fst _ _ = z ≫ 𝔐.f := pullback.lift_fst _ _ _
  have hw2 : w ≫ pullback.snd _ _ = spMap s := pullback.lift_snd _ _ _
  have hab : 𝔐.f (centre z) ∈ abLocus Y.t.G := (abLocus_pullback abLocusOne Y.t.semi 𝔐.m.cart.1 (centre z)).2 hint
  have hrange : Set.range w ⊆ Set.range Y.jQ := by
    rintro _ ⟨p, rfl⟩
    rw [← Y.ab_gen]
    have hp : p = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
    subst hp
    have e : (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) (w (IsLocalRing.closedPoint ℂ)) = 𝔐.f (centre z) :=
      congrArg (fun t : Spec (CommRingCat.of ℂ) ⟶ Y.X => t (IsLocalRing.closedPoint ℂ)) hw1
    show _ ∈ abLocus Y.t.G
    rw [e]
    exact hab
  haveI := Y.jQ_open
  let y₀ : Sp ℂ ⟶ Xo.XF c := IsOpenImmersion.lift Y.jQ w hrange
  have hy : y₀ ≫ Y.jQ = w := IsOpenImmersion.lift_fac _ _ _
  have hj : y₀ ≫ Y.j = z ≫ 𝔐.f := by
    show y₀ ≫ Y.jQ ≫ pullback.fst _ _ = _
    rw [← Category.assoc, hy, hw1]
  have hs : y₀ ≫ pullback.snd _ _ = spMap s := by
    rw [← Y.jQ_over, ← Category.assoc, hy, hw2]
  have hcen : centre (y₀ ≫ Y.j) = 𝔐.f (centre z) := by rw [hj]; rfl
  have h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y₀ ≫ Y.j) := by
    rw [hcen, ← hD.map_genPt]
    exact hc.map 𝔐.f.continuous
  refine ⟨y₀, hj.symm, ?_, hs, h, ?_⟩
  · rintro _ ⟨p, rfl⟩
    have hp : p = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
    subst hp
    refine (Z.closure _).2 ?_
    haveI : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
      IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F)) (S := c.F)
    haveI : IsPreimmersion Y.j := by
      show IsPreimmersion (Y.jQ ≫ pullback.fst _ _)
      infer_instance
    have hind : Topology.IsInducing Y.j := Y.j.isEmbedding.isInducing
    exact hind.specializes_iff.1 h
  · exact ⟨Y.jQ (y₀ (IsLocalRing.closedPoint ℂ)), rfl⟩

theorem frame_gram {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {U : Set (Xo.XF c)}
    {Z : CptOver Y U} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
    {y : (Σ k, J k) → Ω} {𝔐 : HodgeCpt Y S y} {i : Z.Ω →+* Ω} {j : Z.V →+ 𝔐.Li} (ht : CptIn.IsTie Z 𝔐 i j)
    {z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X} (hc : genPt 𝔐.ξ ⤳ centre z) {y₀ : Sp ℂ ⟶ Xo.XF c}
    (hz : z ≫ 𝔐.f = y₀ ≫ Y.j) (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ 𝔐.f (centre z)) {L : Lat (Z.ξ₀ ≫ Y.j) Z.V} {V : Lat 𝔐.ξ 𝔐.Li} {n : ℕ}
    {b : Fin n → Z.V} (hb : L.IsFrameAt b ⟨𝔐.f (centre z), h⟩)
    (hV : V ⟨centre z, hc⟩ = L.pull 𝔐.ξ 𝔐.f j ⟨centre z, hc⟩) {v : Vecs y₀ n} (hv : Rep.IsValFam Z y₀ b v)
    (htan : ∀ k, IsTanAt Xo.univ.t.G (under y₀) (v k)) {bp : Fin n → 𝔐.Li} (hbp : V.IsFrameAt bp ⟨centre z, hc⟩)
    {Γ : Matrix (Fin n) (Fin n) ℂ} (hΓ : 𝔐.M.GramAt 𝔐.t.PP.L z bp Γ) :
    ∃ (d : Ω) (r : ℂ) (Γ₀ : Matrix (Fin n) (Fin n) ℂ), r ≠ 0 ∧ ValAt 𝔐.ξ z d r ∧
      exteriorPower.ιMulti Ω n (fun k => j (b k)) = d • exteriorPower.ιMulti Ω n bp ∧
      IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L (under y₀) v Γ₀ ∧ ‖Γ₀.det‖ = ‖r‖ ^ 2 * ‖Γ.det‖ := by
  have hξ := 𝔐.tie.gen
  obtain ⟨T, T', hTT, hT, hT'⟩ := frame_change _ _ _ _ _ _ 𝔐.f i _ _ j L V ⟨centre z, hc⟩ h n b bp ht.1 hξ ht.2.2.1 hb hV hbp
  set gm := genMap 𝔐.ξ ⟨centre z, hc⟩ with hgm
  let ρ : 𝔐.X.presheaf.stalk (centre z) →+* ℂ := (Scheme.stalkClosedPointTo z).hom
  obtain ⟨vb, hvb, hIP⟩ := hΓ

  have hw : ∀ a, ∃ w, 𝔐.M.ValAt z (j (b a)) w := fun a => by
    obtain ⟨w, h1, -⟩ := val_of_comb 𝔐.M hc bp vb hvb (T a)
    exact ⟨w, (hT a).symm ▸ h1⟩
  choose w hw using hw
  have hcomb : ∀ k, IsComb (fun a => ρ (T' k a)) w (vb k) := fun k => by
    obtain ⟨w', h1, h2⟩ := val_of_comb 𝔐.M hc (fun a => j (b a)) w hw (T' k)
    rw [← hT' k] at h1
    rwa [LieModel.ValAt.unique hξ (hvb k) h1]
  have htan' : ∀ k, IsTanAt 𝔐.t.G z (vb k) := fun k => (hvb k).isTanAt

  obtain ⟨Γ₀, hΓ₀⟩ := exists_gram E H _ Xo.univ.t Xo.univ.proper Xo.univ.ample Xo.univ.ktriv (under y₀) n v htan
  have hfam : ∀ a, ∃ (u : epsAt y₀ ⟶ Y.oF.t.G) (v' : epsAt (y₀ ≫ Y.j) ⟶ Y.t.G),
      (u.left ≫ Y.m0.toSABMap.φ = (v a).left) ∧ u.left ≫ Y.m.φ = v'.left ∧ (w a).left ≫ 𝔐.m.φ = v'.left := by
    intro a
    obtain ⟨v', h1, u, hu1, hu2, hu3⟩ := hv a
    exact ⟨Over.homMk u hu1, v', hu2, hu3, tie_val ht hz.symm h1 (hw a)⟩
  choose u v' hu1 hu2 hu3 using hfam
  have hG1 : IsHodgeGram Y.oF.t.G Y.oF.t.PP.L y₀ u Γ₀ :=
    (hodgeGram_iff_of_sabMap E H _ _ _ _ _ Y.m0.toSABMap y₀ (under y₀) n u v Γ₀ rfl hu1).2 hΓ₀
  have hG2 : IsHodgeGram Y.t.G Y.t.PP.L (y₀ ≫ Y.j) v' Γ₀ :=
    (hodgeGram_iff_of_sabMap E H _ _ _ _ _ Y.m y₀ (y₀ ≫ Y.j) n u v' Γ₀ rfl hu2).1 hG1
  have hG3 : IsHodgeGram 𝔐.t.G 𝔐.t.PP.L z w Γ₀ :=
    (hodgeGram_iff_of_sabMap E H _ _ _ _ _ 𝔐.m z (y₀ ≫ Y.j) n w v' Γ₀ hz.symm hu3).2 hG2
  let A : Matrix (Fin n) (Fin n) ℂ := ρ.mapMatrix T'
  have hG4 : IsHodgeGram 𝔐.t.G 𝔐.t.PP.L z vb (A * Γ₀ * A.conjTranspose) :=
    GlobalTheory.T.hodge_gram_linear_combination _ _ _ z n n w vb Γ₀ A (fun k => (hw k).isTanAt) hG3 hcomb
  have hEq : Γ = (A * Γ₀ * A.conjTranspose).transpose :=
    gram_eq _ _ _ z n vb _ Γ 𝔐.t.PP.isLB htan' hG4 hIP
  have hdet : T.det * T'.det = 1 := by rw [← Matrix.det_mul, hTT, Matrix.det_one]
  have hAd : A.det = ρ T'.det := (RingHom.map_det ρ T').symm
  have hr1 : ρ T.det * A.det = 1 := by rw [hAd, ← map_mul, hdet, map_one]
  have hr0 : ρ T.det ≠ 0 := left_ne_zero_of_mul_eq_one hr1
  refine ⟨gm T.det, ρ T.det, Γ₀, hr0, ⟨hc, T.det, rfl, rfl⟩, ?_, hΓ₀, ?_⟩
  · have e := GlobalTheory.alternating_map_sum_smul_eq_det_smul (exteriorPower.ιMulti Ω n (M := 𝔐.Li)) (gm.mapMatrix T) bp
    have e2 : (fun k => j (b k)) = fun a => ∑ k, (gm.mapMatrix T) a k • bp k := funext hT
    rw [e2, e, RingHom.map_det]
  · have hn : ‖Γ.det‖ = ‖A.det‖ ^ 2 * ‖Γ₀.det‖ := by
      rw [hEq, Matrix.det_transpose, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, norm_mul, norm_mul, norm_star]
      ring
    have hn1 : ‖ρ T.det‖ * ‖A.det‖ = 1 := by rw [← norm_mul, hr1, norm_one]
    rw [hn, ← _root_.mul_assoc, ← mul_pow, hn1, one_pow, _root_.one_mul]

theorem val_pull₀ {X X' : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {f : X' ⟶ X} {i : Ω →+* Ω'} (hD : Dominates ξ' ξ f i)
    (z : Spec (CommRingCat.of ℂ) ⟶ X') (h' : genPt ξ' ⤳ centre z) {a : Ω} {r : ℂ}
    (hv : ValAt ξ (z ≫ f) a r) : ValAt ξ' z (i a) r := by
  obtain ⟨h, s, rfl, rfl⟩ := hv
  exact ⟨h', (f.stalkMap (centre z)).hom s, PullReg.stalkMap_comp_genMap hD ⟨centre z, h'⟩ h s,
    (congrArg (fun t => t.hom s) (Scheme.stalkClosedPointTo_comp z f)).symm⟩

theorem mem_genFibre {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (z : Spec (CommRingCat.of ℂ) ⟶ X) (hc : genPt ξ ⤳ centre z) : (⟨centre z, hc⟩ : Cpt ξ) ∈ genFibre ℤ ξ := by
  intro o ho
  have hx : (Scheme.stalkClosedPointTo z).hom (o : X.presheaf.stalk (centre z)) ≠ 0 := by
    intro h0
    have e := (map_intCast (Scheme.stalkClosedPointTo z).hom o).symm.trans h0
    exact ho (by exact_mod_cast e)
  obtain ⟨x, hxo⟩ := CxVal.isUnit _ hx
  have e : genMap ξ ⟨centre z, hc⟩ x.val = algebraMap ℤ Ω o := by rw [hxo, map_intCast]; simp
  have hu : IsUnit (algebraMap ℤ Ω o) := e ▸ (x.isUnit.map (genMap ξ ⟨centre z, hc⟩))
  refine ⟨hu.ne_zero, ⟨x.val, e⟩, ⟨x⁻¹.val, ?_⟩⟩
  rw [← e, ← map_units_inv]

theorem coeff_of_span {Ω W : Type} [Field Ω] [AddCommGroup W] [Module Ω W] {R : Subring Ω} {e a : W} {c : Ω}
    (hc : c ≠ 0) (h : Submodule.span R {c • a} = Submodule.span R {e}) : ∃ α₀ : Ω, a = α₀ • e := by
  have h1 : c • a ∈ Submodule.span R {e} := h ▸ Submodule.mem_span_singleton_self _
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 h1
  refine ⟨c⁻¹ * r, ?_⟩
  rw [← smul_smul]
  change a = c⁻¹ • (r • e)
  rw [hr, smul_smul, inv_mul_cancel₀ hc, _root_.one_smul]

theorem hodge_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (U : Set (Xo.XF c)) (Z : CptOver Y U) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (τ : CMType H) (i : Z.Ω →+* Ω) (j : Z.V →+ 𝔐.Li) (a : ⋀[Z.Ω]^D.p Z.V) (b : ⋀[Z.Ω]^D.q Z.V) (a' : ⋀[Ω]^D.p 𝔐.Li) (b' : ⋀[Ω]^D.q 𝔐.Li) (φ : FrameFn Xo c) (s : c.F →+* ℂ) (t₀ : ℝ) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (hc : genPt 𝔐.ξ ⤳ centre z) (bp : Fin D.p → 𝔐.Li) (bq : Fin D.q → 𝔐.Li) (Γ : Matrix (Fin D.p) (Fin D.p) ℂ) (Δ : Matrix (Fin D.q) (Fin D.q) ℂ) (α κ : Ω) (u : ℂ), CptIn.IsTie Z 𝔐 i j → IsLineFn U τ.1 φ → IsLineGenOn (Z.eig τ.1) (Z.eig (ComplexEmbedding.conjugate τ.1)) D.p D.q a b Z.genFib → Represents Y U τ.1 Z.M a b φ → HasInfNorm U τ.1 φ s t₀ → CptIn.IsPullWedge i j a a' → CptIn.IsPullWedge i j b b' → 𝔐.Interior z → (∀ a : c.F, ValAt 𝔐.ξ z (𝔐.cst a) (s a)) → (𝔐.V (.inl τ)).IsFrameAt bp ⟨centre z, hc⟩ → (𝔐.V (.inr τ)).IsFrameAt bq ⟨centre z, hc⟩ → 𝔐.M.GramAt 𝔐.t.PP.L z bp Γ → 𝔐.M.GramAt 𝔐.t.PP.L z bq Δ → Γ.PosDef → Δ.PosDef → a' = α • exteriorPower.ιMulti Ω _ bp → b' = κ • exteriorPower.ιMulti Ω _ bq → ValAt 𝔐.ξ z (α / κ) u → Real.log ‖u‖ + (Real.log ‖Γ.det‖ - Real.log ‖Δ.det‖) / 2 = t₀ := by
  intro E _ _ _ H D l Xo c _ Y U Z S Ω _ K _ J _ y 𝔐 τ i j a b a' b' φ s t₀ z hc bp bq Γ Δ α κ u ht hl hg hr hn ha'
    hb' hint hcst hfp hfq hΓ hΔ hΓp hΔp hap hbq hu
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) ∧ IsNoetherianRing (𝓞 c.F) ∧
      ∀ x : c.F, ∃ a b : 𝓞 c.F, algebraMap (𝓞 c.F) c.F b ≠ 0 ∧ x * algebraMap (𝓞 c.F) c.F b = algebraMap (𝓞 c.F) c.F a := by
    refine ⟨IsFractionRing.injective (𝓞 c.F) c.F, inferInstance, fun x => ?_⟩
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 c.F) x
    have hq0 : algebraMap (𝓞 c.F) c.F q ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
    exact ⟨p, q, hq0, div_mul_cancel₀ _ hq0⟩
  obtain ⟨y₀, hz, hU, hs, h, hT⟩ := exists_point E H D l Xo c Y U Z S Ω K J y 𝔐 i j s z hc ht hint hcst
  have hτ : τ.1 (H.rt : E) = H.rt0 := τ.2
  obtain ⟨hv1, hv2, -⟩ := GlobalTheory.T.eigen_lattice_vector_bundle E H D l Xo c _ _ Y U Z τ.1 hβ hτ
  obtain ⟨W₁, hW₁, b₁, -, hb₁⟩ := hv1 _ hT
  have hb₁x := hb₁ _ hT hW₁
  obtain ⟨W₂, hW₂, b₂, -, hb₂⟩ := hv2 _ hT
  have hb₂x := hb₂ _ hT hW₂
  obtain ⟨v, hvv, hve⟩ := GlobalTheory.T.component_point_cm_eigen_frame E H D l Xo c _ _ Y U Z τ.1 hβ hτ ℂ s y₀ hs hU h τ.1 D.p b₁ hb₁x
  obtain ⟨w, hwv, hwe⟩ := GlobalTheory.T.component_point_cm_eigen_frame E H D l Xo c _ _ Y U Z τ.1 hβ hτ ℂ s y₀ hs hU h
    (ComplexEmbedding.conjugate τ.1) D.q b₂ hb₂x
  have hfr : IsFramed U τ.1 s y₀ v w := ⟨hs, hU, hve, hwe⟩

  obtain ⟨-, -, hgen⟩ := hg
  obtain ⟨A₁, B₁, hA₁, hB₁, hw1, hw2, -⟩ := hgen _ hT
  obtain ⟨α₀, ha₀⟩ := coeff_of_span hA₁ (hw1.symm.trans (WedgeFrame.wedge_eq_span_ιMulti _ _ _ _ _ _ _ _ hb₁x).1)
  obtain ⟨κ₀, hb₀⟩ := coeff_of_span hB₁ (hw2.symm.trans (WedgeFrame.wedge_eq_span_ιMulti _ _ _ _ _ _ _ _ hb₂x).1)
  have hRep := hr ℂ s y₀ v w b₁ b₂ α₀ κ₀ hfr ha₀ hb₀ hvv hwv

  obtain ⟨-, hst1, hst2⟩ := GlobalTheory.T.cm_type_lattice_comparison E H D l Xo c Y U Z S Ω K J y 𝔐 τ i j ht ⟨centre z, hc⟩ (mem_genFibre _ z hc)
  have hcen : centre (y₀ ≫ Y.j) = 𝔐.f (centre z) := by rw [← hz]; rfl
  have h' : genPt (Z.ξ₀ ≫ Y.j) ⤳ 𝔐.f (centre z) := hcen ▸ h
  have hpt : (⟨centre (y₀ ≫ Y.j), h⟩ : Cpt (Z.ξ₀ ≫ Y.j)) = ⟨𝔐.f (centre z), h'⟩ := Subtype.ext hcen
  rw [hpt] at hb₁x hb₂x
  obtain ⟨d₁, r₁, Γ₀, hr₁, hd₁, hι₁, hΓ₀, hN₁⟩ :=
    frame_gram ht hc hz h' hb₁x hst1 hvv (fun k => (hve.1 k).1) hfp hΓ
  obtain ⟨d₂, r₂, Δ₀, hr₂, hd₂, hι₂, hΔ₀, hN₂⟩ :=
    frame_gram ht hc hz h' hb₂x hst2 hwv (fun k => (hwe.1 k).1) hfq hΔ

  have hne₁ := (WedgeFrame.wedge_eq_span_ιMulti _ _ _ _ _ _ _ _ hfp).2
  have hne₂ := (WedgeFrame.wedge_eq_span_ιMulti _ _ _ _ _ _ _ _ hfq).2
  have eα : α = i α₀ * d₁ := by
    have e := (ha' b₁ α₀ ha₀).symm.trans hap
    rw [hι₁, smul_smul] at e
    exact (smul_left_injective Ω hne₁ e).symm
  have eκ : κ = i κ₀ * d₂ := by
    have e := (hb' b₂ κ₀ hb₀).symm.trans hbq
    rw [hι₂, smul_smul] at e
    exact (smul_left_injective Ω hne₂ e).symm
  rw [← hz] at hRep
  have hRep' := val_pull₀ ht.1 z hc hRep
  have hval := CxVal.mul (CxVal.mul hRep' hd₁) (CxVal.inv hd₂ hr₂)
  have hαk : α / κ = i (α₀ / κ₀) * d₁ * d₂⁻¹ := by
    rw [eα, eκ, map_div₀]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  rw [← hαk] at hval
  have hu' := CxVal.unique hu hval
  have hφ0 := hl.ne ℂ s y₀ v w hfr
  have hnorm := hn y₀ v w Γ₀ Δ₀ hfr hΓ₀ hΔ₀
  have hΓ0 : ‖Γ.det‖ ≠ 0 := norm_ne_zero_iff.2 hΓp.det_pos.ne'
  have hΔ0 : ‖Δ.det‖ ≠ 0 := norm_ne_zero_iff.2 hΔp.det_pos.ne'
  have h1 : ‖r₁‖ ≠ 0 := norm_ne_zero_iff.2 hr₁
  have h2 : ‖r₂‖ ≠ 0 := norm_ne_zero_iff.2 hr₂
  have h3 : ‖φ ℂ y₀ v w‖ ≠ 0 := norm_ne_zero_iff.2 hφ0
  rw [hN₁, hN₂, Real.log_mul (pow_ne_zero 2 h1) hΓ0, Real.log_mul (pow_ne_zero 2 h2) hΔ0, Real.log_pow, Real.log_pow] at hnorm
  rw [hu', norm_mul, norm_mul, norm_inv, Real.log_mul (mul_ne_zero h3 h1) (inv_ne_zero h2), Real.log_mul h3 h1, Real.log_inv]
  push_cast at hnorm
  linarith

end GlobalTheory.CompanionTheory.Ar.Flat.HodgeFr
