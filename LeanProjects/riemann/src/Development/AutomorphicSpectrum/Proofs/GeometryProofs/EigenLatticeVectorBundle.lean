import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeEigenVectorBundle
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeVectorBundleOfSmooth
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackCorrespondence
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPfB
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.EigVb

section Bundle

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {V : Type} [AddCommGroup V] [Module Ω V]

theorem extends_act (M : LieModel G ξ V) (f : G ⟶ G) [IsMonHom f] (A : V →ₗ[Ω] V) (hA : M.IsDiffOf f A) (p : Cpt ξ)
    {e : V} {v : epsAt (R := X.presheaf.stalk p.1) (X.fromSpecStalk p.1) ⟶ G} (h : M.Extends p e v) :
    M.Extends p (A e) (v ≫ f) := by
  refine ⟨?_, ?_⟩
  · have h1 := h.1
    unfold IsTanAt at h1 ⊢
    rw [Over.comp_left, ← Category.assoc, h1, ← Over.comp_left, Hom.one_def, Category.assoc, IsMonHom.one_hom,
      ← Hom.one_def]
  · rw [hA e, Over.comp_left, h.2, Over.comp_left]
    exact Category.assoc _ _ _

theorem lat_stable (M : LieModel G ξ V) (f : G ⟶ G) [IsMonHom f] (A : V →ₗ[Ω] V) (hA : M.IsDiffOf f A) (p : Cpt ξ)
    {e : V} (he : e ∈ M.lat p) : A e ∈ M.lat p := by
  have : M.lat p ≤ (M.lat p).comap (A.restrictScalars (regAt ξ p)) := by
    refine Submodule.span_le.2 ?_
    rintro e ⟨v, hv⟩
    exact Submodule.subset_span ⟨_, extends_act M f A hA p hv⟩
  exact this he

theorem frame_at_of_smooth [IsCommMonObj G] (hs : Smooth G.hom) (M : LieModel G ξ V) (p : Cpt ξ) :
    ∃ U : X.Opens, p.1 ∈ U ∧ ∃ (g : ℕ) (Bs : Module.Basis (Fin g) Ω V), ∀ q : Cpt ξ, q.1 ∈ U →
      M.lat q = Submodule.span (regAt ξ q) (Set.range Bs) := by
  open LieVB in
  let s : X ⟶ G.left := (1 : Over.mk (𝟙 X) ⟶ G).left
  have hs1 : ∀ {T : Type} [CommRing T] (x : Spec (CommRingCat.of T) ⟶ X),
      (1 : Over.mk x ⟶ G).left = x ≫ s := by
    intro T _ x
    have := MonObj.comp_one (M := G) (Over.homMk x (by simp) : Over.mk x ⟶ Over.mk (𝟙 X))
    exact (congrArg (fun k : Over.mk x ⟶ G => k.left) this).symm
  obtain ⟨U, hU, W, hW, hx, e, hsm⟩ := Smooth.exists_isStandardSmooth G.hom (s p.1)
  letI : Algebra Γ(X, U) Γ(G.left, W) := (G.hom.appLE U W e).hom.toAlgebra
  haveI : Algebra.IsStandardSmooth Γ(X, U) Γ(G.left, W) := hsm
  haveI : Nonempty W := ⟨⟨s p.1, hx⟩⟩
  haveI : Nontrivial Γ(G.left, W) := inferInstance
  let c := Module.finBasis Γ(G.left, W) Ω[Γ(G.left, W)⁄Γ(X, U)]
  obtain ⟨d, w, hd⟩ := exists_isCoord c
  have hc : IsChart (A := Γ(X, U)) (B := Γ(G.left, W)) hW.fromSpec hU.fromSpec :=
    (IsAffineOpen.SpecMap_appLE_fromSpec G.hom hU hW e).symm
  have hpt : ∀ {T : Type} [CommRing T] (x : Spec (CommRingCat.of T) ⟶ X), Set.range x ⊆ (s ⁻¹ᵁ W : Set X) →
      ∃ ε : Γ(G.left, W) →+* T, IsUnitIn (B := Γ(G.left, W)) hW.fromSpec x ε := by
    intro T _ x hx
    have hr : Set.range (x ≫ s) ⊆ Set.range hW.fromSpec := by
      rw [hW.range_fromSpec]
      rintro _ ⟨y, rfl⟩
      exact hx ⟨y, rfl⟩
    refine ⟨(Spec.preimage (IsOpenImmersion.lift hW.fromSpec (x ≫ s) hr)).hom, ?_⟩
    change Spec.map (CommRingCat.ofHom _) ≫ _ = _
    rw [hs1, CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]
  have hst : ∀ q : Cpt ξ, q.1 ∈ s ⁻¹ᵁ W → Set.range (X.fromSpecStalk q.1) ⊆ (s ⁻¹ᵁ W : Set X) := by
    intro q hq
    rw [Scheme.range_fromSpecStalk]
    intro y hy
    exact Specializes.mem_open hy (s ⁻¹ᵁ W).isOpen hq
  have hbase : ∀ (q : Cpt ξ) (εq : Γ(G.left, W) →+* X.presheaf.stalk q.1),
      IsUnitIn (B := Γ(G.left, W)) (T := X.presheaf.stalk q.1) hW.fromSpec (X.fromSpecStalk q.1) εq →
      IsUnitIn (B := Γ(G.left, W)) hW.fromSpec ξ ((genMap ξ q).comp εq) :=
    fun q εq h => unit_base (genMap ξ q) (LieCarrier.genMap_fromSpecStalk q) h
  have hp : p.1 ∈ s ⁻¹ᵁ W := hx
  obtain ⟨εp, hεp⟩ := hpt (X.fromSpecStalk p.1) (hst p hp)
  obtain ⟨Bs, hB⟩ := lat_coord hc hd (hbase p εp hεp) M
  refine ⟨s ⁻¹ᵁ W, hp, _, Bs, fun q hq => ?_⟩
  obtain ⟨εq, hεq⟩ := hpt (X.fromSpecStalk q.1) (hst q hq)
  exact hB q εq hεq (spec_cancel hW.fromSpec ((hbase p εp hεp).trans (hbase q εq hεq).symm))

theorem lat_isVB_of_smooth [IsCommMonObj G] (hs : Smooth G.hom) (M : LieModel G ξ V) :
    M.lat.IsVB (Module.finrank Ω V) ⊤ := fun p _ => by
  obtain ⟨U, hU, g, Bs, hB⟩ := frame_at_of_smooth hs M p
  have hg : g = Module.finrank Ω V := by
    rw [Module.finrank_eq_card_basis Bs, Fintype.card_fin]
  subst hg
  exact ⟨U, hU, Bs, Bs.span_eq, fun q _ hq => ⟨Bs.linearIndependent, hB q hq⟩⟩

end Bundle

section Fibre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {U : Set (Xo.XF c)}

theorem gen_over (Z : CptOver Y U) : (Z.ξ₀ ≫ Y.j) ≫ Y.s = spMap (Z.inc.comp β) := by
  have h1 : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap β := by
    show (Y.jQ ≫ pullback.fst _ _) ≫ Y.s = _
    rw [Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]
  rw [Category.assoc, h1, ← Category.assoc, Z.over_inc]
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem inc_mem_regAt (Z : CptOver Y U) (hβ : Function.Injective β)
    (hfr : ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) (p : Cpt (Z.ξ₀ ≫ Y.j)) (hp : p ∈ Z.genFib) (x : c.F) :
    Z.inc x ∈ regAt (Z.ξ₀ ≫ Y.j) p := by
  let t : Spec (Y.X.presheaf.stalk p.1) ⟶ Spec (CommRingCat.of O) := Y.X.fromSpecStalk p.1 ≫ Y.s
  let θ : O →+* Y.X.presheaf.stalk p.1 := (Spec.preimage t).hom
  have ht : Spec.map (CommRingCat.ofHom θ) = t := by
    simp only [θ, CommRingCat.ofHom_hom, Spec.map_preimage]
  have hg : (genMap (Z.ξ₀ ≫ Y.j) p).comp θ = Z.inc.comp β := by
    refine LieVB.spec_cancel (𝟙 _) ?_
    rw [Category.comp_id, Category.comp_id, ← LieVB.spec_comp', ht]
    refine Eq.trans ?_ (gen_over Z)
    show _ ≫ Y.X.fromSpecStalk p.1 ≫ Y.s = _
    rw [← Category.assoc, LieCarrier.genMap_fromSpecStalk p]
  have hu : ∀ b : O, β b ≠ 0 → IsUnit (θ b) := by
    intro b hb
    by_contra hn
    have hm : θ b ∈ IsLocalRing.maximalIdeal (Y.X.presheaf.stalk p.1) := (IsLocalRing.mem_maximalIdeal _).2 hn
    obtain ⟨w, hw⟩ := hp
    have e1 : t (IsLocalRing.closedPoint _) = spMap β (pullback.snd Y.s (spMap β) w) := by
      show Y.s (Y.X.fromSpecStalk p.1 (IsLocalRing.closedPoint _)) = _
      rw [Scheme.fromSpecStalk_closedPoint, ← hw, ← Scheme.Hom.comp_apply, pullback.condition,
        Scheme.Hom.comp_apply]
    rw [← ht] at e1
    have e2 := congrArg (fun z : PrimeSpectrum O => z.asIdeal) e1
    have e3 : b ∈ (Spec.map (CommRingCat.ofHom θ) (IsLocalRing.closedPoint _)).asIdeal := hm
    have e4 : ∀ z : PrimeSpectrum c.F, z.asIdeal = ⊥ := fun z => Ideal.eq_bot_of_prime _
    simp only at e2
    rw [e2] at e3
    have e5 : β b ∈ (pullback.snd Y.s (spMap β) w).asIdeal := e3
    rw [e4 (pullback.snd Y.s (spMap β) w)] at e5
    exact hb e5
  obtain ⟨a, b, hb, hx⟩ := hfr x
  obtain ⟨u, hu'⟩ := hu b hb
  have h1 : genMap (Z.ξ₀ ≫ Y.j) p (θ b) = Z.inc (β b) := congrArg (fun f : O →+* Z.Ω => f b) hg
  have h2 : genMap (Z.ξ₀ ≫ Y.j) p (θ a) = Z.inc (β a) := congrArg (fun f : O →+* Z.Ω => f a) hg
  refine ⟨θ a * ↑u⁻¹, ?_⟩
  have h3 : genMap (Z.ξ₀ ≫ Y.j) p (θ b) * genMap (Z.ξ₀ ≫ Y.j) p ↑u⁻¹ = 1 := by
    rw [← map_mul, ← hu', Units.mul_inv, map_one]
  rw [map_mul, h2, ← hx, map_mul, ← h1, _root_.mul_assoc, h3, _root_.mul_one]

end Fibre

section Rank

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem epsMul_one {R : Type} [CommRing R] : Geo.Tor.epsMul (1 : R) = RingHom.id _ := by
  ext <;> simp [Geo.Tor.epsMul]

theorem spMap_ringHomId {R : Type} [CommRing R] : spMap (RingHom.id R) = 𝟙 _ := by
  show Spec.map (CommRingCat.ofHom (RingHom.id R)) = _
  rw [CommRingCat.ofHom_id, Spec.map_id]

def gfpModel {L : Type} [Field L] {x : Sp L ⟶ Xo.X} {n : ℕ}
    {xc : ∀ m : ℕ, Chart.sp (R₀ := L) (Chart.JetR L (Fin n) m) ⟶ (Over.pullback x).obj Xo.univ.t.G}
    (hx : Chart.IsUnivChart _ n xc) : LieModel Xo.univ.t.G x (Fin n → L) where
  pt cc := Formalism.L2.Pj.gfpW xc cc
  tan cc := (Formalism.L2.Pj.gfp_tan hx cc).2
  inj a b h := Formalism.L2.Pj.gfp_inj hx (congrArg (fun k => k.left) h)
  onto v hv := by
    obtain ⟨cc, h⟩ := Formalism.L2.Pj.gfp_exists hx v.left ⟨Over.w v, hv⟩
    exact ⟨cc, Over.OverMorphism.ext h.symm⟩
  add a b := by
    obtain ⟨u, hu, hp⟩ := (Formalism.L2.Pj.gfp_comb_iff hx ![a, b] ![1, 1] (a + b)).2 (by simp [Fin.sum_univ_two])
    have h0 : u 0 = Formalism.L2.Pj.gfpW xc a := Over.OverMorphism.ext ((hu 0).trans (by
      simp [epsMul_one, spMap_ringHomId, Formalism.L2.Pj.gfpW]))
    have h1 : u 1 = Formalism.L2.Pj.gfpW xc b := Over.OverMorphism.ext ((hu 1).trans (by
      simp [epsMul_one, spMap_ringHomId, Formalism.L2.Pj.gfpW]))
    have : (List.ofFn u).prod = Formalism.L2.Pj.gfpW xc a * Formalism.L2.Pj.gfpW xc b := by
      simp [List.ofFn_succ, h0, h1]
    rw [this] at hp
    exact Over.OverMorphism.ext hp.symm
  smul c e := by
    obtain ⟨u, hu, hp⟩ := (Formalism.L2.Pj.gfp_comb_iff hx ![e] ![c] (c • e)).2 (by simp)
    have : (List.ofFn u).prod = u 0 := by simp [List.ofFn_succ]
    rw [this, hu 0] at hp
    exact hp.symm

theorem exists_equiv {S : Scheme.{0}} {G : Over S} [GrpObj G] {R : Type} [CommRing R] {x : Sp R ⟶ S} {L L' : Type}
    [AddCommGroup L] [Module R L] [AddCommGroup L'] [Module R L'] (M : LieModel G x L) (M' : LieModel G x L') :
    ∃ ψ : L ≃ₗ[R] L', ∀ e, M'.pt (ψ e) = M.pt e := by
  choose F hF using fun e => M'.onto _ (M.tan e)
  let F' : L →ₗ[R] L' :=
    { toFun := F
      map_add' := fun a b => M'.inj (by rw [M'.add, hF, hF, hF, M.add])
      map_smul' := fun c a => M'.inj (Over.OverMorphism.ext (by
        rw [RingHom.id_apply, M'.smul, hF, hF, M.smul])) }
  refine ⟨LinearEquiv.ofBijective F' ⟨fun a b h => M.inj ?_, fun b => ?_⟩, hF⟩
  · rw [← hF, ← hF]; exact congrArg M'.pt h
  · obtain ⟨a, ha⟩ := M.onto _ (M'.tan b)
    exact ⟨a, M'.inj ((hF a).trans ha)⟩

theorem eig_transfer {S S' T : Scheme.{0}} {G' : Over S'} {G : Over S} {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (h : IsPullback φ G'.hom G.hom f) (a' : G' ⟶ G') (a : G ⟶ G) (ha : a'.left ≫ φ = φ ≫ a.left)
    (A B : T ⟶ G'.left) (hAB : A ≫ G'.hom = B ≫ G'.hom) :
    A ≫ a'.left = B ↔ (A ≫ φ) ≫ a.left = B ≫ φ := by
  constructor
  · rintro rfl
    rw [Category.assoc, Category.assoc, ha]
  · intro e
    refine h.hom_ext ?_ ?_
    · rw [Category.assoc, ha, ← Category.assoc, e]
    · rw [Category.assoc, Over.w a', hAB]

variable {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {U : Set (Xo.XF c)}

theorem finrank_eigSp (Z : CptOver Y U) (τ : E →+* ℂ) :
    Module.finrank Z.Ω (eigSp Z.ρ (Z.inc.comp (tauIn c τ))) = D.mult τ := by
  classical
  letI : Algebra c.F Z.Ω := Z.inc.toAlgebra
  let x : Sp Z.Ω ⟶ Xo.X := Z.ξ₀ ≫ pullback.fst _ _
  have hx0 : x ≫ Xo.s = Formalism.L2.Pj.sOf c Z.Ω := by
    show (Z.ξ₀ ≫ pullback.fst _ _) ≫ Xo.s = _
    rw [Category.assoc, pullback.condition, ← Category.assoc, Z.over_inc]
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  haveI hs : Smooth ((Over.pullback x).obj Xo.univ.t.G).hom := by
    have := Xo.univ.t.semi.smooth
    show Smooth (pullback.snd Xo.univ.t.G.hom x)
    infer_instance
  obtain ⟨n, xc, hx⟩ := Chart.univChartLoc ((Over.pullback x).obj Xo.univ.t.G)
  obtain ⟨M₂, e₂⟩ := (LieMove.models_correspond (x := Z.ξ₀) Y.m.cart Z.V).1 Z.M
  obtain ⟨M₃, e₃⟩ := (LieMove.models_correspond (x := Z.ξ₀) Y.m0.toSABMap.cart Z.V).2 M₂
  obtain ⟨ψ, hψ⟩ := exists_equiv M₃ (gfpModel hx)
  have hmem : ∀ e, e ∈ eigSp Z.ρ (Z.inc.comp (tauIn c τ)) ↔ ψ e ∈ Formalism.L2.Pj.gfpEig (c := c) hx τ := by
    intro e
    have hv : Formalism.L2.Pj.gfpVec x xc (ψ e) = (M₃.pt e).left := congrArg (fun k => k.left) (hψ e)
    have h0 := Formalism.L2.Pj.gfp_eig_iff (c := c) hx τ (ψ e)
    rw [hv] at h0
    refine Iff.trans ?_ h0
    show _ ↔ ∀ a : 𝓞 E, (M₃.pt e).left ≫ (Xo.univ.t.act.act a).left =
      spMap (Geo.Tor.epsMul (Z.inc (tauIn c τ a))) ≫ (M₃.pt e).left
    simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero]
    refine forall_congr' fun a => ?_
    have hAw : (M₂.pt e).left ≫ Y.oF.t.G.hom = spMap (algebraMap _ _) ≫ Z.ξ₀ := Over.w (M₂.pt e)
    have hAB : (M₂.pt e).left ≫ Y.oF.t.G.hom =
        (Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.epsMul (Z.inc (tauIn c τ a)))) ≫ (M₂.pt e).left) ≫ Y.oF.t.G.hom := by
      rw [Category.assoc, hAw, ← Category.assoc, LieMove.epsMul_comp_alg]
    have T1 := eig_transfer Y.m.cart.1 (Y.oF.t.act.act a) (Y.t.act.act a) (Y.m.act a) _ _ hAB
    have T2 := eig_transfer Y.m0.cart.1 (Y.oF.t.act.act a) (Xo.univ.t.act.act a) (Y.m0.act a) _ _ hAB
    have L1 : Z.ρ a e = (Z.inc.comp (tauIn c τ)) a • e ↔ (Z.M.pt e).left ≫ (Y.t.act.act a).left =
        Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.epsMul (Z.inc (tauIn c τ a)))) ≫ (Z.M.pt e).left := by
      constructor
      · intro h
        have h1 := Z.M.smul (Z.inc (tauIn c τ a)) e
        have h2 : Z.M.pt (Z.inc (tauIn c τ a) • e) = Z.M.pt e ≫ Y.t.act.act a := by
          rw [← Z.act a e]
          exact congrArg Z.M.pt h.symm
        rw [h2, Over.comp_left] at h1
        exact h1
      · intro h
        refine Z.M.inj (Over.OverMorphism.ext ?_)
        rw [Z.act a e, Over.comp_left]
        refine h.trans ?_
        exact (Z.M.smul (Z.inc (tauIn c τ a)) e).symm
    refine L1.trans ?_
    rw [← e₂ e, ← e₃ e]
    simp only [Category.assoc] at T1 T2 ⊢
    exact T1.symm.trans T2
  have hmap : (eigSp Z.ρ (Z.inc.comp (tauIn c τ))).map ψ.toLinearMap = Formalism.L2.Pj.gfpEig (c := c) hx τ := by
    ext y
    constructor
    · rintro ⟨e, he, rfl⟩
      exact (hmem e).1 he
    · intro hy
      exact ⟨ψ.symm y, (hmem _).2 (by simpa using hy), by simp⟩
  rw [← Formalism.L2.Pj.gfp_finrank hx0 hx τ, ← hmap, LinearEquiv.finrank_map_eq]

end Rank

section Indep

theorem linearIndependent_sigma {Ω V F : Type} [Field Ω] [CharZero Ω] [AddCommGroup V] [Module Ω V] [Field F]
    [NumberField F] (ρ : 𝓞 F →+* Module.End Ω V) {I : Type} [Fintype I] (φ : I → (F →+* Ω))
    (hφ : Function.Injective φ) {r : I → ℕ} (b : ∀ s, Fin (r s) → V) (hb : ∀ s, LinearIndependent Ω (b s))
    (hm : ∀ s i, b s i ∈ HT.eigSp ρ (φ s)) :
    LinearIndependent Ω (fun i : Σ s, Fin (r s) => b i.1 i.2) := by
  classical
  rw [Fintype.linearIndependent_iff]
  rintro g hg ⟨s, j⟩
  have spec := HT.ProjEig.eigProj_spec Ω V F ρ (φ s)
  have h1 := congrArg (HT.eigProj ρ (φ s)) hg
  rw [map_sum, map_zero, Fintype.sum_sigma] at h1
  have h2 : ∑ j, HT.eigProj ρ (φ s) (g ⟨s, j⟩ • b s j) = 0 := by
    rw [← h1]
    symm
    refine Finset.sum_eq_single s (fun t _ ht => Finset.sum_eq_zero fun j _ => ?_) (by simp)
    rw [map_smul, spec.2.2.1 (φ t) (hφ.ne ht) _ (hm t j), smul_zero]
  simp_rw [map_smul, spec.2.1 _ (hm s _)] at h2
  exact Fintype.linearIndependent_iff.1 (hb s) _ h2 j

end Indep

end GlobalTheory.CompanionTheory.Ar.Flat.EigVb

namespace GlobalTheory.CompanionTheory.Ar.Flat

open EigVb

theorem isVBOn_eig_genFib : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → τ (H.rt : E) = H.rt0 → (Z.eig τ).IsVBOn Z.genFib D.p (eigSp Z.ρ (Z.inc.comp (tauIn c τ))) ∧ (Z.eig (ComplexEmbedding.conjugate τ)).IsVBOn Z.genFib D.q (eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ)))) ∧ (∀ x ∈ Z.genFib, ∃ g : ℕ, ∃ b : Fin g → Z.V, Z.M.lat.IsFrameAt b x ∧ ∀ σ' : E →+* ℂ, ∃ S : Finset (Fin g), Z.eig σ' x = Submodule.span (regAt _ x) (b '' S)) ∧ Z.genFib.Nonempty := by
  rintro E _ _ _ H D l Xo c O _ β Y U Z τ ⟨hinj, -, hfr⟩ hτ
  classical
  haveI : CharZero Z.Ω := charZero_of_injective_ringHom Z.inc.injective
  let σ : (E →+* ℂ) → (𝓞 E →+* Z.Ω) := fun s => Z.inc.comp (tauIn c s)
  let φ : (E →+* ℂ) → (E →+* Z.Ω) := fun s => Z.inc.comp (Formalism.L2.Pj.embF c s)
  have hφ : Function.Injective φ := by
    intro s t h
    ext x
    have h1 := congrArg (fun m : E →+* Z.Ω => m x) h
    have h2 := Z.inc.injective h1
    exact congrArg (fun z : c.F => (z : ℂ)) h2
  have hσ : Function.Injective σ := by
    intro s t h
    refine hφ (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) ?_)
    exact h
  have hcard : Fintype.card (E →+* ℂ) = Module.finrank ℚ E := Embeddings.card E ℂ
  have hVB : Z.M.lat.IsVBOn Z.genFib (Module.finrank Z.Ω Z.V) ⊤ := fun p _ => by
    obtain ⟨W, h, b, hb, hf⟩ := lat_isVB_of_smooth Y.t.semi.smooth Z.M p (Set.mem_univ _)
    exact ⟨W, h, b, hb, fun q _ hq => hf q (Set.mem_univ _) hq⟩
  have hst : ∀ p ∈ Z.genFib, ∀ a, ∀ e ∈ Z.M.lat p, Z.ρ a e ∈ Z.M.lat p := fun p _ a e he => by
    haveI := Y.t.act.hom a
    exact lat_stable Z.M _ (Z.ρ a) (Z.act a) p he
  have hreg : ∀ p ∈ Z.genFib, ∀ s a, σ s a ∈ regAt (Z.ξ₀ ≫ Y.j) p :=
    fun p hp s a => inc_mem_regAt Z hinj hfr p hp (tauIn c s a)
  have hdisc : ∀ p ∈ Z.genFib, unitAt (Z.ξ₀ ≫ Y.j) p ((discr E : ℤ) : Z.Ω) := by
    intro p hp
    have hmem := inc_mem_regAt Z hinj hfr p hp
    have e : ((discr E : ℤ) : Z.Ω) = Z.inc ((discr E : ℤ) : c.F) := by simp
    have h0 : ((discr E : ℤ) : c.F) ≠ 0 := Int.cast_ne_zero.2 (discr_ne_zero E)
    refine ⟨by rw [e]; exact (map_ne_zero _).2 h0, by rw [e]; exact hmem _, ?_⟩
    rw [e, ← map_inv₀]
    exact hmem _
  obtain ⟨hV, hsum⟩ := EigSplit.isVBOn_eigSp Y.X Z.Ω (Z.ξ₀ ≫ Y.j) Z.V E Z.ρ Z.M.lat Z.genFib _ (E →+* ℂ) σ Z.gen hσ
    hcard hVB hst hreg hdisc
  have hne : ComplexEmbedding.conjugate τ (H.rt : E) ≠ H.rt0 := by
    rw [ComplexEmbedding.conjugate_coe_eq, hτ]
    intro h
    obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h
    have hsq := H.sqrt_neg_disc_sq
    rw [hr] at hsq
    have h1 : r ^ 2 = -(H.d : ℝ) := by exact_mod_cast hsq
    have hd : (0 : ℝ) < H.d := Nat.cast_pos.2 H.d_prime.pos
    nlinarith [sq_nonneg r]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := hV τ
    have hr : Module.finrank Z.Ω (eigSp Z.ρ (σ τ)) = D.p := (finrank_eigSp Z τ).trans (if_pos hτ)
    rw [hr] at h
    exact h
  · have h := hV (ComplexEmbedding.conjugate τ)
    have hr : Module.finrank Z.Ω (eigSp Z.ρ (σ (ComplexEmbedding.conjugate τ))) = D.q :=
      (finrank_eigSp Z _).trans (if_neg hne)
    rw [hr] at h
    exact h
  · intro x hx
    choose W hW b hb hfr' using fun s => hV s x hx
    have hfx : ∀ s, (Z.M.lat.inter (eigSp Z.ρ (σ s))).IsFrameAt (b s) x := fun s => hfr' s x hx (hW s)
    let e := Fintype.equivFin (Σ s, Fin (Module.finrank Z.Ω (eigSp Z.ρ (σ s))))
    let bb : Fin _ → Z.V := fun i => b (e.symm i).1 (e.symm i).2
    have hbe : ∀ s j, bb (e ⟨s, j⟩) = b s j := fun s j => by
      show b (e.symm (e ⟨s, j⟩)).1 (e.symm (e ⟨s, j⟩)).2 = _
      rw [e.symm_apply_apply]
    have hli : LinearIndependent Z.Ω bb := by
      have h1 := linearIndependent_sigma Z.ρ φ hφ b (fun s => (hfx s).1) (fun s i => by
        have h2 : b s i ∈ eigSp Z.ρ (σ s) := by
          rw [← hb s]
          exact Submodule.subset_span ⟨i, rfl⟩
        exact h2)
      exact h1.comp _ e.symm.injective
    have hlat : Z.M.lat x = Submodule.span (regAt _ x) (Set.range bb) := by
      rw [hsum x hx]
      apply le_antisymm
      · refine iSup_le fun s => ?_
        rw [(hfx s).2, Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        exact Submodule.subset_span ⟨e ⟨s, j⟩, hbe s j⟩
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        have h1 : bb i ∈ (Z.M.lat.inter (eigSp Z.ρ (σ (e.symm i).1))) x := by
          rw [(hfx _).2]
          exact Submodule.subset_span ⟨_, rfl⟩
        exact (le_iSup (fun s => (Z.M.lat.inter (eigSp Z.ρ (σ s))) x) (e.symm i).1) h1
    refine ⟨_, bb, ⟨hli, hlat⟩, fun σ' => ⟨Finset.univ.filter (fun i => (e.symm i).1 = σ'), ?_⟩⟩
    have h1 : Z.eig σ' x = Submodule.span (regAt _ x) (Set.range (b σ')) := (hfx σ').2
    rw [h1]
    congr 1
    ext v
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨e ⟨σ', j⟩, by simp, hbe σ' j⟩
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨⟨s, j⟩, rfl⟩ := e.surjective i
      have hs : s = σ' := by simpa using hi
      subst hs
      exact ⟨j, (hbe s j).symm⟩
  · refine ⟨⟨genPt (Z.ξ₀ ≫ Y.j), specializes_rfl⟩, ?_⟩
    refine ⟨Y.jQ (Z.ξ₀ (IsLocalRing.closedPoint Z.Ω)), ?_⟩
    exact ((Scheme.Hom.comp_apply Z.ξ₀ (Y.jQ ≫ pullback.fst _ _) _).trans
      (Scheme.Hom.comp_apply Y.jQ (pullback.fst _ _) _)).symm

end GlobalTheory.CompanionTheory.Ar.Flat
