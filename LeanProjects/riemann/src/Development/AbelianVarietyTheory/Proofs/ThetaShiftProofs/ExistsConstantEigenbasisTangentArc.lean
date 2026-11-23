import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueConstantTangentVectorsAlongArc
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LieImgIffIsLieCombStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantLieBasisArcGroup
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantLieBasisArcGroupStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CommonEigenvectorsFlatBaseChange
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisEigen
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsIsComplEigenSubOfValuationRing
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullbackPullbackMap

noncomputable section

namespace GlobalTheory.ConstBasis

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Serre GlobalTheory.EigenSplit
open scoped CategoryTheory.Obj TensorProduct

section Extension

variable {O : Type} [CommRing O] {k : Type} [Field k]

theorem map_surjective {G B : Over (Sp k)} [GrpObj G] [GrpObj B] [IsCommMonObj G] [IsCommMonObj B]
    (a : OAct O G) (b : OAct O B) (q : G ⟶ B) [IsMonHom q] [Smooth q.left] :
    Function.Surjective (Lie.map a b q) := by
  intro v
  let π : CommRingCat.of (DualNumber k) ⟶ CommRingCat.of k :=
    CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom
  have hπ : Function.Surjective π := fun x => ⟨TrivSqZeroExt.inl x, rfl⟩
  have hn : IsNilpotent (RingHom.ker π.hom) := ⟨2, by
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    have hx' : x.fst = 0 := hx
    have hy' : y.fst = 0 := hy
    rw [Ideal.mem_bot]
    ext <;> simp [hx', hy']⟩
  have h0 : η[G].left ≫ q.left = Spec.map π ≫ v.hom.left :=
    (congrArg (·.left) (IsMonHom.one_hom q)).trans v.isTangent.symm
  obtain ⟨U, V, hU, hV, hVU, -, hxV⟩ :=
    exists_isAffineOpen_pair q.left (η[G].left (IsLocalRing.closedPoint k)) (O := ⊤) trivial
  obtain ⟨x, hx, hq⟩ := exists_lift_of_smooth_of_isAffineOpen q.left hU hV hVU π v.hom.left η[G].left h0
    (range_subset_opens_of_isLocalRing _ (by
      have : IsLocalHom π.hom := .of_surjective _ hπ
      have e : q.left (η[G].left (IsLocalRing.closedPoint k)) =
        v.hom.left (Spec.map π (IsLocalRing.closedPoint k)) := congr($h0 (IsLocalRing.closedPoint k))
      rw [← Spec_closedPoint (f := π), ← e]
      exact hVU hxV))
    (range_subset_opens_of_isLocalRing _ hxV) (by
      intro R S _ _ _ _ _ _ p hp φ
      have hs : Function.Surjective p := fun c => (hπ c).imp fun b hb => (hp b).trans hb
      have hk : IsNilpotent (RingHom.ker p.toRingHom) := by
        convert hn using 1
        exact Ideal.ext fun b => Eq.congr_left (hp b)
      exact ⟨Algebra.FormallySmooth.liftOfSurjective φ p hs hk,
        Algebra.FormallySmooth.comp_liftOfSurjective φ p hs hk⟩)
  exact ⟨Lie.mk a (Over.homMk x (by rw [← Over.w q, reassoc_of% hq]; exact Over.w v.hom)) hx,
    Lie.ext (Over.OverMorphism.ext hq)⟩

theorem lieMult_add {S : Scheme.{0}} {K G B : Over S} [GrpObj K] [GrpObj G] [GrpObj B] [IsCommMonObj K]
    [IsCommMonObj G] [IsCommMonObj B] {aK : OAct O K} {aG : OAct O G} {aB : OAct O B} {i : K ⟶ G} {q : G ⟶ B}
    (hi : IsLinearHom aK aG i) (hq : IsLinearHom aG aB q) (hk : IsPullback i (toUnit K) q η[B]) [Smooth q.left]
    (t : Sp k ⟶ S) {J : Type} {σ : J → O →+* k} (hσ : IsSplitting σ) (j : J) {m n : ℕ}
    (hm : LieMult aK t (σ j) m) (hn : LieMult aB t (σ j) n) : LieMult aG t (σ j) (n + m) := by
  have := hi.isMonHom
  have := hq.isMonHom
  have : Smooth ((Over.pullback t).map q).left :=
    MorphismProperty.of_isPullback (TorusExtBaseChange.isPullback_pullback_map t q) ‹_›
  have hk' : IsPullback ((Over.pullback t).map i) (toUnit _) ((Over.pullback t).map q)
      η[(Over.pullback t).obj B] :=
    (hk.map (Over.pullback t)).of_iso (Iso.refl _) (Iso.refl _)
      (Functor.Monoidal.εIso (Over.pullback t)).symm (Iso.refl _) (by simp) (toUnit_unique _ _) (by simp)
      (by rw [Functor.obj.η_def]; simp)
  rw [Lie.lieMult_iff_finrank (isLinearPullback_pullback _ t)] at hm hn ⊢
  have he : ∀ {X : Over (Sp k)} [GrpObj X] [IsCommMonObj X] (a : OAct O X),
      Lie.eig a (σ j) = eigenSub (Module.toModuleEnd k (Lie a)) (σ j) := fun a =>
    Submodule.ext fun v => by rw [mem_eigenSub]; rfl
  rw [he] at hm hn ⊢
  have eq : ∀ {X Y : Over S} [GrpObj X] [GrpObj Y] [IsCommMonObj X] [IsCommMonObj Y] {a : OAct O X} {b : OAct O Y}
      {f : X ⟶ Y} [IsMonHom f], IsLinearHom a b f →
      IsEquivariant (Module.toModuleEnd k (Lie (a.pullback t X))) (Module.toModuleEnd k (Lie (b.pullback t Y)))
        (Lie.map _ _ ((Over.pullback t).map f)) := fun hf x v =>
    Lie.map_act_smul ⟨inferInstance, fun c => by
      exact ((Over.pullback t).map_comp _ _).symm.trans
        ((congrArg _ (hf.comm c)).trans ((Over.pullback t).map_comp _ _))⟩ x v
  obtain ⟨h₁, h₂⟩ := Lie.map_kernel (a := aG.pullback t G) (b := aB.pullback t B) (c := aK.pullback t K) hk'
  have e₁ := (eq hi).eigenMap_injective (σ j) h₁
  have e₂ := IsEquivariant.eigenMap_exact hσ (eq hi) (eq hq) j h₂
  have e₃ := IsEquivariant.eigenMap_surjective hσ (eq hq) j (map_surjective _ _ _)
  have := hm.1
  have := hn.1
  have fin := Module.Finite.of_exact e₂ e₃
  refine ⟨fin, ?_⟩
  rw [← LinearMap.finrank_range_add_finrank_ker ((eq hq).eigenMap (σ j)), LinearMap.range_eq_top.2 e₃,
    finrank_top, e₂.linearMap_ker_eq, LinearMap.finrank_range_of_inj e₁, hm.2, hn.2]

end Extension

section Torus

theorem nonempty_basis_eigenHom {O k X : Type} [CommRing O] [IsDomain O] [Field k] [AddCommGroup X] [Module O X]
    [Module.Finite O X] (τ : O →+* k) (hτ : Function.Injective τ) :
    Nonempty (Module.Basis (Fin (Module.finrank O X)) k (Diag.eigenHom X τ)) := by
  let : Algebra O k := τ.toAlgebra
  have : FaithfulSMul O k := (faithfulSMul_iff_algebraMap_injective _ _).mpr hτ
  let e : (X →ₗ[O] k) ≃ₗ[k] Diag.eigenHom X τ :=
    { toFun := fun f => ⟨f.toAddMonoidHom, fun a x => f.map_smul a x⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun f => ⟨f.1.toAddHom, fun a x => f.2 a x⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e' := LinearMap.liftBaseChangeEquiv (R := O) (M := X) (N := k) k
  have := Module.Finite.equiv (e'.symm ≪≫ₗ e)
  refine ⟨Module.finBasisOfFinrankEq _ _ ?_⟩
  rw [← (e'.symm ≪≫ₗ e).finrank_eq, ← (TensorProduct.isBaseChange O X k).finrank_eq]
  exact Subspace.dual_finrank_eq

theorem eq_diagMap {S : Scheme.{0}} {X : Type} [AddCommGroup X] (u : X →+ X) {t : splitTorus S X ⟶ splitTorus S X}
    (ht : Out.TorusEndOf X u t) : t = Diag.diagMap S u := by
  refine (SplitTorus.pointsEquiv _ X).injective (AddMonoidHom.ext fun x => Additive.toMul.injective (Units.ext ?_))
  rw [SplitTorus.pointsEquiv_apply, SplitTorus.pointsEquiv_apply, Diag.diagMap_chi, ← SplitTorus.charUnit_val (u x),
    ← ht x]
  exact (SplitTorus.res_pullU_charUnit t x _).symm

end Torus

section Level

open ReciprocityTheory.ChartRestriction.G.Out

theorem lieMult_level {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {P : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D P G)
    {O : Type} [CommRing O] [IsDomain O] [StarRing O] [Module O D.toPre.X] {oD : D.OAct O} {oP : P.OAct O}
    {aG : OAct O G} (hl : U.OLinear O oD oP aG.toRingAct) {k : Type} [Field k] (φ : R →+* k)
    (hφ : ∀ x ∈ I, φ x = 0) {J : Type} {σ : J → O →+* k} (hσ : IsSplitting σ) (j : J)
    (hj : Function.Injective (σ j)) {n : ℕ} (hn : LieMult (ofRingAct oD.onB.toRingAct) (spMap φ) (σ j) n) :
    LieMult aG (spMap φ) (σ j) (n + Module.finrank O D.toPre.X) := by
  let φ₀ : R ⧸ I ^ (0 + 1) →+* k := Ideal.Quotient.lift _ φ (by simpa using hφ)
  have e : spMap φ₀ ≫ thick R I 0 = spMap φ := by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    rfl
  have pb : ∀ {X : Over (Sp R)} [GrpObj X] [IsCommMonObj X] (a : OAct O X) (m : ℕ),
      LieMult (a.pullback (thick R I 0) X) (spMap φ₀) (σ j) m ↔ LieMult a (spMap φ) (σ j) m := fun a m => by
    rw [← e]
    exact LiePull.lieMult_pull O _ _ _ _ _ _ _ _ (isLinearPullback_pullback a _).1 (isLinearPullback_pullback a _).2
      k _ _ _
  rw [← pb] at hn ⊢
  let g := U.gt 0
  have := g.q_hom
  have := g.i_hom
  have := g.q_flat
  have := g.q_surj
  have := g.q_affine
  have := (H1.torus_dim (Sp (R ⧸ I ^ (0 + 1))) D.toPre.X).smooth
  have : Smooth g.q.left := by
    refine MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      ((H1.torsor_pullback g.i g.q g.isKernel).map (Over.forget _)).flip
      ⟨⟨‹_›, ‹_›⟩, inferInstanceAs (QuasiCompact g.q.left)⟩ ?_
    exact smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) this
  have : Module.Finite O D.toPre.X := .of_restrictScalars_finite ℤ _ _
  have hb := nonempty_basis_eigenHom (X := D.toPre.X) ((σ j).comp (starRingEnd O))
    (hj.comp star_injective)
  have he : Diag.eigenHom D.toPre.X ((σ j).comp (starRingEnd O)) =
      @Diag.eigenHom O _ D.toPre.X _ (Module.compHom _ (starRingEnd O)) k _ (σ j) :=
    Submodule.ext fun c => ⟨fun h a x => (h (star a) x).trans (congrArg (fun b => σ j b * c x) (star_star a)), fun h a x =>
      (congrArg (fun b => c (b • x)) (star_star a)).symm.trans (h (star a) x)⟩
  rw [he, ← @Diag.lieMult_iff _ _ _ (spMap φ₀) _ _ _ _ (Module.compHom _ (starRingEnd O))] at hb
  refine lieMult_add (i := g.i) (q := g.q) ⟨inferInstance, fun a => ?_⟩ ⟨inferInstance, hl.q_lin 0⟩ g.isKernel
    _ hσ j hb hn
  obtain ⟨t, ht, hi⟩ := hl.i_lin 0 a
  obtain rfl := eq_diagMap (DistribSMul.toAddMonoidHom D.toPre.X (star a)) ht
  exact hi.symm

end Level

section Coordinates

open GlobalTheory.LieEigen Matrix
open ReciprocityTheory.ChartRestriction.G.Chart (prodPts)

variable {R O : Type} [CommRing R] [CommRing O] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {act : OAct O G}
  {g : ℕ} {v : Fin g → (epsR R ⟶ G)} (hv : IsLieBasis v) {M : O → Matrix (Fin g) (Fin g) R}
  (hM : ∀ x i, IsLieComb (M x i) v (v i ≫ act.act x))

include hv hM

theorem prodPts_act (x : O) (c : Fin g → R) : prodPts c v ≫ act.act x = prodPts (c ᵥ* M x) v := by
  have := act.hom x
  have e : prodPts c v ≫ act.act x = prodPts c fun i => v i ≫ act.act x := by
    refine (map_list_prod (IsMonHom.monoidHom (act.act x) _) _).trans ?_
    rw [prodPts, List.map_ofFn]
    exact congrArg (fun f => (List.ofFn f).prod) (funext fun i => Category.assoc _ (v i) (act.act x))
  rw [e, funext fun i => (Chart.isLieComb_iff _ _ _).1 (hM x i), vecMul_eq_sum]
  exact prodPts_prodPts hv.1 c fun i => M x i

theorem eig_iff (x : O) (s : R) (c : Fin g → R) :
    (prodPts c v ≫ act.act x).left = spMap (epsScaleR s) ≫ (prodPts c v).left ↔ c ᵥ* M x = s • c := by
  rw [prodPts_act hv hM, ← (prodPts_injective hv).eq_iff, prodPts_smul, Over.OverMorphism.ext_iff]
  rfl

theorem card_eq_of_lieMult [Smooth G.hom] {K : Type} [Field K] (f : R →+* K) {τ : O →+* K} {N n : ℕ}
    (hN : LieMult act (spMap f) τ N) (u : Fin n → Fin g → K) (hu : ∀ k x, u k ᵥ* (M x).map f = τ x • u k)
    (hu' : ∀ w : Fin g → K, (∀ x, w ᵥ* (M x).map f = τ x • w) → ∃! cf : Fin n → K, w = ∑ k, cf k • u k) :
    n = N := by
  obtain ⟨ρ, hρ⟩ := exists_action hv act
  have hk := isLinearPullback_pullback act (spMap f)
  obtain ⟨v', hv', e⟩ := GlobalTheory.exists_isLieBasis_baseChange R K f _ _ _ hk.1 ‹_› g v hv
  obtain ⟨ρ', hρ'⟩ := exists_action hv' (act.pullback (spMap f) G)
  have h₁ : ∀ x c, ρ x c = c ᵥ* M x := fun x c => prodPts_injective hv ((hρ x c).trans (prodPts_act hv hM x c))
  have h₂ : ∀ x w, ρ' x w = w ᵥ* (M x).map f := fun x w => by
    have : ρ' x = ((M x).map f).vecMulLinear := (Pi.basisFun K (Fin g)).ext fun i => by
      have e₁ : Pi.basisFun K (Fin g) i = f ∘ Pi.single i 1 := by
        ext j; by_cases h : j = i <;> simp [h]
      rw [e₁, ← action_baseChange hk.1 hv' e hk.2 hρ hρ', h₁, ← e₁]
      ext j; simp
    rw [this]; rfl
  have mem : ∀ w, w ∈ eigenSub ρ' τ ↔ ∀ x, w ᵥ* (M x).map f = τ x • w := fun w => by
    simp only [mem_eigenSub, h₂]
  rw [← finrank_of_lieMult hk.1 hv' hk.2 hρ' hN]
  let u' : Fin n → eigenSub ρ' τ := fun k => ⟨u k, (mem _).2 (hu k)⟩
  have hb : Function.Bijective (Fintype.linearCombination K u') :=
    (Function.bijective_iff_existsUnique _).2 fun w => (existsUnique_congr fun cf => by
      rw [Fintype.linearCombination_apply, Subtype.ext_iff, Submodule.coe_sum, eq_comm]; rfl).1
      (hu' w.1 ((mem _).1 w.2))
  rw [← (LinearEquiv.ofBijective _ hb).finrank_eq, Module.finrank_fin_fun]

end Coordinates

end GlobalTheory.ConstBasis

namespace GlobalTheory.ConstBasis

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open Matrix GlobalTheory.LieEigen
open ReciprocityTheory.ChartRestriction.G.Chart (prodPts)

theorem vecMul_map {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {g : ℕ} {u : Fin g → A}
    {M : Matrix (Fin g) (Fin g) A} {s : A} (h : u ᵥ* M = s • u) :
    (fun j => φ (u j)) ᵥ* M.map φ = φ s • fun j => φ (u j) :=
  funext fun i => (φ.map_vecMul M u i).symm.trans (by rw [h]; exact φ.map_mul _ _)

theorem flat_of_injective (A B : Type) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A] [CommRing B] [IsDomain B]
    [Algebra A B] (h : Function.Injective (algebraMap A B)) : Module.Flat A B := by
  have := (faithfulSMul_iff_algebraMap_injective A B).2 h
  infer_instance

theorem lieMult_arc {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {A : Type}
    [CommRing A] [IsDomain A] {b : O →+* A} {a : ArcIn Dw l β A b} {χ : Sp (PowerSeries A) ⟶ Y.X} (W : Wit Y a χ)
    (f : c.F →+* FractionRing A) (hf : f.comp β = (algebraMap A (FractionRing A)).comp b) {r z : O}
    (hr : ((β r : c.F) : ℂ) = H.rt0) (hz : ((β z : c.F) : ℂ) = zeta l.A) (F : Type) [Field F] [IsAlgClosed F]
    [Algebra A F] [Algebra (FractionRing A) F] [IsScalarTower A (FractionRing A) F] (τ : E →+* ℂ) :
    LieMult W.t.act (spMap ((algebraMap A F).comp PowerSeries.constantCoeff))
      (((algebraMap (FractionRing A) F).comp f).comp (embK c τ)) (Dw.mult τ) := by
  classical
  let := H.starRing
  let j := (algebraMap (FractionRing A) F).comp f
  have hinj : Function.Injective fun τ : E →+* ℂ => embK c τ := fun τ τ' h =>
    (EigenSplit.isSplitting_complex E).injective (RingHom.ext fun a =>
      (embK_coe c τ a).symm.trans ((congrArg _ (RingHom.congr_fun h a)).trans (embK_coe c τ' a)))
  have hσ : EigenSplit.IsSplitting fun τ : E →+* ℂ => j.comp (embK c τ) :=
    EigenSplit.isSplitting_of_isDomain hinj (NumberField.Embeddings.card E ℂ) j (by
      simpa using (EigenSplit.isUnit_discr_of_charZero (E := E) c.F).map j)
  obtain ⟨n, hn, hs⟩ := (a.geom F r z hr hz (algebraMap A F) (IsScalarTower.algebraMap_eq _ _ _)).1
    (j.comp (embK c τ))
  have hc : j.comp (embK c τ) H.rt = algebraMap A F (b r) ↔ τ (H.rt : E) = H.rt0 := by
    have e : algebraMap A F (b r) = j (β r) := by
      rw [IsScalarTower.algebraMap_apply A (FractionRing A) F]
      exact congrArg _ (RingHom.congr_fun hf r).symm
    rw [e, RingHom.comp_apply, j.injective.eq_iff, ← hr, ← embK_coe c, Subtype.ext_iff]
  have hm : Dw.mult τ = n + Module.finrank (𝓞 E) W.P.D.toPre.X := by
    rw [← W.e.finrank_eq, hs, Datum.mult]
    exact if_congr hc.symm rfl rfl
  rw [hm]
  refine lieMult_level W.P.U.toUnifPre W.P.lin _ (fun x hx => ?_) hσ τ
    (j.injective.comp ((embF c τ).injective.comp RingOfIntegers.coe_injective)) ?_
  · obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    simp
  · refine (LiePull.lieMult_pull _ _ _ _ _ _ _ (ofRingAct a.oa.onB.toRingAct) _ W.spec.1 W.spec.2.2.2.1 F _ _ _).2 ?_
    convert hn using 1
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext x
    simp

theorem exists_arcBasis : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) [IsPrincipalIdealRing A] [CharZero A] (ρ : (E →+* ℂ) → (𝓞 E →+* A)) (f : c.F →+* FractionRing A), f.comp β = (algebraMap A (FractionRing A)).comp b → (∀ τ x, algebraMap A (FractionRing A) (ρ τ x) = f (embK c τ x)) → (∃ r z : O, ((β r : c.F) : ℂ) = H.rt0 ∧ ((β z : c.F) : ℂ) = zeta l.A) → ∃ e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A), (∀ τ k, GtTanR (e τ k)) ∧ ArcBasis W ρ e := by
  intro hL _ E _ _ _ H Dw l Xo c O _ β Y A _ _ _ _ b a χ W _ _ ρ f hf hρ ⟨r, z, hr, hz⟩
  have hG := hL.globalFns
  obtain ⟨g, e, v, M, hev, hv, -, hM⟩ := T.exists_constantLieBasis_arcGroup hG E H Dw l Xo c O β Y A b a χ W
  have := W.t.semi.smooth
  let F := AlgebraicClosure (FractionRing A)
  have := flat_of_injective A F (by
    rw [IsScalarTower.algebraMap_eq A (FractionRing A) F]
    exact (algebraMap (FractionRing A) F).injective.comp (IsFractionRing.injective A _))
  have := flat_of_injective A (PowerSeries A) PowerSeries.C_injective
  let M' : 𝓞 E → Matrix (Fin g) (Fin g) (PowerSeries A) := fun x => (M x).map (PowerSeries.C (R := A))
  have hM' : ∀ x i, IsLieComb (M' x i) v (v i ≫ W.t.act.act x) := hM
  have key : ∀ τ, ∃ u : Fin (Dw.mult τ) → Fin g → A, (∀ k x, u k ᵥ* M x = ρ τ x • u k) ∧
      ∀ w : Fin g → PowerSeries A, (∀ x, w ᵥ* M' x = PowerSeries.C (R := A) (ρ τ x) • w) →
        ∃! cf : Fin (Dw.mult τ) → PowerSeries A, w = ∑ k, cf k • (fun j => PowerSeries.C (R := A) (u k j)) := by
    intro τ
    obtain ⟨n, u, hu, hu'⟩ := (commonEigenvectors_flat_baseChange A (𝓞 E) g 0 M (ρ τ)).2
    have flat := (commonEigenvectors_flat_baseChange A (𝓞 E) g n M (ρ τ)).1 A u hu (by simpa using hu')
    have hN := lieMult_arc W f hf hr hz F τ
    have hτ : ∀ x, ((algebraMap (FractionRing A) F).comp f).comp (embK c τ) x = algebraMap A F (ρ τ x) := fun x => by
      rw [IsScalarTower.algebraMap_apply A (FractionRing A) F, hρ]; rfl
    have hm : ∀ x, (M' x).map ((algebraMap A F).comp PowerSeries.constantCoeff) = (M x).map (algebraMap A F) :=
      fun x => by ext i j; simp [M']
    obtain rfl := card_eq_of_lieMult hv hM' _ hN (fun k j => algebraMap A F (u k j))
      (fun k x => by
        rw [hm, hτ]
        exact vecMul_map _ (hu k x))
      (fun w hw => flat F w (by simpa only [hm, hτ] using hw))
    exact ⟨u, hu, flat (PowerSeries A)⟩
  choose u hu hu' using key
  choose ν hν using fun τ k => ConstLie.exists_gtComb (u τ k) e
  have img : ∀ τ k, LieImg W (ν τ k) (prodPts (fun j => PowerSeries.C (R := A) (u τ k j)) v) := fun τ k =>
    (T.lieImg_iff_isLieComb_of_gtComb hG E H Dw l Xo c O β Y A b a χ W g _ e _ v _ (fun i => (hev i).2) (hν τ k)).2
      ((Chart.isLieComb_iff _ _ _).2 rfl)
  refine ⟨ν, fun τ k => ((ConstLie.main hG E H Dw l Xo c O β Y A b a χ W _).2 _ (img τ k)).2
    (isTangent_prodPts hv.1 _), _, img, fun τ => ⟨fun k => ⟨isTangent_prodPts hv.1 _, fun x => ?_⟩, fun w hw he => ?_⟩⟩
  · rw [eig_iff hv hM']
    exact vecMul_map _ (hu τ k x)
  · obtain ⟨d, rfl⟩ := exists_prodPts hv hw
    refine (existsUnique_congr fun cf => ?_).1 (hu' τ d fun x => (eig_iff hv hM' _ _ _).1 (he x))
    rw [Chart.isLieComb_iff, prodPts_prodPts hv.1, (prodPts_injective hv).eq_iff]

end GlobalTheory.ConstBasis
