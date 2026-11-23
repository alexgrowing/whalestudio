import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FibreFramesOnModels
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModelBaseChangeOverring
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsSecPullNonzeroOnFibres

noncomputable section

namespace GlobalTheory.KeyUnitModels

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels

section Sections

variable {R : Type} [CommRing R]

theorem constFn_mul {X : Scheme.{0}} (f : X ⟶ Sp R) (U : X.Opens) (a b : R) :
    constFn f U (a * b) = constFn f U a * constFn f U b := by
  simp only [constFn, map_mul]

theorem constFn_one {X : Scheme.{0}} (f : X ⟶ Sp R) (U : X.Opens) : constFn f U 1 = 1 := by
  simp only [constFn, map_one]

theorem constFn_pow {X : Scheme.{0}} (f : X ⟶ Sp R) (U : X.Opens) (a : R) (n : ℕ) :
    constFn f U (a ^ n) = constFn f U a ^ n := by
  simp only [constFn, map_pow]

theorem constFn_congr {X : Scheme.{0}} {f f' : X ⟶ Sp R} (h : f = f') (U : X.Opens) (a : R) :
    constFn f U a = constFn f' U a := by rw [h]

theorem appLE_constFn {X Y : Scheme.{0}} (f : Y ⟶ X) (g : X ⟶ Sp R) (U : X.Opens) (W : Y.Opens)
    (h : W ≤ f ⁻¹ᵁ U) (a : R) : (f.appLE U W h).hom (constFn g U a) = constFn (f ≫ g) W a := by
  simp only [constFn]
  erw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

variable {X : Over (Sp R)} {L : LB X.left}

theorem IsMul.trans {s t u : L.Sec} {a b : R} (h₁ : IsMul (X := X) s a t) (h₂ : IsMul (X := X) t b u) :
    IsMul (X := X) s (a * b) u := fun i => by
  rw [h₁ i, h₂ i, constFn_mul, _root_.mul_assoc]

theorem isMul_self (s : L.Sec) : IsMul (X := X) s 1 s := fun i => by rw [constFn_one, _root_.one_mul]

theorem Generates.isUnit {s t : L.Sec} (hs : Generates (X := X) s) (ht : Generates (X := X) t) {a : R}
    (h : IsMul (X := X) t a s) : IsUnit a := by
  obtain ⟨d, hd, -⟩ := ht s
  have e : a * d = 1 := (hs s).unique (IsMul.trans h hd |> fun h' => by
    have := IsMul.trans (isMul_self (X := X) s) (IsMul.trans hd h)
    simpa [_root_.one_mul, mul_comm] using this) (isMul_self (X := X) s)
  exact ⟨⟨a, d, e, by rw [mul_comm]; exact e⟩, rfl⟩

theorem prod_const_mul {A : Type*} [CommMonoid A] {N : ℕ} (c : A) (x : Fin N → A) :
    ∏ k, c * x k = c ^ N * ∏ k, x k := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem isMul_boxSec {G : Over (Sp R)} {L : LB G.left} {θ θ₀ : L.Sec} {b : R} (h : IsMul (X := G) θ b θ₀) (N : ℕ) :
    IsMul (X := pow G N) (boxSec G θ N) (b ^ N) (boxSec G θ₀ N) := fun j => by
  show (∏ k : Fin N, _) = _ * ∏ k : Fin N, _
  have e : ∀ k : Fin N, (pr G N k ≫ G.hom) = (pow G N).hom := fun k => Over.w (Pi.π (fun _ : Fin N => G) k)
  simp only [h (j _), map_mul, appLE_constFn, constFn_congr (e _)]
  exact (prod_const_mul _ _).trans (congrArg (· * _) (constFn_pow _ _ _ _).symm)

end Sections

section Line

open IsLocalRing ReciprocityTheory.ChartRestriction.G.H1 Formalism.L2.Pj

theorem generates_of_generic_line {V K : Type} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] {X X' : Scheme.{0}}
    (p : X ⟶ Sp V) [Flat p] {p' : X' ⟶ Sp K} {φ : X' ⟶ X}
    (hφ : IsPullback φ p' p (spMap (algebraMap V K))) {L : LB X} {L' : LB X'} (hL : L.IsLB)
    (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ)) (b : L'.Sec)
    (hb : ∀ s : L'.Sec, ∃ a : K, ∀ i, s.f i = constFn p' _ a * b.f i)
    (θ : L.Sec) {g : X} (hg : p g = closedPoint V) (hθ : g ∈ Out.nonzeroLocus θ) (σ : L.Sec) :
    ∃! a : V, ∀ i, σ.f i = constFn p _ a * θ.f i := by
  obtain ⟨k₀, hb₀⟩ := TopologicalSpace.Opens.mem_iSup.1 hθ
  have hk₀ : g ∈ L.U k₀ := X.basicOpen_le _ hb₀
  have un : IsUnit (gs (𝟙 _) g _ (θ.f k₀)) := by
    rw [gs_eq (𝟙 _) g _ hk₀]; exact (X.mem_basicOpen _ _ hk₀).1 hb₀
  obtain ⟨w, gw'⟩ := hw
  have down := sec_pull_down ((isGen_iff w).1 gw') hL hL'
  obtain ⟨θ', hθ'⟩ := down θ
  have : IsDominant (spMap (algebraMap V K)) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V K)).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap (algebraMap V K))
  have : IsSchemeTheoreticallyDominant φ := IsSchemeTheoreticallyDominant.of_isPullback hφ.flip
  have : QuasiCompact φ := MorphismProperty.of_isPullback (P := @QuasiCompact) hφ.flip inferInstance

  have inj : ∀ (σ τ σK τK : _) (r : V), (∀ (Z : Scheme.{0}) (q : Z ⟶ X') (y : Z) j k, φ (q y) ∈ L.U j →
      q y ∈ L'.U k → gs (q ≫ φ) y _ (LB.Sec.f σ j) = (gw w q y j k).val * gs q y _ (LB.Sec.f σK k)) →
      (∀ (Z : Scheme.{0}) (q : Z ⟶ X') (y : Z) j k, φ (q y) ∈ L.U j →
      q y ∈ L'.U k → gs (q ≫ φ) y _ (LB.Sec.f τ j) = (gw w q y j k).val * gs q y _ (LB.Sec.f τK k)) →
      (∀ k, LB.Sec.f σK k = constFn p' _ (algebraMap V _ r) * LB.Sec.f τK k) →
      ∀ j, LB.Sec.f σ j = constFn p _ r * LB.Sec.f τ j := by
    intro σ τ σK τK r h₁ h₂ h₃ j
    refine φ.app_injective _ (fn_ext fun y hy => ?_)
    obtain ⟨k, hk⟩ := exists_chart hL' y
    refine (gs_pull (𝟙 _) φ y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 _) φ y _ hy _).symm)
    rw [gs_mul (𝟙 _ ≫ φ) y _ hy, gs_constFn _ _ (𝟙 _ ≫ φ) y hy, h₁ _ (𝟙 _) y j k hy hk, h₂ _ (𝟙 _) y j k hy hk,
      (sec_eq_iff _ _ _ _).1 h₃ k y hk, Category.id_comp, hφ.w, cst_comp, mul_left_comm]
  have mulc : ∀ {s t u : L'.Sec} {a a' : K}, (∀ k, s.f k = constFn p' _ a * t.f k) →
      (∀ k, t.f k = constFn p' _ a' * u.f k) → ∀ k, s.f k = constFn p' _ (a * a') * u.f k :=
    fun h h' => (sec_eq_iff _ _ _ _).2 fun k y hy => by
      rw [(sec_eq_iff _ _ _ _).1 h k y hy, (sec_eq_iff _ _ _ _).1 h' k y hy, cst_mul, _root_.mul_assoc]
  have invc : ∀ {s t : L'.Sec} {a : K}, a ≠ 0 → (∀ k, s.f k = constFn p' _ a * t.f k) →
      ∀ k, t.f k = constFn p' _ a⁻¹ * s.f k := fun ha h => (sec_eq_iff _ _ _ _).2 fun k y hy => by
    rw [(sec_eq_iff _ _ _ _).1 h k y hy, ← _root_.mul_assoc, ← cst_mul, inv_mul_cancel₀ ha, cst_one, _root_.one_mul]
  have unit : ∀ (σ : L.Sec) (r : V), (∀ j, θ.f j = constFn p _ r * σ.f j) → IsUnit r := fun σ r h => by
    by_contra hr
    rw [(sec_eq_iff _ _ _ _).1 h k₀ g hk₀] at un
    exact cst_not_isUnit p g hg hr (isUnit_of_mul_isUnit_left un)
  obtain ⟨a₀, ha₀⟩ := hb θ'
  have h₀ : a₀ ≠ 0 := fun h => not_isUnit_zero (unit θ 0 (inj θ θ θ' θ' 0 hθ' hθ' ((sec_eq_iff _ _ _ _).2 fun k y hy => by
    rw [(sec_eq_iff _ _ _ _).1 ha₀ k y hy, h, map_zero, ← _root_.mul_assoc, ← cst_mul, mul_zero])))
  obtain ⟨σK, hσK⟩ := down σ
  obtain ⟨a, ha⟩ : ∃ a : K, ∀ i, σK.f i = constFn p' _ a * θ'.f i := by
    obtain ⟨a, ha⟩ := hb σK
    exact ⟨a * a₀⁻¹, mulc ha (invc h₀ ha₀)⟩
  obtain ⟨r, hr⟩ : ∃ r : V, ∀ i, σ.f i = constFn p _ r * θ.f i := by
    by_cases h : IsLocalization.IsInteger V a
    · obtain ⟨r, rfl⟩ := h
      exact ⟨r, inj σ θ σK θ' r hσK hθ' ha⟩
    · have hne : a ≠ 0 := fun e => h (e ▸ IsLocalization.isInteger_zero)
      obtain ⟨r, hr⟩ := (ValuationRing.isInteger_or_isInteger V a).resolve_left h
      obtain ⟨u, rfl⟩ := unit σ r (inj θ σ θ' σK r hθ' hσK (hr ▸ invc hne ha))
      exact absurd ⟨(u⁻¹ : Vˣ), by rw [← inv_inv a, ← hr, map_units_inv]⟩ h
  refine ⟨r, hr, fun r' hr' => ?_⟩
  by_contra hne
  have e : cst p g (r' - r) * gs (𝟙 _) g _ (θ.f k₀) = cst p g (r' - r) * 0 := by
    rw [cst_sub, sub_mul, ← (sec_eq_iff _ _ _ _).1 hr' k₀ g hk₀, ← (sec_eq_iff _ _ _ _).1 hr k₀ g hk₀, sub_self, mul_zero]
  exact un.ne_zero (cst_regular p g (sub_ne_zero.2 hne) e)
variable {V K : Type} [CommRing V] [Field K] [Algebra V K]

def NonzeroClosed [IsLocalRing V] {X : Over (Sp V)} {L : LB X.left} (θ : L.Sec) : Prop :=
  ∃ g : X.left, X.hom g = closedPoint V ∧ g ∈ Out.nonzeroLocus θ

theorem NonzeroClosed.of_isMul [IsLocalRing V] {X : Over (Sp V)} {L : LB X.left} {θ σ : L.Sec} {a : V}
    (h : IsMul (X := X) σ a θ) (hσ : NonzeroClosed (X := X) σ) : IsUnit a ∧ NonzeroClosed (X := X) θ := by
  obtain ⟨g, hg, hσ⟩ := hσ
  obtain ⟨k₀, hb₀⟩ := TopologicalSpace.Opens.mem_iSup.1 hσ
  have hk₀ : g ∈ L.U k₀ := X.left.basicOpen_le _ hb₀
  have un : IsUnit (gs (𝟙 _) g _ (σ.f k₀)) := by
    rw [gs_eq (𝟙 _) g _ hk₀]; exact (X.left.mem_basicOpen _ _ hk₀).1 hb₀
  refine ⟨?_, g, hg, TopologicalSpace.Opens.mem_iSup.2 ⟨k₀, ?_⟩⟩
  · by_contra hr
    rw [(sec_eq_iff _ _ _ _).1 h k₀ g hk₀] at un
    exact cst_not_isUnit X.hom g hg hr (isUnit_of_mul_isUnit_left un)
  · rw [h k₀, Scheme.basicOpen_mul] at hb₀
    exact hb₀.2

theorem generates_of_isFibreOf [IsDomain V] [ValuationRing V] [IsFractionRing V K] {G : Over (Sp V)} [GrpObj G]
    [IsCommMonObj G] [Flat G.hom] {L : LB G.left} (hL : L.IsLB) {rig : LB.Gen (L.pull (eSec G))} {θ : L.Sec} {n : ℕ}
    {w : Fin n → (epsR V ⟶ G)} {x : KeyIn K} (hx : IsFibreOf x G L rig θ w (algebraMap V K)) {θ₀ : L.Sec}
    (h₀ : NonzeroClosed (X := G) θ₀) : Generates (X := G) θ₀ := by
  obtain ⟨φ, -, e, -, -, hp, he, -⟩ := hx
  obtain ⟨g, hg, hθ⟩ := h₀
  obtain ⟨b, hb⟩ := principalPolarisation_exists_unique_section GlobalTheory.firstFiveLaws.2.1.secTwist x.P
  exact generates_of_generic_line G.hom hp.1 hL x.P.isLB ⟨e, he⟩ b (fun s => (hb s).exists) θ₀ hg hθ

end Line

section Loc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F}
  (Y : Model Xo c β) (b : O →+* O') (hb : β'.comp b = β)

include hb in

theorem isPullback_gen : IsPullback (pullback.fst (pullback.snd Y.s (spMap b)) (spMap β') ≫ pullback.fst Y.s (spMap b))
    (pullback.snd (pullback.snd Y.s (spMap b)) (spMap β')) Y.s (spMap β) := by
  have hsp : spMap β' ≫ spMap b = spMap β := by
    rw [← hb, spMap, spMap, spMap, ← Spec.map_comp]
    rfl
  rw [← hsp]
  exact (IsPullback.of_hasPullback _ _).paste_horiz (IsPullback.of_hasPullback _ _)

def locTriple : SAB H (pullback Y.s (spMap b)) := (exists_sab (pullback.fst Y.s (spMap b)) Y.t).choose

def locMap : SABMap (locTriple Y b) Y.t (pullback.fst Y.s (spMap b)) :=
  (exists_sab (pullback.fst Y.s (spMap b)) Y.t).choose_spec.some

theorem exists_locGen : ∃ m' : SABMap Y.oF.t (locTriple Y b) ((Y.jQ ≫ (isPullback_gen Y b hb).isoPullback.inv) ≫
    pullback.fst (pullback.snd Y.s (spMap b)) (spMap β')), Y.m.φ = m'.φ ≫ (locMap Y b).φ := by
  have aux : ∀ (g : Xo.XF c ⟶ pullback Y.s (spMap b)) (e : Xo.XF c ⟶ Y.X) (n : SABMap Y.oF.t Y.t e),
      g ≫ pullback.fst Y.s (spMap b) = e → ∃ m' : SABMap Y.oF.t (locTriple Y b) g, n.φ = m'.φ ≫ (locMap Y b).φ := by
    rintro g e n rfl
    exact ObjMaps.exists_sab_cancel (locMap Y b) n
  refine aux _ _ Y.m ?_
  simp only [Category.assoc, (isPullback_gen Y b hb).isoPullback_inv_fst]

theorem range_locGen : Set.range (Y.jQ ≫ (isPullback_gen Y b hb).isoPullback.inv) =
    (isPullback_gen Y b hb).isoPullback.hom ⁻¹' Set.range Y.jQ := by
  ext y
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u, by simp⟩
  · rintro ⟨u, hu⟩
    exact ⟨u, by simp [hu]⟩

variable [IsPreimmersion (spMap b)] [Flat (spMap b)]

@[reducible] def locModel : Model Xo c β' where
  X := pullback Y.s (spMap b)
  s := pullback.snd _ _
  normal := isNormalScheme_of_flat_of_surjectiveOnStalks (pullback.fst Y.s (spMap b)) Y.normal
  proj := ProjSpace.isProjOver_pullback_snd b Y.proj
  flat := have := Y.flat; inferInstance
  jQ := Y.jQ ≫ (isPullback_gen Y b hb).isoPullback.inv
  jQ_over := by rw [Category.assoc, (isPullback_gen Y b hb).isoPullback_inv_snd, Y.jQ_over]
  jQ_open := have := Y.jQ_open; inferInstance
  jQ_dense := by
    rw [range_locGen Y b hb]
    exact Y.jQ_dense.preimage (isPullback_gen Y b hb).isoPullback.hom.isOpenEmbedding.isOpenMap
  t := locTriple Y b
  oF := Y.oF
  m0 := Y.m0
  m := (exists_locGen Y b hb).choose
  ab_gen := by
    rw [range_locGen Y b hb, ← Y.ab_gen]
    ext y
    simp only [Set.mem_preimage]
    rw [← abLocus_pullback abLocusOne Y.t.semi (locMap Y b).cart.1, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
      (isPullback_gen Y b hb).isoPullback_hom_fst]

theorem locModel_j : (locModel Y b hb).j ≫ pullback.fst Y.s (spMap b) = Y.j := by
  simp only [Model.j, Category.assoc, (isPullback_gen Y b hb).isoPullback_inv_fst]

theorem locModel_m : (locModel Y b hb).m.φ ≫ (locMap Y b).φ = Y.m.φ := (exists_locGen Y b hb).choose_spec.symm

theorem mem_abLocus_locModel (x : (locModel Y b hb).X) :
    x ∈ abLocus (locModel Y b hb).t.G ↔ pullback.fst Y.s (spMap b) x ∈ abLocus Y.t.G :=
  (abLocus_pullback abLocusOne Y.t.semi (locMap Y b).cart.1 x).symm

theorem localisedModel_uniformisation_baseChange (h : Y.N3) : (locModel Y b hb).N3 := by
  intro R _ _ _ _ h₁ h₂ h₃ ξ t m hne hs
  obtain ⟨n, -⟩ := ObjMaps.exists_sab_comp (locMap Y b) m
  have e : ξ ⁻¹' abLocus (locModel Y b hb).t.G = (ξ ≫ pullback.fst Y.s (spMap b)) ⁻¹' abLocus Y.t.G := by
    ext q
    rw [Set.mem_preimage, Set.mem_preimage, mem_abLocus_locModel, Scheme.Hom.comp_apply]
  rw [e] at hne ⊢
  exact h R h₁ h₂ h₃ _ t n hne hs

theorem locModel_pushInvertible (hD : GlobalTheory.Models.IsDedFrac β') (hY : PushInvertible Y.t.G Y.t.PP.L) :
    PushInvertible (locModel Y b hb).t.G (locModel Y b hb).t.PP.L := by
  obtain ⟨l₁, l₂, l₃, -, -⟩ := GlobalTheory.firstFiveLaws
  let C := locModel Y b hb
  exact GlobalTheory.PushInv.pushInvertible_of_model l₁ l₂ l₃ E H D l _ _ _ _ _ _ Y.oF _ β'
    ⟨C.X, C.s, C.normal, C.proj, C.flat, C.jQ, C.jQ_over, C.jQ_open, C.jQ_dense, C.t, C.m, C.ab_gen⟩ hD
    ((GlobalTheory.AbLocusPull.abLocus_sections_pull _ _ _ Y.t.G C.t.G (locMap Y b).φ Y.t.semi (locMap Y b).cart).2 _ _
      Y.t.PP.isLB C.t.PP.isLB (GlobalTheory.LN.GenericPoint.lbIso_of_sabMap (locMap Y b)) fun x => by
        obtain ⟨V, hV, θ, hθ, -, nz⟩ := hY x
        exact ⟨V, hV, θ, hθ, nz⟩)

end Loc

end GlobalTheory.KeyUnitModels
