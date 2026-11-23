import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointExtensionSplit
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocallyOfFiniteTypeKer
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionSectionPullbackStatement
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.RootFrame

namespace UpperTheory.SpecLab

open GlobalTheory.HTMap GlobalTheory.HtChar GlobalTheory.HtGen CategoryTheory.Limits

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

private theorem sect {X : Scheme.{0}} [IsLocallyNoetherian X] (t : SAB H X) {K : Type} [Field K] [CharZero K] {q : ℕ}
    (hq : q ≠ 0) {R : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsLocalRing R] [Algebra R K]
    [IsFractionRing R K] (x : Sp R ⟶ X) (hs : SplitK t (spMap (algebraMap R K) ≫ x) q) {O : Type} [CommRing O]
    [IsDomain O] [IsLocalRing O] (ψ : R →+* O) [IsLocalHom ψ] {z : Sp O ⟶ X} (hz : z = spMap ψ ≫ x)
    (w : Over.mk z ⟶ t.G) (hw : w ^ q = 1) : ∃ σ : Over.mk x ⟶ t.G, σ ^ q = 1 ∧ w.left = spMap ψ ≫ σ.left := by
  haveI : CharZero R := ⟨fun m n h => Nat.cast_injective (R := K) (by simpa using congrArg (algebraMap R K) h)⟩
  obtain ⟨P, hP⟩ := ex_full hq (splitTors_of_splitK x q hs) (IsLocalRing.maximalIdeal R) inferInstance
  have hA : IsUnit P.f := by by_contra hn; exact hP.1 hn
  obtain ⟨β, hβ⟩ := hP.at (φ := ψ) (fun 𝔪 h𝔪 => by
    rw [IsLocalRing.eq_maximalIdeal h𝔪, IsLocalRing.maximalIdeal_comap ψ]) hz w hw
  obtain ⟨β₀, hβ₀, rfl⟩ := sect_of hA _ hβ
  have hσA : P.At (RingHom.id R) (spMap β₀ ≫ P.u.left) β₀ := ⟨hβ₀, rfl⟩
  let σ : Over.mk x ⟶ t.G := mkPt (spMap β₀ ≫ P.u.left) (hσA.over.trans (by rw [spMap_id', Category.id_comp]))
  exact ⟨σ, FP.At.tors (w := σ) hσA, by rw [← hβ.2, ← spc_assoc]; rfl⟩

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

section Lab

variable {O : Type} [CommRing O] {β : O →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {K : Type} [Field K]
  {y : Sp K ⟶ Xo.XF c} {q : ℕ} {lb : Dw.La → (Over.mk y ⟶ Z.oF.t.G)} {ζ : Kˣ}

private theorem lab_pow (h : IsLabel Z y q lb ζ) {b b' : Dw.La} (e : lb b = lb b') (a : Dw.La) :
    ζ ^ Dw.EF a b = ζ ^ Dw.EF a b' := by
  have h1 := h.2.2.2.2 a b
  rw [e] at h1
  exact GlobalTheory.Ex.Specialise.unitOn_bijective.1
    ((GlobalTheory.LevelCompare.weil_existsUnique (GlobalTheory.Obj.toPolAV Z.oF) q (lb a) (lb b') ((h.2.2.2.1 _).2 ⟨a, rfl⟩)
      ((h.2.2.2.1 _).2 ⟨b', rfl⟩)).unique h1 (h.2.2.2.2 a b'))

private noncomputable def labHom (h : IsLabel Z y q lb ζ) : Multiplicative Dw.La →* (Over.mk y ⟶ Z.oF.t.G) :=
  MonoidHom.mk' (fun a => lb a.toAdd) fun a b => h.2.1 _ _

private theorem lab_eq_iff (h : IsLabel Z y q lb ζ) (a a' : Dw.La) : lb a = lb a' ↔ ∃ d, a = a' + q • d := by
  constructor
  · intro e
    have h0 : ∀ b, (q : ℤ) ∣ Dw.EF (a - a') b := fun b => by
      have h1 := h.2.2.2.2 a b
      rw [e] at h1
      have h2 := GlobalTheory.Ex.Specialise.unitOn_bijective.1
        ((GlobalTheory.LevelCompare.weil_existsUnique (GlobalTheory.Obj.toPolAV Z.oF) q (lb a') (lb b) ((h.2.2.2.1 _).2 ⟨a', rfl⟩)
          ((h.2.2.2.1 _).2 ⟨b, rfl⟩)).unique h1 (h.2.2.2.2 a' b))
      rw [← h.1.zpow_eq_one_iff_dvd, map_sub, LinearMap.sub_apply, zpow_sub, h2, mul_inv_cancel]
    choose f hf using h0
    by_cases hq : q = 0
    · refine ⟨0, ?_⟩
      rw [smul_zero, add_zero, ← sub_eq_zero]
      exact Dw.unimod.1 (LinearMap.ext fun b => by rw [hf, hq]; simp)
    have hq' : (q : ℤ) ≠ 0 := by exact_mod_cast hq
    let F : Dw.La →ₗ[ℤ] ℤ := (AddMonoidHom.mk' f fun b b' => mul_left_cancel₀ hq' (by
      rw [mul_add, ← hf, ← hf, ← hf, map_add])).toIntLinearMap
    obtain ⟨d, hd⟩ := Dw.unimod.2 F
    refine ⟨d, ?_⟩
    rw [← sub_eq_iff_eq_add']
    refine Dw.unimod.1 (LinearMap.ext fun b => ?_)
    rw [hf, map_nsmul, hd, LinearMap.smul_apply, nsmul_eq_mul]
    rfl
  · rintro ⟨d, rfl⟩
    have h1 : lb (q • d) = lb d ^ q := map_pow (labHom h) (Multiplicative.ofAdd d) q
    rw [h.2.1, h1, (h.2.2.2.1 _).2 ⟨d, rfl⟩, _root_.mul_one]

private theorem lab_finite (h : IsLabel Z y q lb ζ) (hq : q ≠ 0) : Finite {σ : Over.mk y ⟶ Z.oF.t.G // σ ^ q = 1} := by
  haveI := Dw.fin
  haveI : Module.Finite ℤ Dw.La := Module.Finite.trans (𝓞 E) Dw.La
  let N : Submodule ℤ Dw.La := LinearMap.range (LinearMap.lsmul ℤ Dw.La q)
  haveI : Finite (Dw.La ⧸ N) := Module.finite_of_fg_torsion _ fun x => by
    obtain ⟨x, rfl⟩ := N.mkQ_surjective x
    refine ⟨⟨(q : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hq)⟩, ?_⟩
    exact (map_smul N.mkQ (q : ℤ) x).symm.trans ((Submodule.Quotient.mk_eq_zero N).2 ⟨x, rfl⟩)
  choose a ha using fun σ : {σ : Over.mk y ⟶ Z.oF.t.G // σ ^ q = 1} => (h.2.2.2.1 σ.1).1 σ.2
  refine Finite.of_injective (fun σ => N.mkQ (a σ)) fun σ σ' e => Subtype.ext ?_
  obtain ⟨d, hd⟩ := (Submodule.Quotient.eq N).1 e
  rw [← ha, ← ha, lab_eq_iff h]
  exact ⟨d, by rw [← sub_eq_iff_eq_add', ← hd, LinearMap.lsmul_apply, natCast_zsmul]⟩

end Lab

section Ext

variable {O : Type} [CommRing O] {β : O →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β)

private theorem gen_inj {R K : Type} [CommRing R] [IsDomain R] [CommRing K] (io : R →+* K) (hio : Function.Injective io)
    {y : Sp R ⟶ Xo.XF c} {σ σ' : Over.mk y ⟶ Z.oF.t.G} (h : spMap io ≫ σ.left = spMap io ≫ σ'.left) : σ = σ' := by
  haveI : IsProper Z.oF.t.G.hom := (GlobalTheory.Obj.toPolAV Z.oF).isAb.proper
  haveI : IsDominant (spMap io) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical io).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot io).1 hio]; exact bot_le)⟩
  exact Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := Sp R) Z.oF.t.G.hom
    ((Over.w σ).trans (Over.w σ').symm) (spMap io) h)

private theorem cart_inj {T : Scheme.{0}} {y : T ⟶ Xo.XF c} {σ σ' : Over.mk y ⟶ Z.oF.t.G}
    (h : σ.left ≫ Z.m.φ = σ'.left ≫ Z.m.φ) : σ = σ' :=
  Over.OverMorphism.ext (Z.m.cart.1.hom_ext h ((Over.w σ).trans (Over.w σ').symm))

private theorem cart_lift {T : Scheme.{0}} (y : T ⟶ Xo.XF c) {x : T ⟶ Z.X} (hx : x = y ≫ Z.j) {q : ℕ}
    (w : Over.mk x ⟶ Z.t.G) (hw : w ^ q = 1) : ∃ σ : Over.mk y ⟶ Z.oF.t.G, σ ^ q = 1 ∧ σ.left ≫ Z.m.φ = w.left := by
  subst hx
  obtain ⟨σ, h1, h2⟩ := GlobalTheory.T.exists_torsion_section_pullback _ _ Z.oF.t.G Z.t.G _ Z.m.cm.F Z.m.cart (Over.mk y) w
  exact ⟨σ, h2 q hw, h1⟩

private theorem ex_label {C : Type} [Field C] [IsAlgClosed C] (y : Sp C ⟶ Xo.XF c) {q : ℕ} (hq : q ≠ 0) :
    ∃ lb ζ, IsLabel Z y q lb ζ := by
  obtain ⟨β₀, hβ₀⟩ : ∃ β₀ : KA l →+* C, y ≫ (pullback.fst _ _ ≫ Xo.s) = spMap β₀ :=
    ⟨(Spec.preimage (y ≫ (pullback.fst _ _ ≫ Xo.s))).hom, by simp [spMap]⟩
  obtain ⟨-, I, -⟩ := Z.oF.geom C y β₀ hβ₀
  have h := Nat.pos_of_ne_zero hq
  exact ⟨I.ev q, I.ζ q, I.ζ_prim q h, I.add q, I.lin q, I.onto q h, I.isom q h⟩

private theorem extend [IsLocallyNoetherian Z.X] {K : Type} [Field K] [CharZero K] {q : ℕ} (hq : q ≠ 0) {R : Type}
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsLocalRing R] [Algebra R K] [IsFractionRing R K]
    (yq : Sp R ⟶ Xo.XF c) {y₀ : Sp K ⟶ Xo.XF c} (h₀ : spMap (algebraMap R K) ≫ yq = y₀) (hs : SplitK Z.t (y₀ ≫ Z.j) q)
    {lb : Dw.La → (Over.mk y₀ ⟶ Z.oF.t.G)} {ζ : Kˣ} (hl : IsLabel Z y₀ q lb ζ) {C : Type} [Field C] [IsAlgClosed C]
    (φ : R →+* C) [IsLocalHom φ] {y : Sp C ⟶ Xo.XF c} (hy : spMap φ ≫ yq = y) :
    ∃ s : Dw.La → (Over.mk yq ⟶ Z.oF.t.G), (∀ a, s a ^ q = 1 ∧ pull _ h₀ (s a) = lb a) ∧
      ∀ w : Over.mk y ⟶ Z.oF.t.G, w ^ q = 1 → ∃ a, pull _ hy (s a) = w := by
  obtain ⟨ev, ξ, he⟩ := ex_label Z y hq
  have hsec : ∀ w : {w : Over.mk y ⟶ Z.oF.t.G // w ^ q = 1},
      ∃ σ : Over.mk yq ⟶ Z.oF.t.G, σ ^ q = 1 ∧ pull _ hy σ = w.1 := fun w => by
    obtain ⟨σ, h1, h2⟩ := sect (K := K) Z.t hq (yq ≫ Z.j) (by rw [← Category.assoc, h₀]; exact hs) φ
      (z := y ≫ Z.j) (by rw [← Category.assoc, hy]) (pushHom Z.m.cart (Over.mk y) w.1)
      ((map_pow (pushHom Z.m.cart (Over.mk y)) w.1 q).symm.trans (by rw [w.2, map_one]; rfl))
    obtain ⟨σ', h3, h4⟩ := cart_lift Z yq rfl σ h1
    refine ⟨σ', h3, cart_inj Z ?_⟩
    rw [pull_left, Category.assoc, h4, ← h2]
    rfl
  choose sg hsg hsg' using hsec
  have hinj : Function.Injective (pull (G := Z.oF.t.G) _ h₀) := fun σ σ' e =>
    gen_inj Z _ (IsFractionRing.injective R K) (congrArg (fun v => v.left) e)
  let g : {w : Over.mk y ⟶ Z.oF.t.G // w ^ q = 1} → {w : Over.mk y₀ ⟶ Z.oF.t.G // w ^ q = 1} :=
    fun w => ⟨pull _ h₀ (sg w), by rw [← map_pow, hsg, map_one]⟩
  have hg : Function.Injective g := fun w w' e => Subtype.ext (by
    rw [← hsg', ← hsg', hinj (congrArg Subtype.val e)])
  choose n hn using fun σ : {σ : Over.mk y₀ ⟶ Z.oF.t.G // σ ^ q = 1} => (hl.2.2.2.1 σ.1).1 σ.2
  let k : {w : Over.mk y₀ ⟶ Z.oF.t.G // w ^ q = 1} → {w : Over.mk y ⟶ Z.oF.t.G // w ^ q = 1} :=
    fun w => ⟨ev (n w), (he.2.2.2.1 _).2 ⟨_, rfl⟩⟩
  have hk : Function.Injective k := fun w w' e => Subtype.ext (by
    rw [← hn, ← hn, lab_eq_iff hl, ← lab_eq_iff he]
    exact congrArg Subtype.val e)
  haveI := lab_finite hl hq
  have hsurj : Function.Surjective g := (Finite.injective_iff_surjective.1 (hg.comp hk)).of_comp
  choose r hr using hsurj
  refine ⟨fun a => sg (r ⟨lb a, (hl.2.2.2.1 _).2 ⟨a, rfl⟩⟩), fun a => ⟨hsg _, congrArg Subtype.val (hr _)⟩,
    fun w hw => ⟨n (g ⟨w, hw⟩), ?_⟩⟩
  rw [hsg']
  refine congrArg Subtype.val (hg (a₂ := ⟨w, hw⟩) ?_)
  rw [hr]
  exact Subtype.ext (hn _)

private theorem label_at {K : Type} [Field K] {q : ℕ} (hq : q ≠ 0) {R : Type} [CommRing R] [IsDomain R] (io : R →+* K)
    (hio : Function.Injective io) (yq : Sp R ⟶ Xo.XF c) {y₀ : Sp K ⟶ Xo.XF c} (h₀ : spMap io ≫ yq = y₀)
    {lb : Dw.La → (Over.mk y₀ ⟶ Z.oF.t.G)} (ζ : Rˣ) (hl : IsLabel Z y₀ q lb (Units.map io.toMonoidHom ζ)) {C : Type}
    [Field C] [CharZero C] (φ : R →+* C) {y : Sp C ⟶ Xo.XF c} (hy : spMap φ ≫ yq = y)
    (s : Dw.La → (Over.mk yq ⟶ Z.oF.t.G)) (hs : ∀ a, s a ^ q = 1 ∧ pull _ h₀ (s a) = lb a)
    (hon : ∀ w : Over.mk y ⟶ Z.oF.t.G, w ^ q = 1 → ∃ a, pull _ hy (s a) = w) :
    IsLabel Z y q (fun a => pull _ hy (s a)) (Units.map φ.toMonoidHom ζ) := by
  have hinj : Function.Injective (pull (G := Z.oF.t.G) _ h₀) := fun σ σ' e =>
    gen_inj Z _ hio (congrArg (fun v => v.left) e)
  refine ⟨?_, fun a b => ?_, fun o a => ?_, fun σ => ⟨hon σ, ?_⟩, fun a b => ?_⟩
  · have h1 : IsPrimitiveRoot (io ζ) q := IsPrimitiveRoot.coe_units_iff.2 hl.1
    exact IsPrimitiveRoot.coe_units_iff.1 (prim_map φ hq (h1.of_map_of_injective hio))
  · beta_reduce
    rw [← map_mul, show s (a + b) = s a * s b from hinj (by rw [map_mul, (hs _).2, (hs _).2, (hs _).2, hl.2.1])]
  · have h1 : s (o • a) = s a ≫ Z.oF.t.act.act o := hinj (by
      rw [(hs _).2, hl.2.2.1, ← (hs a).2]
      exact Category.assoc _ _ _)
    beta_reduce
    rw [h1]
    exact Over.OverMorphism.ext (by rw [pull_left, Over.comp_left, Over.comp_left, pull_left, Category.assoc])
  · rintro ⟨a, rfl⟩
    rw [← map_pow, (hs a).1, map_one]
  · let P := GlobalTheory.Obj.toPolAV Z.oF
    obtain ⟨cq, hcq, -⟩ := GlobalTheory.LevelCompare.weil_existsUnique P q (s a) (s b) (hs a).1 (hs b).1
    obtain ⟨u, rfl⟩ := GlobalTheory.Ex.Specialise.unitOn_bijective.2 cq
    have hN := (GlobalTheory.LevelCompare.weil_skew_natural P q (Over.mk yq)).2 (Over.mk y₀) (Over.homMk (spMap io) h₀) _ _ _ hcq
    have hC := (GlobalTheory.LevelCompare.weil_skew_natural P q (Over.mk yq)).2 (Over.mk y) (Over.homMk (spMap φ) hy) _ _ _ hcq
    have hN' : Out.WeilIs P.A P.L q (lb a) (lb b) (unitOn (Units.map io.toMonoidHom u)) := by
      rw [← (hs a).2, ← (hs b).2, ← GlobalTheory.Ex.Specialise.map_unitOn]; exact hN
    have h1 := GlobalTheory.Ex.Specialise.unitOn_bijective.1 ((GlobalTheory.LevelCompare.weil_existsUnique P q (lb a) (lb b)
      ((hl.2.2.2.1 _).2 ⟨a, rfl⟩) ((hl.2.2.2.1 _).2 ⟨b, rfl⟩)).unique hN' (hl.2.2.2.2 a b))
    rw [← map_zpow] at h1
    rw [← map_zpow, ← Units.map_injective (f := io.toMonoidHom) hio h1, ← GlobalTheory.Ex.Specialise.map_unitOn]
    exact hC

end Ext

private theorem factor (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) {R C : Type} [CommRing R]
    [IsLocalRing R] [Field C] (φ : R →+* C) [IsLocalHom φ] (x : Sp R ⟶ Z.X) (y : Sp C ⟶ Xo.XF c)
    (h : spMap φ ≫ x = y ≫ Z.j) : ∃ yq : Sp R ⟶ Xo.XF c, x = yq ≫ Z.j := by
  obtain ⟨α, hα⟩ : ∃ α : 𝓞 c.F →+* R, x ≫ Z.s = spMap α := ⟨(Spec.preimage (x ≫ Z.s)).hom, (Spec.map_preimage _).symm⟩
  obtain ⟨ga, hga⟩ : ∃ ga : c.F →+* C, y ≫ Z.jQ ≫ pullback.snd _ _ = spMap ga :=
    ⟨(Spec.preimage (y ≫ Z.jQ ≫ pullback.snd _ _)).hom, (Spec.map_preimage _).symm⟩
  have hj : Z.j = Z.jQ ≫ pullback.fst _ _ := rfl
  have e : φ.comp α = ga.comp (algebraMap (𝓞 c.F) c.F) := by
    have h1 : spMap (φ.comp α) = spMap (ga.comp (algebraMap (𝓞 c.F) c.F)) := by
      rw [← spc, ← spc, ← hα, ← hga, reassoc_of% h, hj]
      simp only [Category.assoc, pullback.condition]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective (a₁ := CommRingCat.ofHom _) (a₂ := CommRingCat.ofHom _) h1)
  have hu : ∀ s : nonZeroDivisors (𝓞 c.F), IsUnit (α s) := fun s => by
    refine IsUnit.of_map φ _ ?_
    rw [← RingHom.comp_apply, e]
    exact (IsLocalization.map_units c.F s).map ga
  let α' : c.F →+* R := IsLocalization.lift hu
  have hα' : α'.comp (algebraMap (𝓞 c.F) c.F) = α := IsLocalization.lift_comp _
  let xg : Sp R ⟶ pullback Z.s (spMap (algebraMap (𝓞 c.F) c.F)) := pullback.lift x (spMap α') (by rw [hα, spc, hα'])
  have hg : spMap φ ≫ xg = y ≫ Z.jQ := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, h, hj, Category.assoc]
    · rw [Category.assoc, pullback.lift_snd, Category.assoc, hga, spc]
      exact congrArg spMap (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) (by rw [RingHom.comp_assoc, hα', e]))
  haveI := Z.jQ_open
  have hmem : xg (IsLocalRing.closedPoint R) ∈ Set.range Z.jQ := by
    refine ⟨y (IsLocalRing.closedPoint C), ?_⟩
    have h1 : ∀ pt : Sp C, Z.jQ (y pt) = xg (spMap φ pt) := fun pt => by
      rw [← Scheme.Hom.comp_apply, ← hg, Scheme.Hom.comp_apply]
    exact (h1 _).trans (congrArg xg (IsLocalRing.comap_closedPoint φ))
  have hr : Set.range xg ⊆ Set.range Z.jQ := by
    rintro _ ⟨p, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint p).map xg.continuous).mem_open Z.jQ.isOpenEmbedding.isOpen_range hmem
  exact ⟨IsOpenImmersion.lift Z.jQ xg hr, by rw [hj, IsOpenImmersion.lift_fac_assoc, pullback.lift_fst]⟩

private theorem mono_j (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) : Mono Z.j := by
  haveI := Z.jQ_open
  haveI : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) := IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F))
  rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j]
  infer_instance

end UpperTheory.SpecLab

open UpperTheory.SpecLab GlobalTheory.HTMap GlobalTheory.HtChar GlobalTheory.HtGen in
theorem UpperTheory.torsion_labels_on_separated_model :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) [IsLocallyNoetherian Z.X], Z.X.IsSeparated → ∀ (K : Type) [Field K] [CharZero K] (y₀ : Sp K ⟶ Xo.XF c) (q : ℕ), q ≠ 0 → GlobalTheory.HtGen.SplitK Z.t (y₀ ≫ Z.j) q → ∀ (lb : Dw.La → (Over.mk y₀ ⟶ Z.oF.t.G)) (ζ : Kˣ), IsLabel Z y₀ q lb ζ → ∀ χ : Dw.La → (GlobalTheory.HtGen.TorsK Z.t (y₀ ≫ Z.j) q →* Kˣ), (∀ a b (k : GlobalTheory.HtGen.TorsK Z.t (y₀ ≫ Z.j) q), k.1.left = (lb b).left ≫ Z.m.φ → χ a k = ζ ^ Dw.EF a b) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsLocalRing R] [Algebra R K] [IsFractionRing R K] (x : Sp R ⟶ Z.X), spMap (algebraMap R K) ≫ x = y₀ ≫ Z.j → ∀ (p : ℕ) [Fact p.Prime] (ψ : R →+* ↥(intO ℂ_[p])) (z : Sp ↥(intO ℂ_[p]) ⟶ Z.X) (y : Sp ℂ_[p] ⟶ Xo.XF c), IsLocalHom ψ → spMap ψ ≫ x = z → spMap (intO ℂ_[p]).subtype ≫ z = y ≫ Z.j → ∀ ch : Dw.La → TorsChar Z.t z q, (∀ a, GlobalTheory.HtGen.InducedBy (χ a) x (algebraMap R K) ψ (ch a)) → WeilLab Z (intO ℂ_[p]).subtype z y q ch := by
  intro E _ _ _ H Dw l Xo c Z _ _ K _ _ y₀ q hq hs lb ζ hl χ hχ R _ _ _ _ _ _ x hx p _ ψ z y hψ hz hy ch hch
  haveI := GlobalTheory.LatDRFree.intO_isLocalRing ℂ_[p]
  haveI := mono_j Z
  have hinj := IsFractionRing.injective R K
  let φ₀ : R →+* ℂ_[p] := (intO ℂ_[p]).subtype.comp ψ
  let 𝔮 : Ideal R := RingHom.ker φ₀
  haveI : 𝔮.IsPrime := RingHom.ker_isPrime φ₀
  let R' := Localization.AtPrime 𝔮
  have hφu : ∀ s : 𝔮.primeCompl, IsUnit (φ₀ s) := fun s => IsUnit.mk0 _ fun h0 => s.2 (RingHom.mem_ker.2 h0)
  let φ : R' →+* ℂ_[p] := IsLocalization.lift (M := 𝔮.primeCompl) hφu
  have hφ : φ.comp (algebraMap R R') = φ₀ := IsLocalization.lift_comp _
  haveI : IsLocalHom φ := ⟨fun a ha => by
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔮.primeCompl a
    refine (IsLocalization.AtPrime.isUnit_mk'_iff R' 𝔮 r s).2 fun hr => ha.ne_zero ?_
    exact (IsLocalization.lift_mk'_spec hφu _ _ _).2 (by rw [mul_zero]; exact hr)⟩
  have hKu : ∀ s : 𝔮.primeCompl, IsUnit (algebraMap R K s) := fun s => IsUnit.mk0 _ fun h0 => s.2 (by
    rw [hinj (h0.trans (map_zero _).symm)]; exact 𝔮.zero_mem)
  let io : R' →+* K := IsLocalization.lift (M := 𝔮.primeCompl) hKu
  have hio : io.comp (algebraMap R R') = algebraMap R K := IsLocalization.lift_comp _
  letI : Algebra R' K := io.toAlgebra
  haveI : IsScalarTower R R' K := IsScalarTower.of_algebraMap_eq' hio.symm
  haveI : IsFractionRing R' K := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization 𝔮.primeCompl R' K
  haveI : IsIntegrallyClosed R' := isIntegrallyClosed_of_isLocalization _ _ 𝔮.primeCompl_le_nonZeroDivisors
  have hyC : spMap φ ≫ spMap (algebraMap R R') ≫ x = y ≫ Z.j := by rw [spc_assoc, hφ, ← hy, ← hz, spc_assoc]
  obtain ⟨yq, hyq⟩ := factor Z φ _ y hyC
  have h₀ : spMap (algebraMap R' K) ≫ yq = y₀ := by
    rw [← cancel_mono Z.j, Category.assoc, ← hyq, spc_assoc, ← hx]
    exact congrArg (fun f => spMap f ≫ x) hio
  have hC : spMap φ ≫ yq = y := by rw [← cancel_mono Z.j, Category.assoc, ← hyq, hyC]
  obtain ⟨s, hs1, hs2⟩ := extend Z hq yq h₀ hs hl φ hC
  obtain ⟨ζR, hζR⟩ := root_mem (R := R) hq (u := (ζ : K))
    (by rw [← Units.val_pow_eq_pow_val, hl.1.pow_eq_one, Units.val_one])
  have hζu : IsUnit ζR := IsUnit.of_pow_eq_one (n := q) (hinj (by
    rw [map_pow, hζR, map_one, ← Units.val_pow_eq_pow_val, hl.1.pow_eq_one, Units.val_one])) hq
  obtain ⟨u, rfl⟩ := hζu
  obtain rfl : ζ = Units.map (algebraMap R' K).toMonoidHom (Units.map (algebraMap R R').toMonoidHom u) :=
    Units.ext (hζR.symm.trans (RingHom.congr_fun hio _).symm)
  have hL := label_at Z hq (algebraMap R' K) (IsFractionRing.injective R' K) yq h₀ _ hl φ hC s hs1 hs2
  refine ⟨_, _, hL, fun a b w hw hb => ?_⟩
  obtain ⟨σ, hσ, hwσ⟩ := sect (K := K) Z.t hq x (by rw [hx]; exact hs) ψ
    (by rw [← hz, spc_assoc, Algebra.algebraMap_self, RingHom.id_comp]) w hw
  obtain ⟨τ, hτ, hτσ⟩ := cart_lift Z yq hyq (pull _ rfl σ) (by rw [← map_pow, hσ, map_one])
  rw [pull_left] at hτσ
  obtain ⟨b', hb'⟩ := (hl.2.2.2.1 (pull _ h₀ τ)).1 (by rw [← map_pow, hτ, map_one])
  obtain rfl : τ = s b' := gen_inj Z _ (IsFractionRing.injective R' K)
    (congrArg (fun v => v.left) (hb'.symm.trans (hs1 b').2.symm))
  have hbb : pull _ hC (s b) = pull _ hC (s b') := cart_inj Z (by
    rw [hb, pull_left, Category.assoc, hτσ, hwσ, spc_assoc, spc_assoc, hφ])
  rw [lab_pow hL hbb]
  let k : TorsK Z.t (y₀ ≫ Z.j) q := ⟨pull _ hx σ, MonoidHom.mem_ker.2 (by rw [powMonoidHom_apply, ← map_pow, hσ, map_one])⟩
  have hk := hχ a b' k (by
    rw [hb', pull_left _ h₀, Category.assoc, hτσ, spc_assoc]
    exact congrArg (fun f => spMap f ≫ σ.left) hio.symm)
  rw [hch a σ k ((u ^ Dw.EF a b' : Rˣ) : R) w hσ rfl hwσ (by
    rw [hk, ← map_zpow, ← map_zpow]; exact (RingHom.congr_fun hio _).symm), ← map_zpow, ← map_zpow]
  exact (RingHom.congr_fun hφ _).symm
