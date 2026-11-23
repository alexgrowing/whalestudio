import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsChartPtChartPt
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS
noncomputable section
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.CechKS

theorem exists_ringHom_add_eps_mul {R B : Type} [CommRing R] [CommRing B] {n : ℕ} (e : R →+* B)
    (e' : Fin n → (R →+* DualNumber B)) (he : ∀ a f, (e' a f).fst = e f) (δ : R → R)
    (hδa : ∀ f f', δ (f + f') = δ f + δ f') (hδm : ∀ f f', δ (f * f') = f * δ f' + f' * δ f)
    (c : Fin n → B) (ε : B) (hε : ε * ε = 0) :
    ∃ ψ : R →+* B, ∀ f, ψ f = e f + ε * (e (δ f) + ∑ a, c a * (e' a f).snd) := by
  have h1 : δ 1 = 0 := by
    have := hδm 1 1
    simp only [_root_.one_mul, _root_.mul_one] at this
    linear_combination -this
  have h0 : δ 0 = 0 := by
    have := hδa 0 0
    rw [add_zero] at this
    linear_combination -this
  refine ⟨{ toFun := fun f => e f + ε * (e (δ f) + ∑ a, c a * (e' a f).snd),
            map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, fun f => rfl⟩
  · simp [h1]
  · intro f f'
    simp only [hδm, map_add, map_mul, TrivSqZeroExt.snd_mul, he, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op]
    have hs : ∑ x, c x * (e f * TrivSqZeroExt.snd ((e' x) f') + TrivSqZeroExt.snd ((e' x) f) * e f') =
        e f * ∑ a, c a * TrivSqZeroExt.snd ((e' a) f') + e f' * ∑ a, c a * TrivSqZeroExt.snd ((e' a) f) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [hs]
    linear_combination (-(e (δ f) + ∑ a, c a * (e' a f).snd) * (e (δ f') + ∑ a, c a * (e' a f').snd)) * hε
  · simp [h0]
  · intro f f'
    simp only [hδa, map_add, TrivSqZeroExt.snd_add, mul_add, Finset.sum_add_distrib]
    ring

theorem fst_comp_tangent_eq_one : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
    (U : X.affineOpens) (v : Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left) (hv : IsTanAtG t (LogKS.chart U) v)
    {K : Type} [Field K] (x0 : Sp K ⟶ X) (hU : ⊤ ≤ x0 ⁻¹ᵁ U.1) (A : Over (Sp K)) [GrpObj A]
    (m : A.left ⟶ t.G.left) (hm : IsGrpPullback A t.G x0 m) (u : epsR K ⟶ A)
    (hu : u.left ≫ m = spMap (dualMap (ev x0 U.1 hU)) ≫ v),
    spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ u.left = (1 : Over.mk (𝟙 (Sp K)) ⟶ A).left := by
  intro E _ _ _ H X t U v hv K _ x0 hU A _ m hm u hu
  have hv2 : spMap (TrivSqZeroExt.fstHom Γ(X, U.1) Γ(X, U.1) Γ(X, U.1)).toRingHom ≫ v =
      (1 : Over.mk (LogKS.chart U) ⟶ t.G).left := hv.2
  have hux : spMap (ev x0 U.1 hU) ≫ LogKS.chart U = x0 := GlobalTheory.FlagMod.spMap_ev x0 U.2 hU
  let κ : Over.mk x0 ⟶ Over.mk (LogKS.chart U) := Over.homMk (spMap (ev x0 U.1 hU)) hux

  have hG1 : (spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ u.left) ≫ m = (1 : Over.mk x0 ⟶ t.G).left := by
    rw [Category.assoc, hu, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have e : (TrivSqZeroExt.fstHom K K K).toRingHom.comp (dualMap (ev x0 U.1 hU)) =
        (ev x0 U.1 hU).comp ((TrivSqZeroExt.fstHom Γ(X, U.1) Γ(X, U.1) Γ(X, U.1)).toRingHom) := by
      ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    rw [e, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hv2]
    have := congrArg Over.Hom.left (comp_one (M := t.G) κ)
    exact this.symm ▸ rfl
  have hA1 : (1 : Over.mk (𝟙 (Sp K)) ⟶ A).left ≫ m = (1 : Over.mk x0 ⟶ t.G).left := by
    have hw : ((1 : Over.mk (𝟙 (Sp K)) ⟶ A).left ≫ m) ≫ t.G.hom = (Over.mk ((Over.mk (𝟙 (Sp K))).hom ≫ x0)).hom := by
      rw [Category.assoc, hm.1.w, ← Category.assoc, Over.w (1 : Over.mk (𝟙 (Sp K)) ⟶ A)]
      rfl
    let z : Over.mk ((Over.mk (𝟙 (Sp K))).hom ≫ x0) ⟶ t.G := Over.homMk ((1 : Over.mk (𝟙 (Sp K)) ⟶ A).left ≫ m) hw
    have hz : (z * z).left = z.left := by
      have := hm.2 (Over.mk (𝟙 (Sp K))) 1 1 z z rfl rfl
      rw [this, _root_.mul_one]
      rfl
    have hz1 : z = 1 := by
      have : z * z = z := Over.OverMorphism.ext hz
      simpa using this
    let κ' : Over.mk x0 ⟶ Over.mk ((Over.mk (𝟙 (Sp K))).hom ≫ x0) := Over.homMk (𝟙 _) (by simp)
    have := congrArg Over.Hom.left (comp_one (M := t.G) κ')
    calc _ = (κ' ≫ z).left := by simp [κ', z]
      _ = _ := by rw [hz1]; exact this
  have hA2 : (spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ u.left) ≫ A.hom = 𝟙 (Sp K) := by
    rw [Category.assoc, Over.w u]; show spMap _ ≫ spMap (algebraMap K (DualNumber K)) = 𝟙 _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have e3 : (TrivSqZeroExt.fstHom K K K).toRingHom.comp (algebraMap K (DualNumber K)) = RingHom.id K := by
      ext a; simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [e3, CommRingCat.ofHom_id, Spec.map_id]
  refine hm.1.hom_ext (hG1.trans hA1.symm) (hA2.trans ?_)
  exact (Over.w (1 : Over.mk (𝟙 (Sp K)) ⟶ A)).symm

theorem fst_comp_transl_eq : ∀ {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {B : Type} [CommRing B] (φ : K →+* B)
    (x : Sp B ⟶ A.left) (v : epsR K ⟶ A)
    (hv : spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ v.left = (1 : Over.mk (𝟙 (Sp K)) ⟶ A).left)
    (w : Sp (DualNumber B) ⟶ A.left), IsTransl φ x v w → spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ w = x := by
  intro K _ A _ B _ φ x v hv w ⟨x', v', hx', hv', hw⟩
  have hio : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ spMap ((algebraMap B (DualNumber B)).comp φ) = spMap φ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
  let io : Over.mk (spMap φ) ⟶ Over.mk (spMap ((algebraMap B (DualNumber B)).comp φ)) :=
    Over.homMk (spMap (TrivSqZeroExt.fstHom B B B).toRingHom) hio
  have hνw : (spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ v.left) ≫ A.hom = (Over.mk (𝟙 (Sp K))).hom := by
    rw [Category.assoc, Over.w v]; show spMap _ ≫ spMap (algebraMap K (DualNumber K)) = 𝟙 _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have e3 : (TrivSqZeroExt.fstHom K K K).toRingHom.comp (algebraMap K (DualNumber K)) = RingHom.id K := by
      ext a; simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [e3, CommRingCat.ofHom_id, Spec.map_id]
  let ν : Over.mk (𝟙 (Sp K)) ⟶ A := Over.homMk (spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ v.left) hνw
  have hν : ν = 1 := Over.OverMorphism.ext hv
  let κ : Over.mk (spMap φ) ⟶ Over.mk (𝟙 (Sp K)) := Over.homMk (spMap φ) (Category.comp_id _)
  have h1 : io ≫ v' = 1 := by
    have : io ≫ v' = κ ≫ ν := by
      apply Over.OverMorphism.ext
      simp only [io, κ, ν, Over.comp_left, Over.homMk_left, hv']
      rw [← Category.assoc, ← Category.assoc]
      congr 1
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    rw [this, hν, comp_one]
  have h2 : (io ≫ (x' * v')).left = x := by
    rw [comp_mul, h1, _root_.mul_one]
    simp only [io, Over.comp_left, Over.homMk_left, hx']
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (TrivSqZeroExt.fstHom B B B).toRingHom.comp (algebraMap B (DualNumber B)) = RingHom.id B := by
      ext a; simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [this, CommRingCat.ofHom_id, Spec.map_id]
    exact Category.id_comp x
  rw [← hw]
  exact h2

theorem top_le_preimage_of_fst : ∀ {B : Type} [CommRing B] {Z : Scheme.{0}} (z : Sp (DualNumber B) ⟶ Z) (V : Z.Opens),
    ⊤ ≤ (spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ z) ⁻¹ᵁ V → ⊤ ≤ z ⁻¹ᵁ V := by
  intro B _ Z z V h p _
  have hp : (spMap (TrivSqZeroExt.fstHom B B B).toRingHom) ((spMap (algebraMap B (DualNumber B))) p) = p := by
    show PrimeSpectrum.comap _ (PrimeSpectrum.comap _ p) = p
    ext y
    show (algebraMap B (DualNumber B)) (TrivSqZeroExt.fst y) ∈ p.asIdeal ↔ y ∈ p.asIdeal
    rw [TrivSqZeroExt.algebraMap_eq_inl]
    have hy : y = TrivSqZeroExt.inl y.fst + TrivSqZeroExt.inr y.snd := (TrivSqZeroExt.inl_fst_add_inr_snd_eq y).symm
    have hn : TrivSqZeroExt.inr y.snd ∈ p.asIdeal := by
      apply p.isPrime.mem_of_pow_mem 2
      rw [pow_two, TrivSqZeroExt.inr_mul_inr]
      exact p.asIdeal.zero_mem
    constructor
    · intro h1
      rw [hy]
      exact p.asIdeal.add_mem h1 hn
    · intro h1
      have : TrivSqZeroExt.inl y.fst = y - TrivSqZeroExt.inr y.snd :=
        eq_sub_of_add_eq (TrivSqZeroExt.inl_fst_add_inr_snd_eq y)
      rw [this]
      exact p.asIdeal.sub_mem h1 hn
  have := h (Set.mem_univ ((spMap (algebraMap B (DualNumber B))) p))
  show z p ∈ V
  rw [← hp]
  exact this

theorem comp_hom_of_isTransl {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {B : Type} [CommRing B] (φ : K →+* B)
    (x : Sp B ⟶ A.left) (v : epsR K ⟶ A) (w : Sp (DualNumber B) ⟶ A.left) (hw : IsTransl φ x v w) :
    w ≫ A.hom = spMap ((algebraMap B (DualNumber B)).comp φ) := by
  obtain ⟨x', v', -, -, rfl⟩ := hw
  exact Over.w (x' * v')

theorem exists_isChartPt : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X) (U : X.affineOpens) {n : ℕ} (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (D : Γ(X, U.1) → Γ(X, U.1)) (hv : ∀ a, IsTanAtG t (LogKS.chart U) (v a)) (W₀ : t.G.left.Opens) (hW₀ : W₀ ≤ t.G.hom ⁻¹ᵁ U.1) (d : ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)) (hd : LogKS.IsField W₀ d) (hlift : ∀ r, d W₀ ((t.G.hom.appLE U.1 W₀ hW₀).hom r) = (t.G.hom.appLE U.1 W₀ hW₀).hom (D r)) {K : Type} [Field K] (x0 : Sp K ⟶ X) (hU : ⊤ ≤ x0 ⁻¹ᵁ U.1) (y1 : Sp (DualNumber K) ⟶ X) (hU' : ⊤ ≤ y1 ⁻¹ᵁ U.1) (hy1 : ∀ r, ev y1 U.1 hU' r = TrivSqZeroExt.inl (ev x0 U.1 hU r) + TrivSqZeroExt.inr (ev x0 U.1 hU (D r))) (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (m : A.left ⟶ t.G.left) (m' : A'.left ⟶ t.G.left) (u : Fin n → (epsR K ⟶ A)) (hm : IsGrpPullback A t.G x0 m) (hm' : IsGrpPullback A' t.G y1 m') (hu : ∀ a, (u a).left ≫ m = spMap (dualMap (ev x0 U.1 hU)) ≫ v a) (Ω : t.G.left.affineOpens) (hΩ : Ω.1 ≤ W₀) (θ : Matrix (Fin n) (Fin n) K) (Wo : A.left.Opens) (g : Γ(A.left, Wo)ˣ) (B : Type) [CommRing B] [Algebra (DualNumber K) B] (x : Sp B ⟶ A.left) (hx : x ≫ A.hom = spMap (baseMap K B)) (hxΩ : ⊤ ≤ x ⁻¹ᵁ (m ⁻¹ᵁ Ω.1)), ∃ l, IsChartPt A' m m' Ω.1 (d Ω.1) u θ Wo g x l := by
  intro E _ _ _ H X t U n v D hv W₀ hW₀ d hd hlift K _ x0 hU y1 hU' hy1 A _ A' _ m m' u hm hm' hu Ω hΩ θ Wo g B _ _ x hx hxΩ
  have hwT : ∀ a, IsTransl (baseMap K B) x (u a) (transl (baseMap K B) x (u a)) :=
    fun a => isTransl_transl (baseMap K B) x hx (u a)
  have hred : ∀ a, spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ transl (baseMap K B) x (u a) = x := fun a =>
    fst_comp_transl_eq (baseMap K B) x (u a) (fst_comp_tangent_eq_one t U (v a) (hv a) x0 hU A m hm (u a) (hu a)) _ (hwT a)
  have hxm : ⊤ ≤ (x ≫ m) ⁻¹ᵁ Ω.1 := GlobalTheory.FlagMod.le_preimage_map m le_rfl hxΩ
  have hwm : ∀ a, ⊤ ≤ (transl (baseMap K B) x (u a) ≫ m) ⁻¹ᵁ Ω.1 := fun a =>
    top_le_preimage_of_fst _ Ω.1 (by rw [← Category.assoc, hred a]; exact hxm)
  have he : ∀ a f, (ev (transl (baseMap K B) x (u a) ≫ m) Ω.1 (hwm a) f).fst = ev (x ≫ m) Ω.1 hxm f := by
    intro a f
    have := GlobalTheory.FlagMod.ev_spMap (TrivSqZeroExt.fstHom B B B).toRingHom (transl (baseMap K B) x (u a) ≫ m) Ω.1 (hwm a)
      (by rw [← Category.assoc, hred a]; exact hxm)
    have e1 := GlobalTheory.FlagMod.ev_congr (show spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫
      (transl (baseMap K B) x (u a) ≫ m) = x ≫ m by rw [← Category.assoc, hred a]) Ω.1
      (by rw [← Category.assoc, hred a]; exact hxm) hxm
    rw [e1] at this
    rw [this]
    rfl
  have hdΩ := hd.2.1 Ω.1 hΩ
  obtain ⟨ψ, hψ⟩ := exists_ringHom_add_eps_mul (ev (x ≫ m) Ω.1 hxm) (fun a => ev (transl (baseMap K B) x (u a) ≫ m) Ω.1 (hwm a)) he
    (d Ω.1) (hd.1 Ω.1 hΩ) (hd.2.1 Ω.1 hΩ) (fun a => ∑ b, baseMap K B (θ a b) * dlogAt (baseMap K B) x (u b) Wo g)
    (algebraMap (DualNumber K) B DualNumber.eps) (by rw [← map_mul, DualNumber.eps_mul_eps, map_zero])
  have hψ' : ∀ f, ψ f = chartVal m Ω.1 (d Ω.1) u θ Wo g x f := by
    intro f
    rw [hψ f, chartVal, valR_eq_ev _ _ hxm, valR_eq_ev _ _ hxm]
    simp only [valR_eq_ev _ _ (hwm _)]
  set q : Sp B ⟶ t.G.left := spMap ψ ≫ Ω.2.fromSpec with hq_def
  have hqΩ : ⊤ ≤ q ⁻¹ᵁ Ω.1 := GlobalTheory.FlagMod.le_preimage_comp _ (GlobalTheory.FlagMod.tau_le Ω.2 le_rfl)
  have hevq : ev q Ω.1 hqΩ = ψ := GlobalTheory.FlagMod.ev_spMap_tau Ω.2 ψ hqΩ
  have hΩU : Ω.1 ≤ t.G.hom ⁻¹ᵁ U.1 := hΩ.trans hW₀
  have key : ∀ {S : Type} [CommRing S] (ρ : K →+* S) (z : Sp S ⟶ A.left) (hz : z ≫ A.hom = spMap ρ)
      (hzΩ : ⊤ ≤ (z ≫ m) ⁻¹ᵁ Ω.1) (r : Γ(X, U.1)),
      ev (z ≫ m) Ω.1 hzΩ ((t.G.hom.appLE U.1 Ω.1 hΩU).hom r) = ρ (ev x0 U.1 hU r) := by
    intro S _ ρ z hz hzΩ r
    have h1 : (z ≫ m) ≫ t.G.hom = spMap ρ ≫ x0 := by
      rw [Category.assoc, hm.1.w, ← Category.assoc, hz]
    rw [GlobalTheory.FlagMod.ev_appLE (z ≫ m) t.G.hom hΩU hzΩ (GlobalTheory.FlagMod.le_preimage_map t.G.hom hΩU hzΩ) r,
      GlobalTheory.FlagMod.ev_congr h1 U.1 _ (GlobalTheory.FlagMod.le_preimage_comp _ hU), GlobalTheory.FlagMod.ev_spMap ρ x0 U.1 hU]
    rfl
  have hres : ∀ r, resG t.G.left hΩ ((t.G.hom.appLE U.1 W₀ hW₀).hom r) = (t.G.hom.appLE U.1 Ω.1 hΩU).hom r := by
    intro r
    rw [resG, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  have hdr : ∀ r, d Ω.1 ((t.G.hom.appLE U.1 Ω.1 hΩU).hom r) = (t.G.hom.appLE U.1 Ω.1 hΩU).hom (D r) := by
    intro r
    rw [← hres, hd.2.2 W₀ Ω.1 hΩ le_rfl, hlift, hres]
  have hU1 : ⊤ ≤ (q ≫ t.G.hom) ⁻¹ᵁ U.1 := GlobalTheory.FlagMod.le_preimage_map t.G.hom hΩU hqΩ
  have hU2 : ⊤ ≤ (spMap (algebraMap (DualNumber K) B) ≫ y1) ⁻¹ᵁ U.1 := GlobalTheory.FlagMod.le_preimage_comp _ hU'
  have hq : q ≫ t.G.hom = spMap (algebraMap (DualNumber K) B) ≫ y1 := by
    rw [← GlobalTheory.FlagMod.spMap_ev (q ≫ t.G.hom) U.2 hU1, ← GlobalTheory.FlagMod.spMap_ev (spMap (algebraMap (DualNumber K) B) ≫ y1) U.2 hU2]
    suffices e : ev (q ≫ t.G.hom) U.1 hU1 = ev (spMap (algebraMap (DualNumber K) B) ≫ y1) U.1 hU2 by rw [e]
    ext r
    rw [← GlobalTheory.FlagMod.ev_appLE q t.G.hom hΩU hqΩ hU1 r, hevq, hψ, GlobalTheory.FlagMod.ev_spMap _ y1 U.1 hU' hU2,
      RingHom.comp_apply, hy1 r, hdr, key (baseMap K B) x hx hxm, key (baseMap K B) x hx hxm]
    have hw0 : ∀ a, (ev (transl (baseMap K B) x (u a) ≫ m) Ω.1 (hwm a) ((t.G.hom.appLE U.1 Ω.1 hΩU).hom r)).snd = 0 := by
      intro a
      rw [key _ _ (comp_hom_of_isTransl _ x (u a) _ (hwT a)) (hwm a) r]
      simp [TrivSqZeroExt.algebraMap_eq_inl]
    simp only [hw0, mul_zero, Finset.sum_const_zero, add_zero]
    rw [map_add, DualNumber.inr_eq_smul_eps, Algebra.smul_def, map_mul, baseMap, RingHom.comp_apply,
      RingHom.comp_apply, mul_comm, TrivSqZeroExt.algebraMap_eq_inl]
  obtain ⟨l, hl1, hl2⟩ := hm'.1.exists_lift q (spMap (algebraMap (DualNumber K) B)) hq
  refine ⟨l, hl2, ?_, ?_⟩
  · rw [hl1]; exact hqΩ
  · intro f
    rw [← hψ' f, valR_eq_ev _ _ (by rw [hl1]; exact hqΩ)]
    rw [GlobalTheory.FlagMod.ev_congr hl1 Ω.1 _ hqΩ, hevq]

end GlobalTheory.CechKS

end
