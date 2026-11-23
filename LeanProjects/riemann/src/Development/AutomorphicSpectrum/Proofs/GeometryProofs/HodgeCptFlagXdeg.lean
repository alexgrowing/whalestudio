import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorFlagStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductConjugateStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalRingPointsExistsUniqueStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeLine

open scoped ComplexConjugate

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

section Val

variable {R : Type} [CommRing R] [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X}

theorem valAt_unique (hg : IsCptGen ξ) {a : Ω} {r r' : R} (h : ValAt ξ z a r) (h' : ValAt ξ z a r') :
    r = r' := by
  obtain ⟨h1, s, hs, rfl⟩ := h
  obtain ⟨h2, s', hs', rfl⟩ := h'
  have : s = s' := hg.inj ⟨centre z, h1⟩ (hs.trans hs'.symm)
  rw [this]

theorem valAt_mul {a b : Ω} {r r' : R} (h : ValAt ξ z a r) (h' : ValAt ξ z b r') :
    ValAt ξ z (a * b) (r * r') := by
  obtain ⟨h1, s, rfl, rfl⟩ := h
  obtain ⟨h2, s', rfl, rfl⟩ := h'
  exact ⟨h1, s * s', map_mul _ _ _, map_mul _ _ _⟩

theorem valAt_one (h : genPt ξ ⤳ centre z) : ValAt ξ z (1 : Ω) (1 : R) :=
  ⟨h, 1, map_one _, map_one _⟩

theorem valAt_of_mem {a : Ω} (h : genPt ξ ⤳ centre z) (ha : a ∈ regAt ξ ⟨centre z, h⟩) :
    ∃ r : R, ValAt ξ z a r := by
  obtain ⟨s, rfl⟩ := ha
  exact ⟨_, h, s, rfl, rfl⟩

theorem mem_of_valAt {a : Ω} {r : R} (h : ValAt ξ z a r) (h' : genPt ξ ⤳ centre z) :
    a ∈ regAt ξ ⟨centre z, h'⟩ := by
  obtain ⟨h1, s, rfl, rfl⟩ := h
  exact ⟨s, rfl⟩

end Val

section Cx

variable {z : Spec (CommRingCat.of ℂ) ⟶ X}

theorem valAt_inv {a : Ω} {r : ℂ} (h : ValAt ξ z a r) (hr : r ≠ 0) : ValAt ξ z a⁻¹ r⁻¹ := by
  obtain ⟨h1, s, rfl, rfl⟩ := h
  have hu : IsUnit s := (Scheme.isLocalHom_stalkClosedPointTo' z).map_nonunit s (IsUnit.mk0 _ hr)
  obtain ⟨s', hs'⟩ := hu.exists_right_inv
  have e1 : genMap ξ ⟨centre z, h1⟩ s * genMap ξ ⟨centre z, h1⟩ s' = 1 :=
    (map_mul (genMap ξ ⟨centre z, h1⟩) s s').symm.trans (by rw [hs', map_one])
  have e2 : (Scheme.stalkClosedPointTo z).hom s * (Scheme.stalkClosedPointTo z).hom s' = 1 :=
    (map_mul (Scheme.stalkClosedPointTo z).hom s s').symm.trans ((congrArg _ hs').trans (map_one _))
  exact ⟨h1, s', (eq_inv_of_mul_eq_one_right e1), (eq_inv_of_mul_eq_one_right e2)⟩

theorem valAt_zpow {a : Ω} {r : ℂ} (h : ValAt ξ z a r) (hr : r ≠ 0) (hz : genPt ξ ⤳ centre z) (n : ℤ) :
    ValAt ξ z (a ^ n) (r ^ n) := by
  have hn : ∀ {b : Ω} {q : ℂ}, ValAt ξ z b q → ∀ m : ℕ, ValAt ξ z (b ^ m) (q ^ m) := by
    intro b q hb m
    induction m with
    | zero => simpa using valAt_one hz
    | succ m ih => simpa [pow_succ] using valAt_mul ih hb
  cases n with
  | ofNat m => simpa using hn h m
  | negSucc m => simpa [zpow_negSucc] using valAt_inv (hn h (m + 1)) (pow_ne_zero _ hr)

theorem exists_valAt_of_unit {a : Ω} (h : genPt ξ ⤳ centre z) (ha : unitAt ξ ⟨centre z, h⟩ a)
    (hg : IsCptGen ξ) : ∃ r : ℂ, r ≠ 0 ∧ ValAt ξ z a r := by
  obtain ⟨h0, h1, h2⟩ := ha
  obtain ⟨r, hr⟩ := valAt_of_mem (R := ℂ) (z := z) h h1
  obtain ⟨r', hr'⟩ := valAt_of_mem (R := ℂ) (z := z) h h2
  refine ⟨r, ?_, hr⟩
  rintro rfl
  have := valAt_mul hr hr'
  rw [mul_inv_cancel₀ h0, zero_mul] at this
  exact zero_ne_one (valAt_unique hg this (valAt_one h))

abbrev cj (z : Spec (CommRingCat.of ℂ) ⟶ X) : Spec (CommRingCat.of ℂ) ⟶ X := spMap (starRingEnd ℂ) ≫ z

theorem conj_transport (z : Spec (CommRingCat.of ℂ) ⟶ X)
    (P : ∀ q : X, (X.presheaf.stalk q ⟶ CommRingCat.of ℂ) → Prop)
    (h : P (centre z) (Scheme.stalkClosedPointTo z ≫ CommRingCat.ofHom (starRingEnd ℂ))) :
    P (centre (cj z)) (Scheme.stalkClosedPointTo (cj z)) := by
  have hl : IsLocalHom (Scheme.stalkClosedPointTo z ≫ CommRingCat.ofHom (starRingEnd ℂ)).hom := by
    refine ⟨fun a ha => (Scheme.isLocalHom_stalkClosedPointTo' z).map_nonunit a ?_⟩
    have h0 : (starRingEnd ℂ) ((Scheme.stalkClosedPointTo z).hom a) ≠ 0 := ha.ne_zero
    exact IsUnit.mk0 _ fun h1 => h0 (by rw [h1, map_zero])
  have hz : Spec.map (Scheme.stalkClosedPointTo z) ≫ X.fromSpecStalk (centre z) = z :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk z
  have key : SpecToEquivOfLocalRing X (.of ℂ) (cj z) =
      ⟨centre z, Scheme.stalkClosedPointTo z ≫ CommRingCat.ofHom (starRingEnd ℂ), hl⟩ := by
    rw [Equiv.apply_eq_iff_eq_symm_apply]
    show _ = Spec.map (Scheme.stalkClosedPointTo z ≫ CommRingCat.ofHom (starRingEnd ℂ)) ≫ X.fromSpecStalk (centre z)
    rw [Spec.map_comp]
    exact (congrArg (fun t => spMap (starRingEnd ℂ) ≫ t) hz).symm.trans (Category.assoc _ _ _).symm
  exact (congrArg (fun s : (Σ q : X, {f : X.presheaf.stalk q ⟶ CommRingCat.of ℂ // IsLocalHom f.hom}) =>
    P s.1 s.2.1) key).mpr h

theorem centre_cj (z : Spec (CommRingCat.of ℂ) ⟶ X) : centre (cj z) = centre z :=
  conj_transport z (fun q _ => q = centre z) rfl

theorem valAt_conj {a : Ω} {u : ℂ} (h : ValAt ξ z a u) : ValAt ξ (cj z) a (conj u) := by
  obtain ⟨h1, s, hs, rfl⟩ := h
  exact conj_transport z (fun q f => ∃ (h : genPt ξ ⤳ q) (s' : X.presheaf.stalk q), genMap ξ ⟨q, h⟩ s' = a ∧
    f.hom s' = conj ((Scheme.stalkClosedPointTo z).hom s)) ⟨h1, s, hs, rfl⟩

theorem cj_cj (z : Spec (CommRingCat.of ℂ) ⟶ X) : cj (cj z) = z := by
  have h : spMap (starRingEnd ℂ) ≫ spMap (starRingEnd ℂ) = 𝟙 (Sp ℂ) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := by
      ext x; simp
    rw [this]
    exact Spec.map_id _
  show spMap (starRingEnd ℂ) ≫ spMap (starRingEnd ℂ) ≫ z = z
  rw [← Category.assoc, h, Category.id_comp]

theorem coordsAt_conj {K : Type} {J : K → Type} {y : (Σ k, J k) → Ω} {w : (Σ k, J k) → ℂ}
    (h : CoordsAt ξ y z w) : CoordsAt ξ y (cj z) (fun p => conj (w p)) := by
  refine ⟨fun k => ?_, fun k c hc => ?_⟩
  · obtain ⟨c, hc⟩ := h.1 k
    exact ⟨c, hc.map (starRingEnd ℂ)⟩
  · have hu : IsUnit (w ⟨k, c⟩) := by
      refine IsUnit.mk0 _ fun h0 => hc.ne_zero ?_
      simp [h0]
    obtain ⟨h0, h1⟩ := h.2 k c hu
    refine ⟨h0, fun i => ?_⟩
    obtain ⟨r, hr, e⟩ := h1 i
    exact ⟨conj r, valAt_conj hr, by
      show conj (w ⟨k, i⟩) = conj r * conj (w ⟨k, c⟩)
      rw [e, map_mul]⟩

theorem dualMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : B →+* C) (g : A →+* B) :
    dualMap (f.comp g) = (dualMap f).comp (dualMap g) := by
  ext a <;> simp [dualMap]

theorem specMap_dual_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : B →+* C) (g : A →+* B) :
    Spec.map (CommRingCat.ofHom (dualMap (f.comp g))) =
      spMap (dualMap f) ≫ Spec.map (CommRingCat.ofHom (dualMap g)) := by
  rw [dualMap_comp, CommRingCat.ofHom_comp, Spec.map_comp]

def cjTan {G : Over X} (v : epsAt z ⟶ G) : epsAt (cj z) ⟶ G :=
  Over.homMk (spMap (dualMap (starRingEnd ℂ)) ≫ v.left) (by
    have hv : v.left ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ))) ≫ z := Over.w v
    have hc : (dualMap (starRingEnd ℂ)).comp (algebraMap ℂ (DualNumber ℂ)) =
        (algebraMap ℂ (DualNumber ℂ)).comp (starRingEnd ℂ) := by
      ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    have h2 : spMap (dualMap (starRingEnd ℂ)) ≫ spMap (algebraMap ℂ (DualNumber ℂ)) =
        spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap (starRingEnd ℂ) := by
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hc]
    show (spMap (dualMap (starRingEnd ℂ)) ≫ v.left) ≫ G.hom =
      spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap (starRingEnd ℂ) ≫ z
    rw [Category.assoc, hv, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ z) h2)

variable {Li : Type} [AddCommGroup Li] [Module Ω Li]

theorem lieVal_conj {G : Over X} [GrpObj G] (M : LieModel G ξ Li) {e : Li} {v : epsAt z ⟶ G}
    (h : M.ValAt z e v) : M.ValAt (cj z) e (cjTan v) := by
  obtain ⟨h1, v0, hv0, hv⟩ := h
  refine conj_transport z (fun q f => ∃ (h : genPt ξ ⤳ q)
    (v1 : epsAt (R := X.presheaf.stalk q) (X.fromSpecStalk q) ⟶ G), M.Extends ⟨q, h⟩ e v1 ∧
      (cjTan v).left = Spec.map (CommRingCat.ofHom (dualMap f.hom)) ≫ v1.left) ⟨h1, v0, hv0, ?_⟩
  have e2 : Spec.map (CommRingCat.ofHom (dualMap
      (Scheme.stalkClosedPointTo z ≫ CommRingCat.ofHom (starRingEnd ℂ)).hom)) =
      spMap (dualMap (starRingEnd ℂ)) ≫
        Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo z).hom)) :=
    specMap_dual_comp (starRingEnd ℂ) (Scheme.stalkClosedPointTo z).hom
  exact (congrArg (fun t => spMap (dualMap (starRingEnd ℂ)) ≫ t) hv).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ v0.left) e2.symm))

theorem leadMinor_conj {r : ℕ} (Γ : Matrix (Fin r) (Fin r) ℂ) (s : ℕ) :
    leadMinor (Γ.map (starRingEnd ℂ)) s = leadMinor Γ s := by
  unfold leadMinor
  split_ifs with h
  · have : (Γ.map (starRingEnd ℂ)).submatrix (Fin.castLE h) (Fin.castLE h) =
        (starRingEnd ℂ).mapMatrix (Γ.submatrix (Fin.castLE h) (Fin.castLE h)) := by
      ext i j; simp
    rw [this, ← RingHom.map_det]
    simp
  · rfl

open scoped ComplexOrder in
theorem isGrNorm_conj {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (T : SAB H X)
    (M : LieModel T.G ξ Li) (V : Lat ξ Li) {r : ℕ} {b₀ : Fin r → Li} {i : Fin r} {t : Ω} {ν : ℝ}
    (h : M.IsGrNorm T.PP.L V b₀ i z t ν) : M.IsGrNorm T.PP.L V b₀ i (cj z) t ν := by
  obtain ⟨h1, b, Γ, hs, hf, hb, ⟨v, hv, hΓ⟩, hpd, rfl⟩ := h
  have hc := centre_cj z
  have h1' : genPt ξ ⤳ centre (cj z) := hc ▸ h1
  refine ⟨h1', b, Γ.map (starRingEnd ℂ), hs, ?_, hb, ⟨fun i => cjTan (v i), fun i => lieVal_conj M (hv i),
    fun p q => GlobalTheory.T.hodge_inner_product_conjugate E H X T z (v p) (v q) _ _ _ rfl rfl (hΓ p q)⟩,
    (show Γ.transpose = Γ.map (starRingEnd ℂ) from Matrix.ext fun i j => (hpd.1.apply j i).symm) ▸ hpd.transpose, ?_⟩
  · have : (⟨centre (cj z), h1'⟩ : Cpt ξ) = ⟨centre z, h1⟩ := Subtype.ext hc
    rw [this]
    exact hf
  · rw [leadMinor_conj, leadMinor_conj]

def ChartNorm (ξ : Spec (CommRingCat.of Ω) ⟶ X) {K : Type} [Fintype K] {J : K → Type} (y : (Σ k, J k) → Ω)
    (a : K → ℤ) (e₀ : Ω) (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ) (t : Ω) (ν h : ℝ) : Prop :=
  ∀ c : (k : K) → J k, (∀ k, w ⟨k, c k⟩ ≠ 0) → ∃ u : ℂ, ValAt ξ z (t / ((∏ k, y ⟨k, c k⟩ ^ a k) * e₀)) u ∧
    ν * h = ‖u‖ * ∏ k, ‖w ⟨k, c k⟩‖ ^ a k

section Chart

variable {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} {a : K → ℤ} {e₀ : Ω}
  {w : (Σ k, J k) → ℂ} {t : Ω} {ν h : ℝ}

theorem ChartNorm.conj (H : ChartNorm ξ y a e₀ z w t ν h) :
    ChartNorm ξ y a e₀ (cj z) (fun p => conj (w p)) t ν h := by
  intro c hn
  obtain ⟨u, hu, e⟩ := H c fun k h0 => hn k (by simp [h0])
  refine ⟨conj u, valAt_conj hu, ?_⟩
  simpa [Complex.norm_conj] using e

theorem ChartNorm.smul (H : ChartNorm ξ y a e₀ z w t ν h) {κ : K → ℂ} (hκ : ∀ k, κ k ≠ 0) :
    ChartNorm ξ y a e₀ z (fun p => κ p.1 * w p) t ν ((∏ k, ‖κ k‖ ^ a k) * h) := by
  intro c hn
  obtain ⟨u, hu, e⟩ := H c fun k h0 => hn k (by simp [h0])
  refine ⟨u, hu, ?_⟩
  have e2 : ∏ k, ‖κ k * w ⟨k, c k⟩‖ ^ a k = (∏ k, ‖κ k‖ ^ a k) * ∏ k, ‖w ⟨k, c k⟩‖ ^ a k := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [norm_mul, mul_zpow]
  show ν * ((∏ k, ‖κ k‖ ^ a k) * h) = ‖u‖ * ∏ k, ‖κ k * w ⟨k, c k⟩‖ ^ a k
  rw [e2, mul_left_comm, e]
  ring

theorem inChart_of_coords (hz : genPt ξ ⤳ centre z) (hw : CoordsAt ξ y z w) (c : (k : K) → J k)
    (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) :
    InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c ⟨centre z, hz⟩ := by
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (hw.2 k (c k) (IsUnit.mk0 _ (hc k))).1
  refine ⟨Finset.prod_ne_zero_iff.2 fun k _ => hy k, fun c' => ?_⟩
  show (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩ ∈ _
  rw [← Finset.prod_div_distrib]
  refine prod_mem fun k _ => ?_
  obtain ⟨r, hr, -⟩ := (hw.2 k (c k) (IsUnit.mk0 _ (hc k))).2 (c' k)
  exact mem_of_valAt hr hz

theorem valAt_prod (hz : genPt ξ ⤳ centre z) {f : K → Ω} {r : K → ℂ} (h : ∀ k, ValAt ξ z (f k) (r k)) :
    ValAt ξ z (∏ k, f k) (∏ k, r k) := by
  classical
  have : ∀ s : Finset K, ValAt ξ z (∏ k ∈ s, f k) (∏ k ∈ s, r k) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using valAt_one hz
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.prod_insert hk]
      exact valAt_mul (h k) ih
  exact this _

theorem valAt_ratio (hz : genPt ξ ⤳ centre z) (hw : CoordsAt ξ y z w) (c c₀ : (k : K) → J k)
    (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) (hc₀ : ∀ k, w ⟨k, c₀ k⟩ ≠ 0) :
    ∃ m : ℂ, m ≠ 0 ∧ ValAt ξ z ((∏ k, y ⟨k, c k⟩ ^ a k) / ∏ k, y ⟨k, c₀ k⟩ ^ a k) m ∧
      ‖m‖ * ∏ k, ‖w ⟨k, c₀ k⟩‖ ^ a k = ∏ k, ‖w ⟨k, c k⟩‖ ^ a k := by
  have hr : ∀ k, ∃ r : ℂ, ValAt ξ z (y ⟨k, c k⟩ / y ⟨k, c₀ k⟩) r ∧ w ⟨k, c k⟩ = r * w ⟨k, c₀ k⟩ :=
    fun k => (hw.2 k (c₀ k) (IsUnit.mk0 _ (hc₀ k))).2 (c k)
  choose r hr he using hr
  have hr0 : ∀ k, r k ≠ 0 := fun k h0 => hc k (by rw [he k, h0, zero_mul])
  refine ⟨∏ k, r k ^ a k, Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hr0 k), ?_, ?_⟩
  · rw [← Finset.prod_div_distrib]
    have := valAt_prod hz fun k => valAt_zpow (hr k) (hr0 k) hz (a k)
    simpa only [div_zpow] using this
  · rw [norm_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [norm_zpow, he k, norm_mul, mul_zpow]

end Chart

section Gen

variable {p : Cpt ξ}

theorem zpow_mem_regAt {a : Ω} (h1 : a ∈ regAt ξ p) (h2 : a⁻¹ ∈ regAt ξ p) (n : ℤ) : a ^ n ∈ regAt ξ p := by
  cases n with
  | ofNat m => simpa using pow_mem h1 m
  | negSucc m => simpa [zpow_negSucc, inv_pow] using pow_mem h2 (m + 1)

theorem exists_gen {Λ : Lat ξ Ω} {σ : ℤ} {g : Ω} (hg : g ≠ 0)
    (h : Lat.tens (fun _ : Unit => Λ) (fun _ => σ) p = Submodule.span (regAt ξ p) {g}) :
    ∃ t₀, Λ.IsGenAt p t₀ ∧ unitAt ξ p (g / t₀ ^ σ) := by
  have hmem : g ∈ Lat.tens (fun _ : Unit => Λ) (fun _ => σ) p := by
    rw [h]
    exact Submodule.mem_span_singleton_self g
  have hne : ∃ t₀, Λ.IsGenAt p t₀ := by
    by_contra hn
    have he : {t | ∃ s : Unit → Ω, (∀ i, Λ.IsGenAt p (s i)) ∧ t = ∏ i, s i ^ σ} = ∅ := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨s, hs, -⟩
      exact hn ⟨_, hs ()⟩
    have hm2 : g ∈ Submodule.span (regAt ξ p) {t | ∃ s : Unit → Ω, (∀ i, Λ.IsGenAt p (s i)) ∧ t = ∏ i, s i ^ σ} :=
      hmem
    rw [he, Submodule.span_empty, Submodule.mem_bot] at hm2
    exact hg hm2
  obtain ⟨t₀, ht₀⟩ := hne
  have ht₀σ : t₀ ^ σ ≠ 0 := zpow_ne_zero _ ht₀.1
  have hle : Lat.tens (fun _ : Unit => Λ) (fun _ => σ) p ≤ Submodule.span (regAt ξ p) {t₀ ^ σ} := by
    refine Submodule.span_le.2 ?_
    rintro t ⟨s, hs, rfl⟩
    obtain ⟨hs0, hs1'⟩ := hs ()
    have hs1 : Λ p = Submodule.span (regAt ξ p) {s ()} := hs1'
    have h1 : s () ∈ Submodule.span (regAt ξ p) {t₀} := by
      rw [← ht₀.2, hs1]
      exact Submodule.mem_span_singleton_self _
    have h2 : t₀ ∈ Submodule.span (regAt ξ p) {s ()} := by
      rw [← hs1, ht₀.2]
      exact Submodule.mem_span_singleton_self _
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 h1
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 h2
    rw [Subring.smul_def, smul_eq_mul] at ha hb
    have ha0 : (a : Ω) ≠ 0 := fun h0 => hs0 (by rw [← ha, h0, zero_mul])
    have hbi : (a : Ω)⁻¹ = b := by
      have : (b : Ω) * a * t₀ = t₀ := by rw [_root_.mul_assoc, ha, hb]
      have h3 : (b : Ω) * a = 1 := mul_right_cancel₀ ht₀.1 (by rw [this, _root_.one_mul])
      exact (eq_inv_of_mul_eq_one_left h3).symm
    have hmem2 : (a : Ω) ^ σ ∈ regAt ξ p := zpow_mem_regAt a.2 (hbi ▸ b.2) σ
    refine Submodule.mem_span_singleton.2 ⟨⟨_, hmem2⟩, ?_⟩
    rw [Subring.smul_def, smul_eq_mul]
    simp only [Finset.univ_unique, Finset.prod_singleton]
    show (a : Ω) ^ σ * t₀ ^ σ = s default ^ σ
    rw [← mul_zpow, ha]
  have hge : t₀ ^ σ ∈ Submodule.span (regAt ξ p) {g} := by
    rw [← h]
    exact Submodule.subset_span ⟨fun _ => t₀, fun _ => ht₀, by simp⟩
  obtain ⟨m, hm⟩ := Submodule.mem_span_singleton.1 (hle hmem)
  obtain ⟨m', hm'⟩ := Submodule.mem_span_singleton.1 hge
  rw [Subring.smul_def, smul_eq_mul] at hm hm'
  refine ⟨t₀, ht₀, ?_⟩
  have e1 : g / t₀ ^ σ = m := by rw [← hm]; field_simp
  have e2 : (g / t₀ ^ σ)⁻¹ = m' := by rw [← hm']; field_simp
  exact ⟨div_ne_zero hg ht₀σ, e1 ▸ m.2, e2 ▸ m'.2⟩

end Gen

end Cx

section Main

open HodgeCpt GroundTheory.Heights₂.Heights.LowerBoundFree

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {cf : Coeff l} {O : Type} [CommRing O] {β : O →+* cf.F} {Y : Model Xo cf β} {S : Finset ℕ}
  {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω} {𝔐 : HodgeCpt Y S y}

def Good (Fl : 𝔐.Flag) (r : CMType H × Fin (D.p + D.q)) (a : K → ℤ) (e₀ : Ω)
    (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (w : (Σ k, J k) → ℂ) (h : ℝ) : Prop :=
  CoordsAt 𝔐.ξ y z w ∧ 𝔐.Interior z ∧ 0 < h ∧ ∀ t ν,
    𝔐.M.IsGrNorm 𝔐.t.PP.L (𝔐.V (rootIdx D r).1) (Fl.b (rootIdx D r).1) (rootIdx D r).2 z t ν →
      ChartNorm 𝔐.ξ y a e₀ z w (t ^ rootSgn D r) (ν ^ rootSgn D r) h

theorem exists_metric (hβ : Function.Injective β) (Fl : 𝔐.Flag) {xdeg : CMType H × Fin (D.p + D.q) → K → ℤ}
    {e : CMType H × Fin (D.p + D.q) → Ω} (hR : Fl.RootLines xdeg e) (r : CMType H × Fin (D.p + D.q))
    {z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X} {w : (Σ k, J k) → ℂ} (hw : CoordsAt 𝔐.ξ y z w) (hi : 𝔐.Interior z) :
    ∃ h, Good Fl r (xdeg r) (e r) z w h ∧ ∃ (t : Ω) (ν : ℝ), 0 < ν ∧
      𝔐.M.IsGrNorm 𝔐.t.PP.L (𝔐.V (rootIdx D r).1) (Fl.b (rootIdx D r).1) (rootIdx D r).2 z t ν := by
  have hall : genPt 𝔐.ξ ⤳ centre z := 𝔐.all _
  have hgen := 𝔐.tie.gen
  choose c₀ hc₀ using hw.1
  have hn₀ : ∀ k, w ⟨k, c₀ k⟩ ≠ 0 := fun k => (hc₀ k).ne_zero
  obtain ⟨he, hL⟩ := hR r
  have hspan := hL ⟨centre z, hall⟩ (Set.mem_univ _) c₀ (inChart_of_coords hall hw c₀ hn₀)
  have hy₀ : ∀ k, y ⟨k, c₀ k⟩ ≠ 0 := fun k => (hw.2 k (c₀ k) (hc₀ k)).1
  have hG₀ : (∏ k, y ⟨k, c₀ k⟩ ^ xdeg r k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy₀ k)
  have hg₀ : (∏ k, y ⟨k, c₀ k⟩ ^ xdeg r k) • e r ≠ 0 := smul_ne_zero hG₀ he
  obtain ⟨t₀, hgen0, hunit⟩ := exists_gen (Λ := (𝔐.V (rootIdx D r).1).gr (Fl.b (rootIdx D r).1) (rootIdx D r).2)
    (σ := rootSgn D r) hg₀ hspan
  obtain ⟨ν₀, hν₀, hI⟩ := GlobalTheory.T.hodge_cpt_interior_flag E H D l Xo cf O β Y S Ω K J y 𝔐 Fl hβ z hi (rootIdx D r).1
    (rootIdx D r).2 t₀ hgen0
  obtain ⟨u₀, hu₀, hv₀⟩ := exists_valAt_of_unit hall hunit hgen
  have ht₀ := hgen0.1
  have hW₀ : 0 < ∏ k, ‖w ⟨k, c₀ k⟩‖ ^ xdeg r k :=
    Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 (hn₀ k)) _
  have hνσ : 0 < ν₀ ^ rootSgn D r := zpow_pos hν₀ _
  have hu₀' : 0 < ‖u₀‖ := norm_pos_iff.2 hu₀
  refine ⟨(∏ k, ‖w ⟨k, c₀ k⟩‖ ^ xdeg r k) / (‖u₀‖ * ν₀ ^ rootSgn D r), ⟨hw, hi, by positivity, ?_⟩, t₀, ν₀, hν₀,
    (hI t₀ ν₀).2 ⟨1, one_ne_zero, by rw [div_self ht₀]; exact valAt_one hall, by simp⟩⟩
  intro t ν hgr c hc
  obtain ⟨u₁, hu₁, hv₁, rfl⟩ := (hI t ν).1 hgr
  obtain ⟨m, hm, hvm, hnm⟩ := valAt_ratio (a := xdeg r) hall hw c c₀ hc hn₀
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (hw.2 k (c k) (IsUnit.mk0 _ (hc k))).1
  have hG : (∏ k, y ⟨k, c k⟩ ^ xdeg r k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)
  refine ⟨u₁ ^ rootSgn D r * u₀⁻¹ * m⁻¹, ?_, ?_⟩
  · have := valAt_mul (valAt_mul (valAt_zpow hv₁ hu₁ hall (rootSgn D r)) (valAt_inv hv₀ hu₀)) (valAt_inv hvm hm)
    convert this using 1
    rw [smul_eq_mul, div_zpow (t) t₀]
    have := zpow_ne_zero (rootSgn D r) ht₀
    field_simp
  · rw [← hnm, norm_mul, norm_mul, norm_zpow, norm_inv, norm_inv, mul_zpow]
    have hm' : 0 < ‖m‖ := norm_pos_iff.2 hm
    have hu₁' : 0 < ‖u₁‖ := norm_pos_iff.2 hu₁
    field_simp

variable {a : K → ℤ} {e₀ : Ω} {Fl : 𝔐.Flag} {r : CMType H × Fin (D.p + D.q)}

theorem Good.conj {z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X} {w : (Σ k, J k) → ℂ} {h : ℝ}
    (hG : Good Fl r a e₀ z w h) : Good Fl r a e₀ (cj z) (fun p => conj (w p)) h := by
  obtain ⟨hw, hi, hp, hn⟩ := hG
  refine ⟨coordsAt_conj hw, ?_, hp, fun t ν hgr => ?_⟩
  · show centre (cj z) ∈ _
    rw [centre_cj]
    exact hi
  · have := isGrNorm_conj 𝔐.t 𝔐.M _ hgr
    rw [cj_cj] at this
    exact (hn t ν this).conj

theorem Good.smul {z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X} {w : (Σ k, J k) → ℂ} {h : ℝ}
    (hG : Good Fl r a e₀ z w h) {κ : K → ℂ} (hκ : ∀ k, κ k ≠ 0) :
    Good Fl r a e₀ z (fun p => κ p.1 * w p) ((∏ k, ‖κ k‖ ^ a k) * h) := by
  obtain ⟨hw, hi, hp, hn⟩ := hG
  obtain ⟨-, -, t3⟩ := GlobalTheory.T.local_ring_points_existsUnique 𝔐.X Ω 𝔐.ξ K J y 𝔐.tie ℂ
  refine ⟨((t3 z w (𝔐.all _) hw).2 _).2 ⟨fun k => Units.mk0 (κ k) (hκ k), rfl⟩, hi,
    mul_pos (Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 (hκ k)) _) hp,
    fun t ν hgr => (hn t ν hgr).smul hκ⟩

def metricF (Fl : 𝔐.Flag) (r : CMType H × Fin (D.p + D.q)) (a : K → ℤ) (e₀ : Ω) (w : (Σ k, J k) → ℂ) : ℝ :=
  open Classical in
  if hx : ∃ z h, Good Fl r a e₀ z w h then hx.choose_spec.choose else refNorm a w

theorem metricF_eq (hu : ∀ z z' w h h', Good Fl r a e₀ z w h → Good Fl r a e₀ z' w h' → h = h')
    {z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X} {w : (Σ k, J k) → ℂ} {h : ℝ} (hG : Good Fl r a e₀ z w h) :
    metricF Fl r a e₀ w = h := by
  have hx : ∃ z h, Good Fl r a e₀ z w h := ⟨z, h, hG⟩
  unfold metricF
  rw [dif_pos hx]
  exact hu _ _ _ _ _ hx.choose_spec.choose_spec hG

theorem metricF_of_not {w : (Σ k, J k) → ℂ} (hx : ¬ ∃ z h, Good Fl r a e₀ z w h) :
    metricF Fl r a e₀ w = refNorm a w := by
  unfold metricF
  rw [dif_neg hx]

theorem exists_hodgeLine : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β)
    (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ)
    (e : CMType H × Fin (D.p + D.q) → Ω), Function.Injective β → Fl.RootLines xdeg e →
    ∀ r, ∃ A : HermLine J, A.a = xdeg r ∧ Fl.IsHodgeLine r (e r) A ∧ IsConjInvariantH A := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 Fl xdeg e hβ hR r
  have hu : ∀ z z' w h h', Good Fl r (xdeg r) (e r) z w h → Good Fl r (xdeg r) (e r) z' w h' → h = h' := by
    intro z z' w h h' hG hG'
    obtain ⟨t1, -, t3⟩ := GlobalTheory.T.local_ring_points_existsUnique 𝔐.X Ω 𝔐.ξ K J y 𝔐.tie ℂ
    have hzz : z' = z := (t1 w hG.1.1 (t3 z w (𝔐.all _) hG.1).1).unique ⟨𝔐.all _, hG'.1⟩ ⟨𝔐.all _, hG.1⟩
    subst hzz
    obtain ⟨-, -, t, ν, hν, hgr⟩ := exists_metric hβ Fl hR r hG.1 hG.2.1
    choose c₀ hc₀ using hG.1.1
    have hn₀ : ∀ k, w ⟨k, c₀ k⟩ ≠ 0 := fun k => (hc₀ k).ne_zero
    obtain ⟨u, hv, he⟩ := hG.2.2.2 t ν hgr c₀ hn₀
    obtain ⟨u', hv', he'⟩ := hG'.2.2.2 t ν hgr c₀ hn₀
    have huu : u = u' := valAt_unique 𝔐.tie.gen hv hv'
    rw [huu, ← he'] at he
    exact mul_left_cancel₀ (zpow_pos hν _).ne' he
  have hneg : ∀ w, (¬ ∃ z h, Good Fl r (xdeg r) (e r) z w h) →
      ¬ ∃ z h, Good Fl r (xdeg r) (e r) z (fun p => conj (w p)) h := by
    rintro w hx ⟨z, h, hG⟩
    refine hx ⟨cj z, h, ?_⟩
    simpa using hG.conj
  refine ⟨⟨xdeg r, metricF Fl r (xdeg r) (e r), ?_, ?_⟩, rfl, ?_, ?_⟩
  · intro w hw
    by_cases hx : ∃ z h, Good Fl r (xdeg r) (e r) z w h
    · obtain ⟨z, h, hG⟩ := hx
      rw [metricF_eq hu hG]
      exact hG.2.2.1
    · rw [metricF_of_not hx]
      exact refNorm_pos _ hw
  · intro κ w hκ
    by_cases hx : ∃ z h, Good Fl r (xdeg r) (e r) z w h
    · obtain ⟨z, h, hG⟩ := hx
      rw [metricF_eq hu hG, metricF_eq hu (hG.smul hκ)]
    · have hx' : ¬ ∃ z h, Good Fl r (xdeg r) (e r) z (fun p => κ p.1 * w p) h := by
        rintro ⟨z, h, hG⟩
        have := hG.smul (κ := fun k => (κ k)⁻¹) fun k => inv_ne_zero (hκ k)
        have e1 : (fun p : (Σ k, J k) => (κ p.1)⁻¹ * (κ p.1 * w p)) = w := by
          funext p
          rw [inv_mul_cancel_left₀ (hκ p.1)]
        rw [e1] at this
        exact hx ⟨z, _, this⟩
      rw [metricF_of_not hx, metricF_of_not hx']
      exact refNorm_smul (xdeg r) κ w
  · intro z w hw hi t ν hgr
    refine ⟨(hR r).1, hw, fun cc hcc => ?_⟩
    obtain ⟨h, hG, -⟩ := exists_metric hβ Fl hR r hw hi
    show ∃ u : ℂ, ValAt 𝔐.ξ z (t ^ rootSgn D r / ((∏ k, y ⟨k, cc k⟩ ^ xdeg r k) * e r)) u ∧
      ν ^ rootSgn D r * metricF Fl r (xdeg r) (e r) w = ‖u‖ * ∏ k, ‖w ⟨k, cc k⟩‖ ^ xdeg r k
    rw [metricF_eq hu hG]
    exact hG.2.2.2 t ν hgr cc hcc
  · intro w
    show metricF Fl r (xdeg r) (e r) (fun p => conj (w p)) = metricF Fl r (xdeg r) (e r) w
    by_cases hx : ∃ z h, Good Fl r (xdeg r) (e r) z w h
    · obtain ⟨z, h, hG⟩ := hx
      rw [metricF_eq hu hG, metricF_eq hu hG.conj]
    · rw [metricF_of_not hx, metricF_of_not (hneg w hx)]
      unfold refNorm
      simp [Complex.norm_conj]

end Main

end GlobalTheory.CompanionTheory.Ar.HodgeLine
