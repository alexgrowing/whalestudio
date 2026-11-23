import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenPtSpecializes
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionEqZeroOfValuesStatement
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.HtExists
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueTangentDualNumberStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsStalkFractionOfGenericStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusPointOverFractionFieldStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionLiftIsClosedImmersionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionExtendsFromStalkPullbackStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.HTTieK

section val
variable {B B' : Type} [CommRing B] [CommRing B'] {Y Z : Scheme.{0}}

theorem valAt_comp (y : Spec (CommRingCat.of B) ⟶ Y) (φ : Y ⟶ Z) (W : Z.Opens) (h : ⊤ ≤ (y ≫ φ) ⁻¹ᵁ W) (f : Γ(Z, W)) :
    BT.valAt (y ≫ φ) W h f = BT.valAt y (φ ⁻¹ᵁ W) h ((φ.app W).hom f) := by
  simp only [BT.valAt, Scheme.Hom.comp_appLE]
  rfl

theorem valAt_spec (φ : B →+* B') (y : Spec (CommRingCat.of B) ⟶ Y) (W : Y.Opens)
    (h : ⊤ ≤ y ⁻¹ᵁ W) (h' : ⊤ ≤ (Spec.map (CommRingCat.ofHom φ) ≫ y) ⁻¹ᵁ W) (f : Γ(Y, W)) :
    BT.valAt (Spec.map (CommRingCat.ofHom φ) ≫ y) W h' f = φ (BT.valAt y W h f) := by
  have e : (Spec.map (CommRingCat.ofHom φ) ≫ y).appLE W ⊤ h' =
      y.appLE W ⊤ h ≫ (Spec.map (CommRingCat.ofHom φ)).appTop := by
    have := Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom φ)) y W ⊤ ⊤ h le_top
    rw [← this]
    simp [Scheme.Hom.appLE]
    rfl
  have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  simp only [BT.valAt, e]
  exact congrArg (fun z => z.hom ((y.appLE W ⊤ h).hom f)) n

theorem valAt_res (y : Spec (CommRingCat.of B) ⟶ Y) (U V : Y.Opens) (hUV : U ≤ V) (h : ⊤ ≤ y ⁻¹ᵁ U) (h' : ⊤ ≤ y ⁻¹ᵁ V)
    (f : Γ(Y, V)) : BT.valAt y U h (Y.presheaf.map (homOfLE hUV).op f) = BT.valAt y V h' f := by
  have := Scheme.Hom.map_appLE y (V := ⊤) h (homOfLE hUV).op
  simp only [BT.valAt]
  rw [← this]
  rfl

end val

section tors
variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {G : Over X} [GrpObj G]
  {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] {Γ' : QFGroup R T}
  {x : Spec (CommRingCat.of R) ⟶ X} {N : ℕ} {i : Γ'.G.left ⟶ G.left} (k : FractionRing R →+* Ω)

abbrev ptG (i : Γ'.G.left ⟶ G.left) (t : T) : Spec (CommRingCat.of Ω) ⟶ G.left :=
  Spec.map (CommRingCat.ofHom k) ≫ (Γ'.pt t).left ≫ i

abbrev yO (R : Type) [CommRing R] [IsDomain R] (k : FractionRing R →+* Ω) : Over (Spec (CommRingCat.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (k.comp (algebraMap R (FractionRing R)))))

def toGen : yO R k ⟶ BT.genPt R := Over.homMk (Spec.map (CommRingCat.ofHom k)) (by
  simp only [yO, Over.mk_hom, BT.genPt, ← Spec.map_comp]
  rfl)

include k in
theorem tors_pt (h : Γ'.IsTorsionAlong G x N i)
    (hk : Spec.map (CommRingCat.ofHom (k.comp (algebraMap R (FractionRing R)))) ≫ x = ξ)
    (g : Over.mk ξ ⟶ G) (hg : g ^ N = 1) : ∃ t, g.left = ptG k i t := by
  subst hk
  obtain ⟨y, hy⟩ := (h.kernel (yO R k) g).1 hg
  obtain ⟨t, ht⟩ := GlobalTheory.T.torus_point_over_fraction_field R T Γ' Ω k y.left (Over.w y)
  exact ⟨t, by rw [← hy, ht, Category.assoc]⟩

theorem tors_ex (h : Γ'.IsTorsionAlong G x N i)
    (hk : Spec.map (CommRingCat.ofHom (k.comp (algebraMap R (FractionRing R)))) ≫ x = ξ) (t : T) :
    ∃ g : Over.mk ξ ⟶ G, g ^ N = 1 ∧ g.left = ptG k i t := by
  subst hk
  let y : yO R k ⟶ Γ'.G := toGen k ≫ Γ'.pt t
  let g : Over.mk ((yO R k).hom ≫ x) ⟶ G := Over.homMk (y.left ≫ i) (by
    simp [h.isOver, y, toGen, Over.w_assoc])
  exact ⟨g, (h.kernel (yO R k) g).2 ⟨y, rfl⟩, by simp [g, y, toGen]⟩

theorem tors_inj (h : Γ'.IsTorsionAlong G x N i) {s t : T} (e : ptG k i s = ptG k i t) : s = t := by
  have := h.inj (yO R k) (toGen k ≫ Γ'.pt s) (toGen k ≫ Γ'.pt t) (by simpa [toGen] using e)
  have e2 := congrArg (fun z : yO R k ⟶ Γ'.G => z.left (IsLocalRing.closedPoint Ω)) this
  simp only [toGen, Over.comp_left, Over.homMk_left] at e2
  exact Γ'.pt_inj s t _ _ e2

theorem tors_mul (h : Γ'.IsTorsionAlong G x N i)
    (hk : Spec.map (CommRingCat.ofHom (k.comp (algebraMap R (FractionRing R)))) ≫ x = ξ)
    {s t : T} {g g' : Over.mk ξ ⟶ G} (e : g.left = ptG k i s) (e' : g'.left = ptG k i t) :
    (g * g').left = ptG k i (s * t) := by
  subst hk
  have := h.mul (yO R k) (toGen k ≫ Γ'.pt s) (toGen k ≫ Γ'.pt t) g g' (by simpa [toGen] using e)
    (by simpa [toGen] using e')
  rw [this, ← comp_mul, ← map_mul]
  simp [toGen, ptG]

variable {L : LB G.left} {e : (Over.mk ξ ⟶ G) → (Over.mk ξ ⟶ G) → Ωˣ}

theorem exists_alt [IsCommMonObj G] (hw : GenWeil G L ξ N e) (h : Γ'.IsTorsionAlong G x N i)
    (hk : Spec.map (CommRingCat.ofHom (k.comp (algebraMap R (FractionRing R)))) ≫ x = ξ) (χ : T →* Rˣ) :
    ∃ y : Over.mk ξ ⟶ G, y ^ N = 1 ∧ ∀ t (g : Over.mk ξ ⟶ G), g ^ N = 1 → g.left = ptG k i t →
      (e y g : Ω) = k (algebraMap R _ (χ t : R)) := by
  classical
  let kk := k.comp (algebraMap R (FractionRing R))
  let φ : (Over.mk ξ ⟶ G) → Ωˣ := fun g =>
    if hg : g ^ N = 1 then Units.map kk.toMonoidHom (χ (tors_pt k h hk g hg).choose) else 1
  have hφ : ∀ g t, g ^ N = 1 → g.left = ptG k i t → φ g = Units.map kk.toMonoidHom (χ t) := by
    intro g t hg et
    simp only [φ, dif_pos hg]
    rw [tors_inj k h ((tors_pt k h hk g hg).choose_spec.symm.trans et)]
  obtain ⟨y, hy, hye⟩ := hw.perfect φ (fun g g' hg hg' => by
    obtain ⟨t, ht⟩ := tors_pt k h hk g hg
    obtain ⟨t', ht'⟩ := tors_pt k h hk g' hg'
    rw [hφ _ (t * t') (by rw [mul_pow, hg, hg', _root_.one_mul]) (tors_mul k h hk ht ht'), hφ g t hg ht,
      hφ g' t' hg' ht', map_mul, map_mul])
  refine ⟨y, hy, fun t g hg hgt => ?_⟩
  rw [← hye g hg, hφ g t hg hgt]
  rfl

theorem weil_pow (hw : GenWeil G L ξ N e) {y g : Over.mk ξ ⟶ G} (hy : y ^ N = 1) (hg : g ^ N = 1) (n : ℕ) :
    e y (g ^ n) = e y g ^ n := by
  have h1 : e y 1 = 1 := by
    have := hw.mul_right y 1 1 hy (one_pow N) (one_pow N)
    rw [_root_.mul_one] at this
    exact left_eq_mul.1 this
  induction n with
  | zero => simpa using h1
  | succ n ih =>
    rw [pow_succ, hw.mul_right y _ _ hy (by rw [← pow_mul, mul_comm, pow_mul, hg, one_pow]) hg, ih, pow_succ]

theorem exists_reg [IsIntegrallyClosed R] (hw : GenWeil G L ξ N e) (hN : N ≠ 0)
    (hfrac : ∀ a : Ω, ∃ b c : R, k (algebraMap R _ c) ≠ 0 ∧ a * k (algebraMap R _ c) = k (algebraMap R _ b))
    {y g : Over.mk ξ ⟶ G} (hy : y ^ N = 1) (hg : g ^ N = 1) : ∃ r : R, k (algebraMap R _ r) = (e y g : Ω) := by
  have h1 : e y g ^ N = 1 := by
    rw [← weil_pow hw hy hg, hg]
    have := weil_pow hw hy hg 0
    simpa using this
  obtain ⟨b, c, hc, hbc⟩ := hfrac (e y g : Ω)
  have hc' : algebraMap R (FractionRing R) c ≠ 0 := fun h0 => hc (by rw [h0, map_zero])
  set u : FractionRing R := algebraMap R _ b / algebraMap R _ c with hu
  have hku : k u = (e y g : Ω) := by
    rw [hu, map_div₀, ← hbc, mul_div_assoc, div_self hc, _root_.mul_one]
  have hpow : u ^ N = 1 := by
    apply k.injective
    rw [map_pow, hku, map_one]
    simpa using congrArg Units.val h1
  have hint : _root_.IsIntegral R u :=
    IsIntegral.of_pow (Nat.pos_of_ne_zero hN) (by rw [hpow]; exact isIntegral_one)
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  exact ⟨r, by rw [hr, hku]⟩

theorem exists_chi [IsCommMonObj G] [IsIntegrallyClosed R] (hw : GenWeil G L ξ N e) (hN : N ≠ 0)
    (h : Γ'.IsTorsionAlong G x N i)
    (hk : Spec.map (CommRingCat.ofHom (k.comp (algebraMap R (FractionRing R)))) ≫ x = ξ)
    (hfrac : ∀ a : Ω, ∃ b c : R, k (algebraMap R _ c) ≠ 0 ∧ a * k (algebraMap R _ c) = k (algebraMap R _ b))
    {y : Over.mk ξ ⟶ G} (hy : y ^ N = 1) :
    ∃ χ : T →* Rˣ, ∀ t (g : Over.mk ξ ⟶ G), g.left = ptG k i t → (e y g : Ω) = k (algebraMap R _ (χ t : R)) := by
  classical
  have hinj : Function.Injective (k.comp (algebraMap R (FractionRing R))) :=
    k.injective.comp (IsFractionRing.injective R (FractionRing R))
  choose g hgN hgl using tors_ex (Γ' := Γ') (N := N) (i := i) k h hk
  have hone : ∀ t s, (g t * g s) = g (t * s) := fun t s =>
    Over.OverMorphism.ext ((tors_mul k h hk (hgl t) (hgl s)).trans (hgl _).symm)
  let u : T →* Ωˣ := MonoidHom.mk' (fun t => e y (g t)) (fun t s => by
    rw [← hone, hw.mul_right y _ _ hy (hgN t) (hgN s)])
  choose c hc using fun t => exists_reg k hw hN hfrac hy (hgN t)
  let m : T →* R :=
    { toFun := c
      map_one' := hinj (by
        have := hc 1
        have h1 : (u 1 : Ω) = 1 := by rw [map_one]; rfl
        simpa [u] using this.trans h1)
      map_mul' := fun t s => hinj (by
        have h1 : (u (t * s) : Ω) = u t * u s := by rw [map_mul]; rfl
        have h2 := hc (t * s)
        simp only [RingHom.comp_apply, map_mul]
        rw [h2, hc t, hc s]
        exact h1) }
  refine ⟨m.toHomUnits, fun t g' hg' => ?_⟩
  have : g' = g t := Over.OverMorphism.ext (hg'.trans (hgl t).symm)
  rw [this, MonoidHom.coe_toHomUnits]
  exact (hc t).symm

end tors
end GlobalTheory.CompanionTheory.Ar.HTTieK

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.HTTieK

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G]

theorem valAt_congr {B : Type} [CommRing B] {Y : Scheme.{0}} {y y' : Spec (CommRingCat.of B) ⟶ Y} (e : y = y') (W : Y.Opens)
    (h : ⊤ ≤ y ⁻¹ᵁ W) (h' : ⊤ ≤ y' ⁻¹ᵁ W) (f : Γ(Y, W)) : BT.valAt y W h f = BT.valAt y' W h' f := by
  subst e; rfl

theorem one_left {S : Over X} : (1 : S ⟶ G).left = S.hom ≫ (η[G]).left := by
  simp [Hom.one_def]

theorem hk_stalk (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) :
    Spec.map (CommRingCat.ofHom (genMap ξ p)) ≫ X.fromSpecStalk p.1 = ξ := by
  obtain ⟨q, hq⟩ := p
  have a := Scheme.SpecMap_stalkSpecializes_fromSpecStalk hq
  have b := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  have c : Spec.map (CommRingCat.ofHom (genMap ξ ⟨q, hq⟩)) =
      Spec.map (Scheme.stalkClosedPointTo ξ) ≫ Spec.map (X.presheaf.stalkSpecializes hq) :=
    Spec.map_comp _ _
  rw [c, Category.assoc]
  exact (congrArg (fun m => Spec.map (Scheme.stalkClosedPointTo ξ) ≫ m) a).trans b

theorem tan_mem {R : Type} [CommRing R] [IsLocalRing R] (x : Spec (CommRingCat.of R) ⟶ X) (v : epsAt x ⟶ G)
    (hv : IsTanAt G x v) (W : G.left.Opens) (hW : (η[G]).left (x (IsLocalRing.closedPoint R)) ∈ W) :
    ⊤ ≤ v.left ⁻¹ᵁ W := by
  intro z _
  have hσ : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫ v.left = x ≫ (η[G]).left :=
    hv.trans one_left
  have hs : Function.Surjective (TrivSqZeroExt.fstHom R R R).toRingHom := fun r => ⟨TrivSqZeroExt.inl r, rfl⟩
  obtain ⟨z', hz'⟩ : ∃ z' : PrimeSpectrum R,
      PrimeSpectrum.comap (TrivSqZeroExt.fstHom R R R).toRingHom z' = (z : PrimeSpectrum (DualNumber R)) := by
    have hp : (z : PrimeSpectrum (DualNumber R)).asIdeal.IsPrime := PrimeSpectrum.isPrime _
    have key : ∀ a : DualNumber R, a - TrivSqZeroExt.inl a.fst ∈ (z : PrimeSpectrum (DualNumber R)).asIdeal := by
      intro a
      have h2 : (a - TrivSqZeroExt.inl a.fst) ^ 2 = 0 := by
        ext <;> simp [pow_two]
      exact hp.mem_of_pow_mem 2 (by rw [h2]; exact Ideal.zero_mem _)
    refine ⟨PrimeSpectrum.comap (TrivSqZeroExt.inlHom R R) z, ?_⟩
    apply PrimeSpectrum.ext
    ext a
    constructor
    · intro h
      have h' : TrivSqZeroExt.inl a.fst ∈ (z : PrimeSpectrum (DualNumber R)).asIdeal := h
      simpa using Ideal.add_mem _ (key a) h'
    · intro h
      show TrivSqZeroExt.inl a.fst ∈ (z : PrimeSpectrum (DualNumber R)).asIdeal
      simpa using Ideal.sub_mem _ h (key a)
  have e1 : v.left z = (x ≫ (η[G]).left) z' := by
    rw [← hσ, ← hz']
    rfl
  show v.left z ∈ W
  rw [e1]
  have sp : (z' : PrimeSpectrum R) ⤳ IsLocalRing.closedPoint R := IsLocalRing.specializes_closedPoint z'
  have sp2 : (x ≫ (η[G]).left) z' ⤳ (x ≫ (η[G]).left) (IsLocalRing.closedPoint R) :=
    sp.map (x ≫ (η[G]).left).continuous
  exact sp2.mem_open W.isOpen hW

theorem lift_sec [IsSeparated G.hom] (p : X) [IsDomain (X.presheaf.stalk p)] {T : Type} [CommGroup T]
    (Γ' : QFGroup (X.presheaf.stalk p) T) (N : ℕ) (i : Γ'.G.left ⟶ G.left)
    (h : Γ'.IsTorsionAlong G (X.fromSpecStalk p) N i) (s : Γ(Γ'.G.left, ⊤)) :
    ∃ (W : G.left.Opens) (f : Γ(G.left, W)), (η[G]).left p ∈ W ∧
      (i.app W).hom f = Γ'.G.left.presheaf.map (homOfLE (le_top : i ⁻¹ᵁ W ≤ ⊤)).op s := by
  have hover : G.hom ((η[G]).left p) = p := by
    have e : ((η[G]).left ≫ G.hom) p = p := by
      rw [Over.w]
      rfl
    exact e
  have := GlobalTheory.T.torsion_lift_is_closed_immersion G _ T Γ' (X.fromSpecStalk p) N i h
  have key : ∀ i', pullback.lift i Γ'.G.hom h.isOver ≫ pullback.fst G.hom (X.fromSpecStalk p) = i' →
      ∃ (W : G.left.Opens) (f : Γ(G.left, W)), (η[G]).left p ∈ W ∧
      (i'.app W).hom f = Γ'.G.left.presheaf.map (homOfLE (le_top : i' ⁻¹ᵁ W ≤ ⊤)).op s := by
    rintro _ rfl
    exact GlobalTheory.T.section_extends_from_stalk_pullback G.hom p _ hover _ s
  exact key i (pullback.lift_fst _ _ _)

theorem valAt_one {B : Type} [CommRing B] {Y : Scheme.{0}} (y : Spec (CommRingCat.of B) ⟶ Y) (W : Y.Opens)
    (h : ⊤ ≤ y ⁻¹ᵁ W) : BT.valAt y W h 1 = 1 := by
  simp [BT.valAt]

theorem valAt_sub {B : Type} [CommRing B] {Y : Scheme.{0}} (y : Spec (CommRingCat.of B) ⟶ Y) (W : Y.Opens)
    (h : ⊤ ≤ y ⁻¹ᵁ W) (a b : Γ(Y, W)) : BT.valAt y W h (a - b) = BT.valAt y W h a - BT.valAt y W h b := by
  simp [BT.valAt]

theorem comp_pow' {A B : Over X} (ψ : A ⟶ B) (g : B ⟶ G) (n : ℕ) : ψ ≫ g ^ n = (ψ ≫ g) ^ n := by
  induction n with
  | zero => simp [MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, comp_mul, ih]

theorem epi_spMap {K : Type} [Field K] (a : Ω →+* K) : Epi (Spec.map (CommRingCat.ofHom a)) := by
  have : Flat (Spec.map (CommRingCat.ofHom a)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    let _ := a.toAlgebra
    exact (inferInstance : Module.Flat Ω K)
  have : Surjective (Spec.map (CommRingCat.ofHom a)) :=
    ⟨fun z => ⟨IsLocalRing.closedPoint K, Subsingleton.elim (α := PrimeSpectrum Ω) _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem pow_descend {ξ : Spec (CommRingCat.of Ω) ⟶ X} {N : ℕ} {K : Type} [Field K] (a : Ω →+* K)
    {g₀ : Over.mk ξ ⟶ G} {g : Over.mk (spMap a ≫ ξ) ⟶ G} (e : g.left = spMap a ≫ g₀.left) (hg : g ^ N = 1) :
    g₀ ^ N = 1 := by
  let ψ : Over.mk (spMap a ≫ ξ) ⟶ Over.mk ξ := Over.homMk (spMap a) rfl
  have h1 : g = ψ ≫ g₀ := Over.OverMorphism.ext (by simp [e, ψ])
  have h2 : ψ ≫ g₀ ^ N = ψ ≫ 1 := by rw [comp_pow', ← h1, hg, MonObj.comp_one]
  have := epi_spMap a
  apply Over.OverMorphism.ext
  have h3 := congrArg (fun z => z.left) h2
  simp only [Over.comp_left, ψ, Over.homMk_left] at h3
  exact (cancel_epi (spMap a)).1 h3

theorem valAt_mod {R : Type} [CommRing R] {Y : Scheme.{0}} (y : Spec (CommRingCat.of (DualNumber R)) ⟶ Y) (N : ℕ)
    {v : Spec (CommRingCat.of (DualNumber (R ⧸ Ideal.span {(N : R)}))) ⟶ Y}
    (hv : v = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫ y) (W : Y.Opens)
    (h : ⊤ ≤ y ⁻¹ᵁ W) (h' : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(Y, W)) :
    BT.valAt v W h' f = dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})) (BT.valAt y W h f) := by
  subst hv
  exact valAt_spec _ y W h h' f

theorem snd_of_mod {R : Type} [CommRing R] (N : ℕ) (a : DualNumber R) (b : R)
    (h : (TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (Ideal.Quotient.mk (Ideal.span {(N : R)}) b) :
      DualNumber (R ⧸ Ideal.span {(N : R)})) = dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})) a) :
    ∃ r, b = a.snd + N * r := by
  have e4 := congrArg TrivSqZeroExt.snd h
  simp only [dualMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
    TrivSqZeroExt.snd_inr, zero_add] at e4
  obtain ⟨r', hr'⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 e4)
  exact ⟨r', by linear_combination -hr'⟩

theorem mod_of_snd {R : Type} [CommRing R] (N : ℕ) (a : DualNumber R) (b r : R) (h1 : a.fst = 1)
    (h : b = a.snd + N * r) :
    dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})) a =
      TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (Ideal.Quotient.mk (Ideal.span {(N : R)}) b) := by
  have hN : Ideal.Quotient.mk (Ideal.span {(N : R)}) (N * r) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  ext
  · simp [dualMap, h1]
  · simp [dualMap, h, hN]

theorem spec_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    Spec.map (CommRingCat.ofHom (g.comp f)) = Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

theorem dual_alg {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) :
    (dualMap φ).comp (algebraMap A (DualNumber A)) = (algebraMap B (DualNumber B)).comp φ :=
  RingHom.ext fun a => by
    show dualMap φ (TrivSqZeroExt.inl a) = TrivSqZeroExt.inl (φ a)
    ext <;> simp [dualMap]

theorem dual_fst {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) :
    (TrivSqZeroExt.fstHom B B B).toRingHom.comp (dualMap φ) = φ.comp (TrivSqZeroExt.fstHom A A A).toRingHom :=
  RingHom.ext fun a => by
    show (dualMap φ a).fst = φ a.fst
    simp [dualMap]

theorem dual_eps {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (c : A) :
    (dualMap φ).comp (epsMul c) = (epsMul (φ c)).comp (dualMap φ) :=
  RingHom.ext fun a => by
    ext <;> simp [dualMap, epsMul, _root_.mul_comm]

section main
variable {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]

def kL {R : Type} [CommRing R] [IsDomain R] {g : R →+* Ω} (hg : Function.Injective g) : FractionRing R →+* Ω :=
  IsFractionRing.lift hg

theorem kL_comp {R : Type} [CommRing R] [IsDomain R] {g : R →+* Ω} (hg : Function.Injective g) :
    (kL hg).comp (algebraMap R (FractionRing R)) = g :=
  RingHom.ext fun a => IsFractionRing.lift_algebraMap hg a

theorem form_mem_omLat (M : LieModel G ξ E) (N : ℕ) (p : Cpt ξ) (w : Module.Dual Ω E) (h : M.IsHTFormAt N p w) :
    w ∈ M.omLat p := by
  obtain ⟨_, T, _, Γ', i, L', _, _, M₀, j, χ, w₀, -, hpt, -, hwj⟩ := h
  show ∀ e ∈ M.lat p, w e ∈ regAt ξ p
  intro e he
  induction he using Submodule.span_induction with
  | mem e he =>
    obtain ⟨v, htan, hpte⟩ := he
    obtain ⟨e₀, he₀⟩ := M₀.onto v htan
    have hje : j e₀ = e := M.inj (Over.OverMorphism.ext ((hpt e₀).trans (by subst he₀; exact hpte.symm)))
    rw [← hje, hwj]
    exact ⟨_, rfl⟩
  | zero => simp
  | add a b _ _ ha hb => simpa using add_mem ha hb
  | smul c a _ ha =>
    have : w (c • a) = (c : Ω) * w a := by
      rw [Subring.smul_def, map_smul, smul_eq_mul]
    rw [this]
    exact mul_mem c.2 ha

section core
variable [IsCommMonObj G] {R : Type} [CommRing R] [IsLocalRing R] {x : Spec (CommRingCat.of R) ⟶ X} {g : R →+* Ω}
  (hg : Function.Injective g) (hkx : Spec.map (CommRingCat.ofHom g) ≫ x = ξ) (M : LieModel G ξ E)
  {L : LB G.left} {N : ℕ} {e : (Over.mk ξ ⟶ G) → (Over.mk ξ ⟶ G) → Ωˣ} (hw : GenWeil G L ξ N e) {q : X}

include hg hkx hw in
theorem core_le (hfull : FullTorsion G ξ N) (w : Module.Dual Ω E)
    (hl : ∀ (_ : IsDomain R) (T : Type) (_ : CommGroup T) (Γ' : QFGroup R T) (i : Γ'.G.left ⟶ G.left),
      Γ'.IsTorsionAlong G x N i → ∀ s : Γ(Γ'.G.left, ⊤), ∃ (W : G.left.Opens) (f : Γ(G.left, W)), (η[G]).left q ∈ W ∧
        (i.app W).hom f = Γ'.G.left.presheaf.map (homOfLE (le_top : i ⁻¹ᵁ W ≤ ⊤)).op s)
    (h : M.IsHTFormOver N x g w) :
    ∃ y : Over.mk ξ ⟶ G, y ^ N = 1 ∧ ∃ (W : G.left.Opens) (f : Γ(G.left, W)), (η[G]).left q ∈ W ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k] (i : Ω →+* k) (xk g' : Over.mk (spMap i ≫ ξ) ⟶ G) (c : kˣ)
        (h : ⊤ ≤ g'.left ⁻¹ᵁ W), xk.left = spMap i ≫ y.left → g' ^ N = 1 →
          Out.WeilIs G L N xk g' (unitOn c) → secVal (B := k) g'.left W h f = c) ∧
      ∀ e' (v : epsAt x ⟶ G), IsTanAt G x v → (M.pt e').left = Spec.map (CommRingCat.ofHom (dualMap g)) ≫ v.left →
        ∀ h : ⊤ ≤ v.left ⁻¹ᵁ W, ∃ r, w e' = g (BT.valAt v.left W h f).snd + N * g r := by
  obtain ⟨hdom, T, _, Γ', i, L', _, _, M₀, j, χ, w₀, htor, hpt, ⟨s, hs, hv⟩, hwj⟩ := h
  have hkk := kL_comp hg
  have hk : Spec.map (CommRingCat.ofHom ((kL hg).comp (algebraMap R (FractionRing R)))) ≫ x = ξ := by
    rw [hkk]; exact hkx
  obtain ⟨W, f, hW, hf⟩ := hl hdom T inferInstance Γ' i htor s
  have hval : ∀ {B : Type} [CommRing B] (y : Spec (CommRingCat.of B) ⟶ Γ'.G.left) (h : ⊤ ≤ (y ≫ i) ⁻¹ᵁ W),
      BT.valAt (y ≫ i) W h f = BT.valAt y ⊤ le_top s := by
    intro B _ y h
    rw [valAt_comp, hf]
    exact valAt_res y (i ⁻¹ᵁ W) ⊤ le_top h le_top s
  obtain ⟨y, hy, hye⟩ := exists_alt (kL hg) hw htor hk χ
  refine ⟨y, hy, W, f, hW, ?_, ?_⟩
  · intro K _ _ a xk g' c h hxk hg' hweil
    obtain ⟨g₀, hg₀⟩ := hfull K a g' hg'
    have hg0 : g₀ ^ N = 1 := pow_descend a hg₀ hg'
    obtain ⟨t, ht⟩ := tors_pt (kL hg) htor hk g₀ hg0
    have hc := (hw.weil y g₀ hy hg0 K a xk g' c hxk hg₀).1 hweil
    have hsub : ∀ z : Spec (CommRingCat.of Ω), z = (spMap a) (IsLocalRing.closedPoint K) :=
      fun z => Subsingleton.elim (α := PrimeSpectrum Ω) _ _
    have h0 : ⊤ ≤ g₀.left ⁻¹ᵁ W := by
      intro z _
      have : g₀.left z = g'.left (IsLocalRing.closedPoint K) := by
        rw [hg₀, hsub z]; rfl
      show g₀.left z ∈ W
      rw [this]
      exact h (by trivial)
    have h1 : ⊤ ≤ ((Spec.map (CommRingCat.ofHom (kL hg)) ≫ (Γ'.pt t).left) ≫ i) ⁻¹ᵁ W := by
      have : (Spec.map (CommRingCat.ofHom (kL hg)) ≫ (Γ'.pt t).left) ≫ i = g₀.left := by
        rw [ht]; simp only [ptG, Category.assoc]
      rw [this]; exact h0
    have e1 : g'.left = spMap a ≫ (Spec.map (CommRingCat.ofHom (kL hg)) ≫ (Γ'.pt t).left) ≫ i := by
      rw [hg₀, ht]; simp only [ptG, Category.assoc]
    have e2 : secVal (B := K) g'.left W h f = BT.valAt (spMap a ≫ (Spec.map (CommRingCat.ofHom (kL hg)) ≫ (Γ'.pt t).left) ≫ i) W (by rw [← e1]; exact h) f :=
      valAt_congr e1 W _ _ f
    have e7 := valAt_spec (kL hg) (Y := Γ'.G.left) (Γ'.pt t).left ⊤ le_top le_top s
    have e8 : BT.valAt (Γ'.pt t).left ⊤ le_top s = algebraMap R (FractionRing R) (χ t : R) := hs t
    rw [e2, valAt_spec a _ W h1, hval]
    refine (congrArg a e7).trans ?_
    rw [e8, hc, hye t g₀ hg0 ht]
  · intro e' v htan hpte hh
    obtain ⟨e₀, he₀⟩ := M₀.onto v htan
    have hje : j e₀ = e' := M.inj (Over.OverMorphism.ext ((hpt e₀).trans (by subst he₀; exact hpte.symm)))
    obtain ⟨v', hv1, hv2, hv3⟩ := hv e₀
    rw [he₀] at hv2
    have h2 : ⊤ ≤ (v' ≫ i) ⁻¹ᵁ W := by
      rw [hv2]
      exact fun z _ => hh (by trivial)
    have e3 := valAt_mod v.left N hv2 W hh h2 f
    rw [hval, hv3] at e3
    obtain ⟨r', e5⟩ := snd_of_mod N _ _ e3
    refine ⟨r', ?_⟩
    rw [← hje, hwj, e5, map_add, map_mul, map_natCast]

include hkx in
theorem exists_data {w : Module.Dual Ω E}
    (hom : ∀ e' (v : epsAt x ⟶ G), IsTanAt G x v → (M.pt e').left = Spec.map (CommRingCat.ofHom (dualMap g)) ≫ v.left →
      ∃ r, g r = w e') (hg : Function.Injective g) :
    ∃ (L₀ : Type) (_ : AddCommGroup L₀) (_ : Module R L₀) (M₀ : LieModel G x L₀) (j : L₀ → E)
      (w₀ : Module.Dual R L₀), (∀ l, (M.pt (j l)).left = Spec.map (CommRingCat.ofHom (dualMap g)) ≫ (M₀.pt l).left) ∧
        ∀ l, w (j l) = g (w₀ l) := by
  subst hkx
  obtain ⟨L₀, _, _, ⟨M₀⟩⟩ := lieModel_exists X G R x
  have hψ : Spec.map (CommRingCat.ofHom (dualMap g)) ≫ (epsAt x).hom =
      (epsAt (Spec.map (CommRingCat.ofHom g) ≫ x)).hom := by
    simp only [epsAt, Over.mk_hom]
    rw [← Category.assoc, ← Category.assoc, ← spec_comp, ← spec_comp, dual_alg]
  let ψ : epsAt (Spec.map (CommRingCat.ofHom g) ≫ x) ⟶ epsAt x := Over.homMk _ hψ
  have hleft : ∀ l, (ψ ≫ M₀.pt l).left = Spec.map (CommRingCat.ofHom (dualMap g)) ≫ (M₀.pt l).left := fun l => rfl
  have htan : ∀ l, IsTanAt G (Spec.map (CommRingCat.ofHom g) ≫ x) (ψ ≫ M₀.pt l) := by
    intro l
    have t : _ ≫ (M₀.pt l).left = _ := M₀.tan l
    rw [one_left] at t
    show _ ≫ (ψ ≫ M₀.pt l).left = _
    rw [hleft, one_left, ← Category.assoc, ← spec_comp, dual_fst, spec_comp, Category.assoc, t]
    simp
  choose j hj using fun l => M.onto _ (htan l)
  have hjl : ∀ l, (M.pt (j l)).left = Spec.map (CommRingCat.ofHom (dualMap g)) ≫ (M₀.pt l).left := fun l => by
    rw [hj, hleft]
  have hc : ∀ l, ∃ r, g r = w (j l) := fun l => hom _ _ (M₀.tan l) (hjl l)
  choose c hc using hc
  have jadd : ∀ a b, j (a + b) = j a + j b := fun a b => M.inj (by
    rw [hj, M.add, M₀.add, hj, hj, comp_mul])
  have jsmul : ∀ (r : R) a, j (r • a) = g r • j a := fun r a => M.inj (Over.OverMorphism.ext (by
    rw [M.smul, hjl, hjl, M₀.smul, ← Category.assoc, ← Category.assoc, ← spec_comp, ← spec_comp, dual_eps]))
  let w₀ : Module.Dual R L₀ :=
    { toFun := c
      map_add' := fun a b => hg (by rw [map_add, hc, hc, hc, jadd, map_add])
      map_smul' := fun r a => hg (by
        rw [hc, jsmul, map_smul, smul_eq_mul, RingHom.id_apply, smul_eq_mul, map_mul, hc]) }
  exact ⟨L₀, _, _, M₀, j, w₀, hjl, fun l => (hc l).symm⟩

include hg hkx hw in
theorem core_ge [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (hN : N ≠ 0)
    (hfrac : ∀ a : Ω, ∃ b c : R, g c ≠ 0 ∧ a * g c = g b)
    {T : Type} [CommGroup T] (Γ' : QFGroup R T) (i : Γ'.G.left ⟶ G.left) (htor : Γ'.IsTorsionAlong G x N i)
    {y : Over.mk ξ ⟶ G} (hy : y ^ N = 1) {w : Module.Dual Ω E} (hq : x (IsLocalRing.closedPoint R) = q)
    {W : G.left.Opens} {f : Γ(G.left, W)} (hW : (η[G]).left q ∈ W)
    (ha : ∀ (k : Type) [Field k] [IsAlgClosed k] (i : Ω →+* k) (xk g' : Over.mk (spMap i ≫ ξ) ⟶ G) (c : kˣ)
        (h : ⊤ ≤ g'.left ⁻¹ᵁ W), xk.left = spMap i ≫ y.left → g' ^ N = 1 →
          Out.WeilIs G L N xk g' (unitOn c) → secVal (B := k) g'.left W h f = c)
    (hb : ∀ e' (v : epsAt x ⟶ G), IsTanAt G x v → (M.pt e').left = Spec.map (CommRingCat.ofHom (dualMap g)) ≫ v.left →
        ∀ h : ⊤ ≤ v.left ⁻¹ᵁ W, ∃ r, w e' = g (BT.valAt v.left W h f).snd + N * g r)
    (hom : ∀ e' (v : epsAt x ⟶ G), IsTanAt G x v → (M.pt e').left = Spec.map (CommRingCat.ofHom (dualMap g)) ≫ v.left →
      ∃ r, g r = w e') :
    M.IsHTFormOver N x g w := by
  have hkg : ∀ r, kL hg (algebraMap R (FractionRing R) r) = g r := fun r => RingHom.congr_fun (kL_comp hg) r
  have hk : Spec.map (CommRingCat.ofHom ((kL hg).comp (algebraMap R (FractionRing R)))) ≫ x = ξ := by
    rw [kL_comp hg]; exact hkx
  have hfrac' : ∀ a : Ω, ∃ b c : R, kL hg (algebraMap R _ c) ≠ 0 ∧
      a * kL hg (algebraMap R _ c) = kL hg (algebraMap R _ b) := fun a => by
    obtain ⟨b, c, h1, h2⟩ := hfrac a
    exact ⟨b, c, by rwa [hkg], by rw [hkg, hkg, h2]⟩
  have hfin : Finite T := by
    have := hw.finite
    choose g₁ hgN hgl using tors_ex (Γ' := Γ') (N := N) (i := i) (kL hg) htor hk
    exact Finite.of_injective (fun t => (⟨g₁ t, hgN t⟩ : {x : Over.mk ξ ⟶ G // x ^ N = 1}))
      (fun s t h => tors_inj (kL hg) htor ((hgl s).symm.trans
        ((congrArg (fun z : {x : Over.mk ξ ⟶ G // x ^ N = 1} => z.1.left) h).trans (hgl t))))
  obtain ⟨χ, hχ⟩ := exists_chi (kL hg) hw hN htor hk hfrac' hy
  obtain ⟨s, hs⟩ := PositivityTheory.UnitarySelfGeneration.ht_char_section R T Γ' χ

  have hval0 : ∀ g₁ : Over.mk ξ ⟶ G, g₁ ^ N = 1 → ∀ h : ⊤ ≤ g₁.left ⁻¹ᵁ W, BT.valAt g₁.left W h f = (e y g₁ : Ω) := by
    intro g₁ hg₁ h
    let a := algebraMap Ω (AlgebraicClosure Ω)
    let ψ : Over.mk (spMap a ≫ ξ) ⟶ Over.mk ξ := Over.homMk (spMap a) rfl
    have hg' : (ψ ≫ g₁) ^ N = 1 := by rw [← comp_pow', hg₁, MonObj.comp_one]
    have hwe := (hw.weil y g₁ hy hg₁ (AlgebraicClosure Ω) a (ψ ≫ y) (ψ ≫ g₁) (Units.map a.toMonoidHom (e y g₁))
      rfl rfl).2 rfl
    have h' : ⊤ ≤ (spMap a ≫ g₁.left) ⁻¹ᵁ W := fun z _ => h (by trivial)
    have h2 := ha (AlgebraicClosure Ω) a (ψ ≫ y) (ψ ≫ g₁) (Units.map a.toMonoidHom (e y g₁)) h' rfl hg' hwe
    apply a.injective
    exact (valAt_spec a g₁.left W h h' f).symm.trans h2
  have agree : (i.app W).hom f = Γ'.G.left.presheaf.map (homOfLE (le_top : i ⁻¹ᵁ W ≤ ⊤)).op s := by
    rw [← sub_eq_zero]
    refine GlobalTheory.T.section_eq_zero_of_values R T Γ' (i ⁻¹ᵁ W) _ (fun t h => ?_)
    obtain ⟨g₁, hgN, hgl⟩ := tors_ex (kL hg) htor hk t
    have h0 : ⊤ ≤ g₁.left ⁻¹ᵁ W := by
      rw [hgl]
      exact fun z _ => h (by trivial)
    have h1 := hval0 g₁ hgN h0
    have e1 : BT.valAt (Γ'.pt t).left (i ⁻¹ᵁ W) h ((i.app W).hom f) = algebraMap R _ (χ t : R) := by
      apply (kL hg).injective
      rw [← hχ t g₁ hgl, ← h1, ← valAt_comp (Γ'.pt t).left i W h f]
      have h3 : ⊤ ≤ (Spec.map (CommRingCat.ofHom (kL hg)) ≫ (Γ'.pt t).left ≫ i) ⁻¹ᵁ W := by
        have : Spec.map (CommRingCat.ofHom (kL hg)) ≫ (Γ'.pt t).left ≫ i = g₁.left := hgl.symm
        rw [this]; exact h0
      exact (valAt_spec (kL hg) ((Γ'.pt t).left ≫ i) W h h3 f).symm.trans (valAt_congr hgl.symm W h3 h0 f)
    have e2 : BT.valAt (Γ'.pt t).left (i ⁻¹ᵁ W) h (Γ'.G.left.presheaf.map (homOfLE (le_top : i ⁻¹ᵁ W ≤ ⊤)).op s) =
        algebraMap R _ (χ t : R) :=
      (valAt_res _ _ _ _ h le_top s).trans (hs t)
    rw [valAt_sub, e1, e2, sub_self]
  have fst1 : ∀ (v : epsAt x ⟶ G), IsTanAt G x v → ∀ h : ⊤ ≤ v.left ⁻¹ᵁ W, (BT.valAt v.left W h f).fst = 1 := by
    intro v hv h
    have h' : ⊤ ≤ (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫ v.left) ⁻¹ᵁ W :=
      fun z _ => h (by trivial)
    have e1 := valAt_spec (TrivSqZeroExt.fstHom R R R).toRingHom v.left W h h' f
    have e2 : Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫ v.left =
        (1 : Over.mk ξ ⟶ G).left := by
      have : _ ≫ v.left = _ := hv
      rw [this, one_left, one_left]
      simp [← hkx]
    have h'' : ⊤ ≤ (1 : Over.mk ξ ⟶ G).left ⁻¹ᵁ W := by
      rw [← e2]
      exact fun z _ => h' (by trivial)
    have e3 := hval0 1 (one_pow N) h''
    have e4 := valAt_spec g _ W h' (by rw [e2]; exact h'') f
    have e5 : g (BT.valAt v.left W h f).fst = 1 := by
      have e6 : (TrivSqZeroExt.fstHom R R R).toRingHom (BT.valAt v.left W h f) = (BT.valAt v.left W h f).fst := rfl
      rw [← e6, ← e1, ← e4, valAt_congr e2 W _ h'' f, e3]
      have := weil_pow hw hy (one_pow N) 0
      simpa using congrArg Units.val this
    exact hg (by rw [e5, map_one])
  obtain ⟨L₀, _, _, M₀, j, w₀, hjl, hwj⟩ := exists_data hkx M hom hg
  refine ⟨inferInstance, T, inferInstance, Γ', i, L₀, inferInstance, inferInstance, M₀, j, χ, w₀, htor, hjl, ⟨s, hs, fun l => ?_⟩, hwj⟩
  obtain ⟨v', ⟨hv1, hv2⟩, -⟩ := GlobalTheory.T.existsUnique_tangent_dual_number R T Γ' X G x N i htor L₀ M₀ l
  refine ⟨v', hv1, hv2, ?_⟩
  have hl : ⊤ ≤ (M₀.pt l).left ⁻¹ᵁ W := tan_mem x _ (M₀.tan l) W (by rw [hq]; exact hW)
  have h2 : ⊤ ≤ (v' ≫ i) ⁻¹ᵁ W := by
    rw [hv2]
    exact fun z _ => hl (by trivial)
  obtain ⟨r, hr⟩ := hb (j l) _ (M₀.tan l) (hjl l) hl
  have e5 : w₀ l = (BT.valAt (M₀.pt l).left W hl f).snd + N * r := hg (by
    rw [← hwj, hr, map_add, map_mul, map_natCast])
  have e6 : BT.valAt v' ⊤ le_top s = BT.valAt (v' ≫ i) W h2 f := by
    rw [valAt_comp, agree]
    exact (valAt_res v' (i ⁻¹ᵁ W) ⊤ le_top h2 le_top s).symm
  rw [e6, valAt_mod (M₀.pt l).left N hv2 W hl h2 f]
  exact mod_of_snd N _ _ r (fst1 _ (M₀.tan l) hl) e5

include hkx hg in
theorem core_smul [IsDomain R] {T : Type} [CommGroup T] [Finite T] (Γ' : QFGroup R T) (i : Γ'.G.left ⟶ G.left)
    (htor : Γ'.IsTorsionAlong G x N i) {w : Module.Dual Ω E}
    (hom : ∀ e' (v : epsAt x ⟶ G), IsTanAt G x v → (M.pt e').left = Spec.map (CommRingCat.ofHom (dualMap g)) ≫ v.left →
      ∃ r, g r = w e') :
    M.IsHTFormOver N x g ((N : Ω) • w) := by
  obtain ⟨L₀, _, _, M₀, j, w₀, hjl, hwj⟩ := exists_data hkx M hom hg
  refine ⟨inferInstance, T, inferInstance, Γ', i, L₀, inferInstance, inferInstance, M₀, j, 1, (N : R) • w₀, htor, hjl,
    ⟨1, fun t => ?_, fun l => ?_⟩, fun l => ?_⟩
  · refine (valAt_one (Y := Γ'.G.left) (Γ'.pt t).left ⊤ le_top).trans ?_
    simp
  · obtain ⟨v', ⟨hv1, hv2⟩, -⟩ := GlobalTheory.T.existsUnique_tangent_dual_number R T Γ' X G x N i htor L₀ M₀ l
    refine ⟨v', hv1, hv2, (valAt_one v' ⊤ le_top).trans ?_⟩
    have hN : Ideal.Quotient.mk (Ideal.span {(N : R)}) (((N : R) • w₀) l) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (by
        simpa using Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self (N : R)))
    rw [hN]
    simp
  · simp [hwj]

end core
end main
end GlobalTheory.CompanionTheory.Ar.HTTieK

namespace GlobalTheory.CompanionTheory.Ar.LieModel

open GlobalTheory.CompanionTheory.Ar.HTTieK

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

theorem htLat_le_omLatK (M : LieModel G ξ E) (N : ℕ) (p : Cpt ξ) : M.htLat N p ≤ M.omLat p :=
  Submodule.span_le.2 fun w h => form_mem_omLat M N p w h

theorem natCast_smul_mem_htLatK [IsCommMonObj G] (hξ : IsCptGen ξ) (M : LieModel G ξ E) (N : ℕ) (p : Cpt ξ)
    [IsDomain (X.presheaf.stalk p.1)] {T : Type} [CommGroup T] [Finite T] (Γ' : QFGroup (X.presheaf.stalk p.1) T)
    (i : Γ'.G.left ⟶ G.left) (htor : Γ'.IsTorsionAlong G (X.fromSpecStalk p.1) N i) {w : Module.Dual Ω E}
    (hw : w ∈ M.omLat p) : (N : Ω) • w ∈ M.htLat N p :=
  Submodule.subset_span (core_smul (hξ.inj p) (hk_stalk ξ p) M Γ' i htor
    fun e' v a b => hw e' (Submodule.subset_span ⟨v, a, b⟩))

theorem htLat_eq_htOmK [IsCommMonObj G] [IsSeparated G.hom] (hξ : IsCptGen ξ) (M : LieModel G ξ E) (L : LB G.left)
    {N : ℕ} (hN : N ≠ 0) (hfull : FullTorsion G ξ N) {e : (Over.mk ξ ⟶ G) → (Over.mk ξ ⟶ G) → Ωˣ}
    (hw : GenWeil G L ξ N e) (p : Cpt ξ) [IsIntegrallyClosed (X.presheaf.stalk p.1)]
    [IsNoetherianRing (X.presheaf.stalk p.1)]
    (hΓ : ∃ (_ : IsDomain (X.presheaf.stalk p.1)) (T : Type) (_ : CommGroup T)
      (Γ' : QFGroup (X.presheaf.stalk p.1) T) (i : Γ'.G.left ⟶ G.left),
      Γ'.IsTorsionAlong G (X.fromSpecStalk p.1) N i) :
    M.htLat N p = M.htOm L N p := by
  obtain ⟨hd, T, _, Γ', i, htor⟩ := hΓ
  have hd' : IsDomain (X.presheaf.stalk p.1) := hd
  apply le_antisymm
  · refine Submodule.span_le.2 fun w h => ?_
    obtain ⟨y, hy, W, f, hW, hA, hB⟩ := core_le (hξ.inj p) (hk_stalk ξ p) M hw (q := p.1) hfull w
      (fun hd₁ T₁ _ Γ₁ i₁ h₁ s => lift_sec p.1 Γ₁ N i₁ h₁ s) h
    refine Submodule.subset_span ⟨y, hy, form_mem_omLat M N p w h, W, f, hW, hA, fun e' v hv h' => ?_⟩
    obtain ⟨r, hr⟩ := hB e' v hv.1 hv.2 h'
    exact ⟨genMap ξ p r, ⟨r, rfl⟩, hr⟩
  · refine Submodule.span_le.2 ?_
    rintro w ⟨y, hy, hom, W, f, hW, hA, hB⟩
    refine Submodule.subset_span (core_ge (hξ.inj p) (hk_stalk ξ p) M hw (q := p.1) hN (GlobalTheory.T.exists_stalk_fraction_of_generic ξ hξ p) Γ' i htor hy
      Scheme.fromSpecStalk_closedPoint hW hA (fun e' v a b h' => ?_) (fun e' v a b => hom e' (Submodule.subset_span ⟨v, a, b⟩)))
    obtain ⟨_, ⟨r', rfl⟩, hr⟩ := hB e' v ⟨a, b⟩ h'
    exact ⟨r', hr⟩

end GlobalTheory.CompanionTheory.Ar.LieModel
