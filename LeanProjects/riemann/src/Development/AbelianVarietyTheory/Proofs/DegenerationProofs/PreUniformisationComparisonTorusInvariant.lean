import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsUniquePartner
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ComparisonTorusInvariant

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section

namespace GlobalTheory

namespace PreTorusInvariance

theorem cube_alg {V : Type} [CommGroup V] {A : Type} [CommGroup A] {a W W' d : A → V} (h : ∀ x, a x * W' x = W x * d x)
    {x y u : A} {C C' c c' : V}
    (h₁ : C * W (x * y) * W (x * u) * W (y * u) * W 1 = W (x * y * u) * W x * W y * W u * c)
    (h₂ : C' * W' (x * y) * W' (x * u) * W' (y * u) * W' 1 = W' (x * y * u) * W' x * W' y * W' u * c')
    (h₃ : c * d (x * y) * d (x * u) * d (y * u) * d 1 = d (x * y * u) * d x * d y * d u * c') :
    C = a (x * y * u) * (a (x * y))⁻¹ * (a (x * u))⁻¹ * (a (y * u))⁻¹ * a x * a y * a u * (a 1)⁻¹ * C' := by
  have E := fun {p q : V} (e : p = q) => congrArg Additive.ofMul e
  have a₁ := E h₁; have a₂ := E h₂; have a₃ := E h₃
  have b₁ := E (h (x * y * u)); have b₂ := E (h (x * y)); have b₃ := E (h (x * u)); have b₄ := E (h (y * u))
  have b₅ := E (h x); have b₆ := E (h y); have b₇ := E (h u); have b₈ := E (h 1)
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv] at *
  linear_combination (norm := abel) a₁ - a₂ + a₃ - b₁ + b₂ + b₃ + b₄ - b₅ - b₆ - b₇ + b₈

theorem even_alg {V : Type} [CommGroup V] {A : Type} [CommGroup A] {a W W' d : A → V} (h : ∀ x, a x * W' x = W x * d x)
    {x : A} {s s' c c' : V} (h₁ : s * W x = W x⁻¹ * c) (h₂ : s' * W' x = W' x⁻¹ * c') (h₃ : c * d x = d x⁻¹ * c') :
    s * a x = a x⁻¹ * s' := by
  have E := fun {p q : V} (e : p = q) => congrArg Additive.ofMul e
  have a₁ := E h₁; have a₂ := E h₂; have a₃ := E h₃
  have b₁ := E (h x); have b₂ := E (h x⁻¹)
  apply Additive.ofMul.injective
  simp only [ofMul_mul] at *
  linear_combination (norm := abel) a₁ - a₂ + a₃ + b₁ - b₂

theorem vals_id {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {P P' : CP G}
    {w : LB.Iso P'.L.L (P.L.L.pull (𝟙 G.left))} {hw : 𝟙 G.left ≫ G.hom = G.hom ≫ 𝟙 _}
    (h : IsCPMap P' P (𝟙 _) (𝟙 G.left) hw w) {T : Over S} {z : T.left} {N N'} (hN : Good P.L.L z N)
    (hN' : Good P'.L.L z N') (d : (T ⟶ G) → (T.left.presheaf.stalk z)ˣ)
    (hd : ∀ x, d x = gw w x.left z (N x.left) (N' x.left)) {B : Type} [CommGroup B] (β : B →* (T ⟶ G)) :
    (∀ x, val P.sym (β x).left z N * d (β x) = d (β x⁻¹) * val P'.sym (β x).left z N') ∧
    ∀ x y u, cubV P.c z N (β x) (β y) (β u) * d (β (x * y)) * d (β (x * u)) * d (β (y * u)) * d (β 1) =
      d (β (x * y * u)) * d (β x) * d (β y) * d (β u) * cubV P'.c z N' (β x) (β y) (β u) := by
  obtain ⟨-, s, c⟩ := h.vals T z N' N hN' hN d (fun x => by rw [hd, Category.comp_id])
  refine ⟨fun x => ?_, fun x y u => ?_⟩
  · have s := s (β x)
    rwa [Category.comp_id, ← map_inv] at s
  · have c := c (β x) (β y) (β u)
    rw [_root_.id, cubV_toBase_id] at c
    simp only [map_mul, map_one]
    exact c

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] {e : ℕ} {D D' : DegPre R} {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {U : PreU I D A G} {U' : PreU I D' A' G}

def cubP (g : GtCoord I D e G) {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (z : T.left)
    (J : (T.left ⟶ D.P.A.left) → D.P.L.ι) (x y u : T ⟶ thickObj R I e G) : (T.left.presheaf.stalk z)ˣ :=
  cubV D.cub (T := (Over.map (thick R I e)).obj T) z J
    ((Over.map (thick R I e)).map x ≫ g.pG) ((Over.map (thick R I e)).map y ≫ g.pG)
    ((Over.map (thick R I e)).map u ≫ g.pG)

theorem cubP_congr (g : GtCoord I D e G) {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (z : T.left)
    (J : (T.left ⟶ D.P.A.left) → D.P.L.ι) {a b a' b' : T ⟶ thickObj R I e G} (c : T ⟶ thickObj R I e G)
    (ha : a ≫ g.q = a' ≫ g.q) (hb : b ≫ g.q = b' ≫ g.q) : cubP g z J a b c = cubP g z J a' b' c := by
  have k : ∀ {a a' : T ⟶ thickObj R I e G}, a ≫ g.q = a' ≫ g.q →
      (Over.map (thick R I e)).map a ≫ g.pG = (Over.map (thick R I e)).map a' ≫ g.pG := fun h =>
    Over.OverMorphism.ext (TorusInvariance.pG_congr g h)
  unfold cubP
  rw [k ha, k hb]

theorem vals (u : LB.Iso (D'.P.L.pull (U'.gt e).pG.left) (D.P.L.pull (U.gt e).pG.left))
    {wL : LB.Iso U'.P.L.L (U.P.L.L.pull (𝟙 G.left))} {hw : 𝟙 G.left ≫ G.hom = G.hom ≫ 𝟙 _}
    (hL : IsCPMap U'.P U.P (𝟙 _) (𝟙 G.left) hw wL)
    (sq : ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.P.L.ι) (jM' : D'.P.L.ι)
      (jL : U.P.L.L.ι) (jL' : U'.P.L.L.ι), (U.gt e).pG.left (r z) ∈ D.P.L.U jM →
      (U'.gt e).pG.left (r z) ∈ D'.P.L.U jM' → (fstG I e G).left (r z) ∈ U.P.L.L.U jL →
      (fstG I e G).left (r z) ∈ U'.P.L.L.U jL' →
      gw u r z jM (fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') =
        gw (U.w e) r z jM (fun _ => jL) * gw wL (r ≫ (fstG I e G).left) z jL jL')
    {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} {z : T.left} {J : (T.left ⟶ D.P.A.left) → D.P.L.ι}
    {J' : (T.left ⟶ D'.P.A.left) → D'.P.L.ι} (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J')
    (a : (T.left ⟶ (thickObj R I e G).left) → (T.left.presheaf.stalk z)ˣ)
    (ha : ∀ r, a r = gw u r z (J (r ≫ (U.gt e).pG.left)) (fun _ => J' (r ≫ (U'.gt e).pG.left))) :
    (∀ x : T ⟶ thickObj R I e G, val D.sym (x.left ≫ (U.gt e).pG.left) z J * a x.left =
      a (x⁻¹).left * val D'.sym (x.left ≫ (U'.gt e).pG.left) z J') ∧
    ∀ x y v : T ⟶ thickObj R I e G, cubP (U.gt e) z J x y v =
      a (x * y * v).left * (a (x * y).left)⁻¹ * (a (x * v).left)⁻¹ * (a (y * v).left)⁻¹ * a x.left * a y.left *
        a v.left * (a (1 : T ⟶ thickObj R I e G).left)⁻¹ * cubP (U'.gt e) z J' x y v := by
  obtain ⟨N, hN⟩ := exists_good_pt U.P.L.isLB z
  obtain ⟨N', hN'⟩ := exists_good_pt U'.P.L.isLB z
  obtain ⟨W, hW⟩ : ∃ W : (T ⟶ thickObj R I e G) → (T.left.presheaf.stalk z)ˣ, ∀ x, W x =
    gw (U.w e) x.left z (J (x.left ≫ (U.gt e).pG.left)) (fun _ => N (x.left ≫ (fstG I e G).left)) := ⟨_, fun _ => rfl⟩
  obtain ⟨W', hW'⟩ : ∃ W : (T ⟶ thickObj R I e G) → (T.left.presheaf.stalk z)ˣ, ∀ x, W x =
    gw (U'.w e) x.left z (J' (x.left ≫ (U'.gt e).pG.left)) (fun _ => N' (x.left ≫ (fstG I e G).left)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : ((Over.map (thick R I e)).obj T ⟶ G) → (T.left.presheaf.stalk z)ˣ, ∀ x, d x =
    gw wL x.left z (N x.left) (N' x.left) := ⟨_, fun _ => rfl⟩
  obtain ⟨-, s₁, c₁⟩ := U.w_vals e T z N J hN hJ W hW
  obtain ⟨-, s₂, c₂⟩ := U'.w_vals e T z N' J' hN' hJ' W' hW'
  let β : (T ⟶ thickObj R I e G) →* ((Over.map (thick R I e)).obj T ⟶ G) :=
    MonoidHom.mk' (fun x => (Over.map (thick R I e)).map x ≫ fstG I e G) fun x y =>
      toBase_mul_pullback G (thick R I e) T x y
  obtain ⟨s₃, c₃⟩ := vals_id hL (T := (Over.map (thick R I e)).obj T) hN hN' d hd β
  have h : ∀ x : T ⟶ thickObj R I e G, a x.left * W' x = W x * d (β x) := fun x => by
    rw [ha, hW, hW', hd]
    exact sq _ x.left z _ _ _ _ (hJ _) (hJ' _) (hN _) (hN' _)
  refine ⟨fun x => ?_, fun x y v => ?_⟩
  · exact even_alg (a := fun x => a x.left) (d := fun x => d (β x)) h (s₁ x) (s₂ x) (s₃ x)
  · obtain ⟨c, hc⟩ : ∃ c : (T.left.presheaf.stalk z)ˣ,
      c = cubV U.P.c (T := (Over.map (thick R I e)).obj T) z N (β x) (β y) (β v) := ⟨_, rfl⟩
    obtain ⟨c', hc'⟩ : ∃ c : (T.left.presheaf.stalk z)ˣ,
      c = cubV U'.P.c (T := (Over.map (thick R I e)).obj T) z N' (β x) (β y) (β v) := ⟨_, rfl⟩
    have k₁ : cubP (U.gt e) z J x y v * W (x * y) * W (x * v) * W (y * v) * W 1 =
      W (x * y * v) * W x * W y * W v * c := (c₁ x y v).trans (congrArg (_ * ·) hc.symm)
    have k₂ : cubP (U'.gt e) z J' x y v * W' (x * y) * W' (x * v) * W' (y * v) * W' 1 =
      W' (x * y * v) * W' x * W' y * W' v * c' := (c₂ x y v).trans (congrArg (_ * ·) hc'.symm)
    have k₃ : c * d (β (x * y)) * d (β (x * v)) * d (β (y * v)) * d (β 1) =
        d (β (x * y * v)) * d (β x) * d (β y) * d (β v) * c' := by
      rw [hc, hc']; exact c₃ x y v
    have k := cube_alg (A := T ⟶ thickObj R I e G) (a := fun x => a x.left) (d := fun x => d (β x)) h k₁ k₂ k₃
    exact k

end PreTorusInvariance

open TorusInvariance PreTorusInvariance in
set_option maxHeartbeats 400000 in

theorem preU_comparison_torus_invariant : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R) (D D' : DegPre R) (A A' : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (U' : PreU I D' A' G) (wL : LB.Iso U'.P.L.L (U.P.L.L.pull (𝟙 G.left))) (hw : 𝟙 G.left ≫ G.hom = G.hom ≫ 𝟙 _), IsCPMap U'.P U.P (𝟙 _) (𝟙 G.left) hw wL → ∀ (e : ℕ) (β : thickObj R I e D'.P.A ≅ thickObj R I e D.P.A), (U'.gt e).q ≫ β.hom = (U.gt e).q → ∀ u : LB.Iso (D'.P.L.pull (U'.gt e).pG.left) (D.P.L.pull (U.gt e).pG.left), u.IsGen → (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.P.L.ι) (jM' : D'.P.L.ι) (jL : U.P.L.L.ι) (jL' : U'.P.L.L.ι), (U.gt e).pG.left (r z) ∈ D.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.P.L.U jM' → (fstG I e G).left (r z) ∈ U.P.L.L.U jL → (fstG I e G).left (r z) ∈ U'.P.L.L.U jL' → gw u r z jM (fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') = gw (U.w e) r z jM (fun _ => jL) * gw wL (r ≫ (fstG I e G).left) z jL jL') → ∀ (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (τ : Z ⟶ splitTorus _ D.X) (y : Z ⟶ thickObj R I e G) (z : Z.left) (jM : D.P.L.ι) (jM' : D'.P.L.ι), (U.gt e).pG.left (y.left z) ∈ D.P.L.U jM → (U'.gt e).pG.left (y.left z) ∈ D'.P.L.U jM' → gw u ((τ ≫ (U.gt e).i) * y).left z jM (fun _ => jM') = gw u y.left z jM (fun _ => jM') := by
  intro R _ _ _ I D D' A A' G _ _ U U' wL hw hL e β hβ u hu sq Z₀ τ₀ y₀ z₀ jM jM' m m'
  have := (U.gt e).q_hom
  have := (U'.gt e).q_hom
  have := (U.gt e).i_hom
  have := U.semi.geomConnected
  have := connectedSpace_spec_quotient (I ^ (e + 1)) (Z₀.hom z₀)
  have : GeometricallyConnected (thickObj R I e G).hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd G.hom (thick R I e)))
  have : ConnectedSpace (thickObj R I e G).left :=
    GroupConn.connectedSpace_of_section (thickObj R I e G).hom (η : 𝟙_ _ ⟶ thickObj R I e G).left (Over.w _)
  have hq : ∀ {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (τ : Z ⟶ splitTorus _ D.X),
      (τ ≫ (U.gt e).i) ≫ (U.gt e).q = (1 : Z ⟶ thickObj R I e G) ≫ (U.gt e).q := fun τ => by
    rw [Category.assoc, (U.gt e).isKernel.w, MonObj.one_comp, ← Category.assoc, comp_toUnit, Hom.one_def]
  have hq' : ∀ {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (τ : Z ⟶ splitTorus _ D.X),
      (τ ≫ (U.gt e).i) ≫ (U'.gt e).q = (1 : Z ⟶ thickObj R I e G) ≫ (U'.gt e).q := fun τ => by
    rw [← cancel_mono β.hom, Category.assoc _ _ β.hom, Category.assoc _ _ β.hom, hβ]
    exact hq τ
  have hp : ∀ {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (τ : Z ⟶ splitTorus _ D.X)
      (y : Z ⟶ thickObj R I e G), ((τ ≫ (U.gt e).i) * y).left ≫ (U.gt e).pG.left = y.left ≫ (U.gt e).pG.left :=
    fun τ y => pG_congr _ (by rw [MonObj.mul_comp, hq, ← MonObj.mul_comp, _root_.one_mul])
  have hp' : ∀ {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (τ : Z ⟶ splitTorus _ D.X)
      (y : Z ⟶ thickObj R I e G), ((τ ≫ (U.gt e).i) * y).left ≫ (U'.gt e).pG.left = y.left ≫ (U'.gt e).pG.left :=
    fun τ y => pG_congr _ (by rw [MonObj.mul_comp, hq', ← MonObj.mul_comp, _root_.one_mul])
  obtain ⟨ρ, key⟩ := exists_ratio_translate (U.gt e).i D.P.isLB D'.P.isLB u hu (fun _ => hp) (fun _ => hp')
  have triv := ratio_eq_one (U.gt e).i ρ (fun Z z => by
    obtain ⟨J, hJ⟩ := exists_good_pt D.P.isLB z
    obtain ⟨J', hJ'⟩ := exists_good_pt D'.P.isLB z
    obtain ⟨a, ha⟩ : ∃ a : (Z.left ⟶ (thickObj R I e G).left) → (Z.left.presheaf.stalk z)ˣ,
      ∀ r, a r = gw u r z (J (r ≫ (U.gt e).pG.left)) (fun _ => J' (r ≫ (U'.gt e).pG.left)) := ⟨_, fun _ => rfl⟩
    obtain ⟨s, c⟩ := vals u hL sq hJ hJ' a ha
    refine ⟨a, fun t y => ?_, fun t t' y => ?_, fun t => ?_⟩
    · rw [ha, ha, hp, hp']
      exact key Z t y z _ _ (hJ _) (hJ' _)
    · have p := c (t ≫ (U.gt e).i) (t' ≫ (U.gt e).i) y
      have q := c 1 1 y
      rw [cubP_congr (U.gt e) z J y (hq t) (hq t'), cubP_congr (U'.gt e) z J' y (hq' t) (hq' t')] at p
      rw [prod_psum, prod_psum]
      exact mul_right_cancel (p.symm.trans q)
    · have p := s (t ≫ (U.gt e).i)
      have q := s 1
      rw [pG_congr (U.gt e) (hq t), pG_congr (U'.gt e) (hq' t)] at p
      exact cancel_even p q)
  rw [key Z₀ τ₀ y₀ z₀ jM jM' m m', triv, map_one, _root_.one_mul]

end GlobalTheory
