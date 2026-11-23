import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.WtAlg

theorem valR_eq' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f : Γ(X, U)) : valR x U f = (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((x.appLE U ⊤ h).hom f) := dif_pos h

theorem valR_add' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f g : Γ(X, U)) : valR x U (f + g) = valR x U f + valR x U g := by
  simp only [valR_eq' x U h, map_add]

theorem valR_sub' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f g : Γ(X, U)) : valR x U (f - g) = valR x U f - valR x U g := by
  simp only [valR_eq' x U h, map_sub]

theorem valR_mul'' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f g : Γ(X, U)) : valR x U (f * g) = valR x U f * valR x U g := by
  simp only [valR_eq' x U h, map_mul]

theorem valR_zero' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) :
    valR x U (0 : Γ(X, U)) = 0 := by
  unfold valR; split_ifs <;> simp

theorem valR_natCast' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (m : ℕ) : valR x U (m : Γ(X, U)) = m := by
  simp only [valR_eq' x U h, map_natCast]

theorem appLE_congr_top {P P' : Scheme.{0}} (b b' : P ⟶ P') (e : b = b') (h h') :
    b.appLE ⊤ ⊤ h = b'.appLE ⊤ ⊤ h' := by
  subst e; rfl

theorem valR_constFn_congr {A B : Type} [CommRing A] [CommRing B] {X : Scheme.{0}} (x x' : Sp A ⟶ X) (p : X ⟶ Sp B)
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ x' ⁻¹ᵁ U) (e : x ≫ p = x' ≫ p) (r : B) :
    valR x U (constFn p U r) = valR x' U (constFn p U r) := by
  have key : ∀ (b : Sp A ⟶ X) (hb : ⊤ ≤ b ⁻¹ᵁ U) (y : Γ(Sp B, ⊤)),
      (b.appLE U ⊤ hb).hom ((p.appLE ⊤ U (fun _ _ => trivial)).hom y) = ((b ≫ p).appLE ⊤ ⊤ (fun _ _ => trivial)).hom y := by
    intro b hb y
    rw [← Scheme.Hom.appLE_comp_appLE]; rfl
  rw [valR_eq' x U h, valR_eq' x' U h', constFn, key, key]
  have hh := appLE_congr_top (x ≫ p) (x' ≫ p) e (fun _ _ => trivial) (fun _ _ => trivial)
  rw [hh]

theorem rsT_self {X : Scheme.{0}} {O : X.Opens} (s : Γ(X, O)) : rsT s O = s := by
  simp [rsT, resG]

end GlobalTheory.Heat.WtAlg

namespace GlobalTheory.Heat.WtAlg

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} {Y : Ray oa}

theorem c_zero {S : Type} [CommRing S] {φ : R →+* S} (x x' : Over.mk (spMap φ) ⟶ Y.H) (c : Q.X → Sˣ)
    (hc : ∀ χ y J, Good Q.P.L y J →
      val ((Y.Φ _ x').s χ) (𝟙 _) y J = gm (𝟙 (Over.mk (spMap φ)).left) y ⊤ (unitOn (c χ)) * val ((Y.Φ _ x).s χ) (𝟙 _) y J) :
    c 0 = 1 := by
  have hu : unitOn (c 0) = 1 := unit_ext fun y _ => by
    obtain ⟨J, hJ, -⟩ := exists_good Q.P.L Q.P.isLB y (K := PEmpty.{1}) PEmpty.elim PEmpty.elim
      (fun a => a.elim) (fun a => a.elim)
    have e := hc 0 y J hJ
    rw [(val_corr hJ (Y.Φ _ x').s_zero _).trans (val_one _), (val_corr hJ (Y.Φ _ x).s_zero _).trans (val_one _),
      _root_.mul_one] at e
    rw [map_one]; exact e.symm
  have := congrArg (fun u : (Γ(Sp S, ⊤))ˣ => (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom u.val) hu
  simp only [unitOn, Units.coe_map, Units.val_one, map_one] at this
  exact Units.ext ((Iso.inv_hom_id_apply _ _).symm.trans this)

theorem isWt_add {α : Q.X} {V : Y.H.left.Opens} {f g : Γ(Y.H.left, V)} (hf : IsWt Y α V f) (hg : IsWt Y α V g) :
    IsWt Y α V (f + g) := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  rw [valR_add' _ _ hV', valR_add' _ _ hV, hf S φ x x' c a a' ha ha' hV hV' hq hc,
    hg S φ x x' c a a' ha ha' hV hV' hq hc, mul_add]

theorem isWt_sub {α : Q.X} {V : Y.H.left.Opens} {f g : Γ(Y.H.left, V)} (hf : IsWt Y α V f) (hg : IsWt Y α V g) :
    IsWt Y α V (f - g) := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  rw [valR_sub' _ _ hV', valR_sub' _ _ hV, hf S φ x x' c a a' ha ha' hV hV' hq hc,
    hg S φ x x' c a a' ha ha' hV hV' hq hc, mul_sub]

theorem isWt_zero (α : Q.X) (V : Y.H.left.Opens) : IsWt Y α V 0 := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  rw [valR_zero', valR_zero', mul_zero]

theorem isWt_sum {α : Q.X} {V : Y.H.left.Opens} {I : Type} (s : Finset I) (f : I → Γ(Y.H.left, V))
    (hf : ∀ i ∈ s, IsWt Y α V (f i)) : IsWt Y α V (∑ i ∈ s, f i) :=
  Finset.sum_induction f (IsWt Y α V) (fun _ _ => isWt_add) (isWt_zero α V) hf

theorem isRaynaudTorusWeightFunction_weightZero_mul {α : Q.X} {V : Y.H.left.Opens} {g f : Γ(Y.H.left, V)} (hg : IsWt Y 0 V g) (hf : IsWt Y α V f) :
    IsWt Y α V (g * f) := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  rw [valR_mul'' _ _ hV', valR_mul'' _ _ hV, hg S φ x x' c a a' ha ha' hV hV' hq hc,
    hf S φ x x' c a a' ha ha' hV hV' hq hc, c_zero x x' c hc, Units.val_one, _root_.one_mul]
  ring

theorem isWt_natCast (V : Y.H.left.Opens) (m : ℕ) : IsWt Y 0 V (m : Γ(Y.H.left, V)) := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  rw [valR_natCast' _ _ hV', valR_natCast' _ _ hV, c_zero x x' c hc, Units.val_one, _root_.one_mul]

theorem isWt_constFn (V : Y.H.left.Opens) (r : R) : IsWt Y 0 V (constFn Y.H.hom V r) := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  subst ha ha'
  rw [valR_constFn_congr x'.left x.left Y.H.hom V hV' hV ((Over.w x').trans (Over.w x).symm) r,
    c_zero x x' c hc, Units.val_one, _root_.one_mul]

end GlobalTheory.Heat.WtAlg

namespace GlobalTheory.Heat.WtAlg

theorem op_isWt : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} (dd : Fin n → Fld Y.H.left) (D : R → R) (h : Heat Y.H Y.q.left Q.P.L dd D), (∀ a (α : Q.X) (V : Y.H.left.Opens) f, IsWt Y α V f → IsWt Y α V (dd a V f)) → IsBasic Y h → ∀ (i : h.J) (k : ℕ) (α : Q.X) (f : Γ(Y.H.left, h.W i)), IsWt Y α (h.W i) f → IsWt Y α (h.W i) (op Y.H dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (h.W i) f) := by
  intro R _ _ Q O _ _ _ oa Y n dd D h hdd hB i k α f hf
  obtain ⟨⟨V, hV⟩, hp, hp', hd⟩ := hB i
  have key : ∀ g : Γ(Y.H.left, h.W i), IsWt Y α (h.W i) g → IsWt Y α (h.W i) (h.d i (h.W i) g) := by
    have := hd α V hV.ge
    rw [← hV] at this
    exact this
  have h2 : IsWt Y 0 (h.W i) (2 : Γ(Y.H.left, h.W i)) := by simpa using isWt_natCast (Y := Y) (h.W i) 2
  have hk : IsWt Y 0 (h.W i) (k : Γ(Y.H.left, h.W i)) := isWt_natCast (h.W i) k
  have hk2 : IsWt Y 0 (h.W i) ((k : Γ(Y.H.left, h.W i)) ^ 2) := by rw [sq]; exact isRaynaudTorusWeightFunction_weightZero_mul hk hk
  have hrp : IsWt Y 0 (h.W i) (rsT (h.p i) (h.W i)) := by rw [rsT_self]; exact hp
  have hrp' : IsWt Y 0 (h.W i) (rsT (h.p' i) (h.W i)) := by rw [rsT_self]; exact hp'
  unfold op
  refine isWt_add (isWt_add (isWt_sub ?_ ?_) ?_) ?_
  · exact isRaynaudTorusWeightFunction_weightZero_mul (isRaynaudTorusWeightFunction_weightZero_mul h2 hk) (key f hf)
  · exact isWt_sum _ _ fun a _ => isWt_sum _ _ fun b _ =>
      isRaynaudTorusWeightFunction_weightZero_mul (isWt_constFn _ _) (hdd _ _ _ _ (hdd _ _ _ _ hf))
  · exact isRaynaudTorusWeightFunction_weightZero_mul h2 (isWt_sum _ _ fun a _ => isRaynaudTorusWeightFunction_weightZero_mul (isWt_constFn _ _) (hdd _ _ _ _ hf))
  · exact isRaynaudTorusWeightFunction_weightZero_mul (isWt_add (isRaynaudTorusWeightFunction_weightZero_mul (isRaynaudTorusWeightFunction_weightZero_mul h2 hk2) hrp) (isRaynaudTorusWeightFunction_weightZero_mul (isRaynaudTorusWeightFunction_weightZero_mul h2 hk) hrp')) hf

end GlobalTheory.Heat.WtAlg
