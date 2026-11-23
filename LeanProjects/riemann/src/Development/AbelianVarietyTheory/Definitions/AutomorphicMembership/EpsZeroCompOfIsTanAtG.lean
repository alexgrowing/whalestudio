import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.BoundaryLocalData GlobalTheory.ShFam
open GlobalTheory.LieVB GlobalTheory.Conormal
open GlobalTheory.Twist (resM resM_resM resM_self app_resM)
open GlobalTheory.QCoh (pullbackSections)
open ReciprocityTheory.ChartRestriction.G.Pdiv (specO)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocM

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

section Pairing

variable {X : Scheme.{0}} (t : SAB H X) {k : Type} [CommRing k] {x : Sp k ⟶ X} {v : Sp (DualNumber k) ⟶ t.G.left}

theorem epsZero_comp_of_isTanAtG (hv : IsTanAtG t x v) : sec (epsZero k) ≫ v = x ≫ unitSec t.G :=
  hv.2

def tanForm (hv : IsTanAtG t x v) :
    (Scheme.Modules.pullback x).obj (omega t.G) ⟶ GlobalTheory.structureModule (Sp k) :=
  baseMap (π := t.G.hom) (φ := v) (f := x) (sec_hom (epsZero k)) hv.1 (epsZero_comp_of_isTanAtG t hv) ≫ (epsIso k).hom

def tanEv (hv : IsTanAtG t x v) {V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ V) (s : Γ(omega t.G, V)) : k :=
  (Scheme.ΓSpecIso (.of k)).hom ((tanForm t hv).app ⊤ (pullbackSections x (omega t.G) h s))

theorem tanEv_add (hv : IsTanAtG t x v) {V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ V) (s s' : Γ(omega t.G, V)) :
    tanEv t hv h (s + s') = tanEv t hv h s + tanEv t hv h s' := by
  simp only [tanEv, map_add]
  exact map_add (Scheme.ΓSpecIso (.of k)).hom.hom _ _

theorem tanEv_smul (hv : IsTanAtG t x v) {V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ V) (a : Γ(X, V)) (s : Γ(omega t.G, V)) :
    tanEv t hv h (a • s) = (Scheme.ΓSpecIso (.of k)).hom (x.appLE V ⊤ h a) * tanEv t hv h s := by
  have e2 : (tanForm t hv).app ⊤ (pullbackSections x (omega t.G) h (a • s)) =
      x.appLE V ⊤ h a • (tanForm t hv).app ⊤ (pullbackSections x (omega t.G) h s) := by
    have e : pullbackSections x (omega t.G) h (a • s) = x.appLE V ⊤ h a • pullbackSections x (omega t.G) h s :=
      QCoh.pullbackSections_smul x (omega t.G) h a s
    rw [e]
    exact Scheme.Modules.Hom.app_smul _ _ _
  unfold tanEv
  rw [e2]
  exact map_mul (Scheme.ΓSpecIso (.of k)).hom.hom _ _

theorem tanEv_resM (hv : IsTanAtG t x v) {V V' : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ V') (h' : V' ≤ V) (s : Γ(omega t.G, V)) :
    tanEv t hv h (resM _ h' s) = tanEv t hv (h.trans (x.preimage_mono h')) s := by
  unfold tanEv
  congr 2
  exact QCoh.pullbackSections_res x (omega t.G) h h' s

theorem tanEv_dUnit (hv : IsTanAtG t x v) {V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ V) {W : t.G.left.Opens}
    (hW : V ≤ unitSec t.G ⁻¹ᵁ W) (hv' : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(t.G.left, W)) :
    tanEv t hv h (dUnit t.G hW f) = ((Scheme.ΓSpecIso (.of (DualNumber k))).hom (v.appLE W ⊤ hv' f)).snd := by
  have h1 : (baseMap (π := t.G.hom) (φ := v) (f := x) (sec_hom (epsZero k)) hv.1 (epsZero_comp_of_isTanAtG t hv)).app ⊤
      (pullbackSections x (conormal (unitSec t.G)) h (d (sec_hom η[t.G]) hW f)) =
      d (sec_hom (epsZero k)) (le_preimage_top _ ⊤) (v.appLE W ⊤ hv' f) :=
    baseMap_d (sec_hom η) (sec_hom (epsZero k)) hv.left (epsZero_comp_of_isTanAtG t hv) hW h
      (le_preimage_top (LieVB.sec (epsZero k)) ⊤) hv' f
  have h2 (P Q : Γ(Sp (DualNumber k), ⊤)) : d (sec_hom (epsZero k)) (le_preimage_top _ ⊤) (P * Q) =
      (sec (epsZero k)).appLE ⊤ ⊤ (le_preimage_top _ ⊤) P • d (sec_hom (epsZero k)) (le_preimage_top _ ⊤) Q +
      (sec (epsZero k)).appLE ⊤ ⊤ (le_preimage_top _ ⊤) Q • d (sec_hom (epsZero k)) (le_preimage_top _ ⊤) P :=
    d_mul (sec_hom (epsZero k)) (le_preimage_top (LieVB.sec (epsZero k)) ⊤) P Q
  have h3 (a : Γ(Sp k, ⊤)) : d (sec_hom (epsZero k)) (le_preimage_top _ ⊤)
      ((specO k (DualNumber k)).hom.appLE ⊤ ⊤ (le_preimage_top _ ⊤) a) = 0 :=
    d_base (sec_hom (epsZero k)) (le_preimage_top (LieVB.sec (epsZero k)) ⊤)
      (le_preimage_top (specO k (DualNumber k)).hom ⊤) a
  have hB (c : k) : (specO k (DualNumber k)).hom.appLE ⊤ ⊤ (le_preimage_top _ ⊤) (cst k c) =
      (Scheme.ΓSpecIso (.of (DualNumber k))).inv (algebraMap k (DualNumber k) c) := by
    rw [appLE_top]
    have e := congrArg (fun g => g.hom c)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k (DualNumber k))))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
    exact e.symm
  have hP (a : Γ(Sp k, ⊤)) :
      (sec (epsZero k)).appLE ⊤ ⊤ (le_preimage_top _ ⊤) ((specO k (DualNumber k)).hom.appLE ⊤ ⊤ (le_preimage_top _ ⊤) a) = a := by
    rw [appLE_top, appLE_top]
    have e := congrArg (fun g : Sp k ⟶ Sp k => g.appTop a) (sec_hom (epsZero k))
    simp at e
    exact e
  set F := v.appLE W ⊤ hv' f
  set D := (Scheme.ΓSpecIso (.of (DualNumber k))).hom F with hD
  have hdec : F = (specO k (DualNumber k)).hom.appLE ⊤ ⊤ (le_preimage_top _ ⊤) (cst k D.fst) +
      (specO k (DualNumber k)).hom.appLE ⊤ ⊤ (le_preimage_top _ ⊤) (cst k D.snd) * epsFn k := by
    rw [hB, hB, epsFn, ← map_mul, ← map_add]
    have e : algebraMap k (DualNumber k) D.fst + algebraMap k (DualNumber k) D.snd * DualNumber.eps = D := by
      ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [e, hD, Iso.hom_inv_id_apply]
  have hdF : d (sec_hom (epsZero k)) (le_preimage_top _ ⊤) F =
      (sec (epsZero k)).appLE ⊤ ⊤ (le_preimage_top _ ⊤)
          ((specO k (DualNumber k)).hom.appLE ⊤ ⊤ (le_preimage_top _ ⊤) (cst k D.snd)) •
        d (sec_hom (epsZero k)) (le_preimage_top _ ⊤) (epsFn k) := by
    rw [hdec, map_add, h3, h2, h3, smul_zero, add_zero, zero_add]
  have h4 : (tanForm t hv).app ⊤ (pullbackSections x (omega t.G) h (dUnit t.G hW f)) =
      (epsIso k).hom.app ⊤ (d (sec_hom (epsZero k)) (le_preimage_top _ ⊤) F) := by
    rw [← h1]
    exact (QCoh.app_app _ _ _ _).symm
  rw [tanEv, h4, hdF]
  erw [Scheme.Modules.Hom.app_smul, epsIso_d, hP]
  erw [smul_eq_mul, _root_.mul_one]
  simp

end Pairing

variable {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W}
  {i₀ : Idx H p}

abbrev Mdl.om (B : Mdl Y i₀) : B.X.Modules := omega B.t.G

structure Lat (B : Mdl Y i₀) : Type where

  N : VB.Sub B.om

  free : ∀ x : B.X, ∃ (V : B.X.Opens) (n : ℕ) (m : Fin n → Γ(N.toMod, V)), x ∈ V ∧ VB.IsFrame m

  gen : ∀ V : B.X.Opens, V ≤ B.genO → N.sec V = ⊤

def rangeSub {X : Scheme.{0}} {F G : X.Modules} (θ : F ⟶ G) [Mono θ] : VB.Sub G where
  sec V := LinearMap.range (QCoh.appLinear θ V)
  res_mem := by
    rintro V V' h _ ⟨s, rfl⟩
    exact ⟨resM F h s, app_resM θ h s⟩
  mem_of_local {V s} hs := by
    choose U hU hx t ht using fun x : V => hs x x.2
    have hc : V ≤ iSup U := fun x hxV => Opens.mem_iSup.2 ⟨⟨x, hxV⟩, hx _⟩
    have ht' (x : V) : θ.app _ (t x) = resM G (hU x) s := ht x
    obtain ⟨r, hr⟩ := Twist.exists_sec_of_cover U hU hc t fun x y => QCoh.injective_app_of_mono θ _ (by
      rw [app_resM, app_resM, ht', ht', resM_resM, resM_resM])
    exact ⟨r, Twist.sec_ext_of_cover U hU hc fun x =>
      (app_resM θ _ r).symm.trans ((congrArg _ (hr x)).trans (ht' x))⟩

theorem isIso_lift_rangeSub {X : Scheme.{0}} {F G : X.Modules} (θ : F ⟶ G) [Mono θ] :
    IsIso ((rangeSub θ).lift θ fun _ s => ⟨s, rfl⟩) := by
  set φ := (rangeSub θ).lift θ fun _ s => ⟨s, rfl⟩
  have hfac : φ ≫ (rangeSub θ).incl = θ := (rangeSub θ).lift_incl θ _
  have hsurj (V : X.Opens) (s : Γ((rangeSub θ).toMod, V)) : ∃ r, φ.app V r = s := by
    obtain ⟨r, hr⟩ := (rangeSub θ).incl_app_mem s
    refine ⟨r, (rangeSub θ).incl_app_injective V ?_⟩
    rw [QCoh.app_app, hfac]
    simpa using hr
  have : Mono φ := mono_of_mono_fac hfac
  have : Epi φ := ⟨fun {Z} g₁ g₂ h => by
    ext V s
    obtain ⟨r, rfl⟩ := hsurj V s
    rw [QCoh.app_app, QCoh.app_app, h]⟩
  exact isIso_of_mono_of_epi φ

namespace Lat

variable {B : Mdl Y i₀}

def ofBundle {F : B.X.Modules} (θ : F ⟶ B.om) [Mono θ]
    (hF : ∀ x : B.X, ∃ (V : B.X.Opens) (n : ℕ) (m : Fin n → Γ(F, V)), x ∈ V ∧ VB.IsFrame m)
    (hθ : ∀ V : B.X.Opens, V ≤ B.genO → Function.Surjective (θ.app V)) : Lat B where
  N := rangeSub θ
  free x :=
    have ⟨V, n, _, hx, hm⟩ := hF x
    have := isIso_lift_rangeSub θ
    ⟨V, n, _, hx, hm.map_iso ((rangeSub θ).lift θ fun _ s => ⟨s, rfl⟩)⟩
  gen V h := LinearMap.range_eq_top.2 (hθ V h)

theorem mem_ofBundle {F : B.X.Modules} (θ : F ⟶ B.om) [Mono θ] (hF hθ) {V : B.X.Opens} {s : Γ(B.om, V)} :
    s ∈ (ofBundle θ hF hθ).N.sec V ↔ ∃ r, θ.app V r = s := by
  change s ∈ LinearMap.range (QCoh.appLinear θ V) ↔ _
  simp [LinearMap.mem_range]

variable (B) in

def top : Lat B :=
  ofBundle (𝟙 _) (have := B.t.semi; have := B.t.semi.smooth; exists_isFrame_omega B.t.G) fun _ _ s => ⟨s, rfl⟩

def IsTop (L : Lat B) : Prop := ∀ V, L.N.sec V = ⊤

theorem isTop_top : (top B).IsTop := fun _ =>
  eq_top_iff.2 fun s _ => (mem_ofBundle _ _ _).2 ⟨s, rfl⟩

theorem ext {L L' : Lat B} (h : ∀ V, L.N.sec V = L'.N.sec V) : L = L' := by
  obtain ⟨⟨N, r, m⟩, f, g⟩ := L
  obtain ⟨⟨N', r', m'⟩, f', g'⟩ := L'
  obtain rfl : N = N' := funext h
  rfl

theorem isTop_iff {L : Lat B} : L.IsTop ↔ L = top B := by
  refine ⟨fun hL => ext fun V => (hL V).trans (isTop_top V).symm, ?_⟩
  rintro rfl
  exact isTop_top

end Lat

variable (Y i₀) in

structure Step : Type where

  B : Mdl Y i₀

  L : Lat B

  σ : E →+* ℂ

  k : ℕ

  le : k ≤ Dw.mult σ

def InStep (Z B : Mdl Y i₀) (σ : E →+* ℂ) (r : ℕ) {k : Type} [Field k] (w : Sp k ⟶ Z.X)
    (v : Sp (DualNumber k) ⟶ B.t.G.left) : Prop :=
  ∃ (τ : (Y Z.i).X ⟶ (Y B.i).X) (mu : SABMap (Y Z.i).t (Y B.i).t τ) (u : Vecs Dw (Y Z.i).t k) (i : Fin (Dw.mult σ)),
    LocM.IsTrans B.i Z.i τ mu ∧ Z.FlagAt w u ∧ (i : ℕ) < r ∧ v ≫ B.tMap.φ = u σ i ≫ mu.φ

def Step.Holds (t : Step Y i₀) (Z : Mdl Y i₀) : Prop :=
  t.k ∈ Z.ty t.σ ∧ ∃ g : Z.X ⟶ t.B.X, IsMap Z t.B g ∧ ∀ x : Z.X,
    ∃ (U : Z.X.Opens) (hU : IsAffineOpen U) (V : t.B.X.Opens) (n : ℕ) (m : Fin n → Γ(t.L.N.toMod, V))
      (a : GL (Fin n) Γ(Z.X, U)), x ∈ U ∧ U ≤ g ⁻¹ᵁ V ∧ VB.IsFrame m ∧
      ∀ (k : Type) [Field k] (φ : Γ(Z.X, U) →+* k) (v : Sp (DualNumber k) ⟶ t.B.t.G.left)
        (hv : IsTanAtG t.B.t ((spMap φ ≫ hU.fromSpec) ≫ g) v) (h : ⊤ ≤ ((spMap φ ≫ hU.fromSpec) ≫ g) ⁻¹ᵁ V),
        InStep Z t.B t.σ t.k (spMap φ ≫ hU.fromSpec) v →
        ∀ j : Fin n, t.k ≤ (j : ℕ) → ∑ l, φ (a j l) * tanEv t.B.t hv h (t.L.N.incl.app V (m l)) = 0

open Classical in

def stepTy (s : Finset (Step Y i₀)) (σ : E →+* ℂ) : Finset ℕ := (s.filter fun t => t.σ = σ).image Step.k

theorem mem_stepTy {s : Finset (Step Y i₀)} {σ : E →+* ℂ} {r : ℕ} : r ∈ stepTy s σ ↔ ∃ t ∈ s, t.σ = σ ∧ t.k = r := by
  simp [stepTy, and_assoc]

def IsFlagCl (Z : Mdl Y i₀) (s : Finset (Step Y i₀)) (Z' : Mdl Y i₀) : Prop :=
  Z'.i = Z.i ∧ (∀ σ, Z'.ty σ = Z.ty σ ∪ stepTy s σ) ∧ (∃ f, IsMap Z' Z f) ∧ (∀ t ∈ s, t.Holds Z') ∧
    ∀ Z'' : Mdl Y i₀, (∃ g, IsMap Z'' Z g) → (∀ t ∈ s, t.Holds Z'') → ∃ h, IsMap Z'' Z' h

open Classical in

def flagClosure (Z : Mdl Y i₀) (s : Finset (Step Y i₀)) : Mdl Y i₀ := if h : ∃ Z', IsFlagCl Z s Z' then h.choose else Z

theorem isFlagCl_flagClosure {Z : Mdl Y i₀} {s : Finset (Step Y i₀)} (h : ∃ Z', IsFlagCl Z s Z') :
    IsFlagCl Z s (flagClosure Z s) := by
  rw [flagClosure, dif_pos h]
  exact h.choose_spec

theorem isFlagCl_empty {Z : Mdl Y i₀} (h : ∃ f, IsMap Z Z f) : IsFlagCl Z ∅ Z :=
  ⟨rfl, fun σ => by simp [stepTy], h, by simp, fun _ hg _ => hg⟩

theorem IsFlagCl.exists_isMap {Z Z₁ Z₂ : Mdl Y i₀} {s : Finset (Step Y i₀)} (h₁ : IsFlagCl Z s Z₁) (h₂ : IsFlagCl Z s Z₂) :
    ∃ f, IsMap Z₁ Z₂ f :=
  h₂.2.2.2.2 Z₁ h₁.2.2.1 h₁.2.2.2.1

open Classical in

def allSteps {B : Mdl Y i₀} (L : Lat B) : Finset (Step Y i₀) :=
  Finset.univ.image fun q : Σ σ : E →+* ℂ, Fin (Dw.mult σ + 1) => ⟨B, L, q.1, q.2, Nat.lt_succ_iff.1 q.2.2⟩

theorem mem_allSteps {B : Mdl Y i₀} {L : Lat B} {t : Step Y i₀} :
    t ∈ allSteps L ↔ ∃ σ r hr, t = ⟨B, L, σ, r, hr⟩ := by
  classical
  constructor
  · rintro h
    obtain ⟨⟨σ, r⟩, -, rfl⟩ := Finset.mem_image.1 h
    exact ⟨σ, r, _, rfl⟩
  · rintro ⟨σ, r, hr, rfl⟩
    exact Finset.mem_image.2 ⟨⟨σ, ⟨r, Nat.lt_succ_iff.2 hr⟩⟩, Finset.mem_univ _, rfl⟩

theorem stepTy_allSteps {B : Mdl Y i₀} (L : Lat B) (σ : E →+* ℂ) :
    stepTy (allSteps L) σ = Finset.range (Dw.mult σ + 1) := by
  ext r
  rw [mem_stepTy, Finset.mem_range]
  constructor
  · rintro ⟨t, ht, rfl, rfl⟩
    obtain ⟨σ', r', hr', rfl⟩ := mem_allSteps.1 ht
    exact Nat.lt_succ_iff.2 hr'
  · intro h
    exact ⟨⟨B, L, σ, r, Nat.lt_succ_iff.1 h⟩, mem_allSteps.2 ⟨σ, r, _, rfl⟩, rfl, rfl⟩

theorem allSteps_ne_empty {B : Mdl Y i₀} (L : Lat B) : allSteps L ≠ ∅ := by
  intro h
  obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hm : (⟨B, L, σ, 0, Nat.zero_le _⟩ : Step Y i₀) ∈ allSteps L := mem_allSteps.2 ⟨σ, 0, _, rfl⟩
  rw [h] at hm
  exact Finset.notMem_empty _ hm

def Step.admitted (P : ∀ B : Mdl Y i₀, Lat B → Prop) (Z : Mdl Y i₀) (t : Step Y i₀) : Prop :=
  (t.B = Z ∨ ∃ f, IsMap Z t.B f) ∧ (t.L.IsTop ∨ P t.B t.L)

def FlagFam (P : ∀ B : Mdl Y i₀, Lat B → Prop) (Z : Mdl Y i₀) : Type :=
  {s : Finset (Step Y i₀) // ∀ t ∈ s, t.admitted P Z}

namespace FlagFam

variable {P : ∀ B : Mdl Y i₀, Lat B → Prop}

def empty (Z : Mdl Y i₀) : FlagFam P Z := ⟨∅, by simp⟩

def full {Z : Mdl Y i₀} (L : Lat Z) (h : L.IsTop ∨ P Z L) : FlagFam P Z :=
  ⟨allSteps L, fun t ht => by
    obtain ⟨σ, r, hr, rfl⟩ := mem_allSteps.1 ht
    exact ⟨.inl rfl, h⟩⟩

def deRham (Z : Mdl Y i₀) : FlagFam P Z := full (Lat.top Z) (.inl Lat.isTop_top)

end FlagFam

end Free

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

open Classical in

def At.flagCl (ct : At S κ p) (Z : ct.Mdl) (s : Finset (Step ct.Y ⟨κ.l, κ.c, κ.good p ct.hp⟩)) : ct.Mdl :=
  if s = ∅ then Z else if s = allSteps (Lat.top Z) ∧ IsDRFlag Z ct.YY then ct.YY else flagClosure Z s

theorem At.flagCl_empty (ct : At S κ p) (Z : ct.Mdl) : ct.flagCl Z ∅ = Z := by
  simp [At.flagCl]

theorem At.flagCl_allSteps (ct : At S κ p) : ct.flagCl ct.Xm (allSteps (Lat.top ct.Xm)) = ct.YY := by
  rw [At.flagCl, if_neg (allSteps_ne_empty _), if_pos ⟨rfl, ct.isYY⟩]

theorem At.isFlagCl_flagCl (ct : At S κ p) (Z : ct.Mdl) (s : Finset (Step ct.Y ⟨κ.l, κ.c, κ.good p ct.hp⟩))
    (hid : ∃ f, IsMap Z Z f) (hdr : IsDRFlag Z ct.YY → IsFlagCl Z (allSteps (Lat.top Z)) ct.YY)
    (hex : ∃ Z', IsFlagCl Z s Z') : IsFlagCl Z s (ct.flagCl Z s) := by
  rw [At.flagCl]
  split_ifs with h₀ h₁
  · subst h₀
    exact isFlagCl_empty hid
  · obtain ⟨rfl, h₂⟩ := h₁
    exact hdr h₂
  · exact isFlagCl_flagClosure hex

def flgOf (ct : At S κ p) (P : ∀ B : ct.Mdl, Lat B → Prop) : FlgSt ct where
  FlagData := FlagFam P
  flagCl Z s := ct.flagCl Z s.1
  allFlags := FlagFam.deRham ct.Xm
  YY_eq := ct.flagCl_allSteps.symm

example (ct : At S κ p) (P : ∀ B : ct.Mdl, Lat B → Prop) (Z : ct.Mdl) :
    (flgOf ct P).flagCl Z (FlagFam.empty Z) = Z := ct.flagCl_empty Z

example (ct : At S κ p) (P : ∀ B : ct.Mdl, Lat B → Prop) (σ : D.host.E →+* ℂ) :
    stepTy (flgOf ct P).allFlags.1 σ = ct.YY.ty σ := (stepTy_allSteps _ σ).trans (ct.isYY.2.1.1 σ).symm

end GlobalTheory.LocM
