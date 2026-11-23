import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsAtOfNorms
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowOfFramesTriv
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameGlue.PullEv

open GlobalTheory.Cartier

variable {X Z : Scheme.{0}} [IsIntegral X] [IsIntegral Z] (f : Z ⟶ X)

def evR : X.presheaf.stalk (f (genericPoint Z)) →+* Z.functionField :=
  (f.stalkMap (genericPoint Z)).hom

open Classical in

def ev (g : X.functionField) : Z.functionField :=
  if h : RegAt (f (genericPoint Z)) g then evR f h.choose else 0

theorem ev_algebraMap (a : X.presheaf.stalk (f (genericPoint Z))) :
    ev f (algebraMap _ X.functionField a) = evR f a := by
  have h : RegAt (f (genericPoint Z)) (algebraMap _ X.functionField a) := ⟨a, rfl⟩
  rw [ev, dif_pos h]
  congr 1
  exact IsFractionRing.injective _ X.functionField h.choose_spec

theorem ev_fnOf {V : X.Opens} (hV : genericPoint X ∈ V) (a : Γ(X, V)) (hZ : genericPoint Z ∈ f ⁻¹ᵁ V) :
    ev f (fnOf V hV a) = fnOf (f ⁻¹ᵁ V) hZ (f.app V a) := by
  rw [← algebraMap_germ (x := f (genericPoint Z)) hZ a, ev_algebraMap]
  exact Scheme.Hom.germ_stalkMap_apply f V (genericPoint Z) hZ a

theorem ev_spec (z : Z) (a : X.presheaf.stalk (f z)) :
    ev f (algebraMap _ X.functionField a) = algebraMap _ Z.functionField ((f.stalkMap z).hom a) := by
  obtain ⟨V, hx, b, rfl⟩ := X.presheaf.exists_germ_eq a
  have hz : z ∈ f ⁻¹ᵁ V := hx
  rw [algebraMap_germ hx b, ev_fnOf f _ b (gen_mem hz)]
  exact ((congrArg (algebraMap _ _) (Scheme.Hom.germ_stalkMap_apply f V z hx b)).trans
    (algebraMap_germ (x := z) hz _)).symm

end GlobalTheory.FrameGlue.PullEv

namespace GlobalTheory.FrameGlue.PullEv

open GlobalTheory.Cartier

variable {X Z : Scheme.{0}} [IsIntegral X] [IsIntegral Z] {f : Z ⟶ X}

theorem unitAt_gen {z : Z} {g : X.functionField} (h : UnitAt (f z) g) : UnitAt (f (genericPoint Z)) g := by
  obtain ⟨V, hV, hall⟩ := h.exists_nhds
  have hx : f (genericPoint Z) ∈ V := gen_mem (show z ∈ f ⁻¹ᵁ V from hV)
  exact hall _ hx

variable (f)

theorem regAt_ev {z : Z} {g : X.functionField} (h : RegAt (f z) g) : RegAt z (ev f g) := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨_, (ev_spec f z a).symm⟩

theorem unitAt_ev {z : Z} {g : X.functionField} (h : UnitAt (f z) g) : UnitAt z (ev f g) := by
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨_, ha.map _, (ev_spec f z a).symm⟩

theorem zeroAt_ev {z : Z} {g : X.functionField} (h : ZeroAt (f z) g) : ZeroAt z (ev f g) := by
  obtain ⟨a, ha, rfl⟩ := h
  refine ⟨_, ?_, (ev_spec f z a).symm⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha ⊢
  exact fun hu => ha (isUnit_of_map_unit _ _ hu)

theorem ev_eq_zero {g : X.functionField} (h : ZeroAt (f (genericPoint Z)) g) : ev f g = 0 := by
  by_contra hne
  exact (zeroAt_iff.1 (zeroAt_ev f (z := genericPoint Z) h)).2 (unitAt_genericPoint hne)

theorem ev_one : ev f (1 : X.functionField) = 1 := by
  rw [← map_one (algebraMap (X.presheaf.stalk (f (genericPoint Z))) X.functionField), ev_algebraMap, map_one]

theorem ev_mul {g h : X.functionField} (hg : RegAt (f (genericPoint Z)) g) (hh : RegAt (f (genericPoint Z)) h) :
    ev f (g * h) = ev f g * ev f h := by
  obtain ⟨a, rfl⟩ := hg
  obtain ⟨b, rfl⟩ := hh
  rw [← map_mul, ev_algebraMap, ev_algebraMap, ev_algebraMap, map_mul]

theorem ev_sub {g h : X.functionField} (hg : RegAt (f (genericPoint Z)) g) (hh : RegAt (f (genericPoint Z)) h) :
    ev f (g - h) = ev f g - ev f h := by
  obtain ⟨a, rfl⟩ := hg
  obtain ⟨b, rfl⟩ := hh
  rw [← map_sub, ev_algebraMap, ev_algebraMap, ev_algebraMap, map_sub]

open Classical in

def evu (u : X.functionFieldˣ) : Z.functionFieldˣ :=
  if h : UnitAt (f (genericPoint Z)) (u : X.functionField) then
    Units.mk0 (ev f u) (unitAt_ev f (z := genericPoint Z) h).ne_zero else 1

theorem val_evu {u : X.functionFieldˣ} (h : UnitAt (f (genericPoint Z)) (u : X.functionField)) :
    (evu f u : Z.functionField) = ev f u := by
  rw [evu, dif_pos h]; rfl

theorem unitAt_evu {z : Z} {u : X.functionFieldˣ} (h : UnitAt (f z) (u : X.functionField)) :
    UnitAt z (evu f u : Z.functionField) := by
  rw [val_evu f (unitAt_gen h)]; exact unitAt_ev f h

theorem unitAt_units_mul {x : X} {u v : X.functionFieldˣ} (hu : UnitAt x (u : X.functionField))
    (hv : UnitAt x (v : X.functionField)) : UnitAt x ((u * v : X.functionFieldˣ) : X.functionField) := by
  rw [Units.val_mul]; exact hu.mul hv

theorem unitAt_units_inv {x : X} {u : X.functionFieldˣ} (hu : UnitAt x (u : X.functionField)) :
    UnitAt x ((u⁻¹ : X.functionFieldˣ) : X.functionField) := by
  rw [Units.val_inv_eq_inv_val]; exact hu.inv

theorem evu_one : evu f 1 = 1 :=
  Units.ext (by rw [val_evu f (by rw [Units.val_one]; exact unitAt_one _), Units.val_one, Units.val_one, ev_one])

theorem evu_mul {u v : X.functionFieldˣ} (hu : UnitAt (f (genericPoint Z)) (u : X.functionField))
    (hv : UnitAt (f (genericPoint Z)) (v : X.functionField)) : evu f (u * v) = evu f u * evu f v :=
  Units.ext (by rw [val_evu f (unitAt_units_mul hu hv), Units.val_mul, Units.val_mul, val_evu f hu, val_evu f hv,
    ev_mul f hu.regAt hv.regAt])

theorem evu_inv {u : X.functionFieldˣ} (hu : UnitAt (f (genericPoint Z)) (u : X.functionField)) :
    evu f u⁻¹ = (evu f u)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← evu_mul f (unitAt_units_inv hu) hu, inv_mul_cancel, evu_one])

theorem evu_div {u v : X.functionFieldˣ} (hu : UnitAt (f (genericPoint Z)) (u : X.functionField))
    (hv : UnitAt (f (genericPoint Z)) (v : X.functionField)) : evu f (u / v) = evu f u / evu f v := by
  rw [div_eq_mul_inv, evu_mul f hu (unitAt_units_inv hv), evu_inv f hv, div_eq_mul_inv]

theorem unitAt_units_pow {x : X} {u : X.functionFieldˣ} (hu : UnitAt x (u : X.functionField)) (n : ℕ) :
    UnitAt x ((u ^ n : X.functionFieldˣ) : X.functionField) := by
  induction n with
  | zero => rw [pow_zero, Units.val_one]; exact unitAt_one x
  | succ n ih => rw [pow_succ]; exact unitAt_units_mul ih hu

theorem evu_pow {u : X.functionFieldˣ} (hu : UnitAt (f (genericPoint Z)) (u : X.functionField)) (n : ℕ) :
    evu f (u ^ n) = evu f u ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, evu_one]
  | succ n ih => rw [pow_succ, pow_succ, evu_mul f (unitAt_units_pow hu n) hu, ih]

theorem exists_lift {n : Type} {A : Matrix n n X.functionField} (h : ∀ i j, RegAt (f (genericPoint Z)) (A i j)) :
    ∃ A' : Matrix n n (X.presheaf.stalk (f (genericPoint Z))),
      A'.map (algebraMap _ X.functionField) = A ∧ A.map (ev f) = A'.map (evR f) := by
  choose A' hA' using h
  refine ⟨Matrix.of A', Matrix.ext fun i j => hA' i j, Matrix.ext fun i j => ?_⟩
  simp only [Matrix.map_apply, Matrix.of_apply, ← hA' i j, ev_algebraMap]

theorem not_isUnit_of_eq_zero (p : ℕ) (hp : (p : Γ(Z, ⊤)) = 0) (z : Z) :
    ¬ IsUnit (p : X.presheaf.stalk (f z)) := by
  intro hu
  have h := hu.map (f.stalkMap z).hom
  rw [map_natCast] at h
  have e : (p : Z.presheaf.stalk z) = (Z.presheaf.germ ⊤ z trivial).hom (p : Γ(Z, ⊤)) := (map_natCast _ p).symm
  rw [e, hp, map_zero] at h
  exact not_isUnit_zero h

section Div

variable {ι : Type} (U : ι → X.Opens) (b₀ : Z → ι) (hb₀ : ∀ z, f z ∈ U (b₀ z)) (r : ι → Z.functionFieldˣ)
  (hr : ∀ z b b', f z ∈ U b → f z ∈ U b' → UnitAt z ((r b : Z.functionField) / r b'))

def divOfCharts : CartierDiv Z :=
  show cartierGroup Z from ⟨fun z => germOf z (r (b₀ z)), fun z =>
    ⟨f ⁻¹ᵁ U (b₀ z), hb₀ z, r (b₀ z), fun y hy => germOf_eq_iff.2 (hr y _ _ hy (hb₀ y))⟩⟩

theorem isEqn_divOfCharts {z : Z} {b : ι} (hb : f z ∈ U b) : (divOfCharts f U b₀ hb₀ r hr).IsEqn z (r b) :=
  germOf_eq_iff.2 (hr z b (b₀ z) hb (hb₀ z))

end Div

end GlobalTheory.FrameGlue.PullEv

namespace GlobalTheory.FrameGlue

open GlobalTheory.Cartier GlobalTheory.FrameGlue.PullEv

theorem flagOfTriv_of_modPFrames : ∀ (X : Scheme.{0}) [IsIntegral X] (p : ℕ) (ι : Type) (N : ℕ) (U : ι → X.Opens)
    (M : ι → Matrix (Fin N) (Fin N) X.functionField) (c : ι → Fin N → X.functionFieldˣ), GlobalTheory.FrameGlue.ModPFrames p U M c →
    ∀ (L : Fin N → LB X) (hL : ∀ i, (L i).IsLB) (m : ℕ), (∀ i, GlobalTheory.FrameGlue.PowOfFrames p U (fun a => c a i) m (L i)) →
    ∀ (Z : Scheme.{0}) [IsIntegral Z] (ι' : Z ⟶ X), (p : Γ(Z, ⊤)) = 0 →
      ∃ g : Fin N → Pic Z, FlagOfTriv g ∧ ∀ i, CechPic.pull ι' (cls (L i) (hL i)) = m • g i := by
  intro X _ p ι N U M c hF L hL m hPow Z _ ι' hp
  obtain ⟨h1, h2, h3⟩ := hF
  have hov := not_isUnit_of_eq_zero (X := X) ι' p hp
  obtain ⟨a₀, ha₀⟩ := h1 _ (hov (genericPoint Z))
  choose b₀ hb₀ using fun z : Z => h1 _ (hov z)
  have gen : ∀ {z : Z} {V : X.Opens}, ι' z ∈ V → ι' (genericPoint Z) ∈ V := fun {z V} h =>
    gen_mem (show z ∈ ι' ⁻¹ᵁ V from h)

  let r : Fin N → ι → Z.functionFieldˣ := fun i b => evu ι' (c b i / c a₀ i)
  have hr : ∀ i z b b', ι' z ∈ U b → ι' z ∈ U b' → UnitAt z ((r i b : Z.functionField) / r i b') := by
    intro i z b b' hb hb'
    have u1 := (h3 b a₀ _ (gen hb) ha₀ (hov _) i).1
    have u2 := (h3 b' a₀ _ (gen hb') ha₀ (hov _) i).1
    have u3 := (h3 b b' _ hb hb' (hov z) i).1
    have e : c b i / c a₀ i / (c b' i / c a₀ i) = c b i / c b' i := div_div_div_cancel_right _ _ _
    rw [← Units.val_div_eq_div_val, ← evu_div ι' u1 u2, e]
    exact unitAt_evu ι' u3
  let D : Fin N → CartierDiv Z := fun i => divOfCharts ι' U b₀ hb₀ (r i) (hr i)
  have hD : ∀ i z b, ι' z ∈ U b → (D i).IsEqn z (r i b) := fun i z b hb =>
    isEqn_divOfCharts ι' U b₀ hb₀ (r i) (hr i) hb
  refine ⟨fun i => toPic (D i), ?_, fun i => ?_⟩
  · refine ⟨fun i => toLB (D i), fun i => isLB_toLB _, fun i j => j.1.2, (M a₀).map (ev ι'), fun i => rfl,
      fun i => (presents_toLB _).isRatSec, fun z => ?_⟩
    have hb := hb₀ z
    have hxb := gen hb
    obtain ⟨Ma, hMa, hMaev⟩ := exists_lift ι' (h2 a₀ _ ha₀ (hov _)).1
    obtain ⟨Mb, hMb, hMbev⟩ := exists_lift ι' (h2 (b₀ z) _ hxb (hov _)).1
    have hdet : IsUnit Ma.det := by
      obtain ⟨d, hd, e⟩ := (h2 a₀ _ ha₀ (hov _)).2
      rw [← hMa, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at e
      rwa [IsFractionRing.injective _ X.functionField e] at hd
    have hinv : (M a₀)⁻¹ = Ma⁻¹.map (algebraMap _ X.functionField) := by
      rw [← hMa]
      refine Matrix.inv_eq_left_inv ?_
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
    have hP : (M a₀)⁻¹ * M (b₀ z) = (Ma⁻¹ * Mb).map (algebraMap _ X.functionField) := by
      rw [hinv, ← hMb, ← Matrix.map_mul]
    have hQ : ∀ i k, ev ι' (((M a₀)⁻¹ * M (b₀ z)) i k) = evR ι' ((Ma⁻¹ * Mb) i k) := by
      intro i k; rw [hP, Matrix.map_apply, ev_algebraMap]
    have hAB : (M a₀).map (ev ι') * (Ma⁻¹ * Mb).map (evR ι') = Mb.map (evR ι') := by
      rw [hMaev, ← Matrix.map_mul, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]
    refine ⟨(Ma⁻¹ * Mb).map (evR ι'), fun i k hki => ?_, fun i k => ?_, ?_, fun i j hz => ?_⟩
    · rw [Matrix.map_apply, ← hQ]
      exact ev_eq_zero ι' ((h3 a₀ (b₀ z) _ ha₀ hxb (hov _) i).2.1 k hki)
    · rw [hAB, ← hMbev, Matrix.map_apply]
      exact regAt_ev ι' ((h2 (b₀ z) _ hb (hov z)).1 i k)
    · rw [hAB, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← ev_algebraMap, RingHom.map_det,
        RingHom.mapMatrix_apply, hMb]
      exact unitAt_ev ι' (h2 (b₀ z) _ hb (hov z)).2
    · have u := (h3 a₀ (b₀ z) _ ha₀ hxb (hov _) i).1
      have u' := (h3 (b₀ z) a₀ _ hxb ha₀ (hov _) i).1
      have reg1 : RegAt (ι' (genericPoint Z)) (((M a₀)⁻¹ * M (b₀ z)) i i) := by
        rw [hP]; exact ⟨_, rfl⟩
      have hii : evR ι' ((Ma⁻¹ * Mb) i i) = ev ι' ((c a₀ i / c (b₀ z) i : X.functionFieldˣ) : X.functionField) := by
        rw [← hQ]
        have := ev_eq_zero ι' (h3 a₀ (b₀ z) _ ha₀ hxb (hov _) i).2.2
        rwa [ev_sub ι' reg1 u.regAt, sub_eq_zero] at this
      have e1 := (hD i z (b₀ z) hb).iff_unitAt.1 (j.2.2 z hz)
      show UnitAt z ((Ma⁻¹ * Mb).map (evR ι') i i * (j.1.2 : Z.functionField))
      rw [Matrix.map_apply, hii, ← val_evu ι' u, show c a₀ i / c (b₀ z) i = (c (b₀ z) i / c a₀ i)⁻¹ from
        (inv_div _ _).symm, evu_inv ι' u', Units.val_inv_eq_inv_val, inv_mul_eq_div]
      exact e1
  · obtain ⟨s, hs, hsu⟩ := hPow i
    let t : ((L i).pull ι').ι → Z.functionFieldˣ := fun J => evu ι' (s (J PUnit.unit) / c a₀ i ^ m)
    have pres : Presents (m • D i) ((L i).pull ι') t := by
      refine ⟨pull_isLB (hL i) ι', fun J J' h => ?_, fun J z hz => ?_⟩
      · have hk : ι' (genericPoint Z) ∈ (L i).U (J PUnit.unit) := mem_pull.1 h.1
        have hk' : ι' (genericPoint Z) ∈ (L i).U (J' PUnit.unit) := mem_pull.1 h.2
        have hgX : genericPoint X ∈ (L i).U (J PUnit.unit) ⊓ (L i).U (J' PUnit.unit) := gen_mem ⟨hk, hk'⟩
        have e := hs (J PUnit.unit) (J' PUnit.unit) hgX
        have uk := hsu a₀ (J PUnit.unit) _ ha₀ hk (hov _)
        have uk' := hsu a₀ (J' PUnit.unit) _ ha₀ hk' (hov _)
        have hZ : genericPoint Z ∈ ι' ⁻¹ᵁ ((L i).U (J PUnit.unit) ⊓ (L i).U (J' PUnit.unit)) := ⟨hk, hk'⟩
        have hg : fnOf _ h ((((L i).pull ι').g J J' : Γ(Z, _)ˣ) : Γ(Z, _)) =
            ev ι' (fnOf _ hgX (((L i).g (J PUnit.unit) (J' PUnit.unit) : Γ(X, _)ˣ) : Γ(X, _))) := by
          rw [ev_fnOf ι' hgX _ hZ]
          show fnOf _ h (Units.val (∏ _k : PUnit, (res _ (pullU ι' _ ((L i).g (J PUnit.unit) (J' PUnit.unit)))) ^ (1 : ℤ))) = _
          rw [Fintype.prod_unique, zpow_one]
          exact fnOf_resG (X := Z) _ h _
        rw [hg, val_evu ι' uk, val_evu ι' uk', ← ev_mul ι' (regAt_fnOf (U := (L i).U (J PUnit.unit) ⊓ (L i).U (J' PUnit.unit))
          (show ι' (genericPoint Z) ∈ _ from ⟨hk, hk'⟩) hgX _) uk'.regAt]
        congr 1
        rw [Units.val_div_eq_div_val, Units.val_div_eq_div_val, e, mul_div_assoc]
      · have hk : ι' z ∈ (L i).U (J PUnit.unit) := mem_pull.1 hz
        have hb := hb₀ z
        refine ((hD i z (b₀ z) hb).nsmul m).iff_unitAt.2 ?_
        have u1 := hsu a₀ (J PUnit.unit) _ ha₀ (gen hk) (hov _)
        have u2 := (h3 (b₀ z) a₀ _ (gen hb) ha₀ (hov _) i).1
        have e : s (J PUnit.unit) / c a₀ i ^ m / (c (b₀ z) i / c a₀ i) ^ m = s (J PUnit.unit) / c (b₀ z) i ^ m := by
          rw [div_pow, div_div_div_cancel_right]
        show UnitAt z ((evu ι' (s (J PUnit.unit) / c a₀ i ^ m) : Z.functionField) / (evu ι' (c (b₀ z) i / c a₀ i) ^ m : Z.functionFieldˣ))
        rw [← evu_pow ι' u2, ← Units.val_div_eq_div_val, ← evu_div ι' u1 (unitAt_units_pow u2 m), e]
        exact unitAt_evu ι' (hsu (b₀ z) (J PUnit.unit) _ hb hk (hov z))
    rw [← map_nsmul, pres.toPic_eq]
    exact (cls_pull (hL i) ι' _).symm

end GlobalTheory.FrameGlue
