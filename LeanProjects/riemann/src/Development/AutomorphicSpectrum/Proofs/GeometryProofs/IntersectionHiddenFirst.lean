import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSubMemEigW
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.BiextChangeSecondFactor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.DegZ

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegZ.IsoMap

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA

variable {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {d : ℕ}

def Zp {n : ℕ} (a : Pt R n d) : Prop := ∀ i, constantCoeff (a i) = 0

theorem zp_pt {n : ℕ} (j : Fin n) : Zp (pt R d j) := fun i => by
  show constantCoeff (X (j, i) : PS R n d) = 0
  simp

theorem zp_zero {n : ℕ} : Zp (0 : Pt R n d) := fun i => by simp

theorem zp_comp1 {n : ℕ} {φ : Pt R 1 d} {a : Pt R n d} (hφ : Zp φ) (ha : Zp a) : Zp (comp1 φ a) :=
  fun i => constantCoeff_ev (CZ.cons ha CZ.nil) (hφ i)

theorem zp_mP {n : ℕ} {a : Pt R n d} (ha : Zp a) : Zp (mP f a) := fun i => by
  have h : coeff (0 : Fin n × Fin d →₀ ℕ) (MvPowerSeries.map f (a i)) = f (coeff 0 (a i)) := coeff_map _ _ _
  rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, ha i, map_zero] at h
  exact h

theorem map_ev1 {n : ℕ} {a : Pt R n d} (ha : Zp a) (g : PS R 1 d) :
    MvPowerSeries.map f (ev ![a] g) = ev ![mP f a] (MvPowerSeries.map f g) := by
  rw [map_ev' f (CZ.cons ha CZ.nil), mV_cons, mV_nil]

theorem map_ev2 {n : ℕ} {a b : Pt R n d} (ha : Zp a) (hb : Zp b) (g : PS R 2 d) :
    MvPowerSeries.map f (ev ![a, b] g) = ev ![mP f a, mP f b] (MvPowerSeries.map f g) := by
  rw [map_ev' f (CZ.cons ha (CZ.cons hb CZ.nil)), mV_cons, mV_cons, mV_nil]

theorem map_ev3 {n : ℕ} {a b c : Pt R n d} (ha : Zp a) (hb : Zp b) (hc : Zp c) (g : PS R 3 d) :
    MvPowerSeries.map f (ev ![a, b, c] g) = ev ![mP f a, mP f b, mP f c] (MvPowerSeries.map f g) := by
  rw [map_ev' f (CZ.cons ha (CZ.cons hb (CZ.cons hc CZ.nil))), mV_cons, mV_cons, mV_cons, mV_nil]

theorem mapPoint_comp1' {n : ℕ} (φ : Pt R 1 d) {a : Pt R n d} (ha : Zp a) :
    mP f (comp1 φ a) = comp1 (mP f φ) (mP f a) := by
  funext i
  exact map_ev1 f ha (φ i)

variable {O : Type} [CommRing O] [StarRing O]

theorem zp_add (B : Germ.FB R d O) {n : ℕ} {a b : Pt R n d} (ha : Zp a) (hb : Zp b) : Zp (B.G.add a b) :=
  fun i => constantCoeff_ev (CZ.cons ha (CZ.cons hb CZ.nil)) (B.G.const i)

theorem zp_act (B : Germ.FB R d O) (a : O) : Zp (B.A.act a) := B.A.const a

variable {f} {B : Germ.FB R d O} {C : Germ.FB S d O}

theorem mapPoint_add (h : IsMapOf f B C) {n : ℕ} {a b : Pt R n d} (ha : Zp a) (hb : Zp b) :
    mP f (B.G.add a b) = C.G.add (mP f a) (mP f b) := by
  funext i
  show MvPowerSeries.map f (ev ![a, b] (B.G.F i)) = ev ![mP f a, mP f b] (C.G.F i)
  rw [h.F, map_ev2 f ha hb]

theorem mapPoint_act (h : IsMapOf f B C) (a : O) : mP f (B.A.act a) = C.A.act a := by
  funext i
  exact (h.act a i).symm

theorem isIso_mP {B₂ : Germ.FB R d O} {C₂ : Germ.FB S d O} {φ ψ : Germ.Pt R 1 d} {lam : Germ.PS R 2 d}
    (h₁ : IsMapOf f B C) (h₂ : IsMapOf f B₂ C₂) (I : IsIso B B₂ φ ψ lam) :
    IsIso C C₂ (mP f φ) (mP f ψ) (MvPowerSeries.map f lam) := by
  have hφ : Zp φ := I.c₁
  have hψ : Zp ψ := I.c₂
  refine ⟨zp_mP f hφ, zp_mP f hψ, ?_, ?_, ⟨?_, ?_⟩, ?_, fun a => ?_, ?_, ?_, ?_, fun a => ?_⟩
  · have h := congrArg (mP f) I.inv₁
    rwa [mapPoint_comp1' f _ hψ, mapPoint_pt] at h
  · have h := congrArg (mP f) I.inv₂
    rwa [mapPoint_comp1' f _ hφ, mapPoint_pt] at h
  · have h := congrArg (MvPowerSeries.map f) I.ax.1
    simpa only [map_ev2 f zp_zero (zp_pt 0), mapPoint_zero f, mapPoint_pt, map_one] using h
  · have h := congrArg (MvPowerSeries.map f) I.ax.2
    simpa only [map_ev2 f (zp_pt 0) zp_zero, mapPoint_zero f, mapPoint_pt, map_one] using h
  · have h := congrArg (mP f) I.law
    simp only [mapPoint_comp1' f _ (zp_add _ (zp_pt _) (zp_pt _)), mapPoint_comp1' f _ (zp_pt _),
      mapPoint_add h₁ (zp_comp1 hφ (zp_pt _)) (zp_comp1 hφ (zp_pt _)), mapPoint_add h₂ (zp_pt _) (zp_pt _), mapPoint_pt] at h
    simpa only [mapPoint_comp1' f _ (zp_pt _), mapPoint_pt] using h
  · have h := congrArg (mP f) (I.act a)
    rwa [mapPoint_comp1' f _ (zp_act _ _), mapPoint_comp1' f _ hφ, mapPoint_act h₁, mapPoint_act h₂] at h
  · have h := congrArg (MvPowerSeries.map f) I.ph1
    simp (maxDischargeDepth := 6) only [map_mul, map_ev2 f, map_ev3 f, mapPoint_comp1' f, mapPoint_add h₂, mapPoint_pt,
      ← h₁.ph1, ← h₂.ph1, hφ, zp_pt, zp_comp1, zp_add] at h
    exact h
  · have h := congrArg (MvPowerSeries.map f) I.ph2
    simp (maxDischargeDepth := 6) only [map_mul, map_ev2 f, map_ev3 f, mapPoint_comp1' f, mapPoint_add h₂, mapPoint_pt,
      ← h₁.ph2, ← h₂.ph2, hφ, zp_pt, zp_comp1, zp_add] at h
    exact h
  · have h := congrArg (MvPowerSeries.map f) I.sy
    simp (maxDischargeDepth := 6) only [map_mul, map_ev2 f, mapPoint_comp1' f, mapPoint_pt,
      ← h₁.sy, ← h₂.sy, hφ, zp_pt, zp_comp1] at h
    exact h
  · have h := congrArg (MvPowerSeries.map f) (I.ad a)
    simp (maxDischargeDepth := 6) only [map_mul, map_ev2 f, mapPoint_comp1' f, mapPoint_act h₂, mapPoint_pt,
      ← h₁.ad, ← h₂.ad, hφ, zp_pt, zp_comp1, zp_act] at h
    exact h

end GlobalTheory.CompanionTheory.Ar.Flat.DegZ.IsoMap

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegZ

theorem isIso_map : ∀ (R S : Type) [CommRing R] [CommRing S] (f : R →+* S) (d : ℕ) (O : Type) [CommRing O] [StarRing O]
    (B B₂ : Germ.FB R d O) (C C₂ : Germ.FB S d O) (φ ψ : Germ.Pt R 1 d) (lam : Germ.PS R 2 d),
    IsMapOf f B C → IsMapOf f B₂ C₂ → IsIso B B₂ φ ψ lam →
      IsIso C C₂ (fun i => MvPowerSeries.map f (φ i)) (fun i => MvPowerSeries.map f (ψ i)) (MvPowerSeries.map f lam) := by
  intro R S _ _ f d O _ _ B B₂ C C₂ φ ψ lam h₁ h₂ I
  exact IsoMap.isIso_mP h₁ h₂ I

end GlobalTheory.CompanionTheory.Ar.Flat.DegZ
