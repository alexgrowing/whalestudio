import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubWeilOfInjective
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBMapPf
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair.Reduce

open Formalism.MainNotions.ModuliIntegralCharts.H1.FBMap

section Ring

variable {R S : Type} [CommRing R] [CommRing S] {d : ℕ}

def addDefect (F : Fin d → PS R 2 d) (ga : Fin d → PowerSeries R) (i : Fin d) : MvPowerSeries (Fin 2) R :=
  MvPowerSeries.subst (fun q : Fin 2 × Fin d =>
    MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X q.1 : MvPowerSeries (Fin 2) R)) (ga q.2)) (F i) -
    MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R)) (ga i)

def cob (F : Fin d → PS R 2 d) (b : PS R 1 d) : PS R 2 d :=
  ev (n := 2) ![addOf F (pt R d 0) (pt R d 1)] b - ev (n := 2) ![pt R d 0] b - ev (n := 2) ![pt R d 1] b

theorem map_addDefect (ψ : R →+* S) (F : Fin d → PS R 2 d) (ga : Fin d → PowerSeries R)
    (h0 : ∀ i, PowerSeries.constantCoeff (ga i) = 0) (i : Fin d) :
    MvPowerSeries.map ψ (addDefect F ga i) =
      addDefect (fun i => MvPowerSeries.map ψ (F i)) (fun i => PowerSeries.map ψ (ga i)) i := by
  have hX : ∀ k : Fin 2, MvPowerSeries.HasSubst
      (fun _ : Unit => (MvPowerSeries.X k : MvPowerSeries (Fin 2) R)) := fun k =>
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
  have hA : MvPowerSeries.HasSubst
      (fun _ : Unit => (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
  have hq : MvPowerSeries.HasSubst (fun q : Fin 2 × Fin d =>
      MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X q.1 : MvPowerSeries (Fin 2) R)) (ga q.2)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q =>
      MvPowerSeries.constantCoeff_subst_eq_zero (hX q.1) (fun _ => by simp) (h0 q.2))
  unfold addDefect
  rw [map_sub, MvPowerSeries.map_subst hq, MvPowerSeries.map_subst hA]
  simp only [MvPowerSeries.map_subst (hX _), map_add, MvPowerSeries.map_X]
  rfl

theorem map_cob (ψ : R →+* S) (F : Fin d → PS R 2 d) (hF : ∀ i, MvPowerSeries.constantCoeff (F i) = 0)
    (b : PS R 1 d) :
    MvPowerSeries.map ψ (cob F b) = cob (fun i => MvPowerSeries.map ψ (F i)) (MvPowerSeries.map ψ b) := by
  unfold cob
  rw [map_sub, map_sub,
    map_ev' ψ _ (by intro j k; fin_cases j; exact cz_add F hF _ _ (cz_pt _) (cz_pt _) k),
    map_ev' ψ _ (by intro j k; fin_cases j; exact cz_pt _ k),
    map_ev' ψ _ (by intro j k; fin_cases j; exact cz_pt _ k),
    mp_cons, mp_cons, mp_cons, mp_nil, mp_add ψ _ _ _ (cz_pt _) (cz_pt _), mp_pt, mp_pt]

theorem map_cubicalTermLinearAlongTangent (ψ : R →+* S) (ph2 : PS R 3 d) (u : Fin d → R) :
    MvPowerSeries.map ψ (c2 ph2 u) = c2 (MvPowerSeries.map ψ ph2) (fun i => ψ (u i)) := by
  ext mu
  rw [MvPowerSeries.coeff_map]
  change ψ (∑ i : Fin d, _) = ∑ i : Fin d, _
  simp only [map_sum, map_mul, MvPowerSeries.coeff_map]

theorem map_map {T σ : Type} [CommRing T] (ψ : R →+* S) (χ : S →+* T) (f : MvPowerSeries σ R) :
    MvPowerSeries.map (χ.comp ψ) f = MvPowerSeries.map χ (MvPowerSeries.map ψ f) := by
  ext mu
  simp only [MvPowerSeries.coeff_map, RingHom.comp_apply]

end Ring

theorem exists_lift {C : Type} [Field C] (V : VF C) {σ : Type} (f : MvPowerSeries σ C)
    (hf : ∀ mu, V.Ge 0 (MvPowerSeries.coeff mu f)) :
    ∃ g : MvPowerSeries σ V.RR, MvPowerSeries.map V.RR.subtype g = f :=
  ⟨fun mu => ⟨MvPowerSeries.coeff mu f, hf mu⟩, by ext mu; rfl⟩

theorem degenerate_of_not_ndg : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (d : ℕ) (Y : FBChart C V O d) (R₀ : Type) [CommRing R₀] (j : R₀ →+* V.RR) (F : Fin d → PS R₀ 2 d) (ph2 : PS R₀ 3 d), (∀ i, MvPowerSeries.constantCoeff (F i) = 0) → (∀ i, Y.B.G.F i = MvPowerSeries.map (V.RR.subtype.comp j) (F i)) → Y.B.ph2 = MvPowerSeries.map (V.RR.subtype.comp j) ph2 → ∀ (Ω : Type) [Field Ω] (ρ : V.RR →+* Ω), (∀ x : V.RR, ρ x = 0 ↔ V.MM (x : C)) → ¬ NDG Y → Degenerate V.l (fun i => MvPowerSeries.map (ρ.comp j) (F i)) (MvPowerSeries.map (ρ.comp j) ph2) := by
  intro C _ _ V O _ _ d Y R₀ _ j F ph2 hF0 hF hph Ω _ ρ hρ hN
  unfold NDG at hN
  push Not at hN
  obtain ⟨ga, hcv, ⟨i₀, hi₀⟩, hadd, b, hb, hcob⟩ := hN
  have hlift : ∀ i, ∃ g : PowerSeries V.RR, PowerSeries.map V.RR.subtype g = ga i := fun i =>
    ⟨PowerSeries.mk fun n => ⟨PowerSeries.coeff n (ga i), (hcv i).2 n⟩, by ext n; simp⟩
  choose g hg using hlift
  obtain ⟨bR, rfl⟩ := exists_lift V b hb
  obtain rfl : ga = fun i => PowerSeries.map V.RR.subtype (g i) := funext fun i => (hg i).symm
  have hg0 : ∀ i, PowerSeries.constantCoeff (g i) = 0 := fun i => by
    have := (hcv i).1
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply] at this
    exact Subtype.ext this
  have hFR : Y.B.G.F = fun i => MvPowerSeries.map V.RR.subtype (MvPowerSeries.map j (F i)) :=
    funext fun i => by rw [hF i, map_map]
  have hFR0 : ∀ i, MvPowerSeries.constantCoeff (MvPowerSeries.map j (F i)) = 0 := fun i => by
    rw [MvPowerSeries.constantCoeff_map, hF0 i, map_zero]
  rw [map_map] at hph
  simp only [map_map]
  refine ⟨fun i => PowerSeries.map ρ (g i), fun i => ?_, ⟨i₀, ?_⟩, fun i mu h0 h1 => ?_,
    MvPowerSeries.map ρ bR, ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hg0 i, map_zero]
  · rw [PowerSeries.coeff_map] at hi₀ ⊢
    exact fun h => hi₀ ((hρ _).1 h)
  · have h : V.MM (MvPowerSeries.coeff mu (addDefect Y.B.G.F (fun i => PowerSeries.map V.RR.subtype (g i)) i)) :=
      hadd i mu h0 h1
    rw [hFR, ← map_addDefect V.RR.subtype _ g hg0 i, MvPowerSeries.coeff_map] at h
    change MvPowerSeries.coeff mu (addDefect (fun i => MvPowerSeries.map ρ (MvPowerSeries.map j (F i)))
      (fun i => PowerSeries.map ρ (g i)) i) = 0
    rw [← map_addDefect ρ _ g hg0 i, MvPowerSeries.coeff_map]
    exact (hρ _).2 h
  · change _ = cob (fun i => MvPowerSeries.map ρ (MvPowerSeries.map j (F i))) (MvPowerSeries.map ρ bR)
    simp only [PowerSeries.coeff_map]
    rw [← map_cob ρ _ hFR0, ← map_cubicalTermLinearAlongTangent, ← sub_eq_zero, ← map_sub]
    ext mu
    have h : V.MM (MvPowerSeries.coeff mu (c2 Y.B.ph2 (fun i => PowerSeries.coeff 1
        (PowerSeries.map V.RR.subtype (g i))) - cob Y.B.G.F (MvPowerSeries.map V.RR.subtype bR))) := hcob mu
    simp only [PowerSeries.coeff_map] at h
    rw [hFR, hph, ← map_cob V.RR.subtype _ hFR0, ← map_cubicalTermLinearAlongTangent, ← map_sub, MvPowerSeries.coeff_map] at h
    rw [MvPowerSeries.coeff_map, map_zero]
    exact (hρ _).2 h

end GlobalTheory.AlphaPair.Reduce
end
