import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

noncomputable section
namespace GlobalTheory.GermRing
open GlobalTheory.Conv

def Rep (w : ℂ) (f : ℂ⸨X⸩) (x : ℂ) : Prop :=
  ∃ (T : ℝ) (hw : T < w.im) (a s : halfRing T),
    ev T w hw s ≠ 0 ∧ (s : ℂ⸨X⸩) * f = a ∧ ev T w hw a = x * ev T w hw s

theorem Rep.common {w : ℂ} {f g : ℂ⸨X⸩} {x y : ℂ} (hf : Rep w f x) (hg : Rep w g y) :
    ∃ (T : ℝ) (hw : T < w.im) (a s b t : halfRing T),
      (ev T w hw s ≠ 0 ∧ (s : ℂ⸨X⸩) * f = a ∧ ev T w hw a = x * ev T w hw s) ∧
      (ev T w hw t ≠ 0 ∧ (t : ℂ⸨X⸩) * g = b ∧ ev T w hw b = y * ev T w hw t) := by
  obtain ⟨T, hw, a, s, h⟩ := hf
  obtain ⟨T', hw', b, t, h'⟩ := hg
  exact ⟨max T T', max_lt hw hw', ⟨a, halfRing_mono (le_max_left _ _) a.2⟩,
    ⟨s, halfRing_mono (le_max_left _ _) s.2⟩, ⟨b, halfRing_mono (le_max_right _ _) b.2⟩,
    ⟨t, halfRing_mono (le_max_right _ _) t.2⟩, h, h'⟩

theorem Rep.unique {w : ℂ} {f : ℂ⸨X⸩} {x y : ℂ} (hx : Rep w f x) (hy : Rep w f y) : x = y := by
  obtain ⟨T, hw, a, s, b, t, ⟨h1, h2, h3⟩, k1, k2, k3⟩ := hx.common hy
  have e : a * t = b * s := Subtype.ext (by
    push_cast
    rw [← h2, ← k2]; ring)
  have e' := congrArg (ev T w hw) e
  rw [map_mul, map_mul, h3, k3] at e'
  apply mul_right_cancel₀ (mul_ne_zero h1 k1)
  linear_combination e'

theorem Rep.add {w : ℂ} {f g : ℂ⸨X⸩} {x y : ℂ} (hx : Rep w f x) (hy : Rep w g y) :
    Rep w (f + g) (x + y) := by
  obtain ⟨T, hw, a, s, b, t, ⟨h1, h2, h3⟩, k1, k2, k3⟩ := hx.common hy
  refine ⟨T, hw, a * t + b * s, s * t, by rw [map_mul]; exact mul_ne_zero h1 k1, ?_, ?_⟩
  · push_cast
    rw [← h2, ← k2]; ring
  · rw [map_add, map_mul, map_mul, map_mul, h3, k3]; ring

theorem Rep.mul {w : ℂ} {f g : ℂ⸨X⸩} {x y : ℂ} (hx : Rep w f x) (hy : Rep w g y) :
    Rep w (f * g) (x * y) := by
  obtain ⟨T, hw, a, s, b, t, ⟨h1, h2, h3⟩, k1, k2, k3⟩ := hx.common hy
  refine ⟨T, hw, a * b, s * t, by rw [map_mul]; exact mul_ne_zero h1 k1, ?_, ?_⟩
  · push_cast
    rw [← h2, ← k2]; ring
  · rw [map_mul, map_mul, h3, k3]; ring

theorem rep_of_mem {T : ℝ} {w : ℂ} (hw : T < w.im) (s : halfRing T) :
    Rep w (s : ℂ⸨X⸩) (ev T w hw s) :=
  ⟨T, hw, s, 1, by rw [map_one]; exact one_ne_zero, by simp, by rw [map_one, _root_.mul_one]⟩

theorem rep_algebraMap (w c : ℂ) : Rep w (algebraMap ℂ ℂ⸨X⸩ c) c := by
  have hw : w.im - 1 < w.im := sub_one_lt _
  have h := rep_of_mem hw (algebraMap ℂ (halfRing (w.im - 1)) c)
  rw [AlgHom.commutes] at h
  exact h

theorem Rep.inv {w : ℂ} {f : ℂ⸨X⸩} {x : ℂ} (hx : Rep w f x) (h0 : x ≠ 0) :
    ∃ g, Rep w g x⁻¹ ∧ f * g = 1 := by
  obtain ⟨T, hw, a, s, h1, h2, h3⟩ := hx
  have ha : ev T w hw a ≠ 0 := by rw [h3]; exact mul_ne_zero h0 h1
  have ha' : (a : ℂ⸨X⸩) ≠ 0 := fun h => ha (by rw [show a = 0 from Subtype.ext h, map_zero])
  have hf : f ≠ 0 := fun h => ha' (by rw [← h2, h, mul_zero])
  refine ⟨f⁻¹, ⟨T, hw, s, a, ha, ?_, ?_⟩, mul_inv_cancel₀ hf⟩
  · rw [← h2, _root_.mul_assoc, mul_inv_cancel₀ hf, _root_.mul_one]
  · rw [h3, ← _root_.mul_assoc, inv_mul_cancel₀ h0, _root_.one_mul]

def ring (w : ℂ) : Subalgebra ℂ ℂ⸨X⸩ where
  carrier := {f | ∃ x, Rep w f x}
  mul_mem' := fun ⟨_, hx⟩ ⟨_, hy⟩ => ⟨_, hx.mul hy⟩
  add_mem' := fun ⟨_, hx⟩ ⟨_, hy⟩ => ⟨_, hx.add hy⟩
  algebraMap_mem' c := ⟨c, rep_algebraMap w c⟩

def val (w : ℂ) (f : ring w) : ℂ := Classical.choose (show ∃ x, Rep w f x from f.2)

theorem rep_val (w : ℂ) (f : ring w) : Rep w f (val w f) := Classical.choose_spec (show ∃ x, Rep w f x from f.2)

def evRing (w : ℂ) : ring w →ₐ[ℂ] ℂ where
  toFun := val w
  map_one' := (rep_val w 1).unique (by simpa using rep_algebraMap w 1)
  map_mul' f g := (rep_val w (f * g)).unique ((rep_val w f).mul (rep_val w g))
  map_zero' := (rep_val w 0).unique (by simpa using rep_algebraMap w 0)
  map_add' f g := (rep_val w (f + g)).unique ((rep_val w f).add (rep_val w g))
  commutes' c := (rep_val w _).unique (rep_algebraMap w c)

def germs : Germs where
  R := ring
  ev := evRing
  unit w s hs := by
    obtain ⟨g, hg, h⟩ := (rep_val w s).inv hs
    exact IsUnit.of_mul_eq_one (⟨g, _, hg⟩ : ring w) (Subtype.ext h)
  le T w hw f hf := ⟨_, rep_of_mem hw ⟨f, hf⟩⟩
  ev_eq T w hw s := (rep_val w _).unique (rep_of_mem hw s)
  frac w f := by
    obtain ⟨T, hw, a, s, h1, h2, -⟩ := rep_val w f
    exact ⟨T, hw, a, s, h1, h2⟩

theorem germs_spec : Nonempty Germs ∧ ∀ (Γ : Germs) (w : ℂ), IsLocalRing (Γ.R w) ∧ (∀ f : Γ.R w, (f : ℂ⸨X⸩) ∈ Conv.convLaurent) ∧ ∀ (f : Γ.R w) (g : ℂ⸨X⸩), Γ.ev w f ≠ 0 → (f : ℂ⸨X⸩) * g ∈ Γ.R w → g ∈ Γ.R w := by
  refine ⟨⟨germs⟩, fun Γ w => ⟨?_, fun f => ?_, fun f g hf h => ?_⟩⟩
  · refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun f => ?_
    by_cases h : Γ.ev w f = 0
    · exact Or.inr (Γ.unit w _ (by rw [map_sub, map_one, h, sub_zero]; exact one_ne_zero))
    · exact Or.inl (Γ.unit w _ h)
  · obtain ⟨T, hw, a, s, h1, h2⟩ := Γ.frac w f
    have hs : (s : ℂ⸨X⸩) ≠ 0 := fun h => h1 (by rw [show s = 0 from Subtype.ext h, map_zero])
    have e : (f : ℂ⸨X⸩) = (s : ℂ⸨X⸩)⁻¹ * a := by
      rw [← h2, ← _root_.mul_assoc, inv_mul_cancel₀ hs, _root_.one_mul]
    rw [e]
    exact mul_mem (convLaurent.inv_mem (halfRing_le_convLaurent T s.2)) (halfRing_le_convLaurent T a.2)
  · obtain ⟨k, hk⟩ := (Γ.unit w f hf).exists_left_inv
    have hk' : (k : ℂ⸨X⸩) * f = 1 := congrArg Subtype.val hk
    have e : g = k * (f * g) := by rw [← _root_.mul_assoc, hk', _root_.one_mul]
    rw [e]
    exact mul_mem k.2 h

end GlobalTheory.GermRing
