import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace PositivityTheory.Xgf.OntoKer

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
  {P : D.La →+ (Fin g → ℂ)}

theorem ty_eq_of_rt {i j : Fin g} (h : ty i (H.rt : E) = ty j (H.rt : E)) (α : OK H) :
    ty i ((α : 𝓞 E) : E) = ty j ((α : 𝓞 E) : E) := by
  have hw : ty i ((H.w0 : 𝓞 E) : E) = ty j ((H.w0 : 𝓞 E) : E) := by
    have e : (2 : E) * ((H.w0 : 𝓞 E) : E) = 1 + ((H.rt : 𝓞 E) : E) := by
      have e0 := congrArg (fun z : 𝓞 E => (z : E)) H.two_weight_eq_one_add_root
      push_cast at e0
      exact e0
    have hi := congrArg (ty i) e
    have hj := congrArg (ty j) e
    simp only [map_mul, map_add, map_one, map_ofNat] at hi hj
    have h2 : (2 : ℂ) * ty i ((H.w0 : 𝓞 E) : E) = 2 * ty j ((H.w0 : 𝓞 E) : E) := by
      rw [hi, hj, h]
    exact mul_left_cancel₀ two_ne_zero h2
  suffices hs : ∀ β ∈ OK H, ty i ((β : 𝓞 E) : E) = ty j ((β : 𝓞 E) : E) from hs _ α.2
  intro β hβ
  induction hβ using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.1 hx]
    exact hw
  | algebraMap r => simp
  | add x y _ _ hx hy =>
    push_cast
    rw [map_add, map_add, hx, hy]
  | mul x y _ _ hx hy =>
    push_cast
    rw [map_mul, map_mul, hx, hy]

open Classical in

def kap (ty : Fin g → (E →+* ℂ)) (H : Host E) (b : Bool) (α : OK H) : ℂ :=
  if h : ∃ i, ty i (H.rt : E) = sgnRt H b then ty h.choose ((α : 𝓞 E) : E) else 0

theorem P_smul (hP : IsPeriod D ty P) {b : Bool} (a : PureType.lat hP (sgnRt H b)) (α : OK H) :
    P ((α : 𝓞 E) • (a : D.La)) = kap ty H b α • P a := by
  funext i
  rw [Pi.smul_apply, smul_eq_mul, hP.1]
  by_cases hi : ty i (H.rt : E) = sgnRt H b
  · have hex : ∃ i, ty i (H.rt : E) = sgnRt H b := ⟨i, hi⟩
    rw [kap, dif_pos hex, ty_eq_of_rt (hi.trans hex.choose_spec.symm) α]
  · have h0 : P (a : D.La) i = 0 := a.2 i hi
    rw [h0, mul_zero, mul_zero]

theorem span_top (hP : IsPeriod D ty P) (b : Fin g → Bool) (a : ∀ k, PureType.lat hP (sgnRt H (b k))) (N : ℕ)
    (hN0 : 0 < N) (hN : ∀ y : D.La, N • y ∈ Submodule.span (OK H) (Set.range fun k => (a k : D.La))) :
    Submodule.span ℂ (Set.range fun k => P (a k)) = ⊤ := by
  set W := Submodule.span ℂ (Set.range fun k => P (a k)) with hW
  have hmem : ∀ y, P y ∈ W := by
    intro y
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (OK H)).1 (hN y)
    have h1 : P (N • y) ∈ W := by
      rw [← hc, map_sum]
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [Subalgebra.smul_def, P_smul hP (a k) (c k)]
      exact W.smul_mem _ (Submodule.subset_span ⟨k, rfl⟩)
    rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ] at h1
    have h2 := W.smul_mem ((N : ℂ)⁻¹) h1
    rwa [smul_smul, inv_mul_cancel₀ (by exact_mod_cast hN0.ne'), one_smul] at h2
  have hR : Submodule.span ℝ (Set.range P) ≤ W.restrictScalars ℝ :=
    Submodule.span_le.2 (by rintro _ ⟨y, rfl⟩; exact hmem y)
  rw [eq_top_iff]
  intro z _
  have hz : z ∈ Submodule.span ℝ (Set.range P) := by
    rw [hP.2.2.2.1]
    trivial
  exact hR hz

theorem exists_coeffs (hP : IsPeriod D ty P) (b : Fin g → Bool) (a : ∀ k, PureType.lat hP (sgnRt H (b k))) (N : ℕ)
    (hN0 : 0 < N) (hN : ∀ y : D.La, N • y ∈ Submodule.span (OK H) (Set.range fun k => (a k : D.La))) (z : Fin g → ℂ) :
    ∃ c : Fin g → ℂ, z = ∑ k, c k • P (a k) := by
  have hz : z ∈ Submodule.span ℂ (Set.range fun k => P (a k)) := by rw [span_top hP b a N hN0 hN]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hz
  exact ⟨c, hc.symm⟩

theorem linIndep (hP : IsPeriod D ty P) (b : Fin g → Bool) (a : ∀ k, PureType.lat hP (sgnRt H (b k))) (N : ℕ)
    (hN0 : 0 < N) (hN : ∀ y : D.La, N • y ∈ Submodule.span (OK H) (Set.range fun k => (a k : D.La))) :
    LinearIndependent ℂ fun k => P (a k) := by
  apply linearIndependent_of_top_le_span_of_card_eq_finrank
  · rw [span_top hP b a N hN0 hN]
  · simp

theorem coeff_of_period (hP : IsPeriod D ty P) (b : Fin g → Bool) (a : ∀ k, PureType.lat hP (sgnRt H (b k))) (N : ℕ)
    (hN0 : 0 < N) (hN : ∀ y : D.La, N • y ∈ Submodule.span (OK H) (Set.range fun k => (a k : D.La)))
    (s : Fin g → ℂ) (y : D.La) (hs : ∑ k, s k • P (a k) = P y) :
    ∃ α : Fin g → OK H, ∀ k, (N : ℂ) * s k = kap ty H (b k) (α k) := by
  have hli := linIndep hP b a N hN0 hN
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (OK H)).1 (hN y)
  refine ⟨c, fun k => ?_⟩
  have e1 : ∑ k, ((N : ℂ) * s k) • P (a k) = (N : ℂ) • P y := by
    simp only [mul_smul, ← Finset.smul_sum, hs]
  have e2 : ∑ k, kap ty H (b k) (c k) • P (a k) = (N : ℂ) • P y := by
    rw [Nat.cast_smul_eq_nsmul, ← map_nsmul, ← hc, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Subalgebra.smul_def, P_smul hP (a k) (c k)]
  have hsum : ∑ k, ((N : ℂ) * s k - kap ty H (b k) (c k)) • P (a k) = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, e1, e2, sub_self]
  exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hli _ hsum k)

end PositivityTheory.Xgf.OntoKer

end
