import Development.WeilBound.CoreStatements.VolumeEquality.DegPushDefs
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DetLatticeFrameGenStatement

noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

section Lin

variable {Ω₃ : Type} [Field Ω₃] (O : ValuationSubring Ω₃) {r : ℕ}

theorem mu_det_le (T T' : Matrix (Fin r) (Fin r) Ω₃)
    (h : ∀ k, (fun m => T m k) ∈ Submodule.span O (Set.range fun k m => T' m k)) :
    O.valuation T.det ≤ O.valuation T'.det := by
  choose N hN using fun k => (Submodule.mem_span_range_iff_exists_fun O).1 (h k)
  have e : T = T' * (Matrix.of fun a b => N b a).map O.subtype := by
    ext m k
    have := congrFun (hN k) m
    simp only [Finset.sum_apply, Pi.smul_apply] at this
    rw [← this, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  have e2 : ((Matrix.of fun a b => N b a).map O.subtype).det = ((Matrix.of fun a b => N b a).det : O) :=
    (RingHom.map_det O.subtype _).symm
  rw [e, Matrix.det_mul, map_mul, e2]
  exact mul_le_of_le_one_right' (O.valuation_le_one _)

theorem mu_det_eq (T T' : Matrix (Fin r) (Fin r) Ω₃)
    (h : Submodule.span O (Set.range fun k m => T m k) = Submodule.span O (Set.range fun k m => T' m k)) :
    O.valuation T.det = O.valuation T'.det :=
  le_antisymm (mu_det_le O T T' fun k => h ▸ Submodule.subset_span ⟨k, rfl⟩)
    (mu_det_le O T' T fun k => h ▸ Submodule.subset_span ⟨k, rfl⟩)

theorem mu_coord {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] (R : Subring Ω) (i : Ω →+* Ω₃) (hi : ∀ a ∈ R, i a ∈ O)
    (c : Fin r → V) (hc : LinearIndependent Ω c) (Z : Set V) (Λ : Submodule O (Fin r → Ω₃))
    (hZ : ∀ w ∈ Z, ∃ x : Fin r → Ω, w = ∑ m, x m • c m ∧ (fun m => i (x m)) ∈ Λ) (x : Fin r → Ω)
    (hx : ∑ m, x m • c m ∈ Submodule.span R Z) : (fun m => i (x m)) ∈ Λ := by
  have key : ∀ w ∈ Submodule.span R Z, ∃ x : Fin r → Ω, w = ∑ m, x m • c m ∧ (fun m => i (x m)) ∈ Λ := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw => exact hZ w hw
    | zero => exact ⟨0, by simp, by simp only [Pi.zero_apply, map_zero]; exact Λ.zero_mem⟩
    | add a b _ _ ha hb =>
      obtain ⟨x, rfl, hx⟩ := ha
      obtain ⟨y, rfl, hy⟩ := hb
      refine ⟨x + y, by simp [add_smul, Finset.sum_add_distrib], ?_⟩
      convert Λ.add_mem hx hy using 1
      ext m; simp
    | smul a w _ hw =>
      obtain ⟨x, rfl, hx⟩ := hw
      refine ⟨fun m => (a : Ω) * x m, ?_, ?_⟩
      · rw [Subring.smul_def]
        simp [Finset.smul_sum, mul_smul]
      · convert Λ.smul_mem ⟨i a, hi a a.2⟩ hx using 1
        ext m
        show i (a * x m) = i a * i (x m)
        exact map_mul _ _ _
  obtain ⟨x', e, hx'⟩ := key _ hx
  have : x = x' := funext (Fintype.linearIndependent_iffₛ.1 hc x x' e)
  exact this ▸ hx'

theorem mu_alg {G : Type} [CommGroupWithZero G] {m₁ m₂ e₁ e₂ t₁ t₂ r₁ r₂ : G} (h₁ : m₁ * e₁ * t₁ = 1) (h₂ : m₂ * e₂ * t₂ = 1)
    (h : r₁ * t₁ = r₂ * t₂) (hr : r₁ ≠ 0) : m₂ = e₁ * r₂ / (r₁ * e₂) * m₁ := by
  have he : e₂ ≠ 0 := by rintro rfl; simp at h₂
  rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero hr he)]
  calc m₂ * (r₁ * e₂) = m₂ * (r₁ * e₂) * (m₁ * e₁ * t₁) := by rw [h₁, mul_one]
    _ = m₂ * e₂ * (r₁ * t₁) * (m₁ * e₁) := by ac_rfl
    _ = m₂ * e₂ * t₂ * (e₁ * r₂ * m₁) := by rw [h]; ac_rfl
    _ = _ := by rw [h₂, one_mul]

end Lin

section Lats

variable {X : Scheme.{0}} {Ω Ω₃ : Type} [Field Ω] [Field Ω₃] {ξ : Sp Ω ⟶ X} {q : Cpt ξ}

theorem mu_gen_ratio {Λ : Lat ξ Ω} {t t' : Ω} (h : Λ.IsGenAt q t) (h' : Λ.IsGenAt q t') : t' / t ∈ regAt ξ q := by
  have : t' ∈ Submodule.span (regAt ξ q) {t} := h.2 ▸ h'.2 ▸ Submodule.mem_span_singleton_self _
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 this
  have e : (a : Ω) * t = t' := ha
  rw [← e, mul_div_cancel_right₀ _ h.1]
  exact a.2

theorem mu_gen_val {O : ValuationSubring Ω₃} {i : Ω →+* Ω₃} (hD : Dom O i ξ q) {Λ : Lat ξ Ω} {t t' : Ω} (h : Λ.IsGenAt q t)
    (h' : Λ.IsGenAt q t') : O.valuation (i t) = O.valuation (i t') := by
  have k : ∀ {t t' : Ω}, Λ.IsGenAt q t → Λ.IsGenAt q t' → O.valuation (i t') ≤ O.valuation (i t) := fun {t t'} h h' => by
    have h1 := (O.valuation_le_one_iff _).2 (hD.1 _ (mu_gen_ratio h h'))
    have e : t' = t * (t' / t) := (mul_div_cancel₀ _ h.1).symm
    rw [e, map_mul, map_mul]
    exact mul_le_of_le_one_right' h1
  exact le_antisymm (k h' h) (k h h')

theorem mu_tens_gen {I : Type} [Fintype I] {Λ : I → Lat ξ Ω} (a : I → ℤ) {t : I → Ω} (h : ∀ j, (Λ j).IsGenAt q (t j)) :
    (Lat.tens Λ a).IsGenAt q (∏ j, t j ^ a j) := by
  refine ⟨Finset.prod_ne_zero_iff.2 fun j _ => zpow_ne_zero _ (h j).1, le_antisymm (Submodule.span_le.2 ?_)
    (Submodule.span_le.2 ?_)⟩
  · rintro _ ⟨s, hs, rfl⟩
    have hm : ∏ j, (s j / t j) ^ a j ∈ regAt ξ q := prod_mem fun j _ => by
      obtain ⟨n, e | e⟩ := (a j).eq_nat_or_neg
      · rw [e, zpow_natCast]; exact pow_mem (mu_gen_ratio (h j) (hs j)) _
      · rw [e, zpow_neg, zpow_natCast, ← inv_pow, inv_div]; exact pow_mem (mu_gen_ratio (hs j) (h j)) _
    refine Submodule.mem_span_singleton.2 ⟨⟨_, hm⟩, ?_⟩
    show (∏ j, (s j / t j) ^ a j) * ∏ j, t j ^ a j = _
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => by rw [← mul_zpow, div_mul_cancel₀ _ (h j).1]
  · rintro _ rfl
    exact Submodule.subset_span ⟨t, h, rfl⟩

theorem mu_tens_ex {I : Type} [Fintype I] {Λ : I → Lat ξ Ω} {a : I → ℤ} {w : Ω} (h : (Lat.tens Λ a).IsGenAt q w) :
    ∃ t : I → Ω, ∀ j, (Λ j).IsGenAt q (t j) := by
  by_contra hn
  have e : (Lat.tens Λ a) q = ⊥ := by
    refine le_bot_iff.1 (Submodule.span_le.2 ?_)
    rintro _ ⟨s, hs, rfl⟩
    exact absurd ⟨s, hs⟩ hn
  have : w ∈ (Lat.tens Λ a) q := h.2 ▸ Submodule.mem_span_singleton_self _
  rw [e] at this
  exact h.1 this

theorem mu_deg_gen {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} {Λ : Lat ξ Ω} {a : K → ℤ} {e : Ω}
    (h : Λ.IsDegOn Set.univ y a e) {ch : ∀ k, J k} (hc : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) ch q) :
    Λ.IsGenAt q ((∏ k, y ⟨k, ch k⟩ ^ a k) * e) :=
  ⟨mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (Finset.prod_ne_zero_iff.1 hc.1 k (Finset.mem_univ _))) h.1,
    h.2 q trivial ch hc⟩

theorem mu_char0 [Algebra ℚ Ω₃] {O : ValuationSubring Ω₃} {i : Ω →+* Ω₃} (hD : Dom O i ξ q)
    (hO : ∀ x : ℚ, algebraMap ℚ Ω₃ x ∈ O) (p : ℕ) (hp : p.Prime) : ¬ InFibre ξ p q := by
  have : CharZero Ω₃ := algebraRat.charZero Ω₃
  have h0 : (p : Ω) ≠ 0 := fun h => by
    have := congrArg i h
    rw [map_natCast, map_zero] at this
    exact hp.ne_zero (Nat.cast_eq_zero.1 this)
  refine not_not.2 ⟨h0, natCast_mem _ _, hD.2 _ (natCast_mem _ _) h0 ?_⟩
  simpa using hO (p : ℚ)⁻¹

theorem mu_side {V : Type} [AddCommGroup V] [Module Ω V] (L : Lat ξ V) {r r' : ℕ} (hr : r = r') (W : Submodule Ω V)
    (hL : L.IsVB r W) (c : Fin r → V) (hc : LinearIndependent Ω c) (hW : Submodule.span Ω (Set.range c) = W)
    (s : Fin r' → V) (hs : LinearIndependent Ω s) (hsW : ∀ k, s k ∈ W) :
    ∃ ρ : Ω, ρ ≠ 0 ∧ ∀ (q : Cpt ξ) (O : ValuationSubring Ω₃) (i : Ω →+* Ω₃) (Ω₀ : Type) (ψ : Ω₀ → Ω) (B : Set (Fin r → Ω₀)),
      Dom O i ξ q → L q = Submodule.span (regAt ξ q) {w | ∃ a ∈ B, w = ∑ m, ψ (a m) • c m} →
      ∃ (t : Ω) (T : Matrix (Fin r) (Fin r) Ω₃), (detLat L s).IsGenAt q t ∧ T.det = i (ρ * t) ∧
        Submodule.span O (Set.range fun k m => T m k) = Submodule.span O {x | ∃ a ∈ B, x = fun m => i (ψ (a m))} := by
  subst hr
  subst hW
  choose P hP using fun k => (Submodule.mem_span_range_iff_exists_fun Ω).1 (hsW k)
  have hPi : LinearIndependent Ω P := by
    refine LinearIndependent.of_comp (Fintype.linearCombination Ω c) ?_
    convert hs using 1
    funext k
    simpa [Fintype.linearCombination_apply] using hP k
  set Pm : Matrix (Fin r) (Fin r) Ω := (Matrix.of P).transpose with hPm
  have hd : Pm.det ≠ 0 := by
    rw [hPm, Matrix.det_transpose]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_rows_iff_isUnit.1 hPi)).ne_zero
  refine ⟨Pm.det, hd, fun q O i Ω₀ ψ B hD hq => ?_⟩
  obtain ⟨U, hU, b, hb, hf⟩ := hL q trivial
  have hf := hf q trivial hU
  choose T₀ hT using fun k => (Submodule.mem_span_range_iff_exists_fun Ω).1
    (show b k ∈ Submodule.span Ω (Set.range c) from hb ▸ Submodule.subset_span ⟨k, rfl⟩)
  set Tm : Matrix (Fin r) (Fin r) Ω := (Matrix.of T₀).transpose with hTm
  have hPT : Pm * (Pm⁻¹ * Tm) = Tm := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (Ne.isUnit hd), Matrix.one_mul]
  have hbs : ∀ k, b k = ∑ k', (Pm⁻¹ * Tm) k' k • s k' := fun k => by
    rw [← hT k]
    simp only [← hP, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    have := congrFun (congrFun hPT m) k
    rw [Matrix.mul_apply] at this
    rw [show T₀ k m = Tm m k from rfl, ← this]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  refine ⟨(Pm⁻¹ * Tm).det, Tm.map i, GlobalTheory.T.det_lattice_frame_gen X Ω ξ V L r s b _ q hs hf hbs, ?_, le_antisymm (Submodule.span_le.2 ?_)
    (Submodule.span_le.2 ?_)⟩
  · rw [← Matrix.det_mul, hPT]
    exact (RingHom.map_det i _).symm
  · rintro _ ⟨k, rfl⟩
    refine mu_coord O (regAt ξ q) i hD.1 c hc {w | ∃ a ∈ B, w = ∑ m, ψ (a m) • c m} _ ?_ (T₀ k) ?_
    · rintro _ ⟨a, ha, rfl⟩
      exact ⟨_, rfl, Submodule.subset_span ⟨a, ha, rfl⟩⟩
    · rw [← hq, hT k, hf.2]
      exact Submodule.subset_span ⟨k, rfl⟩
  · rintro _ ⟨a, ha, rfl⟩
    refine mu_coord O (regAt ξ q) i hD.1 c hc (Set.range b) _ ?_ (fun m => ψ (a m)) ?_
    · rintro _ ⟨k, rfl⟩
      exact ⟨T₀ k, (hT k).symm, Submodule.subset_span ⟨k, rfl⟩⟩
    · rw [← hf.2, hq]
      exact Submodule.subset_span ⟨a, ha, rfl⟩

end Lats

end SheetDecomposition
