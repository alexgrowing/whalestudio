import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsDiagPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.MemDivSuppOfDivCycleNeZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedC
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

universe u

namespace DiagPull

section Ring

variable {R : Type*} [CommRing R]

theorem mem_minimalPrimes_of_cross {V W : Ideal R} {f g u v : R} (hrel : f * v - g * u ∈ V)
    (hW : W ∈ (V ⊔ Ideal.span {f}).minimalPrimes) (hu : u ∉ W) (hv : v ∉ W) :
    W ∈ (V ⊔ Ideal.span {g}).minimalPrimes := by
  have hWp := hW.1.1
  have hVW : V ≤ W := le_sup_left.trans hW.1.2
  have hfW : f ∈ W := hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  have hgW : g ∈ W := by
    have h : g * u ∈ W := by
      have e : g * u = f * v - (f * v - g * u) := by ring
      rw [e]
      exact W.sub_mem (W.mul_mem_right v hfW) (hVW hrel)
    exact (hWp.mem_or_mem h).resolve_right hu
  refine ⟨⟨hWp, sup_le hVW ((Ideal.span_singleton_le_iff_mem _).mpr hgW)⟩, fun Q hQ hQW => ?_⟩
  have hVQ : V ≤ Q := le_sup_left.trans hQ.2
  have hgQ : g ∈ Q := hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self g))
  have hfQ : f ∈ Q := by
    have h : f * v ∈ Q := by
      have e : f * v = (f * v - g * u) + g * u := by ring
      rw [e]
      exact Q.add_mem (hVQ hrel) (Q.mul_mem_right u hgQ)
    exact (hQ.1.mem_or_mem h).resolve_right fun h' => hv (hQW h')
  exact hW.2 ⟨hQ.1, sup_le hVQ ((Ideal.span_singleton_le_iff_mem _).mpr hfQ)⟩ hQW

theorem locLen_cross {V : Ideal R} (hV : V.IsPrime) {f g u v : R} (hrel : f * v - g * u ∈ V)
    (p : PrimeSpectrum R) (hVp : V ≤ p.asIdeal) (hu : u ∉ p.asIdeal) (hv : v ∉ p.asIdeal) :
    locLen (R ⧸ (V ⊔ Ideal.span {f})) p = locLen (R ⧸ (V ⊔ Ideal.span {g})) p := by
  have e : V ⊔ Ideal.span {v * f} = V ⊔ Ideal.span {u * g} := by
    apply le_antisymm
    · refine sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
      have e' : v * f = (f * v - g * u) + u * g := by ring
      rw [e']
      exact Ideal.add_mem _ (Ideal.mem_sup_left hrel)
        (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    · refine sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
      have e' : u * g = v * f - (f * v - g * u) := by ring
      rw [e']
      exact Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
        (Ideal.mem_sup_left hrel)
  have h1 := I1.locLen_mul hV (fun h => hv (hVp h)) f p
  have h2 := I1.locLen_mul hV (fun h => hu (hVp h)) g p
  rw [e, h2, I1.locLen_quot_eq_zero p hu, I1.locLen_quot_eq_zero p hv, add_zero, add_zero] at h1
  exact h1.symm

end Ring

section Homog

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem eval₂_mul_blk {S : Type*} [CommRing S] {s : MRing ι} {d : K → ℕ} (hs : IsMultiHomog s d)
    (f : ℤ →+* S) (g : (Σ k, ι k) → S) (t : K → S) :
    eval₂ f (fun q => g q * t q.1) s = (∏ k, t k ^ d k) * eval₂ f g s := by
  rw [eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hprod : ∏ q, (g q * t q.1) ^ m q = (∏ k, t k ^ d k) * ∏ q, g q ^ m q := by
    simp_rw [mul_pow, Finset.prod_mul_distrib]
    rw [mul_comm]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, t k ^ m ⟨k, i⟩ = t k ^ d k
    rw [Finset.prod_pow_eq_pow_sum, hs m hm k]
  rw [hprod]
  ring

end Homog

theorem prod_YBlk {M : Type*} [CommMonoid M] (f : T.YBlk → M) : ∏ b, f b = f .base * (f .det * f .line) := by
  rw [show (Finset.univ : Finset T.YBlk) = {.base, .det, .line} from rfl]
  simp

def blk (j : Fin 2) : T.YBlk → T.WBlk
  | .base => .base
  | .det => .det
  | .line => if j = 0 then .line0 else .line1

def lineScal (c : ℂ) : T.YBlk → ℂ
  | .line => c
  | _ => 1

section Models

variable {Ω : Type*} [Field Ω] {ι ν κ : Type u} [Fintype ι] [Fintype ν] [Fintype κ]
  {E : Type*} [AddCommGroup E] [Module Ω E] {Φ : Type*} [Field Φ] [Algebra Ω Φ]
  (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (a₀ : Φ)

theorem multiConeMap_rename (j : Fin 2) (s : MRing (T.yyIdx ι ν κ)) :
    T.multiConeMap (T.wwCoord x δ e φ a₀ a₀) (rename (T.yyEmb j) s) =
      eval₂ (Int.castRingHom _) (fun q => C (T.yyCoord x δ e φ a₀ q) * X (blk j q.1)) s := by
  rw [T.multiConeMap, coe_eval₂Hom, eval₂_rename]
  congr 1
  funext q
  obtain ⟨b, i⟩ := q
  fin_cases j <;> cases b <;> rfl

theorem multiConeMap_X_line0 (k : κ) :
    T.multiConeMap (T.wwCoord x δ e φ a₀ a₀) (X ⟨.line0, k⟩) = C (T.lineVal e (φ k) a₀) * X .line0 := by
  simp [T.multiConeMap, T.wwCoord]

theorem multiConeMap_X_line1 (k : κ) :
    T.multiConeMap (T.wwCoord x δ e φ a₀ a₀) (X ⟨.line1, k⟩) = C (T.lineVal e (φ k) a₀) * X .line1 := by
  simp [T.multiConeMap, T.wwCoord]

theorem minor_mem (i k : κ) :
    (X ⟨.line0, i⟩ * X ⟨.line1, k⟩ - X ⟨.line0, k⟩ * X ⟨.line1, i⟩ : MRing (T.wwIdx ι ν κ)) ∈
      T.wwIdeal x δ e φ a₀ a₀ := by
  rw [T.wwIdeal, RingHom.mem_ker, map_sub, map_mul, map_mul, multiConeMap_X_line0, multiConeMap_X_line1,
    multiConeMap_X_line0, multiConeMap_X_line1]
  ring

theorem cross_mem (s : MRing (T.yyIdx ι ν κ)) (d : T.YBlk → ℕ) (hs : IsMultiHomog s d) (k : κ) :
    rename (T.yyEmb 0) s * X ⟨.line1, k⟩ ^ d .line - rename (T.yyEmb 1) s * X ⟨.line0, k⟩ ^ d .line ∈
      T.wwIdeal x δ e φ a₀ a₀ := by
  rw [T.wwIdeal, RingHom.mem_ker, map_sub, map_mul, map_mul, map_pow, map_pow, multiConeMap_X_line0,
    multiConeMap_X_line1, multiConeMap_rename, multiConeMap_rename,
    eval₂_mul_blk hs (Int.castRingHom _) (fun q => C (T.yyCoord x δ e φ a₀ q)) (fun b => X (blk 0 b)),
    eval₂_mul_blk hs (Int.castRingHom _) (fun q => C (T.yyCoord x δ e φ a₀ q)) (fun b => X (blk 1 b)),
    prod_YBlk, prod_YBlk]
  simp only [blk]
  simp only [Fin.isValue, if_true, one_ne_zero, if_false]
  ring

theorem exists_line_notMem {W : Ideal (MRing (T.wwIdx ι ν κ))} (hW : W.IsPrime)
    (hΔ : T.wwIdeal x δ e φ a₀ a₀ ≤ W) (hrel : IsRelevant W) :
    ∃ k : κ, (X ⟨.line0, k⟩ : MRing (T.wwIdx ι ν κ)) ∉ W ∧ (X ⟨.line1, k⟩ : MRing (T.wwIdx ι ν κ)) ∉ W := by
  obtain ⟨i, hi⟩ := hrel .line0
  obtain ⟨j, hj⟩ := hrel .line1
  refine ⟨i, hi, fun h => ?_⟩
  have hm := hΔ (minor_mem x δ e φ a₀ i j)
  have h2 : (X ⟨.line0, j⟩ * X ⟨.line1, i⟩ : MRing (T.wwIdx ι ν κ)) ∈ W := W.mul_mem_left _ h
  have h3 : (X ⟨.line0, i⟩ * X ⟨.line1, j⟩ : MRing (T.wwIdx ι ν κ)) ∈ W := by
    have e' : (X ⟨.line0, i⟩ * X ⟨.line1, j⟩ : MRing (T.wwIdx ι ν κ)) =
        (X ⟨.line0, i⟩ * X ⟨.line1, j⟩ - X ⟨.line0, j⟩ * X ⟨.line1, i⟩) + X ⟨.line0, j⟩ * X ⟨.line1, i⟩ := by
      ring
    rw [e']
    exact W.add_mem hm h2
  rcases hW.mem_or_mem h3 with h4 | h4
  · exact hi h4
  · exact hj h4

omit [Fintype ι] [Fintype ν] [Fintype κ] in
theorem multAt_eq_locLen (J W : Ideal (MRing (T.wwIdx ι ν κ))) (hW : W.IsPrime) :
    multAt J W = (locLen (MRing (T.wwIdx ι ν κ) ⧸ J) ⟨W, hW⟩).toNat := by
  simp [multAt, hW, locLen]

theorem divCycle_eq (s : MRing (T.yyIdx ι ν κ)) (d : T.YBlk → ℕ) (hs : IsMultiHomog s d) :
    divCycle (T.wwIdeal x δ e φ a₀ a₀) (rename (T.yyEmb 0) s) =
      divCycle (T.wwIdeal x δ e φ a₀ a₀) (rename (T.yyEmb 1) s) := by
  classical
  have hV : (T.wwIdeal x δ e φ a₀ a₀).IsPrime := RingHom.ker_isPrime _
  have hc := cross_mem x δ e φ a₀ s d hs
  have hc' : ∀ k : κ, rename (T.yyEmb 1) s * X ⟨.line0, k⟩ ^ d .line -
      rename (T.yyEmb 0) s * X ⟨.line1, k⟩ ^ d .line ∈ T.wwIdeal x δ e φ a₀ a₀ := fun k => by
    rw [← neg_sub]
    exact neg_mem (hc k)
  have hsupp : ∀ W, W ∈ divSupp (T.wwIdeal x δ e φ a₀ a₀) (rename (T.yyEmb 0) s) ↔
      W ∈ divSupp (T.wwIdeal x δ e φ a₀ a₀) (rename (T.yyEmb 1) s) := by
    intro W
    constructor
    · rintro ⟨hW, hr⟩
      obtain ⟨k, h0, h1⟩ := exists_line_notMem x δ e φ a₀ hW.1.1 (le_sup_left.trans hW.1.2) hr
      exact ⟨mem_minimalPrimes_of_cross (hc k) hW (fun h => h0 (hW.1.1.mem_of_pow_mem _ h))
        (fun h => h1 (hW.1.1.mem_of_pow_mem _ h)), hr⟩
    · rintro ⟨hW, hr⟩
      obtain ⟨k, h0, h1⟩ := exists_line_notMem x δ e φ a₀ hW.1.1 (le_sup_left.trans hW.1.2) hr
      exact ⟨mem_minimalPrimes_of_cross (hc' k) hW (fun h => h1 (hW.1.1.mem_of_pow_mem _ h))
        (fun h => h0 (hW.1.1.mem_of_pow_mem _ h)), hr⟩
  ext W
  simp only [divCycle, Finsupp.ofSupportFinite_coe]
  by_cases h : W ∈ divSupp (T.wwIdeal x δ e φ a₀ a₀) (rename (T.yyEmb 0) s)
  · rw [if_pos h, if_pos ((hsupp W).1 h)]
    obtain ⟨hW, hr⟩ := h
    have hWp := hW.1.1
    obtain ⟨k, h0, h1⟩ := exists_line_notMem x δ e φ a₀ hWp (le_sup_left.trans hW.1.2) hr
    rw [multAt_eq_locLen _ _ hWp, multAt_eq_locLen _ _ hWp,
      locLen_cross hV (hc k) ⟨W, hWp⟩ (le_sup_left.trans hW.1.2)
        (fun h => h0 (hWp.mem_of_pow_mem _ h)) (fun h => h1 (hWp.mem_of_pow_mem _ h))]
  · rw [if_neg h, if_neg (mt (hsupp W).2 h)]

theorem exists_line_prop {z : (Σ k, T.wwIdx ι ν κ k) → ℂ} (hz : z ∈ mcPts (T.wwIdeal x δ e φ a₀ a₀)) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ k : κ, z ⟨.line1, k⟩ = c * z ⟨.line0, k⟩ := by
  have hmin : ∀ i k : κ, z ⟨.line0, i⟩ * z ⟨.line1, k⟩ - z ⟨.line0, k⟩ * z ⟨.line1, i⟩ = 0 := by
    intro i k
    have := hz.2 _ (minor_mem x δ e φ a₀ i k)
    simpa using this
  obtain ⟨i, hi⟩ := hz.1 .line0
  obtain ⟨j, hj⟩ := hz.1 .line1
  have hi' : z ⟨.line0, i⟩ ≠ 0 := hi
  have hk : ∀ k : κ, z ⟨.line1, k⟩ = z ⟨.line1, i⟩ / z ⟨.line0, i⟩ * z ⟨.line0, k⟩ := by
    intro k
    have h := hmin i k
    field_simp
    linear_combination h
  refine ⟨z ⟨.line1, i⟩ / z ⟨.line0, i⟩, fun h0 => hj ?_, hk⟩
  rw [hk j, h0, zero_mul]

omit [Fintype ι] [Fintype ν] [Fintype κ] in
theorem diagonalPullback_secondLine_eq {z : (Σ k, T.wwIdx ι ν κ k) → ℂ} {c : ℂ} (hk : ∀ k : κ, z ⟨.line1, k⟩ = c * z ⟨.line0, k⟩) :
    (fun p => z (T.yyEmb 1 p)) = fun p => lineScal c p.1 * z (T.yyEmb 0 p) := by
  funext p
  obtain ⟨b, i⟩ := p
  cases b
  · simp [T.yyEmb, lineScal]
  · simp [T.yyEmb, lineScal]
  · exact hk i

end Models

end DiagPull

theorem DiagPull.proof : DiagPull.Statement := by
  intro Ω _ ι ν κ _ _ _ E _ _ Φ _ _ x e φ δ a₀
  refine ⟨fun s d hs => DiagPull.divCycle_eq x δ e φ a₀ s d hs, ?_, ?_⟩
  · intro A A₀ A₁ h0 h1 z hz
    obtain ⟨c, hc, hk⟩ := DiagPull.exists_line_prop x δ e φ a₀ hz
    refine ⟨c, hc, hk, ?_⟩
    rw [h1.2, h0.2, DiagPull.diagonalPullback_secondLine_eq hk]
    have hne : ∀ b, DiagPull.lineScal c b ≠ 0 := fun b => by cases b <;> simp [DiagPull.lineScal, hc]
    rw [A.smul _ _ hne]
    congr 1
    rw [DiagPull.prod_YBlk]
    simp [DiagPull.lineScal]
  · intro s d hs A A₀ A₁ hA h0 h1 z hz
    obtain ⟨c, hc, hk⟩ := DiagPull.exists_line_prop x δ e φ a₀ hz
    have hne : ∀ b, DiagPull.lineScal c b ≠ 0 := fun b => by cases b <;> simp [DiagPull.lineScal, hc]
    have hh : A₁.h z = ‖c‖ ^ (d .line) * A₀.h z := by
      rw [h1.2, h0.2, DiagPull.diagonalPullback_secondLine_eq hk, A.smul _ _ hne, DiagPull.prod_YBlk, hA .line]
      simp [DiagPull.lineScal]
    have hev : eval z (map (Int.castRingHom ℂ) (rename (T.yyEmb 1) s)) =
        c ^ (d .line) * eval z (map (Int.castRingHom ℂ) (rename (T.yyEmb 0) s)) := by
      rw [map_rename, map_rename, eval_rename, eval_rename]
      have e1 : z ∘ T.yyEmb 1 = fun p => DiagPull.lineScal c p.1 * (z ∘ T.yyEmb 0) p :=
        DiagPull.diagonalPullback_secondLine_eq hk
      rw [e1, eval_smul_of_isMultiHomog hs, DiagPull.prod_YBlk]
      simp [DiagPull.lineScal]
    unfold logNorm
    rw [hev, hh, norm_mul, norm_pow, mul_div_mul_left]
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr hc)

end

end GroundTheory.Heights₂.Heights.Inter
