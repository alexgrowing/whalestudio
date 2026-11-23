import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsDiagFormDiv
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsChartFormsRational
import GroundTheory.HeightsAndTheta.Heights.Intersections.PMobiusAlgIndep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

namespace DiagonalFormDivisor

set_option linter.unusedSectionVars false

section Generic

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]

theorem homog_zero (a : K → ℕ) : IsMultiHomog (0 : MRing ι) a := by
  intro m hm
  simp at hm

theorem homog_one : IsMultiHomog (1 : MRing ι) 0 := by
  classical
  intro m hm k
  rw [mem_support_iff, coeff_one] at hm
  split_ifs at hm with h
  · subst h
    simp
  · exact absurd rfl hm

theorem homog_add {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h
  exacts [hf m h k, hg m h k]

theorem homog_neg {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) : IsMultiHomog (-f) a := by
  intro m hm
  rw [mem_support_iff, coeff_neg, neg_ne_zero, ← mem_support_iff] at hm
  exact hf m hm

def fracPairs (c c' : (Σ k, ι k) → Φ) : Subring (Φ × Φ) where
  carrier := {w | ∃ (γ : K → ℕ) (r q : MRing ι), IsMultiHomog r γ ∧ IsMultiHomog q γ ∧ aeval c q ≠ 0 ∧
    aeval c' q ≠ 0 ∧ aeval c r = aeval c q * w.1 ∧ aeval c' r = aeval c' q * w.2}
  zero_mem' := ⟨0, 0, 1, homog_zero _, homog_one, by simp, by simp, by simp, by simp⟩
  one_mem' := ⟨0, 1, 1, homog_one, homog_one, by simp, by simp, by simp, by simp⟩
  add_mem' := by
    rintro w₁ w₂ ⟨γ₁, r₁, q₁, hr₁, hq₁, h₁, h₁', e₁, e₁'⟩ ⟨γ₂, r₂, q₂, hr₂, hq₂, h₂, h₂', e₂, e₂'⟩
    refine ⟨γ₁ + γ₂, r₁ * q₂ + q₁ * r₂, q₁ * q₂, homog_add (exHomog_mul hr₁ hq₂) (exHomog_mul hq₁ hr₂),
      exHomog_mul hq₁ hq₂, by simp [h₁, h₂], by simp [h₁', h₂'], ?_, ?_⟩
    · simp only [map_add, map_mul, e₁, e₂, Prod.fst_add]
      ring
    · simp only [map_add, map_mul, e₁', e₂', Prod.snd_add]
      ring
  mul_mem' := by
    rintro w₁ w₂ ⟨γ₁, r₁, q₁, hr₁, hq₁, h₁, h₁', e₁, e₁'⟩ ⟨γ₂, r₂, q₂, hr₂, hq₂, h₂, h₂', e₂, e₂'⟩
    refine ⟨γ₁ + γ₂, r₁ * r₂, q₁ * q₂, exHomog_mul hr₁ hr₂, exHomog_mul hq₁ hq₂, by simp [h₁, h₂],
      by simp [h₁', h₂'], ?_, ?_⟩
    · simp only [map_mul, e₁, e₂, Prod.fst_mul]
      ring
    · simp only [map_mul, e₁', e₂', Prod.snd_mul]
      ring
  neg_mem' := by
    rintro w ⟨γ, r, q, hr, hq, h, h', e, e'⟩
    exact ⟨γ, -r, q, homog_neg hr, hq, h, h', by simp [e], by simp [e']⟩

theorem mem_fracPairs_of {c c' : (Σ k, ι k) → Φ} {γ : K → ℕ} {r q : MRing ι} {y y' : Φ} (hr : IsMultiHomog r γ)
    (hq : IsMultiHomog q γ) (h : aeval c q ≠ 0) (h' : aeval c' q ≠ 0) (e : aeval c r = aeval c q * y)
    (e' : aeval c' r = aeval c' q * y') : (y, y') ∈ fracPairs c c' :=
  ⟨γ, r, q, hr, hq, h, h', e, e'⟩

theorem fracPairs_div {c c' : (Σ k, ι k) → Φ} {p p' : Φ} (hp : (p, p) ∈ fracPairs c c')
    (hp' : (p', p') ∈ fracPairs c c') (h0 : p' ≠ 0) : (p / p', p / p') ∈ fracPairs c c' := by
  obtain ⟨γ₁, r₁, q₁, hr₁, hq₁, h₁, h₁', e₁, e₁'⟩ := hp
  obtain ⟨γ₂, r₂, q₂, hr₂, hq₂, h₂, h₂', e₂, e₂'⟩ := hp'
  refine ⟨γ₁ + γ₂, r₁ * q₂, q₁ * r₂, exHomog_mul hr₁ hq₂, exHomog_mul hq₁ hr₂, ?_, ?_, ?_, ?_⟩
  · rw [map_mul, e₂]
    exact mul_ne_zero h₁ (mul_ne_zero h₂ h0)
  · rw [map_mul, e₂']
    exact mul_ne_zero h₁' (mul_ne_zero h₂' h0)
  · rw [map_mul, map_mul, e₁, e₂]
    field_simp
  · rw [map_mul, map_mul, e₁', e₂']
    field_simp

theorem eval₂_mem_fracPairs {R : Type} [CommRing R] (f : R →+* Φ) {c c' : (Σ k, ι k) → Φ}
    (hf : ∀ y, (f y, f y) ∈ fracPairs c c') {n : Type} (z z' : n → Φ) (hz : ∀ j, (z j, z' j) ∈ fracPairs c c')
    (G : MvPolynomial n R) : (eval₂ f z G, eval₂ f z' G) ∈ fracPairs c c' := by
  induction G using MvPolynomial.induction_on with
  | C y => simpa using hf y
  | add p q hp hq => simpa using add_mem hp hq
  | mul_X p j hp => simpa using mul_mem hp (hz j)

theorem aeval_scale (u : K → Φ) (c : (Σ k, ι k) → Φ) (s : MRing ι) (β : K → ℕ) (hs : IsMultiHomog s β) :
    aeval (fun p => u p.1 * c p) s = (∏ k, u k ^ β k) * aeval c s := by
  have h1 := congrArg (MvPolynomial.eval u) (DiagRAux.multiConeMap_of_homog c s β hs)
  have h2 : (MvPolynomial.eval u).comp (T.multiConeMap c) =
      (aeval (fun p => u p.1 * c p) : MRing ι →ₐ[ℤ] Φ).toRingHom :=
    MvPolynomial.ringHom_ext (fun r => by simp [T.multiConeMap]) (fun p => by simp [T.multiConeMap, mul_comm])
  rw [← RingHom.comp_apply, h2, map_mul, eval_C, map_prod] at h1
  simp only [map_pow, eval_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h1
  rw [h1, mul_comm]

end Generic

theorem X_sub_X_dvd {R : Type} [CommRing R] (P : MvPolynomial (Fin 2) R) :
    (X 1 - X 0 : MvPolynomial (Fin 2) R) ∣ P - aeval (fun _ => (X 0 : MvPolynomial (Fin 2) R)) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    rw [map_add, add_sub_add_comm]
    exact dvd_add hp hq
  | mul_X p n hp =>
    rw [map_mul, aeval_X]
    have e : p * X n - aeval (fun _ => (X 0 : MvPolynomial (Fin 2) R)) p * X 0 =
        (p - aeval (fun _ => (X 0 : MvPolynomial (Fin 2) R)) p) * X n +
          aeval (fun _ => (X 0 : MvPolynomial (Fin 2) R)) p * (X n - X 0) := by ring
    rw [e]
    refine dvd_add (dvd_mul_of_dvd_left hp _) (dvd_mul_of_dvd_right ?_ _)
    fin_cases n
    · simp
    · exact dvd_rfl

theorem prod_wblk {M : Type} [CommMonoid M] (g : T.WBlk → M) :
    ∏ k, g k = g .base * g .det * g .line0 * g .line1 := by
  rw [show (Finset.univ : Finset T.WBlk) = {.base, .det, .line0, .line1} from rfl]
  simp [Finset.prod_insert, mul_assoc]

section Geometry

variable {Ω : Type} [Field Ω] {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] {E : Type} [AddCommGroup E] [Module Ω E] {Φ : Type} [Field Φ]
  [Algebra Ω Φ]

def ratioPoly {R : Type} [CommRing R] (xb : ι → R) (ε : ν → R) (c₀ c₁ : κ → R) :
    (Σ k, T.wwIdx ι ν κ k) → MvPolynomial (Fin 2) R
  | ⟨.base, j⟩ => C (xb j)
  | ⟨.det, l⟩ => C (ε l)
  | ⟨.line0, k⟩ => C (c₀ k) + C (c₁ k) * X 0
  | ⟨.line1, k⟩ => C (c₀ k) + C (c₁ k) * X 1

def blockScale {M : Type} (u₁ u₂ u₃ u₄ : M) : T.WBlk → M
  | .base => u₁
  | .det => u₂
  | .line0 => u₃
  | .line1 => u₄

theorem lineVal_comb (e : Module.Basis (Fin 2) Ω E) (φ₀ φ₁ : E →ₗ[Ω] Ω) (c₀ c₁ : Ω) (b : Φ) :
    T.lineVal e (c₀ • φ₀ + c₁ • φ₁) b =
      algebraMap Ω Φ c₀ * T.lineVal e φ₀ b + algebraMap Ω Φ c₁ * T.lineVal e φ₁ b := by
  simp only [T.lineVal, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, map_add, map_mul]
  ring

theorem wwCoord_eq (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (F : Subfield Ω)
    (i : ι) (l₀ : ν) (k₀ k₁ : κ) (hx : x i ≠ 0) (hδ : δ l₀ ≠ 0) (xb : ι → F) (ε : ν → F) (c₀ c₁ : κ → F)
    (hxb : ∀ j, (xb j : Ω) = x j / x i) (hε : ∀ l, (ε l : Ω) = δ l / δ l₀)
    (hc : ∀ k, φ k = (c₀ k : Ω) • φ k₀ + (c₁ k : Ω) • φ k₁) (b₀ b₁ : Φ) (w : Fin 2 → Φ)
    (h₀ : T.lineVal e (φ k₀) b₀ ≠ 0) (h₁ : T.lineVal e (φ k₀) b₁ ≠ 0)
    (hw₀ : w 0 = T.lineVal e (φ k₁) b₀ / T.lineVal e (φ k₀) b₀)
    (hw₁ : w 1 = T.lineVal e (φ k₁) b₁ / T.lineVal e (φ k₀) b₁) :
    T.wwCoord x δ e φ b₀ b₁ = fun p => blockScale (algebraMap Ω Φ (x i)) (algebraMap Ω Φ (δ l₀))
      (T.lineVal e (φ k₀) b₀) (T.lineVal e (φ k₀) b₁) p.1 *
        eval₂ ((algebraMap Ω Φ).comp F.subtype) w (ratioPoly xb ε c₀ c₁ p) := by
  have hx' : algebraMap Ω Φ (x i) ≠ 0 := (map_ne_zero _).2 hx
  have hδ' : algebraMap Ω Φ (δ l₀) ≠ 0 := (map_ne_zero _).2 hδ
  funext p
  rcases p with ⟨_ | _ | _ | _, j⟩
  · simp only [T.wwCoord, blockScale, ratioPoly, eval₂_C, RingHom.comp_apply, Subfield.coe_subtype]
    rw [hxb j, map_div₀]
    field_simp
  · simp only [T.wwCoord, blockScale, ratioPoly, eval₂_C, RingHom.comp_apply, Subfield.coe_subtype]
    rw [hε j, map_div₀]
    field_simp
  · simp only [T.wwCoord, blockScale, ratioPoly, eval₂_add, eval₂_mul, eval₂_C, eval₂_X, RingHom.comp_apply,
      Subfield.coe_subtype, hw₀]
    rw [hc j, lineVal_comb]
    field_simp
  · simp only [T.wwCoord, blockScale, ratioPoly, eval₂_add, eval₂_mul, eval₂_C, eval₂_X, RingHom.comp_apply,
      Subfield.coe_subtype, hw₁]
    rw [hc j, lineVal_comb]
    field_simp

theorem aeval_comp_eval₂ {σ n R : Type} [CommRing R] (f : R →+* Φ) (w : n → Φ) (g : σ → MvPolynomial n R)
    (s : MvPolynomial σ ℤ) : aeval (fun p => eval₂ f w (g p)) s = eval₂ f w (aeval g s) := by
  have h : (eval₂Hom f w).comp (aeval g : MvPolynomial σ ℤ →ₐ[ℤ] MvPolynomial n R).toRingHom =
      (aeval (fun p => eval₂ f w (g p)) : MvPolynomial σ ℤ →ₐ[ℤ] Φ).toRingHom :=
    MvPolynomial.ringHom_ext (fun r => by simp) (fun p => by simp)
  exact (RingHom.congr_fun h s).symm

theorem homog_monomial (i : ι) (l : ν) (k : κ) (n₁ n₂ n₃ n₄ : ℕ) :
    IsMultiHomog (X ⟨.base, i⟩ ^ n₁ * X ⟨.det, l⟩ ^ n₂ * X ⟨.line0, k⟩ ^ n₃ * X ⟨.line1, k⟩ ^ n₄ :
      MRing (T.wwIdx ι ν κ)) (blockScale n₁ n₂ n₃ n₄) := by
  have h := exHomog_mul (exHomog_mul (exHomog_mul (exHomog_pow (exHomog_X (ι := T.wwIdx ι ν κ) T.WBlk.base i) n₁)
    (exHomog_pow (exHomog_X (ι := T.wwIdx ι ν κ) T.WBlk.det l) n₂))
    (exHomog_pow (exHomog_X (ι := T.wwIdx ι ν κ) T.WBlk.line0 k) n₃))
    (exHomog_pow (exHomog_X (ι := T.wwIdx ι ν κ) T.WBlk.line1 k) n₄)
  convert h using 1
  funext b
  cases b <;> simp [blockScale]

theorem line_mem_fracPairs (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (k₀ k₁ : κ)
    (b₀ b₁ : Φ) (h₀ : T.lineVal e (φ k₀) b₀ ≠ 0) (h₁ : T.lineVal e (φ k₀) b₁ ≠ 0) :
    (T.lineVal e (φ k₁) b₀ / T.lineVal e (φ k₀) b₀, T.lineVal e (φ k₁) b₀ / T.lineVal e (φ k₀) b₀) ∈
        fracPairs (T.wwCoord x δ e φ b₀ b₁) (T.wwCoord x δ e φ b₀ b₀) ∧
      (T.lineVal e (φ k₁) b₁ / T.lineVal e (φ k₀) b₁, T.lineVal e (φ k₁) b₀ / T.lineVal e (φ k₀) b₀) ∈
        fracPairs (T.wwCoord x δ e φ b₀ b₁) (T.wwCoord x δ e φ b₀ b₀) := by
  have hq := exHomog_mul (exHomog_X (ι := T.wwIdx ι ν κ) T.WBlk.line0 k₀) (exHomog_X T.WBlk.line1 k₀)
  constructor
  · refine mem_fracPairs_of (exHomog_mul (exHomog_X T.WBlk.line0 k₁) (exHomog_X T.WBlk.line1 k₀)) hq ?_ ?_ ?_ ?_
    · simp only [map_mul, aeval_X, T.wwCoord]
      exact mul_ne_zero h₀ h₁
    · simp only [map_mul, aeval_X, T.wwCoord]
      exact mul_ne_zero h₀ h₀
    · simp only [map_mul, aeval_X, T.wwCoord]
      field_simp
    · simp only [map_mul, aeval_X, T.wwCoord]
      field_simp
  · refine mem_fracPairs_of (exHomog_mul (exHomog_X T.WBlk.line0 k₀) (exHomog_X T.WBlk.line1 k₁)) hq ?_ ?_ ?_ ?_
    · simp only [map_mul, aeval_X, T.wwCoord]
      exact mul_ne_zero h₀ h₁
    · simp only [map_mul, aeval_X, T.wwCoord]
      exact mul_ne_zero h₀ h₀
    · simp only [map_mul, aeval_X, T.wwCoord]
      field_simp
    · simp only [map_mul, aeval_X, T.wwCoord]
      field_simp

end Geometry

end DiagonalFormDivisor

open DiagonalFormDivisor in

theorem DiagFormDiv.proof (hF : ChartFormsRational.Statement) : DiagFormDiv.Statement := by
  intro Ω _ ι ν κ _ _ _ E _ _ Φ _ _ x B e φ δ hS hG hD hx a ha α d hd hdΔ
  obtain ⟨i, hi⟩ := hx
  obtain ⟨l₀, k₀, k₁, hδ, hDet, hε, ⟨c₀, c₁, hc₀, hc₁, hc⟩, hκ⟩ := hF Ω ι ν κ E x B e φ δ hS hG hD i hi
  obtain ⟨hL, hind⟩ := MobiusAlgIndep.proof Ω Φ 2 a (φ k₁ (e 0)) (φ k₁ (e 1)) (φ k₀ (e 0)) (φ k₀ (e 1)) ha
    (fun h => hDet (by linear_combination -h))
  have hL' : ∀ j, T.lineVal e (φ k₀) (a j) ≠ 0 := hL
  have hx' : algebraMap Ω Φ (x i) ≠ 0 := (map_ne_zero _).2 hi
  have hδ' : algebraMap Ω Φ (δ l₀) ≠ 0 := (map_ne_zero _).2 hδ
  let F := chartFunField x i
  let f : F →+* Φ := (algebraMap Ω Φ).comp F.subtype
  let z : Fin 2 → Φ := fun j => T.lineVal e (φ k₁) (a j) / T.lineVal e (φ k₀) (a j)
  let zΔ : Fin 2 → Φ := fun _ => z 0

  have hindF : ∀ Q : MvPolynomial (Fin 2) F, eval₂ f z Q = 0 → Q = 0 := by
    intro Q hQ
    have h1 : aeval z (map F.subtype Q) = 0 := by
      rw [aeval_def, eval₂_map]
      exact hQ
    have h2 : map F.subtype Q = 0 :=
      algebraicIndependent_iff_injective_aeval.mp hind (h1.trans (map_zero _).symm)
    exact map_injective _ (fun u v h => Subtype.ext h) (h2.trans (map_zero _).symm)
  let xb : ι → F := fun j => ⟨x j / x i, Subfield.subset_closure ⟨j, rfl⟩⟩
  let ε : ν → F := fun l => ⟨δ l / δ l₀, hε l⟩
  let C₀ : κ → F := fun k => ⟨c₀ k, hc₀ k⟩
  let C₁ : κ → F := fun k => ⟨c₁ k, hc₁ k⟩

  have hev : ∀ (b₀ b₁ : Φ) (w : Fin 2 → Φ), T.lineVal e (φ k₀) b₀ ≠ 0 → T.lineVal e (φ k₀) b₁ ≠ 0 →
      w 0 = T.lineVal e (φ k₁) b₀ / T.lineVal e (φ k₀) b₀ →
      w 1 = T.lineVal e (φ k₁) b₁ / T.lineVal e (φ k₀) b₁ →
      aeval (T.wwCoord x δ e φ b₀ b₁) d = (∏ k, blockScale (algebraMap Ω Φ (x i)) (algebraMap Ω Φ (δ l₀))
        (T.lineVal e (φ k₀) b₀) (T.lineVal e (φ k₀) b₁) k ^ α k) * eval₂ f w (aeval (ratioPoly xb ε C₀ C₁) d) := by
    intro b₀ b₁ w h₀ h₁ hw₀ hw₁
    rw [wwCoord_eq x δ e φ F i l₀ k₀ k₁ hi hδ xb ε C₀ C₁ (fun _ => rfl) (fun _ => rfl) hc b₀ b₁ w h₀ h₁ hw₀ hw₁]
    exact (aeval_scale _ (fun p => eval₂ f w (ratioPoly xb ε C₀ C₁ p)) d α hd).trans (by rw [aeval_comp_eval₂])
  have hc1 := hev (a 0) (a 1) z (hL' 0) (hL' 1) rfl rfl
  have hcΔ := hev (a 0) (a 0) zΔ (hL' 0) (hL' 0) rfl rfl
  have hU : ∀ u₀ u₁ : Φ, u₀ ≠ 0 → u₁ ≠ 0 →
      (∏ k, blockScale (algebraMap Ω Φ (x i)) (algebraMap Ω Φ (δ l₀)) u₀ u₁ k ^ α k) ≠ 0 := by
    intro u₀ u₁ h₀ h₁
    refine Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ ?_
    cases k <;> assumption
  have h0 : aeval (T.wwCoord x δ e φ (a 0) (a 0)) d = 0 := by
    by_contra h
    exact (DiagRAux.not_mem_ker_iff_aeval_ne _ d α hd).2 h hdΔ

  have hPΔ : eval₂ f zΔ (aeval (ratioPoly xb ε C₀ C₁) d) = 0 := by
    rw [hcΔ] at h0
    exact (mul_eq_zero.1 h0).resolve_left (hU _ _ (hL' 0) (hL' 0))
  have hP₀ : aeval (fun _ : Fin 2 => (X 0 : MvPolynomial (Fin 2) F)) (aeval (ratioPoly xb ε C₀ C₁) d) = 0 := by
    apply hindF
    rw [aeval_eq_bind₁, ← coe_eval₂Hom, eval₂Hom_bind₁]
    simp only [coe_eval₂Hom, eval₂_X]
    exact hPΔ
  obtain ⟨G, hGP⟩ := X_sub_X_dvd (aeval (ratioPoly xb ε C₀ C₁) d)
  rw [hP₀, sub_zero] at hGP
  have hPz : eval₂ f z (aeval (ratioPoly xb ε C₀ C₁) d) = (z 1 - z 0) * eval₂ f z G := by
    rw [hGP]
    simp

  have htD : T.diagSec a * algebraMap Ω Φ (φ k₀ (e 0) * φ k₁ (e 1) - φ k₁ (e 0) * φ k₀ (e 1)) =
      (z 1 - z 0) * (T.lineVal e (φ k₀) (a 0) * T.lineVal e (φ k₀) (a 1)) := by
    have h0' := hL' 0
    have h1' := hL' 1
    simp only [z]
    field_simp
    simp only [T.diagSec, T.lineVal, map_sub, map_mul]
    ring
  have hκx : algebraMap Ω Φ ((φ k₀ (e 0) * φ k₁ (e 1) - φ k₁ (e 0) * φ k₀ (e 1)) * δ l₀ / x i ^ 3) *
      algebraMap Ω Φ (x i) ^ 3 =
      algebraMap Ω Φ (φ k₀ (e 0) * φ k₁ (e 1) - φ k₁ (e 0) * φ k₀ (e 1)) * algebraMap Ω Φ (δ l₀) := by
    rw [← map_pow, ← map_mul, ← map_mul]
    congr 1
    field_simp

  have hsub : Subring.closure (Set.range fun j => x j / x i) ≤
      (fracPairs (T.wwCoord x δ e φ (a 0) (a 1)) (T.wwCoord x δ e φ (a 0) (a 0))).comap
        (RingHom.prod (algebraMap Ω Φ) (algebraMap Ω Φ)) := by
    rw [Subring.closure_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, Subring.mem_comap]
    refine ⟨Pi.single T.WBlk.base 1, X ⟨.base, j⟩, X ⟨.base, i⟩, exHomog_X _ _, exHomog_X _ _, ?_, ?_, ?_, ?_⟩
    · simpa [T.wwCoord] using hx'
    · simpa [T.wwCoord] using hx'
    · simp only [aeval_X, T.wwCoord, RingHom.prod_apply, map_div₀]
      field_simp
    · simp only [aeval_X, T.wwCoord, RingHom.prod_apply, map_div₀]
      field_simp
  have hFmem : ∀ y : F, (f y, f y) ∈ fracPairs (T.wwCoord x δ e φ (a 0) (a 1)) (T.wwCoord x δ e φ (a 0) (a 0)) := by
    intro y
    obtain ⟨p, hp, p', hp', hy⟩ := Subfield.mem_closure_iff.1 y.2
    have h1 := hsub hp
    have h2 := hsub hp'
    rw [Subring.mem_comap, RingHom.prod_apply] at h1 h2
    have hfy : f y = algebraMap Ω Φ p / algebraMap Ω Φ p' := by
      rw [← map_div₀, hy]
      rfl
    rw [hfy]
    by_cases hp0 : p' = 0
    · rw [hp0, map_zero, div_zero]
      exact zero_mem _
    · exact fracPairs_div h1 h2 ((map_ne_zero _).2 hp0)
  obtain ⟨hz0, hz1⟩ := line_mem_fracPairs x δ e φ k₀ k₁ (a 0) (a 1) (hL' 0) (hL' 1)
  have hzmem : ∀ j, (z j, zΔ j) ∈ fracPairs (T.wwCoord x δ e φ (a 0) (a 1)) (T.wwCoord x δ e φ (a 0) (a 0)) := by
    intro j
    fin_cases j
    exacts [hz0, hz1]
  have hGmem := eval₂_mem_fracPairs f hFmem z zΔ hzmem G
  have hκmem := hFmem ⟨_, hκ⟩
  obtain ⟨γ', r', q', hr', hq', -, hq'Δ, e', -⟩ := mul_mem hκmem hGmem
  have hfκ : f ⟨_, hκ⟩ = algebraMap Ω Φ ((φ k₀ (e 0) * φ k₁ (e 1) - φ k₁ (e 0) * φ k₀ (e 1)) * δ l₀ / x i ^ 3) :=
    rfl
  rw [Prod.fst_mul, hfκ] at e'

  have hs := exHomog_mul hq' (homog_monomial i l₀ k₀ 0 1 1 1)
  have hr := exHomog_mul hr' (homog_monomial i l₀ k₀ (α .base + 3) (α .det) (α .line0) (α .line1))
  refine ⟨_, _, _, _, hs, hr, ?_, ?_, ?_⟩
  · intro k
    cases k <;> simp only [Pi.add_apply, blockScale, T.wwDeg] <;> omega
  · rw [T.wwIdeal, DiagRAux.not_mem_ker_iff_aeval_ne _ _ _ hs]
    simp only [map_mul, aeval_X, T.wwCoord, pow_zero, pow_one, one_mul]
    exact mul_ne_zero hq'Δ (mul_ne_zero (mul_ne_zero hδ' (hL' 0)) (hL' 0))
  · rw [hc1, hPz]
    simp only [map_mul, map_pow, aeval_X, T.wwCoord, prod_wblk, blockScale, pow_zero, pow_one, one_mul]
    rw [e']
    linear_combination (-(algebraMap Ω Φ (x i) ^ α .base * algebraMap Ω Φ (δ l₀) ^ α .det *
        T.lineVal e (φ k₀) (a 0) ^ α .line0 * T.lineVal e (φ k₀) (a 1) ^ α .line1 * eval₂ f z G *
        aeval (T.wwCoord x δ e φ (a 0) (a 1)) q' * algebraMap Ω Φ (δ l₀))) * htD +
      (-(T.diagSec a * aeval (T.wwCoord x δ e φ (a 0) (a 1)) q' * eval₂ f z G *
        (algebraMap Ω Φ (x i) ^ α .base * algebraMap Ω Φ (δ l₀) ^ α .det *
        T.lineVal e (φ k₀) (a 0) ^ α .line0 * T.lineVal e (φ k₀) (a 1) ^ α .line1))) * hκx

end

end GroundTheory.Heights₂.Heights.Inter
