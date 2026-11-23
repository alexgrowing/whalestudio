import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.PosOfTorusNoLe
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusNoLeClassNoRankOne

noncomputable section

namespace GlobalTheory.SUVol.TamModel

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.UCls.Model GlobalTheory.SUVol
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Up.Definite
open scoped ENNReal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem sEquiv_refl (G : Matrix (Fin r) (Fin r) E) (L : Set (Fin r → E)) (M : ℕ) (g) : SEquiv G L M g g :=
  ⟨1, by rw [SUVol.ratM_one]; exact ⟨(isKM_one _ G L M).1, det_one⟩, 1, isKM_one _ G L M, det_one, by
    rw [SUVol.ratM_one]; simp⟩

theorem sEquiv_trans {G : Matrix (Fin r) (Fin r) E} {L : Set (Fin r → E)} {M : ℕ} {a b d}
    (h : SEquiv G L M a b) (h' : SEquiv G L M b d) : SEquiv G L M a d := by
  obtain ⟨γ, hγ, k, hk, hd, rfl⟩ := h
  obtain ⟨γ', hγ', k', hk', hd', rfl⟩ := h'
  exact ⟨γ' * γ, by
    rw [SUVol.ratM_mul]; exact ⟨isUA_mul _ G hγ'.1 hγ.1, by rw [det_mul, hγ'.2, hγ.2, one_mul]⟩,
    k * k', isKM_mul _ G L M hk hk', by rw [det_mul, hd, hd', one_mul], by
    rw [SUVol.ratM_mul]; simp only [Matrix.mul_assoc]⟩

theorem sEquiv_symm {G : Matrix (Fin r) (Fin r) E} {L : Set (Fin r → E)} {M : ℕ} {a b}
    (h : SEquiv G L M a b) : SEquiv G L M b a := by
  obtain ⟨γ, hγ, k, hk, hkd, rfl⟩ := h
  have hd1 : γ.det = 1 := by
    have h1 := hγ.2
    rw [ratM_det] at h1
    exact one_tmul_injective (F := maximalRealSubfield E) h1
  have hd : IsUnit γ.det := hd1 ▸ isUnit_one
  have hi : ratM (maximalRealSubfield E) γ⁻¹ * ratM (maximalRealSubfield E) γ = 1 := by
    rw [← SUVol.ratM_mul, nonsing_inv_mul γ hd, SUVol.ratM_one]
  refine ⟨γ⁻¹, ⟨by rw [← inv_eq_left_inv hi]; exact isUA_inv _ G hγ.1, ?_⟩, k⁻¹, isKM_inv _ G L M hk, ?_, ?_⟩
  · have := congrArg det hi
    rwa [det_mul, hγ.2, mul_one, det_one] at this
  · have := congrArg det (nonsing_inv_mul k hk.1.1)
    rwa [det_mul, hkd, mul_one, det_one] at this
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv k hk.1.1, Matrix.mul_one, ← Matrix.mul_assoc, hi,
      Matrix.one_mul]

theorem exists_sReps (G : Matrix (Fin r) (Fin r) E) (L : Set (Fin r → E)) (M : ℕ) :
    ∃ (J : Type) (s : J → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), Nonempty J ∧ IsSReps G L M s := by
  let S : Setoid {g // IsSA G g} :=
    ⟨fun a b => SEquiv G L M a.1 b.1, fun a => sEquiv_refl G L M a.1, sEquiv_symm, sEquiv_trans⟩
  refine ⟨Quotient S, fun q => q.out.1, ⟨Quotient.mk S ⟨1, (isKM_one _ G L M).1, det_one⟩⟩, fun q => q.out.2,
    fun i j h => ?_, fun g hg => ⟨Quotient.mk S ⟨g, hg⟩, Quotient.mk_out (s := S) ⟨g, hg⟩⟩⟩
  rw [← i.out_eq, ← j.out_eq]
  exact Quotient.sound h

theorem not_isSReps_empty (G : Matrix (Fin r) (Fin r) E) (L : Set (Fin r → E)) (M : ℕ)
    (s : Empty → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)) : ¬ IsSReps G L M s := fun h => by
  obtain ⟨j, -⟩ := h.2.2 1 ⟨(isKM_one _ G L M).1, det_one⟩
  exact j.elim

variable (E) in

theorem exists_cmType : ∃ Ψ : Finset (E →+* ℂ), ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ := by
  classical
  refine ⟨Finset.univ.filter fun τ => τ = (InfinitePlace.mk τ).embedding, fun τ => ?_⟩
  have hne : ComplexEmbedding.conjugate τ ≠ τ := fun h =>
    IsTotallyComplex.complexEmbedding_not_isReal τ (ComplexEmbedding.isReal_iff.2 h)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, InfinitePlace.mk_conjugate_eq]
  rcases InfinitePlace.embedding_mk_eq τ with h | h <;> rw [h] <;> simp [hne, hne.symm]

variable (E) in

theorem exists_skew : ∃ δ : E, δ ≠ 0 ∧ IsIntegral ℤ δ ∧ cc δ = -δ := by
  by_contra hcon
  push Not at hcon
  have key : ∀ x : 𝓞 E, cc (x : E) = x := fun x => by
    by_contra hx
    refine hcon ((x : E) - cc (x : E)) (sub_ne_zero.2 (Ne.symm hx)) (x.isIntegral_coe.sub (isIntegral_cc x.isIntegral_coe)) ?_
    simp [cc]
  apply IsCMField.complexConj_ne_one E
  ext y
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) y
  have ha := key a
  have hb' := key b
  simp only [cc] at ha hb'
  simp only [map_div₀, AlgEquiv.one_apply]
  exact congrArg₂ (· / ·) ha hb'

theorem exists_lie_one : ∃ e : Fin (2 ^ 2 - 1) → Matrix (Fin 2) (Fin 2) E,
    (∀ i, e i ∈ lieLat 1 (intVec E 2)) ∧ LinearIndependent (maximalRealSubfield E) e := by
  obtain ⟨δ, h0, hi, hc⟩ := exists_skew E
  simp only [cc] at hc
  let e : Fin 3 → Matrix (Fin 2) (Fin 2) E := ![!![δ, 0; 0, -δ], !![0, 1; -1, 0], !![0, δ; δ, 0]]
  refine ⟨e, fun (i : Fin 3) => ⟨?_, fun x y => ?_, fun x hx => ?_⟩, ?_⟩
  · fin_cases i <;> simp [e, trace_fin_two]
  · fin_cases i <;> simp [e, herm, cc, mulVec, dotProduct, hc, one_apply] <;> ring
  · rw [mem_intVec] at hx ⊢
    intro a
    have h1 := hx 0
    have h2 := hx 1
    have h3 := hi.mul h1
    have h4 := hi.mul h2
    fin_cases i <;> fin_cases a <;> simp [e, mulVec, dotProduct] <;> first | assumption | exact IsIntegral.neg ‹_›
  · change LinearIndependent (maximalRealSubfield E) e
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h1 := congrFun (congrFun hg 0) 0
    have h2 := congrFun (congrFun hg 0) 1
    have h3 := congrFun (congrFun hg 1) 0
    simp [e, Fin.sum_univ_three, Subfield.smul_def, h0] at h1 h2 h3
    have h4 : (g 1 : E) = 0 := by linear_combination (1 / 2 : E) * h2 - (1 / 2 : E) * h3
    have h5 : (g 2 : E) * δ = 0 := by linear_combination (1 / 2 : E) * h2 + (1 / 2 : E) * h3
    intro i
    fin_cases i
    · simpa using h1
    · simpa using h4
    · simpa [h0] using h5

theorem exists_lie_hyp : ∃ e : Fin (2 ^ 2 - 1) → Matrix (Fin 2) (Fin 2) E,
    (∀ i, e i ∈ lieLat !![0, 1; 1, 0] (intVec E 2)) ∧ LinearIndependent (maximalRealSubfield E) e := by
  obtain ⟨δ, h0, hi, hc⟩ := exists_skew E
  simp only [cc] at hc
  let e : Fin 3 → Matrix (Fin 2) (Fin 2) E := ![!![1, 0; 0, -1], !![0, δ; 0, 0], !![0, 0; δ, 0]]
  refine ⟨e, fun (i : Fin 3) => ⟨?_, fun x y => ?_, fun x hx => ?_⟩, ?_⟩
  · fin_cases i <;> simp [e, trace_fin_two]
  · fin_cases i <;> simp [e, herm, cc, mulVec, dotProduct, hc] <;> ring
  · rw [mem_intVec] at hx ⊢
    intro a
    have h1 := hx 0
    have h2 := hx 1
    have h3 := hi.mul h1
    have h4 := hi.mul h2
    fin_cases i <;> fin_cases a <;> simp [e, mulVec, dotProduct] <;>
      first | assumption | exact IsIntegral.neg ‹_› | exact isIntegral_zero
  · change LinearIndependent (maximalRealSubfield E) e
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h1 := congrFun (congrFun hg 0) 0
    have h2 := congrFun (congrFun hg 0) 1
    have h3 := congrFun (congrFun hg 1) 0
    simp [e, Fin.sum_univ_three, Subfield.smul_def, h0] at h1 h2 h3
    intro i
    fin_cases i
    · simpa using h1
    · simpa using h2
    · simpa using h3

theorem joint_hyp : ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E) (Ψ : Finset (E →+* ℂ)),
    Unr E ∧ (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) ∧
    ∀ G : Matrix (Fin 2) (Fin 2) E, G = 1 ∨ G = !![0, 1; 1, 0] →
      ∃ (Λ : Submodule (𝓞 E) (Fin 2 → E)) (e : Fin (2 ^ 2 - 1) → Matrix (Fin 2) (Fin 2) E)
        (J : Type) (s : J → Matrix (Fin 2) (Fin 2) (RA (maximalRealSubfield E) E)),
        SelfDualLat G Λ ∧ (∀ i, e i ∈ lieLat G Λ) ∧ LinearIndependent (maximalRealSubfield E) e ∧
          IsSReps G (Λ : Set (Fin 2 → E)) 1 s := by
  obtain ⟨E, _, _, _, hU, -⟩ := exists_field
  obtain ⟨Ψ, hΨ⟩ := exists_cmType E
  refine ⟨E, inferInstance, inferInstance, inferInstance, Ψ, hU, hΨ, fun G hG => ?_⟩
  obtain ⟨J, s, -, hs⟩ := exists_sReps G (intVec E 2 : Set (Fin 2 → E)) 1
  rcases hG with rfl | rfl
  · obtain ⟨e, h1, h2⟩ := exists_lie_one (E := E)
    exact ⟨_, e, J, s, selfDual_one, h1, h2, hs⟩
  · obtain ⟨e, h1, h2⟩ := exists_lie_hyp (E := E)
    exact ⟨_, e, J, s, selfDual_hyp.1, h1, h2, hs⟩

theorem mem_ratStab_of (G : Matrix (Fin r) (Fin r) E) (L : Set (Fin r → E)) (s k) (γ : GL (Fin r) E)
    (h1 : (γ : Matrix (Fin r) (Fin r) E).det = 1)
    (h2 : ∀ x y, herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) = herm G x y)
    (hk : IsKM (IsCMField.complexConj E) G L 1 k)
    (he : ratM (maximalRealSubfield E) (γ : Matrix (Fin r) (Fin r) E) * s = s * k) : γ ∈ ratStab G L s := by
  refine ⟨h1, h2, fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨z, hz, rfl⟩ := hk.2.2 y hy
    refine ⟨z, hz, ?_⟩
    have hi : ratM (maximalRealSubfield E) ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *
        ratM (maximalRealSubfield E) (γ : Matrix (Fin r) (Fin r) E) = 1 := by
      rw [← SUVol.ratM_mul, Units.inv_mul, SUVol.ratM_one]
    have := congrArg (ratM (maximalRealSubfield E) ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ ·) hxy
    simp only [mulVec_mulVec] at this
    rwa [← he, ← Matrix.mul_assoc, hi, Matrix.one_mul, one_mulVec] at this
  · rintro ⟨y, hy, rfl⟩
    exact ⟨k *ᵥ y, IsKM_maps _ G L 1 hk hy, by rw [mulVec_mulVec, mulVec_mulVec, he]⟩

end GlobalTheory.SUVol.TamModel
