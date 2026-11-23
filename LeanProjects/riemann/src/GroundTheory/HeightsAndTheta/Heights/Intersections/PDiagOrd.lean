import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsDiagDiv
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsDiagOffUnit
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsDiagOrdOne
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsDiagRelevant
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleMul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

namespace DiagonalOrder

section Orders

variable {K : Type} {ι : K → Type}

theorem multAt_eq_zero_of_not_le {J W : Ideal (MRing ι)} (hW : W.IsPrime) (h : ¬ J ≤ W) : multAt J W = 0 := by
  have := hW
  unfold multAt
  rw [dif_pos hW, Module.length_eq_zero_iff.mpr (NumbersDVR.localizedQuot_subsingleton_of_not_le _ W h)]
  rfl

theorem multAt_sup_span_eq {P W : Ideal (MRing ι)} [P.IsPrime] (hW : W.IsPrime) (hPW : P ≤ W)
    {g h u v : MRing ι} (hu : u ∉ W) (hv : v ∉ W) (hm : u * g - v * h ∈ P) :
    multAt (P ⊔ Ideal.span {g}) W = multAt (P ⊔ Ideal.span {h}) W := by
  have := hW
  have hlen : ∀ {s w : MRing ι}, w ∉ W →
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (MRing ι ⧸ (P ⊔ Ideal.span {w * s}))) =
        Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (MRing ι ⧸ (P ⊔ Ideal.span {s}))) := by
    intro s w hw
    rw [NumbersDVR.length_localizedQuot_sup_span_mul P W s (fun h' => hw (hPW h')),
      Module.length_eq_zero_iff.mpr (NumbersDVR.localizedQuot_subsingleton_of_not_le _ W
        (fun hle => hw (hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self w))))), add_zero]
  have heq : P ⊔ Ideal.span {u * g} = P ⊔ Ideal.span {v * h} := by
    apply le_antisymm
    · refine sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
      have e : u * g = (u * g - v * h) + v * h := by ring
      rw [e]
      exact Ideal.add_mem _ (Ideal.mem_sup_left hm) (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    · refine sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
      have e : v * h = u * g - (u * g - v * h) := by ring
      rw [e]
      exact Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)) (Ideal.mem_sup_left hm)
  unfold multAt
  rw [dif_pos hW, dif_pos hW, ← hlen (s := g) hu, heq, hlen hv]

end Orders

section Diagonal

variable {Ω : Type} [Field Ω] {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] {E : Type} [AddCommGroup E]
  [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]

def polyCoord (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) :
    (Σ k, T.wwIdx ι ν κ k) → MvPolynomial (Fin 2) Ω
  | ⟨.base, i⟩ => C (x i)
  | ⟨.det, l⟩ => C (δ l)
  | ⟨.line0, k⟩ => C (φ k (e 0)) + X 0 * C (φ k (e 1))
  | ⟨.line1, k⟩ => C (φ k (e 0)) + X 1 * C (φ k (e 1))

def polyConeMap (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) :
    MRing (T.wwIdx ι ν κ) →+* MvPolynomial T.WBlk (MvPolynomial (Fin 2) Ω) :=
  eval₂Hom (Int.castRingHom _) fun p => C (polyCoord x δ e φ p) * X p.1

omit [Fintype ι] [Fintype ν] [Fintype κ] in

theorem multiConeMap_eq (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω)
    (b : Fin 2 → Φ) :
    T.multiConeMap (T.wwCoord x δ e φ (b 0) (b 1)) =
      (MvPolynomial.map (aeval b : MvPolynomial (Fin 2) Ω →ₐ[Ω] Φ).toRingHom).comp (polyConeMap x δ e φ) := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
  · simp [T.multiConeMap, polyConeMap]
  · rcases p with ⟨_ | _ | _ | _, i⟩ <;>
      simp [T.multiConeMap, polyConeMap, polyCoord, T.wwCoord, T.lineVal, mul_comm]

omit [Fintype ι] [Fintype ν] [Fintype κ] in

theorem wwIdeal_le_diag (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω)
    (a : Fin 2 → Φ) (ha : AlgebraicIndependent Ω a) :
    T.wwIdeal x δ e φ (a 0) (a 1) ≤ T.wwIdeal x δ e φ (a 0) (a 0) := by
  intro s hs
  rw [T.wwIdeal, RingHom.mem_ker, multiConeMap_eq x δ e φ a, RingHom.comp_apply] at hs
  have hinj : Function.Injective (aeval a : MvPolynomial (Fin 2) Ω →ₐ[Ω] Φ).toRingHom :=
    algebraicIndependent_iff_injective_aeval.mp ha
  have hz : polyConeMap x δ e φ s = 0 := MvPolynomial.map_injective _ hinj (hs.trans (map_zero _).symm)
  rw [T.wwIdeal, RingHom.mem_ker, multiConeMap_eq x δ e φ (fun _ => a 0), RingHom.comp_apply, hz, map_zero]

theorem aeval_diag_eq (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω)
    (a₀ a₁ : Φ) {m : ℕ} {h : MRing (T.wwIdx ι ν κ)} (hh : IsMultiHomog h (T.wwDeg m 0)) :
    aeval (T.wwCoord x δ e φ a₀ a₀) h = aeval (T.wwCoord x δ e φ a₀ a₁) h := by
  rw [aeval_def, aeval_def]
  apply eval₂_congr
  intro p c hp hc
  rcases p with ⟨_ | _ | _ | _, i⟩
  · rfl
  · rfl
  · rfl
  · exfalso
    have hs := hh c (mem_support_iff.mpr hc) .line1
    simp only [T.wwDeg] at hs
    exact (Finsupp.mem_support_iff.mp hp) ((Finset.sum_eq_zero_iff.mp hs) i (Finset.mem_univ _))

end Diagonal

end DiagonalOrder

open DiagonalOrder in

theorem DiagOrd.proof (hU : DiagOffUnit.Statement) (hO : DiagOrdOne.Statement) (hR : DiagRelevant.Statement) :
    DiagOrd.Statement := by
  intro Ω _ ι ν κ _ _ _ E _ _ Φ _ _ x B e φ δ hS hG hD hx a ha n g h hg hh hP hq
  have hrel := hR Ω ι ν κ E Φ x B e φ δ hS hG hD hx a ha
  have hone := hO Ω ι ν κ E Φ x B e φ δ hS hG hD hx a ha n g h hg hh hP hq
  have hunit := hU Ω ι ν κ E Φ x B e φ δ hS hG hD hx a ha
  set P := T.wwIdeal x δ e φ (a 0) (a 1) with hPdef
  set Δ := T.wwIdeal x δ e φ (a 0) (a 0) with hΔdef
  have hPp : P.IsPrime := RingHom.ker_isPrime _
  have hΔp : Δ.IsPrime := RingHom.ker_isPrime _
  have hPΔ : P ≤ Δ := wwIdeal_le_diag x δ e φ a ha
  have hhΔ : h ∉ Δ := by
    refine (DiagRAux.not_mem_ker_iff_aeval_ne _ h _ hh).2 ?_
    rw [aeval_diag_eq x δ e φ (a 0) (a 1) hh]
    exact (DiagRAux.not_mem_ker_iff_aeval_ne _ h _ hh).1 hP
  have hgΔ : g ∈ Δ := by
    by_contra hgn
    rw [multAt_eq_zero_of_not_le hΔp (fun hle => hgn (hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self g))))]
      at hone
    exact zero_ne_one hone
  have hJΔ : P ⊔ Ideal.span {g * h} ≤ Δ :=
    sup_le hPΔ ((Ideal.span_singleton_le_iff_mem _).mpr (Δ.mul_mem_right h hgΔ))
  have key : ∀ W : Ideal (MRing (T.wwIdx ι ν κ)), W.IsPrime → IsRelevant W → P ≤ W → ¬ Δ ≤ W →
      ∃ u v, u ∉ W ∧ v ∉ W ∧ u * g - v * h ∈ P := by
    intro W hW hWr hPW hΔW
    obtain ⟨α, β, u, v, hu, hv, hdeg, huW, hvW, huv⟩ := hunit W hW hWr hPW hΔW
    refine ⟨u, v, huW, hvW, ?_⟩
    have hβ : β + T.wwDeg (n + 3) 0 = α + T.wwDeg n 1 := by
      funext k
      have := hdeg k
      cases k <;> simp only [T.wwDeg, Pi.add_apply] at this ⊢ <;> omega
    have hd : IsMultiHomog (u * g - v * h) (α + T.wwDeg n 1) :=
      exHomog_sub (exHomog_mul hu hg) (hβ ▸ exHomog_mul hv hh)
    by_contra hn
    apply (DiagRAux.not_mem_ker_iff_aeval_ne _ _ _ hd).1 hn
    rw [map_sub, map_mul, map_mul, hq, ← huv]
    ring
  refine ⟨⟨⟨⟨hΔp, hJΔ⟩, fun Q hQ hQΔ => ?_⟩, hrel⟩, fun W hW => ?_⟩
  · by_contra hΔQ
    have hPQ : P ≤ Q := le_sup_left.trans hQ.2
    obtain ⟨u, v, huQ, hvQ, hm⟩ :=
      key Q hQ.1 (fun k => (hrel k).imp fun _ hi hq' => hi (hQΔ hq')) hPQ hΔQ
    have hhQ : h ∉ Q := fun hh' => hhΔ (hQΔ hh')
    have hgQ : g ∈ Q :=
      (hQ.1.mem_or_mem (hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))).resolve_right hhQ
    have hvh : v * h ∈ Q := by
      have e : v * h = u * g - (u * g - v * h) := by ring
      rw [e]
      exact Q.sub_mem (Q.mul_mem_left u hgQ) (hPQ hm)
    rcases hQ.1.mem_or_mem hvh with h1 | h1
    exacts [hvQ h1, hhQ h1]
  · have hWp : W.IsPrime := hW.1.1.1
    by_cases hWΔ : W = Δ
    · rw [if_pos hWΔ, hWΔ, hone, multAt_eq_zero_of_not_le hΔp
        (fun hle => hhΔ (hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self h))))]
      norm_num
    · rw [if_neg hWΔ]
      have hPW : P ≤ W := le_sup_left.trans hW.1.1.2
      have hΔW : ¬ Δ ≤ W := fun hle => hWΔ (le_antisymm (hW.1.2 ⟨hΔp, hJΔ⟩ hle) hle)
      obtain ⟨u, v, hu, hv, hm⟩ := key W hWp hW.2 hPW hΔW
      rw [multAt_sup_span_eq hWp hPW hu hv hm]
      simp

end

end GroundTheory.Heights₂.Heights.Inter
