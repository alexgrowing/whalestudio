import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCutChartSection
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutTools
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace SegreFlagCutLiesOverProof

variable {κ : Type} [Fintype κ] [DecidableEq κ] {ικ : κ → Type} [∀ o, Fintype (ικ o)] {O : Type} [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] {Φ : Type} [Field Φ] [Algebra O Φ]

theorem le_comap_of_chart (pt : (Σ o, ικ o) → Φ) {A F : Type*} [CommRing A] [FunLike F A (MRing ικ O)]
    [RingHomClass F A (MRing ικ O)] (ρ : F) (Q : Ideal A) (u : MRing ικ O) (τ : Φ) {cs ch dl dm : κ → ℕ}
    {s h l μ : MRing ικ O} (hs : IsMultiHomog s cs) (hh : IsMultiHomog h ch) (hl : IsMultiHomog l dl)
    (hμ : IsMultiHomog μ dm) (hdeg : cs + dm = dl + ch) (hsP : s ∉ pointIdeal O pt)
    (hhP : h ∉ pointIdeal O pt) (hsv : aeval pt s = τ * aeval pt h) (hlv : aeval pt l = τ * aeval pt μ)
    (hsat : ∀ q ∈ Q, ∃ n : ℕ, u ^ n * ρ q ∈ pointIdeal O pt ⊔ Ideal.span {l})
    {W : Ideal (MRing ικ O)} (hμW : μ ∉ W) (huW : ∀ n : ℕ, u ^ n ∉ W)
    (hPW : pointIdeal O pt ≤ W) (hW : ratDiv (pointIdeal O pt) s h W ≠ 0) : Q ≤ W.comap ρ := by
  have : (pointIdeal O pt).IsPrime := RingHom.ker_isPrime _
  have hμP : μ ∉ pointIdeal O pt := fun h' => hμW (hPW h')
  have hsv0 : aeval pt s ≠ 0 := fun h0 => hsP (GenericProjClosureDivisor.mem_of_homog hs h0)
  have hτ : τ ≠ 0 := by
    rintro rfl
    exact hsv0 (by rw [hsv, zero_mul])
  have hμv : aeval pt μ ≠ 0 := fun h0 => hμP (GenericProjClosureDivisor.mem_of_homog hμ h0)
  have hlP : l ∉ pointIdeal O pt := fun h' =>
    mul_ne_zero hτ hμv (hlv ▸ GenericProjClosureDivisor.aeval_eq_zero_of_mem h')
  have hdiff : s * μ - l * h ∈ pointIdeal O pt := by
    have h2 := hl.mul hh
    rw [← hdeg] at h2
    have h1 : IsMultiHomog (s * μ - l * h) (cs + dm) :=
      (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.sub_mem _
        ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr (hs.mul hμ))
        ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr h2))
    refine GenericProjClosureDivisor.mem_of_homog h1 ?_
    rw [map_sub, map_mul, map_mul, hsv, hlv]
    ring
  have hrat := congrFun (ratDiv_eq_of_sub_mem hsP hhP hlP hμP hdiff) W
  have hμ0 : divCycle (pointIdeal O pt) μ W = 0 := by
    unfold divCycle
    rw [dif_neg]
    rintro ⟨h', -⟩
    exact hμW (h'.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self μ)))
  have hl0 : divCycle (pointIdeal O pt) l W ≠ 0 := by
    rw [hrat] at hW
    unfold ratDiv at hW
    rwa [hμ0, sub_zero] at hW
  have hmin : W ∈ (pointIdeal O pt ⊔ Ideal.span {l}).minimalPrimes := by
    unfold divCycle at hl0
    split_ifs at hl0 with h'
    · exact h'.1
    · exact absurd rfl hl0
  have hWp : W.IsPrime := hmin.1.1
  intro q hq
  obtain ⟨n, hn⟩ := hsat q hq
  exact (hWp.mem_or_mem (hmin.1.2 hn)).resolve_left (huW n)

omit [Fintype κ] [DecidableEq κ] [∀ o, Fintype (ικ o)] [IsDomain O] [IsDiscreteValuationRing O] in

theorem support_ratDiv {P W : Ideal (MRing ικ O)} {s h : MRing ικ O} (hW : ratDiv P s h W ≠ 0) :
    W.IsPrime ∧ P ≤ W ∧ IsRelevant W := by
  have key : ∀ v, divCycle P v W ≠ 0 → W.IsPrime ∧ P ≤ W ∧ IsRelevant W := by
    intro v hv
    unfold divCycle at hv
    split_ifs at hv with h'
    · exact ⟨h'.1.1.1, le_sup_left.trans h'.1.1.2, h'.2⟩
    · exact absurd rfl hv
  by_cases h1 : divCycle P s W = 0
  · exact key h fun h2 => hW (by simp [ratDiv, h1, h2])
  · exact key s h1

end SegreFlagCutLiesOverProof

open SegreFlagCutLiesOverProof in

theorem SegreFlagCutLiesOver.proof (hChart : SegreFlagCutChartSection.Statement) :
    SegreFlagCutLiesOver.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hBB' w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
    Φ _ _ _ _ e t ht k hk
  have hchart : ∀ (s h : MRing (bundleIdx (bundleIdx ι M) M') O) (W : Ideal (MRing (bundleIdx (bundleIdx ι M) M') O)),
      ratDiv (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))) s h W ≠ 0 →
      ∃ c : ∀ j, ι j, segreVec y c ≠ 0 ∧ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) ≤ W ∧
        ∀ m : K → ℕ, (∏ j, (X ⟨some (some j), c j⟩ : MRing (bundleIdx (bundleIdx ι M) M') O) ^ m j) ∉ W := by
    intro s h W hW
    obtain ⟨hWp, hPW, hWr⟩ := support_ratDiv hW
    choose c hc using fun j : K => hWr (some (some j))
    refine ⟨c, ?_, hPW, ?_⟩
    · unfold segreVec
      rw [Finset.prod_ne_zero_iff]
      intro j _ hj
      apply hc j (hPW ?_)
      refine GenericProjClosureDivisor.mem_of_homog (isWeightedHomogeneous_X O _ _) ?_
      rw [aeval_X]
      simp [flagClosurePt, pairProjCoord, projCoord, hj]
    · intro m hm
      obtain ⟨j, -, hj⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hWp)).mp hm
      exact hc j (hWp.mem_of_pow_mem _ hj)
  have hdeg : ∀ {cs ch dl dm : Option (Option K) → ℕ} {D : Option (Option K) → ℤ},
      (fun o => (cs o : ℤ) - ch o) = D → (fun o => (dl o : ℤ) - dm o) = D → cs + dm = dl + ch := by
    intro cs ch dl dm D h1 h2
    funext o
    have e1 := congrFun h1 o
    have e2 := congrFun h2 o
    simp only [Pi.add_apply] at e1 e2 ⊢
    omega
  refine ⟨fun cs ch s h hs hh hsh hsP hhP hsv W _ hW => ?_, fun cs ch s h hs hh hsh hsP hhP hsv W _ hW => ?_⟩
  · obtain ⟨c, hc, hPW, hmono⟩ := hchart s h W hW
    obtain ⟨⟨dl, dm, l, μ, m, hμ, hl, hμh, hdl, hlv, hsat⟩, -⟩ :=
      hChart O ϖ hϖ Ω K ι y d hV N E B B' hBB' w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk c hc
    exact le_comap_of_chart _ _ _ _ _ hs hh hl hμh (hdeg hsh hdl) hsP hhP hsv hlv hsat (hμ ▸ hmono m)
      (fun n => by rw [← Finset.prod_pow]; exact hmono fun _ => n) hPW hW
  · obtain ⟨c, hc, hPW, hmono⟩ := hchart s h W hW
    obtain ⟨-, ⟨dl, dm, l, μ, m, hμ, hl, hμh, hdl, hlv, hsat⟩⟩ :=
      hChart O ϖ hϖ Ω K ι y d hV N E B B' hBB' w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk c hc
    exact le_comap_of_chart _ _ _ _ _ hs hh hl hμh (hdeg hsh hdl) hsP hhP hsv hlv hsat (hμ ▸ hmono m)
      (fun n => by rw [← Finset.prod_pow]; exact hmono fun _ => n) hPW hW

end

end GroundTheory.Heights₂.Heights.NumbersDVR
