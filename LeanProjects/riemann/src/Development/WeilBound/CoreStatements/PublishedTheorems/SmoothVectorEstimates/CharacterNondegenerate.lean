import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace CharacterNondegenerate

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def chi (ψ : AddChar (Ad E) ℂ) : AddChar (Cinf E) ℂ := ψ.compAddMonoidHom (sInf E).toAddMonoidHom

theorem chi_apply (ψ : AddChar (Ad E) ℂ) (z : Cinf E) : chi ψ z = ψ (sInf E z) := rfl

theorem pInf_sInf (z : Cinf E) : pInf E (sInf E z) = z := (infEq E).symm_apply_apply z

theorem pFin_sInf (z : Cinf E) : pFin E (sInf E z) = 0 := rfl

theorem sInf_mul (z : Cinf E) (x : Ad E) : sInf E z * x = sInf E (z * pInf E x) := by
  refine ad_ext ?_ ?_
  · rw [map_mul, pInf_sInf, pInf_sInf]
  · rw [map_mul, pFin_sInf, pFin_sInf, zero_mul]

theorem continuous_sInf : Continuous (sInf E) :=
  ((continuous_infEq E).prodMk continuous_const :
    Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))

omit [IsTotallyComplex E] in
theorem nonempty_pl : Nonempty (Pl E) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 E)
  exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField E)⟩⟩

theorem continuous_chi {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) : Continuous (chi ψ) :=
  hψ.cont.comp continuous_sInf

theorem chi_nondeg {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (z : Cinf E) (hz : ∀ w, chi ψ (z * w) = 1) : z = 0 := by
  obtain ⟨d, hd⟩ := hψ.ann (sInf E z) fun c => by rw [sInf_mul]; exact hz _
  have hd0 : d = 0 := by
    by_contra h0
    obtain ⟨w⟩ := nonempty_pl (E := E)
    have h1 : sInf E z * algebraMap E (Ad E) d⁻¹ = 1 := by
      rw [hd, ← map_mul, mul_inv_cancel₀ h0, map_one]
    have h2 := congrArg (fun x => pLoc E w (pFin E x)) h1
    simp only [map_mul, pFin_sInf, zero_mul, map_zero, map_one] at h2
    exact zero_ne_one h2
  rw [← pInf_sInf z, hd, hd0, map_zero, map_zero]

theorem sInf_lastE (k : ℕ) (y : UnipotentBlockColumnIndex a k k → Cinf E) :
    sInf E (lastE k y) = lastE k (fun t => sInf E (y t)) := by
  simp only [lastE, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs <;> simp

theorem polyBd : PolyBd (repI E a) := ⟨1, 0, zero_le_one, fun g x => by
  show ‖Rt E a (infGL E a g) x‖ ≤ 1 * _ ^ 0 * ‖x‖
  rw [pow_zero, mul_one, one_mul, norm_Rt]⟩

end CharacterNondegenerate

open CharacterNondegenerate in
theorem whittaker_nondegenerate_character : S7 → MirabolicColumnBlock → G0 → G5 → G6 := by
  intro hS7 hS10 hG0 hG5 E _ _ _ a ψ hψ S Y Y' hY hY' n m hn hSt
  obtain ⟨φ, hφY, φ', hφY', hsm, hsm', hlev, hlev', hW1, hWeq⟩ := hSt
  obtain ⟨hcI, hcLI, hcIf, -, -, -, hcomm, -, hb, -⟩ := hG0 E a
  obtain ⟨hΛ, hRt, hGood, hlaw⟩ := hG5 E a ψ hψ
  obtain ⟨hdec, -, -, hBlk1, -⟩ := hS10 (Cinf E) a (n + 1)
  obtain ⟨η, r, hη1, hr1, hmir, -, -, hv⟩ := hS7 (InfinitePlace E) a (XB E a) (repI E a) polyBd n hn (chi ψ)
    (continuous_chi hψ) (fun z => hψ.norm _) (chi_nondeg hψ) Set.univ Filter.univ_mem
  have memY : ∀ Z : Submodule ℂ (XB E a), YOK ψ S Z → ∀ g, ∀ x ∈ Z, repI E a g x ∈ Z :=
    fun Z hZ g x hx => hZ.stable _ (fun w _ => hcLI w g) x hx
  have whB : ∀ x : XB E a, Good ψ (a - 1) x → ∀ (y : UnipotentBlockColumnIndex a (n + 1) (n + 1) → Cinf E) (g : GA E a),
      Wh ψ x (infGL E a (blkU y) * g) = chi ψ (lastE (n + 1) y) * Wh ψ x g := by
    intro x hx y g
    rw [hb, chi_apply, sInf_lastE]
    exact (hlaw x hx).2.2 (n + 1) n.succ_pos _ g
  have lawOf : ∀ Z : Submodule ℂ (XB E a), YOK ψ S Z → ∀ g' : GA E a, cInf g' = 1 →
      ∀ Λ : XB E a →L[ℂ] ℂ, (∀ x : XB E a, Good ψ (a - 1) x → Λ x = Wh ψ x g') →
      ∀ x ∈ Z, ∀ y : UnipotentBlockColumnIndex a (n + 1) (n + 1) → Cinf E,
        Λ (repI E a (blkU y) x) = chi ψ (lastE (n + 1) y) * Λ x := by
    intro Z hZ g' hg' Λ hΛg x hx y
    have hx' := hZ.good x hx
    change Λ (Rt E a (infGL E a (blkU y)) x) = _
    rw [hΛg _ (hGood x _ hx'), hΛg x hx', hRt, hcomm g' hg', whB x hx']
  have levOf : ∀ x x' : XB E a, Lev S x → (∀ Z : Submodule ℂ (XB E a), IsClosed (Z : Set (XB E a)) →
      (∀ g, ∀ y ∈ Z, repI E a g y ∈ Z) → x ∈ Z → x' ∈ Z) → Lev S x' := by
    intro x x' hx hZ w hw
    refine Filter.mem_of_superset (hx w hw) fun u hu => ?_
    have hu' : Rt E a (fl a w u) x = x := hu
    let T : XB E a →L[ℂ] XB E a := Rt E a (fl a w u) - ContinuousLinearMap.id ℂ _
    have hmem : ∀ y, T y = 0 ↔ Rt E a (fl a w u) y = y := fun y => by simp [T, sub_eq_zero]
    have hk := hZ _ T.isClosed_ker (fun g y hy => by
        rw [LinearMap.mem_ker] at hy ⊢
        refine (hmem _).2 ?_
        have hy' := (hmem y).1 hy
        change Rt E a (fl a w u) (Rt E a (infGL E a g) y) = Rt E a (infGL E a g) y
        rw [← ContinuousLinearMap.mul_apply, ← map_mul, hcomm _ (hcIf w u), map_mul,
          ContinuousLinearMap.mul_apply, hy'])
      (LinearMap.mem_ker.2 ((hmem x).2 hu'))
    rw [LinearMap.mem_ker] at hk
    exact (hmem x').1 hk
  obtain ⟨v, hvs, hvP⟩ := hv φ hsm
  obtain ⟨v', hvs', hvP'⟩ := hv φ' hsm'
  obtain ⟨hvY, hvΛ⟩ := hvP Y hY.closed (memY Y hY) hφY
  obtain ⟨hvY', hvΛ'⟩ := hvP' Y' hY'.closed (memY Y' hY') hφY'
  have conv : ∀ (g' : GA E a) (Λ : XB E a →L[ℂ] ℂ), (∀ x : XB E a, Good ψ (a - 1) x → Λ x = Wh ψ x g') →
      ∀ x : XB E a, Good ψ (a - 1) x → ∀ k, Λ (repI E a k x) = Wh ψ x (g' * infGL E a k) := by
    intro g' Λ hΛg x hx k
    change Λ (Rt E a (infGL E a k) x) = _
    rw [hΛg _ (hGood x _ hx), hRt]
  have hgY := hY.good
  have hgY' := hY'.good
  refine ⟨v, hvY, v', hvY', hvs, hvs', levOf φ v hlev fun Z hc hs hx => (hvP Z hc hs hx).1,
    levOf φ' v' hlev' fun Z hc hs hx => (hvP' Z hc hs hx).1, ?_, ?_⟩
  · obtain ⟨Λ₁, hΛ₁⟩ := hΛ 1
    have e1 := hvΛ Λ₁ (lawOf Y hY 1 (map_one _) Λ₁ hΛ₁) 1 hBlk1
    rw [conv 1 Λ₁ hΛ₁ v (hgY v hvY), conv 1 Λ₁ hΛ₁ φ (hgY φ hφY), hr1, map_one, one_mul] at e1
    rw [e1]
    exact mul_ne_zero hη1 hW1
  · intro g hg
    obtain ⟨hgI, hgL⟩ := hg
    obtain ⟨y, h, hh, hyh⟩ := hdec (cInf g) hgI
    obtain ⟨g', hg'⟩ : ∃ g' : GA E a, g' = (infGL E a (cInf g))⁻¹ * g := ⟨_, rfl⟩
    have hg'1 : cInf g' = 1 := by rw [hg', map_mul, map_inv, hcI, inv_mul_cancel]
    have hgeq : g = infGL E a (blkU y) * (g' * infGL E a h) := by
      rw [hcomm g' hg'1 h, ← mul_assoc, ← map_mul, ← hyh, hg', mul_inv_cancel_left]
    obtain ⟨Λ, hΛg⟩ := hΛ g'
    have e := hvΛ Λ (lawOf Y hY g' hg'1 Λ hΛg) h hh
    have e' := hvΛ' Λ (lawOf Y' hY' g' hg'1 Λ hΛg) h hh
    rw [conv g' Λ hΛg v (hgY v hvY), conv g' Λ hΛg φ (hgY φ hφY)] at e
    rw [conv g' Λ hΛg v' (hgY' v' hvY'), conv g' Λ hΛg φ' (hgY' φ' hφY')] at e'
    rw [hgeq, whB v (hgY v hvY), whB v' (hgY' v' hvY'), e, e']
    by_cases hη : η h = 0
    · simp [hη]
    · rw [hWeq _ ⟨?_, fun w => ?_⟩]
      · rw [map_mul, hg'1, one_mul, hcI]
        exact hmir h hh hη
      · rw [map_mul, hcLI, mul_one, hg', map_mul, map_inv, hcLI, inv_one, one_mul]
        exact hgL w

end PositivityTheory.jumpWindows

end
