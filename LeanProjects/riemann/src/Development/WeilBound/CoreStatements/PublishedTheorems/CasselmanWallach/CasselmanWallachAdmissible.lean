import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SmoothSeminormAndSobolevBounds
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CasselmanWallachAdm
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CasselmanWallachLift
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsClosedImageOfSobolevLower

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

namespace PositivityTheory.CW

theorem model_of (c1 : C1) (c2a : CardSubmodulesOfIndexLePow) (c2b : CardSubmodulesAndLinearEquivBounds) (c3a : HighestWeightSpaceFinite) (c3b : HighestWeightIntegral) (c3d : KTypesBoundedFinite) :
    AllIrr fun _ ε _ _ _ σ => ∃ E, KDer ε σ E ∧ Mod ε E := by
  intro n ε H _ _ _ σ hU hI
  obtain ⟨E, hE, hgl, hun, hirr⟩ := c1 n ε H σ hU hI
  have hL := c2a n ε H σ hU hI E hE
  exact ⟨E, hE, hgl, hun, hirr, c2b n ε _ E hgl hun hL,
    c3d n ε _ E hgl hun hL (c3a n ε H σ hU hI E hE) (c3b n ε H σ hU hI E hE)⟩

theorem sobBdOn_sub {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mx n → (H →L[ℂ] H)} {E : Type} [AddCommGroup E] [Module ℂ E] {P : H → Prop} {p : ℕ → Seminorm ℂ E}
    {T T' : H →ₗ[ℂ] E} (h : SobBdOn ε σ P p T) (h' : SobBdOn ε σ P p T') : SobBdOn ε σ P p (T - T') := by
  intro i
  obtain ⟨S, C, hS, hC⟩ := h i
  obtain ⟨S', C', hS', hC'⟩ := h' i
  refine ⟨S ++ S', |C| + |C'|, words_append hS hS', fun w hw => ?_⟩
  have e1 := hC w hw
  have e2 := hC' w hw
  rw [LinearMap.sub_apply, sobNorm_append]
  have := map_sub_le_add (p i) (T w) (T' w)
  have a := sobNorm_nonneg σ S w
  have b := sobNorm_nonneg σ S' w
  nlinarith [le_abs_self C, le_abs_self C', abs_nonneg C, abs_nonneg C', mul_nonneg (abs_nonneg C) b,
    mul_nonneg (abs_nonneg C') a, mul_le_mul_of_nonneg_right (le_abs_self C) a,
    mul_le_mul_of_nonneg_right (le_abs_self C') b]

theorem lift_of_steps (hM : MaxPr) (hmod : AllIrr fun _ ε _ _ _ σ => ∃ E, KDer ε σ E ∧ Mod ε E) (c4 : C4) (c5 : C5)
    (c6 : C6) (c7 : C7) (d0 : D0) (d1 : D1) (d2 : D2) (d3 : D3) (d4 : D4) (d5 : D5) :
    GlobalTheory.Published.CasselmanWallachLift := by
  intro n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hπ T₀ hT₀
  have hD := c5 n ε H σ hU hI
  obtain ⟨A, hA, hMod⟩ := hmod n ε H σ hU hI
  have hcore := c7 hM c4 n ε H σ hU hI hD A hA hMod
  obtain ⟨T, hT, hTb⟩ := d2 n ε H σ hU hI E p π dπ hπ hD T₀ (d1 n ε H σ hU hI E p π dπ hπ hcore T₀ hT₀)
  have hGK : IsGKMap ε σ π dπ T :=
    ⟨fun k hk v hv => by rw [hT _ (isKFin_translate hv hk), hT v hv, hT₀.1 k hk v hv],
      fun X hX v hv => by rw [hT _ (hD.2.1 v hv X hX), hT v hv, hT₀.2 X hX v hv]⟩
  have h3 := d3 d0 n ε H σ hU hI E p π dπ hπ hD T hGK hTb
  refine ⟨T, hT, ⟨fun g hg w hw => ?_, hTb⟩, fun T' hT' hG' w hw => ?_⟩
  · obtain ⟨k, hk, X, hX, rfl⟩ := d5 n ε g hg
    have hx : NormedSpace.exp X ∈ UJset ε := by simpa using exp_mem_UJ hX 1
    rw [sigma_mul hU (K_le_UJ hk) hx, (h3 _ (Sm.translate hU hw hx)).1 k hk,
      d4 n ε H σ hU hI E p π dπ hπ (c6 n ε H σ hU hI) T hTb X hX (fun u hu => (h3 u hu).2 X hX) w hw,
      hπ.map_mul k (K_le_UJ hk) _ hx]
    rfl
  · have := d0 n ε H σ hU hI E p π dπ hπ hD (T' - T) (sobBdOn_sub hG'.2 hTb)
      (fun v hv => by rw [LinearMap.sub_apply, hT v hv, hT' v hv, sub_self]) w hw
    rwa [LinearMap.sub_apply, sub_eq_zero] at this

theorem cw_of_steps (hM : MaxPr) (hmod : AllIrr fun _ ε _ _ _ σ => ∃ E, KDer ε σ E ∧ Mod ε E) (c5 : C5) (d0 : D0)
    (hL : GlobalTheory.Published.CasselmanWallachLift) (e1a : SmoothSeminormGrowth) (e1b : faceMap_comp_succAbove_castSucc) (e2a : E2a) (e2b : E2b) (e2c : CasimirPairingBound) (e2d : SobolevBoundedPairing)
    (e3a : CasimirPowerSurjectiveSymmetric) (e3b : faceMap_castSucc_comp_eq_succ) (e3c : SmoothMapSeminormBound) (e3d : SobolevNormDomination) : GlobalTheory.Published.CasselmanWallach := by
  intro n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hπ T₀ hT₀
  have hD := c5 n ε H σ hU hI
  obtain ⟨A, hA, hMod⟩ := hmod n ε H σ hU hI
  obtain ⟨T, hT, hG, hu⟩ := hL n ε H σ hU hI E p π dπ hπ T₀ hT₀
  have hTb : SobBdOn ε σ (Sm ε σ) p T := hG.2
  have hd : ∀ X ∈ lieSet ε, ∀ v, IsKFin ε σ v → T (dRep σ X v) = dπ X (T v) := fun X hX v hv => by
    rw [hT _ (hD.2.1 v hv X hX), hT v hv, hT₀.2 X hX v hv]
  have low : (∃ v, IsKFin ε σ v ∧ T₀ v ≠ 0) → ∀ S : List (List (Mx n)), Words (lieSet ε) S →
      ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ w, Sm ε σ w → sobNorm σ S w ≤ q (T w) := by
    rintro ⟨v₀, hv₀, h0⟩
    rw [← hT v₀ hv₀] at h0
    obtain ⟨i, hi⟩ := hπ.withSeminorms.separating_of_T1 _ h0
    obtain ⟨Q, N, hQ, hQ1, hQ2, hQ3⟩ := e1a n ε H σ hU hI E p π dπ hπ i
    let Q' : Seminorm ℂ (kfin ε σ) := Q.comp (T ∘ₗ (kfin ε σ).subtype)
    have hQ' : ∀ v : kfin ε σ, Q' v = Q (T v) := fun _ => rfl
    have hinv : ∀ k ∈ Kset ε, ∀ v v' : kfin ε σ, (v' : H) = σ k v → Q' v' = Q' v := fun k hk v v' e => by
      rw [hQ', hQ', e, hG.1 k (K_le_UJ hk) _ (hD.1 _ v.2), hQ3 k hk]
    have hdef : ∀ v : kfin ε σ, v ≠ 0 → Q' v ≠ 0 := fun v hv h => by
      obtain ⟨g, hg, h1⟩ := e1b n ε H σ hU hI E p π dπ hπ T hG i v₀ (hD.1 _ hv₀) hi v (hD.1 _ v.2)
        (fun e => hv (Subtype.ext e))
      have := hQ1 g hg (T v)
      rw [← hQ', h, mul_zero] at this
      exact h1 (le_antisymm this (apply_nonneg _ _))
    have hb := e2c n ε _ A hMod.gl hMod.uni hMod Q' fun v hv => by
      obtain ⟨B, b1, b2, b3⟩ := e2b n ε H σ hU hI Q' hinv v (hdef v hv)
      exact ⟨B, e2a n ε H σ hU hI hD A hA B b1, b2, b3⟩
    obtain ⟨q, hq, hq1⟩ := e3c hM e3a e3b n ε H σ hU hI E p π dπ hπ hD A hA hMod T hG hd Q N hQ hQ2 fun η hη => by
      obtain ⟨C, hC, h1⟩ := hb ⟨η, hη⟩
      exact ⟨C, hC, (e2d n ε H σ hU hI E p π dπ hπ hD T hTb Q hQ [] η C (by simp)).1 fun y hy => h1 ⟨y, hy⟩⟩
    exact e3d e2d n ε H σ hU hI E p π dπ hπ hD T hTb hd q hq hq1
  refine ⟨T, hT, hG, hu, ?_, low⟩
  by_cases h0 : ∃ v, IsKFin ε σ v ∧ T₀ v ≠ 0
  · exact GlobalTheory.CompanionTheory.SmoothClosed.isClosed_image_of_sobolev_lower n ε H σ hU hI E p π dπ hπ T hG (low h0)
  · have hz := d0 n ε H σ hU hI E p π dπ hπ hD T hTb fun v hv => by
      rw [hT v hv]
      by_contra h
      exact h0 ⟨v, hv, h⟩
    have : T '' {w | SmoothVec (lieSet ε) σ w} = {0} := by
      refine Set.Subset.antisymm ?_ ?_
      · rintro _ ⟨w, hw, rfl⟩
        exact hz w hw
      · rintro _ rfl
        exact ⟨0, (smooth (Jm ε) σ).zero_mem, map_zero T⟩
    rw [this]
    exact isClosed_singleton

theorem casselman_wallach_admissible (c5 : C5) (h : GlobalTheory.Published.CasselmanWallach) : GlobalTheory.Published.CasselmanWallachAdm := by
  intro n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hπ T₀ hT₀ _
  obtain ⟨T, h1, h2, -, h4, h5⟩ := h n ε H σ hU hI E p π dπ hπ T₀ hT₀
  refine ⟨T, h1, h2, h4, fun hinj S hS => ?_⟩
  by_cases h0 : ∃ v, IsKFin ε σ v ∧ T₀ v ≠ 0
  · exact h5 h0 S hS
  · refine ⟨0, continuous_const, fun w hw => ?_⟩
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    obtain ⟨v, hv, h⟩ := (c5 n ε H σ hU hI).2.2 w hw S hS δ hδ
    have : v = 0 := hinj v hv (by
      by_contra h
      exact h0 ⟨v, hv, h⟩)
    rw [this, sub_zero] at h
    simpa using h.le

end PositivityTheory.CW

end
