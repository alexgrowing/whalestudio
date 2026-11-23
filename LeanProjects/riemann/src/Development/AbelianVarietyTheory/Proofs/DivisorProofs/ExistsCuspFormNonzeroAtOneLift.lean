import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import Development.AbelianVarietyTheory.Definitions.UpperBounds.FreeBallIffOfDimXEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUpperLevelSubgroupComponentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UpperLevelIsUnitaryStabiliserBothLatticesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTotallySplitPrimeUpperLevelUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UpperLevelTrivialDefiniteNoContractionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetPowerSectionNeZeroDefiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeBallNoContractionUnitaryUpperLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitInterpolationDetWeightFreeBallIndefiniteStatement

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.LiftInterp

theorem zero_mem_SS {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) : (0 : Frame X.Ψ r → ℂ) ∈ X.SS la := by
  obtain ⟨⟨hz, -, -⟩, -⟩ := siegelSpaceAlgebra_holds r X la la 0
  exact hz

theorem bchar_ne_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Ψ : Finset (E →+* ℂ)}
    (la : Wt Ψ r) {b : Frame Ψ r} (hb : b ∈ Bor Ψ r) : bchar la b ≠ 0 := by
  classical
  unfold bchar
  refine Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ ?_
  intro h0
  apply (hb τ).1
  have hU : (mat b τ).IsUpperTriangular := fun a c hca => (hb τ).2 a c hca
  rw [Matrix.det_of_upperTriangular hU]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simpa [mat] using h0)

theorem comp_interp {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : DataX E r)
    (hχ : ∀ la, ∀ γ ∈ X.Γ, X.χ la γ = 1) (G : Subgroup (GL (Fin r) E)) (g : ℕ)
    (hg : GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsTotallySplitPrime E g) (hgr : 3 * r < g) (hΓG : X.Γ ≤ G)
    (hL' : ∀ γ ∈ G, IsUStab X.Gm X.L' γ) (hΛ : ∀ γ ∈ G, IsUStab X.Gm X.Λ γ)
    (hU : ∀ γ ∈ G, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsUnipotentModOver X.L' g γ) (s : ℕ) (hs : Even s)
    (hsb : 2 * r + 50 * r ^ 2 * (X.Ψ.card * (X.p0 * (r - X.p0))) + 1 ≤ s)
    (x : Frame X.Ψ r) (hx : x ∈ X.dom) (hNC : GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.NoContraction X x) :
    ∃ P ∈ X.SS (deMul X.Ψ r X.p0 s), P x ≠ 0 ∧ ∀ γ ∈ G, γ ∉ X.Γ → P (lact γ x) = 0 := by
  by_cases hdef : X.p0 = 0 ∨ X.p0 = r
  · have h1 := GlobalTheory.T.upperLevel_trivial_definite_noContraction E r X G g hg hgr hL' hU hdef x hx hNC
    obtain ⟨P, hP, hP0⟩ := GlobalTheory.T.exists_detPowerSection_ne_zero_definite E r X.toData (fun γ hγ => h1 γ (hΓG hγ)) hdef s x hx
    refine ⟨P, hP, hP0, fun γ hγ hγ' => absurd ?_ hγ'⟩
    rw [h1 γ hγ]
    exact X.Γ.one_mem
  · push_neg at hdef
    have hp0 : 0 < X.p0 := Nat.pos_of_ne_zero hdef.1
    have hp1 : X.p0 < r := lt_of_le_of_ne X.p0_le hdef.2
    obtain ⟨x0, h0, ⟨b, hb, rfl⟩, hFB⟩ := GlobalTheory.T.freeBall_noContraction_unitaryUpperLevel E r X G g hg hgr hΓG hL' hΛ hU x hx hNC
    obtain ⟨P, hP, hP0, hPγ⟩ := GlobalTheory.T.orbitInterpolation_detWeight_freeBall_indefinite E r X.toData hχ G x0 h0 hFB hp0 hp1 s hs hsb
    have hx0 : x0 ∈ X.dom := IW.orth_mem_dom X.toData x0 h0
    refine ⟨P, hP, ?_, fun γ hγ hγ' => ?_⟩
    · rw [hP.1.1.2.1 x0 hx0 b hb]
      exact mul_ne_zero (bchar_ne_zero _ hb) hP0
    · have hy : lact γ x0 ∈ X.dom := GlobalTheory.MajInv.lact_mem_dom X.toData (hΛ γ hγ) hx0
      rw [FundSetPf.lact_rmul, hP.1.1.2.1 _ hy b hb, hPγ γ hγ hγ', mul_zero]

theorem castFrame_symm_cast {E : Type} [Field E] {r : ℕ} {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ')
    (y : Frame Ψ r) : castFrame h.symm (castFrame h y) = y := by
  subst h; rfl

theorem castFrame_lact {E : Type} [Field E] {r : ℕ} {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ')
    (γ : GL (Fin r) E) (y : Frame Ψ r) : castFrame h (lact γ y) = lact γ (castFrame h y) := by
  subst h; rfl

theorem castFrame_mem_GG {E : Type} [Field E] {r : ℕ} {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ')
    (G : Matrix (Fin r) (Fin r) E) (p : ℕ) (y : Frame Ψ' r) (hy : y ∈ GG Ψ' G p) :
    castFrame h.symm y ∈ GG Ψ G p := by
  subst h; exact hy

theorem castWt_deMul {E : Type} [Field E] {r : ℕ} {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') (p s : ℕ) :
    castWt h (deMul Ψ' r p s) = deMul Ψ r p s := by
  subst h; rfl

theorem exists_form_one_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [Finite U] [Finite C] [MulAction U C] (M : TwoLevels E r U C), LevelHyp M → ∀ s : ℕ, Even s → 2 * r + 50 * r ^ 2 * M.dimX + 1 ≤ s → ∀ (c : C) (x : Frame M.Ψ r), GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.NoContraction (M.comp c) (castFrame (M.comp_Ψ c).symm x) → x ∈ M.dom → ∃ u ∈ M.SS (deMul M.Ψ r M.p0 s), u c x ≠ 0 ∧ (∀ h : U, h ≠ 1 → M.pull h u c x = 0) ∧ ∀ c', (∀ h : U, h • c ≠ c') → ∀ y, u c' y = 0 := by
  intro E _ _ _ r U C _ _ _ _ M hLH s hs hsb c x hNC hx
  classical
  obtain ⟨g, hg, hgr, hUn⟩ := GlobalTheory.T.exists_totallySplitPrime_upperLevel_unipotent E r U C M hLH
  obtain ⟨G, hG, hΓG⟩ := GlobalTheory.T.exists_upperLevel_subgroup_component E r U C M c
  have hΨ : (M.comp c).Ψ = M.Ψ := M.comp_Ψ c
  have hx' : castFrame hΨ.symm x ∈ (M.comp c).dom := by
    have := castFrame_mem_GG hΨ M.Gm M.p0 x hx
    show castFrame hΨ.symm x ∈ GG (M.comp c).Ψ (M.comp c).Gm (M.comp c).p0
    rw [M.comp_Gm c, M.comp_basePoint c]
    exact this
  have hsb' : 2 * r + 50 * r ^ 2 * ((M.comp c).Ψ.card * ((M.comp c).p0 * (r - (M.comp c).p0))) + 1 ≤ s := by
    rw [hΨ, M.comp_basePoint c]; exact hsb
  obtain ⟨P, hP, hP0, hPγ⟩ := comp_interp (M.comp c) (M.χ_one c) G g hg hgr hΓG
    (fun β hβ => (GlobalTheory.T.upperLevel_isUnitaryStabiliser_both_lattices E r U C M c β ((hG β).1 hβ)).1) (fun β hβ => (GlobalTheory.T.upperLevel_isUnitaryStabiliser_both_lattices E r U C M c β ((hG β).1 hβ)).2)
    (fun β hβ => hUn c β ((hG β).1 hβ)) s hs hsb' _ hx' hNC
  let u : C → Frame M.Ψ r → ℂ := fun c' y => if c' = c then P (castFrame hΨ.symm y) else 0
  refine ⟨u, ?_, ?_, ?_, ?_⟩
  · intro c'
    by_cases hc : c' = c
    · subst hc
      have e : (fun y => u c' (castFrame (M.comp_Ψ c') y)) = P := by
        funext y
        simp only [u, if_pos rfl]
        exact congrArg P (castFrame_symm_cast _ y)
      rw [e, castWt_deMul]
      rw [M.comp_basePoint c'] at hP
      exact hP
    · have e : (fun y => u c' (castFrame (M.comp_Ψ c') y)) = 0 := by
        funext y
        simp [u, hc]
      rw [e]
      exact zero_mem_SS _ _
  · simpa [u] using hP0
  · intro h hh
    unfold TwoLevels.pull
    by_cases hc : h • c = c
    · simp only [u, hc, if_pos rfl]
      rw [castFrame_lact]
      refine hPγ _ ((hG _).2 ⟨h, hc, 1, (M.comp c).Γ.one_mem, by simp⟩) fun hm => hh ?_
      exact M.tr_faithful h c hc hm
    · simp [u, hc]
  · intro c' hc' y
    have hne : c' ≠ c := fun e => hc' 1 (by simp [e])
    simp [u, hne]

end GlobalTheory.LiftInterp
