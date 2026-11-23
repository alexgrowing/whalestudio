import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.LatData
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.CommProjectionHolds
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.StatementB

namespace Formalism.InvariantFactorPaths.PW

open Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

noncomputable def polProj (p : ℕ) [Fact p.Prime] (r : ℕ) (L2 : Letters N) :
    MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  weightedHomogeneousComponent (wL N r) (fun i => (L2.deg i : ℤ))

theorem polProj_mem (L2 : Letters N) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    polProj p r L2 x ∈ Pol p r L2 := by
  rw [pol_iff]; exact weightedHomogeneousComponent_isWeightedHomogeneous _ _

theorem polProj_id (L2 : Letters N) {x : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hx : x ∈ Pol p r L2) :
    polProj p r L2 x = x := by
  rw [pol_iff] at hx
  rw [polProj, weightedHomogeneousComponent_of_mem hx, if_pos rfl]

theorem polProj_glAct (LL L2 : Letters N) (j : ℕ) (c d : Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    polProj p r L2 (glAct p LL j c d x) = glAct p LL j c d (polProj p r L2 x) :=
  Formalism.CountingSumsFrames.whc_comm _ _ (fun _ _ hx => glAct_wL LL j c d hx) _ x

theorem isoC_inf_pol_le (LL L2 : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ) :
    IsoC p LL j Cs la ⊓ Pol p r L2 ≤ IsoW (GAe p LL j (enumC Cs)) (Pol p r L2) (la ∘ enumC Cs) := by
  have hle : IsoC p LL j Cs la ≤
      (IsoW (GAe p LL j (enumC Cs)) (Pol p r L2) (la ∘ enumC Cs)).comap (polProj p r L2) := by
    rw [IsoC]
    refine sInf_le ⟨?_, ?_⟩
    · intro x hx
      rw [Submodule.mem_comap]
      refine (GAe p LL j (enumC Cs)).subset_gS _ ⟨?_, polProj_mem L2 x⟩
      exact (hwc_iff LL j Cs la _).mp
        (hwc_map_of_comm LL j Cs _ (fun c _ d _ y => polProj_glAct LL L2 j c d y) la x hx)
    · rw [stableC_iff]
      intro a b x hx
      rw [Submodule.mem_comap] at hx ⊢
      rw [GAe_E, polProj_glAct]
      exact (GAe p LL j (enumC Cs)).gS_stable _ a b _ hx
  intro x hx
  have h := hle hx.1
  rwa [Submodule.mem_comap, polProj_id L2 hx.2] at h

theorem weylLat_self (LL : Letters N) (j : ℕ) (h : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    h ∈ WeylLat p LL j h := by
  rw [WeylLat, Submodule.mem_sInf]
  exact fun L hL => hL.1

theorem weylLat_div (LL : Letters N) (j : ℕ) (h : MvPolynomial (Fin N × Fin r) ℚ_[p]) (c d : Fin r) (hcd : c ≠ d)
    (k : ℕ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hx : x ∈ WeylLat p LL j h) :
    (((k.factorial : ℚ_[p]))⁻¹) • ((glAct p LL j c d) ^ k) x ∈ WeylLat p LL j h := by
  rw [WeylLat, Submodule.mem_sInf] at hx ⊢
  exact fun L hL => hL.2 c d hcd k x (hx L hL)

theorem zpClosed_toAddSubgroup {W : Type} [AddCommGroup W] [Module ℚ_[p] W] [Module ℤ_[p] W]
    [IsScalarTower ℤ_[p] ℚ_[p] W] (L : Submodule ℤ_[p] W) : ZpClosed p L.toAddSubgroup := by
  intro c hc x hx
  rw [Submodule.mem_toAddSubgroup] at hx ⊢
  obtain ⟨a, ha⟩ : ∃ a : ℤ_[p], (a : ℚ_[p]) = c := ⟨⟨c, hc⟩, rfl⟩
  have e : c • x = a • x := by
    rw [← ha]
    exact algebraMap_smul ℚ_[p] a x
  rw [e]
  exact L.smul_mem _ hx

theorem iSup_weylLat_div (LL : Letters N) (j : ℕ) (Q : MvPolynomial (Fin N × Fin r) ℚ_[p] → Prop)
    (c d : Fin r) (hcd : c ≠ d) (k : ℕ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hx : x ∈ ⨆ (h : MvPolynomial (Fin N × Fin r) ℚ_[p]) (_ : Q h), WeylLat p LL j h) :
    (((k.factorial : ℚ_[p]))⁻¹) • ((glAct p LL j c d) ^ k) x ∈
      ⨆ (h : MvPolynomial (Fin N × Fin r) ℚ_[p]) (_ : Q h), WeylLat p LL j h := by
  have hle : (⨆ (h : MvPolynomial (Fin N × Fin r) ℚ_[p]) (_ : Q h), WeylLat p LL j h) ≤
      (⨆ (h : MvPolynomial (Fin N × Fin r) ℚ_[p]) (_ : Q h), WeylLat p LL j h).comap
        (((((k.factorial : ℚ_[p]))⁻¹) • ((glAct p LL j c d) ^ k) :
          MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]).restrictScalars ℤ_[p]) := by
    refine iSup_le fun h => iSup_le fun hh => ?_
    intro y hy
    rw [Submodule.mem_comap]
    exact (le_iSup_of_le h (le_iSup_of_le hh le_rfl) :
      WeylLat p LL j h ≤ ⨆ (h : MvPolynomial (Fin N × Fin r) ℚ_[p]) (_ : Q h), WeylLat p LL j h)
      (weylLat_div LL j h c d hcd k y hy)
  exact hle hx

theorem weylP_of (hW : WeylInt) (hB : LatBasisPol) : WeylP := by
  intro p _ N r LL j _ la x hx hxi
  have he : kapC p r LL.total = (univ : Finset (Fin r)).card.choose 2 *
      Nat.log p (LL.total + (univ : Finset (Fin r)).card - 1) := by
    rw [kapC, Finset.card_univ, Fintype.card_fin]
  rw [he]
  have h1 := hW p _ _ (GAe p LL j (enumC (univ : Finset (Fin r)))) (Pol p r LL)
    (IntPol p (Fin N × Fin r)).toAddSubgroup LL.total (polLatData_of hB LL LL j _) (la ∘ enumC univ) x
    (isoC_inf_pol_le LL LL j univ la hx) hxi
  have hle : DeltaLat p (GAe p LL j (enumC (univ : Finset (Fin r))))
      {h | (GAe p LL j (enumC (univ : Finset (Fin r)))).IsHW (la ∘ enumC univ) h ∧ h ∈ Pol p r LL ∧
        h ∈ (IntPol p (Fin N × Fin r)).toAddSubgroup} ≤
      (⨆ (h : MvPolynomial (Fin N × Fin r) ℚ_[p])
        (_ : h ∈ HWC p LL j univ la ⊓ Pol p r LL ∧ h ∈ IntPol p (Fin N × Fin r)),
        WeylLat p LL j h).toAddSubgroup := by
    refine sInf_le ⟨?_, zpClosed_toAddSubgroup _, ?_⟩
    · rintro h ⟨h1, h2, h3⟩
      exact (le_iSup_of_le h (le_iSup_of_le ⟨⟨(hwc_iff LL j univ la h).mpr h1, h2⟩, h3⟩ le_rfl) :
        WeylLat p LL j h ≤ ⨆ (h : MvPolynomial (Fin N × Fin r) ℚ_[p])
          (_ : h ∈ HWC p LL j univ la ⊓ Pol p r LL ∧ h ∈ IntPol p (Fin N × Fin r)), WeylLat p LL j h)
        (weylLat_self LL j h)
    · intro a b hab k y hy
      exact iSup_weylLat_div LL j _ _ _ (fun h => hab ((enumC univ).injective h)) k y hy
  exact hle h1

end Formalism.InvariantFactorPaths.PW
