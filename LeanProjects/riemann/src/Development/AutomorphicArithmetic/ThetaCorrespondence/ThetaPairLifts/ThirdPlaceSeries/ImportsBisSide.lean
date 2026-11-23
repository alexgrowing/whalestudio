import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCanonicalModuleSuccessor
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.RowModCanon
open MeasureTheory Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.PeterssonHilbertSpace
open scoped InnerProductSpace
end GlobalTheory.RowModCanon
namespace GlobalTheory.RowModCanon
open MeasureTheory Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Lev
  Formalism.IndefR.Links Formalism.IndefR.RecTie
set_option maxHeartbeats 1000000 in
theorem main_alt_alt : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7)
    (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), ∀ (j : Fin D.R.m) (j' : ℕ)
    (hj : j.1 + 1 = j'), ∃ Y : RowMod D P.rep j', GlobalTheory.NJoin.IsCanon X j hj Y := by
  intro hH hC hL D P X hA j j' hj
  subst hj
  have hmod := X.given.core.models
  have hθ := hmod.inf
  have hν := hmod.νW j
  have hHaar : (X.R.νW j).IsHaarMeasure := hν.1.1
  have hFD := hν.2
  have hSig : (Wc D j).SigOK := D.sp.W_sig _
  have hSA : SchurAll D := fun V _ S θ M J χ μ 𝓕 => (GlobalTheory.MultFinite.hcFinite_and_schurMult hH hC D θ V S M J χ μ 𝓕).2
  have hHA : HCAll D := fun V _ S θ M J χ => (GlobalTheory.MultFinite.hcFinite_and_schurMult hH hC D θ V S M J χ 0 ∅).1
  have hStd : GlobalTheory.Mem.R3.StdFrame hA.hF (X.PW j) := hA.stdW j
  have hcc := GlobalTheory.T.unitary_congruence_conj_contains_congruence D.host.E D.R.r
  obtain ⟨hlin, hherm, hpos⟩ := GlobalTheory.FinTypesRows.minf_sesq (M := X.R.MW j (sg0 D X.A)) (θ := X.R.θ) (X.R.νW j) (X.R.fdW j)
    (X.PW j) hSA hSig hθ hHaar hFD
  have hT := X.recR.tied.lift
  have hLev := GlobalTheory.FinTypesRows.levOK_levS (X.PW j) hStd (X.R.βW j) (X.R.datWp j (X.R.levL X.F false (sg0 D X.A)))
  set c : ℝ := (∏ ρ, ((Mult.dimK _ _ (kapAt (Wc D j) (sg0 D X.A) ρ) : ℚ) : ℝ)) * (RealDat.nP X.F false)⁻¹ with hcdef
  have hc : 0 < c := mul_pos (Finset.prod_pos fun ρ _ => by exact_mod_cast GlobalTheory.Mem.EasyInputs.dimOK D j (sg0 D X.A) ρ)
    (inv_pos.2 (RealDat.nP_pos false))
  have hSm := GlobalTheory.Mem.EasyInputs.smAll D (Wc D j) _ (X.R.MW j (sg0 D X.A))
  have hex : ∀ x ∈ principalLevelFrame.Minf X.R.θ (X.PW j) (X.R.MW j (sg0 D X.A)), ∀ y ∈ principalLevelFrame.Minf X.R.θ (X.PW j) (X.R.MW j (sg0 D X.A)),
      ∃ b, Mult.IsMultIP (X.R.MW j (sg0 D X.A)) (X.R.νW j) (X.R.fdW j) x y b := by
    intro x hx y hy
    obtain ⟨N, -, hx', hy'⟩ := GlobalTheory.FinTypesRows.exists_common (X.PW j) hx hy
    exact hSA _ hSig _ X.R.θ _ _ _ _ _ hθ hHaar hFD x hx' y hy'
  let φ : D.what₂.Mj (j.1 + 1) →ₗ[ℂ] Mult.MMap (X.R.MW j (sg0 D X.A)) :=
    (PiTensorProduct.lift : Mult.MMap (X.R.MW j (sg0 D X.A)) ≃ₗ[ℂ] _).symm.toLinearMap ∘ₗ
      (Submodule.subtype ((toLiftReal X.R X.F X.tupT X.hm X.hTop X.hinj).Wc j)) ∘ₗ (X.IL.jMj j).toLinearMap
  have hφ : ∀ y, PiTensorProduct.lift (φ y) = (X.IL.jMj j y).1 := by
    intro y
    exact LinearEquiv.apply_symm_apply _ _
  have hgood : ∀ y, φ y ∈ Mult.goodPart X.R.θ (X.R.MW j (sg0 D X.A)) (levS _ (X.R.βW j) (X.R.datWp j (X.R.levL X.F false (sg0 D X.A))))
      (levChi _ (X.R.βW j) (X.R.datWp j (X.R.levL X.F false (sg0 D X.A)))) (X.R.eWf j (sg0 D X.A)) := by
    intro y
    obtain ⟨a, ha, hay⟩ := (X.IL.jMj j y).2
    have : φ y = a := by
      show PiTensorProduct.lift.symm (X.IL.jMj j y).1 = a
      rw [← hay]
      exact LinearEquiv.symm_apply_apply _ _
    rw [this]
    exact ha
  have hmem : ∀ y, φ y ∈ principalLevelFrame.Minf X.R.θ (X.PW j) (X.R.MW j (sg0 D X.A)) := fun y =>
    principalLevelFrame.mult_le_Minf hLev (Mult.goodPart_le _ _ _ _ _ (hgood y))
  refine ⟨{ A := Mult.MMap (X.R.MW j (sg0 D X.A))
            ρ := principalLevelFrame.actM (X.PW j) (X.R.MW j (sg0 D X.A))
            C := principalLevelFrame.Minf X.R.θ (X.PW j) (X.R.MW j (sg0 D X.A))
            B := fun x y => (c : ℂ) * Mult.ipM (X.R.MW j (sg0 D X.A)) (X.R.νW j) (X.R.fdW j) x y
            lin := fun x hx y hy z hz c' => by
              rw [hlin x hx y hy z hz c']
              ring
            herm := fun x hx y hy => by
              rw [map_mul, Complex.conj_ofReal, ← hherm x hx y hy]
            pos := fun x hx hx0 => by
              rw [Complex.re_ofReal_mul]
              exact mul_pos hc (hpos x hx hx0)
            stab := fun h x hx => GlobalTheory.FinTypesRows.minf_stable (X.PW j) hcc h hx
            inv := fun h x hx y hy => by
              rw [GlobalTheory.T.schur_pairing_invariant_under_standard_group D (Wc D j) _ X.R.θ (X.R.MW j (sg0 D X.A)) D.R.r (X.PW j) (X.R.νW j) (X.R.fdW j) hSA hSig hθ
                hHaar hFD h x hx y hy]
            smooth := fun x hx => GlobalTheory.FinTypesRows.minf_smooth (X.PW j) hx
            adm := fun N hN => GlobalTheory.FinTypesRows.minf_adm (X.PW j) hHA hSig hθ (GlobalTheory.FinTypesRows.levN_open (X.PW j) hStd) N hN
            φ := φ
            φ_mem := hmem
            φ_inner := fun x y => by
              beta_reduce
              rw [hT.mj j x y]
              change (∏ τ, ((Mult.dimK _ _ (kapAt (Wc D j) (sg0 D X.A) τ) : ℚ) : ℂ)) *
                Mult.ipM (X.R.MW j (sg0 D X.A)) (ENNReal.ofReal (RealDat.nP X.F false)⁻¹ • X.R.νW j) (X.R.fdW j) (φ x) (φ y) = _
              rw [ipM_smul_measure _ hSm _ _ (inv_nonneg.2 (RealDat.nP_pos false).le) _ _ (hex _ (hmem x) _ (hmem y)), hcdef]
              push_cast
              ring
            isot := fun σ y => by
              rw [hT.isot j σ y, X.recR.prtWE j σ, principalLevelFrame.isotIn_iso _ _ (hA.rep_iso σ)]
              constructor
              · rintro ⟨a, ha, hay⟩
                have e : φ y = a := by
                  show PiTensorProduct.lift.symm (X.IL.jMj j y).1 = a
                  rw [← hay]
                  exact LinearEquiv.symm_apply_apply _ _
                rw [e]
                exact (Submodule.mem_inf.1 ha).2
              · intro h
                exact ⟨φ y, Submodule.mem_inf.2 ⟨hgood y, h⟩, hφ y⟩ }, LinearMap.id, c, Function.injective_id, hc, Submodule.map_id _, fun h x => rfl, fun x _ y _ => rfl,
            fun y => hφ y⟩
end GlobalTheory.RowModCanon
end
end
