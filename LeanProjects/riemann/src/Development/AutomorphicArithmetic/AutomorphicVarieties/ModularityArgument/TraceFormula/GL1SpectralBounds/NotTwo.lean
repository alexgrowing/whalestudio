import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.CuspOrTwoAlt
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSatAsc
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.EventuallySatV
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PStringStepC
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.JacquetShalikaRigidity

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F UpperTheory.V.Z.Tf.GOne

private theorem satV_of_locComp {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}
    {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) {w : HeightOneSpectrum (𝓞 E)}
    {σ : SmIrr (Matrix.GeneralLinearGroup (Fin N) (w.adicCompletion E))} (hσ : IsLocCompGL V w σ) {B : Multiset ℂˣ}
    (hB : GlobalTheory.LFun.HasSatGL w σ.ρ B) {φ : Sm E N} (hφ : φ ∈ V) (h0 : φ ≠ 0)
    (hfix : ∀ k ∈ GlobalTheory.LFun.KGL w N, finRep E N (locGL E N w k) φ = φ) : SatV V w B := by
  have hmem : ∀ ψ ∈ V, ψ ∈ ⨆ f : SatakeVectors.SatakeVectorEventually.MapsD V w σ, LinearMap.range f.1 := fun ψ hψ => by
    rw [SatakeVectors.SatakeVectorEventually.iSup_range_eq hV w σ hσ]; exact hψ
  have key : ∀ ψ ∈ V, (∀ k ∈ GlobalTheory.LFun.KGL w N, finRep E N (locGL E N w k) ψ = ψ) → ψ ≠ 0 →
      GlobalTheory.LFun.IsSatVecGL w ((finRep E N).comp (locGL E N w)) ψ B := fun ψ hψ hψK hψ0 =>
    GlobalTheory.HeightCounting.Blocks.isSatVecGL_of_mem_iSup σ.irred hB (fun f : SatakeVectors.SatakeVectorEventually.MapsD V w σ => f.1) (fun f => f.2.2)
      (hmem ψ hψ) (GlobalTheory.LGrp.mem_fixed.2 hψK) hψ0
  exact ⟨⟨φ, hφ, key φ hφ hfix h0⟩, key⟩

theorem UpperTheory.V.Z.Tf.GOne.notTwo :
    NotTwo := by
  intro E _ _ _ N a d V P π ha hd hV hA h
  have hNa : d * a = N := by
    obtain ⟨e, -⟩ := hA
    simpa using e
  have hN : 1 ≤ N := by
    rw [← hNa]
    exact Nat.mul_pos (by omega) ha
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV.ne_bot
  have hlev := GlobalTheory.CuspRep.LocSph.eventually_mem (E := E) ((hV.aut φ hφ).level.mem_nhds (by simp))
  have key : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite,
      ∃ (B : Fin d → Multiset ℂˣ) (B' : Unit → Multiset ℂˣ),
        (∀ i, ((CG.mk P).twist (GlobalTheory.CuspRep.Model.absC E (spehExp d i : ℂ))).HasSat w (B i)) ∧
        (∀ _j : Unit, (CG.mk π).HasSat w (B' ())) ∧ ∑ i, B i = ∑ j, B' j := by
    filter_upwards [h, satAsc_holds E N a d V P hV hA, hlev] with w hw hs hl
    obtain ⟨σ, B, hσ, hB, hπ⟩ := hw
    obtain ⟨B₀, hB₀, hall⟩ := hs
    have hfix : ∀ k ∈ GlobalTheory.LFun.KGL w N, finRep E N (locGL E N w k) φ = φ := fun k hk => by
      obtain ⟨g, rfl⟩ := hk
      exact hl g
    have e := hall B (satV_of_locComp hV hσ hB hφ h0 hfix)
    refine ⟨fun i => B₀.map (· * (GlobalTheory.CuspRep.Model.absC E (spehExp d i : ℂ)).val w), fun _ => B,
      fun i => StrStepB.hasSat_twist_absC P hB₀ _, fun _ => hπ, ?_⟩
    apply Multiset.map_injective (f := fun b : ℂˣ => (b : ℂ)) Units.val_injective
    simp only [Finset.univ_unique, Finset.sum_singleton]
    rw [e, StrStepC.map_fsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [SatakeVectors.satTw_eq]
    simp only [Multiset.map_map]
    refine Multiset.map_congr rfl fun b _ => ?_
    simp [StrStepB.absC_val]
  obtain ⟨s, -⟩ := PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity E (Fin d) Unit (fun _ => a) (fun _ => N)
    (fun i => (CG.mk P).twist (GlobalTheory.CuspRep.Model.absC E (spehExp d i : ℂ))) (fun _ => CG.mk π)
    (fun _ => ha) (fun _ => hN) key
  have hc := Fintype.card_congr s
  simp at hc
  omega
