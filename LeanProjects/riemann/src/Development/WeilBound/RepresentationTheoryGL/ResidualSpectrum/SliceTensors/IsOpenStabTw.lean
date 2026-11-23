import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSatCore
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSatTw
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.EventuallySatV
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.ExistsHasInfCharGL
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PProjA
import GroundTheory.PAdicHodge.AInfGalois

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin GlobalTheory.BCWords

namespace PositivityTheory.Rg.Rs

namespace SatakeInductionStabiliserOpen

open SatakeVectors PInfInd2A

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem isOpen_stab_tw {m : ℕ} {V : Submodule ℂ (Sm E m)} (hV : IsDiscrete V) (z : ℂ) (w : HeightOneSpectrum (𝓞 E)) :
    ∀ ψ ∈ tw V z, IsOpen {g : GL (Fin m) (w.adicCompletion E) | finRep E m (locGL E m w g) ψ = ψ} := by
  intro ψ hψ
  obtain ⟨φ, hφ, rfl⟩ := Submodule.mem_map.1 hψ
  set χ := Model.absC E z
  have hA : IsOpen {g : GL (Fin m) (w.adicCompletion E) | finRep E m (locGL E m w g) φ = φ} :=
    (hV.aut φ hφ).level.preimage (CuspSub.continuous_locGL w)
  have hC := CuspSub.isOpen_ker_locDet (a := m) χ w
  let H : Subgroup (GL (Fin m) (w.adicCompletion E)) :=
    { carrier := {g | finRep E m (locGL E m w g) (mulChi m χ φ) = mulChi m χ φ}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        change finRep E m (locGL E m w (a * b)) _ = _
        rw [map_mul, map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := fun {a} ha => by
        change finRep E m (locGL E m w a⁻¹) _ = _
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one, Module.End.one_apply] }
  have hsub : {g : GL (Fin m) (w.adicCompletion E) | finRep E m (locGL E m w g) φ = φ} ∩
      {g | CuspSub.locDet m χ w g = 1} ⊆ (H : Set _) := fun g hg => by
    change finRep E m (locGL E m w g) (mulChi m χ φ) = mulChi m χ φ
    rw [finRep_mulChi]
    have e1 : χ.loc w (Matrix.GeneralLinearGroup.det g) = 1 := hg.2
    rw [e1, Units.val_one, one_smul, hg.1]
  exact H.isOpen_of_mem_nhds (Filter.mem_of_superset ((hA.inter hC).mem_nhds
    ⟨(by simp : finRep E m (locGL E m w 1) φ = φ), by simp⟩) hsub)

def blkS (B₁ B₂ : Multiset ℂˣ) : Fin 2 → Multiset ℂˣ
  | ⟨0, _⟩ => B₁
  | ⟨1, _⟩ => B₂

end SatakeInductionStabiliserOpen

open SatakeVectors SatakeInductionStabiliserOpen PInfInd2A in
theorem satInd2_holds : SatInd2 := by
  intro E _ _ _ r s V V₁ V₂ z₁ z₂ hV hV₁ hV₂ hemb
  filter_upwards [eventually_satV hV, eventually_satV hV₁, eventually_satV hV₂] with w hB hB₁ hB₂
  obtain ⟨B, hB⟩ := hB
  obtain ⟨B₁, hB₁⟩ := hB₁
  obtain ⟨B₂, hB₂⟩ := hB₂
  refine ⟨B, B₁, B₂, hB, hB₁, hB₂, ?_⟩
  obtain ⟨f, hfP, hfi, hfe⟩ := hemb
  obtain ⟨φ, hφ, hsat⟩ := hB.1
  have hF0 : f φ ≠ 0 := fun e => hsat.1 (hfi φ hφ e)

  have hsatD : GlobalTheory.LFun.IsSatVecGL w (GlobalTheory.DiscLocEx.locRepD hV.stable w) ⟨φ, hφ⟩ B :=
    GlobalTheory.LFun.IsSatVecGL.of_map (ρ' := (finRep E (r + s)).comp (locGL E (r + s) w)) V.subtype (fun _ _ => rfl)
      Subtype.val_injective hsat
  have hFB : GlobalTheory.LFun.IsSatVecGL w ((finRep E (r + s)).comp (locGL E (r + s) w)) (f φ) B :=
    hsatD.map (f ∘ₗ V.subtype) (fun g v => hfe (.fin (locGL E (r + s) w g)) v.1 v.2) hF0
  have hFK : ∀ k ∈ GlobalTheory.LFun.KGL w (r + s), finRep E (r + s) (locGL E (r + s) w k) (f φ) = f φ := fun k hk =>
    GlobalTheory.LGrp.mem_fixed.1 hFB.2.1 k hk
  have h : ∑ i, (![r, s] : Fin 2 → ℕ) i = r + s := GlobalTheory.CompanionTheory.CTFin.CapFactor.two_sum _
  have hcore := isSatVecGL_of_ind (n := ![r, s]) h (blkV (tw V₁ z₁) (tw V₂ z₂))
    (fun i => by fin_cases i
                 · exact fun g ψ hψ => ParabolicProjection.isStable_tw hV₁.stable z₁ (.fin g) ψ hψ
                 · exact fun g ψ hψ => ParabolicProjection.isStable_tw hV₂.stable z₂ (.fin g) ψ hψ)
    (fun i => by fin_cases i
                 · exact isOpen_stab_tw hV₁ z₁ w
                 · exact isOpen_stab_tw hV₂ z₂ w)
    (blkS (B₁.map (· * qU w (-z₁))) (B₂.map (· * qU w (-z₂))))
    (fun i => by fin_cases i
                 · exact satLike_tw (satLike_of_satV hB₁) z₁
                 · exact satLike_tw (satLike_of_satV hB₂) z₂)
    hF0 hFK
    (fun u hu g => by
      obtain ⟨x, rfl⟩ := GlobalTheory.CompanionTheory.CTFin.CapFactor.exists_unip_of_mem ![r, s] h hu
      exact (hfP φ hφ).1 x g)
    (fun k g => by
      have := tensorSp_of_tens2 (n := ![r, s]) (tw V₁ z₁) (tw V₂ z₂) ((hfP φ hφ).2 k g)
      convert this using 2 with m
      have e := GlobalTheory.CompanionTheory.CTFin.CapFactor.lev_eq_leviEmb (![r, s]) h (m 0, m 1)
      rw [levPair_eta] at e
      exact congrArg (fun x => (f φ).1 (x * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g))) e.symm)
  have hBeq := GlobalTheory.LFun.IsSatVecGL.unique hFB hcore
  have q0 : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (NumberField.HeightOneSpectrum.one_lt_absNorm w).ne_bot
  rw [hBeq, Fin.sum_univ_two, Multiset.map_add]
  congr 1
  · change ((B₁.map (· * qU w (-z₁))).map (· * qU w ((modExp (fun i => Fin (![r, s] i)) 0 : ℂ) / 2))).map
      (fun b : ℂˣ => (b : ℂ)) = _
    rw [GlobalTheory.CompanionTheory.CTFin.CapFactor.modExp_zero, satTw_eq, Multiset.map_map, Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl fun b _ => ?_
    simp only [Function.comp_apply, Units.val_mul, qU_val]
    rw [mul_assoc, ← Complex.cpow_add _ _ q0]
    congr 2
    simp
    ring
  · change ((B₂.map (· * qU w (-z₂))).map (· * qU w ((modExp (fun i => Fin (![r, s] i)) 1 : ℂ) / 2))).map
      (fun b : ℂˣ => (b : ℂ)) = _
    rw [GlobalTheory.CompanionTheory.CTFin.CapFactor.modExp_one, satTw_eq, Multiset.map_map, Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl fun b _ => ?_
    simp only [Function.comp_apply, Units.val_mul, qU_val]
    rw [mul_assoc, ← Complex.cpow_add _ _ q0]
    congr 2
    simp
    ring

end PositivityTheory.Rg.Rs

end
