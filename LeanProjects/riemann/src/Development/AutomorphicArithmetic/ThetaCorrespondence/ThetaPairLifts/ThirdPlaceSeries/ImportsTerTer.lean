import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugatePlaceCompletionIsoTame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.TypeBlockConj
end GlobalTheory.TypeBlockConj
namespace GlobalTheory.TypeBlockConj
set_option maxHeartbeats 1000000 in
theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (S : Reading P.T), _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E) (hw : IsSplitPl D.host s.w), s.w = GlobalTheory.DimPartsCompare.cPl (D.naut.plGw k v) → IsTame (S i s.w hw).mu → ∀ c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E, Continuous c → (∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) → ∀ Q, ∃ f ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q), f ≠ 0 ∧ ∀ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x → Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x) ∈ blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t → NG.rt D.host.E D.R.nV x f = blockChar (S i s.w hw).mu (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) • f := by
  intro hL D P S hS i k v s hw hs hμt c hc hcs Q
  obtain ⟨hj1, hj2⟩ := D.nd.j_range i
  let j : Fin D.R.m := ⟨D.nd.j i - 1, by omega⟩
  have hj : j.1 + 1 = D.nd.j i := by simp only [j]; omega
  have hconj : IsConjPl D.host (D.naut.plGw k v) s.w := by
    rw [hs]; exact GlobalTheory.DimPartsCompare.isConjPl_cPl _
  obtain ⟨hw₀, hi₀⟩ := GlobalTheory.T.conjugateSplitPlace_eq_conjugatePlace_and_embedding D s _ hconj
  obtain ⟨ψ₀, ξ, hψ, hξ, hU⟩ := P.H.level.uni i j hj k v (GlobalTheory.TypeTame.conjSP s) hw₀
  have hcc : ∀ x : D.host.E, D.host.conj (D.host.conj x) = x := fun x => by
    letI := Formalism.BasicNotions.Host.cmStar D.host
    rw [← GlobalTheory.DimPartsCompare.star_conj, ← GlobalTheory.DimPartsCompare.star_conj, star_star]
  have hcsd : IsCSD D.host (P.tp.tup (D.nd.mu i) j) := by
    have := (P.chr.csd _).1 (D.naut.muC_csd i)
    rwa [P.chr.muC i j hj] at this
  have hconj' : IsConjPl D.host s.w (D.naut.plGw k v) := by
    have := GlobalTheory.DimPartsCompare.isConjPl_cPl (GlobalTheory.DimPartsCompare.cPl (D.naut.plGw k v))
    rwa [GlobalTheory.DimPartsCompare.cPl_cPl, ← hs] at this
  have hμ := hS.mu i s.w hw j hj
  have hrel : ∀ u, ξ⁻¹ u = (S i s.w hw).mu (Units.map c.toMonoidHom u) := by
    refine GlobalTheory.T.splitPlace_unitsCharacter_eq_of_agree_on_field s c hc hcs _ _ hμ.1 ?_ ?_
    · obtain ⟨N, hN⟩ := hξ.1
      exact ⟨N, fun u hu => by rw [MonoidHom.inv_apply, hN u hu, inv_one]⟩
    · intro x
      have e1 : Units.map (s.i : D.host.E →* s.v.adicCompletion (maximalRealSubfield D.host.E)) x =
          Units.map ((GlobalTheory.TypeTame.conjSP s).i : D.host.E →* s.v.adicCompletion (maximalRealSubfield D.host.E))
            (Units.map (MonoidHomClass.toMonoidHom D.host.conj) x) := by
        ext; simp [hi₀, hcc]
      rw [MonoidHom.inv_apply, e1, hξ.2, hw₀, hcsd.1 _ _ hconj' x, inv_inv, hμ.2]
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer (maximalRealSubfield D.host.E) s.v
  set ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E) := (π : s.v.adicCompletion (maximalRealSubfield D.host.E)) with hϖdef
  have hϖ : Valued.v ϖ = WithZero.exp (-1) := by
    rw [hϖdef, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; exact hπ
  have hϖ0 : ϖ ≠ 0 := by
    intro h0; rw [h0, map_zero] at hϖ; exact WithZero.zero_ne_coe hϖ
  let d : GL (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E)) :=
    ⟨Matrix.diagonal (fun a : Fin D.R.nV => if (a : ℕ) < D.R.r then 1 else ϖ),
     Matrix.diagonal (fun a : Fin D.R.nV => if (a : ℕ) < D.R.r then 1 else ϖ⁻¹),
     by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext a; split_ifs <;> simp [hϖ0],
     by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext a; split_ifs <;> simp [hϖ0]⟩
  obtain ⟨y, hyT, hyd⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq D.R.nV (GlobalTheory.TypeTame.conjSP s) d⁻¹
  obtain ⟨y0, hy0, hy00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (D.naut.typeV_ne i Q)
  set f₀ := (P.M.loc i).real y0 with hf₀
  have hf0iso : f₀ ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q) := by
    rw [P.H.av.typeV] at hy0; exact hy0
  have hf0type : f₀ ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ := by
    rw [← (P.M.loc i).real_range]; exact LinearMap.mem_range_self _ _
  have hf0ne : f₀ ≠ 0 := fun h0 => hy00 ((P.M.loc i).real_inj (h0.trans (map_zero _).symm))
  refine ⟨NG.rt D.host.E D.R.nV y f₀, GlobalTheory.CompRed.isoTyp_stable _ _ _ hf0iso, ?_, ?_⟩
  · intro h0
    apply hf0ne
    funext g
    have := congrFun h0 (g * y⁻¹)
    simpa [NG.rt] using this
  · intro x hxT hxB
    have hv := GlobalTheory.T.splitPlace_completionIso_preserves_valuation s c hc hcs
    have hab := GlobalTheory.T.conjugateSplitPlace_unitaryLoc_eq_transpose_inv D.R.nV s x
    obtain ⟨κ, hκ⟩ : ∃ κ : GAf D.host.E D.R.nV, κ = y⁻¹ * x * y := ⟨_, rfl⟩
    have hκT : TrivOutside {s.v} κ := hκ ▸ GlobalTheory.TypeBlockConj.trivOutside_mul (GlobalTheory.TypeBlockConj.trivOutside_mul (GlobalTheory.TypeBlockConj.trivOutside_inv hyT) hxT) hyT
    have hκloc : (GlobalTheory.TypeTame.conjSP s).loc D.R.nV κ = d * (GlobalTheory.TypeTame.conjSP s).loc D.R.nV x * d⁻¹ := by
      rw [hκ, map_mul, map_mul, map_inv, hyd, inv_inv]
    obtain ⟨hUni, hsup⟩ := GlobalTheory.T.diagUniformiserConj_transposeInv_mem_upperParahoric s D.R.r D.R.t c hv (s.loc D.R.nV x) ((GlobalTheory.TypeTame.conjSP s).loc D.R.nV x) hab hxB ϖ hϖ d rfl
    obtain ⟨u, hu, hbc⟩ := GlobalTheory.T.blockCharacter_eq_inv_at_transposeInv_lowerBlockDet s D.R.r D.R.t c hv (s.loc D.R.nV x) ((GlobalTheory.TypeTame.conjSP s).loc D.R.nV x) hab hxB ϖ hϖ d rfl
    have hκJ : κ ∈ (P.M.loc i).J := (hU.mem κ hκT).2 (by rw [hκloc]; exact hUni)
    have hchr := hU.chr κ hκJ hκT u (by rw [hu, hκloc]; rfl)
    rw [hψ.1 _ (by rw [hκloc]; exact hsup), one_mul] at hchr
    have hty := hf0type.2 ⟨κ, hκJ⟩
    have hval : blockChar (S i s.w hw).mu (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) =
        (((P.M.loc i).χ ⟨κ, hκJ⟩ : ℂˣ) : ℂ) := by
      rw [hbc _ hμt, hchr, ← hrel u, MonoidHom.inv_apply, inv_inv]
    rw [hval]
    funext g
    have e := congrFun hty (g * y)
    have e2 : g * y * κ = g * x * y := by rw [hκ]; group
    rw [GlobalTheory.TypeBlockConj.rt_rt, Pi.smul_apply, ← e2]
    exact e
end GlobalTheory.TypeBlockConj
end
end
