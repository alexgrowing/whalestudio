import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatIndLastKerRow
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineModelKappaTransformIsLocalModel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierPairingDualIndicatorAddNonzeroCosets
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DualLatticeCosetIndicatorIsSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatTensorIndicatorCharacterFacts
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPlaceModelExtensionLineLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SbHalfOfNsmul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)

noncomputable section
namespace GlobalTheory.KapStep
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem colExt : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (L T : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p T n) (ζ : Fin L.rank → D.host.E) (s : k), s ≠ 0 → ∀ (FL : GlobalTheory.LocMod.Frame k L.rank Unit), (∀ r, FL.β r () = s * (GlobalTheory.LocMod.Place.ofSplitPt p).pr (ζ r)) → ∀ (a : (n → k) → ℂ) (c : SB (Matrix n Unit k)), (∀ M, c.1 M = a (s⁻¹ • fun r => M r ())) → GlobalTheory.LocMod.Witness.ext (GlobalTheory.LocMod.Place.ofSplitPt p) FL (GlobalTheory.LocMod.Frame.ofFinPl β) c = colFun β ζ a := by
  intro D k _ _ _ _ p L T n _ _ β ζ s hs FL hFL a c hc
  classical
  funext y
  rw [GlobalTheory.LocMod.Witness.ext_apply, hc, colFun]
  refine if_congr Iff.rfl ?_ rfl
  congr 1
  funext r
  simp only [GlobalTheory.LocMod.Place.down, GlobalTheory.FinPl.ExtZero.zcol, Pi.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.mulVec,
    dotProduct, map_sum, map_mul, hFL, Matrix.map_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  show s⁻¹ * (β.b' r i * p.pr (y i j) * (s * p.pr (incA D (ζ j)))) = _
  field_simp

theorem rowExt : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (T L : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p T n) (ζ₀ : Fin L.rank → D.host.E), IsLineVec L ζ₀ → ∀ (FL : GlobalTheory.LocMod.Frame k L.rank Unit), (∀ r, FL.β r () = (GlobalTheory.LocMod.Place.ofSplitPt p).pr (ζ₀ r)) → ∀ (b : (n → k) → ℂ) (Φ : SB (Matrix Unit n k)), (∀ M, Φ.1 M = b (M ())) → GlobalTheory.LocMod.Witness.ext (GlobalTheory.LocMod.Place.ofSplitPt p) (GlobalTheory.LocMod.Frame.ofFinPl β) FL Φ = rowFun β ζ₀ b := by
  intro D k _ _ _ _ p T L n _ _ β ζ hζ FL hFL b Φ hΦ
  classical
  funext x
  rw [GlobalTheory.LocMod.Witness.ext_apply, hΦ, rowFun]
  refine if_congr Iff.rfl ?_ rfl
  congr 1
  set P := GlobalTheory.LocMod.Place.ofSplitPt p with hP
  set f := GlobalTheory.LocMod.Witness.prH P with hf
  have hfa : ∀ a, f a = p.pr (incA D a) := fun _ => rfl
  set h : D.host.E := star ζ ⬝ᵥ Matrix.mulVec L.gram ζ with hh
  have h0 : f h ≠ 0 := (map_ne_zero f).2 hζ.2
  set u : Fin L.rank → k := fun j => f ((Matrix.vecMul (star ζ) L.gram) j) with hu
  have hu1 : ∑ j, u j * f (ζ j) = f h := by
    rw [hh, Matrix.dotProduct_mulVec, dotProduct, map_sum]
    exact Finset.sum_congr rfl fun j _ => (map_mul f _ _).symm
  have hγ : ∀ j, FL.γ () j = (f h)⁻¹ * u j := fun j => by
    have h1 : ∀ i, f (ζ i) * FL.γ () j = (1 : Matrix _ _ k) i j := fun i => by
      rw [← FL.βγ, Matrix.mul_apply]
      simp only [Finset.univ_unique, Finset.sum_singleton]
      exact congrArg (· * _) (hFL i).symm
    have h2 : u j = f h * FL.γ () j := by
      rw [← hu1, Finset.sum_mul]
      simp only [mul_assoc, h1, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [h2, inv_mul_cancel_left₀ h0]
  funext r
  simp only [GlobalTheory.LocMod.Place.down, GlobalTheory.FinPl.ExtZero.zrow, Pi.smul_apply, smul_eq_mul, Matrix.mul_apply, hγ, Matrix.map_apply]
  show _ = (f h)⁻¹ * ∑ i, p.pr (∑ j, incA D (Matrix.vecMul (star ζ) L.gram j) * x j i) * β.b i r
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum, ← mul_assoc, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, mul_assoc]
  rfl

open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (Lifts InDual resUnit) in

theorem fourier : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : MeasureTheory.Measure k), ν.IsAddHaarMeasure → ∀ (n : Type) [Fintype n] [DecidableEq n] (χ : AddChar k Circle) (hχ : HasConductor χ 1) (q : Unif k) (ψk : AddChar k Circle) (xi s : k), (∀ x, ψk x = χ (xi * x)) → s ≠ 0 → ∀ w : 𝒪[k]ˣ, -(xi * s) = ((w : 𝒪[k]) : k) → ∀ Q : Pair k n, ∃ (C : ℂ) (c : SB (Matrix n Unit k)) (Ψ : SB (Matrix Unit n k)), (∀ M, c.1 M = charInd (resChar χ hχ q) Q (s⁻¹ • fun r => M r ())) ∧ (∀ M, Ψ.1 M = cosetInd q Q.lat ((GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.resUnit w)⁻¹ • Q).red (M ())) ∧ ∀ η, C * Ψ.1 η = GlobalTheory.StepData.hat ψk ν (-1) (fun y => c.1 (Matrix.of fun r _ => y r)) (η ()) := by
  intro k _ _ _ _ _ _ ν hν n _ _ χ hχ q ψk xi s hψk hs w hw Q
  classical
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  haveI := secondCountable k
  haveI := hν
  obtain ⟨F, hF⟩ := GlobalTheory.FinPl.CosetPairing.exists_lifts Q
  set wk : k := ((w : 𝒪[k]) : k) with hwk
  set wi : k := (((w⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) : k) with hwi
  have hww : wk * wi = 1 := by rw [hwk, hwi, ← Subring.coe_mul, Units.mul_inv]; rfl
  have hF' : Lifts Q.lat (wi • F) ((resUnit w)⁻¹ • Q).red := fun y => by
    obtain ⟨t, ht, hr⟩ := hF y
    refine ⟨(w⁻¹ : 𝒪[k]ˣ) * t, by rw [smul_dotProduct, ← ht]; rfl, ?_⟩
    rw [map_mul, hr]
    rfl
  let L' : Submodule 𝒪[k] (n → k) := Q.lat.comap ((LinearMap.lsmul k (n → k) s⁻¹).restrictScalars 𝒪[k])
  have hc : (fun M : Matrix n Unit k => charInd (resChar χ hχ q) Q (s⁻¹ • fun r => M r ())) ∈ SB (Matrix n Unit k) :=
    GlobalTheory.FinPl.Comm.comp_mem_SB (GlobalTheory.FinPl.SBFacts.charInd_mem _ Q) (s := fun y => Matrix.of fun r _ => s * y r)
      (by fun_prop) (continuous_pi fun r => continuous_pi fun _ => by simp only [Matrix.of_apply]; fun_prop) fun M => by
        ext r u
        simp [hs]
  have hΨ : (fun M : Matrix Unit n k => cosetInd q Q.lat ((resUnit w)⁻¹ • Q).red (M ())) ∈ SB (Matrix Unit n k) :=
    GlobalTheory.FinPl.Comm.comp_mem_SB (GlobalTheory.FinPl.CosetSB.cosetInd_mem_SB k n q Q.lat _) (s := fun y => Matrix.of fun _ r => y r)
      (by fun_prop) (continuous_pi fun _ => continuous_pi fun r => by simp only [Matrix.of_apply]; fun_prop) fun M => rfl
  refine ⟨∫ y, vecInd L' y ∂(MeasureTheory.Measure.pi fun _ => ν), ⟨_, hc⟩, ⟨_, hΨ⟩, fun _ => rfl, fun _ => rfl, fun η => ?_⟩
  set η' : n → k := η () - q.inv • wi • F with hη'
  have e1 : cosetInd q Q.lat ((resUnit w)⁻¹ • Q).red (η ()) = dualInd Q.lat η' := by
    rw [← GlobalTheory.FinPl.CosetPairing.cosetInd_add q hF' η', hη', sub_add_cancel]
  have e2 : ∀ y : n → k, charInd (resChar χ hχ q) Q (s⁻¹ • y) * (ψk (-1 * (η () ⬝ᵥ y)) : ℂ) =
      vecInd L' y * (χ (wk * s⁻¹ * (η' ⬝ᵥ y)) : ℂ) := fun y => by
    by_cases hy : s⁻¹ • y ∈ Q.lat
    · have hy' : y ∈ L' := hy
      obtain ⟨t, ht, hr⟩ := hF ⟨_, hy⟩
      have hr' : Q.ev (s⁻¹ • y) = residue 𝒪[k] t := ((Q.hasVal_fn ⟨_, hy⟩).ev_eq).trans hr.symm
      rw [charInd, vecInd, vecInd, if_pos hy, if_pos hy', hr', ← map_neg, resChar_residue, hψk, mul_one, one_mul,
        ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
      congr 2
      have ht' : (t : k) = s⁻¹ * (F ⬝ᵥ y) := by rw [ht]; simp
      have hx : xi = -wk * s⁻¹ := by rw [← hw]; field_simp
      rw [hη', sub_dotProduct, smul_dotProduct, smul_dotProduct, Subring.coe_neg, ht', hx, smul_eq_mul, smul_eq_mul]
      linear_combination (q.inv * s⁻¹ * (F ⬝ᵥ y)) * hww
    · have hy' : y ∉ L' := hy
      rw [charInd, vecInd, vecInd, if_neg hy, if_neg hy', mul_zero, zero_mul, zero_mul]
  show _ * cosetInd q Q.lat ((resUnit w)⁻¹ • Q).red (η ()) =
    ∫ y, charInd (resChar χ hχ q) Q (s⁻¹ • y) * (ψk (-1 * (η () ⬝ᵥ y)) : ℂ) ∂(MeasureTheory.Measure.pi fun _ => ν)
  simp only [e2]
  rw [e1, dualInd]
  split_ifs with hd
  · rw [mul_one]
    congr 1
    funext y
    by_cases hy : y ∈ L'
    · have h1 : wk * s⁻¹ * (η' ⬝ᵥ y) ∈ 𝒪[k] := by
        have := mul_mem (w : 𝒪[k]).2 (hd _ hy)
        convert this using 1
        simp [mul_assoc, hwk]
      rw [apply_int_eq_one hχ ⟨_, h1⟩]
      simp
    · rw [vecInd, if_neg hy, zero_mul]
  · rw [mul_zero]
    obtain ⟨y, hy, hn⟩ : ∃ y ∈ Q.lat, η' ⬝ᵥ y ∉ 𝒪[k] := by
      by_contra h
      push Not at h
      exact hd h
    have h0 : η' ⬝ᵥ y ≠ 0 := fun h => hn (h ▸ zero_mem _)
    obtain ⟨z, hz, hz1⟩ : ∃ z, valuation k z ≤ valuation k (η' ⬝ᵥ y) ∧ χ z ≠ 1 := by
      by_contra h
      push Not at h
      exact hn ((Valuation.mem_integer_iff _ _).2 (by simpa using (hχ _).1 h))
    have ht : z / (η' ⬝ᵥ y) ∈ 𝒪[k] := by
      rw [Valuation.mem_integer_iff, map_div₀]
      exact div_le_one_of_le₀ hz zero_le'
    let t : 𝒪[k] := (w⁻¹ : 𝒪[k]ˣ) * ⟨_, ht⟩
    have hy₀ : s • t • y ∈ L' := by
      show s⁻¹ • s • t • y ∈ Q.lat
      rw [inv_smul_smul₀ hs]
      exact Q.lat.smul_mem t hy
    refine (GlobalTheory.FinPl.Comm.integral_vecInd_eq_zero χ _ _ L' η' hy₀ ?_).symm
    convert hz1 using 2
    show wk * s⁻¹ * (η' ⬝ᵥ s • (wi * (z / (η' ⬝ᵥ y))) • y) = z
    rw [dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, mul_assoc wi, div_mul_cancel₀ _ h0]
    field_simp
    linear_combination z * hww

theorem kapStep : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (q : Unif k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (χ : AddChar k Circle) (hχ : HasConductor χ 1), p.IsChar ψ χ → ∀ (n : Type) [Fintype n] [DecidableEq n] (L S L'' : HSp D) (ζ : Fin L.rank → D.host.E) (ζ₀ : Fin L''.rank → D.host.E), IsLineVec L ζ → IsLineVec L'' ζ₀ → ∀ (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (lam : D.host.E), Matrix.mulVec τ ζ₀ = lam • ζ → valuation k (p.pr (incA D lam)) = 1 → τ.conjTranspose * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∃ ε : 𝓀[k]ˣ, ∀ (β : Frame p S n) (LS : Lat S), IsSelfDualC S LS → ∀ (Q : Pair k n) (g₁ : WO L S → ℂ) (T₁ : (WO L S → ℂ) →ₗ[ℂ] (WO L S → ℂ)), IsThetaFunO ψ L S g₁ → IsPlaceModel ψ (symplO L S) (heisO ψ L S) p.e (latO L S ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ} : Lat L) : Set _) (LS : Set _) (· = p.v)) 1 g₁ T₁ → ∃ (g₃ : WO S L'' → ℂ) (T₃ : (WO S L'' → ℂ) →ₗ[ℂ] (WO S L'' → ℂ)), IsThetaFunO ψ S L'' g₃ ∧ IsPlaceModel ψ (symplO S L'') (heisO ψ S L'') p.e (latO S L'' (LS : Set _) ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ₀} : Lat L'') : Set _) (· = p.v)) 1 g₃ T₃ ∧ T₃ (rowFun β ζ₀ (cosetInd q Q.lat (ε • Q).red)) = fun w => T₁ (colFun β ζ (charInd (resChar χ hχ q) Q)) (kap τ S w) := by
  intro D k _ _ _ _ p q ψ hψ hU χ hχ hc n _ _ L S L'' ζ ζ₀ hζ hζ₀ τ lam hτ hlam hG
  set P := GlobalTheory.LocMod.Place.ofSplitPt p with hP
  set l : k := p.pr (incA D lam) with hl
  have hl0 : l ≠ 0 := fun h => by rw [h, map_zero] at hlam; exact zero_ne_one hlam
  have hlO : l ∈ 𝒪[k] := (Valuation.mem_integer_iff _ _).2 hlam.le
  have hliO : l⁻¹ ∈ 𝒪[k] := (Valuation.mem_integer_iff _ _).2 (by rw [map_inv₀, hlam, inv_one])
  let w : 𝒪[k]ˣ := ⟨⟨l, hlO⟩, ⟨l⁻¹, hliO⟩, Subtype.ext (mul_inv_cancel₀ hl0), Subtype.ext (inv_mul_cancel₀ hl0)⟩
  refine ⟨(GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.resUnit w)⁻¹, ?_⟩
  intro β LS hLS Q g₁ T₁ hg₁ hT₁
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  have hν : (MeasureTheory.Measure.addHaar : MeasureTheory.Measure k).IsAddHaarMeasure := inferInstance
  have hxi : P.xi ≠ 0 := GlobalTheory.LocMod.Witness.xi_ne P
  set s : k := -l / P.xi with hs
  have hs0 : s ≠ 0 := div_ne_zero (neg_ne_zero.2 hl0) hxi
  have hxs : -(P.xi * s) = ((w : 𝒪[k]) : k) := by
    show -(P.xi * (-l / P.xi)) = l
    field_simp

  have hζne : ∃ r, ζ r ≠ 0 := by
    by_contra h
    push Not at h
    apply hζ.2
    have : ζ = 0 := funext h
    simp [this]
  have hz : (fun r => s * P.pr (ζ r)) ≠ 0 := by
    obtain ⟨r, hr⟩ := hζne
    intro h
    have h1 := congrFun h r
    simp only [Pi.zero_apply] at h1
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact hs0 h2
    · exact hr ((GlobalTheory.LocMod.Witness.prH P).injective (h2.trans (map_zero _).symm))
  obtain ⟨FL, hFL⟩ := GlobalTheory.KappaModel.exists_frame_col hζ.1 _ hz
  set FS := GlobalTheory.LocMod.Frame.ofFinPl β with hFS
  have hTLS := GlobalTheory.LineLatModel.isModel_ext D k p ψ hψ hU L S ζ hζ LS hLS g₁ T₁ hg₁ hT₁ n FL FS

  let ψk : AddChar k Circle := χ.compAddMonoidHom (AddMonoidHom.mulLeft P.xi)
  have hψk : ∀ x, ψk x = χ (P.xi * x) := fun _ => rfl
  have hk : P.IsChar ψ ψk := (GlobalTheory.LocMod.Place.isChar_ofSplitPt p hc).2 hψk
  set z₀ : Fin L''.rank → k := fun i => P.pr (ζ₀ i) with hz₀
  have hτz : (τ.map P.pr).mulVec z₀ = (-(P.xi * s)) • fun i => P.pr (ζ i) := by
    rw [hxs]
    funext i
    have h2 := congrArg (fun v => GlobalTheory.LocMod.Witness.prH P (v i)) hτ
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.map_mulVec] at h2
    simp only [Pi.smul_apply, smul_eq_mul]
    exact h2
  obtain ⟨FL'', hFL'', TL, hTL, hTLc⟩ := GlobalTheory.KappaModel.kappa_model D k P MeasureTheory.Measure.addHaar hν ψ hψ ψk hk
    L S L'' ζ τ hζ₀.1 hG s z₀ hs0 hτz n FS FL hFL _ hTLS
  obtain ⟨C, c, Ψ, hc1, hΨ, hCΨ⟩ := fourier k MeasureTheory.Measure.addHaar hν n χ hχ q ψk P.xi s hψk hs0 w hxs Q
  obtain ⟨g₃, T₃, hg₃, hT₃, hT₃e⟩ := GlobalTheory.T.exists_splitPlaceModel_extension_lineLattice D k p ψ hψ hU S L'' ζ₀ hζ₀ LS hLS n FS FL'' (C • TL)
    (GlobalTheory.LocMod.Witness.isModel_smul P hTL C)
  refine ⟨g₃, T₃, hg₃, hT₃, ?_⟩
  have hrow := rowExt D k p S L'' n β ζ₀ hζ₀ FL'' hFL'' _ Ψ hΨ
  have hcol := colExt D k p L S n β ζ s hs0 FL hFL _ c hc1
  rw [← hrow, hT₃e, LinearMap.smul_apply, ← map_smul]
  funext w'
  rw [hTLc c (C • Ψ) (fun η => by rw [← hCΨ η]; rfl) w']
  show T₁ (GlobalTheory.LocMod.Witness.ext P FL FS c) _ = _
  rw [hcol]
  rfl

end GlobalTheory.KapStep

end
