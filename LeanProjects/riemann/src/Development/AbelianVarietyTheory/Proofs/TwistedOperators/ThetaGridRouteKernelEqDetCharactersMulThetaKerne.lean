import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsGridFr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunOOfMatchedSquareBigRoute
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumAdjointNegSourceKernelsAgree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawOneSourceOrthogonalSumTargets
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTwistHeckeCharacters

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.RouteSeesaw GlobalTheory.ChainFr
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SquareDict.ExactBig

variable {D : D7}

theorem exists_change {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χ χ₁ χ' : (AE D)ˣ →* Circle}
    {ω₁ : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (H₁ : IsWeilDatumO ψ S T χ₁ χ' ω₁)
    (hχ : IsHeckeChar D χ) (rχ : ResEta D χ S.rank) :
    ∃ ω, IsWeilDatumO ψ S T χ χ' ω ∧ ∀ u g y, IsDetRoot T g y → ω₁ (u, g) = (((χ₁ / χ) y : Circle) : ℂ) • ω (u, g) := by
  have r0 : ResEta D (χ * χ₁⁻¹) 0 :=
    Formalism.L2.Theta.resEta_parity (Formalism.L2.Theta.resEta_mul rχ (Formalism.L2.Theta.resEta_inv H₁.resS)) (by omega)
  have r1 : ResEta D 1 0 := ⟨r0.1, fun _ _ _ => by simp⟩
  have h1 : IsHeckeChar D 1 := ⟨continuous_const, fun _ => rfl⟩
  obtain ⟨ω, H, hv⟩ := GlobalTheory.WeilChange.exists_weilDatum_twist D ψ H₁.std S T χ₁ χ' (χ * χ₁⁻¹) 1 ω₁ H₁
    (GlobalTheory.WeilChange.hecke_mul hχ (GlobalTheory.WeilChange.hecke_inv H₁.hecS)) h1 r0 r1
  have e : χ₁ * (χ * χ₁⁻¹) = χ := by rw [mul_comm χ, mul_inv_cancel_left]
  rw [e, mul_one] at H
  refine ⟨ω, H, fun u g y hy => ?_⟩
  obtain ⟨x, hx⟩ := GlobalTheory.RecDict.exists_isDetRoot D S u
  have e1 : (χ₁ / χ) y * (((1 : (AE D)ˣ →* Circle) x)⁻¹ * (χ * χ₁⁻¹) y) = 1 := by
    rw [MonoidHom.one_apply, inv_one, one_mul, ← MonoidHom.mul_apply, ← mul_assoc, div_mul_cancel, mul_inv_cancel,
      MonoidHom.one_apply]
  rw [hv u g x y hx hy, smul_smul, ← Circle.coe_mul, e1, Circle.coe_one, one_smul]

theorem seesaw_exact {ψ : AddChar (AF D.host.F) ℂ} {S A B : HSp D} {χ χ₁ χ₁' χ₂ χ₂' : (AE D)ˣ →* Circle}
    {ω₁ : GA D S × GA D A →* Module.End ℂ (WO S A → ℂ)} {ω₂ : GA D S × GA D B →* Module.End ℂ (WO S B → ℂ)}
    {ω : GA D S × GA D (GlobalTheory.Doubling.hsum A B) →* Module.End ℂ (WO S (GlobalTheory.Doubling.hsum A B) → ℂ)}
    (H₁ : IsWeilDatumO ψ S A χ₁ χ₁' ω₁) (H₂ : IsWeilDatumO ψ S B χ₂ χ₂' ω₂)
    (H : IsWeilDatumO ψ S (GlobalTheory.Doubling.hsum A B) χ (χ₁' * χ₂') ω)
    {φ : WO S A → ℂ} {φ' : WO S B → ℂ} (hφ : IsThetaFunO ψ S A φ) (hφ' : IsThetaFunO ψ S B φ')
    (u : GA D S) (g : GA D A) (g₁ : GA D B) {x y : (AE D)ˣ} (hx : IsDetRoot A g x) (hy : IsDetRoot B g₁ y) :
    thetaKO ω₁ u g φ * thetaKO ω₂ u g₁ φ' = (((χ₁ / χ) x : Circle) : ℂ) * (((χ₂ / χ) y : Circle) : ℂ) *
      thetaKO ω u (GlobalTheory.SquareComm.blk A B (g, g₁)) (box2 φ φ') := by
  obtain ⟨o₁, K₁, e₁⟩ := exists_change H₁ H.hecS H.resS
  obtain ⟨o₂, K₂, e₂⟩ := exists_change H₂ H.hecS H.resS
  have key := (GlobalTheory.TensorTargetRule.tensorTarget D ψ H.std _ A B (GlobalTheory.BiTransfer.sumDec A B) S).om_box χ χ₁' χ₂' ω o₁
    o₂ H K₁ K₂ u g g₁ φ φ' hφ hφ'
  simp only [thetaKO]
  rw [← GlobalTheory.SeesawSumTarget.emb_sumDec, ← GlobalTheory.SeesawSumTarget.boxT_sumDec, key, GlobalTheory.MixModel.OrthDec.boxT_zero,
    e₁ u g x hx, e₂ u g₁ y hy]
  simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem adjoint_exact {ψ : AddChar (AF D.host.F) ℂ} {S B : HSp D} {χB χS : (AE D)ˣ →* Circle}
    {ω₂ : GA D B × GA D S →* Module.End ℂ (WO B S → ℂ)} (H : IsWeilDatumO ψ B S χB χS ω₂) :
    ∃ ω : GA D (negSp S) × GA D B →* Module.End ℂ (WO (negSp S) B → ℂ),
      IsWeilDatumO ψ (negSp S) B χS⁻¹ χB⁻¹ ω ∧ ∀ f : WO B S → ℂ, IsThetaFunO ψ B S f →
        IsThetaFunO ψ (negSp S) B (fun y => f (adjM S B y)) ∧
        ∀ g₁ u, thetaKO ω (negGA S u) g₁ (fun y => f (adjM S B y)) = thetaKO ω₂ g₁ u f := by
  have hψ := H.std
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjSource (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjAdjoint ω₂),
    GlobalTheory.ConjWeil.weil_conjSource D ψ S B _ _ _ (GlobalTheory.ConjAdjWeil.isWeilDatumO_conjAdjoint D ψ B S _ _ ω₂ H),
    fun f hf => ?_⟩
  have e : (fun y : WO (negSp S) B => f (adjM S B y)) =
      GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S B) f) := by
    funext y; simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, GlobalTheory.AdjSwap.dagger_eq_adjM]
  rw [e]
  have h1 : IsThetaFunO ψ S B (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S B) f) :=
    ((GlobalTheory.AdjointPair.adjoint_clauses D ψ hψ B S).2.2.1 f).2 hf
  refine ⟨((GlobalTheory.CjNeg.theta_heis_neg D ψ hψ S B).1 _).2.2 h1, fun g₁ u => ?_⟩
  show GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjSource (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjAdjoint ω₂) (negGA S u, g₁) _ 0 = ω₂ (g₁, u) f 0
  rw [GlobalTheory.ConjWeil.conjSource_apply]
  simp only [MulEquiv.symm_apply_apply, GlobalTheory.ConjWeil.cj_id_cj_id]
  rw [GlobalTheory.TensorTargetRule.conjAdjoint_cj]
  simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, GlobalTheory.AdjSwap.dagger_eq_adjM, adjM_zero]

theorem attChr_eq {C : Type} [CommGroup C] (χ η : C) (n : ℕ) :
    Formalism.IndefR.Lift.attChr χ η n = χ / η ^ (n % 2) := by
  unfold Formalism.IndefR.Lift.attChr
  rcases Nat.even_or_odd n with h | h
  · rw [if_neg (Nat.not_odd_iff_even.2 h), Nat.even_iff.1 h]; simp
  · rw [if_pos h, Nat.odd_iff.1 h]; simp [div_eq_mul_inv]

theorem kerBig_eq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (t : T) (i j : Fin D.R.m)
    (ωA : GlobalTheory.Grid.WRep (G.V (.grid (↑i + 1) (↑j + 1))) (GlobalTheory.Doubling.hsum (G.V (.grid ↑i (↑j + 1))) (G.V (.grid (↑i + 1) ↑j)))),
    GlobalTheory.Grid.IsWeil W.ψ true _ _ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) ωA →
    ∀ (B : Frames G) (ρ : RealMatch W) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)), IsMatched B t ρ i j Θ Θ' →
    ∀ g g₁ u, kerBig W Θ g g₁ u = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV G i j g * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV₁ G t i j g₁ *
      thetaKO ωA u (GlobalTheory.SquareComm.blk _ _ (g, g₁)) (GlobalTheory.SquareDict.datumA W Θ) := by
  intro D T L sc G μ₀ hL W t i j ωA hA B ρ Θ Θ' hΘ g g₁ u
  have hd := isThetaFunO_of_isMatched hL W B ρ t i j Θ Θ' hΘ
  have h1 := W.om_is (.chi i (j + 1)) (show (↑i + 1 ≤ D.R.m ∧ ↑j + 1 ≤ D.R.m) by omega)
  have h2 := W.om_is (.mu t (i + 1) j) (show (↑i + 1 ≤ D.R.m ∧ ↑j + 1 ≤ D.R.m) by omega)
  obtain ⟨ω₂, hω₂, hadj⟩ := adjoint_exact h2
  have r : ∀ a b, a ≤ D.R.m → b ≤ D.R.m → (G.V (.grid a b)).rank = rankV D a b :=
    fun a b ha hb => (node_isV G hL (X := .grid a b) ⟨ha, hb⟩).rank
  have hi := i.2
  have hj := j.2
  obtain ⟨s, hs⟩ := odd_sLen D
  obtain ⟨t', ht⟩ := D.R.t_odd
  have pW : (G.V (.grid (i + 1) (j + 1))).rank % 2 = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps
    rw [r _ _ (by omega) (by omega), r _ _ (by omega) (by omega)]
    simp only [rankV, add_mul, one_mul]
    omega
  have pV : (G.V (.grid i (j + 1))).rank % 2 = (G.V (.grid (i + 1) j)).rank % 2 := by
    rw [r _ _ (by omega) (by omega), r _ _ (by omega) (by omega)]
    simp only [rankV, add_mul, one_mul]
    omega
  have cT : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j =
      G.chrT (.chi i (j + 1)) * (G.chrS (.mu t (i + 1) j))⁻¹ := by
    simp only [GridData.chrT, GridData.chrS, GridData.chr, attChr_eq, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha]
    rw [pV, mul_div_mul_right_eq_div, ← div_eq_mul_inv, div_div_div_cancel_right]
  have cV : G.chrS (.chi i (j + 1)) / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j = (L.eta ^ (2 * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j))⁻¹ := by
    simp only [GridData.chrS, GridData.chr, attChr_eq, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta]
    rw [pW, two_mul, pow_add, div_div, mul_left_comm, div_mul_cancel_left]
  have cV₁ : (G.chrT (.mu t (i + 1) j))⁻¹ / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j =
      (L.mu t (j + 1) * G.ch.chi (D.R.m - i))⁻¹ := by
    simp only [GridData.chrT, GridData.chr, attChr_eq, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta]
    rw [pW, inv_div, div_div, ← mul_assoc, div_mul_cancel_right]
  rw [cT] at hA
  let S := G.V (.grid (↑i + 1) (↑j + 1))
  let A := G.V (.grid (↑i) (↑j + 1))
  let Bs := G.V (.grid (↑i + 1) ↑j)
  have hA' : IsWeilDatumO W.ψ (negSp S) (GlobalTheory.Doubling.hsum A Bs) _ _ (ωA.toSgn true) := hA
  have e : ∀ d ∈ Θ.support, W.kerA (.right i (j + 1)) d.1.2 g u * W.kerA (.down t (i + 1) j) d.2 u g₁ =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV G i j g * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV₁ G t i j g₁ * ωA (u, GlobalTheory.SquareComm.blk A Bs (g, g₁))
        (box2 (S := negSp S) (A := A) (B := Bs) d.1.2 (fun y => d.2 (adjM S Bs y))) 0 := fun d hdm => by
    have k := seesaw_exact h1 hω₂ hA' (hd d hdm).1 (hadj _ (hd d hdm).2).1 (negGA S u) g g₁
      (GlobalTheory.RecDict.exists_isDetRoot D _ g).choose_spec (GlobalTheory.RecDict.exists_isDetRoot D _ g₁).choose_spec
    rw [(hadj _ (hd d hdm).2).2, cV, cV₁] at k
    exact k
  simp only [thetaKO, GlobalTheory.SquareDict.datumA, kerBig, Finsupp.sum, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hdm => ?_
  rw [e d hdm]
  ring

end GlobalTheory.SquareDict.ExactBig

end
