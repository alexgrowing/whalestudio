import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StageFactorNonvanishingScalars
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedSquareLocalMatching
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedSquareThetaIntegralsEq
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaParameterDictionaryBijective
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaFlipInvolutiveCorrespondence
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaFiniteDataMatchEachStage
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SquareIdentityOfMatching
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RegularisedIntegralComparison
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StageFactorNonvanishingScalarsStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.ConstRatio (Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.ThetaRegularizationComparison
open GlobalTheory.RegCompare in
theorem regularised_thetaInt_comparison_smul (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree) (hTA : GlobalTheory.SquareSt.ThetaIntegralsAgree)
    {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {W W₁ X : HSp D} {A : Fr W} {A₁ : Fr W₁} {B : Fr X}
    {α β : (AE D)ˣ →* Circle} (hT : IsTriple W W₁ X α β) {ν 𝓕 ν₁ 𝓕₁} (hν : IsHaarFD W ν 𝓕) (hν₁ : IsHaarFD W₁ ν₁ 𝓕₁)
    {ωA ωB Pi rf rl p p'} (hm : IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p') :
    ∃ c : ℂ, c ≠ 0 ∧ (∀ Φ ∈ algF ψ θ true A B, p Φ = 0 → thetaInt ωA ν 𝓕 Φ = 0) ∧
      ∀ Φ ∈ algF ψ θ true A B, ∀ Φ' ∈ algF ψ θ false A₁ B, ∀ g : ℂ, p Φ = g • p' Φ' →
        (∃ z, zdeg z ≠ 0 ∧ Intg ωB ν₁ 𝓕₁ (wop ωB z Φ') ∧
          zdeg z • thetaInt ωA ν 𝓕 Φ = (c * g) • thetaInt ωB ν₁ 𝓕₁ (wop ωB z Φ')) ∧
        (Intg ωB ν₁ 𝓕₁ Φ' → thetaInt ωA ν 𝓕 Φ = (c * g) • thetaInt ωB ν₁ 𝓕₁ Φ') := by
  obtain ⟨c, hc0, hc⟩ := _root_.GlobalTheory.RegCompare.regularised_integral_comparison hP hK hTA D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB Pi rf rl p p' hm
  have kill : ∀ Φ ∈ algF ψ θ true A B, p Φ = 0 → thetaInt ωA ν 𝓕 Φ = 0 := fun Φ hΦ h0 => by
    obtain ⟨z', -, -, -, -, hz'⟩ := hc 0 (Submodule.zero_mem _)
    have h2 := thetaInt_smul ωB ν₁ 𝓕₁ 0 0
    rw [zero_smul, zero_smul] at h2
    rw [hz' _ hΦ (by rw [h0, map_zero, smul_zero]), map_zero, h2, smul_zero]
  refine ⟨c, hc0, kill, fun Φ hΦ Φ' hΦ' g hg => ?_⟩
  obtain ⟨z, -, hz0, -, hzM, hz⟩ := hc Φ' hΦ'
  have hI : zdeg z • thetaInt ωA ν 𝓕 Φ = (c * g) • thetaInt ωB ν₁ 𝓕₁ (wop ωB z Φ') := by
    by_cases h0 : g = 0
    · rw [kill Φ hΦ (by rw [hg, h0, zero_smul]), h0, mul_zero, zero_smul, smul_zero]
    · have h1 := hz ((zdeg z * g⁻¹) • Φ) (Submodule.smul_mem _ _ hΦ)
        (by rw [map_smul, hg, smul_smul, mul_assoc, inv_mul_cancel₀ h0, mul_one])
      rw [thetaInt_smul] at h1
      rw [mul_comm c, mul_smul, ← h1, smul_smul, mul_left_comm, mul_inv_cancel₀ h0, mul_one]
  refine ⟨⟨z, hz0, intg_of_modInt hzM, hI⟩, fun hi => ?_⟩
  rw [thetaInt_wop_intg hν₁ (GlobalTheory.T.thetaKernel_leftInvariant_rational_unitary D ψ θ hθ W₁ X A₁ B _ _ ωB hm.weilB Φ' hΦ') hi z, smul_comm] at hI
  exact smul_right_injective _ hz0 hI
set_option maxHeartbeats 1000000 in
theorem regulator_constant_eq : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) → NumbersIn D.what₂.embLL S μ₀ → ∀ (ρ : RealMatch W), ρ.Tied → ∀ (i j : Fin D.R.m) (X : TriG G i j) (lam : T → ℂ),
    TopGrid W i j X → IsStageC W i j (pp D j) (qq D j) X → Factor X W.ψ W.θ lam →
    ∃ κ : T → ℂ, (∀ t, κ t ≠ 0 ∧ ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧ κ t = D.what₂.embLL ζ * κ μ₀) ∧
      ∀ (t : T) (c₀ : ℂ), RegConst W S.B ρ t i j c₀ → c₀ = κ t * lam t := by
  intro hP hK hM
  have hLM := _root_.GlobalTheory.T.twisted_local_factors_match hP.howeDualityReal hP hK hM
  have hTA := _root_.GlobalTheory.T.twisted_square_theta_integrals_eq hP hK hM
  obtain ⟨F1, H1⟩ := _root_.GlobalTheory.T.theta_parameter_dictionary_bijective hP
  obtain ⟨F2, H2⟩ := _root_.GlobalTheory.T.thetaFlip_involutive_correspondence hP hK hM
  obtain ⟨F3, H3⟩ := _root_.GlobalTheory.T.theta_finiteData_match_each_stage hP hK hM
  refine ⟨max F1 (max F2 F3), fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, H1⟩ := H1 ε CF (le_of_max_le_left hCF)
  obtain ⟨C2, x2, H2⟩ := H2 ε CF (le_of_max_le_left (le_of_max_le_right hCF))
  obtain ⟨C3, x3, H3⟩ := H3 ε CF (le_of_max_le_right (le_of_max_le_right hCF))
  refine ⟨max C1 (max C2 C3), max (max x1 x2) (max x3 ((12 : ℝ) ^ (5 / ε))), fun C hC D large₂ he hx hR T Lc μ₀ hL G => ?_⟩
  replace H1 := H1 C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left (le_of_max_le_left hx)) hR T Lc μ₀ hL G
  replace H2 := H2 C (le_of_max_le_left (le_of_max_le_right hC)) D large₂ he (le_of_max_le_right (le_of_max_le_left hx)) hR T Lc μ₀ hL G
  replace H3 := H3 C (le_of_max_le_right (le_of_max_le_right hC)) D large₂ he (le_of_max_le_left (le_of_max_le_right hx)) hR T Lc μ₀ hL G
  have hst : ∀ t, SquareStanding G t :=
    standing hR hR.size.2.1.eleven_le hL G
  intro W S hψ hN ρ hρ i j X lam hTG hSC hF
  have hbig : Node.InRange D.R.m (.grid (i + 1) (j + 1)) := ⟨i.2, j.2⟩
  have hsm : Node.InRange D.R.m (.grid i j) := ⟨i.2.le, j.2.le⟩
  obtain ⟨A, hA⟩ := exists_isGridFr W hbig
  obtain ⟨A₁, hA₁⟩ := exists_isGridFr W hsm
  obtain ⟨AV, hV⟩ := exists_isGridFr W (X := .grid i (j + 1)) ⟨i.2.le, j.2⟩
  obtain ⟨AV₁, hV₁⟩ := exists_isGridFr W (X := .grid (i + 1) j) ⟨i.2, j.2.le⟩
  obtain ⟨σ, σ', hσ⟩ := H1 W i j X hTG hSC A A₁ AV AV₁ hA hA₁ hV hV₁
  obtain ⟨κ, hκ, hflip⟩ := H2 W S hψ hN ρ i j X hTG hSC A A₁ AV AV₁ hA hA₁ hV hV₁
  replace H3 := H3 W i j _ _ _ _ _ X hSC A A₁ (frSum AV AV₁)
  have hIs := hSC.2.2.2.2.2.2.2
  have hrk : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j = rankV D i j % 2 := congrArg (· % 2) (Nat.add_right_cancel hSC.2.2.2.1)
  have eα : ∀ t, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j = Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2) := fun t => by
    rw [← hrk]; rfl
  have eβ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j = G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2) := by
    rw [← hrk]; rfl
  have hD := fun t => dict hL W t i j A A₁ AV AV₁ hA hA₁ hV hV₁
  have hT : ∀ t, IsTriple _ _ _ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) := fun t =>
    (hD t).1 (hst t) _ (exists_vol G hL t).choose_spec
  choose a b ha hb _ using (hT μ₀).gap
  obtain ⟨ι, -, hιA⟩ := GlobalTheory.SquareIdent.realA hL W i j A AV AV₁ hA hV hV₁
  obtain ⟨ι', -, hιB⟩ := GlobalTheory.SquareIdent.realB hL W i j A₁ AV AV₁ hA₁ hV hV₁
  obtain ⟨Pr, q, q', hq, hq', H⟩ := hLM D W.ψ W.θ W.ψ_std W.θ_is _ _ _ A A₁ (frSum AV AV₁) a b
  obtain ⟨hlam, PF, pF, pF', J, -, hJ, -, hI, hI', P₀, hP₀, hP₀i⟩ := hF
  obtain ⟨P₁, hP₁⟩ := hq (q' (σ' P₀))
  have key : ∀ t, ∃ l m : ℂ, m ≠ 0 ∧ pF (σ.symm P₁) = m • pF' P₀ ∧ (∀ x ∈ ρ.rel i j, q (ι x.1) = l • q' (ι' x.2)) ∧
      (∃ x ∈ ρ.rel i j, q (ι x.1) ≠ 0) ∧ ∀ c₀, RegConst W S.B ρ t i j c₀ → c₀ = l * m * κ t * lam t := by
    intro t
    obtain ⟨M, hM', a₀, τ, τ', n, Φ, hn, hfl, g, g₁, hne⟩ :=
      GlobalTheory.BigNZ.exists_integral_ne_zero hP.strongApproxSU hK hM hL W S.B ρ t i j (hst t)
    have wA : GlobalTheory.Grid.IsWeil W.ψ true _ _ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j)
        (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) (X.ω t) := by rw [eα, eβ]; exact hIs.weil t
    have wB : GlobalTheory.Grid.IsWeil W.ψ false _ _ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j)
        (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) (X.ω' t) := by rw [eα, eβ]; exact hIs.weil' t
    obtain ⟨Pi, rf, rl, p, p', hm, hcore⟩ := _root_.GlobalTheory.SquareIdent.square_identity_reduction hP.howeDualityReal hP hM hL W i j A A₁ AV AV₁ hA hA₁ hV hV₁ t S.B ρ M
      (hst t) hM' (hT t) _ _ wA wB
    obtain ⟨fτ, fτ', -⟩ := (hcore 0).choose_spec n Φ τ τ' hn hfl
    obtain ⟨Pf, r, r', e, -, -, hp, hp'⟩ := (H _ _ (hT t) fun τ =>
      ⟨GlobalTheory.SquareRel.hasInfExp_alpha G i j hL μ₀ t τ (ha τ), hb τ⟩).2 _ _ _ _ _ _ _ hm
    obtain ⟨ff, ff', hk, hk'⟩ := hσ t
    obtain ⟨γ, hγ0, hγ⟩ := H3 t ff ff' Pi rf rl p p' (by rw [← eα, ← eβ]; exact hm) Pr Pf q q' r r' e hq hq' hp hp'
    have hνA : IsHaarFD _ (M.ν _) (M.fd _) := (hM'.vtx _ hbig).haar_fund
    have hνB : IsHaarFD _ (M.ν _) (M.fd _) := (hM'.vtx _ hsm).haar_fund
    obtain ⟨s, hs0, hs⟩ := exists_haar_smul _ X.m _ hIs.meas.1 hνA.1
    obtain ⟨s', hs0', hs'⟩ := exists_haar_smul _ X.m' _ hIs.meas'.1 hνB.1
    have hsC : ((s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0
    have hsC' : ((s' : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0'
    obtain ⟨c, hc0, kill, hc⟩ := _root_.GlobalTheory.ThetaRegularizationComparison.regularised_thetaInt_comparison_smul hP hK hTA W.θ_is (hT t) hνA hνB hm
    have mA : fockF W.ψ W.θ true A (frSum AV AV₁) (X.f t) P₁ ∈ algF W.ψ W.θ true A (frSum AV AV₁) :=
      Submodule.subset_span ⟨_, _, ff, rfl⟩
    have mB : fockF W.ψ W.θ false A₁ (frSum AV AV₁) (X.f' t) (σ' P₀) ∈ algF W.ψ W.θ false A₁ (frSum AV AV₁) :=
      Submodule.subset_span ⟨_, _, ff', rfl⟩
    have cA := fun h => integral_change _ hIs.meas hνA hs
      (fun u => thetaKO (X.ω t) u h (fockF W.ψ W.θ true A (frSum AV AV₁) (X.f t) P₁))
      fun γ hγ u => GlobalTheory.SquareIdent.thetaKO_left_neg W.θ_is _ _ wA mA γ hγ u h
    have cB := fun h => integral_change _ hIs.meas' hνB hs'
      (fun u => thetaKO (X.ω' t) u h (fockF W.ψ W.θ false A₁ (frSum AV AV₁) (X.f' t) (σ' P₀)))
      fun γ hγ u => GlobalTheory.T.thetaKernel_leftInvariant_rational_unitary D W.ψ W.θ W.θ_is _ _ _ _ _ _ _ wB _ mB γ hγ u h
    have iB : GlobalTheory.RegCompare.Intg (X.ω' t) (M.ν _) (M.fd _) (fockF W.ψ W.θ false A₁ (frSum AV AV₁) (X.f' t) (σ' P₀)) :=
      fun h => (cB h).1 (by simpa only [← hk'] using hP₀i t h)
    have eA : thetaInt (X.ω t) (M.ν _) (M.fd _) (fockF W.ψ W.θ true A (frSum AV AV₁) (X.f t) P₁) =
        J t ((((s : ℝ) : ℂ) * lam t) • pF (σ.symm P₁)) := by
      rw [map_smul, mul_smul, ← hI]
      funext h
      refine (cA h).2.trans ?_
      simp only [_root_.Pi.smul_apply, smul_eq_mul, Tri.I, hk, LinearEquiv.apply_symm_apply]
    have eB : thetaInt (X.ω' t) (M.ν _) (M.fd _) (fockF W.ψ W.θ false A₁ (frSum AV AV₁) (X.f' t) (σ' P₀)) =
        J t (((s' : ℝ) : ℂ) • pF' P₀) := by
      rw [map_smul, ← hI' t P₀ (hP₀i t)]
      funext h
      refine (cB h).2.trans ?_
      simp only [_root_.Pi.smul_apply, smul_eq_mul, Tri.I', hk']
    have hne' : p' (fockF W.ψ W.θ false A₁ (frSum AV AV₁) (X.f' t) (σ' P₀)) ≠ 0 := fun h0 => by
      have h1 := (hc 0 (Submodule.zero_mem _) _ mB 1 (by rw [h0, map_zero, smul_zero])).2 iB
      rw [kill 0 (Submodule.zero_mem _) (map_zero _), eB, ← map_smul, ← map_zero (J t)] at h1
      have h2 := (hJ t h1).symm
      simp [hc0, hs0', hP₀] at h2
    have hstd : p (fockF W.ψ W.θ true A (frSum AV AV₁) (X.f t) P₁) =
        γ • p' (fockF W.ψ W.θ false A₁ (frSum AV AV₁) (X.f' t) (σ' P₀)) := by
      rw [hp _ ff, hp' _ ff', hP₁, hγ, TensorProduct.tmul_smul, map_smul]
    have hu : (((s : ℝ) : ℂ) * lam t) • pF (σ.symm P₁) = (c * γ) • ((s' : ℝ) : ℂ) • pF' P₀ := by
      have h1 := (hc _ mA _ mB γ hstd).2 iB
      rw [eA, eB, ← map_smul (J t)] at h1
      exact hJ t h1
    have hy : q' (σ' P₀) ≠ 0 := fun h0 => hne' (by rw [hp' _ ff', h0, TensorProduct.zero_tmul, map_zero])
    have hfp := hflip t M hM' s s' hs hs' Pi rf rl p p' hm n Φ τ τ' hn hfl P₁ (σ' P₀) γ hne' hstd
    rw [hp _ fτ, hp' _ fτ', hP₁, ← map_smul, ← map_smul, ← TensorProduct.tmul_smul, ← TensorProduct.tmul_smul] at hfp
    have hr := tmul_cancel_left hy (e.injective hfp)
    set δ : ℂ := ((s : ℝ) : ℂ)⁻¹ * (κ t * ((s' : ℝ) : ℂ) * γ) with hδ
    have hδ0 : δ ≠ 0 := mul_ne_zero (inv_ne_zero hsC) (mul_ne_zero (mul_ne_zero (hκ t).1 hsC') hγ0)
    have hr' : r (datumA W τ) = δ • r' (datumB W τ') := by
      rw [hδ, mul_smul, ← hr, smul_smul, inv_mul_cancel₀ hsC, one_smul]
    obtain ⟨c₁, hc₁⟩ := hρ i j A A₁ AV AV₁ hA hA₁ hV hV₁ t _ _ Pi rf rl p p' hm S.B n Φ τ τ' hn hfl
    obtain ⟨b', hb'⟩ := ρ.onto_big i j (toTens a₀)
    obtain ⟨b₀, rfl⟩ : ∃ b₀ : PolT G (routeSmall t i j) →₀ ℂ, toTens b₀ = b' := toTens_surjective b'
    have hΘ : IsMatched S.B t ρ i j (tensT W a₀ τ) (tensT W b₀ τ') := ⟨a₀, b₀, τ, τ', n, Φ, hb', hn, hfl, rfl, rfl⟩
    obtain ⟨ξ, hξ⟩ := (hD t).2 _ _ wA wB
    obtain ⟨aA, aB, -, kB, jA, jB⟩ := hξ S.B ρ _ _ hΘ
    have hp0 : p (datumA W (tensT W a₀ τ)) ≠ 0 := fun h0 => hne (by rw [jA, kill _ aA h0]; exact mul_zero _)
    have hp1 := hp0
    rw [hιA t S.B ρ n Φ τ τ' hfl, hp _ fτ] at hp1
    have hx0 : q (ι (toTens a₀)) ≠ 0 := fun h0 => hp1 (by rw [h0, TensorProduct.zero_tmul, map_zero])
    have hr0 : r' (datumB W τ') ≠ 0 := fun h0 => hp1 (by rw [hr', h0, smul_zero, TensorProduct.tmul_zero, map_zero])
    have hm0 : ((s : ℝ) : ℂ) * lam t ≠ 0 := mul_ne_zero hsC (hlam t)
    refine ⟨δ⁻¹ * c₁, (((s : ℝ) : ℂ) * lam t)⁻¹ * (c * γ * ((s' : ℝ) : ℂ)),
      mul_ne_zero (inv_ne_zero hm0) (mul_ne_zero (mul_ne_zero hc0 hγ0) hsC'), ?_, ?_, ⟨_, hb', hx0⟩, fun c₀ h₀ => ?_⟩
    · rw [mul_smul, mul_smul, ← hu, smul_smul, inv_mul_cancel₀ hm0, one_smul]
    · rintro ⟨x, y⟩ hxy
      obtain ⟨x, rfl⟩ : ∃ x₀ : PolT G (routeBig t i j) →₀ ℂ, toTens x₀ = x := toTens_surjective x
      obtain ⟨y, rfl⟩ : ∃ y₀ : PolT G (routeSmall t i j) →₀ ℂ, toTens y₀ = y := toTens_surjective y
      have h1 := hc₁ x y hxy
      rw [hιA t S.B ρ n Φ τ τ' hfl, hιB t S.B ρ n Φ τ τ' hfl, hp _ fτ, hp' _ fτ', hr', ← map_smul e, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul', TensorProduct.smul_tmul'] at h1
      have h2 := tmul_cancel_right hr0 (e.injective h1)
      show q (ι (toTens x)) = (δ⁻¹ * c₁) • q' (ι' (toTens y))
      rw [mul_smul, ← h2, smul_smul, inv_mul_cancel₀ hδ0, one_smul]
    · obtain ⟨z, hz0, hzi, hz⟩ := (hc _ aA _ aB c₁ (hc₁ a₀ b₀ hb')).1
      have ez : zact (X.ω' t) z (datumB W (tensT W b₀ τ')) = GlobalTheory.RegCompare.wop (X.ω' t) z (datumB W (tensT W b₀ τ')) :=
        (GlobalTheory.RegCompare.wop_apply _ _ _).symm
      have h1 : c₀ = c * c₁ := by
        refine eq_of_regConst hK hL (hst t) hM' hΘ hne hz0 ?_ ?_ h₀
        · rw [funext (kB z g g₁), ez]
          exact (hzi _).const_mul _
        · rw [jA, jB, ez]
          have := congrFun hz (blk _ _ (g, g₁))
          simp only [_root_.Pi.smul_apply, smul_eq_mul] at this
          linear_combination ξ (g, g₁) * this
      have := hlam t
      have := (hκ t).1
      rw [h1, hδ]
      field_simp
  choose l m hm0 hm hl hx hc using key
  have em : ∀ t, m t = m μ₀ := fun t => smul_left_injective ℂ hP₀ ((hm t).symm.trans (hm μ₀))
  obtain ⟨x, hxr, hx0⟩ := hx μ₀
  have hy0 : q' (ι' x.2) ≠ 0 := fun h => hx0 (by rw [hl μ₀ x hxr, h, smul_zero])
  have hl0 : l μ₀ ≠ 0 := fun h => hx0 (by rw [hl μ₀ x hxr, h, zero_smul])
  have el : ∀ t, l t = l μ₀ := fun t => smul_left_injective ℂ hy0 ((hl t x hxr).symm.trans (hl μ₀ x hxr))
  refine ⟨fun t => l μ₀ * m μ₀ * κ t, fun t => ⟨mul_ne_zero (mul_ne_zero hl0 (hm0 μ₀)) (hκ t).1, ?_⟩, fun t c₀ h => ?_⟩
  · obtain ⟨ζ, h1, h2⟩ := (hκ t).2
    exact ⟨ζ, h1, by dsimp only; rw [h2]; ring⟩
  · rw [hc t c₀ h, em t, el t]
end GlobalTheory.ThetaRegularizationComparison
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.ConstRatio (Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regConst_eq_away_unit_mul_factor : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) → NumbersIn D.what₂.embLL S μ₀ → ∀ (ρ : RealMatch W), ρ.Tied → ∀ (i j : Fin D.R.m) (X : TriG G i j) (lam : T → ℂ),
    TopGrid W i j X → IsStageC W i j (pp D j) (qq D j) X → Factor X W.ψ W.θ lam →
    ∃ κ : T → ℂ, (∀ t, κ t ≠ 0 ∧ ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧ κ t = D.what₂.embLL ζ * κ μ₀) ∧
      ∀ (t : T) (c₀ : ℂ), RegConst W S.B ρ t i j c₀ → c₀ = κ t * lam t := by
  first | exact @_root_.GlobalTheory.ThetaRegularizationComparison.regulator_constant_eq | exact _root_.GlobalTheory.ThetaRegularizationComparison.regulator_constant_eq | (intros; apply _root_.GlobalTheory.ThetaRegularizationComparison.regulator_constant_eq <;> assumption)
end
