import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealMatchingTiedRegularizationConstant
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedSquareLocalMatching
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedWeilRepresentationConvergence
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedSquareThetaIntegralsEq
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RegularisedIntegralComparison
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SquareIdentityOfMatching
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaKernelMatchOnOppositeParabolic
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RankPolarizationPiLeAleph0
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealMatchingTiedRegularizationConstantStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.ChainFr Matrix
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.GridFrameExistence
open GlobalTheory.SquareComm GlobalTheory.SquareDict GlobalTheory.SquareAgree GlobalTheory.Grid
variable {D : D7}
theorem tied_pair_scalar_match (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hL : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    (hθ : IsInfFam θ) {W W₁ X : HSp D} {A : Fr W} {A₁ : Fr W₁} {B : Fr X} {α β : (AE D)ˣ →* Circle} (hT : IsTriple W W₁ X α β)
    {ν 𝓕 ν₁ 𝓕₁} (hν : IsHaarFD W ν 𝓕) (hν₁ : IsHaarFD W₁ ν₁ 𝓕₁) {ωA ωB Pi₀ rf₀ rl₀ p₀ p₀' Pi rf rl p p'}
    (h₀ : IsMatch ψ θ A A₁ B α β ωA ωB Pi₀ rf₀ rl₀ p₀ p₀') (hM : IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p') :
    ∃ s : ℂ, s ≠ 0 ∧ ∀ Φ ∈ algF ψ θ true A B, ∀ Φ' ∈ algF ψ θ false A₁ B, p₀ Φ = p₀' Φ' → p' Φ' = s • p Φ := by
  obtain ⟨e, Bs, Γ, Xc, om, om', cA, cB, hO, hTD⟩ :=
    GlobalTheory.T.exists_placewise_seesaw_triple_over_hermitian D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB hM.weilA hM.weilB
  obtain ⟨R, Rf, hR⟩ := hL D.host.F D.host.E D.sp.cm.sig Bs W.rank W₁.rank Γ Xc om om' hTD
  have hRe := hP.howeDualityReal
  have kA : ∀ Φ ∈ algF ψ θ true A B, p Φ = 0 ↔ p₀ Φ = 0 := fun Φ hΦ => by
    obtain ⟨ΦD, hΦD, hD⟩ := hO.algA Φ hΦ
    exact (_root_.GlobalTheory.SquareAgree.theta_kernel_match_on_parabolic hRe hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR
      Pi rf rl p p' hM Φ hΦ ΦD hΦD hD).trans (_root_.GlobalTheory.SquareAgree.theta_kernel_match_on_parabolic hRe hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om'
      cA cB hθ hT hO hTD R Rf hR Pi₀ rf₀ rl₀ p₀ p₀' h₀ Φ hΦ ΦD hΦD hD).symm
  have kB : ∀ Φ ∈ algF ψ θ false A₁ B, p' Φ = 0 ↔ p₀' Φ = 0 := fun Φ hΦ => by
    obtain ⟨ΦD, hΦD, hD⟩ := hO.algB Φ hΦ
    exact (_root_.GlobalTheory.SquareAgree.theta_kernel_match_on_opposite_parabolic hRe hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR
      Pi rf rl p p' hM Φ hΦ ΦD hΦD hD).trans (_root_.GlobalTheory.SquareAgree.theta_kernel_match_on_opposite_parabolic hRe hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc
      om om' cA cB hθ hT hO hTD R Rf hR Pi₀ rf₀ rl₀ p₀ p₀' h₀ Φ hΦ ΦD hΦD hD).symm
  let S : Submodule ℂ (Pi × Pi) :=
    { carrier := {x | ∃ Φ ∈ algF ψ θ true A B, ∃ Φ' ∈ algF ψ θ false A₁ B, p₀ Φ = p₀' Φ' ∧ x = (p Φ, p' Φ')}
      add_mem' := by
        rintro _ _ ⟨Φ, hΦ, Φ', hΦ', h, rfl⟩ ⟨Ψ, hΨ, Ψ', hΨ', k, rfl⟩
        exact ⟨Φ + Ψ, add_mem hΦ hΨ, Φ' + Ψ', add_mem hΦ' hΨ', by rw [map_add, map_add, h, k],
          Prod.ext (map_add p Φ Ψ).symm (map_add p' Φ' Ψ').symm⟩
      zero_mem' := ⟨0, zero_mem _, 0, zero_mem _, by rw [map_zero, map_zero],
        Prod.ext (map_zero p).symm (map_zero p').symm⟩
      smul_mem' := by
        rintro c _ ⟨Φ, hΦ, Φ', hΦ', h, rfl⟩
        exact ⟨c • Φ, Submodule.smul_mem _ c hΦ, c • Φ', Submodule.smul_mem _ c hΦ', by rw [map_smul, map_smul, h],
          Prod.ext (map_smul p c Φ).symm (map_smul p' c Φ').symm⟩ }
  obtain ⟨s, hs, H⟩ := eq_smul_of_stable_graph D X Pi rf rl hM.irred
    (_root_.GlobalTheory.SquareAgree.rank_polarization_pi_le_aleph0 hRe hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR
      Pi rf rl p p' hM) S
    (by
      rintro g hg _ ⟨Φ, hΦ, Φ', hΦ', h, rfl⟩
      refine ⟨_, hM.mapA.stabX.1 g hg Φ hΦ, _, hM.mapB.stabX.1 g hg Φ' hΦ', ?_, ?_⟩
      · rw [h₀.mapA.eqf g hg Φ hΦ, h₀.mapB.eqf g hg Φ' hΦ', h]
      · rw [hM.mapA.eqf g hg Φ hΦ, hM.mapB.eqf g hg Φ' hΦ'])
    (by
      rintro τ Y hY _ ⟨Φ, hΦ, Φ', hΦ', h, rfl⟩
      obtain ⟨Ψ, hΨ, hd⟩ := hM.mapA.stabX.2 τ Y hY Φ hΦ
      obtain ⟨Ψ', hΨ', hd'⟩ := hM.mapB.stabX.2 τ Y hY Φ' hΦ'
      refine ⟨Ψ, hΨ, Ψ', hΨ', ?_, ?_⟩
      · rw [h₀.mapA.eql τ Y hY Φ hΦ Ψ hΨ hd, h₀.mapB.eql τ Y hY Φ' hΦ' Ψ' hΨ' hd', h]
      · rw [hM.mapA.eql τ Y hY Φ hΦ Ψ hΨ hd, hM.mapB.eql τ Y hY Φ' hΦ' Ψ' hΨ' hd'])
    (by
      rintro x ⟨Φ, hΦ, Φ', hΦ', h, hx⟩
      obtain ⟨rfl, h0⟩ := Prod.mk.inj hx
      exact (kA Φ hΦ).2 (h.trans ((kB Φ' hΦ').1 h0.symm)))
    (by
      rintro y ⟨Φ, hΦ, Φ', hΦ', h, hy⟩
      obtain ⟨h0, rfl⟩ := Prod.mk.inj hy
      exact (kB Φ' hΦ').2 (h.symm.trans ((kA Φ hΦ).1 h0.symm)))
    (by
      intro x
      obtain ⟨Φ, hΦ, rfl⟩ : x ∈ (algF ψ θ true A B).map p := hM.mapA.onto ▸ Submodule.mem_top
      obtain ⟨Φ', hΦ', h⟩ : p₀ Φ ∈ (algF ψ θ false A₁ B).map p₀' := h₀.mapB.onto ▸ Submodule.mem_top
      exact ⟨p' Φ', Φ, hΦ, Φ', hΦ', h.symm, rfl⟩)
  exact ⟨s, hs, fun Φ hΦ Φ' hΦ' h => H _ _ ⟨Φ, hΦ, Φ', hΦ', h, rfl⟩⟩
open GlobalTheory.SquareIdent in
theorem tied_pair_square_relation (hH : GlobalTheory.Published.HoweDualityReal) (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hTL : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching)
    (hLM : GlobalTheory.SquareSt.LocalMatching) {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (hst : ∀ t, SquareStanding G t) (W : G.Weil) (i j : Fin D.R.m) :
    ∃ r : Submodule ℂ (PolRoute G (.grid i (j + 1)) (.grid (i + 1) (j + 1)) (.grid (i + 1) j) ×
      PolRoute G (.grid i (j + 1)) (.grid i j) (.grid (i + 1) j)), (∀ a, ∃ b, (a, b) ∈ r) ∧ (∀ b, ∃ a, (a, b) ∈ r) ∧ r ≠ ⊤ ∧
    ∀ (ρ : RealMatch W) (A : Fr (G.V (.grid (i + 1) (j + 1)))) (A₁ : Fr (G.V (.grid i j))) (AV : Fr (G.V (.grid i (j + 1))))
      (AV₁ : Fr (G.V (.grid (i + 1) j))), IsGridFr W _ A → IsGridFr W _ A₁ → IsGridFr W _ AV → IsGridFr W _ AV₁ →
      ∀ (t : T) ωA ωB Pi rf rl p p', IsMatch W.ψ W.θ A A₁ (frSum AV AV₁) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j)
        (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) ωA ωB Pi rf rl p p' →
      ∀ B : Frames G, ∃ c : ℂ, ∀ n Φ τ τ', (∀ w ∈ locPl G t, depthAt G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w)) →
        HasFlip B t ρ i j n Φ τ τ' → ∀ (a : PolT G (routeBig t i j) →₀ ℂ) (b : PolT G (routeSmall t i j) →₀ ℂ),
          (toTens a, toTens b) ∈ r → p (datumA W (tensT W a τ)) = c • p' (datumB W (tensT W b τ')) := by
  obtain ⟨A, hA⟩ := exists_isGridFr W (X := .grid (i + 1) (j + 1)) ⟨i.2, j.2⟩
  obtain ⟨A₁, hA₁⟩ := exists_isGridFr W (X := .grid i j) ⟨i.2.le, j.2.le⟩
  obtain ⟨AV, hV⟩ := exists_isGridFr W (X := .grid i (j + 1)) ⟨i.2.le, j.2⟩
  obtain ⟨AV₁, hV₁⟩ := exists_isGridFr W (X := .grid (i + 1) j) ⟨i.2, j.2.le⟩
  choose M hM using exists_vol G hL
  have hT := fun t => (dict hL W t i j A A₁ AV AV₁ hA hA₁ hV hV₁).1 (hst t) (M t) (hM t)
  choose a b ha hb _ using (hT μ₀).gap
  obtain ⟨ι, hι, hιA⟩ := realA hL W i j A AV AV₁ hA hV hV₁
  obtain ⟨ι', hι', hιB⟩ := realB hL W i j A₁ AV AV₁ hA₁ hV hV₁
  obtain ⟨Pr, q, q', hq, hq', H⟩ := hLM D W.ψ W.θ W.ψ_std W.θ_is _ _ _ A A₁ (frSum AV AV₁) a b
  have hexp : ∀ t τ, HasInfExp D (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) τ (a τ) ∧ HasInfExp D (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) τ (b τ) :=
    fun t τ => ⟨GlobalTheory.SquareRel.hasInfExp_alpha G i j hL μ₀ t τ (ha τ), hb τ⟩
  have hqi : Function.Surjective (q ∘ₗ ι) := hq.comp hι
  have hqi' : Function.Surjective (q' ∘ₗ ι') := hq'.comp hι'
  haveI hPr : Nontrivial Pr := by
    obtain ⟨⟨ωA, ωB, Pi, rf, rl, p, p', hm⟩, H2⟩ := H _ _ (hT μ₀) (hexp μ₀)
    obtain ⟨Pf, -, -, e, -⟩ := H2 ωA ωB Pi rf rl p p' hm
    haveI : Nontrivial Pi := hm.irred.1
    exact GlobalTheory.SquareRel.nontrivial_of_tensor e
  refine ⟨GlobalTheory.SquareRel.relOf (q ∘ₗ ι) (q' ∘ₗ ι'), GlobalTheory.SquareRel.relOf_fst hqi', GlobalTheory.SquareRel.relOf_snd hqi,
    GlobalTheory.SquareRel.relOf_ne_top hqi, ?_⟩
  intro ρ A' A₁' AV' AV₁' hA' hA₁' hV' hV₁' t ωA ωB Pi rf rl p p' hm B
  obtain rfl := gridFr_unique hA hA'
  obtain rfl := gridFr_unique hA₁ hA₁'
  obtain rfl := gridFr_unique hV hV'
  obtain rfl := gridFr_unique hV₁ hV₁'
  obtain ⟨Pi₀, rf₀, rl₀, p₀, p₀', hm₀, hcore⟩ := _root_.GlobalTheory.SquareIdent.square_identity_reduction hH hP hTL hL W i j A A₁ AV AV₁ hA hA₁ hV hV₁ t B ρ (M t) (hst t) (hM t)
    (hT t) ωA ωB hm.weilA hm.weilB
  obtain ⟨Pf, r, r', e, -, -, hp, hp'⟩ := (H _ _ (hT t) (hexp t)).2 ωA ωB Pi₀ rf₀ rl₀ p₀ p₀' hm₀
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : Pr)
  obtain ⟨P₀, rfl⟩ := hq x₀
  obtain ⟨P₀', hP₀⟩ := hcore P₀
  obtain ⟨lam, hlam⟩ := exists_scalar (Q := Pf) hx₀ (q' P₀')
  have hbig : Node.InRange D.R.m (.grid (i + 1) (j + 1)) := ⟨i.2, j.2⟩
  have hsm : Node.InRange D.R.m (.grid i j) := ⟨i.2.le, j.2.le⟩
  obtain ⟨s, hs, hs'⟩ := _root_.GlobalTheory.GridFrameExistence.tied_pair_scalar_match hP hTL W.θ_is (hT t) ((hM t).vtx _ hbig).haar_fund ((hM t).vtx _ hsm).haar_fund hm₀ hm
  refine ⟨s⁻¹ * lam, fun n Φ τ τ' hn hF a' b' hab => ?_⟩
  obtain ⟨f1, f2, f3⟩ := hP₀ n Φ τ τ' hn hF
  rw [hp _ f1, hp' _ f2] at f3
  have h1 := hlam _ _ (e.injective f3)
  have h2 : q (ι (toTens a')) = q' (ι' (toTens b')) := hab
  rw [hιA t B ρ n Φ τ τ' hF, hιB t B ρ n Φ τ τ' hF]
  have h3 := hs' _ (Submodule.subset_span ⟨_, ι (toTens a'), f1, rfl⟩)
    _ (Submodule.smul_mem _ lam (Submodule.subset_span ⟨_, ι' (toTens b'), f2, rfl⟩))
    (by rw [map_smul, hp _ f1, hp' _ f2, h1, h2, TensorProduct.tmul_smul, map_smul])
  rw [map_smul] at h3
  rw [mul_smul, h3, smul_smul, inv_mul_cancel₀ hs, one_smul]
open GlobalTheory.SquareIdent in
theorem tied_pair_regularization_constant (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree) (hWC : GlobalTheory.SquareSt.WeilConvergence)
    (hTA : GlobalTheory.SquareSt.ThetaIntegralsAgree) {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (hst : SquareStanding G t) (i j : Fin D.R.m)
    {A : Fr (G.V (.grid (i + 1) (j + 1)))} {A₁ : Fr (G.V (.grid i j))} {AV : Fr (G.V (.grid i (j + 1)))}
    {AV₁ : Fr (G.V (.grid (i + 1) j))} (hA : IsGridFr W _ A) (hA₁ : IsGridFr W _ A₁) (hV : IsGridFr W _ AV) (hV₁ : IsGridFr W _ AV₁)
    {ωA ωB Pi rf rl p p'} (hm : IsMatch W.ψ W.θ A A₁ (frSum AV AV₁) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j)
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) ωA ωB Pi rf rl p p') {lam : ℂ}
    (hlam : ∀ Θ Θ', IsMatched B t ρ i j Θ Θ' → p (datumA W Θ) = lam • p' (datumB W Θ')) :
    ∃ c : ℂ, GlobalTheory.SqTower.RegConst W B ρ t i j c := by
  have hD := dict hL W t i j A A₁ AV AV₁ hA hA₁ hV hV₁
  obtain ⟨M₁, hM₁⟩ := exists_vol G hL t
  have hT := hD.1 hst M₁ hM₁
  have hbig : Node.InRange D.R.m (.grid (i + 1) (j + 1)) := ⟨i.2, j.2⟩
  have hsm : Node.InRange D.R.m (.grid i j) := ⟨i.2.le, j.2.le⟩
  obtain ⟨c₀, -, hc₀⟩ := _root_.GlobalTheory.RegCompare.regularised_integral_comparison hP hK hTA D W.ψ W.θ W.θ_is _ _ _ A A₁
    (frSum AV AV₁) _ _ hT _ _ _ _ (hM₁.vtx _ hbig).haar_fund (hM₁.vtx _ hsm).haar_fund ωA ωB Pi rf rl p p' hm
  obtain ⟨κ, hκ⟩ := hD.2 ωA ωB hm.weilA hm.weilB
  refine ⟨lam * c₀, fun M hM Θ Θ' hΘ g g₁ => ?_⟩
  obtain ⟨aA, aB, kA, kB, iA, iB⟩ := hκ B ρ Θ Θ' hΘ
  have hconv := GlobalTheory.T.bigRoute_kernel_integrableOn_unitary_quotient hWC hL W B ρ t i j (GlobalTheory.T.squareThetaTripleHypotheses_of_standing hL W t i j hst) M hM Θ Θ' hΘ g₁ g
  have hpp := hlam Θ Θ' hΘ
  obtain ⟨z, -, hz0, hzS, hzM, hz⟩ := hc₀ _ aB
  have ez : zact ωB z (datumB W Θ') = GlobalTheory.RegCompare.wop ωB z (datumB W Θ') := (GlobalTheory.RegCompare.wop_apply _ _ _).symm
  have hI : zdeg z • thetaInt ωA (M₁.ν _) (M₁.fd _) (datumA W Θ) =
      (lam * c₀) • thetaInt ωB (M₁.ν _) (M₁.fd _) (GlobalTheory.RegCompare.wop ωB z (datumB W Θ')) := by
    by_cases h0 : lam = 0
    · obtain ⟨z', -, -, -, -, hz'⟩ := hc₀ 0 (Submodule.zero_mem _)
      have h1 := hz' _ aA (by rw [hpp, h0, zero_smul, map_zero, smul_zero])
      have h2 := GlobalTheory.RegCompare.thetaInt_smul ωB (M₁.ν _) (M₁.fd _) 0 0
      rw [zero_smul, zero_smul] at h2
      rw [h1, map_zero, h2, h0, zero_mul, zero_smul, smul_zero, smul_zero]
    · have h1 := hz ((zdeg z * lam⁻¹) • datumA W Θ) (Submodule.smul_mem _ _ aA)
        (by rw [map_smul, hpp, smul_smul, mul_assoc, inv_mul_cancel₀ h0, mul_one])
      rw [GlobalTheory.RegCompare.thetaInt_smul] at h1
      rw [mul_smul, ← h1, smul_smul, mul_left_comm, mul_inv_cancel₀ h0, mul_one]
  have invA : ∀ γ ∈ GQ (G.V (.grid (i + 1) (j + 1))), ∀ u, kerBig W Θ g g₁ (γ * u) = kerBig W Θ g g₁ u := fun γ hγ u => by
    rw [kA, kA, thetaKO_left_neg W.θ_is _ _ hm.weilA aA γ hγ]
  have invB : ∀ γ ∈ GQ (G.V (.grid i j)), ∀ u, translates z (kerSmall W Θ' g g₁) (γ * u) = translates z (kerSmall W Θ' g g₁) u :=
    fun γ hγ u => by
      rw [kB, kB, ez, GlobalTheory.SquareComm.ThetaLeft.main D W.ψ W.θ W.θ_is _ _ _ _ _ _ ωB hm.weilB _ hzS γ hγ]
  refine ⟨z, hz0, ⟨hconv, ?_⟩, ?_⟩
  · rw [GlobalTheory.VolIdent.vol_integrableOn_iff M M₁ hM hM₁ hsm _ invB, funext (kB z g g₁), ez]
    exact (GlobalTheory.RegCompare.intg_of_modInt hzM _).const_mul _
  · rw [GlobalTheory.VolIdent.vol_setIntegral_eq M M₁ hM hM₁ hbig _ invA, GlobalTheory.VolIdent.vol_setIntegral_eq M M₁ hM hM₁ hsm _ invB,
      iA, iB, ez]
    have := congrFun hI (blk _ _ (g, g₁))
    simp only [_root_.Pi.smul_apply, smul_eq_mul] at this
    linear_combination κ (g, g₁) * this
theorem exists_tied_pair_of_standing_hypotheses (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree)
    (hTL : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching) {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (hst : ∀ t, SquareStanding G t) (W : G.Weil) (rm : RealMatch W) :
    ∃ ρ : RealMatch W, ρ.vX = rm.vX ∧ ρ.vT = rm.vT ∧ ρ.Tied ∧
      ∀ (B : Frames G) (i j : Fin D.R.m) (t : T), ∃ c : ℂ, GlobalTheory.SqTower.RegConst W B ρ t i j c := by
  have hLM := _root_.GlobalTheory.T.twisted_local_factors_match hP.howeDualityReal hP hK hTL
  choose r hr1 hr2 hr3 hr4 using _root_.GlobalTheory.GridFrameExistence.tied_pair_square_relation hP.howeDualityReal hP hTL hLM hL hst W
  let rel' : ∀ i j : ℕ, Submodule ℂ (PolRoute G (.grid i (j + 1)) (.grid (i + 1) (j + 1)) (.grid (i + 1) j) ×
      PolRoute G (.grid i (j + 1)) (.grid i j) (.grid (i + 1) j)) := fun i j =>
    if h : i < D.R.m ∧ j < D.R.m then r ⟨i, h.1⟩ ⟨j, h.2⟩ else rm.rel i j
  have e : ∀ i j : Fin D.R.m, rel' i j = r i j := fun i j => dif_pos ⟨i.2, j.2⟩
  let ρ : RealMatch W := { rm with
    rel := rel'
    onto_big := fun i j a => by
      by_cases h : i < D.R.m ∧ j < D.R.m
      · simp only [rel', dif_pos h]; exact hr1 ⟨i, h.1⟩ ⟨j, h.2⟩ a
      · simp only [rel', dif_neg h]; exact rm.onto_big i j a
    onto_small := fun i j b => by
      by_cases h : i < D.R.m ∧ j < D.R.m
      · simp only [rel', dif_pos h]; exact hr2 ⟨i, h.1⟩ ⟨j, h.2⟩ b
      · simp only [rel', dif_neg h]; exact rm.onto_small i j b
    proper := fun i j => by
      by_cases h : i < D.R.m ∧ j < D.R.m
      · simp only [rel', dif_pos h]; exact hr3 ⟨i, h.1⟩ ⟨j, h.2⟩
      · simp only [rel', dif_neg h]; exact rm.proper i j }
  refine ⟨ρ, rfl, rfl, fun i j A A₁ AV AV₁ hA hA₁ hV hV₁ t ωA ωB Pi rf rl p p' hm B n Φ τ τ' hn hF => ?_, fun B i j t => ?_⟩
  · obtain ⟨c, hc⟩ := hr4 i j ρ A A₁ AV AV₁ hA hA₁ hV hV₁ t ωA ωB Pi rf rl p p' hm B
    exact ⟨c, fun a b hab => hc n Φ τ τ' hn hF a b (e i j ▸ hab)⟩
  obtain ⟨A, hA⟩ := exists_isGridFr W (X := .grid (i + 1) (j + 1)) ⟨i.2, j.2⟩
  obtain ⟨A₁, hA₁⟩ := exists_isGridFr W (X := .grid i j) ⟨i.2.le, j.2.le⟩
  obtain ⟨AV, hV⟩ := exists_isGridFr W (X := .grid i (j + 1)) ⟨i.2.le, j.2⟩
  obtain ⟨AV₁, hV₁⟩ := exists_isGridFr W (X := .grid (i + 1) j) ⟨i.2, j.2.le⟩
  obtain ⟨M, hM⟩ := exists_vol G hL t
  have hT := (dict hL W t i j A A₁ AV AV₁ hA hA₁ hV hV₁).1 (hst t) M hM
  choose a b ha hb _ using hT.gap
  obtain ⟨Pr, q, q', -, -, H⟩ := hLM D W.ψ W.θ W.ψ_std W.θ_is _ _ _ A A₁ (frSum AV AV₁) a b
  obtain ⟨ωA, ωB, Pi, rf, rl, p, p', hm⟩ := (H _ _ hT fun τ => ⟨ha τ, hb τ⟩).1
  obtain ⟨c, hc⟩ := hr4 i j ρ A A₁ AV AV₁ hA hA₁ hV hV₁ t ωA ωB Pi rf rl p p' hm B
  refine _root_.GlobalTheory.GridFrameExistence.tied_pair_regularization_constant hP hK (_root_.GlobalTheory.T.twisted_theta_integral_converges hP.siegelSetUnitary hP) (_root_.GlobalTheory.T.twisted_square_theta_integrals_eq hP hK hTL) hL W B ρ t (hst t) i j
    hA hA₁ hV hV₁ hm (lam := c) ?_
  rintro _ _ ⟨a', b', τ, τ', n, Φ, hab, hn, hF, rfl, rfl⟩
  exact hc n Φ τ τ' hn hF a' b' (e i j ▸ hab)
theorem exists_tied_pair : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (B : Frames G) (ρ : RealMatch W), ∃ ρ₀ : RealMatch W,
      ρ₀.vX = ρ.vX ∧ ρ₀.vT = ρ.vT ∧ ρ₀.Tied ∧ ∀ (i j : Fin D.R.m) (t : T), ∃ c₀ : ℂ, GlobalTheory.SqTower.RegConst W B ρ₀ t i j c₀ := by
  intro hP hK hTL
  refine ⟨0, fun ε CF _ => ⟨0, (12 : ℝ) ^ (5 / ε), fun C _ D large₂ he hx hR T Lc μ₀ hL G W B ρ => ?_⟩⟩
  obtain ⟨ρ₀, h1, h2, h3, h4⟩ := _root_.GlobalTheory.GridFrameExistence.exists_tied_pair_of_standing_hypotheses hP hK hTL hL
    (fun t => standing_of_size hR.size hR.size.2.1.eleven_le hL G t) W ρ
  exact ⟨ρ₀, h1, h2, h3, h4 B⟩
end GlobalTheory.GridFrameExistence
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.ConstRatio (Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tied_theta_pair : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (B : Frames G) (ρ : RealMatch W), ∃ ρ₀ : RealMatch W, ρ₀.vX = ρ.vX ∧ ρ₀.vT = ρ.vT ∧ ρ₀.Tied ∧
    ∀ (i j : Fin D.R.m) (t : T), ∃ c₀ : ℂ, RegConst W B ρ₀ t i j c₀ := by
  first | exact @_root_.GlobalTheory.GridFrameExistence.exists_tied_pair | exact _root_.GlobalTheory.GridFrameExistence.exists_tied_pair | (intros; apply _root_.GlobalTheory.GridFrameExistence.exists_tied_pair <;> assumption)
end
