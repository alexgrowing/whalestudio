import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareConstantProportionalRegular
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedWeilRepresentationConvergence
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaIntegralKernelLieAlgebraStable
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.WeilRepresentationSquareComm
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SquareIdentityOfMatching
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareConstantProportionalRegularStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.ChainFr Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.RealSep
section Generic
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.BigNZ
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
end Generic
section Nonzero
open GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ blkU conjU UB)
end Nonzero
section Read
open GlobalTheory.SquareComm GlobalTheory.SquareAgree GlobalTheory.Grid GlobalTheory.TripleRead GlobalTheory.SquareIdent
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (incM conjU)
variable {D : D7}
end Read
section Grid
open GlobalTheory.SquareComm GlobalTheory.SquareAgree GlobalTheory.TripleRead GlobalTheory.SquareIdent GlobalTheory.SquareDict GlobalTheory.BigNZ
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (alpha beta blkU spV spW spW₁ spV₁ xiV xiV₁)
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}
end Grid
section Null
open GlobalTheory.SquareComm GlobalTheory.SquareIdent GlobalTheory.SquareDict
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (alpha beta spV spW spW₁ spV₁)
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}
set_option maxHeartbeats 1000000 in
theorem exists_nullSpace_realPlace (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree)
    (hLM : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching) {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (hst : ∀ t, SquareStanding G t)
    (i j : Fin D.R.m) {A : Fr (spW G i j)} {AV : Fr (spV G i j)} {AV₁ : Fr (spV₁ G i j)} (hA : IsGridFr W _ A)
    (hV : IsGridFr W _ AV) (hV₁ : IsGridFr W _ AV₁)
    (ι : PolRoute G (.grid i (j + 1)) (.grid (i + 1) (j + 1)) (.grid (i + 1) j) →ₗ[ℂ]
      PolF D (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)).rank (spW G i j).rank)
    (hι : ∀ (t : T) (B : Frames G) (ρ : RealMatch W) n Φ (τ : TotT G (routeBig t i j)) τ', HasFlip B t ρ i j n Φ τ τ' →
      ∀ a : PolT G (routeBig t i j) →₀ ℂ,
        datumA W (tensT W a τ) = fockF W.ψ W.θ true A (frSum AV AV₁) (datumA W τ) (ι (toTens a))) :
    ∃ K : Submodule ℂ (PolRoute G (.grid i (j + 1)) (.grid (i + 1) (j + 1)) (.grid (i + 1) j)),
      (∀ B ρ t x, IsNull W B ρ t i j x ↔ x ∈ K) ∧
      (∀ x ∈ K, ∀ t ν 𝓕, IsHaarFD (spW G i j) ν 𝓕 → ∀ ωA : GlobalTheory.Grid.WRep (spW G i j) (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)),
        GlobalTheory.Grid.IsWeil W.ψ true _ _ (beta G i j) (beta G i j / alpha G t i j) ωA →
        ∀ f, IsFinF W.ψ W.θ true A (frSum AV AV₁) f → thetaInt ωA ν 𝓕 (fockF W.ψ W.θ true A (frSum AV AV₁) f (ι x)) = 0) ∧
      ∀ B (ρ : RealMatch W) t (M : Vol G), M.Is t → ∀ n Φ τ τ', (∀ w ∈ locPl G t, depthAt G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w)) →
        HasFlip B t ρ i j n Φ τ τ' → ∀ g g₁, ∃ l : PolRoute G (.grid i (j + 1)) (.grid (i + 1) (j + 1)) (.grid (i + 1) j) →ₗ[ℂ] ℂ,
          ∀ a, ∫ u in M.fd _, kerBig W (tensT W a τ) g g₁ u ∂M.ν _ = l (toTens a) := by
  obtain ⟨A₁, hA₁⟩ := exists_isGridFr W (X := .grid i j) ⟨i.2.le, j.2.le⟩
  have hD := fun t => dict hL W t i j A A₁ AV AV₁ hA hA₁ hV hV₁
  have hT := fun t => (hD t).1 (hst t) _ (exists_vol G hL t).choose_spec
  choose a b ha hb _ using (hT μ₀).gap
  obtain ⟨Pr, q, H⟩ := _root_.GlobalTheory.T.thetaIntegral_factors_through_kType hP hK hLM D W.ψ W.θ W.ψ_std W.θ_is _ _ _ A A₁ (frSum AV AV₁) a b
  replace H := fun t => H _ _ (hT t) fun τ => ⟨GlobalTheory.SquareRel.hasInfExp_alpha G i j hL μ₀ t τ (ha τ), hb τ⟩
  choose ωA ωB hωA hωB using fun t => _root_.GlobalTheory.T.weilRepresentation_square_comm hP D W.ψ W.ψ_std _ _ _ _ _ (hT t)
  have hbig : Node.InRange D.R.m (.grid (i + 1) (j + 1)) := ⟨i.2, j.2⟩
  have form : ∀ B (ρ : RealMatch W) t (M : Vol G), M.Is t → ∀ n Φ τ τ',
      (∀ w ∈ locPl G t, depthAt G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w)) → HasFlip B t ρ i j n Φ τ τ' →
      ∃ (Pf : ModuleCat.{0} ℂ) (y : Pf) (J : Pr ⊗[ℂ] Pf →ₗ[ℂ] (GA D (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)) → ℂ))
        (κ : _ → ℂ), (J = 0 ∨ Function.Injective J) ∧
        (∀ P, thetaInt (ωA t) (M.ν _) (M.fd _) (fockF W.ψ W.θ true A (frSum AV AV₁) (datumA W τ) P) = J (q P ⊗ₜ y)) ∧
        ∀ g g₁ a, ∫ u in M.fd _, kerBig W (tensT W a τ) g g₁ u ∂M.ν _ = κ (g, g₁) * J (q (ι (toTens a)) ⊗ₜ y) (blk _ _ (g, g₁)) := by
    intro B ρ t M hM n Φ τ τ' hn hF
    obtain ⟨_, _, _, _, _, -, hc⟩ := _root_.GlobalTheory.SquareIdent.square_identity_reduction hP.howeDualityReal hP hLM hL W i j A A₁ AV AV₁ hA hA₁ hV hV₁ t B ρ M (hst t) hM (hT t)
      _ _ (hωA t) (hωB t)
    obtain ⟨_, hc⟩ := hc 0
    obtain ⟨Pf, y, J, h1, h2⟩ := H t _ _ (hM.vtx _ hbig).haar_fund _ (hωA t) _ (hc n Φ τ τ' hn hF).1
    obtain ⟨κ, hκ⟩ := (hD t).2 _ _ (hωA t) (hωB t)
    refine ⟨Pf, y, J, κ, h1, h2, fun g g₁ a => ?_⟩
    obtain ⟨b', hb'⟩ := ρ.onto_big i j (toTens a)
    obtain ⟨b, rfl⟩ := toTens_surjective b'
    rw [(hκ B ρ _ _ ⟨a, b, τ, τ', n, Φ, hb', hn, hF, rfl, rfl⟩).2.2.2.2.1 M g g₁, hι t B ρ n Φ τ τ' hF, h2]
  refine ⟨LinearMap.ker (q ∘ₗ ι), fun B ρ t x => ⟨fun h0 => ?_, fun hx M hM a ha n Φ τ τ' hn hF g g₁ => ?_⟩,
    fun x hx t ν 𝓕 hν ω hω f hf => ?_, fun B ρ t M hM n Φ τ τ' hn hF g g₁ => ?_⟩
  · obtain ⟨a, rfl⟩ := toTens_surjective x
    obtain ⟨M, hM, a₀, τ, τ', n, Φ, hn, hF, g, g₁, hne⟩ :=
      exists_integral_ne_zero hP.strongApproxSU hK hLM hL W B ρ t i j (hst t)
    obtain ⟨Pf, y, J, κ, h1, h2, h3⟩ := form B ρ t M hM n Φ τ τ' hn hF
    rw [h3] at hne
    have hy : y ≠ 0 := by rintro rfl; simp at hne
    have hJ : Function.Injective J := h1.resolve_left (by rintro rfl; simp at hne)
    have h4 := thetaInt_eq_zero hP.strongApproxSU hK hLM hL W B ρ t i j (hst t) hA hA₁ hV hV₁ (hωA t)
      (fun n Φ τ τ' hF => hι t B ρ n Φ τ τ' hF a) h0 hM hn hF
    rw [h2, ← map_zero J] at h4
    obtain ⟨c, hc⟩ := exists_scalar (Q := Pr) hy 0
    have h5 := congrArg (TensorProduct.comm ℂ Pr Pf) (hJ h4)
    rw [TensorProduct.comm_tmul, map_zero] at h5
    exact (hc _ 0 (h5.trans (TensorProduct.zero_tmul _ _).symm)).trans (smul_zero c)
  · obtain ⟨Pf, y, J, κ, -, -, h3⟩ := form B ρ t M hM n Φ τ τ' hn hF
    rw [h3, ha, show q (ι x) = 0 from hx, TensorProduct.zero_tmul, map_zero, Pi.zero_apply, mul_zero]
  · obtain ⟨Pf, y, J, -, h2⟩ := H t ν 𝓕 hν ω hω f hf
    rw [h2, show q (ι x) = 0 from hx, TensorProduct.zero_tmul, map_zero]
  · obtain ⟨Pf, y, J, κ, -, -, h3⟩ := form B ρ t M hM n Φ τ τ' hn hF
    exact ⟨κ (g, g₁) • (LinearMap.proj (blk _ _ (g, g₁)) ∘ₗ J ∘ₗ (TensorProduct.mk ℂ Pr Pf).flip y ∘ₗ q ∘ₗ ι), fun a => h3 g g₁ a⟩
theorem exists_scalar_of_realStandingData (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree)
    (hLM : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching) {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (hst : ∀ t, SquareStanding G t)
    (B : Frames G) (ρ ρ₀ : RealMatch W) (h1 : ρ₀.vX = ρ.vX) (h2 : ρ₀.vT = ρ.vT) (i j : Fin D.R.m) :
    ∃ lam : ℂ, lam ≠ 0 ∧ ∀ t c' c₀, IsSquareConst W B ρ t i j c' → GlobalTheory.SqTower.RegConst W B ρ₀ t i j c₀ → c₀ ≠ 0 ∧ c' = lam * c₀ ∧
      ∀ a a₀ b, (a, b) ∈ ρ.rel i j → (a₀, b) ∈ ρ₀.rel i j → ∀ t', IsNull W B ρ t' i j (a - lam • a₀) := by
  obtain ⟨A, hA⟩ := exists_isGridFr W (X := .grid (i + 1) (j + 1)) ⟨i.2, j.2⟩
  obtain ⟨AV, hV⟩ := exists_isGridFr W (X := .grid i (j + 1)) ⟨i.2.le, j.2⟩
  obtain ⟨AV₁, hV₁⟩ := exists_isGridFr W (X := .grid (i + 1) j) ⟨i.2, j.2.le⟩
  obtain ⟨ι, -, hι⟩ := realA hL W i j A AV AV₁ hA hV hV₁
  obtain ⟨K, hN, -, hl⟩ := _root_.GlobalTheory.RealSep.exists_nullSpace_realPlace hP hK hLM hL W hst i j hA hV hV₁ ι hι
  obtain ⟨x, hx⟩ := exists_not_isNull hP.strongApproxSU hK hLM hL W B ρ μ₀ i j (hst μ₀)
  rw [hN] at hx
  have key : ∀ t c' c₀, IsSquareConst W B ρ t i j c' → GlobalTheory.SqTower.RegConst W B ρ₀ t i j c₀ →
      ∀ a a₀ b, (a, b) ∈ ρ.rel i j → (a₀, b) ∈ ρ₀.rel i j → (c₀ • a - c' • a₀ ∈ K) ∧ (c' = 0 → a ∈ K) ∧ (c₀ = 0 → a₀ ∈ K) := by
    intro t c' c₀ hc hc₀ a a₀ b hab hab₀
    obtain ⟨a, rfl⟩ := toTens_surjective a
    obtain ⟨a₀, rfl⟩ := toTens_surjective a₀
    obtain ⟨b, rfl⟩ := toTens_surjective b
    have H : ∀ M : Vol G, M.Is t → ∀ n Φ τ τ', (∀ w ∈ locPl G t, depthAt G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w)) →
        HasFlip B t ρ i j n Φ τ τ' → ∀ g g₁,
        ∃ (l : PolRoute G (.grid i (j + 1)) (.grid (i + 1) (j + 1)) (.grid (i + 1) j) →ₗ[ℂ] ℂ) (r : ℂ),
          (∀ a, ∫ u in M.fd _, kerBig W (tensT W a τ) g g₁ u ∂M.ν _ = l (toTens a)) ∧ l (toTens a) = c' * r ∧
            l (toTens a₀) = c₀ * r := by
      intro M hM n Φ τ τ' hn hF g g₁
      obtain ⟨l, e⟩ := hl B ρ t M hM n Φ τ τ' hn hF g g₁
      have hΘ : IsMatched B t ρ i j (tensT W a τ) (tensT W b τ') := ⟨a, b, τ, τ', n, Φ, hab, hn, hF, rfl, rfl⟩
      obtain ⟨z, z0, z1, z2⟩ := hc₀ M hM _ _ ⟨a₀, b, τ, τ', n, Φ, hab₀, hn, hasFlip_congr h1 h2 hF, rfl, rfl⟩ g g₁
      have z3 := hc M hM _ _ hΘ z g g₁ ⟨GlobalTheory.T.bigRoute_kernel_integrableOn_unitary_quotient (_root_.GlobalTheory.T.twisted_theta_integral_converges hP.siegelSetUnitary hP) hL W B ρ t i j
        (GlobalTheory.T.squareThetaTripleHypotheses_of_standing hL W t i j (hst t)) M hM _ _ hΘ g₁ g, z1.2⟩
      replace z2 := (congrArg (zdeg z * ·) (e a₀)).symm.trans z2
      replace z3 := (congrArg (zdeg z * ·) (e a)).symm.trans z3
      exact ⟨l, _ / zdeg z, e, by rw [← mul_div_assoc, ← z3, mul_div_cancel_left₀ _ z0],
        by rw [← mul_div_assoc, ← z2, mul_div_cancel_left₀ _ z0]⟩
    refine ⟨(hN B ρ t _).1 ?_, fun h => (hN B ρ t _).1 ?_, fun h => (hN B ρ t _).1 ?_⟩ <;>
    · intro M hM a' ha' n Φ τ τ' hn hF g g₁
      obtain ⟨l, r, e1, e2, e3⟩ := H M hM n Φ τ τ' hn hF g g₁
      rw [e1, ha']
      first
        | rw [map_sub, map_smul, map_smul, e2, e3, smul_eq_mul, smul_eq_mul]; ring
        | rw [e2, h, zero_mul]
        | rw [e3, h, zero_mul]
  obtain ⟨b, hb⟩ := ρ.onto_big i j x
  obtain ⟨x₀, hx₀⟩ := ρ₀.onto_small i j b
  obtain ⟨b₁, hb₁⟩ := ρ₀.onto_big i j x
  obtain ⟨x₁, hx₁⟩ := ρ.onto_small i j b₁
  by_cases hex : ∃ t c' c₀, IsSquareConst W B ρ t i j c' ∧ GlobalTheory.SqTower.RegConst W B ρ₀ t i j c₀
  swap
  · exact ⟨1, one_ne_zero, fun t c' c₀ h h₀ => absurd ⟨t, c', c₀, h, h₀⟩ hex⟩
  obtain ⟨s, d', d₀, hd, hd₀⟩ := hex
  have n₀ : ∀ t c' c₀, IsSquareConst W B ρ t i j c' → GlobalTheory.SqTower.RegConst W B ρ₀ t i j c₀ → c₀ ≠ 0 := fun t c' c₀ h h₀ e =>
    hx ((key t c' c₀ h h₀ _ _ _ hx₁ hb₁).2.2 e)
  have k : ∀ a a₀ b, (a, b) ∈ ρ.rel i j → (a₀, b) ∈ ρ₀.rel i j → a - (d' / d₀) • a₀ ∈ K := fun a a₀ b h h₀ => by
    have := K.smul_mem d₀⁻¹ (key s d' d₀ hd hd₀ a a₀ b h h₀).1
    rwa [smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ (n₀ _ _ _ hd hd₀), one_smul, ← div_eq_inv_mul] at this
  refine ⟨d' / d₀, div_ne_zero (fun e => hx ((key s d' d₀ hd hd₀ _ _ _ hb hx₀).2.1 e)) (n₀ _ _ _ hd hd₀),
    fun t c' c₀ h h₀ => ⟨n₀ t c' c₀ h h₀, ?_, fun a a₀ b h h₀ t' => (hN B ρ t' _).2 (k a a₀ b h h₀)⟩⟩
  by_contra hne
  have e := K.sub_mem (key t c' c₀ h h₀ _ _ _ hx₁ hb₁).1 (K.smul_mem c₀ (k _ _ _ hx₁ hb₁))
  rw [smul_sub, sub_sub_sub_cancel_left, smul_smul, ← sub_smul] at e
  exact hx ((K.smul_mem_iff (sub_ne_zero.2 fun e => hne (by rw [← e, mul_comm]))).1 e)
end Null
section Main
open GlobalTheory.SquareComm GlobalTheory.SquareIdent GlobalTheory.SquareDict GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (alpha beta spV spW spW₁ spV₁)
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}
theorem realPlace_theta_matching : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (B : Frames G) (ρ ρ₀ : RealMatch W), ρ₀.vX = ρ.vX → ρ₀.vT = ρ.vT →
      ∀ i j : Fin D.R.m, ∃ lam : ℂ, lam ≠ 0 ∧ ∀ (t : T) (c' c₀ : ℂ), IsSquareConst W B ρ t i j c' →
        GlobalTheory.SqTower.RegConst W B ρ₀ t i j c₀ → c₀ ≠ 0 ∧ c' = lam * c₀ := by
  intro hP hK hLM
  refine ⟨0, fun ε CF _ => ⟨0, (12 : ℝ) ^ (5 / ε), fun C _ D large₂ he hx hR T Lc μ₀ hL G W B ρ ρ₀ h1 h2 i j => ?_⟩⟩
  have hst := standing hR.size hL hR.size.2.1.eleven_le G
  obtain ⟨lam, h0, H⟩ := _root_.GlobalTheory.RealSep.exists_scalar_of_realStandingData hP hK hLM hL W hst B ρ ρ₀ h1 h2 i j
  exact ⟨lam, h0, fun t c' c₀ hc hc₀ => ⟨(H t c' c₀ hc hc₀).1, (H t c' c₀ hc hc₀).2.1⟩⟩
end Main
end GlobalTheory.RealSep
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.ConstRatio (Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_real_places_separation : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (B : Frames G) (ρ ρ₀ : RealMatch W), ρ₀.vX = ρ.vX → ρ₀.vT = ρ.vT →
    ∀ i j : Fin D.R.m, ∃ lam : ℂ, lam ≠ 0 ∧ ∀ (t : T) (c' c₀ : ℂ), IsSquareConst W B ρ t i j c' → RegConst W B ρ₀ t i j c₀ → c₀ ≠ 0 ∧ c' = lam * c₀ := by
  first | exact @_root_.GlobalTheory.RealSep.realPlace_theta_matching | exact _root_.GlobalTheory.RealSep.realPlace_theta_matching | (intros; apply _root_.GlobalTheory.RealSep.realPlace_theta_matching <;> assumption)
end
