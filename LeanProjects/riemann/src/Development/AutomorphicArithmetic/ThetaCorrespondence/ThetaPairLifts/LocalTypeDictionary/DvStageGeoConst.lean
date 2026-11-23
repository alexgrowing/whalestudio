import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AutomorphicArithmetic.LocalEmbeddings.StageGeoConst
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedSquareLocalMatching
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TripleWeilTransferMatching
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DvStageGeoPass

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Geo piW chrW unifAt latAtV At SInf)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime IsSplitBasis)
open GlobalTheory.BotMatch (evW)
open GlobalTheory.StageGeo
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.StageGeo
variable {D : D7} {T : Type} {A A' WW : HSp D} {X : Tri T A A' WW} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
  {α β : T → ((AE D)ˣ →* Circle)} {νH : T → Formalism.L2.Host.HChar D.host.E} {S : T → Finset (HeightOneSpectrum (𝓞 D.host.E))}
  {FA : Fr A} {FA' : Fr A'} {FW : Fr WW} {Bs : Base D.host.F D.host.E} {Γ : Geo D.sp.cm.sig A.rank A'.rank}
theorem geometric_stage_constant_ratio (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree) (hM : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching)
    (hX : X.Is ψ θ α β νH S) (hG : IsStageGeo ψ X FA FA' FW hX.rank Bs Γ) {a b : D.what₂.Tau → ℚ}
    (hd : ∀ t : T, IsTriple A A' WW (α t) (β t) ∧ (∀ τ, HasInfExp D (α t) τ (a τ) ∧ HasInfExp D (β t) τ (b τ)) ∧
      IsFinF ψ θ true FA FW (X.f t) ∧ IsFinF ψ θ false FA' FW (X.f' t) ∧
      (∀ P g h, thetaKO (X.ω t) g h (fockF ψ θ true FA FW (X.f t) P) = X.ker ψ θ t P h g) ∧
      ∀ P g h, thetaKO (X.ω' t) g h (fockF ψ θ false FA' FW (X.f' t) P) = X.ker' ψ θ t P h g)
    {lam : T → ℂ} (hF : GlobalTheory.ConstRatio.Factor X ψ θ lam) {t₁ t₂ : T} {X₁ X₂ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E}
    (r₁ : Reads α β S Bs t₁ X₁) (r₂ : Reads α β S Bs t₂ X₂) {R om₁ om₁' Rf₁ om₂ om₂' Rf₂} {c₁ c₂ : ℂ}
    (m₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ X₁ om₁ om₁' R Rf₁) (m₂ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ X₂ om₂ om₂' R Rf₂)
    (k₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst Bs Γ X₁ om₁ om₁' R Rf₁ c₁) (k₂ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst Bs Γ X₂ om₂ om₂' R Rf₂ c₂) :
    c₁ * lam t₂ = c₂ * lam t₁ := by
  have hψ := hX.isVac.1
  have hθ := hX.isVac.2.inf
  obtain ⟨g, g0, hg⟩ := exists_vac (ε := true) hG.pairA hG.latA hX.isVac
  obtain ⟨g', g0', hg'⟩ := exists_vac (ε := false) hG.pairB hG.latB hX.isVac'
  have hco : ∀ {κ : Type} (T₀ : Finset (HeightOneSpectrum (𝓞 D.host.F)))
      {φ vac : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (κ → Fv D.host.F v) → ℂ}, (∀ v ∉ T₀, φ v = vac v) →
      ∀ᶠ v in Filter.cofinite, φ v = vac v := fun T₀ _ _ h =>
    Filter.Eventually.mono T₀.finite_toSet.compl_mem_cofinite fun v hv => h v hv
  obtain ⟨Φ, Φ', hΦ, hΦ', eΦ, eΦ'⟩ : ∃ (Φ : PolF D WW.rank A.rank →ₗ[ℂ] SInf D.host.F (Fin A.rank × Fin (A.rank + A'.rank)))
      (Φ' : PolF D WW.rank A'.rank →ₗ[ℂ] SInf D.host.F (Fin A'.rank × Fin (A.rank + A'.rank))),
      LinearMap.range Φ = Γ.M.Pol Bs.ψ Bs.emb ∧ LinearMap.range Φ' = Γ.M'.Pol Bs.ψ Bs.emb ∧
      (∀ φ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = Γ.M.vac v) → ∀ P,
        thO Γ.M ψ (sgn true A).gram (finCongr hX.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Φ P) φ) =
          fockF ψ θ true FA FW (thO Γ.M ψ (sgn true A).gram (finCongr hX.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ)) P) ∧
      ∀ φ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = Γ.M'.vac v) → ∀ P,
        thO Γ.M' ψ (sgn false A').gram (finCongr hX.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Φ' P) φ) =
          fockF ψ θ false FA' FW (thO Γ.M' ψ (sgn false A').gram (finCongr hX.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g' φ)) P := by
    obtain ⟨φ, φ', s, s', v, v', n, n', -, e, e'⟩ := exists_fin hX hG r₁ m₁ hg hg'
    obtain ⟨Φ, h1, h2⟩ := UpperTheory.thetaLift_pure_tensor_of_isFinF D ψ true A WW _ hX.rank Bs Γ.V Γ.W Γ.M hG.pairA θ hθ FA FW hG.cartA g g0 φ s (hco _ v) n
      (e ▸ (hd t₁).2.2.1)
    obtain ⟨Φ', h1', h2'⟩ := UpperTheory.thetaLift_pure_tensor_of_isFinF D ψ false A' WW _ hX.rank Bs Γ.V' Γ.W Γ.M' hG.pairB θ hθ FA' FW hG.cartB g' g0' φ' s'
      (hco _ v') n' (e' ▸ (hd t₁).2.2.2.1)
    exact ⟨Φ, Φ', h1, h1', h2, h2'⟩
  obtain ⟨-, Pi, p, p', J, -, hJ, -, hI, hI', P', hP', hint⟩ := hF
  have mP' : Φ' P' ∈ Γ.M'.Pol Bs.ψ Bs.emb := hΦ' ▸ LinearMap.mem_range_self _ _
  obtain ⟨f, mf, ef⟩ : R.p' (Φ' P') ∈ (Γ.M.Pol Bs.ψ Bs.emb).map R.p := by rw [m₁.real.quot.onto]; trivial
  obtain ⟨P, rfl⟩ : f ∈ LinearMap.range Φ := hΦ ▸ mf
  obtain ⟨Pr, qm, qm', -, -, hLM⟩ := _root_.GlobalTheory.T.twisted_local_factors_match hP.howeDualityReal hP hK hM D ψ θ hψ hθ A A' WW FA FA' FW a b
  have key : ∀ t Xc om om' Rf c, Reads α β S Bs t Xc → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst Bs Γ Xc om om' R Rf c → lam t • p P = c • p' P' := by
    intro t Xc om om' Rf c r m k
    obtain ⟨hT, hE, -, -, hk, hk'⟩ := hd t
    obtain ⟨Pim, rf, rl, pm, pm', hmm⟩ := _root_.GlobalTheory.T.triple_weil_transfer_matching hP.howeDualityReal hP hK hM D ψ θ hψ hθ A A' WW FA FA' FW _ _ hT
      (hLM _ _ hT hE).1 (X.ω t) (X.ω' t) (hX.weil t) (hX.weil' t)
    obtain ⟨φ, φ', s, s', v, v', -, -, l, e, e'⟩ := exists_fin hX hG r m hg hg'
    obtain ⟨cA, cB, hO, dA, dB⟩ := UpperTheory.exists_seesaw_intertwiners_of_triple D ψ θ hθ T A A' WW X FA FA' FW hX.rank Bs Γ hG Xc om om' m.triple (X.ω t) (X.ω' t)
      (by rw [r.eα, r.eβ]; exact hX.weil t) (by rw [r.eα, r.eβ]; exact hX.weil' t)
    rw [r.eα, r.eβ] at hO
    have d1 := dA _ (GlobalTheory.TensUniq.pure_mem_schA (Φ P) φ s (((hco _ v).and m.triple.geo.hM.std).mono fun v h => h.1.trans h.2))
    have d2 := dB _ (GlobalTheory.TensUniq.pure_mem_schA (Φ' P') φ' s'
      (((hco _ v').and m.triple.geo.hM'.std).mono fun v h => h.1.trans h.2))
    rw [eΦ φ s (hco _ v), ← e] at d1
    rw [eΦ' φ' s' (hco _ v'), ← e'] at d2
    have h1 := _root_.GlobalTheory.StageGeo.geometric_stage_constant_on_pure_tensors hP hK D ψ θ A A' WW FA FA' FW _ _ _ _ _ _ _ _ _ Bs Γ Xc om om' cA cB hθ hT hO hX.meas' (hX.weil' t)
      hmm.mapB.stabM.1 R Rf c m k _ mf _ mP' φ φ' s s' v v' ef l _ _ d1 d2 (fun h => by
        simp only [hk']
        exact hint t h)
    have h2 : X.I ψ θ t P = c • X.I' ψ θ t P' := by
      funext h
      have h3 := congrFun h1 h
      simp only [thetaInt, _root_.Pi.smul_apply, hk, hk'] at h3
      exact h3
    refine hJ t ?_
    rw [map_smul, map_smul, ← hI, ← hI' t P' (hint t), h2]
  have q₁ := key _ _ _ _ _ _ r₁ m₁ k₁
  have q₂ := key _ _ _ _ _ _ r₂ m₂ k₂
  refine smul_left_injective ℂ hP' ?_
  show (c₁ * lam t₂) • p' P' = (c₂ * lam t₁) • p' P'
  rw [mul_comm c₁, mul_comm c₂, mul_smul, mul_smul, ← q₁, ← q₂, smul_comm]
end GlobalTheory.StageGeo
end
end
