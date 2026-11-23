import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingMeasureStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsTripleFactorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TripleGeometryUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubGAlgDOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsRealFiniteStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsFiniteIdentityStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingFundamentalDomainStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingIntegrableStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPlacewiseSeesawTripleOverHermitianStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankPiLeAleph0
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DixmierCommutantScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomDictionaryFramesExponentsKernelStatement

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

private theorem GlobalTheory.BotUniqT.kerA : GlobalTheory.Published.HoweDualityUnitary → GlobalTheory.Published.HoweDualityReal → GlobalTheory.Published.MinguezThetaGL → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ Φ ∈ algF ψ θ true A B, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, IsDatum Γ.M ψ cA ΦD Φ → (p Φ = 0 ↔ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf ΦD 0) := by
  intro hU hR hM hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT' R Rf hRf Pi rf rl p p' hm
    Φ hΦ ΦD hΦD hD
  obtain ⟨K₁, g₁, ne₁, max₁, h₁⟩ := GlobalTheory.T.seesaw_unfolding_measure hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT'
    Pi rf rl p p' hm
  obtain ⟨K₂, g₂, ne₂, h₂⟩ := GlobalTheory.T.matched_maps_triple_factor hP _ _ _ Bs _ _ Γ Xc om om' hT' R Rf hRf
  have hle : K₁ ≤ K₂ := fun x hx =>
    (h₂ x (g₁.1.1 hx)).2 (GlobalTheory.T.triple_geometry_unitary hU hR hM hP _ _ _ Bs _ _ Γ Xc om om' hT' R Rf hRf K₁ g₁ ne₁ x hx)
  rcases max₁ K₂ g₂ hle with h | h
  · rw [← h₁ Φ hΦ ΦD hΦD hD, ← h, h₂ ΦD hΦD]
  · exact absurd h ne₂

end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

namespace GlobalTheory.SquareAgree

private theorem _root_.GlobalTheory.BotUniqT.kerB : GlobalTheory.Published.HoweDualityUnitary → GlobalTheory.Published.HoweDualityReal → GlobalTheory.Published.MinguezThetaGL → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ Φ₀ ∈ algF ψ θ false A₁ B, ∀ Φ₀D ∈ algD Γ.M' Bs.ψ Bs.emb, IsDatum Γ.M' ψ cB Φ₀D Φ₀ → (p' Φ₀ = 0 ↔ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf 0 Φ₀D) := by
  intro hU hR hG hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT' R Rf hM Pi rf rl p p' hm
    Φ₀ hΦ₀ Φ₀D hΦ₀D hD
  obtain ⟨K, hK, hKs, hKne⟩ := GlobalTheory.T.seesaw_unfolding_fundamental_domain hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT'
    Pi rf rl p p' hm
  obtain ⟨KD, hKD, hKDs, hKDne⟩ := GlobalTheory.T.matched_maps_finite_identity hP Bs Γ Xc om om' R Rf hM
  have h1 : K ≤ KD := fun Φ hΦ => (hKD Φ).2 ⟨hKs.le hΦ, GlobalTheory.T.matched_maps_real_finite hU hR hG hP Bs Γ Xc om om' R Rf hM K hKs hKne Φ hΦ⟩
  have h2 : KD = K := (GlobalTheory.T.seesaw_unfolding_integrable hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT'
    Pi rf rl p p' hm K KD hK hKDs h1).resolve_right hKDne
  constructor
  · intro h0
    have hm : Φ₀D ∈ K := (hK Φ₀D).2 ⟨hΦ₀D, Φ₀, hΦ₀, hD, h0⟩
    rw [← h2] at hm
    exact ((hKD _).1 hm).2
  · intro hpm
    have hm : Φ₀D ∈ KD := (hKD _).2 ⟨hΦ₀D, hpm⟩
    rw [h2] at hm
    obtain ⟨_, Φ₁, _, hD₁, h0⟩ := (hK _).1 hm
    rw [IsDatum.fun_eq Γ.M' ψ cB cB.surjective hD hD₁]
    exact h0

end GlobalTheory.SquareAgree

end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotUniqT

private theorem exists_equiv_of_ker {V P₀ P : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup P₀] [Module ℂ P₀]
    [AddCommGroup P] [Module ℂ P] (S : Submodule ℂ V) (p₀ : V →ₗ[ℂ] P₀) (p : V →ₗ[ℂ] P)
    (h₀ : S.map p₀ = ⊤) (h : S.map p = ⊤) (hk : ∀ x ∈ S, p₀ x = 0 ↔ p x = 0) :
    ∃ E : P₀ ≃ₗ[ℂ] P, ∀ x ∈ S, p x = E (p₀ x) := by
  have s₀ : Function.Surjective (p₀.domRestrict S) := by
    intro y
    have hy : y ∈ S.map p₀ := h₀ ▸ Submodule.mem_top
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have s : Function.Surjective (p.domRestrict S) := by
    intro y
    have hy : y ∈ S.map p := h ▸ Submodule.mem_top
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker : LinearMap.ker (p₀.domRestrict S) = LinearMap.ker (p.domRestrict S) := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply]
    exact hk x.1 x.2
  let E : P₀ ≃ₗ[ℂ] P := ((p₀.domRestrict S).quotKerEquivOfSurjective s₀).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans ((p.domRestrict S).quotKerEquivOfSurjective s))
  refine ⟨E, fun x hx => ?_⟩
  have e1 : ((p₀.domRestrict S).quotKerEquivOfSurjective s₀).symm (p₀ x) = Submodule.Quotient.mk ⟨x, hx⟩ := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  show p x = ((p.domRestrict S).quotKerEquivOfSurjective s) ((Submodule.quotEquivOfEq _ _ hker)
    (((p₀.domRestrict S).quotKerEquivOfSurjective s₀).symm (p₀ x)))
  rw [e1]
  rfl

private theorem intertwine {V P₀ P : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup P₀] [Module ℂ P₀]
    [AddCommGroup P] [Module ℂ P] (S : Submodule ℂ V) (p₀ : V →ₗ[ℂ] P₀) (p : V →ₗ[ℂ] P) (E : P₀ ≃ₗ[ℂ] P)
    (hE : ∀ x ∈ S, p x = E (p₀ x)) (h₀ : S.map p₀ = ⊤) (a : Module.End ℂ P₀) (b : Module.End ℂ P)
    (H : ∀ Φ ∈ S, ∃ Φ' ∈ S, p₀ Φ' = a (p₀ Φ) ∧ p Φ' = b (p Φ)) (x : P₀) : E (a x) = b (E x) := by
  have hx : x ∈ S.map p₀ := h₀ ▸ Submodule.mem_top
  obtain ⟨Φ, hΦ, rfl⟩ := hx
  obtain ⟨Φ', hΦ', h1, h2⟩ := H Φ hΦ
  rw [← h1, ← hE Φ' hΦ', h2, hE Φ hΦ]

private theorem comm_of_intertwine {P₀ P : Type} [AddCommGroup P₀] [Module ℂ P₀] [AddCommGroup P] [Module ℂ P]
    (E E' : P₀ ≃ₗ[ℂ] P) (a : Module.End ℂ P₀) (b : Module.End ℂ P) (hE : ∀ x, E (a x) = b (E x))
    (hE' : ∀ x, E' (a x) = b (E' x)) :
    ((E.trans E'.symm : P₀ ≃ₗ[ℂ] P₀) : Module.End ℂ P₀) * a = a * ((E.trans E'.symm : P₀ ≃ₗ[ℂ] P₀) : Module.End ℂ P₀) := by
  ext x
  simp only [Module.End.mul_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply]
  rw [hE, LinearEquiv.symm_apply_eq, hE', LinearEquiv.apply_symm_apply]

private theorem uniq_of_triple (hH : GlobalTheory.Published.HoweDualityReal) (hP : GlobalTheory.FunPr.Hypotheses₂) (hL : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching)
    {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (W : G.Weil) (i j : Fin D.R.m)
    {A A' WW : HSp D} (X : Tri T A A' WW) (hX : IsBottomTri W i j X) (t : T)
    (hT : IsTriple A A' WW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)))
    (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW)
    (Pi₀ : ModuleCat.{0} ℂ) (rf₀ : GA D WW → Module.End ℂ Pi₀)
    (rl₀ : D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ → Module.End ℂ Pi₀)
    (p₀ : (WO A WW → ℂ) →ₗ[ℂ] Pi₀) (p₀' : (WO A' WW → ℂ) →ₗ[ℂ] Pi₀)
    (Pi : ModuleCat.{0} ℂ) (rf : GA D WW → Module.End ℂ Pi)
    (rl : D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ → Module.End ℂ Pi)
    (p : (WO A WW → ℂ) →ₗ[ℂ] Pi) (p' : (WO A' WW → ℂ) →ₗ[ℂ] Pi)
    (hm₀ : IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2))
      (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (X.ω t) (X.ω' t) Pi₀ rf₀ rl₀ p₀ p₀')
    (hm : IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2))
      (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (X.ω t) (X.ω' t) Pi rf rl p p') :
    ∃ (E : Pi₀ ≃ₗ[ℂ] Pi) (c : ℂ), c ≠ 0 ∧ (∀ Φ ∈ algF W.ψ W.θ true FA FW, p Φ = c • E (p₀ Φ)) ∧
      ∀ Φ' ∈ algF W.ψ W.θ false FA' FW, p' Φ' = E (p₀' Φ') := by
  have hθ : IsInfFam W.θ := hX.is.isVac.2.inf
  obtain ⟨e, Bs, Γ, Xc, om, om', cA, cB, hO, hTD⟩ := GlobalTheory.T.exists_placewise_seesaw_triple_over_hermitian D W.ψ W.θ hθ A A' WW FA FA' FW _ _ hT X.m X.fd X.m' X.fd'
    hX.is.meas hX.is.meas' (X.ω t) (X.ω' t) hm.weilA hm.weilB
  obtain ⟨R, Rf, hR⟩ := hL D.host.F D.host.E D.sp.cm.sig Bs A.rank A'.rank Γ Xc om om' hTD
  have kA : ∀ Φ ∈ algF W.ψ W.θ true FA FW, p₀ Φ = 0 ↔ p Φ = 0 := fun Φ hΦ => by
    obtain ⟨ΦD, hΦD, hD⟩ := hO.algA Φ hΦ
    rw [GlobalTheory.BotUniqT.kerA hP.howeDualityUnitary hH hP.minguezThetaGL hP D _ _ A A' WW FA FA' FW _ _ _ _
        _ _ _ _ e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi₀ rf₀ rl₀ p₀ p₀' hm₀ Φ hΦ ΦD hΦD hD,
      GlobalTheory.BotUniqT.kerA hP.howeDualityUnitary hH hP.minguezThetaGL hP D _ _ A A' WW FA FA' FW _ _ _ _
        _ _ _ _ e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi rf rl p p' hm Φ hΦ ΦD hΦD hD]
  have kB : ∀ Φ ∈ algF W.ψ W.θ false FA' FW, p₀' Φ = 0 ↔ p' Φ = 0 := fun Φ hΦ => by
    obtain ⟨ΦD, hΦD, hD⟩ := hO.algB Φ hΦ
    rw [GlobalTheory.BotUniqT.kerB hP.howeDualityUnitary hH hP.minguezThetaGL hP D _ _ A A' WW FA FA' FW _ _
        _ _ _ _ _ _ e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi₀ rf₀ rl₀ p₀ p₀' hm₀ Φ hΦ ΦD hΦD hD,
      GlobalTheory.BotUniqT.kerB hP.howeDualityUnitary hH hP.minguezThetaGL hP D _ _ A A' WW FA FA' FW _ _
        _ _ _ _ _ _ e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi rf rl p p' hm Φ hΦ ΦD hΦD hD]
  obtain ⟨EA, hEA⟩ := exists_equiv_of_ker _ p₀ p hm₀.mapA.onto hm.mapA.onto kA
  obtain ⟨EB, hEB⟩ := exists_equiv_of_ker _ p₀' p' hm₀.mapB.onto hm.mapB.onto kB

  have fA : ∀ h ∈ GfC WW, ∀ x, EA (rf₀ h x) = rf h (EA x) := fun h hh =>
    intertwine _ p₀ p EA hEA hm₀.mapA.onto _ _ fun Φ hΦ =>
      ⟨_, hm₀.mapA.stabX.1 h hh Φ hΦ, hm₀.mapA.eqf h hh Φ hΦ, hm.mapA.eqf h hh Φ hΦ⟩
  have fB : ∀ h ∈ GfC WW, ∀ x, EB (rf₀ h x) = rf h (EB x) := fun h hh =>
    intertwine _ p₀' p' EB hEB hm₀.mapB.onto _ _ fun Φ hΦ =>
      ⟨_, hm₀.mapB.stabX.1 h hh Φ hΦ, hm₀.mapB.eqf h hh Φ hΦ, hm.mapB.eqf h hh Φ hΦ⟩
  have lA : ∀ τ, ∀ Y ∈ lieAt WW τ, ∀ x, EA (rl₀ τ Y x) = rl τ Y (EA x) := fun τ Y hY =>
    intertwine _ p₀ p EA hEA hm₀.mapA.onto _ _ fun Φ hΦ => by
      obtain ⟨Φ', hΦ', hd⟩ := hm₀.mapA.stabX.2 τ Y hY Φ hΦ
      exact ⟨Φ', hΦ', hm₀.mapA.eql τ Y hY Φ hΦ Φ' hΦ' hd, hm.mapA.eql τ Y hY Φ hΦ Φ' hΦ' hd⟩
  have lB : ∀ τ, ∀ Y ∈ lieAt WW τ, ∀ x, EB (rl₀ τ Y x) = rl τ Y (EB x) := fun τ Y hY =>
    intertwine _ p₀' p' EB hEB hm₀.mapB.onto _ _ fun Φ hΦ => by
      obtain ⟨Φ', hΦ', hd⟩ := hm₀.mapB.stabX.2 τ Y hY Φ hΦ
      exact ⟨Φ', hΦ', hm₀.mapB.eql τ Y hY Φ hΦ Φ' hΦ' hd, hm.mapB.eql τ Y hY Φ hΦ Φ' hΦ' hd⟩

  let ι := {g // g ∈ GfC WW} ⊕ {x : D.what₂.Tau × Matrix (Fin WW.rank) (Fin WW.rank) ℂ // x.2 ∈ lieAt WW x.1}
  let ρ : ι → Module.End ℂ Pi₀ := Sum.elim (fun g => rf₀ g.1) (fun x => rl₀ x.1.1 x.1.2)
  have hrank : Module.rank ℂ Pi₀ ≤ Cardinal.aleph0 :=
    GlobalTheory.SquareAgree.rank_pi_le_aleph0 hP.howeDualityUnitary hH hP D _ _ A A' WW FA FA' FW _ _ _ _ _ _ _ _ e Bs Γ Xc om om'
      cA cB hθ hT hO hTD R Rf hR Pi₀ rf₀ rl₀ p₀ p₀' hm₀
  have hirr : ∀ N : Submodule ℂ Pi₀, (∀ k, ∀ x ∈ N, ρ k x ∈ N) → N = ⊥ ∨ N = ⊤ := fun N hN =>
    hm₀.irred.2 N (fun g hg x hx => hN (Sum.inl ⟨g, hg⟩) x hx) fun τ Y hY x hx => hN (Sum.inr ⟨(τ, Y), hY⟩) x hx
  have hcomm : ∀ k, ((EA.trans EB.symm : Pi₀ ≃ₗ[ℂ] Pi₀) : Module.End ℂ Pi₀) * ρ k =
      ρ k * ((EA.trans EB.symm : Pi₀ ≃ₗ[ℂ] Pi₀) : Module.End ℂ Pi₀) := by
    rintro (⟨g, hg⟩ | ⟨⟨τ, Y⟩, hY⟩)
    · exact comm_of_intertwine EA EB _ _ (fA g hg) (fB g hg)
    · exact comm_of_intertwine EA EB _ _ (lA τ Y hY) (lB τ Y hY)
  obtain ⟨c, hc⟩ := GlobalTheory.dixmier_commutant_scalar ι Pi₀ ρ hrank hirr _ hcomm
  have hT' : ∀ x, EB.symm (EA x) = c • x := fun x => by
    have := LinearMap.congr_fun hc x
    simpa using this
  haveI : Nontrivial Pi₀ := hm₀.irred.1
  have hc0 : c ≠ 0 := by
    rintro rfl
    obtain ⟨x, hx⟩ := exists_ne (0 : Pi₀)
    have h1 := hT' x
    rw [zero_smul, LinearEquiv.map_eq_zero_iff, LinearEquiv.map_eq_zero_iff] at h1
    exact hx h1
  refine ⟨EB, c, hc0, fun Φ hΦ => ?_, fun Φ hΦ => hEB Φ hΦ⟩
  rw [hEA Φ hΦ, ← LinearEquiv.map_smul, ← hT', LinearEquiv.apply_symm_apply]

end GlobalTheory.BotUniqT

end

end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.T.bottom_triangle_matched_factors : GlobalTheory.Published.HoweDualityReal → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (t : T), ∀ (Pi₀ : ModuleCat.{0} ℂ) rf₀ rl₀ p₀ p₀' (Pi : ModuleCat.{0} ℂ) rf rl p p', IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (X.ω t) (X.ω' t) Pi₀ rf₀ rl₀ p₀ p₀' → IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (X.ω t) (X.ω' t) Pi rf rl p p' → ∃ (E : Pi₀ ≃ₗ[ℂ] Pi) (c : ℂ), c ≠ 0 ∧ (∀ Φ ∈ algF W.ψ W.θ true FA FW, p Φ = c • E (p₀ Φ)) ∧ ∀ Φ' ∈ algF W.ψ W.θ false FA' FW, p' Φ' = E (p₀' Φ') := by
  intro hH hP hK hL
  obtain ⟨CF0, h⟩ := GlobalTheory.T.definiteBottom_dictionary_frames_exponents_kernel
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := h ε CF hCF
  refine ⟨C0, x0, fun C hC D large₂ he hx hr T Lc μ hμ G => ?_⟩
  intro W i j A A' WW X hX FA FA' FW t Pi₀ rf₀ rl₀ p₀ p₀' Pi rf rl p p' hm₀ hm
  obtain ⟨FA₀, FA₀', FW₀, a, b, s₁, s₂, s₃, hall⟩ := h C hC D large₂ he hx hr T Lc μ hμ G W i j A A' WW X hX
  exact GlobalTheory.BotUniqT.uniq_of_triple hH hP hL G W i j X hX t (hall t).1 FA FA' FW Pi₀ rf₀ rl₀ p₀ p₀' Pi rf rl p p' hm₀ hm
