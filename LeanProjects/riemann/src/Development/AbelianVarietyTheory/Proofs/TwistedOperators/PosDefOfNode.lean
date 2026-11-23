import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ToPairMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteThetaIntegralIntegrableContinuous
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteUnitaryCocompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKOContinuousAndRatInvariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridFiniteDatumVectorThetaFockVacuum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorsOfSmoothThetaStable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelGridRationalLeftInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfOpenCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryEmbeddingContinuousMulRationalStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselColumnScalarFunctionContinuousLeftInvarianStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridTopVertexFormFunctionContinuousLeftInvariantStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries

open scoped ComplexOrder

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefConv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G)

def IsInvCont (X : Node) (F : Fn G X) : Prop := Continuous F ∧ ∀ γ ∈ GQ (G.V X), ∀ g, F (γ * g) = F g

def Good (a : Arrow T) (f : Sch G a) : Prop :=
  (Continuous fun p : GA D (G.V a.src) × GA D (G.V a.tgt) => W.kerA a f p.1 p.2) ∧
  (∀ γ ∈ GQ (G.V a.src), ∀ γ' ∈ GQ (G.V a.tgt), ∀ g h, W.kerA a f (γ * g) (γ' * h) = W.kerA a f g h) ∧
  (∀ τ, (gramAt D (G.V a.src) τ).PosDef) ∧ (M.ν a.src).IsHaarMeasure ∧
  IsFundamentalDomain (GQ (G.V a.src)) (M.fd a.src) (M.ν a.src)

theorem step {a : Arrow T} {f : Sch G a} (hg : Good W M a f) {F : Fn G a.src} (hF : IsInvCont a.src F) :
    LiftConv W M a f F ∧ IsInvCont a.tgt (liftA W M a f F) := by
  obtain ⟨hK, hinv, hpos, hH, hfd⟩ := hg
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact _ hpos
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V a.src)
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V a.tgt)
  have hl : ∀ γ ∈ GQ (G.V a.src), ∀ g h, W.kerA a f (γ * g) h = W.kerA a f g h := fun γ hγ g h => by
    simpa using hinv γ hγ 1 (one_mem _) g h
  have hr : ∀ γ ∈ GQ (G.V a.tgt), ∀ g h, W.kerA a f g (γ * h) = W.kerA a f g h := fun γ hγ g h => by
    simpa using hinv 1 (one_mem _) γ hγ g h
  refine ⟨fun h => ?_, ?_, fun γ hγ h => ?_⟩
  · exact GlobalTheory.CocompactIntegrable.integrableOn_of_cocompact _ _ _ C hfd hC hcov _
      ((hK.comp (Continuous.prodMk_left h)).mul hF.1) (fun γ hγ g => by simp only [hl γ hγ, hF.2 γ hγ])
  · exact GlobalTheory.DefLiftCont.continuous_integral_of_cocompact (G := GA D (G.V a.tgt)) (GQ (G.V a.src)) (M.ν a.src)
      (M.fd a.src) C hfd hC hcov (fun h g => W.kerA a f g h * F g)
      ((hK.comp continuous_swap).mul (hF.1.comp continuous_snd)) (fun γ hγ h g => by simp only [hl γ hγ, hF.2 γ hγ])
  · simp only [liftA_apply, hr γ hγ]

theorem path {X : Node} {F : Fn G X} (hF : IsInvCont X F) : ∀ {Y : Node} (p : Path T X Y) (d : PureT G p),
    Path.Fam.All (fun a f => Good W M a f) d → PathConv W M p d F ∧ IsInvCont Y (liftP W M p d F)
  | _, .nil, _, _ => ⟨trivial, hF⟩
  | _, .snoc a p, d, h => by
    obtain ⟨h1, h2⟩ := path hF p d.1 h.1
    obtain ⟨h3, h4⟩ := step W M h.2 h2
    exact ⟨⟨h1, h3⟩, h4⟩

theorem all_colFam {S : Arrow T → Type} {P : ∀ a, S a → Prop} (t : T) :
    ∀ n (f : ∀ j : Fin n, S (.col t j)), (∀ j, P _ (f j)) → Path.Fam.All P (colFam t n f)
  | 0, _, _ => trivial
  | n + 1, f, h => ⟨all_colFam t n _ fun j => h j.castSucc, h (Fin.last n)⟩

theorem all_rowFam {S : Arrow T → Type} {P : ∀ a, S a → Prop} (j : ℕ) :
    ∀ n (f : ∀ i : Fin n, S (.right i j)), (∀ i, P _ (f i)) → Path.Fam.All P (rowFam j n f)
  | 0, _, _ => trivial
  | n + 1, f, h => ⟨all_rowFam j n _ fun i => h i.castSucc, h (Fin.last n)⟩

end GlobalTheory.DefConv

namespace GlobalTheory.DefConv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem posDef_of_node (G : GridData L sc) {μ0 : T} (hL : L.Is μ0) {X : Node} (h : X.InRange D.R.m)
    (h0 : X.neg D.R.m = 0) (τ : D.what₂.Tau) : (gramAt D (G.V X) τ).PosDef := by
  have hV := node_isV G hL h
  rw [h0] at hV
  refine GlobalTheory.RepsObj.gramAt_posDef (fun σ => ?_) hV.sigOK τ
  rw [hV.sig σ, hV.rank, Nat.sub_zero]

variable (W : G.Weil) {U : Set T} (S : GridChoice W U)

theorem theta_fock {t : T} {p : Pair T} (hp : DefPair D.R.m p) (hr : p.InRange D.R.m) (d : FinDatum G t p)
    (hv : S.Z.HasVec d) (Q : PolF D (G.pT p).rank (G.pS p).rank) :
    IsThetaFunO W.ψ (G.pS p) (G.pT p) (W.fock p (movedVec t S d) Q) := by
  have h1 := (GlobalTheory.FockRealVec.vec_theta_fock W S.Z hp d hv).1
  have h2 : IsThetaFunO W.ψ _ _ (movedVec t S d) := (W.om_is p hr).om_pres _ _ h1
  exact GlobalTheory.FockTheta.ptStable D W.ψ W.θ W.ψ_std W.θ_is _ _ _ _ _ _ _ Q h2

end GlobalTheory.DefConv

namespace GlobalTheory.DefConv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G)

theorem good_col {t : T} {j : ℕ} (hj : j < D.R.m) (f : Sch G (.col t j))
    (hf : IsThetaFunO W.ψ (G.pS (.top t j)) (G.pT (.top t j)) f) (hpos : ∀ τ, (gramAt D (G.V (.top j)) τ).PosDef)
    {K : Subgroup (GL (Fin (G.V (.top j)).rank) (Lev.EAf D))} (hM : M.IsAt (.top j) K) : Good W M (.col t j) f := by
  have hr : (Pair.top t j : Pair T).InRange D.R.m := by show j + 1 ≤ D.R.m; omega
  obtain ⟨hc, -⟩ := GlobalTheory.thetaKO_continuous_and_rat_invariant W.ψ _ _ _ _ _ (W.om_is _ hr) f hf
  exact ⟨hc, fun γ hγ γ' hγ' g h => GlobalTheory.T.thetaKernel_grid_rational_left_invariant W _ hr f hf γ hγ γ' hγ' g h, hpos, hM.haar_fund.1, hM.haar_fund.2⟩

theorem good_row {i : ℕ} (hi : i < D.R.m) (f : Sch G (.right i D.R.m))
    (hf : IsThetaFunO W.ψ (G.pS (.chi i D.R.m)) (G.pT (.chi i D.R.m)) f)
    (hpos : ∀ τ, (gramAt D (G.V (.grid i D.R.m)) τ).PosDef)
    {K : Subgroup (GL (Fin (G.V (.grid i D.R.m)).rank) (Lev.EAf D))} (hM : M.IsAt (.grid i D.R.m) K) :
    Good W M (.right i D.R.m) f := by
  have hr : (Pair.chi i D.R.m : Pair T).InRange D.R.m := by show i + 1 ≤ D.R.m ∧ D.R.m ≤ D.R.m; omega
  obtain ⟨hc, -⟩ := GlobalTheory.thetaKO_continuous_and_rat_invariant W.ψ _ _ _ _ _ (W.om_is _ hr) f hf
  refine ⟨?_, fun γ hγ γ' hγ' g h => GlobalTheory.T.thetaKernel_grid_rational_left_invariant W _ hr f hf γ hγ γ' hγ' g h, hpos, hM.haar_fund.1, hM.haar_fund.2⟩
  exact hc.comp (((continuous_negGA _).comp continuous_snd).prodMk continuous_fst)

end GlobalTheory.DefConv

namespace GlobalTheory.DefConv

end GlobalTheory.DefConv
