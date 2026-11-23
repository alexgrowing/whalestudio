import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeafTW1OfAllConjugatesGood

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BigOn.TwistBoundAtPlace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

theorem tupleRead_baseTuple_eq_family : p.tupT D.what₂.mu0 = p.P.A3.A.μ0 :=
  p.charW.base.lev.xi_inj (by rw [p.tupXi D.what₂.mu0 (Or.inl rfl), p.Tp.trueColumnChoices_heckeChar_reference_eq_one, p.charW.base.lev.xi_base])

theorem twistedAt_of_mem {v : HeightOneSpectrum (𝓞 D.what₂.LL)} (hv : v ∈ p.R.twPl) : TwistedAt D (D.plEq.symm v) := by
  intro he
  apply p.charW.tup.mu_ne v hv
  have := p.tupAt (D.plEq.symm v)
  rw [he, tupleRead_baseTuple_eq_family, Equiv.apply_symm_apply] at this
  exact this.symm

theorem conj_mem {v : HeightOneSpectrum (𝓞 D.what₂.LL)} (hv : v ∈ p.R.twPl) : Formalism.DivisionValues.conjPl v ∈ p.R.twPl := by
  by_contra h
  have := p.charW.tup.mu_off _ h
  rw [p.charW.tup.mu_conj] at this
  exact p.charW.tup.mu_ne v hv this

end Point

set_option maxHeartbeats 1600000 in

theorem hasTwistBound_at {eps : ℝ} {Fm : FamP eps} {x : ℝ} {hx : Fm.x1 < x} {i : Fm.Ix x} (p : Pt Fm x hx i)
    {r : TwoRuns p.T p.P.Gp} {c : OnConst} {O : Obj p c} (hR : RecAt p (Fm.parT x hx i) r O)
    (hE : ∀ v ∈ p.R.twPl, ∀ j, GlobalTheory.TwistIndex.ExportTie p.P.A3.A (Fm.ex x hx i).nch (twE Fm x hx i) (R2 p) j (F2 p).P0
      (F2 p).ψ0⁻¹ 1 v (ownAt (Fm.D x i) v))
    (hS : LeafSup O) (hK : GlobalTheory.TraceClassRank.RankAtPlaces O)
    {N0 : (Fm.D x i).ntw.Tw → ℕ} {S : ∀ (i' : (Fm.D x i).ntw.Tw) (j : ℕ) (b : Bool), Finset ((Fm.D x i).nexp.Dat i' j b)}
    (hG : Formalism.MainNotions.TwGoodAt (Fm.D x i) (Fm.ex x hx i).nch ⟨twE Fm x hx i, N0, S⟩) : HasTwistBound O := by
  obtain ⟨hc, hinj, z, act, y, ht⟩ := hR.1.tied
  have tied : ∀ v ∈ p.R.twPl, TwistedAt (Fm.D x i) ((Fm.D x i).plEq.symm v) ∧
      ∀ j, GlobalTheory.TwistIndex.TiedAt p.P.A3.A (Fm.ex x hx i).nch (twE Fm x hx i) O v j (id j) := fun v hv =>
    ⟨twistedAt_of_mem p hv, fun j => ⟨(r.used v).full, p.alg, R2 p, p.κ, p.v₀, (hR.1.ok.laws v).p, fw2 p, hinj,
      (Fm.ex x hx i).errX, ownAt (Fm.D x i) v, _, _, _, z j, act j, GlobalTheory.OntoChain.mirIncl (R2 p), r.lev j, (F2 p).P0, (F2 p).ψ0⁻¹, 1, y v j,
      (ht v j).1, hE v hv j⟩⟩
  exact GlobalTheory.TwistIndex.exists_leafTW1_of_twGoodAt p.P.A3.A (Fm.ex x hx i).nch ⟨twE Fm x hx i, N0, S⟩ hG O id
    Function.injective_id (GlobalTheory.TwistIndex.goodPartLattice_of_leafSup hS)
    (fun w hw => ⟨fun j => ((hK w hw).1 j).2.1, fun j => ((hK w hw).2 j).2.1⟩)
    (fun w hw => ⟨tied w hw, tied _ (conj_mem p hw)⟩)

theorem twistSt_of (hE : ExportSt) (hG : GeoSt)
    (hK : AtRec fun _ _ _ _ _ _ O => GlobalTheory.TraceClassRank.RankAtPlaces O) : TwistSt := by
  obtain ⟨a, ha, H⟩ := (hE.and hG).and hK
  refine ⟨a, ha, fun e he hle => ?_⟩
  obtain ⟨K, hK'⟩ := H e he hle
  refine ⟨K, fun Fm CH hc hL => ?_⟩
  obtain ⟨⟨⟨x1, E1⟩, ⟨c1, G1⟩⟩, ⟨c2, K1⟩⟩ := hK' Fm CH hc hL
  obtain ⟨x0, T0⟩ := hc.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨max c1 c2, fun c hcC hb => ?_⟩
  obtain ⟨x2, G2⟩ := G1 c ((le_max_left _ _).trans hcC) hb
  obtain ⟨x3, K2⟩ := K1 c ((le_max_right _ _).trans hcC) hb
  refine ⟨max (max x0 x1) (max x2 x3), fun x hx hle i p hp hM r O hR => ?_⟩
  have h0 : x0 ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hle)
  have h1 : x1 ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hle)
  have h2 : x2 ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hle)
  have h3 : x3 ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans hle)
  obtain ⟨-, N0, S, hTG⟩ := T0 x h0 hx i
  exact hasTwistBound_at p hR (E1 x hx h1 i p hp hM) (G2 x hx h2 i p hp hM r O hR).1 (K2 x hx h3 i p hp hM r O hR) hTG

end GlobalTheory.BigOn.TwistBoundAtPlace
