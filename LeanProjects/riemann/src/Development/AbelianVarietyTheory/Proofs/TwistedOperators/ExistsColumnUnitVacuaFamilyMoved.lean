import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RootOfUnityThetaTwist
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdelicCharacterPowEqOneFiniteIdelesOfOrderDvd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeOrbitVectorsMovedPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilFinitePointPreservesFockVacuum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SqNormIntegralFundamentalDomainEqL2NormSq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ColVac

variable {D : D7} {T : Type}

theorem xi_mem_xiVals {L : LevCh D T} {μ0 : T} (hL : L.Is μ0) (t : T) (x : (AE D)ˣ) :
    Circle.toUnits (L.xi t x) ∈ xiVals L t := by
  obtain ⟨n, hn0, hn⟩ := hL.xi_fin t
  obtain ⟨-, a, b, -, -, hab, ha, hb⟩ := GlobalTheory.IdeleParts.congr_open_and_parts D
  have e : L.xi t x = L.xi t (b x) := by
    conv_lhs => rw [hab x, map_mul, GlobalTheory.TupRoot.eq_one_of_finPart (hL.xi t) hn0 hn _ (ha x).2, one_mul]
  rw [e]
  have hx := (hb x).1
  generalize b x = u at hx
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  have h4 := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2 h4 _ _ (hL.xi t)
  let y : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ :=
    ⟨ι (finPart D (u : AE D)), ι (finPart D ((u⁻¹ : (AE D)ˣ) : AE D)),
      by rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one],
      by rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]⟩
  obtain ⟨S, k, hS, hS'⟩ := GlobalTheory.finiteIdele_exists_local_approx D.host.E N hN y
  have h5 := hprod u hx S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS'
  have h6 : Circle.toUnits (L.xi t u) = ∏ P ∈ S, (L.xiH t).locK P (k P) := by
    apply Units.ext
    rw [Units.coe_prod]
    exact h5
  rw [h6]
  exact prod_mem fun P _ => Subgroup.subset_closure ⟨P, _, rfl⟩

theorem attChr_mu {L : LevCh D T} {μ0 : T} (hL : L.Is μ0) (t : T) (j n : ℕ) :
    Formalism.IndefR.Lift.attChr (L.mu t j) L.eta n = Formalism.IndefR.Lift.attChr (L.mu μ0 j) L.eta n * L.xi t := by
  have hb : L.xi μ0 = 1 :=
    MonoidHom.ext (GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hL.xi_base ▸ hL.xi μ0))
  have e : L.mu t j = L.mu μ0 j * L.xi t := by
    show L.mu0 j * L.xi t = L.mu0 j * L.xi μ0 * L.xi t
    rw [hb, mul_one]
  unfold Formalism.IndefR.Lift.attChr
  rw [e]
  split_ifs
  · exact mul_right_comm _ _ _
  · rfl

section Move

variable {V : HSp D} {k : GA D V} {C Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}

set_option synthInstance.maxHeartbeats 400000 in

theorem fwd (h : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) C ↔
      (Formalism.IndefR.Lev.finE V k).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) (s : Fin V.rank → D.host.E) (hs : s ∈ C) :
    (fun i => Formalism.IndefR.Datum.toEAf D ((mt V k *ᵥ fun j => incA D (s j)) i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  rw [GlobalTheory.MovedHomLat.bridge]
  exact (h _).1 (Submodule.subset_span ⟨s, hs, rfl⟩)

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem bwd (h : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) C ↔
      (Formalism.IndefR.Lev.finE V k).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) (s : Fin V.rank → D.host.E) (hs : s ∈ Λ) :
    (fun i => Formalism.IndefR.Datum.toEAf D ((mt V k⁻¹ *ᵥ fun j => incA D (s j)) i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) C := by
  have e2 : (Formalism.IndefR.Lev.finE V k).1 * (Formalism.IndefR.Lev.finE V k⁻¹).1 = 1 :=
    congrArg Units.val (((Formalism.IndefR.Lev.finE V).map_mul k k⁻¹).symm.trans
      ((congrArg (Formalism.IndefR.Lev.finE V) (mul_inv_cancel k)).trans (Formalism.IndefR.Lev.finE V).map_one))
  rw [GlobalTheory.MovedHomLat.bridge]
  refine (h _).2 ?_
  rw [Matrix.mulVec_mulVec, e2, Matrix.one_mulVec]
  exact Submodule.subset_span ⟨s, hs, rfl⟩

end Move

variable {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} {N : Std G U}

theorem isVac_moved (Z : Normal W N) (t : T) {j : ℕ} (hj : j < D.R.m) :
    W.IsVac (.top t j) (W.om (.top t j) ((N.u (.top j)).1, (N.u (.top (j + 1))).1) (Z.vac (.top t j))) := by
  have h0 := N.u_lat (.top j) hj.le
  have h1 := N.u_lat (.top (j + 1)) hj
  have H := GlobalTheory.MovedHomLat.actO_latO_onto (G.V (.top j)) (G.V (.top (j + 1))) (N.u (.top j)).1 (N.u (.top (j + 1))).1
    _ _ _ _ (fwd h0) (fwd h1) (bwd h0) (bwd h1)
  refine GlobalTheory.WeilVacMove.isVacO_om D W.ψ W.θ _ _ _ _ _ (W.om_is (.top t j) (show j + 1 ≤ D.R.m from hj)) W.θ_is
    _ _ _ _ _ _ _ _ _ _ (fun τ => ?_) (fun τ => ?_) (fun u => ⟨fun hu => ?_, ?_⟩) _ (Z.vac_is (.top t j) hj)
  · rw [GlobalTheory.FockRealMove.compAt_mt_of_mem_GfC W.θ τ _ (N.u (.top j)).2, Matrix.mul_one, Matrix.one_mul]
  · rw [GlobalTheory.FockRealMove.compAt_mt_of_mem_GfC W.θ τ _ (N.u (.top (j + 1))).2, Matrix.mul_one, Matrix.one_mul]
  · obtain ⟨w, hw, e⟩ := H.2 u hu
    exact ⟨w, hw, e.symm⟩
  · rintro ⟨w, hw, rfl⟩
    exact H.1 w hw

theorem colVac : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ∀ (ch : Choice R), ch.Is → ∃ v, IsColVac ch v ∧ ∃ (κ : ℕ → ℂˣ) (z : T → ℕ → ℂˣ), (∀ t j, z t j ∈ xiVals R.toLevCh t) ∧ ∀ (t : T) (j : ℕ), j < D.R.m → ch.W.om (.top t j) (ch.G.toPair (.top t j) (ch.S.N.u (Pair.top t j : Pair T).small).1 (ch.S.N.u (Pair.top t j : Pair T).big).1) (ch.S.Z.vac (.top t j)) = ((κ j * z t j : ℂˣ) : ℂ) • v j := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R large₂ F hS ch _
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  choose x hx using fun j => GlobalTheory.RecDict.exists_isDetRoot D (ch.G.V (.top j)) (ch.S.N.u (.top j)).1
  refine ⟨fun j => ch.W.om (.top A.μ0 j) ((ch.S.N.u (.top j)).1, (ch.S.N.u (.top (j + 1))).1) (ch.S.Z.vac (.top A.μ0 j)),
    fun t j hj => isVac_moved ch.S.Z A.μ0 hj, fun _ => 1,
    fun t j => Circle.toUnits (R.toLevCh.xi t ((x j)⁻¹ * x (j + 1))),
    fun t j => xi_mem_xiVals hL t _, fun t j hj => ?_⟩
  have hW0 := ch.W.om_is (.top A.μ0 j) (show j + 1 ≤ D.R.m from hj)
  have hWt := ch.W.om_is (.top t j) (show j + 1 ≤ D.R.m from hj)
  have eS : ch.G.chrS (.top t j) = ch.G.chrS (.top A.μ0 j) * R.toLevCh.xi t := attChr_mu hL t _ _
  have eT : ch.G.chrT (.top t j) = ch.G.chrT (.top A.μ0 j) * R.toLevCh.xi t := attChr_mu hL t _ _
  rw [eS, eT] at hWt
  have e := GlobalTheory.TupRoot.twist_eq hW0 hWt (hx j) (hx (j + 1)) (ch.S.Z.vac_is (.top A.μ0 j) hj).2.theta
  rw [(ch.S.Z.free t A.μ0 j).2.1]
  refine e.trans ?_
  congr 1
  rw [one_mul, ← MonoidHom.map_inv, ← MonoidHom.map_mul]
  rfl

end GlobalTheory.ColVac

end
