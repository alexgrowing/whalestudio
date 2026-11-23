import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AuxiliaryPrimeLtFirstTypePrimeOfSizes
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjThetaKOMulIntegrableOn
import Formalism.LocalToGlobal.IndefiniteReal.MultLemmas
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridParameterRegularCardEqRankFormula
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsTypeAtDualParIffStarIsTypeAtStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaFunctionFockVectorRightwardArrowStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsConstSetIntegralHaarFundamentalDomainsUnitStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RightArrowCusp

theorem vert_par : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}, GlobalTheory.Hk3.Core R F → ∀ G : GlobalTheory.Grid.GridPre R, G.Is → ∀ i j : ℕ, i ≤ D.R.m → j ≤ D.R.m → (G.V i j).S = GlobalTheory.Grid.parV D i j := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R F _ G hG i j hi hj
  cases i with
  | zero =>
    rw [GlobalTheory.Grid.parV_zero D hj]
    rcases j with _ | j
    · rfl
    · show (if j + 1 < D.R.m then GlobalTheory.Grid.nodeY R (j + 1) else GlobalTheory.Grid.nodeX R).S = _
      split_ifs with h
      · simp [Nat.min_eq_left hj]
      · have : j + 1 = D.R.m := by omega
        rw [this]
  | succ i => exact (hG.spaces.vert i j hi hj).par

theorem meas_haar_fund : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}, GlobalTheory.Hk3.Core R F → ∀ G : GlobalTheory.Grid.GridPre R, G.Is → ∀ (t : T) (i j : ℕ), i ≤ D.R.m → j ≤ D.R.m → (G.meas t i j).ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ (G.V i j).V) (G.meas t i j).fd (G.meas t i j).ν := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R F hC G hG t i j hi hj
  have aux : ∀ {N : GlobalTheory.Grid.Node D} (m : N.MeasDat) (df : Prop) K, m.Is df K →
      m.ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ N.V) m.fd m.ν := by
    intro N m df K h
    by_cases hd : df
    · exact ⟨(h.1 hd).1.1, (h.1 hd).2⟩
    · exact ⟨(h.2 hd).1.1, (h.2 hd).2⟩
  have cst : ∀ {S S' : GlobalTheory.Grid.Node D} (e : S = S') (m : S.MeasDat),
      m.ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ S.V) m.fd m.ν →
      (GlobalTheory.Grid.Node.MeasDat.cast e m).ν.IsHaarMeasure ∧
        IsFundamentalDomain (GQ S'.V) (GlobalTheory.Grid.Node.MeasDat.cast e m).fd (GlobalTheory.Grid.Node.MeasDat.cast e m).ν := by
    intro S S' e m h
    subst e
    exact h
  rcases i with _ | i
  · rcases j with _ | j
    · exact aux _ _ _ (hG.meas.col 0 (Nat.zero_le _))
    · show (GlobalTheory.Grid.meas0 R t j).ν.IsHaarMeasure ∧
        IsFundamentalDomain (GQ (GlobalTheory.Grid.row0 R (j + 1)).V) (GlobalTheory.Grid.meas0 R t j).fd (GlobalTheory.Grid.meas0 R t j).ν
      unfold GlobalTheory.Grid.meas0
      split_ifs with h
      · apply cst
        by_cases h2 : j + 1 + 1 < D.R.m
        · have := hC.models.νY t (j + 1) h2
          exact ⟨this.1.1, this.2⟩
        · have := hC.models.νY' t
          have e : D.R.m - 1 = j + 1 := by omega
          rw [e] at this
          exact ⟨this.1.1, this.2⟩
      · apply cst
        have := hC.models.νX t
        exact ⟨this.1.1, this.2⟩
  · rcases j with _ | j
    · exact aux _ _ _ (hG.meas.col (i + 1) hi)
    · exact aux _ _ _ (hG.meas.vert i j hi hj)

theorem thetaKO_eq_kerA : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts} {G' : GridData R.toLevCh sc} (W : G'.Weil) (i j : ℕ) (Ls : Submodule (𝓞 D.host.E) (G'.V (.grid i j)).V) (hs1 : Submodule.IsLattice D.host.E Ls) (hs2 : Formalism.HermitianLatticesTheory.IsUnimodular (G'.V (.grid i j)).hT Ls) (Lt : Submodule (𝓞 D.host.E) (G'.V (.grid (i + 1) j)).V) (ht1 : Submodule.IsLattice D.host.E Lt) (ht2 : Formalism.HermitianLatticesTheory.IsUnimodular (G'.V (.grid (i + 1) j)).hT Lt) (ω : GlobalTheory.Grid.WRep (GlobalTheory.VolRatioCompare.reLat (G'.V (.grid (i + 1) j)) Lt ht1 ht2) (GlobalTheory.VolRatioCompare.reLat (G'.V (.grid i j)) Ls hs1 hs2)), HEq (ω.toSgn true) (W.om (.chi i j)) → ∀ (Φ : Sch G' (.right i j)) (g : GA D (G'.V (.grid i j))) (h : GA D (G'.V (.grid (i + 1) j))), thetaKO ω h g Φ = W.kerA (.right i j) Φ g h := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc G' W i j Ls hs1 hs2 Lt ht1 ht2 ω hω Φ g h
  have e : ω.toSgn true = W.om (.chi i j) := eq_of_heq hω
  show (ω (h, g)) Φ 0 = (W.om (.chi i j) (negGA _ h, g)) Φ 0
  rw [← e]
  rfl

theorem isThetaFunO_neg_reLat : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S U : HSp D) (L : Submodule (𝓞 D.host.E) S.V) (h1 : Submodule.IsLattice D.host.E L) (h2 : Formalism.HermitianLatticesTheory.IsUnimodular S.hT L) (L' : Submodule (𝓞 D.host.E) U.V) (h1' : Submodule.IsLattice D.host.E L') (h2' : Formalism.HermitianLatticesTheory.IsUnimodular U.hT L') (Φ : WO (negSp S) U → ℂ), IsThetaFunO ψ (negSp S) U Φ → IsThetaFunO ψ (GlobalTheory.Grid.neg (GlobalTheory.VolRatioCompare.reLat S L h1 h2)) (GlobalTheory.VolRatioCompare.reLat U L' h1' h2') Φ := by
  intro D ψ S U L h1 h2 L' h1' h2' Φ h
  exact ⟨h.1, h.2, h.3, h.4⟩

theorem isCuspListed_smul : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (θ : InfFam D) (X : Node) (c : ℂ) (F : Fn G X), IsCuspListed θ X F → IsCuspListed θ X (c • F) := by
  intro D T L sc G θ X c F ⟨h1, h2, h3⟩
  refine ⟨Formalism.IndefR.Mult.isAutFunSm_smul _ _ h1 c, Formalism.IndefR.Mult.isCuspFun_smul _ h2 c, ?_⟩
  rcases X with ⟨i, j⟩ | i | j
  · intro τ
    have e : (fun g => star ((c • F) g)) = star c • fun g => star (F g) := by
      funext g; simp [Pi.smul_apply, smul_eq_mul, star_mul', mul_comm]
    show IsTypeAt _ _ _ _ fun g => star ((c • F) g)
    rw [e]
    exact GlobalTheory.Mem.Th.isTypeAt_smul _ (h3 τ)
  · intro τ; exact GlobalTheory.Mem.Th.isTypeAt_smul c (h3 τ)
  · intro τ; exact GlobalTheory.Mem.Th.isTypeAt_smul c (h3 τ)

theorem kerA_mul_left_invariant : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts} {G' : GridData R.toLevCh sc} (W : G'.Weil) (i j : ℕ), i < D.R.m → j ≤ D.R.m → ∀ Φ : Sch G' (.right i j), IsThetaFunO W.ψ (G'.pS (.chi i j)) (G'.pT (.chi i j)) Φ → ∀ F : Fn G' (.grid i j), IsCuspListed W.θ (.grid i j) F → ∀ h, ∀ γ ∈ GQ (G'.V (.grid i j)), ∀ g, W.kerA (.right i j) Φ (γ * g) h * F (γ * g) = W.kerA (.right i j) Φ g h * F g := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc G' W i j hi hj Φ hΦ F hF h γ hγ g
  have hω := W.om_is (.chi i j) (by first | exact ⟨hi, hj⟩ | exact ⟨hj, hi⟩ | simpa using ⟨hi, hj⟩)
  show thetaKO (W.om (.chi i j)) (negGA _ h) (γ * g) Φ * F (γ * g) = thetaKO (W.om (.chi i j)) (negGA _ h) g Φ * F g
  rw [GlobalTheory.UpArrowConv.thetaKO_left_snd hω hΦ _ γ hγ g, hF.1.left γ hγ g]

theorem isAutFunSm_reLat_iff : ∀ {D : D7} (θ : InfFam D) (V : HSp D) (L : Submodule (𝓞 D.host.E) V.V) (h1 : Submodule.IsLattice D.host.E L) (h2 : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L) (φ : GA D V → ℂ), IsAutFunSm θ (GlobalTheory.VolRatioCompare.reLat V L h1 h2) φ ↔ IsAutFunSm θ V φ := by
  intro D θ V L h1 h2 φ
  exact ⟨fun h => ⟨⟨h.left, h.level, h.cont⟩, h.smooth, h.zfin, h.growth⟩,
    fun h => ⟨⟨h.left, h.level, h.cont⟩, h.smooth, h.zfin, h.growth⟩⟩

theorem isCuspOfType_iff_isCuspListed : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts}, sc.cGap = 1 → ∀ {G' : GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ (i j : ℕ), i ≤ D.R.m → j ≤ D.R.m → ∀ (L : Submodule (𝓞 D.host.E) (G'.V (.grid i j)).V) (h1 : Submodule.IsLattice D.host.E L) (h2 : Formalism.HermitianLatticesTheory.IsUnimodular (G'.V (.grid i j)).hT L) (Mo : Formalism.IndefR.Mult.DSModel (GlobalTheory.VolRatioCompare.reLat (G'.V (.grid i j)) L h1 h2) (GlobalTheory.Grid.parV D i j)) (Λ : Submodule (𝓞 D.host.E) (Fin (GlobalTheory.VolRatioCompare.reLat (G'.V (.grid i j)) L h1 h2).rank → D.host.E)) (β : GL (Fin (GlobalTheory.VolRatioCompare.reLat (G'.V (.grid i j)) L h1 h2).rank) (Lev.EAf D)) (φ : Fn G' (.grid i j)), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ ⟨GlobalTheory.VolRatioCompare.reLat (G'.V (.grid i j)) L h1 h2, GlobalTheory.Grid.parV D i j, Mo, Λ, β⟩ φ ↔ IsCuspListed W.θ (.grid i j) φ := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc hsc G' W hW i j hi hj L h1 h2 Mo Λ β φ
  rw [hW.θ]
  refine and_congr (isAutFunSm_reLat_iff R.θ _ L h1 h2 φ) (and_congr Iff.rfl ?_)
  show (∀ τ, IsTypeAt R.θ (GlobalTheory.VolRatioCompare.reLat (G'.V (.grid i j)) L h1 h2) τ (GlobalTheory.Grid.parV D i j τ) φ) ↔
    ∀ τ, IsTypeAt R.θ (G'.V (.grid i j)) τ (Node.par D sc.cGap (.grid i j) τ) fun g => star (φ g)
  refine forall_congr' fun τ => ?_
  rw [hsc]
  have hp : GlobalTheory.Grid.parV D i j τ = Formalism.IndefR.Mult.dualPar (GlobalTheory.ChiGrid.parV D 1 i j τ) := by
    unfold GlobalTheory.Grid.parV GlobalTheory.ChiGrid.parV
    rw [GlobalTheory.GridParDCount.grid_eq_num D τ]
  rw [hp]
  exact GlobalTheory.T.isTypeAt_dualPar_iff_star_isTypeAt R.θ (G'.V (.grid i j)) τ _ φ

open GlobalTheory.GridJoin in

theorem lift_right_of_smooth {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts} (hsc : sc.cGap = 1) {G' : GridData R.toLevCh sc} (W : G'.Weil)
    (hW : W.Over R) (ρ : RealMatch W) (hρ : RealMatch.Over R ρ) (M : Vol G') (t : T) (hM : M.Is t) (i j : ℕ) (hi : i < D.R.m)
    (hj : j ≤ D.R.m) (Ns Nt : GlobalTheory.Grid.Node D) (hs : SameSp (G'.V (.grid i j)) Ns.V) (ht : SameSp (G'.V (.grid (i + 1) j)) Nt.V)
    (hSs : Ns.S = GlobalTheory.Grid.parV D i j) (hSt : Nt.S = GlobalTheory.Grid.parV D (i + 1) j) (m : Ns.MeasDat) (hm1 : m.ν.IsHaarMeasure)
    (hm2 : IsFundamentalDomain (GQ Ns.V) m.fd m.ν) (ω : GlobalTheory.Grid.WRep Nt.V Ns.V) (hω : HEq (ω.toSgn true) (W.om (.chi i j)))
    (H : ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg Nt.V) Ns.V Φ →
      GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsSmooth R.θ (A := Ns) (B := Nt) m fun h g => thetaKO ω h g Φ) :
    ∀ e, IsIdemSum e (locPl G' t) → ∀ φ f, IsLocVec W (.chi i j) e (vacOf ρ (.right i j)) φ f →
      ∀ (Q : PolF D (G'.pT (.chi i j)).rank (G'.pS (.chi i j)).rank) (F : Fn G' (.grid i j)), IsCuspListed W.θ (.grid i j) F →
        LiftConv W M (.right i j) (W.fock (.chi i j) f Q) F ∧
          IsCuspListed W.θ (.grid (i + 1) j) (liftA W M (.right i j) (W.fock (.chi i j) f Q) F) := by
  obtain ⟨Vs, Ss, Ms, Λs, βs⟩ := Ns
  obtain ⟨Vt, St, Mt, Λt, βt⟩ := Nt
  obtain ⟨Ls, hs1, hs2, rfl⟩ := hs
  obtain ⟨Lt, ht1, ht2, rfl⟩ := ht
  dsimp only at hSs hSt
  subst hSs hSt
  intro e he φ f hf Q F hF
  have hΦ0 := GlobalTheory.T.isThetaFunction_fock_vector_rightward_arrow hW ρ hρ t i j hi hj e he φ f hf Q
  have hΦ : IsThetaFunO R.ψ (GlobalTheory.Grid.neg (GlobalTheory.VolRatioCompare.reLat (G'.V (.grid (i + 1) j)) Lt ht1 ht2))
      (GlobalTheory.VolRatioCompare.reLat (G'.V (.grid i j)) Ls hs1 hs2) (W.fock (.chi i j) f Q) :=
    hW.ψ ▸ isThetaFunO_neg_reLat W.ψ _ _ Lt ht1 ht2 Ls hs1 hs2 _ hΦ0
  have hK := thetaKO_eq_kerA W i j Ls hs1 hs2 Lt ht1 ht2 ω hω (W.fock (.chi i j) f Q)
  have hFs := (isCuspOfType_iff_isCuspListed hsc W hW i j hi.le hj Ls hs1 hs2 Ms Λs βs F).2 hF
  obtain ⟨hI, hT⟩ := H _ hΦ F hFs
  have hMX := (hM.vtx (.grid i j) ⟨hi.le, hj⟩).haar_fund
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_const_setIntegral_haar_fundamentalDomains_unitary (M.ν (.grid i j)) m.ν (M.fd (.grid i j)) m.fd hMX.1 hm1 hMX.2 hm2
  have key := fun h => hc (fun g => W.kerA (.right i j) (W.fock (.chi i j) f Q) g h * F g) (kerA_mul_left_invariant W i j hi hj _ hΦ0 F hF h)
  have e2 : ∀ h, (fun g => thetaKO ω h g (W.fock (.chi i j) f Q) * F g) =
      fun g => W.kerA (.right i j) (W.fock (.chi i j) f Q) g h * F g := fun h => funext fun g => by rw [hK g h]
  refine ⟨fun h => (key h).1.2 (e2 h ▸ hI h), ?_⟩
  have e : liftA W M (.right i j) (W.fock (.chi i j) f Q) F =
      c • fun h => ∫ g in m.fd, thetaKO ω h g (W.fock (.chi i j) f Q) * F g ∂m.ν := by
    funext h
    rw [liftA_apply, (key h).2]
    exact congrArg (c * ·) (congrArg (fun φ : GA D (G'.V (.grid i j)) → ℂ => ∫ g in m.fd, φ g ∂m.ν) (e2 h).symm)
  rw [e]
  exact isCuspListed_smul _ _ c _ ((isCuspOfType_iff_isCuspListed hsc W hW (i + 1) j hi hj Lt ht1 ht2 Mt Λt βt _).1 hT)

theorem cuspStep_right : (∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidalSmoothAt D) → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch =>
  ∀ (t : T) (M : Vol ch.G), M.Is t → ∀ a : Arrow T, IsGridArrow D.R.m t a → (∃ i j, a = Arrow.right i j) →
    ∀ e, IsIdemSum e (locPl ch.G t) → ∀ φ f, IsLocVec ch.W a.pair e (vacOf ch.rm a) φ f →
    ∀ (Q : PolF D (ch.G.pT a.pair).rank (ch.G.pS a.pair).rank) (F : Fn ch.G a.src), IsCuspListed ch.W.θ a.src F →
      LiftConv ch.W M a (ch.W.fock a.pair f Q) F ∧ IsCuspListed ch.W.θ a.tgt (liftA ch.W M a (ch.W.fock a.pair f Q) F) := by
  intro hLS hP
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hSet ch hch hsc => ?_⟩⟩
  intro t M hM a ha hr e he φ f hf Q F' hF
  obtain ⟨i, j, rfl⟩ := hr
  obtain ⟨i', j', hi, hj, h'⟩ | ⟨_, _, _, _, _, h'⟩ := ha
  · cases h'
    have hcg : ch.sc.cGap = 1 := by rw [hsc]
    obtain ⟨G, hG, hMa⟩ := GlobalTheory.GridJoin.exists_gridPre hP.discreteSeriesUpqExists hP.discreteSeriesCover
      hP.harishChandraModules hSet.host hSet.size hSet.core hcg ch.W hch.weil
    have hRB : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R :=
      ⟨hSet.core.lev, hSet.core.models.inf, hSet.core.models.νY, hSet.core.models.νY', hSet.core.models.νX⟩
    have hSm := (hLS D (GlobalTheory.RowSizes.sizes_of_sizeRows large₂ hSet.size) Γ Pl0 T A Ks R G hRB hG).X t i j hi hj
    have hgm := meas_haar_fund hSet.core G hG t i j hi.le hj
    exact lift_right_of_smooth hcg ch.W hch.weil ch.rm hch.vac M t hM i j hi hj (G.V i j) (G.V (i + 1) j)
      (hMa.1.vert i j hi.le hj).sp (hMa.1.vert (i + 1) j hi hj).sp (vert_par hSet.core G hG i j hi.le hj)
      (vert_par hSet.core G hG (i + 1) j hi hj) (G.meas t i j) hgm.1 hgm.2 (G.X i j).ω (hMa.2.omX i j hi hj) hSm
      e he φ f hf Q F' hF

end GlobalTheory.RightArrowCusp

end
