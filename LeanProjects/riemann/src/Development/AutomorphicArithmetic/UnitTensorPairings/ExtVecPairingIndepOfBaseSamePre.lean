import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicCoreTransportEnlargedCoefficientBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseChangeEquivCrdOver
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ModelSame
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult GlobalTheory.RealGeo
set_option maxHeartbeats 4000000

noncomputable section

private def UpperTheory.HasUnitPureTensorPairing {D : D7} {W : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel W S) {V : HSp D} (c : CoefA V)
    {P : Type} [AddCommGroup P] [Module ℂ P] (io : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] P) (Δ : P) (v : M.Vec) : Prop :=
  ∃ (u : ∀ ρ, lowT M ρ) (w : c.W), (∀ ρ, (u ρ : M.sm ρ) = v ρ) ∧ ‖w‖ = 1 ∧ io (PiTensorProduct.tprod ℂ u) w = Δ

private theorem UpperTheory.isExtVec_of_same_model {D : D7} {W : HSp D} {S S' : D.what₂.Tau → SPar} (M : DSModel W S) (M' : DSModel W S')
    (hMM : GeoTies.ModelSame M M') (v : M.Vec) (v' : M'.Vec) (hv : HEq v' v) : IsExtVec M v → IsExtVec M' v' := by
  obtain ⟨X, σ, lam, ε, fr, _, _, _, _⟩ := M
  obtain ⟨X', σ'', lam', ε', fr', _, _, _, _⟩ := M'
  obtain ⟨m1, m2, m3, m4, m5, m6, m7⟩ := hMM
  dsimp only at m1 m2 m3 m4 m5 m6 m7
  cases m1
  cases m2
  cases m3
  cases m4
  cases m5
  cases m6
  cases m7
  have hv' : v' = v := eq_of_heq hv
  subst hv'
  exact id

private theorem UpperTheory.hasUnitPureTensorPairing_imp_of_heq {D : D7} {W : HSp D} {S S' : D.what₂.Tau → SPar} (M : DSModel W S) (M' : DSModel W S')
    (hMM : GeoTies.ModelSame M M') (v : M.Vec) (v' : M'.Vec) (hv : HEq v' v) {V : HSp D} (c c' : CoefA V)
    (h1 : HEq c'.W c.W) (h2 : HEq c'.nW c.nW) (h3 : HEq c'.iW c.iW)
    {P : Type} [AddCommGroup P] [Module ℂ P] (io : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] P) (io' : LowT M' →ₗ[ℂ] c'.W →ₗ[ℂ] P)
    (hio : HEq io' io) (Δ : P) :
    ((∃ u, IsExtVec M u ∧ UpperTheory.HasUnitPureTensorPairing M c io Δ u) → UpperTheory.HasUnitPureTensorPairing M c io Δ v) →
      ((∃ u, IsExtVec M' u ∧ UpperTheory.HasUnitPureTensorPairing M' c' io' Δ u) → UpperTheory.HasUnitPureTensorPairing M' c' io' Δ v') := by
  obtain ⟨X, σ, lam, ε, fr, _, _, _, _⟩ := M
  obtain ⟨X', σ'', lam', ε', fr', _, _, _, _⟩ := M'
  obtain ⟨m1, m2, m3, m4, m5, m6, m7⟩ := hMM
  dsimp only at m1 m2 m3 m4 m5 m6 m7
  cases m1
  cases m2
  cases m3
  cases m4
  cases m5
  cases m6
  cases m7
  obtain ⟨Y, ρ⟩ := c
  obtain ⟨Y', ρ'⟩ := c'
  dsimp only at h1 h2 h3
  cases h1
  cases h2
  cases h3
  have hv' : v' = v := eq_of_heq hv
  subst hv'
  have hio' : io' = io := eq_of_heq hio
  subst hio'
  exact id

end

theorem UpperTheory.extVecPairing_indep_of_base_same_pre :
    ∀ (B B' : Base) (f : Fr B.toPre) (f' : Fr B'.toPre) (T : TwDat B) (T' : TwDat B') (w : ColW B f T) (w' : ColW B' f' T'),
        B'.toPre = B.toPre → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt) (Z' : w'.Lt) (hX' : B'.fields.Ok)
        (Wt' : Set B'.places.Pl) (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
        (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
        (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
          HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
          HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
          HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
        Formalism.L2.Pj.LawsCore core'.toCore →
        letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr : TrI B' w'.px)
          (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F),
          RSideW z Wt' R' → HEq R'.toLevCh.mu0 z.R.toLevCh.mu0 →
          ∀ ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ y, (w'.st Z').toD7.what₂.embLL (ι y) = (w.st Z).toD7.what₂.embLL y) →
          ∀ (v₀' : ∀ (i : Fin (w'.st Z').toD7.R.m) (σ : (w'.st Z').toD7.what₂.LL →+* ℂ), (R'.MW i σ).Vec),
            (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ σ' : (w'.st Z').toD7.what₂.LL →+* ℂ,
              HEq (v₀' i' σ') (z.geo.v₀ i (σ'.comp ι))) →
          ∀ (i : Fin (w'.st Z').toD7.R.m) (σ : (w'.st Z').toD7.what₂.LL →+* ℂ), Formalism.IndefR.FWT.IsChosenExtremalVector R'.toRealDat i σ (v₀' i σ) := by
  intro B B' f f' T T' w w' hPre Z hX Wt z Z' hX' Wt' core' alg' halg hc _ Xg tr R' hRS _ ι hι v₀' hv i' σ'
  letI := alg'
  letI := z.alg
  have hm : (w'.st Z').toD7.R.m = (w.st Z).toD7.R.m := (by with_unfolding_all exact ((congrArg (fun P : Pre => P.R.m) hPre) :))
  let i : Fin (w.st Z).toD7.R.m := ⟨i'.1, hm ▸ i'.2⟩
  have hi : (i : ℕ) = i' := rfl
  have hb := z.geo.fw.hv₀ i (σ'.comp ι)
  have hall := hRS.2.2.2.2.2.2.2.2.2.2.2.2.1 i i' hi
  have hcl := (hall.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ι hι).1 σ'
  have hMM : GeoTies.ModelSame (z.R.MW i (σ'.comp ι)) (R'.MW i' σ') :=
    ⟨hcl.1.1, hcl.1.2.1, hcl.1.2.2.1, hcl.1.2.2.2.1, hcl.1.2.2.2.2.1, hcl.1.2.2.2.2.2.1, hcl.1.2.2.2.2.2.2.1⟩
  have c1 := hall.1
  have c2 := hall.2.2.1
  have c3 := hall.2.2.2.1
  have hio := hall.2.2.2.2.2.1
  have hv1 := hv i i' hi σ'
  have hs' : sg0 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).A = (w'.st Z').toD7.what₂.embLL :=
    sgAt_mk _ R'.toRealDat.hv0
  have hs : sg0 (w.st Z).toD7 (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A = (w.st Z).toD7.what₂.embLL :=
    sgAt_mk _ z.R.toRealDat.hv0
  clear hcl hall hRS hv hc halg
  generalize v₀' i' σ' = v' at hv1 ⊢
  generalize z.geo.v₀ i (σ'.comp ι) = v at hv1 hb
  have hσ : σ' = sg0 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).A →
      σ'.comp ι = sg0 (w.st Z).toD7 (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A := fun h => by
    rw [h, hs', hs]
    exact RingHom.ext hι
  generalize σ'.comp ι = s at hMM v hv1 hb hσ
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hPre
  subst hPre
  let S₀ : (w'.st Z').toD7.what₂.Tau → SPar := (by with_unfolding_all exact ((parAt (Wc (w.st Z).toD7 i) s) :))
  let M₀ : DSModel (Wc (w'.st Z').toD7 i') S₀ :=
    @DSModel.mk _ _ _ ((by with_unfolding_all exact ((z.R.MW i s).H :))) ((by with_unfolding_all exact ((z.R.MW i s).nacg :))) ((by with_unfolding_all exact ((z.R.MW i s).ips :)))
      ((by with_unfolding_all exact ((z.R.MW i s).σ :))) ((by with_unfolding_all exact ((z.R.MW i s).lam :))) ((by with_unfolding_all exact ((z.R.MW i s).ε :)))
      ((by with_unfolding_all exact ((z.R.MW i s).fr :))) ((by with_unfolding_all exact ((z.R.MW i s).enum :))) ((by with_unfolding_all exact ((z.R.MW i s).ds :)))
      ((by with_unfolding_all exact ((z.R.MW i s).fr_unit :))) ((by with_unfolding_all exact ((z.R.MW i s).fr_gram :)))
  let u₀ : M₀.Vec := (by with_unfolding_all exact (v :))
  refine ⟨UpperTheory.isExtVec_of_same_model M₀ (R'.MW i' σ') ((by with_unfolding_all exact (hMM :))) u₀ v' ((by with_unfolding_all exact (hv1 :))) ((by with_unfolding_all exact (hb.1 :))), fun h => ?_⟩
  have h0 := hσ h
  have hb2 := hb.2 h0
  subst h
  subst h0
  let c₀ : CoefA (Vc (w'.st Z').toD7 i') :=
    @CoefA.mk _ _ (z.R.cV i).W (z.R.cV i).nW (z.R.cV i).iW (z.R.cV i).fW ((by with_unfolding_all exact ((z.R.cV i).ρ :)))
  let io₀ : LowT M₀ →ₗ[ℂ] c₀.W →ₗ[ℂ] PolF (w'.st Z').toD7 (Wc (w'.st Z').toD7 i').rank (Vc (w'.st Z').toD7 i').rank :=
    (by with_unfolding_all exact ((z.R.ioP i) :))
  exact (by with_unfolding_all exact ((UpperTheory.hasUnitPureTensorPairing_imp_of_heq M₀ (R'.MW i' _) ((hMM)) u₀ v' ((hv1)) c₀ (R'.cV i') ((c1)) ((c2)) ((c3))
    io₀ (R'.ioP i') ((hio)) (RealDat.Delta i') ((hb2))) : _))
