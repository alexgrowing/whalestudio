import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicCoreTransportEnlargedCoefficientBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseChangeEquivCrdOver
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ModelSame
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult GlobalTheory.RealGeo
set_option maxHeartbeats 4000000

theorem UpperTheory.cuspCoreDatum_transport_of_same_pre :
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
          ∃ (v₀' : ∀ (i : Fin (w'.st Z').toD7.R.m) (σ : (w'.st Z').toD7.what₂.LL →+* ℂ), (R'.MW i σ).Vec),
            (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ σ' : (w'.st Z').toD7.what₂.LL →+* ℂ,
              HEq (v₀' i' σ') (z.geo.v₀ i (σ'.comp ι))) := by
  intro B B' f f' T T' w w' hPre Z hX Wt z Z' hX' Wt' core' alg' halg hcore hlaws Xg tr R' hR hmu ι hι
  obtain ⟨P'⟩ := B'
  dsimp only at hPre
  subst hPre
  clear hmu hlaws hcore
  have key : ∀ (i : Fin (w'.st Z').toD7.R.m) (σ : (w'.st Z').toD7.what₂.LL →+* ℂ),
      ∃ v : (R'.MW i σ).Vec, HEq v (z.geo.v₀ i (σ.comp ι)) := by
    intro i σ
    have hs := ((hR.2.2.2.2.2.2.2.2.2.2.2.2.1 i i rfl).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ι hι).1 σ
    obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, -⟩, -⟩ := hs
    clear hR
    generalize R'.MW i σ = M' at h1 h2 h3 h4 h5 h6 h7 ⊢
    obtain @⟨H, nacg, ips, sg, lam, ep, fr, enum, ds, fu, fg⟩ := M'
    dsimp only at h1 h2 h3 h4 h5 h6 h7
    ( (
  have e : @Eq (type_of% (H)) ((by with_unfolding_all exact (((z.R.MW i (σ.comp ι)).H) :))) (H) := (by with_unfolding_all exact ((@eq_of_heq (type_of% (H)) (H) ((((z.R.MW i (σ.comp ι)).H))) (((h1)))).symm : _))
  clear (h1)
  subst e))
    ( (
  have e : @Eq (type_of% (nacg)) ((by with_unfolding_all exact (((z.R.MW i (σ.comp ι)).nacg) :))) (nacg) := (by with_unfolding_all exact ((@eq_of_heq (type_of% (nacg)) (nacg) ((((z.R.MW i (σ.comp ι)).nacg))) (((h2)))).symm : _))
  clear (h2)
  subst e))
    ( (
  have e : @Eq (type_of% (ips)) ((by with_unfolding_all exact (((z.R.MW i (σ.comp ι)).ips) :))) (ips) := (by with_unfolding_all exact ((@eq_of_heq (type_of% (ips)) (ips) ((((z.R.MW i (σ.comp ι)).ips))) (((h3)))).symm : _))
  clear (h3)
  subst e))
    ( (
  have e : @Eq (type_of% (sg)) ((by with_unfolding_all exact (((z.R.MW i (σ.comp ι)).σ) :))) (sg) := (by with_unfolding_all exact ((@eq_of_heq (type_of% (sg)) (sg) ((((z.R.MW i (σ.comp ι)).σ))) (((h4)))).symm : _))
  clear (h4)
  subst e))
    ( (
  have e : @Eq (type_of% (lam)) ((by with_unfolding_all exact (((z.R.MW i (σ.comp ι)).lam) :))) (lam) := (by with_unfolding_all exact ((@eq_of_heq (type_of% (lam)) (lam) ((((z.R.MW i (σ.comp ι)).lam))) (((h5)))).symm : _))
  clear (h5)
  subst e))
    ( (
  have e : @Eq (type_of% (ep)) ((by with_unfolding_all exact (((z.R.MW i (σ.comp ι)).ε) :))) (ep) := (by with_unfolding_all exact ((@eq_of_heq (type_of% (ep)) (ep) ((((z.R.MW i (σ.comp ι)).ε))) (((h6)))).symm : _))
  clear (h6)
  subst e))
    ( (
  have e : @Eq (type_of% (fr)) ((by with_unfolding_all exact (((z.R.MW i (σ.comp ι)).fr) :))) (fr) := (by with_unfolding_all exact ((@eq_of_heq (type_of% (fr)) (fr) ((((z.R.MW i (σ.comp ι)).fr))) (((h7)))).symm : _))
  clear (h7)
  subst e))
    exact ⟨(by with_unfolding_all exact ((z.geo.v₀ i (σ.comp ι)) :)), (by with_unfolding_all exact ((HEq.refl (z.geo.v₀ i (σ.comp ι))) :))⟩
  choose v hv using key
  refine ⟨v, fun i i' hi σ' => ?_⟩
  have e : i = i' := Fin.ext hi
  subst e
  exact hv i σ'
