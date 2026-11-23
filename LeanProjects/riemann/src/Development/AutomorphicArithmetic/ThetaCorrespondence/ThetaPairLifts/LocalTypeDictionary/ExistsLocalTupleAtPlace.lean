import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EmbeddingCompatAtPlace
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LocalFixedPointAtPlace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EmbeddingCompatAtPlaceStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)
namespace GlobalTheory.PlaceTup
theorem has_local_tuples_at_place : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayer → ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
  ∀ τ : ℂ ≃+* ℂ, (∀ a, τ (embLL0 D a) = embLL0 D a) → ∀ ψ' : Twist D Circle, ψ'.Good → ConjChar τ (twVia Z.ρ ι) ψ' →
  GlobalTheory.BigOn.Exp.TwConj.HasTuples X.core X.R.toRealDat X.geo.κ X.geo.v₀ X.geo.O (fun _ => 1) j (baseOf Z c w j) (twVia Z.ρ ι) ψ' := by
  intro hDS hCW _ hP D X X0 Y S YS Z c w j H ι hι τ hτ ψ' hψ' hC
  have hC0 := X.char
  have hL : GlobalTheory.BigOn.Exp.TwConj.Laws X.core X.R.toRealDat X.F.lv2 X.geo.κ X.geo.v₀ X.geo.O (fun _ => 1) j (baseOf Z c w j) :=
    ⟨⟨hC0.lev, hC0.grp, hC0.fam, hC0.models, hC0.chain, hC0.thP⟩, X.finT, ⟨X.geo.fw⟩,
      GlobalTheory.IoExtremal.ioExt D _ _ _ _ _ X.R.toRealDat hC0.lev hC0.fam hC0.models hC0.thP, X.guard, X.geo.pins j,
      by
        convert X.geo.phase j X.unif using 2
        all_goals (rename_i k; rw [X.phs k]; try simp),
      GlobalTheory.BigOn.Exp.TwConj.baseOf_of_realPin hC0.lev Z.good Z.pin (c.twI w) j (c.sd w)⟩
  exact GlobalTheory.T.twist_conjugate_tuples_same_realisation_extension hDS hCW hP.decay hP.what₂.art hP.ray X.core X.R.toRealDat X.F.lv2 X.geo.κ X.geo.v₀ X.geo.O (fun _ => 1) j
    (baseOf Z c w j) X.host hL (twVia Z.ρ ι) ψ' (Y.tupT (D.what₂.muTw w)) τ (H.tup ι hι) hC
    (_root_.GlobalTheory.PlaceFix.fixed_at_place_of_local hP D X X0 Y S YS Z c w j H τ hτ).2
end GlobalTheory.PlaceTup
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_tuple_at_place : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayer → ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
  ∀ τ : ℂ ≃+* ℂ, (∀ a, τ (embLL0 D a) = embLL0 D a) → ∀ ψ' : Twist D Circle, ψ'.Good → ConjChar τ (twVia Z.ρ ι) ψ' →
  GlobalTheory.BigOn.Exp.TwConj.HasTuples X.core X.R.toRealDat X.geo.κ X.geo.v₀ X.geo.O (fun _ => 1) j (baseOf Z c w j) (twVia Z.ρ ι) ψ' := by
  first | exact @_root_.GlobalTheory.PlaceTup.has_local_tuples_at_place | exact _root_.GlobalTheory.PlaceTup.has_local_tuples_at_place | (intros; apply _root_.GlobalTheory.PlaceTup.has_local_tuples_at_place <;> assumption)
end
