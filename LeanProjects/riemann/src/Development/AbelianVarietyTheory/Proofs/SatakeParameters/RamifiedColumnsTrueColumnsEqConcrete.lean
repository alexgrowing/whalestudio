import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JetSplitAmb
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JetOpIntegral
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Formalism.SharpRestriction.ElevenLe
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FormMapRBijective
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EmbFColFormMemMram
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColStep0MemLat
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistedChainInitialLatticeCompatibleTrueColumns
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelsOverOfFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.AtG

attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.AtG

theorem ramCols_true : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} (I : GlobalTheory.Mem.Col2.TC B X) (h : I.Ok) (l : I.Laws) (Z : GlobalTheory.Mem.Col2.TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word), ∃ eM : ((I.rec7 l Z).div.Nu u).V ≃+ Formalism.L2.Col.MramV (Pr := B.primes X) B.wts I.Ch u, (∀ (r : (I.rec7 l Z).what₂.LL) x, eM (r • x) = (show B.fields.K from r) • eM x) ∧ (∀ x, x ∈ DV.MramL (I.rec7 l Z) u ↔ eM x ∈ Formalism.L2.Col.MramL (Pr := B.primes X) B.wts I.Ch u) ∧ (∀ x, (I.rec7 l Z).nuIn u x = GlobalTheory.Mem.Col2.KerRat.colForm I l h u I.mu0 (eM x).1) ∧ ∀ a φ, (I.fm l u a).emb 0 (GlobalTheory.Mem.Col2.KerRat.colForm I l h u a φ) = (I.cols l).e0Tw u a ((I.fm l u I.mu0).emb 0 (GlobalTheory.Mem.Col2.KerRat.colForm I l h u I.mu0 φ)) := by
  intro B X I h l Z l0 u
  have hX := (GlobalTheory.Mem.Col2.base_fields_primes_ok B X).1
  obtain ⟨κ, hκ⟩ := GlobalTheory.Core.ColZero.exists_colEquiv I h hX l u I.mu0
  have hκc : ∀ φ, κ φ = GlobalTheory.Mem.Col2.KerRat.colForm I l h u I.mu0 φ := fun φ => Subtype.ext (funext (hκ φ))
  have hram : ∀ φ, κ φ ∈ (I.fm l u I.mu0).ramSub ↔ φ ∈ Formalism.L2.Col.MramV (Pr := B.primes X) B.wts I.Ch u := fun φ =>
    GlobalTheory.Core.ColRam.isCol_mem_ramSub_iff I h hX l u I.mu0 (κ φ) φ (hκ φ)
  have hrange : ∀ x, (I.rec7 l Z).nuIn u x ∈ (I.fm l u I.mu0).ramSub := fun x =>
    (I.rec7 l Z).nuIn_range u ▸ ⟨x, rfl⟩
  have hinj := (I.rec7 l Z).nuIn_inj u
  have hsurj : ∀ φ : Formalism.L2.Col.MramV (Pr := B.primes X) B.wts I.Ch u, ∃ x, (I.rec7 l Z).nuIn u x = κ φ.1 := by
    intro φ
    have hm : κ φ.1 ∈ LinearMap.range ((I.rec7 l Z).nuIn u) := (I.rec7 l Z).nuIn_range u ▸ (hram φ.1).2 φ.2
    exact hm
  let f : ((I.rec7 l Z).div.Nu u).V → Formalism.L2.Col.MramV (Pr := B.primes X) B.wts I.Ch u := fun x =>
    ⟨κ.symm ((I.rec7 l Z).nuIn u x), (hram _).1 (Eq.subst (motive := fun y => y ∈ (I.fm l u I.mu0).ramSub) (κ.apply_symm_apply ((I.rec7 l Z).nuIn u x)).symm (hrange x))⟩
  have hf : ∀ x, κ (f x).1 = (I.rec7 l Z).nuIn u x := fun x => κ.apply_symm_apply _
  have fbij : Function.Bijective f := by
    refine ⟨fun x y e => hinj ?_, fun φ => ?_⟩
    · rw [← hf x, ← hf y, e]
    · obtain ⟨x, hx⟩ := hsurj φ
      exact ⟨x, Subtype.ext (by rw [← κ.injective.eq_iff, hf, hx])⟩
  have fadd : ∀ x y, f (x + y) = f x + f y := fun x y => Subtype.ext (by
    exact (congrArg κ.symm (map_add ((I.rec7 l Z).nuIn u) x y)).trans (map_add κ.symm _ _))
  refine ⟨AddEquiv.ofBijective (AddMonoidHom.mk' f fadd) fbij, ?_, ?_, ?_, ?_⟩
  · intro r x
    apply Subtype.ext
    show κ.symm _ = _
    exact (congrArg κ.symm (map_smul ((I.rec7 l Z).nuIn u) r x)).trans (map_smul κ.symm _ _)
  · intro x
    have e := GlobalTheory.Core.Ht2.colStep0_mem_lat I h hX l u I.mu0 (κ (f x).1) (f x).1 (hκ _)
    show (I.rec7 l Z).nuIn u x ∈ ((I.fm l u I.mu0).lat 0).L ↔ (f x).1 ∈ Formalism.L2.Col.MfL (Pr := B.primes X) B.wts I.Ch u
    exact (Eq.subst (motive := fun y => (y ∈ ((I.fm l u I.mu0).lat 0).L ↔ (f x).1 ∈ Formalism.L2.Col.MfL (Pr := B.primes X) B.wts I.Ch u)) (hf x) e)
  · intro x
    show _ = GlobalTheory.Mem.Col2.KerRat.colForm I l h u I.mu0 (f x).1
    rw [← hκc, hf]
  · intro a φ
    funext c'
    have e := GlobalTheory.LvT.TrueStep0.rep_eCls0_symm h l u a c'
    show Formalism.L2.Col.evV _ _ _ _ (φ.1 ((I.stp u a 0).rep c').1.1.deco) =
      Formalism.L2.Col.evV _ _ _ _ (φ.1 ((I.stp u I.mu0 0).rep ((I.eCls0 l u a).symm c')).1.1.deco)
    rw [e]

end GlobalTheory.AtG
