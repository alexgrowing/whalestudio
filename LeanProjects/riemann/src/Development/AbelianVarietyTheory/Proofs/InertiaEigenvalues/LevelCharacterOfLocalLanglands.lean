import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EigenCompatibleOfBadSet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AtMemAnd
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section

namespace GlobalTheory.GalLoc.PsiLvl

def PsiRead (D : D7) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) : Prop :=
  ∀ (i : D.ntw.Tw) (u : G0g D.nd) (hu : u ∈ D.nexp.U) (hu' : u ∈ Formalism.IndefR.NX.U D.nd),
    ((D.nexp.psiU i true ⟨u, hu⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) =
      IsFractionRing.map (A := D.ntw.O0 i) (B := D.ntw.O i) (K := FractionRing (D.ntw.O0 i))
        (L := FractionRing (D.ntw.O i)) (D.ntw.O_inj i)
        (D.ntw.emb0 i ((psiUOf D.nd (NX.xiRed D) θ ⟨u, hu'⟩ : (↥D.LL0)ˣ) : ↥D.LL0))

theorem psiRead_withLoc {hL : GlobalTheory.Published.LocalLanglandsGL} {D' : D7} (b : NBuilt hL D') : PsiRead (withLoc b.L) b.θ := by
  intro i u hu hu'
  have h := b.Bs.psiU i true u hu hu'
  exact h

theorem exists_theta_of_eq {D₀ : D7} {L : LocAll (lay0 D₀)} {D' : D7} (h : D' = withLoc L)
    (θ0 : ∀ kk : Fin 2, Multiplicative (ZMod ((withLoc L).host.g kk)) →* (↥(withLoc L).LL0)ˣ)
    (h0 : PsiRead (withLoc L) θ0) :
    ∃ θ : ∀ kk : Fin 2, Multiplicative (ZMod (D'.host.g kk)) →* (↥D'.LL0)ˣ, HEq θ θ0 ∧ PsiRead D' θ := by
  subst h
  exact ⟨θ0, HEq.rfl, h0⟩

theorem atMem_of_forall {hL : GlobalTheory.Published.LocalLanglandsGL} {p : LayP hL}
    (h : ∀ K B f T w Z Wt p0 t nch n c, p K B f T w Z Wt p0 t nch n c) : AtMem hL p := by
  refine ⟨1, one_pos, fun eps C8 C5 c6 Cb _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C _ _ _ => ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨0, fun K _ _ _ _ _ _ => ?_⟩⟩⟩⟩⟩
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp, fun B f T _ _ _ _ => ?_⟩
  intro _ w Z Wt p0 t nch n xd c _ _ _
  exact h K B f T w Z Wt p0 t nch n c

theorem lvlPsi_at : PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t _ _ c =>
    ∃ θ : ∀ kk : Fin 2, Multiplicative (ZMod ((w.D Z).host.g kk)) →* (↥(w.D Z).LL0)ˣ, HEq θ c.a.nt.θ ∧
      GlobalTheory.HeightCounting.RatSide.LvlPsi t.r.z.R t.r.z.F t.r.z.cG θ := by
  intro _ _ hL
  refine atMem_of_forall fun K B f T w Z Wt p0 t nch n c => ?_
  obtain ⟨θ, hθ, hR⟩ := exists_theta_of_eq c.a.nt.eq c.a.nt.θ (psiRead_withLoc c.a.nt.toNBuilt)
  refine ⟨θ, hθ, fun g => ?_, fun u hu => ?_⟩
  · exact (c.row.grp.lvl0 g).trans (SetLike.ext_iff.mp c.a.all.exp.U_eq _)
  · have hu0 : (t.r.z.R.eG.trans t.r.z.cG) u ∈ (w.D Z).nexp.U := (c.row.grp.lvl0 u).1 u.2
    obtain ⟨i⟩ : Nonempty (w.D Z).ntw.Tw := by
      obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 (w.D Z).what₂.LL)
      exact ⟨nch.twI ((w.D Z).plEq.symm
        ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)⟩)⟩
    obtain ⟨x, hx, hx'⟩ := c.row.grp.psi0 u hu0 i true
    have h2 := hR i _ hu0 hu
    have h3 : IsFractionRing.map (A := (w.D Z).ntw.O0 i) (B := (w.D Z).ntw.O i) (K := FractionRing ((w.D Z).ntw.O0 i))
          (L := FractionRing ((w.D Z).ntw.O i)) ((w.D Z).ntw.O_inj i) ((w.D Z).ntw.emb0 i x) =
        IsFractionRing.map (A := (w.D Z).ntw.O0 i) (B := (w.D Z).ntw.O i) (K := FractionRing ((w.D Z).ntw.O0 i))
          (L := FractionRing ((w.D Z).ntw.O i)) ((w.D Z).ntw.O_inj i) ((w.D Z).ntw.emb0 i
          ((psiUOf (w.D Z).nd (NX.xiRed (w.D Z)) θ ⟨(t.r.z.R.eG.trans t.r.z.cG) u, hu⟩ : (↥(w.D Z).LL0)ˣ) : ↥(w.D Z).LL0)) :=
      hx'.symm.trans h2
    have h4 := (IsFractionRing.map (A := (w.D Z).ntw.O0 i) (B := (w.D Z).ntw.O i) (K := FractionRing ((w.D Z).ntw.O0 i))
          (L := FractionRing ((w.D Z).ntw.O i)) ((w.D Z).ntw.O_inj i)).injective h3
    have h5 := ((w.D Z).ntw.emb0 i).injective h4
    exact (congrArg (fun z : ↥(w.D Z).LL0 => (z : (w.D Z).what₂.LL)) h5).symm.trans hx

end GlobalTheory.GalLoc.PsiLvl
