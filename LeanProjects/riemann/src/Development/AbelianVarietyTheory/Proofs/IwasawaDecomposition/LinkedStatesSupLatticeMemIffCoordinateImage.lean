import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RealMoveOfParts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupLatticeExtendedDataEqCoordinatewiseImage
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove

namespace GlobalTheory.HeightCounting.SerMove.MKLink
open GlobalTheory.Mem.R3.MKExt Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option maxHeartbeats 4000000 in

theorem mk_iff_of_extN {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T}
    {w' : ColW B' f' T'} {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
    {Wt' : Set B'.places.Pl} (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w'.st Z') w'.I hX' T' Wt')
    (hB : B'.toPre = B.toPre) (hN : ExtN z z') (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m) (hj : (j : ℕ) = j')
    (φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL)
    (hφ : ∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x)
    (y : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL) (y' : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL)
    (hyy : ∀ (k : Fin (z.R.nW j)) (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → y' k' = φ (y k))
    (hy : y ∈ (z.R.FW j).WK) : y ∈ (z.R.FW j).MK ↔ y' ∈ (z'.R.FW j').MK := by
  cases B with | mk P => ?_
  cases B' with | mk P' => ?_
  dsimp only at hB
  subst hB
  have hH : z'.core.Q.H = z.core.Q.H := eq_of_heq hN.H
  have hκ := hN.κ j j' hj
  have ha : wtA (z'.geo.κ j') = wtA (z.geo.κ j) := by
    funext x
    unfold wtA
    refine Finset.sum_congr rfl fun t _ => ?_
    have e1 : ext0 ((z'.geo.κ j').aP t) = ext0 ((z.geo.κ j).aP t) :=
      extendByZero_eq_of_heq_families (fun i => ((w.st Z).toD7.R.sigW (i + 1)).1) hj.symm hκ.1 t
    have e2 : ext0 ((z'.geo.κ j').aM t) = ext0 ((z.geo.κ j).aM t) :=
      extendByZero_eq_of_heq_families (fun i => ((w.st Z).toD7.R.sigW (i + 1)).2) hj.symm hκ.2.1 t
    rw [e1, e2]
    rfl
  have hj1 : (j' : ℕ) + 1 = (j : ℕ) + 1 := by rw [hj]
  have hn : z'.R.nW j' = z.R.nW j :=
    (congrFun (eq_of_heq hN.nW) j').trans (congrArg z.R.nW (Fin.ext hj.symm))
  have hinj : Function.Injective (w'.st Z').toD7.what₂.embLL := RingHom.injective _
  obtain ⟨g, he⟩ : ∃ g, z.geo.fw.e j g = ⟨y, hy⟩ := ⟨_, LinearEquiv.apply_symm_apply _ _⟩
  obtain ⟨g', hgg, hP⟩ := cusp_match' hH hN.Dw hN.l hN.Xo hN.c hN.U hj1 ha hκ.2.2 g
  have hx : ((z.geo.fw.e j g : (z.R.FW j).WK) : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL) = y :=
    congrArg Subtype.val he
  have hx' : y' = ((z'.geo.fw.e j' g' : (z'.R.FW j').WK) : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL) := by
    funext k'
    have hk : ((Fin.cast hn k' : Fin (z.R.nW j)) : ℕ) = k' := rfl
    have h3 := hN.forms j j' hj g g' hgg (Fin.cast hn k') k' hk
    have h4 := hyy (Fin.cast hn k') k' hk
    apply hinj
    rw [h4]
    exact (hφ _).trans ((congrArg (fun v => (w.st Z).toD7.what₂.embLL (v (Fin.cast hn k'))) hx).symm.trans h3.symm)
  subst hx'
  subst hx
  constructor
  · rintro ⟨_, h2⟩
    exact ⟨(z'.geo.fw.e j' g').2, (nrm_le_one_iff z'.geo.fw j' g').2 (hP.2 ((nrm_le_one_iff z.geo.fw j g).1 h2))⟩
  · rintro ⟨_, h2⟩
    exact ⟨(z.geo.fw.e j g).2, (nrm_le_one_iff z.geo.fw j g).2 (hP.1 ((nrm_le_one_iff z'.geo.fw j' g').1 h2))⟩

end GlobalTheory.HeightCounting.SerMove.MKLink

namespace GlobalTheory.HeightCounting.SerMove
open GlobalTheory.Mem.R3.Tr

set_option maxHeartbeats 4000000 in

theorem mk_iff_of_link : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), ∀ (j : Fin (Dof x).R.m) (j' : Fin (Dof x').R.m), (j : ℕ) = j' → ∀ (y : Fin ((sideAt x g hg a).R.nW j) → (Dof x).what₂.LL) (y' : Fin ((sideAt x' g' hg' a').R.nW j') → (Dof x').what₂.LL), (∀ (k : Fin ((sideAt x g hg a).R.nW j)) (k' : Fin ((sideAt x' g' hg' a').R.nW j')), (k : ℕ) = k' → y' k' = ι (y k)) → y ∈ ((sideAt x g hg a).R.FW j).WK → (y ∈ ((sideAt x g hg a).R.FW j).MK ↔ y' ∈ ((sideAt x' g' hg' a').R.FW j').MK) := by
  intro K B B' f f' T T' w w' P P' x x' ι e g g' l hg hg' a a' j j' hj y y' hyy hy
  exact MKLink.mk_iff_of_extN (datAt x g) (datAt x' g') l.enl.1 l.extN j j' hj ι (fun t => l.cp.embLL t) y y' hyy hy

end GlobalTheory.HeightCounting.SerMove
