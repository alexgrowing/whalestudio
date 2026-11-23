import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MapBaseTiedSel
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealPins3RealTOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealPinsRealTOf
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Div.PgTie

open Classical in

theorem image_congr {D : D7} {X X' : Formalism.L2.Col.Fields} (hX : X = X') {s : Formalism.L2.Ker.Seam D X} {s' : Formalism.L2.Ker.Seam D X'}
    (hs : HEq s s') {Pr : Formalism.L2.Col.Primes X} {Pr' : Formalism.L2.Col.Primes X'} (hP : HEq Pr Pr') :
    Pr.vGs.image (Formalism.L2.Host.CT.plMap s.iE) = Pr'.vGs.image (Formalism.L2.Host.CT.plMap s'.iE) := by
  subst hX
  cases hs
  cases hP
  rfl

theorem plMap_refl {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) :
    Formalism.L2.Host.CT.plMap (RingEquiv.refl E) P = P := by
  ext x
  exact Formalism.L2.Host.CT.mem_plMap (RingEquiv.refl E) P x

open Classical in

theorem image_refl {E : Type} [Field E] [NumberField E] (f : E ≃+* E) (hf : f = RingEquiv.refl E)
    (S : Finset (HeightOneSpectrum (𝓞 E))) : S.image (Formalism.L2.Host.CT.plMap f) = S := by
  subst hf
  rw [show Formalism.L2.Host.CT.plMap (RingEquiv.refl E) = id from funext plMap_refl, Finset.image_id]

open Classical in
set_option maxHeartbeats 4000000 in

theorem pgEq_of_linked : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Prm hL), GlobalTheory.Fc.EvP fun _ K => ∀ (q : WPt p.s K) (c : ℝ) (b : GlobalTheory.Fc.Bundle (q.w.D q.Z) q.O c) (w : BWit q b), q.O.L.sc = K.s → (open Classical in w.x.R.Pg = b.R.T.ker.Pr.vGs.image (Formalism.L2.Host.CT.plMap b.R.T.ker.seam.iE)) := by
  intro hL p
  refine GlobalTheory.Fc.EvP.of_all ?_
  intro _ K _ q c b w _
  have hk := w.recPin.k.std
  rw [image_congr hk.X_eq hk.seam hk.Pr]
  have hl := q.x.what₂.r.z.lev.Pg
  obtain ⟨x, a, ax, y, _⟩ := w
  cases ax
  obtain ⟨Dc, Sp, Zsc, lam, err, lam_eq, x, pack, _⟩ := a
  obtain ⟨G, grp, fin, Pl0, I0, T0, A3, core, alg, R, F, cG, _⟩ := x
  dsimp only at pack ⊢
  cases pack
  exact hl.trans (image_refl _ rfl _).symm

end GlobalTheory.Div.PgTie
