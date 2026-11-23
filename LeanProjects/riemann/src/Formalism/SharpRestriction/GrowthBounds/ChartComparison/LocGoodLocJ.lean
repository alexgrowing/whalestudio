import Formalism.SharpRestriction.GrowthBounds.ChartComparison.StepIn
import Formalism.LocalToGlobal.GroupLattices.LevelCharts.LevelsOfChChartsCover
import Formalism.LocalToGlobal.GroupLattices.LevelCharts.FiniteClassSetOfFiniteIndex
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePtOneRec
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePsi

noncomputable section

namespace Formalism.MainNotions.G.CmpJ

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem gramN_apply (D : D7) (i : ℕ) (hi : i ≤ D.R.m) (x y : Fin (D.R.N i)) :
    gramN D i hi x y = (D.sp.X i).gram (Fin.cast (rankN D i hi).symm x) (Fin.cast (rankN D i hi).symm y) := rfl

variable {D : D7} {X : Formalism.L2.Herm.Herm0 D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w hg)} {Lv : Levels Fl} {i : ℕ}
  (hi : i + 1 ≤ D.R.m) {cmp : Type} [Fintype cmp] {em : cmp → Lv.compS i}
  {Lb : Submodule (𝓞 D.host.E) (Fin (D.sp.X (i + 1)).rank → D.host.E)}
  {Uloc : ∀ v : HeightOneSpectrum (𝓞 D.host.F),
    Subgroup (GL (Fin (D.sp.X (i + 1)).rank) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F))}
  {ψ : awayG D.sp.cm.sig (D.sp.X (i + 1)).gram Uloc (D.what₂.places.resChar w) →* (D.gat u w hg).Oˣ}
  {eps : UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (D.sp.X (i + 1)).gram →* (D.gat u w hg).Oˣ}
  (t : GChartTie (X.g u w hg) Lv i em (D.sp.X (i + 1)).gram Lb Uloc ψ eps)
  (B : GL (Fin (D.sp.X (i + 1)).rank) D.host.E)

set_option maxHeartbeats 1000000 in

def locJ : LocAt D.host.F D.host.E (D.R.N (i + 1)) (gatCh (gatJ Lv (i + 1)) em) where
  rk := t.rk.trans (rankN D (i + 1) hi)
  pl := (X.g u w hg).pl
  eQ := fun v => (X.g u w hg).eQ v _ rfl
  spl := fun v => (X.g u w hg).spl _ ((X.g u w hg).pl v).2
  B := reGL (rankN D (i + 1) hi) _ B
  yG := fun c => reGL (rankN D (i + 1) hi) _ (t.yG c).1
  gamI := fun c => (reGL (rankN D (i + 1) hi) D.host.E).toMonoidHom.comp
    ((UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (D.sp.X (i + 1)).gram).subtype.comp (t.gamI c))

def FrRatJ : Prop :=
  ∀ (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
    t.fr w' h =
      bc (((RingHom.fst _ _).comp ((X.g u w hg).spl w' h).toRingHom).comp
        (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B

theorem locJ_UJ (c : cmp) (γ : ((gatCh (gatJ Lv (i + 1)) em).lev c).Γ) :
    (locJ hi t B).gamI c γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D (i + 1) hi) :=
  reGL_mem_UJ (rankN D (i + 1) hi) _ (D.sp.X (i + 1)).gram _ (gramN_apply D (i + 1) hi) _ (t.gamI c γ).2

set_option maxHeartbeats 4000000 in

theorem locJ_actB (hB : FrRatJ t B) : (locJ hi t B).ActB := by
  refine LocAt.actB_of (locJ hi t B) (rankN D (i + 1) hi) B (fun c γ => (t.gamI c γ).1) rfl (fun _ _ => rfl) ?_
  intro c v γ a b a' b' ha hb
  have h1 := t.act_eq c v _ rfl ((X.g u w hg).pl v).2 γ a b a' b' ha hb
  rw [hB _ ((X.g u w hg).pl v).2, bc_comp] at h1
  exact h1

set_option maxHeartbeats 4000000 in

theorem locGood_locJ : LocGood (sigD D) (gramN D (i + 1) hi) (locJ hi t B) where
  herm := isHerm_re (rankN D (i + 1) hi) _ (D.sp.X (i + 1)).gram _ (gramN_apply D (i + 1) hi) (gram_herm D.sp.cm (D.sp.X (i + 1)))
  det := det_re (rankN D (i + 1) hi) (D.sp.X (i + 1)).gram _ (gramN_apply D (i + 1) hi) (gram_det_unit D.sp.cm (D.sp.X (i + 1)))
  sig := fun v x => (X.g u w hg).spl_sig _ ((X.g u w hg).pl v).2 x
  yG_mem := fun c => reGL_mem_UPts (rankN D (i + 1) hi) D.sp.cm.sig (D.sp.X (i + 1)).gram _ (gramN_apply D (i + 1) hi) _ _ (t.yG c).2
  yG_p := fun c v => by
    have h1 := t.yG_p c _ ((X.g u w hg).pl v).2
    have h2 := bc_reGL (rankN D (i + 1) hi) (prV (E := D.host.E) ((X.g u w hg).pl v).1) (t.yG c).1
    rw [h1, map_one] at h2
    exact h2

theorem locInt_locJ : LocInt (locJ hi t B) :=
  fun v x => (X.g u w hg).completion_integers_iff v _ rfl x

end Formalism.MainNotions.G.CmpJ

end
