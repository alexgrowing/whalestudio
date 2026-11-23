import Formalism.SharpRestriction.GrowthBounds.ChartComparison.StepIn
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieWeak
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieDim
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.MRatSpanOfRatInv

noncomputable section

namespace Formalism.MainNotions.G.CmpJ

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ}
  {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p} {S : StepIn M i hi G}

namespace StepIn

theorem Core.iw_eq {e : D.what₂.LL →+* G.Kf} {β β' : S.Ch} (H : S.Core e β) (H' : S.Core e β') (v : Fin G.P.nV) (x : D.host.E) :
    (S.loc β).iw v x = (S.loc β').iw v x := by
  have h0 : 0 < G.P.n' v := lt_of_lt_of_le (by norm_num) (G.P.setting v).two_le
  apply (G.P.ι v).injective
  have h1 := H.pos_emb v ⟨0, h0⟩ x
  have h2 := H'.pos_emb v ⟨0, h0⟩ x
  simp only [pow_zero] at h1 h2
  exact h1.symm.trans h2

theorem Core.posCompat {e : D.what₂.LL →+* G.Kf} {β : S.Ch} (H : S.Core e β) :
    PosCompat G e (S.loc β).iw (fun v s => tPos (sigD D) (tEL D) S.pos v s) := by
  intro v s x
  rw [tPos_apply]
  exact H.pos_emb v s x

theorem Core.actE {e : D.what₂.LL →+* G.Kf} {β : S.Ch} (H : S.Core e β) (a : S.cmpt β) (γ : ((S.charts.gat β).lev a).Γ) :
    ∃ g : GL (Fin (G.P.m + 1)) D.host.E, ∀ v, ((S.charts.gat β).lev a).act v γ = Matrix.GeneralLinearGroup.map ((S.loc β).iw v) g := by
  refine ⟨(castGL (S.loc β).rk D.host.E).symm ((S.loc β).B⁻¹ * (S.loc β).gamI a γ * (S.loc β).B), fun v => ?_⟩
  have h1 : ((S.charts.gat β).lev a).act v γ = bc ((S.loc β).iw v)
      ((castGL (S.loc β).rk D.host.E).symm ((S.loc β).B⁻¹ * (S.loc β).gamI a γ * (S.loc β).B)) := by
    rw [← castGL_symm_bc, ← H.actB a v γ, MulEquiv.symm_apply_apply]
    rfl
  rw [h1]
  apply Units.ext
  ext a b
  rfl

theorem Core.chiRatG {e : D.what₂.LL →+* G.Kf} {β : S.Ch} (H : S.Core e β) (a : S.cmpt β) (γ : ((S.charts.gat β).lev a).Γ) :
    ∃ r : D.what₂.LL, e r = algebraMap G.O G.Kf (((S.charts.gat β).lev a).χ γ : G.O) := by
  obtain ⟨κ, hκ⟩ := awayEx_of H.good (S.K β).lev H.gam a γ
  obtain ⟨r, _, hr⟩ := H.chi a γ κ hκ
  exact ⟨r⁻¹, by rw [map_inv₀]; exact (eq_inv_of_mul_eq_one_left hr).symm⟩

def IwF (S : StepIn M i hi G) (β : S.Ch) : Prop :=
  ∀ v (a : D.host.F), (S.loc β).iw v (algebraMap D.host.F D.host.E a) =
    ((S.loc β).eQ v).symm (algebraMap D.host.F (((S.loc β).pl v).1.adicCompletion D.host.F) a)

theorem desc [IsFractionRing G.O G.Kf] (e : D.what₂.LL →+* G.Kf) (H : ∀ β, S.Core e β) (hF : ∀ β, S.IwF β)
    (pw : HeightOneSpectrum (𝓞 D.what₂.LL))
    (hσ : ∀ x : D.what₂.LL, pw.valuation D.what₂.LL x ≤ 1 ↔ e x ∈ Set.range (algebraMap G.O G.Kf)) (hfin : G.FinClasses) :
    MRatSpan G.P G.comp e G.M := by
  by_cases hne : Nonempty S.Ch
  · obtain ⟨β0⟩ := hne
    have hA : ActE G (S.loc β0).iw := by
      intro c γ
      obtain ⟨⟨β, a⟩, rfl⟩ := S.eC.surjective c
      obtain ⟨g, hg⟩ := (H β).actE a γ
      refine ⟨g, fun v => ?_⟩
      have h1 : (S.loc β).iw v = (S.loc β0).iw v := RingHom.ext fun x => (H β).iw_eq (H β0) v x
      rw [← h1]
      exact hg v
    have hC : ChiRat G e := by
      intro c γ
      obtain ⟨⟨β, a⟩, rfl⟩ := S.eC.surjective c
      exact (H β).chiRatG a γ
    have hW : WeakApprox G (S.loc β0).iw := weak_of_locAt (S.charts.gat β0) (S.loc β0) (hF β0) (H β0).int
    exact mRatSpan_of_rat_inv G e pw hσ hfin (ratLev_of G e (S.loc β0).iw _ (H β0).posCompat hA hC)
      (ratBasis_of G e (S.loc β0).iw _ (H β0).posCompat (ratTup_of_weak G (S.loc β0).iw hW))
  · have hE : IsEmpty G.comp := ⟨fun c => hne ⟨(S.eC.symm c).1⟩⟩
    have hs : Subsingleton (FnP G.P G.comp) := ⟨fun a b => funext fun c => (hE.false c).elim⟩
    unfold MRatSpan
    ext x
    have hx : x = 0 := Subsingleton.elim _ _
    rw [hx]
    exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩

theorem cmpJ_mem_span (e : D.what₂.LL →+* G.Kf) (H : ∀ β, S.Core e β) (hS : BlockRationalityField) (w : D.what₂.places.Pl) (hw : S.okW w)
    (hloc : S.ValIntJ e w) (x : (M.lat i).V) : cmpJL e H hS x ∈ Submodule.span G.Kf (G.M : Set G.Fn) := by
  have hx : x ∈ Submodule.span D.what₂.LL ((M.lat i).L : Set (M.lat i).V) := by
    rw [(M.lat_good i).2.2]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    apply Submodule.subset_span
    exact (cmpJ_lat e H hS w hw hloc y).2 (Submodule.subset_span hy)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ h1 h2 => rw [map_add]; exact Submodule.add_mem _ h1 h2
  | smul a y _ h1 => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ h1

theorem cmpJ_li (e : D.what₂.LL →+* G.Kf) (H : ∀ β, S.Core e β) (hS : BlockRationalityField) :
    LinearIndependent G.Kf fun a => cmpJL e H hS ((M.lat i).b a) :=
  li_of_rat e (evG G) (cmpJL e H hS).toAddMonoidHom (evG_sep G) (fun a x => (cmpJL e H hS).map_smulₛₗ a x)
    (fun x => (ratFn_iff G e _).1 (cmpJ_rat e x)) (cmpJ_inj e H hS) _ (M.lat i).b.linearIndependent

theorem surj_of_card [IsFractionRing G.O G.Kf] [Module.Finite G.O G.M] (e : D.what₂.LL →+* G.Kf) (H : ∀ β, S.Core e β)
    (hS : BlockRationalityField) (w : D.what₂.places.Pl) (hw : S.okW w) (hloc : S.ValIntJ e w)
    (hcard : Fintype.card (M.lat i).ι = Module.finrank G.O G.M) (Fn : G.Fn) (hFn : Fn ∈ G.M) (hrat : RatFn G e Fn) :
    ∃ x, S.cmpJ e x = Fn := by
  have h1 : Fn ∈ Submodule.span G.Kf (Set.range fun a => cmpJL e H hS ((M.lat i).b a)) :=
    mem_span_of_card G.M _ (cmpJ_li e H hS) (fun a => cmpJ_mem_span e H hS w hw hloc _) hcard Fn hFn
  have h2 : Fn ∈ Submodule.span G.Kf (Set.range (cmpJL e H hS).toAddMonoidHom) := by
    refine Submodule.span_mono ?_ h1
    rintro _ ⟨a, rfl⟩
    exact ⟨_, rfl⟩
  exact rat_mem e (evG G) (cmpJL e H hS).toAddMonoidHom (evG_sep _) (fun a x => (cmpJL e H hS).map_smulₛₗ a x)
    (fun x => (ratFn_iff _ _ _).1 (cmpJ_rat e x)) h2 ((ratFn_iff _ _ _).1 hrat)

end StepIn

end Formalism.MainNotions.G.CmpJ

end
