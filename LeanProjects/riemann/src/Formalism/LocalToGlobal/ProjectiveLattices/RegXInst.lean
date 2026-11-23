import Formalism.LocalToGlobal.ProjectiveLattices.IntegralExtensionOfRegR1
import Formalism.LocalToGlobal.ProjectiveLattices.IntAtExtExtAll
import Formalism.LocalToGlobal.ProjectiveLattices.ValSetAlgSubset

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j)

include h hj in

theorem pt_realise (la : HeightOneSpectrum (𝓞 T.Q.c.F))
    (y : PtV (T.Q.Xo j) T.Q.c (algCls _ _) Unit (fun _ _ _ _ => True) la) :
    ∃ y' : T.PtA j la, ∀ f, vAtV y' f = vAtV y f := by
  rcases y with ⟨q, S, io, e, ho, z, hz, η, hη, rfl⟩
  obtain ⟨η', hη'⟩ := T.G.liesTotal h.points_condition h.bc66 hj la S io e ho z hz
  exact ⟨PtV.mk la ho z hz η' hη', fun _ => rfl⟩

theorem regularity_R1_extended_points : RegularityR1 (recPJ h j hj) (extAll h j hj) := by
  intro w F hF la y'
  rw [extAll_vAt_inc]
  refine (h.reg j hj).int (dom_wtA w) (cutR_le T.C j w F.2) ?_ la y'.1 y'.2
  rintro la' _ ⟨y, rfl⟩
  obtain ⟨y', hy'⟩ := pt_realise h j hj la' y
  have := hF la' y'
  rw [recPJ_vAt_inc, hy'] at this
  exact this

theorem ereal_lin (a c : ℝ) (v : EReal) (h0 : 0 ≤ v) (ht : v ≠ ⊤) :
    (((a + c * v.toReal : ℝ)) : EReal) = (a : EReal) + (c : EReal) * v := by
  have hb : v ≠ ⊥ := fun hb => by simp [hb] at h0
  conv_rhs => rw [← EReal.coe_toReal ht hb]
  push_cast
  rfl

theorem regularity_R2_extended_points :
    RegularityR2 (recPJ h j hj) (extAll h j hj)
      (fun {wL} {n} gens => NoCommonZero (T.Q.Xo j) T.Q.c fun i => (gens i).1) := by
  have hv : ∀ la (y : (recPJ h j hj).Pt la) w (F : (recB h.toLawsCore).Cusp j w),
      (recPJ h j hj).vAt la y ((recPJ h j hj).inc w F) = vAtV y F.1 :=
    fun la y w F => recPJ_vAt_inc h j hj la y w F
  have ev : ∀ la (y : (extAll h j hj).Pt' la) w (F : (recB h.toLawsCore).Cusp j w),
      (extAll h j hj).vAt' la y ((recPJ h j hj).inc w F) = y.1 F.1 :=
    fun la y w F => extAll_vAt_inc h j hj la y w F
  constructor
  · intro wL wE n gens et nus c hc hNZ hX la y'
    have hR := (h.reg j hj).1.2 ⟨(wtA wL, wL.n), dom_wtA wL⟩ ⟨(wtA wE, wE.n), dom_wtA wE⟩ n
      (fun k => ⟨(gens k).1, cutR_le T.C j wL (gens k).2⟩) ⟨et.1, cutR_le T.C j wE et.2⟩ nus c hc hNZ
      (by
        rintro la' ⟨_, ⟨y, rfl⟩⟩
        obtain ⟨y0, hy0⟩ := pt_realise h j hj la' y
        have hx := hX la' y0
        have eet : (recPJ h j hj).vAt la' y0 ((recPJ h j hj).inc wE et) = vAtV y et.1 :=
          (hv la' y0 wE et).trans (hy0 _)
        have egs : (⨅ k, (recPJ h j hj).vAt la' y0 ((recPJ h j hj).inc wL (gens k))) =
            ⨅ k, vAtV y (gens k).1 := iInf_congr fun k => (hv la' y0 wL (gens k)).trans (hy0 _)
        have h0 : 0 ≤ vAtV y et.1 := le_of_le_of_eq hx.1 eet
        show 0 ≤ vAtV y et.1 ∧ (vAtV y et.1 ≠ ⊤ →
          (⨅ k, vAtV y (gens k).1) ≤ (nus la' : EReal) + (c : EReal) * vAtV y et.1)
        refine ⟨h0, fun hne => ?_⟩
        have hne' : (recPJ h j hj).vAt la' y0 ((recPJ h j hj).inc wE et) ≠ ⊤ := by rw [eet]; exact hne
        calc (⨅ k, vAtV y (gens k).1)
            = ⨅ k, (recPJ h j hj).vAt la' y0 ((recPJ h j hj).inc wL (gens k)) := egs.symm
          _ ≤ (((nus la' : ℝ) + c * ((recPJ h j hj).vAt la' y0 ((recPJ h j hj).inc wE et)).toReal : ℝ) :
                EReal) := hx.2 hne'
          _ = (nus la' : EReal) + (c : EReal) * vAtV y et.1 := by
              rw [eet]; exact ereal_lin _ _ _ h0 hne)
    obtain ⟨h1, h2⟩ := hR.1 la ⟨y'.1, y'.2⟩
    have eet : (extAll h j hj).vAt' la y' ((recPJ h j hj).inc wE et) = y'.1 et.1 := ev la y' wE et
    have egs : (⨅ k, (extAll h j hj).vAt' la y' ((recPJ h j hj).inc wL (gens k))) =
        ⨅ k, y'.1 (gens k).1 := iInf_congr fun k => ev la y' wL (gens k)
    have h1' : 0 ≤ y'.1 et.1 := h1
    refine ⟨le_of_le_of_eq h1' eet.symm, fun hne => ?_⟩
    have hne' : y'.1 et.1 ≠ ⊤ := by rw [← eet]; exact hne
    calc (⨅ k, (extAll h j hj).vAt' la y' ((recPJ h j hj).inc wL (gens k)))
        = ⨅ k, y'.1 (gens k).1 := egs
      _ ≤ (nus la : EReal) + (c : EReal) * y'.1 et.1 := h2 hne'
      _ = (((nus la : ℝ) + c * ((extAll h j hj).vAt' la y' ((recPJ h j hj).inc wE et)).toReal : ℝ) :
            EReal) := by rw [eet]; exact (ereal_lin _ _ _ h1' hne').symm
  · intro wL n gens nus hNZ hX la y'
    have hR := (h.reg j hj).2 (wtA wL) wL.n (dom_wtA wL) n (fun k => (gens k).1)
      (fun k => cutR_le T.C j wL (gens k).2) hNZ nus
      (by
        rintro la' _ ⟨y, rfl⟩
        obtain ⟨y0, hy0⟩ := pt_realise h j hj la' y
        have egs : (⨅ k, (recPJ h j hj).vAt la' y0 ((recPJ h j hj).inc wL (gens k))) =
            ⨅ k, vAtV y (gens k).1 := iInf_congr fun k => (hv la' y0 wL (gens k)).trans (hy0 _)
        exact le_of_eq_of_le egs.symm (hX la' y0)) la y'.1 y'.2
    calc (⨅ k, (extAll h j hj).vAt' la y' ((recPJ h j hj).inc wL (gens k)))
        = ⨅ k, y'.1 (gens k).1 := iInf_congr fun k => ev la y' wL (gens k)
      _ ≤ _ := hR

end Formalism.L2.Pj
