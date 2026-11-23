import Formalism.AdmissibleDesigns.MemUnramifiedOfCoboundary

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TB

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR

section Record

open Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i)
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (Formalism.MainNotions.N.RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (Formalism.MainNotions.N.RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

abbrev Qcore (c : Fin (D.R.t + 1)) (n cB : ℕ) : Type :=
  ↥(Hc i dc Dd c n ⊓ divBy (Fc i dc Dd c n) (((D.nd.l i : ℕ) : D.nd.O i) ^ cB)) ⧸
    (Fc i dc Dd c n).comap (Hc i dc Dd c n ⊓ divBy (Fc i dc Dd c n) (((D.nd.l i : ℕ) : D.nd.O i) ^ cB)).subtype

def TBLenAt (cB : ℕ) (n : ℕ) (c : Fin (D.R.t + 1)) : Prop :=
  Module.length (D.nd.O i) (Qcore i dc Dd c n cB) ≤
    Module.length (D.nd.O i) (D.nd.O i ⧸ Ideal.span {((D.nd.l i : ℕ) : D.nd.O i)}) * (cB : ℕ∞) *
      ((Formalism.MainNotions.N.locDeg D.host.E (plOf i dc n) : ℕ∞) + 1)

def TBLen (cB : ℕ) : Prop :=
  ∀ n ∈ rowsN i dc, ∀ c : Fin (D.R.t + 1), 1 ≤ (c : ℕ) → TBLenAt i dc Dd cB n c

def TrivialBoundAtRows (cB : ℕ) : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), w ∈ dc.row →
    Formalism.MainNotions.N.TBAt (Br.PD D.loc D.nbr i w hw) (O := ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL)) (Br.inert D.nbr i w hw)
      (Jr i r π (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)) D.R.t cB

theorem row_trivial_bound_of_admitted (cB : ℕ) (hG : SelfGood i) (h : TruncatedSeriesCountingIdentities.admTB i r π cB) : TrivialBoundAtRows i dc r π cB := by
  intro w hw _
  exact h w hw _ (hG w hw)

theorem eW_symm_cont {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    Continuous (eW i dc hw).symm := by
  have h1 : Continuous (D.nbr i w hw).e.symm := (D.nbr i w hw).e_symm_cont
  have h2 : Continuous (MulEquiv.subgroupCongr (Dw_idx i dc hw)).symm :=
    continuous_induced_rng.2 continuous_subtype_val
  exact h2.comp h1

theorem eW_inert {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (g : Dw i dc (idx i dc w)) (hg : g ∈ (Ine (F := D.host.E) (Aw i dc (idx i dc w))).subgroupOf (Dw i dc (idx i dc w))) :
    eW i dc hw g ∈ Br.inert D.nbr i w hw := by
  have hmem : w ∈ plSet i dc := by
    simp only [plSet, Finset.mem_union]
    exact Or.inl ((dc.cover w).2 hw)
  have hA : Aw i dc (idx i dc w) = D.nd.plOm.1 w := by
    unfold Aw
    rw [plOf_idx i dc hmem]
  unfold Br.inert
  rw [Subgroup.mem_subgroupOf, hA] at hg
  simp only [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Br.iota]
  have hx : ((Br.ι (D.nbr i w hw) (eW i dc hw g)) : GE D.nd) = (g : GE D.nd) := by
    simp [Br.ι, eW]
  rw [hx]
  exact hg

set_option maxHeartbeats 1000000 in

theorem tbTarget_of (cB : ℕ) (hTB : TrivialBoundAtRows i dc r π cB) (hd : TBDict i dc r π Dd)
    (hlen : TBLen i dc Dd cB) : TBTarget i dc Dd cB := by
  intro n hn c hc
  have hlen' := hlen n hn c hc
  obtain ⟨w, hwrow, rfl⟩ := Finset.mem_image.1 hn
  have hw : w ∈ placesOver D.host.E (D.nd.l i) := (dc.cover w).1 (Or.inl hwrow)
  obtain ⟨Y, Cd, hY, hψ, hloc⟩ := hd w hw hwrow c hc
  have hT : Formalism.MainNotions.N.TBAt (Br.PD D.loc D.nbr i w hw) (O := ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL)) (Br.inert D.nbr i w hw)
      (Jr i r π (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)) D.R.t cB := hTB w hw hwrow
  have het : (c : ℕ) - 1 < D.R.t := by
    have := c.2
    omega
  have hp : (Br.PD D.loc D.nbr i w hw).p = D.nd.l i := Br.PD_p D.loc D.nbr i w hw
  refine ⟨?_, le_rfl, ?_, hlen'⟩
  · unfold Fc Hc
    split_ifs
    · exact inf_le_left
    · exact bot_le
  · intro ψ hψe z hz
    unfold Fc
    split_ifs with h1
    · obtain ⟨hzl, m, hm⟩ := tb_zero (σ := selfO i hw) (M := Mc i Dd c) (eG := eW i dc hw) hT (by omega) het Y hY Cd hψ hloc (eW_symm_cont i dc hw) hp
        ((Ine (F := D.host.E) (Aw i dc (idx i dc w))).subgroupOf (Dw i dc (idx i dc w))) (eW_inert i dc hw)
        ψ hψe z hz
      rw [← map_smul]
      exact ⟨mem_locally_constant_of _ _ (hzl.comp (fun m => ((D.nd.l i : D.nd.O i) ^ cB) • m)),
        mem_unramified_of_coboundary _ _ _ m hm⟩
    · have := tb_pos (σ := selfO i hw) (M := Mc i Dd c) (eG := eW i dc hw) hT (by omega) het Y hY Cd hψ hloc (eW_symm_cont i dc hw) hp ψ hψe z hz
      rw [Submodule.mem_bot, ← map_smul]
      exact mkQ_eq_zero_of _ _ this

end Record

end Formalism.MainNotions.N.K.TB

end
