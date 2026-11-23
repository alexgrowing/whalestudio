import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearExtensionOfFormWithTransportedReStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelFlagDomainTransporterMemDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UsedRunCuspFormReadingMemModelCuspFormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UsedRunCuspFormReadingLinearIndependentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelCuspFormsSpanUsedRunReadingsStatement

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares

namespace GlobalTheory.ShareOn.Reading

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Main2
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

open GlobalTheory.OnTies in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in

theorem reading_of_runModel (p : PtAt ex Csz) (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r) (i : Fin D.R.m) {C : Type}
    [Finite C] [MulAction p.P.Gp C] (M : TwoLevels D.host.E D.R.r p.P.Gp C) (ka : Wt M.Ψ D.R.r)
    (hb0 : 0 < badN D) (hn : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV) (hM : RunModel p r h i M ka) :
    M.Ψ.card = D.R.f ∧ ∃ (ρ : Representation ℂ p.P.Gp (M.cusp ka)) (σ : D.what₂.LL →+* ℂ)
      (f : (Fin (p.R.toRealDat.nW i) → D.what₂.LL) →ₛₗ[σ] M.cusp ka),
      IsPullRep M ka ρ ∧ (∀ g v, ρ g (f v) = f ((p.R.toRealDat.FW i).ρ g v)) ∧
      (LinearIndependent ℂ fun k => f (Pi.single k 1)) ∧ Submodule.span ℂ (Set.range f) = ⊤ := by
  refine ⟨card_of_runModel hM, ?_⟩
  obtain ⟨v, e, ha, hb, hc, -⟩ := hM
  obtain ⟨act, hact, hcu⟩ := h.action v i

  let Rd : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i) →ₛₗ[(r.used v).full.σ₀] M.cusp ka :=
    LinearMap.codRestrict (M.cusp ka) (rdLin h ha) fun F => Submodule.subset_span ⟨_, GlobalTheory.T.usedRunCuspForm_reading_mem_modelCuspForms h ha hb F, rfl⟩
  have hRd : ∀ F, ((Rd F : M.cusp ka) : C → M.dom → ℂ) = rdLin h ha F := fun F => rfl
  letI : Algebra (r.used v).full.J.Q.c.F D.what₂.LL := p.alg
  obtain ⟨σ, hσ⟩ := exists_ext_embedding (K := (r.used v).full.J.Q.c.F) (LL := D.what₂.LL) (r.used v).full.σ₀
  let cu := cuspTo (h.laws v).p (fw2 p) i
  have hcuW : ∀ F, cu F ∈ ((R2 p).FW i).WK := fun F => ((fw2 p).e i _).2
  have hcuinj : Function.Injective cu := by
    intro F G hFG
    have h1 := Subtype.ext hFG
    have h2 := ((fw2 p).e i).injective h1
    exact Submodule.inclusion_injective _ h2
  have hsurj : ∀ w ∈ ((R2 p).FW i).WK, ∃ F, cu F = w := by
    intro w hw
    refine ⟨⟨(((fw2 p).e i).symm ⟨w, hw⟩).1, by
      rw [cutR_eq _ (inR_succ i)]; exact (((fw2 p).e i).symm ⟨w, hw⟩).2⟩, ?_⟩
    show ((((fw2 p).e i) _ : ((R2 p).FW i).WK) : Fin _ → D.what₂.LL) = w
    exact congrArg Subtype.val (LinearEquiv.apply_symm_apply ((fw2 p).e i) ⟨w, hw⟩)
  obtain ⟨m, b', hbW, hbK, hspK, hbL, hspL⟩ := (fw2 p).ks i
  choose bC hbC using fun k => hsurj (b' k) (hbW k)
  have hbC' : (fun k => cu (bC k)) = b' := funext hbC
  have hbs : Submodule.span (recB (h.laws v).p.toLawsCore).KO (Set.range bC) = ⊤ := by
    rw [eq_top_iff]
    intro F _
    have h1 : cu F ∈ Submodule.span p.T.Q.c.F (Set.range b') := by rw [hspK]; exact hcuW F
    obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h1
    have h2 : cu (∑ k, (show (recB (h.laws v).p.toLawsCore).KO from cf k) • bC k) = cu F := by
      rw [map_sum, ← hcf]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, hbC k]
      rfl
    rw [← hcuinj h2]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hbi : LinearIndependent D.what₂.LL (fun k => cu (bC k)) := by rw [hbC']; exact hbL
  have hbt : Submodule.span D.what₂.LL (Set.range fun k => cu (bC k)) = ⊤ := by rw [hbC']; exact hspL
  have hK : LinearIndependent (recB (h.laws v).p.toLawsCore).KO bC := by
    apply LinearIndependent.of_comp cu
    show LinearIndependent _ (fun k => cu (bC k))
    rw [hbC']; exact hbK
  have hR : LinearIndependent ℂ (fun k => Rd (bC k)) :=
    LinearIndependent.of_comp (M.cusp ka).subtype (GlobalTheory.T.cuspForm_family_linearIndependent h ha m bC hK)
  have hRs : Submodule.span ℂ (Set.range Rd) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨y, hy⟩ -
    have hy' : y ∈ (Submodule.span ℂ (Set.range Rd)).map (M.cusp ka).subtype := by
      rw [Submodule.map_span, ← Set.range_comp]
      unfold TwoLevels.cusp at hy
      refine Submodule.span_le.2 ?_ hy
      rintro _ ⟨G, hG, rfl⟩
      obtain ⟨m', α, Fs, hGe⟩ := GlobalTheory.T.modelCuspForms_span_usedRunReadings h ha hb hb0 hn G hG
      have hGs : M.res G = ∑ k, α k • rdLin h ha (Fs k) := by
        funext c x
        simp only [TwoLevels.res, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, rdLin_apply]
        exact hGe c x.1 x.2
      rw [hGs]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fs k, rfl⟩)
    obtain ⟨z, hz, hzy⟩ := hy'
    have hz' : z = ⟨y, hy⟩ := Subtype.ext hzy
    rw [← hz']; exact hz
  obtain ⟨f, ρ, hfcu, hint, hind, hspan⟩ := GlobalTheory.T.exists_semilinear_extension_of_form_with_transported_rep (r.used v).full.σ₀ σ hσ cu bC hbs hbi hbt Rd hR hRs ((R2 p).FW i).ρ
  have hρR : ∀ g F, ρ g (Rd F) = Rd (act g F) := by
    intro g F
    rw [← hfcu, ← hfcu, hint, hcu g F]
  obtain ⟨a, hpull⟩ := hc
  refine ⟨ρ, σ, f, ⟨a, fun g G hG c x => ?_⟩, hint, hind, hspan⟩
  obtain ⟨m', α, Fs, hGe⟩ := GlobalTheory.T.modelCuspForms_span_usedRunReadings h ha hb hb0 hn G hG
  have hy : (⟨M.res G, Submodule.subset_span ⟨G, hG, rfl⟩⟩ : M.cusp ka) = ∑ k, α k • Rd (Fs k) := by
    apply Subtype.ext
    funext c' x'
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, TwoLevels.res, hRd,
      rdLin_apply]
    exact hGe c' x'.1 x'.2
  rw [hy, map_sum]
  simp only [map_smul, hρR, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hRd,
    rdLin_apply]
  rw [TwoLevels.pull, hGe (g • c) _ (GlobalTheory.T.twoLevelFlagDomain_transporter_mem_domain M g c x.1 x.2), Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk := hpull (Fs k) g c x.1 x.2 (psi_eq ha c) (psi_eq ha (g • c))
  rw [rdLin_apply]
  unfold rdFun rdR
  rw [hact g⁻¹ (Fs k)]
  refine (congrArg (α k * ·) hk).trans ?_
  ring
end Main2

end GlobalTheory.ShareOn.Reading
