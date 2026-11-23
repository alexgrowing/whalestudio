import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLocalGroupLeBaseLatticeLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLocalGroupContainsPrincipalCongruence
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLocalGroupFiniteIndexAtFurtherPlaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharacterAllChartsFurtherPlacesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

set_option maxHeartbeats 4000000 in

theorem further_group_charts : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, GlobalTheory.Mem.Col2.AdT.ChiFin I l Z (K β).lev) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∃ (W : ∀ v, v ∈ Q → Subgroup (GL (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F))) (ψ : (∀ v : Q, ↥(W v.1 v.2)) →* ℂˣ), (∀ v hv, W v hv ≤ levelVL (I.rec7 l Z).sp.cm.sig ((I.rec7 l Z).sp.X (B.R.m - 1)).gram v Lb0) ∧ (∀ v hv, ∃ n : ℕ, 0 < n ∧ ∀ x, Formalism.L2.Herm.InPrinc (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X (B.R.m - 1)) v n Lb0 x → x ∈ W v hv) ∧ (∀ β v hv, (K β).lev.Uloc v ≤ (W v hv).map (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom) ∧ (∀ β v hv, ((((K β).lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom).subgroupOf (W v hv)).FiniteIndex) ∧ (∀ β (κ : (K β).lev.U) (z : ∀ v : Q, ↥(W v.1 v.2)), (∀ v : Q, reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (z v).1 = bc (prV (E := (I.rec7 l Z).host.E) v.1) κ.1) → (∀ v, v ∉ Q → bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ψ z) := by
  intro B X I hI hP l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hR hfin hoff hchi Lb0 hLb
  classical
  rcases isEmpty_or_nonempty Ch with hE | hNE
  · refine ⟨fun v _ => levelVL (I.rec7 l Z).sp.cm.sig ((I.rec7 l Z).sp.X (B.R.m - 1)).gram v Lb0, 1, fun v hv => le_rfl,
      fun v hv => ⟨1, one_pos, fun x hx => hx.1⟩, fun β => hE.elim β, fun β => hE.elim β, fun β => hE.elim β⟩
  · obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_character_allCharts_furtherPlaces I hI hP l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hR hfin hoff hchi Lb0 hLb
    refine ⟨fun v _ => (⨆ β', ((K β').lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom), ψ, fun v hv => iSup_le fun β => GlobalTheory.Mem.Col2.TC.chart_Uloc_le_levelVL_base I hI hP l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hR hoff hchi Lb0 hLb β v hv, fun v hv => ?_, fun β v hv => ?_, fun β v hv => GlobalTheory.T.chartLocalGroup_finiteIndex_at_furtherPlace I hI hP l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hR hoff hchi Lb0 hLb β v hv, hψ⟩
    · obtain ⟨β⟩ := hNE
      obtain ⟨n, hn, hx⟩ := GlobalTheory.Mem.Col2.AdT.LevQ.chart_contains_princ I hI hP l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hR hoff hchi Lb0 hLb β v hv
      exact ⟨n, hn, fun x h => le_iSup (fun β' => ((K β').lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom) β (hx x h)⟩
    · intro x hx
      refine ⟨(reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).symm x, le_iSup (fun β' => ((K β').lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom) β ?_, ?_⟩
      · rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]; exact hx
      · rw [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]

end GlobalTheory.Mem.Col2.TC

end
