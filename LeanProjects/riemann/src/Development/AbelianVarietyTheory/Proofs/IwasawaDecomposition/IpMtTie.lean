import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CevInjective
import Formalism.LocalToGlobal.HermitianForms.TiedTwJSym

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.IpMt

theorem ipMt_tie : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (jM : (I.per l u a).Mt →ₛₗ[starRingEnd ℂ] (I.per l u a).Wrow), (∀ F, jM F ∈ (I.fm l u a).ptC) → (∀ w F, (I.per l u a).period w F = (I.fm l u a).ipP (jM F) w) → (∀ F G, I.ipMt l u a F G = (I.fm l u a).ipP (jM G) (jM F)) ∧ ∀ F, F ≠ 0 → 0 < (I.ipMt l u a F F).re := by
  intro B X I hOk hP l Z u a jM hmem hper
  obtain ⟨j0, hinj, -, hmem0, hper0, hpos⟩ := PerConj.period_conj I hOk hP l Z u a
  have uniq : ∀ z ∈ (I.fm l u a).ptC, ∀ z' ∈ (I.fm l u a).ptC,
      (∀ w, (I.fm l u a).ipP z w = (I.fm l u a).ipP z' w) → z = z' := by
    intro z hz z' hz' h
    by_contra hne
    have h1 := hpos _ (sub_mem hz hz') (sub_ne_zero.2 hne)
    rw [map_sub (I.fm l u a).ipP, LinearMap.sub_apply, h, sub_self] at h1
    simp at h1
  have hj : ∀ G, I.jStd l u a G = jM G := by
    intro G
    have hex : ∃ z, z ∈ (I.fm l u a).ptC ∧ ∀ w, (I.per l u a).period w G = (I.fm l u a).ipP z w :=
      ⟨jM G, hmem G, fun w => hper w G⟩
    have hs := Classical.epsilon_spec hex
    exact uniq _ hs.1 _ (hmem G) fun w => (hs.2 w).symm.trans (hper w G)
  have hform : ∀ F G, I.ipMt l u a F G = (I.fm l u a).ipP (jM G) (jM F) := by
    intro F G
    rw [TC.ipMt, hj, hj]
  refine ⟨hform, fun F hF => ?_⟩
  have h0 : jM F = j0 F := uniq _ (hmem F) _ (hmem0 F) fun w => (hper w F).symm.trans (hper0 w F)
  have hne : jM F ≠ 0 := by
    rw [h0]
    exact fun h => hF (hinj (h.trans (map_zero j0).symm))
  rw [hform]
  exact hpos _ (hmem F) hne

theorem ipMt_sum {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (hP : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (a : I.ι) (F G : (I.perIn u a).Mt B.fields.emb B.embLL) :
    I.ipMt l u a F G = letI := (I.perIn u a).clFin (l.per u a);
      ∑ c, (I.perIn u a).wt c * pairB (I.perIn u a).sgT
        (MvPolynomial.map (starRingEnd ℂ) (F.1 c.1 ((I.perIn u a).S'.rep c))) (G.1 c.1 ((I.perIn u a).S'.rep c)) := by
  have hE : ∀ τ x, embAt B.embLL B.fields.emb τ (letI := B.fields.starE; star x) =
      starRingEnd ℂ (embAt B.embLL B.fields.emb τ x) := fun τ x => (GlobalTheory.Mem.FieldsLaws.fields_ok B).conjE _ x
  have hH : ∀ b, (I.perIn u a).H b = ⊤ := fun _ => rfl
  have h := (ipMt_tie I hOk hP l Z u a (PerConj.jM (I.perIn u a) B.fields.emb B.embLL)
    (PerConj.jM_mem _ _ hE (l.per u a) hH)
    (PerConj.period_eq _ _ (l.ch u a) (l.per u a) (B.hcW u))).1 F G
  refine h.trans ?_
  refine (PerConj.petersson_apply B.fields.emb B.embLL (l.per u a) _ _).trans ?_
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  exact (PerConj.ipVal_cev _ _ _ _ _).trans (congrArg (fun p => pairB _ p _) (PerConj.polOf_cev _ _ _ _))

end GlobalTheory.Mem.Col2.IpMt

end
