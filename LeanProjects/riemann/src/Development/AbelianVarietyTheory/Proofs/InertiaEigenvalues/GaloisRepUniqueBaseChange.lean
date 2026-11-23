import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceNondegenerateOfIsSSRep
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.BaseChangeConj

open Formalism.MainNotions.SumRepresentations Polynomial

theorem charpoly_eq_of_dense' {Γ : Type} [Group Γ] [TopologicalSpace Γ] {k : Type} [Field k]
    [TopologicalSpace k] [IsTopologicalRing k] [T2Space k] [Infinite k] {a : ℕ} (ρ₁ ρ₂ : Γ →* GL (Fin a) k)
    (h1 : Continuous fun g => ((ρ₁ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k))
    (h2 : Continuous fun g => ((ρ₂ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k))
    (S : Set Γ) (hS : closure S = Set.univ)
    (hE : ∀ g ∈ S, ((ρ₁ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly =
      ((ρ₂ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly) (g : Γ) :
    ((ρ₁ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly =
      ((ρ₂ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly := by
  apply Polynomial.funext
  intro t
  rw [Matrix.eval_charpoly, Matrix.eval_charpoly]
  have hc : IsClosed {g : Γ | (Matrix.scalar (Fin a) t - ((ρ₁ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)).det =
      (Matrix.scalar (Fin a) t - ((ρ₂ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)).det} :=
    isClosed_eq (continuous_const.sub h1).matrix_det (continuous_const.sub h2).matrix_det
  have hsub : closure S ⊆ _ := hc.closure_subset_iff.mpr fun g hg => by
    show _ = _
    rw [← Matrix.eval_charpoly, ← Matrix.eval_charpoly, hE g hg]
  rw [hS] at hsub
  exact hsub (Set.mem_univ g)

theorem rep_conj_of_baseChange : ∀ D : D7, SumRepresentations.adm5 D → ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r → ∀ (x : D.nd.X i) (P : D.naut.AV i) (Pa : List (Formalism.BasicNotions.Part D.naut.CG)), D.naut.ptV i P = some x → IsBCV D.nd D.naut i P Pa → ∀ ρ : GE D.nd →* GL (Fin D.R.nV) (Qbar (D.nd.l i)), SumRepresentations.At.ContQ D.nd i ρ → IsSSRep ρ → (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2)) → ∃ Pm : GL (Fin D.R.nV) (Qbar (D.nd.l i)), ∀ g, mapRep (iotaOQ D.nd D.naut i) (r x) g = Pm⁻¹ * ρ g * Pm := by
  intro D hAN i r hr x P Pa hP hB ρ hρc hρs hwd
  obtain ⟨-, -, hCheb, hBN⟩ := hAN
  have hl : (D.nd.l i).Prime := Fact.out
  have hfin : (((placesOver D.host.E (D.nd.l i)) ∪ (D.nd.S i : Set _)) ∪ (D.nd.Q i : Set _)).Finite :=
    ((placesOver_finite D.host.E (D.nd.l i) hl.ne_zero).union (D.nd.S i).finite_toSet).union
      (D.nd.Q i).finite_toSet
  have hdense := hCheb _ hfin

  have hfrob : ∀ g ∈ {σ : G D.host.E D.nd.Om | ∃ w ∉ (((placesOver D.host.E (D.nd.l i)) ∪ (D.nd.S i : Set _)) ∪
      (D.nd.Q i : Set _)), IsSplitPl D.host w ∧ ∃ B : ValuationSubring D.nd.Om,
      IsPlaceOver (F := D.host.E) B w ∧ IsFrob (F := D.host.E) B (normV w) σ},
      ((ρ g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))).charpoly =
      ((mapRep (iotaOQ D.nd D.naut i) (r x) g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))).charpoly := by
    rintro σ ⟨w, hw, hsp, B, hB', hσ⟩
    simp only [Set.mem_union, not_or] at hw
    obtain ⟨⟨hwl, hwS⟩, hwQ⟩ := hw
    replace hwS : w ∉ D.nd.S i := by simpa using hwS
    replace hwQ : w ∉ D.nd.Q i := by simpa using hwQ
    have hso : SplitOut D.nd i w := ⟨hsp, hwl, hwS, hwQ⟩
    have hS := hwS
    rw [D.nd.S_def] at hS
    have hS' := fun h => hS ⟨h, hwl⟩
    have hu : D.naut.unr (D.naut.locV i P w) := D.naut.locV_unr i P w hsp hwQ
      (Fin.forall_fin_two.2 ⟨fun h => hS' (Or.inl h), fun h => hS' (Or.inr (Or.inl h))⟩)
      fun h => hS' (Or.inr (Or.inr h))
    have hloc := hB.2.2.2.1 w hsp
    have hwd' := hwd w hwl
    rw [hloc] at hwd'
    have hun : D.naut.unr (D.naut.wdOf i ρ w) := by rw [hwd']; exact (D.naut.unr_tw _ _).2 hu
    have e1 := D.naut.wdOf_frob i ρ w hwl hρc hun B σ hB' hσ
    rw [hwd', ← D.naut.pt_loc i P x hP w hso] at e1
    have e2 := (hr x).2.2 w hso B σ hB' hσ
    apply Polynomial.map_injective (D.naut.iotaQC i).toRingHom (D.naut.iotaQC i).injective
    have e3 : ((mapRep (iotaOQ D.nd D.naut i) (r x) σ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))) =
        ((r x σ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).map (iotaOQ D.nd D.naut i) := rfl
    rw [e1, e3, Matrix.charpoly_map, e2, Polynomial.map_map]
    rfl
  have hc2 : SumRepresentations.At.ContQ D.nd i (mapRep (iotaOQ D.nd D.naut i) (r x)) :=
    contQ_of_continuous D.nd D.naut i (r x) (hr x).1
  have hall := charpoly_eq_of_dense' ρ (mapRep (iotaOQ D.nd D.naut i) (r x)) hρc hc2 _ hdense hfrob
  have : CharZero (Kf D.nd i) := RingHom.charZero (D.naut.iotaQ i)
  have hss : IsSSRep (mapRep (iotaOQ D.nd D.naut i) (r x)) := by
    have h := GlobalTheory.TraceSemisimple.isSSRep_mapRep _ _ _ (D.naut.iotaQ i) _ _ (hr x).2.1
    have e : mapRep (iotaOQ D.nd D.naut i) (r x) =
        mapRep (D.naut.iotaQ i) (mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) (r x)) := by
      ext g a b
      rfl
    rw [e]
    exact h
  exact hBN _ _ ρ _ hρs hss hall

end GlobalTheory.BaseChangeConj
