import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

noncomputable section

namespace GlobalTheory.MuCharProof

theorem charpoly_fin_one {k : Type} [CommRing k] (M : Matrix (Fin 1) (Fin 1) k) :
    M.charpoly = X - C (M 0 0) := by
  rw [Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply_eq]

theorem mem_list_sum {α β : Type} (L : List α) (f : α → Multiset β) {a : α} (ha : a ∈ L) {b : β}
    (hb : b ∈ f a) : b ∈ (L.map f).sum :=
  Multiset.mem_of_le (List.le_sum_of_mem (List.mem_map_of_mem ha)) hb

theorem muChar_holds : MuChar := by
  intro D hA i hg ρ hρ w hw
  obtain ⟨x, ⟨P, -, Pa, hBC, hmem⟩, -⟩ := hg
  have h2 : Formalism.MainNotions.SumRepresentations.adm2 D := hA.1.1.2.2.2.1
  have h5 : Formalism.MainNotions.SumRepresentations.adm5 D := hA.1.1.2.2.2.2.2.2
  set χ := D.naut.tw (D.naut.muC i) D.naut.etaTinv with hχ
  set s : ℝ := ((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2 with hs

  have halg : ∀ τ : D.host.E →+* ℂ, ∀ z ∈ D.naut.infG χ τ, ∃ k : ℤ, z + (s : ℂ) = (k : ℂ) := by
    intro τ z hz
    have ht : 0 ∈ List.range D.R.t := List.mem_range.2 D.R.t_odd.pos
    have h1 : z + (((D.R.t : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ)) ∈ isoInf D.nd D.naut Pa τ := by
      refine mem_list_sum Pa _ hmem ?_
      refine mem_list_sum _ _ (a := ((0 : ℕ) : ℂ)) ?_ ?_
      · simp only [List.mem_range]
        simp
        exact ⟨0, D.R.t_odd.pos, by simp⟩
      · exact Multiset.mem_map_of_mem _ hz
    rw [hBC.2.2.2.2.2 τ] at h1
    let τ' : D.host.E →+* Qbar (D.nd.l i) := (D.naut.iotaQC i).symm.toRingHom.comp τ
    have hτ : (D.naut.iotaQC i).toRingHom.comp τ' = τ := by
      ext e
      simp [τ']
    have hj := D.naut.locAut_hodgeTateWeightsLevelZero_def i τ'
    rw [hτ] at hj
    have h3 : -(z + (((D.R.t : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ))) + ((D.R.nV : ℂ) - 1) / 2 ∈
        (D.naut.locAutHodgeTateWeightsLevelZero i τ').map (fun n : ℤ => (n : ℂ)) := by
      rw [hj]
      exact Multiset.mem_map_of_mem _ h1
    obtain ⟨n, -, hn⟩ := Multiset.mem_map.1 h3
    refine ⟨-n, ?_⟩
    rw [hs]
    push_cast at hn ⊢
    linear_combination hn
  obtain ⟨ρ', hc', hw', -⟩ := (h2 i).2.2 χ s halg

  have hc0 : Continuous fun g => ((ρ g : GL _ _) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0 := by
    have : (fun g => ((ρ g : GL _ _) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0) =
        fun g => iotaOQ D.nd D.naut i (chi1 D.nd i g) := funext hρ
    rw [this]
    exact (Formalism.MainNotions.SumRepresentations.continuous_iotaOQ D.nd D.naut i).comp (D.nd.chi_cont i 1)
  have hc0' : Continuous fun g => ((ρ' g : GL _ _) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0 :=
    hc'.matrix_elem 0 0

  have hfin : (placesOver D.host.E (D.nd.l i) ∪ ↑(D.nd.S i) ∪ ↑(D.nd.Q i) : Set (PlE D.host)).Finite :=
    ((Formalism.MainNotions.SumRepresentations.placesOver_finite D.host.E (D.nd.l i) (D.nd.lPrime i).out.ne_zero).union
      (D.nd.S i).finite_toSet).union (D.nd.Q i).finite_toSet
  have hdense := h5.2.2.1 _ hfin
  have hsub : {σ : G D.host.E D.nd.Om | ∃ w ∉ (placesOver D.host.E (D.nd.l i) ∪ ↑(D.nd.S i) ∪ ↑(D.nd.Q i) :
      Set (PlE D.host)), IsSplitPl D.host w ∧ ∃ B : ValuationSubring D.nd.Om,
      IsPlaceOver (F := D.host.E) B w ∧ IsFrob (F := D.host.E) B (normV w) σ} ⊆
      {g | ((ρ g : GL _ _) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0 =
        ((ρ' g : GL _ _) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0} := by
    rintro σ ⟨v, hv, hsp, B, hB, hσ⟩
    simp only [Set.mem_union, not_or, Finset.mem_coe] at hv
    have hso : SplitOut D.nd i v := ⟨hsp, hv.1.1, hv.1.2, hv.2⟩
    obtain ⟨hu, hf⟩ := D.naut.chi_mu i v hso
    have hunr : D.naut.unr (D.naut.wdOf i ρ' v) := by
      rw [hw' v hv.1.1]
      exact (D.naut.unr_tw _ _).2 hu
    have e := D.naut.wdOf_frob i ρ' v hv.1.1 hc' hunr B σ hB hσ
    rw [hw' v hv.1.1, hf B σ hB hσ, Multiset.map_singleton, Multiset.prod_singleton, charpoly_fin_one,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] at e
    have e2 := (D.naut.iotaQC i).injective (C_injective (sub_right_injective e))
    show _ = _
    rw [hρ σ]
    exact e2.symm
  have hall : ∀ g, ((ρ g : GL _ _) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0 =
      ((ρ' g : GL _ _) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0 := by
    intro g
    have hcl : IsClosed {g | ((ρ g : GL _ _) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0 =
        ((ρ' g : GL _ _) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0} := isClosed_eq hc0 hc0'
    have := closure_minimal hsub hcl
    rw [hdense] at this
    exact this (Set.mem_univ g)
  have heq : ρ = ρ' := by
    refine MonoidHom.ext fun g => Units.ext (Matrix.ext fun a b => ?_)
    rw [Subsingleton.elim a 0, Subsingleton.elim b 0]
    exact hall g
  rw [heq]
  exact hw' w hw

end GlobalTheory.MuCharProof
