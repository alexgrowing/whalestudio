import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlocksUnique
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocAutHodgeTateWeightsLevelZeroDef
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting

theorem eventually_map_residue_eq {Γ O : Type} [TopologicalSpace Γ] [CommRing O] [IsLocalRing O]
    [TopologicalSpace O] [IsTopologicalRing O]
    (hO : IsOpen ((IsLocalRing.maximalIdeal O : Ideal O) : Set O)) {r : ℕ}
    (M : Γ → Matrix (Fin r) (Fin r) O) (hM : Continuous M) (g0 : Γ) :
    ∀ᶠ g in nhds g0, (M g).map (IsLocalRing.residue O) = (M g0).map (IsLocalRing.residue O) := by
  have h : ∀ a b, ∀ᶠ g in nhds g0, M g a b - M g0 a b ∈ IsLocalRing.maximalIdeal O := by
    intro a b
    have hc : Continuous fun g => M g a b - M g0 a b := (hM.matrix_elem a b).sub continuous_const
    exact hc.continuousAt.preimage_mem_nhds (hO.mem_nhds (by simp))
  have h2 : ∀ᶠ g in nhds g0, ∀ a b, M g a b - M g0 a b ∈ IsLocalRing.maximalIdeal O := by
    rw [Filter.eventually_all]; intro a; rw [Filter.eventually_all]; exact h a
  filter_upwards [h2] with g hg
  ext a b
  simp only [Matrix.map_apply]
  exact (Ideal.Quotient.eq).2 (hg a b)

theorem sub_mem_nonunits_vs {K : Type} [Field K] (A : ValuationSubring K) {x y : K}
    (hx : x ∈ A.nonunits) (hy : y ∈ A.nonunits) : x - y ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at *
  exact lt_of_le_of_lt (A.valuation.map_sub x y) (max_lt hx hy)

theorem charpoly_coeff_congr_same_place : ∀ (D : D7) (Rw : RowSide D) (Pl : PlSide D) (X : LocNd (lay0 D)) (Y : LocAut X), GlobalTheory.RowTie.ChebSplit D.nd → (∀ i σ w, Y.locW i σ w = Rw.locR σ w) → (∀ (i : X.nd.Loc) (y : X.nd.O i), ∃ h : iotaO X.nd Y.naut i y ∈ Pl.plB (X.nd.w i), fbCast (X.nd.w_l i) (D.what₂.places.resChar_prime (X.nd.w i)) (X.nd.lPrime i).out (Pl.plκ (X.nd.w i) (IsLocalRing.residue (Pl.plB (X.nd.w i)) ⟨_, h⟩)) = Y.naut.kFbar i (IsLocalRing.residue (X.nd.O i) y)) → ∀ (σ : D.what₂.FT) (i i' : X.nd.Loc), X.nd.w i = X.nd.w i' → ∀ (Sig Sig' : List (Formalism.BasicNotions.Part Y.naut.CG)) (ρ : G D.host.E X.nd.Om →* GL (Fin D.R.r) (X.nd.O i)) (ρ' : G D.host.E X.nd.Om →* GL (Fin D.R.r) (X.nd.O i')), HasParamW X.nd Y.naut i σ Sig → IsRepOfSig X.nd Y.naut i Sig ρ → HasParamW X.nd Y.naut i' σ Sig' → IsRepOfSig X.nd Y.naut i' Sig' ρ' → ∀ (g : G D.host.E X.nd.Om) (n : ℕ), iotaO X.nd Y.naut i ((ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i)).charpoly.coeff n) - iotaO X.nd Y.naut i' ((ρ' g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i')).charpoly.coeff n) ∈ (Pl.plB (X.nd.w i)).nonunits := by
  classical
  intro D Rw Pl X Y hCheb hRw hPl σ i i' hw Sig Sig' ρ ρ' hP hR hP' hR' g n
  have key : ∀ (j : X.nd.Loc) (y y' : X.nd.O j), IsLocalRing.residue (X.nd.O j) y = IsLocalRing.residue (X.nd.O j) y' →
      iotaO X.nd Y.naut j y - iotaO X.nd Y.naut j y' ∈ (Pl.plB (X.nd.w j)).nonunits := by
    intro j y y' hyy
    obtain ⟨h1, e1⟩ := hPl j y
    obtain ⟨h2, e2⟩ := hPl j y'
    have hres : IsLocalRing.residue (Pl.plB (X.nd.w j)) ⟨_, h1⟩ = IsLocalRing.residue (Pl.plB (X.nd.w j)) ⟨_, h2⟩ := by
      apply (Pl.plκ (X.nd.w j)).injective
      apply (fbCast (X.nd.w_l j) (D.what₂.places.resChar_prime (X.nd.w j)) (X.nd.lPrime j).out).injective
      rw [e1, e2, hyy]
    have hm := (Ideal.Quotient.eq).1 hres
    have hv := (ValuationSubring.valuation_lt_one_iff _ _).1 hm
    rw [ValuationSubring.mem_nonunits_iff]
    simpa using hv
  have key' := key i'
  rw [← hw] at key'
  have hO : ∀ j, IsOpen ((IsLocalRing.maximalIdeal (X.nd.O j) : Ideal (X.nd.O j)) : Set (X.nd.O j)) := fun j => by
    simpa using (isAdic_iff.1 (X.nd.O_adic j)).1 1
  have hclosed : IsClosed {g : G D.host.E X.nd.Om |
      iotaO X.nd Y.naut i ((ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i)).charpoly.coeff n) -
        iotaO X.nd Y.naut i' ((ρ' g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i')).charpoly.coeff n) ∈
        (Pl.plB (X.nd.w i)).nonunits} := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro g0 hg0
    have e1 := eventually_map_residue_eq (hO i) (fun g => (ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i))) hR.1 g0
    have e2 := eventually_map_residue_eq (hO i') (fun g => (ρ' g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i'))) hR'.1 g0
    filter_upwards [e1, e2] with g h1 h2
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hg0 ⊢
    intro hg
    apply hg0
    have c1 : IsLocalRing.residue (X.nd.O i) ((ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i)).charpoly.coeff n) =
        IsLocalRing.residue (X.nd.O i) ((ρ g0 : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i)).charpoly.coeff n) := by
      rw [← Polynomial.coeff_map, ← Polynomial.coeff_map, ← Matrix.charpoly_map, ← Matrix.charpoly_map, h1]
    have c2 : IsLocalRing.residue (X.nd.O i') ((ρ' g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i')).charpoly.coeff n) =
        IsLocalRing.residue (X.nd.O i') ((ρ' g0 : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i')).charpoly.coeff n) := by
      rw [← Polynomial.coeff_map, ← Polynomial.coeff_map, ← Matrix.charpoly_map, ← Matrix.charpoly_map, h2]
    have := sub_mem_nonunits_vs _ hg (sub_mem_nonunits_vs _ (key i _ _ c1) (key' _ _ c2))
    convert this using 1
    ring
  have hfin := Filter.eventually_cofinite.1 hR.2.2
  have hfin' := Filter.eventually_cofinite.1 hR'.2.2
  have hdense := hCheb (hfin.toFinset ∪ hfin'.toFinset)
  have hE := hdense.mono (s₂ := {g : G D.host.E X.nd.Om |
      iotaO X.nd Y.naut i ((ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i)).charpoly.coeff n) -
        iotaO X.nd Y.naut i' ((ρ' g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i')).charpoly.coeff n) ∈
        (Pl.plB (X.nd.w i)).nonunits}) (fun s hs => by
    obtain ⟨w, hwS, hsplit, B, hB, hF⟩ := hs
    simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_or, not_not] at hwS
    obtain ⟨q1, q2⟩ := hwS
    have r1 := q1 B s hB hF
    have r2 := q2 B s hB hF
    have eqloc : isoLoc X.nd Y.naut Sig w = isoLoc X.nd Y.naut Sig' w :=
      (hP.2.2 w hsplit).trans ((hRw i σ w).trans ((hRw i' σ w).symm.trans (hP'.2.2 w hsplit).symm))
    rw [Set.mem_setOf_eq, ← Polynomial.coeff_map, ← Polynomial.coeff_map, r1, r2, eqloc, sub_self, ValuationSubring.mem_nonunits_iff,
      map_zero]
    exact zero_lt_one)
  have hc := hE.closure_eq
  rw [hclosed.closure_eq] at hc
  exact Set.eq_univ_iff_forall.1 hc g

end GlobalTheory.HeightCounting
