import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.LocalTraceForms.ExistsClopenSep
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.LocalTraceForms.ContinuousCp

noncomputable section

open Matrix Polynomial GroundTheory.Automorphic.Whittaker Set

namespace PositivityTheory.RgUd.TP.Loc.Psplit

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem fib_split (hSp : PositivityTheory.RgUd.TP.Loc.Split k) {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (χ : k[X]) {m : ℕ}
    (F : Fin m → Set (Matrix (Fin n) (Fin n) k)) (hF : IsPieces Z χ F) (ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ)
    (hS : Supp ξ ((Bz Z ∩ {x | x.charpoly = χ}) ×ˢ univ)) (hI : Inv Z ξ) :
    ∃ η : Fin m → (Sp k n → ℂ) →ₗ[ℂ] ℂ, (∀ i, Supp (η i) (F i ×ˢ univ) ∧ Inv Z (η i)) ∧
      ∀ f ∈ supportedIn (univ : Set (Sp k n)), ξ f = ∑ i, η i f := by
  refine hSp n Z F (fun i => ⟨(hF.1 i).1, (hF.1 i).2.2⟩) hF.2.1 ξ ?_ hI
  intro f hf h0
  refine hS f hf fun p hp => ?_
  obtain ⟨i, hi⟩ := hF.2.2 p.1 hp.1.1 hp.1.2
  exact h0 p ⟨mem_iUnion.2 ⟨i, hi⟩, mem_univ _⟩

theorem locAll_of_pf : PositivityTheory.RgUd.TP.Loc.Split k → PositivityTheory.RgUd.TP.Loc.LocChi k → LocAll k := by
  intro hSp hLC n Z _hZ hP ξ hS hI
  have hU : IsOpen {p : Sp k n | p.2 ≠ 0} := (isClosed_eq continuous_snd continuous_const).isOpen_compl
  refine hLC n Z _ hU (fun χ ξ' hS' hI' f hf => ?_) ξ hS hI
  obtain ⟨m, F, hF, hi⟩ := hP χ
  obtain ⟨η, hη, hsum⟩ := fib_split hSp Z χ F hF ξ' hS' hI'
  rw [hsum f (supportedIn_mono (subset_univ _) hf)]
  exact Finset.sum_eq_zero fun i _ => hi i (η i) (hη i).1 (hη i).2 f hf

theorem locOff_of_pf : PositivityTheory.RgUd.TP.Loc.Split k → PositivityTheory.RgUd.TP.Loc.LocChi k → LocOff k := by
  intro hSp hLC n Z _hZ hP ξ hS hI U hU hUp
  refine hLC n Z U hU (fun χ ξ' hS' hI' f hf => ?_) ξ hS hI
  obtain ⟨m, F, hF, hi⟩ := hP χ
  obtain ⟨η, hη, hsum⟩ := fib_split hSp Z χ F hF ξ' hS' hI'
  rw [hsum f (supportedIn_mono (subset_univ _) hf)]
  refine Finset.sum_eq_zero fun i _ => ?_
  rcases hi i with ⟨c, hc, hnil⟩ | hv
  · refine (hη i).1 f (supportedIn_mono (subset_univ _) hf) fun p hp => ?_
    by_contra h0
    exact ((hUp p (hf.2 h0)).2) ⟨⟨c, hc, hnil p.1 hp.1⟩, (hF.1 i).2.1 hp.1⟩
  · exact hv (η i) (hη i).1 (hη i).2 f (supportedIn_mono (fun p hp => (hUp p hp).1) hf)

theorem split (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    PositivityTheory.RgUd.TP.Loc.Split k := split_pf
theorem locChi (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    PositivityTheory.RgUd.TP.Loc.LocChi k := locChi_pf
theorem locOff_of (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    PositivityTheory.RgUd.TP.Loc.Split k → PositivityTheory.RgUd.TP.Loc.LocChi k → LocOff k := locOff_of_pf
theorem locAll_of (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    PositivityTheory.RgUd.TP.Loc.Split k → PositivityTheory.RgUd.TP.Loc.LocChi k → LocAll k := locAll_of_pf

end PositivityTheory.RgUd.TP.Loc.Psplit
