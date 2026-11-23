import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ArchSz
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridGivenPathTensorMemSubfield
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.ConjSize
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace UpperTheory.IteratedPhiSize

open GlobalTheory.StepData ValuativeRel Formalism.L2.Host GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim MeasureTheory

section Local

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {K : Type} [Field K] (ι τ : K →+* ℂ)

private theorem lam_principal_un {a : Type*} [Fintype a] [DecidableEq a] (g : (TypeDatum.principal k a).J) :
    Un ι τ (((TypeDatum.principal k a).lam g : ℂˣ) : ℂ) := by
  change Un ι τ ((1 : ℂˣ) : ℂ)
  rw [Units.val_one]
  exact Un.one

private theorem lam_reindex_un {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (P : TypeDatum k a)
    (e : a ≃ b) (hP : ∀ g, Un ι τ ((P.lam g : ℂˣ) : ℂ)) (g : (P.reindex e).J) :
    Un ι τ (((P.reindex e).lam g : ℂˣ) : ℂ) :=
  hP _

private theorem lam_step_un {a t : Type*} [Fintype a] [DecidableEq a] [Fintype t] [DecidableEq t] (P : TypeDatum k a)
    (μ : kˣ →* ℂˣ) (hμ : IsTame μ) (hP : ∀ g, Un ι τ ((P.lam g : ℂˣ) : ℂ)) (hμF : ∀ x, Un ι τ ((μ x : ℂˣ) : ℂ))
    (h : (P.step t μ hμ).J) : Un ι τ (((P.step t μ hμ).lam h : ℂˣ) : ℂ) := by
  rw [P.step_lam μ hμ h (P.corner h) (P.corner_val h), Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val]
  exact ((hP _).mul (hμF _).inv).mul (hμF _)

private theorem lam_iter_un {r t : Type*} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] (P : TypeDatum k r)
    (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (hP : ∀ g, Un ι τ ((P.lam g : ℂˣ) : ℂ))
    (hμF : ∀ j x, Un ι τ ((μ j x : ℂˣ) : ℂ)) (j : ℕ) : ∀ g, Un ι τ (((P.iter t μ hμ j).lam g : ℂˣ) : ℂ) := by
  induction j with
  | zero => exact lam_reindex_un ι τ P _ hP
  | succ j ih => exact lam_reindex_un ι τ _ _ (lam_step_un ι τ _ _ _ ih (hμF _))

private theorem Phi_sz {a t : Type*} [Fintype a] [DecidableEq a] (P : TypeDatum k a) (μ : kˣ →* ℂˣ)
    (hP : ∀ g, Un ι τ ((P.lam g : ℂˣ) : ℂ)) (hμF : ∀ x, Un ι τ ((μ x : ℂˣ) : ℂ)) (x : Matrix (a ⊕ t) a k) :
    Sz ι τ (P.Phi t μ x) 1 := by
  by_cases h : P.Phi t μ x = 0
  · rw [h]; exact Sz.zero zero_le_one
  · obtain ⟨⟨g, hg, e⟩, h2⟩ := (P.Phi_ne_zero_iff μ).1 h
    rw [P.Phi_of_mem μ ⟨g, hg⟩ e h2, Units.val_inv_eq_inv_val]
    exact ((hP _).mul (hμF _).inv).sz

private theorem iterPhi_sz {r t : Type*} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] (P : TypeDatum k r)
    (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (hP : ∀ g, Un ι τ ((P.lam g : ℂˣ) : ℂ))
    (hμF : ∀ j x, Un ι τ ((μ j x : ℂˣ) : ℂ)) (j : ℕ) (x : Matrix (Ix r t (j + 1)) (Ix r t j) k) :
    Sz ι τ (P.iterPhi t μ hμ j x) 1 :=
  Phi_sz ι τ _ _ (lam_iter_un ι τ P μ hμ hP hμF j) (hμF _) _

private theorem parPhi_sz {r s s' : Type*} [Fintype r] [DecidableEq r] (δ : kˣ →* ℂˣ)
    (hδ : ∀ x, Un ι τ ((δ x : ℂˣ) : ℂ)) (x : Matrix (r ⊕ s) (r ⊕ s') k) : Sz ι τ (parPhi δ x) 1 := by
  by_cases h : parPhi δ x = 0
  · rw [h]; exact Sz.zero zero_le_one
  · obtain ⟨⟨g, hg, e⟩, h21, h12, h22⟩ := (parPhi_ne_zero_iff δ).1 h
    rw [parPhi_of_mem δ hg e h21 h12 h22, Units.val_inv_eq_inv_val]
    exact (hδ _).inv.sz

private theorem indicator_one_sz {X : Type*} (S : Set X) (x : X) : Sz ι τ (S.indicator (1 : X → ℂ) x) 1 := by
  classical
  rw [Set.indicator_apply]
  split_ifs
  · exact Sz.one
  · exact Sz.zero zero_le_one

end Local

section Global

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {K : Type} [Field K] (ι τ : K →+* ℂ)
  (w : Pl D.host.E)

private theorem muBase_un (hmu : ∀ j x, Un ι τ ((L.C.mu0 j).loc w x : ℂ)) (c : ℕ) (x : (Kw w)ˣ) :
    Un ι τ (((muBase L c).loc w x : ℂˣ) : ℂ) := by
  rcases c with _ | c
  · simpa [muBase] using (Un.one : Un ι τ 1)
  · simp only [muBase]
    split_ifs with h
    · exact hmu _ _
    · simpa using (Un.one : Un ι τ 1)

variable {t : T} (hmu : ∀ j x, Un ι τ ((L.C.mu0 j).loc w x : ℂ)) (hxi : ∀ x, Un ι τ ((L.xiH t).loc w x : ℂ))
include hmu hxi

private theorem stepFn_sz (j : ℕ) (x) : Sz ι τ (stepFn L t w j x) 1 := by
  unfold stepFn
  split_ifs
  · refine iterPhi_sz ι τ _ _ _ (lam_principal_un ι τ) (fun c y => ?_) _ _
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
    exact (muBase_un ι τ w hmu c y).inv
  · refine parPhi_sz ι τ _ (fun y => ?_) _
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
    exact (hxi y).inv
  · exact indicator_one_sz ι τ _ _

private theorem givenDatum_sz (B : Frames G) (Φ : G.Datum) (b : Edge) (x) : Sz ι τ (givenDatum t w B Φ b x) 1 := by
  rcases b with ⟨i, j⟩ | ⟨i, j⟩
  · rcases i with _ | i
    · simp only [givenDatum]
      exact stepFn_sz ι τ w hmu hxi _ _
    · simp only [givenDatum]
      exact Sz.zero zero_le_one
  · rcases j with _ | j
    · simp only [givenDatum]
      split_ifs
      · exact indicator_one_sz ι τ _ _
      · exact Sz.zero zero_le_one
    · simp only [givenDatum]
      exact Sz.zero zero_le_one

end Global

end UpperTheory.IteratedPhiSize

theorem UpperTheory.localGrid_tensor_size_le_one_of_unimodular :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {K : Type} [Field K] (ι τ : K →+* ℂ) (B : Frames G) (t : T) (Φ : G.Datum) (w : Pl D.host.E), (∀ j x, Un ι τ ((L.C.mu0 j).loc w x : ℂ)) → (∀ x, Un ι τ ((L.xiH t).loc w x : ℂ)) → ∀ z : (locGrid G t w).Args, Sz ι τ ((givenStage t w B Φ).tensor z) 1 := by
  intro D T L sc G K _ ι τ B t Φ w hmu hxi z
  show Sz ι τ ((GlobalTheory.SplitFlip.givenPath D.R.m).map fun b => givenDatum t w B Φ b (z b)).prod 1
  refine Sz.list_prod fun y hy => ?_
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hy
  exact UpperTheory.IteratedPhiSize.givenDatum_sz ι τ w hmu hxi B Φ b _
