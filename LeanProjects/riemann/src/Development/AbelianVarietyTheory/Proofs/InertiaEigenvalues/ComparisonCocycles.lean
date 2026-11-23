import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

noncomputable section

namespace GlobalTheory.NewPrime

section
variable {A : Type} [CommRing A] {a r : ℕ}

theorem rect_map {B B' : Type} [AddCommGroup B] [Module A B] [AddCommGroup B'] [Module A B'] (p : B →ₗ[A] B')
    (Z : Matrix (Fin r) (Fin a) A) (x : Fin a → B) : p.compLeft (Fin r) (rect Z x) = rect Z (p ∘ x) := by
  funext c
  simp [rect, map_sum]

theorem matAct_map {B B' : Type} [AddCommGroup B] [Module A B] [AddCommGroup B'] [Module A B'] (p : B →ₗ[A] B')
    (Φ : Matrix (Fin a) (Fin a) A) (x : Fin a → B) : p ∘ matAct Φ x = matAct Φ (p ∘ x) := by
  funext c
  simp [matAct, map_sum]

end

theorem comparison_cocycles : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q Q' : Finset (PlE D.host)) (a a' : ℕ) (Φ : Matrix (Fin a) (Fin a) A) (Φ' : Matrix (Fin a') (Fin a') A) Z Z' (γ σ : Bool → GE N), Univ bkP i s κ Q Φ Z → Univ bkP i s κ Q' Φ' Z' → (∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] (f : GE N → Fin D.R.r → Y), SelC bkP i s κ Y Q' f → (∀ b, f (γ b) = 0) → SelC bkP i s κ Y Q f) → (∀ (Y : Type) [AddCommGroup Y] [Module A Y] b m, repOn (Tgl i s) κ Y (σ b) m = m) → ∃ E : Matrix (Fin a) (Fin a') A, what₂ E ⊔ (what₂ Φ' ⊔ what₂ (fun j : Bool × Fin D.R.r => Z' (γ j.1) j.2)) = ⊤ ∧ (∀ b, (Φ * E) b ∈ what₂ Φ' ⊔ what₂ (fun j : Bool × Fin D.R.r => Z' (γ j.1) j.2)) ∧ ∀ j : Bool × Fin D.R.r, Z' (σ j.1) j.2 - Matrix.vecMul (Z (σ j.1) j.2) E ∈ what₂ Φ' ⊔ what₂ (fun j : Bool × Fin D.R.r => Z' (γ j.1) j.2) := by
  intro D N X bkP i s A _ _ κ Q Q' a a' Φ Φ' Z Z' γ σ hU hU' hSel hσ
  set W : Submodule A (Fin a' → A) := what₂ Φ' ⊔ what₂ (fun j : Bool × Fin D.R.r => Z' (γ j.1) j.2) with hW
  letI tY : TopologicalSpace ((Fin a' → A) ⧸ W) := ⊥
  haveI : DiscreteTopology ((Fin a' → A) ⧸ W) := ⟨rfl⟩
  let gens : Fin a' → (Fin a' → A) ⧸ W := fun j => W.mkQ (Pi.single j 1)
  have hsum : ∀ v : Fin a' → A, ∑ j, v j • gens j = W.mkQ v := by
    intro v
    have : v = ∑ j, v j • (Pi.single j (1 : A) : Fin a' → A) := by
      funext c
      simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [this]
    simp [gens, map_sum]
  have hrect : ∀ g c, rect (Z' g) gens c = W.mkQ (Z' g c) := fun g c => hsum _
  have hgens : matAct Φ' gens = 0 := by
    funext b
    have : matAct Φ' gens b = W.mkQ (Φ' b) := hsum (Φ' b)
    rw [this]
    exact (Submodule.Quotient.mk_eq_zero W).2 ((le_sup_left : what₂ Φ' ≤ W) (Submodule.subset_span ⟨b, rfl⟩))
  have hf' := (hU' ((Fin a' → A) ⧸ W)).1 gens hgens
  have hγ : ∀ b, (fun g => rect (Z' g) gens) (γ b) = 0 := by
    intro b
    funext c
    show rect (Z' (γ b)) gens c = 0
    rw [hrect]
    exact (Submodule.Quotient.mk_eq_zero W).2
      ((le_sup_right : what₂ (fun j : Bool × Fin D.R.r => Z' (γ j.1) j.2) ≤ W) (Submodule.subset_span ⟨(b, c), rfl⟩))
  have hf := hSel _ _ hf' hγ
  obtain ⟨x, hx, m, hm⟩ := (hU ((Fin a' → A) ⧸ W)).2.2 _ hf
  obtain ⟨E, hE⟩ : ∃ E : Matrix (Fin a) (Fin a') A, ∀ b, W.mkQ (E b) = x b :=
    ⟨fun b => (Submodule.mkQ_surjective W (x b)).choose, fun b => (Submodule.mkQ_surjective W (x b)).choose_spec⟩
  have hvm : ∀ v : Fin a → A, W.mkQ (∑ k, v k • E k) = ∑ k, v k • x k := fun v => by
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [map_smul, hE]
  refine ⟨E, ?_, ?_, ?_⟩
  · let S : Submodule A ((Fin a' → A) ⧸ W) := Submodule.span A (Set.range x)
    letI tS : TopologicalSpace (((Fin a' → A) ⧸ W) ⧸ S) := ⊥
    haveI : DiscreteTopology (((Fin a' → A) ⧸ W) ⧸ S) := ⟨rfl⟩
    have hpx : S.mkQ ∘ x = 0 := by
      funext b
      exact (Submodule.Quotient.mk_eq_zero S).2 (Submodule.subset_span ⟨b, rfl⟩)
    have hz : S.mkQ ∘ gens = 0 := by
      refine (hU' (((Fin a' → A) ⧸ W) ⧸ S)).2.1 _ ?_ ⟨S.mkQ.compLeft (Fin D.R.r) m, fun g => ?_⟩
      · rw [← matAct_map, hgens]
        funext b
        simp
      · have e := congrArg (S.mkQ.compLeft (Fin D.R.r)) (hm g)
        rw [map_sub, map_sub, rect_map, rect_map, hpx, repOn_map] at e
        have h0 : rect (Z g) (0 : Fin a → ((Fin a' → A) ⧸ W) ⧸ S) = 0 := by
          funext c
          simp [rect]
        rw [h0, sub_zero] at e
        exact e
    have hgS : ∀ j, gens j ∈ S := fun j =>
      (Submodule.Quotient.mk_eq_zero S).1 (congrFun hz j)
    rw [eq_top_iff]
    intro v _
    have hvS : W.mkQ v ∈ S := by
      rw [← hsum]
      exact S.sum_mem fun j _ => S.smul_mem _ (hgS j)
    have hSm : S = (what₂ E).map W.mkQ := by
      show Submodule.span A (Set.range x) = (Submodule.span A (Set.range E)).map W.mkQ
      rw [Submodule.map_span]
      congr 1
      ext y
      constructor
      · rintro ⟨b, rfl⟩
        exact ⟨E b, ⟨b, rfl⟩, hE b⟩
      · rintro ⟨_, ⟨b, rfl⟩, rfl⟩
        exact ⟨b, (hE b).symm⟩
    rw [hSm] at hvS
    obtain ⟨e, he, hev⟩ := hvS
    have hd : v - e ∈ W := by
      rw [← Submodule.Quotient.mk_eq_zero W, ← Submodule.mkQ_apply, map_sub, hev, sub_self]
    have : v = e + (v - e) := by abel
    rw [this]
    exact Submodule.add_mem_sup he hd
  · intro b
    rw [← Submodule.Quotient.mk_eq_zero W, ← Submodule.mkQ_apply]
    have e1 : (Φ * E) b = ∑ k, Φ b k • E k := by
      funext c
      simp [Matrix.mul_apply, Finset.sum_apply]
    rw [e1, hvm (Φ b)]
    exact congrFun hx b
  · rintro ⟨b, c⟩
    rw [← Submodule.Quotient.mk_eq_zero W, ← Submodule.mkQ_apply]
    have e1 : Matrix.vecMul (Z (σ b) c) E = ∑ k, Z (σ b) c k • E k := by
      funext t
      simp [Matrix.vecMul, dotProduct, Finset.sum_apply]
    have e2 := congrFun (hm (σ b)) c
    rw [hσ, sub_self] at e2
    show W.mkQ (Z' (σ b) c - Matrix.vecMul (Z (σ b) c) E) = 0
    rw [map_sub, e1, hvm (Z (σ b) c), ← hrect]
    exact e2

end GlobalTheory.NewPrime
