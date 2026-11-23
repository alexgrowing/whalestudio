import Formalism.LocalToGlobal.Columns.WmpNatCardQuotEqPowFinrank

noncomputable section

namespace Formalism.L2.Col

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Module

section Paths

theorem double_sum_eq_of_filter_card {α M : Type} [DecidableEq α] [AddCommMonoid M] (A A' : Finset α) (B B' : α → Finset α) (φ : α → M)
    (h : ∀ f, (A.filter fun e => f ∈ B e).card = (A'.filter fun e => f ∈ B' e).card) :
    ∑ e ∈ A, ∑ f ∈ B e, φ f = ∑ e ∈ A', ∑ f ∈ B' e, φ f := by

  have key : ∀ (A : Finset α) (B : α → Finset α) (U : Finset α), (∀ e ∈ A, B e ⊆ U) →
      ∑ e ∈ A, ∑ f ∈ B e, φ f = ∑ f ∈ U, (A.filter fun e => f ∈ B e).card • φ f := by
    intro A B U hU
    rw [Finset.sum_comm' (t' := U) (s' := fun f => A.filter fun e => f ∈ B e)]
    · simp only [Finset.sum_const]
    · intro e f
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨he, hf⟩
        exact ⟨⟨he, hf⟩, hU e he hf⟩
      · rintro ⟨⟨he, hf⟩, -⟩
        exact ⟨he, hf⟩
  set U := A.biUnion B ∪ A'.biUnion B'
  rw [key A B U (fun e he => (Finset.subset_biUnion_of_mem B he).trans Finset.subset_union_left),
    key A' B' U (fun e he => (Finset.subset_biUnion_of_mem B' he).trans Finset.subset_union_right)]
  exact Finset.sum_congr rfl fun f _ => by rw [h f]

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

open Classical in

def decorationPathCount (P Q : Ideal (𝓞 E)) (i j : ℕ) (d f : DecoSet E n ST SG) : ℕ :=
  ((d.heckeNb P i).filter fun e => f ∈ e.heckeNb Q j).card

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K}

open Classical in
theorem card_filter_neighbours_eq_paths (c : DecoPts S E n ST SG) (P Q : Ideal (𝓞 E)) (i j : ℕ) (d f : S.D) :
    ((c.nb P i d).filter fun e => f ∈ c.nb Q j e).card = decorationPathCount P Q i j (c.pts d) (c.pts f) := by
  show ((((c.pts d).heckeNb P i).map c.pts.symm.toEmbedding).filter fun e => f ∈ c.nb Q j e).card = _
  rw [Finset.filter_map, Finset.card_map]
  unfold decorationPathCount
  congr 1
  ext x
  simp only [Finset.mem_filter, Function.comp_apply, Equiv.toEmbedding_apply, DecoPts.mem_nb,
    Equiv.apply_symm_apply]

theorem heckeOperators_commute_of_paths (c : DecoPts S E n ST SG) (P Q : Ideal (𝓞 E)) (i j : ℕ)
    (h : ∀ d f : DecoSet E n ST SG, decorationPathCount P Q i j d f = decorationPathCount Q P j i d f) :
    Commute (heckeD c P i).op (heckeD c Q j).op := by
  classical
  refine LinearMap.ext fun φ => Subtype.ext (funext fun d => ?_)
  show (((heckeD c P i).op ((heckeD c Q j).op φ) : S.EqFun) : S.D → S.V) d =
    (((heckeD c Q j).op ((heckeD c P i).op φ) : S.EqFun) : S.D → S.V) d
  simp only [heckeD, LocOp.ofNbr_op_apply, LinearMap.id_apply]
  refine double_sum_eq_of_filter_card _ _ _ _ _ fun f => ?_
  rw [card_filter_neighbours_eq_paths, card_filter_neighbours_eq_paths, h]

def DecorationPathSymmetry (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (ST SG : Finset (HeightOneSpectrum (𝓞 E))) : Prop :=
  ∀ P Q : HeightOneSpectrum (𝓞 E), conjPrime₂ P ≠ P → conjPrime₂ Q ≠ Q →
    (∀ R : ST, R.1 ≠ P ∧ R.1 ≠ conjPrime₂ P) → (∀ w : SG, w.1 ≠ P ∧ w.1 ≠ conjPrime₂ P) →
    (∀ R : ST, R.1 ≠ Q ∧ R.1 ≠ conjPrime₂ Q) → (∀ w : SG, w.1 ≠ Q ∧ w.1 ≠ conjPrime₂ Q) →
    ∀ (i j : ℕ) (d f : DecoSet E n ST SG), decorationPathCount P.asIdeal Q.asIdeal i j d f = decorationPathCount Q.asIdeal P.asIdeal j i d f

private lemma levOff_conjP_ne_and_ne_places {S0 : Set (HeightOneSpectrum (𝓞 E))} (x : LevOff ST SG S0) :
    conjPrime₂ x.1 ≠ x.1 ∧ (∀ R : ST, R.1 ≠ x.1 ∧ R.1 ≠ conjPrime₂ x.1) ∧ (∀ w : SG, w.1 ≠ x.1 ∧ w.1 ≠ conjPrime₂ x.1) := by
  obtain ⟨P, h1, h2, h3⟩ := x
  rw [conjIdeal_asIdeal] at h1 h3
  refine ⟨fun h => h1 (congrArg HeightOneSpectrum.asIdeal h), fun R => ⟨?_, ?_⟩, fun w => ⟨?_, ?_⟩⟩
  · intro h
    have h' : R.1 = P := h
    apply h2
    rw [← h']
    exact Or.inl (Or.inr (Finset.mem_coe.2 R.2))
  · intro h
    exact h3 R.1 (Or.inl (Or.inr (Finset.mem_coe.2 R.2))) (congrArg HeightOneSpectrum.asIdeal h)
  · intro h
    have h' : w.1 = P := h
    apply h2
    rw [← h']
    exact Or.inr (Finset.mem_coe.2 w.2)
  · intro h
    exact h3 w.1 (Or.inr (Finset.mem_coe.2 w.2)) (congrArg HeightOneSpectrum.asIdeal h)

theorem heckeComm_of_paths (c : DecoPts S E n ST SG) (S0 : Set (HeightOneSpectrum (𝓞 E))) (h : DecorationPathSymmetry E n ST SG) :
    HeckeComm c S0 := by
  intro x y
  obtain ⟨hx1, hx2, hx3⟩ := levOff_conjP_ne_and_ne_places x.1
  obtain ⟨hy1, hy2, hy3⟩ := levOff_conjP_ne_and_ne_places y.1
  exact heckeOperators_commute_of_paths c _ _ _ _ fun d f => h x.1.1 y.1.1 hx1 hy1 hx2 hx3 hy2 hy3 x.2 y.2 d f

end Paths

end Formalism.L2.Col
