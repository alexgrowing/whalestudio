import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasisOfBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandwichDatumEigenMultiplicityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrDeterminantProductOrdersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntertwinerMapsEigenspacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandwichDatumScalarActionStatement

noncomputable section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

section SlopeTestRemainingChoices

variable {O : Type} [CommRing O] {C : Type} [Field C] [Algebra O C]

theorem incl_apply' (h : ℕ) (l : Fin h → O) : incl C h l = fun i => algebraMap O C (l i) := rfl

theorem incl_mem_eig {Λ : Type} [CommRing Λ] {h : ℕ} (ρ : Λ → Matrix (Fin h) (Fin h) O)
    (σ : Λ →+* O) (l : Fin h → O) (hl : ∀ a, ρ a *ᵥ l = σ a • l) : incl C h l ∈ eig C ρ σ := by
  simp only [eig, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  intro a
  funext i
  have e := congrFun (hl a) i
  simp only [incl_apply', Pi.smul_apply, smul_eq_mul] at e ⊢
  rw [← map_mul, ← e, RingHom.map_mulVec]
  rfl

end SlopeTestRemainingChoices

section Parts

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] {C : Type} [Field C] [Algebra O C]
  {ε : PreTilt O p} {h : ℕ} {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ]

theorem card_eq_lieRank (hinj : Function.Injective (algebraMap O C)) (D : Datum ε h Λ)
    (τ : Λ →+* O) {a : ℕ} (x : Fin a → Fin h → C) (hx : IsBasisOf C (lieSub C D τ) x) :
    a = D.lieRank τ := by
  haveI : Nontrivial O := (algebraMap O C).domain_nontrivial
  have hincl : Function.Injective (incl C h : (Fin h → O) →ₗ[O] (Fin h → C)) := by
    intro u u' e
    funext i
    exact hinj (congrFun e i)
  have hliO : LinearIndependent O x := by
    refine hx.1.restrict_scalars ?_
    intro r s e
    apply hinj
    simpa [Algebra.algebraMap_eq_smul_one] using e
  have h1 : Module.finrank O (lieSub C D τ) = a := by
    rw [← hx.2, finrank_span_eq_card hliO, Fintype.card_fin]
  have h2 : Module.finrank O ↥(D.Lie ⊓ D.Tsub τ) = Module.finrank O (lieSub C D τ) :=
    (Submodule.equivMapOfInjective _ hincl _).finrank_eq
  unfold Datum.lieRank
  rw [h2, h1]

theorem span_eigPart_top (D : Datum ε h Λ) (τ : Λ →+* O)
    (hind : iSupIndep (fun σ : Λ →+* O => eig C (actT D) σ))
    (htop : (⨆ σ : Λ →+* O, eig C (actT D) σ) = ⊤) {n : ℕ} (u : Fin n → Fin h → C)
    (hu : Submodule.span O (Set.range u) = eigPart C (actT D) τ ⊤) (hue : ∀ i, u i ∈ eig C (actT D) τ) :
    Submodule.span C (Set.range u) = eig C (actT D) τ := by
  set S := Submodule.span C (Set.range u) with hSdef
  set R := ⨆ σ : {σ : Λ →+* O // σ ≠ τ}, eig C (actT D) σ.1 with hRdef
  have hSle : S ≤ eig C (actT D) τ := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hue i
  have hdisj : Disjoint (eig C (actT D) τ) R :=
    (hind τ).mono_right (iSup_le fun σ => le_iSup₂_of_le (f := fun j (_ : j ≠ τ) => eig C (actT D) j) σ.1 σ.2 le_rfl)
  have htop' : eig C (actT D) τ ⊔ R = ⊤ := by
    refine top_le_iff.1 ?_
    rw [← htop]
    refine iSup_le fun σ => ?_
    by_cases hσ : σ = τ
    · subst hσ
      exact le_sup_left
    · exact le_sup_of_le_right (le_iSup (fun σ : {σ : Λ →+* O // σ ≠ τ} => eig C (actT D) σ.1) ⟨σ, hσ⟩)
  have hS : ∀ z, z ∈ eigPart C (actT D) τ ⊤ → z ∈ S := by
    intro z hz
    rw [← hu] at hz
    exact Submodule.span_le_restrictScalars O C _ hz
  have hall : (⊤ : Submodule C (Fin h → C)) ≤ S ⊔ R := by
    rw [← (Pi.basisFun C (Fin h)).span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have hej : (Pi.basisFun C (Fin h) j) ∈ eig C (actT D) τ ⊔ R := by
      rw [htop']
      trivial
    obtain ⟨y, hy, r, hr, hyr⟩ := Submodule.mem_sup.1 hej
    have hy' : y ∈ eigPart C (actT D) τ ⊤ := by
      refine Submodule.mem_inf.2 ⟨hy, ?_⟩
      refine Submodule.mem_sup.2 ⟨Pi.basisFun C (Fin h) j, ⟨Pi.single j 1, trivial, ?_⟩, -r,
        Submodule.neg_mem _ hr, by rw [← hyr]; abel⟩
      funext k
      by_cases hk : k = j
      · subst hk
        simp [incl_apply']
      · simp [incl_apply', Pi.single_apply, hk]
    exact Submodule.mem_sup.2 ⟨y, hS y hy', r, hr, hyr⟩
  refine le_antisymm hSle fun z hz => ?_
  have hz' : z ∈ (S ⊔ R) ⊓ eig C (actT D) τ := ⟨hall trivial, hz⟩
  rwa [sup_inf_assoc_of_le R hSle, hdisj.symm.eq_bot, sup_bot_eq] at hz'

end Parts

theorem lieRank_add_card_and_lift : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ) (τ : Λ →+* O) (a b : ℕ) (x : Fin a → Fin h → C) (w : Fin a → Fin h → C) (n : Fin b → Fin h → C), IsBasisOf C (lieSub C D τ) x → IsBasisOf C (wQuot C D τ) w → IsBasisOf C (alQuot C D τ) n → a = D.lieRank τ ∧ a + b = N ∧ ∀ i, ∃ y : eig C (actH D) τ, bC C D y = x i := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ N h hh D τ a b x w n hx hw hn
  obtain ⟨⟨hindT, htopT, hdimT⟩, ⟨hindH, htopH, hdimH⟩⟩ :=
    GlobalTheory.T.sandwich_datum_eigen_multiplicity p C v O hv ε hε Λ N h hh D
  refine ⟨card_eq_lieRank hv.hom_inj D τ x hx, ?_, ?_⟩
  · obtain ⟨u, -, -, hu, -⟩ := GlobalTheory.T.dvr_determinant_product_orders p C v O hv ε hε Λ a b h D τ w n hw hn
    have hspan := span_eigPart_top D τ hindT htopT (fun i => (u i : Fin h → C)) hu.2
      (fun i => (u i).2)
    have e := finrank_span_eq_card hu.1
    rw [hspan, hdimT τ, Fintype.card_fin] at e
    exact e.symm
  · intro i
    have hint := GlobalTheory.T.sandwich_datum_scalar_action p C v O hv ε hε Λ h D
    have hX : ∀ l, D.G.map (WittVector.fontaineTheta O p) * actH D l =
        actT D l * D.G.map (WittVector.fontaineTheta O p) := by
      intro l
      have e' := congrArg (fun M => M.map (WittVector.fontaineTheta O p)) (hint.2.2.1 l)
      simp only [Matrix.map_mul] at e'
      unfold actH actT
      rw [e']
      simp only [rhoTA, Matrix.map_map]
      rfl
    have hmap := (GlobalTheory.T.intertwiner_maps_eigenspaces C O Λ h (actH D) (actT D)
      (D.G.map (WittVector.fontaineTheta O p)) hX).2 htopH hindT τ
    have hbC : bC C D = Matrix.toLin' ((D.G.map (WittVector.fontaineTheta O p)).map (algebraMap O C)) :=
      rfl
    have hxi : x i ∈ lieSub C D τ := hx.2 ▸ Submodule.subset_span ⟨i, rfl⟩
    obtain ⟨l, ⟨hlL, hlT⟩, hl⟩ := Submodule.mem_map.1 hxi
    obtain ⟨m, rfl⟩ := hlL
    have hT : incl C h (D.bb m) ∈ eig C (actT D) τ := by
      refine incl_mem_eig _ _ _ fun c => ?_
      have := (Submodule.mem_iInf _).1 hlT c
      rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at this
      exact this
    have hR : incl C h (D.bb m) ∈ LinearMap.range (bC C D) := by
      refine ⟨incl C h m, ?_⟩
      funext k
      rw [hbC, Matrix.toLin'_apply, incl_apply', incl_apply']
      show _ = algebraMap O C ((D.G.map (WittVector.fontaineTheta O p) *ᵥ m) k)
      rw [RingHom.map_mulVec]
      rfl
    rw [hbC] at hR
    have hmem := hmap ▸ (Submodule.mem_inf.2 ⟨hR, hT⟩)
    obtain ⟨y, hy, hyeq⟩ := Submodule.mem_map.1 hmem
    exact ⟨⟨y, hy⟩, by rw [hbC]; exact hyeq.trans hl⟩

end GlobalTheory.DetInv
