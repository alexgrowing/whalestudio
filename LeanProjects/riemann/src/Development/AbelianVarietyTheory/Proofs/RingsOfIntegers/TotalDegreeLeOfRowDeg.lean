import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceIdem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ChartValJ
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AdmissibleColumnsLeAndHarmonicMapCover

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

set_option autoImplicit false

namespace GlobalTheory.PlaceInt

theorem span_mul_prod_of_eq {E T : Type} [Field E] [Fintype T] {F F' : IntermediateField ℚ ℂ} (h : F' = F)
    (A B : Set E) (f : T → E →+* F) (f' : T → E →+* F')
    (hf : ∀ τ x, f' τ x = IntermediateField.equivOfEq h.symm (f τ x)) (m : T → ℕ) (β : F)
    (hβ : Submodule.span (𝓞 F) {β} * ∏ τ, Submodule.span (𝓞 F) (f τ '' A) ^ m τ =
      ∏ τ, Submodule.span (𝓞 F) (f τ '' B) ^ m τ) :
    Submodule.span (𝓞 F') {IntermediateField.equivOfEq h.symm β} * ∏ τ, Submodule.span (𝓞 F') (f' τ '' A) ^ m τ =
      ∏ τ, Submodule.span (𝓞 F') (f' τ '' B) ^ m τ := by
  subst h
  have hff : f' = f := funext fun τ => RingHom.ext fun x => hf τ x
  subst hff
  exact hβ

theorem totalDegree_le_of_rowDeg {T : Type} [Fintype T] (r : T → ℕ) (n : ℕ) {k : Type} [Field k] (a : T → ℕ → ℕ)
    (P : MvPolynomial (Letter T r n) k) (hP : RowDeg r n k a P) :
    P.totalDegree ≤ ∑ τ, ∑ i : Fin (r τ), a τ i := by
  unfold MvPolynomial.totalDegree
  refine Finset.sup_le fun m hm => le_of_eq ?_
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => hP m hm σ i

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n)

theorem eF_embF (τ : E →+* ℂ) (x : E) : d.eF (embF c τ x) = embF d.c₂ τ x := by
  exact Subtype.ext rfl

theorem map_eF_mem_symO (Λ : GenLat E n) (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ symO c Λ) :
    MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P ∈ symO (Dw := Dw) d.c₂ Λ := by
  have key : symO c Λ ≤ (symO (Dw := Dw) d.c₂ Λ).comap (MvPolynomial.map (d.eF : c.F →+* d.c₂.F)) := by
    refine Subring.closure_le.2 ?_
    rintro f (⟨o, rfl⟩ | ⟨σ, i, b, hb, rfl⟩)
    · refine Subring.mem_comap.2 (Subring.subset_closure (Or.inl ⟨⟨d.eF o, ?_⟩, ?_⟩))
      · exact o.2.map (d.eF : c.F →+* d.c₂.F).toIntAlgHom
      · rw [MvPolynomial.map_C]
        rfl
    · refine Subring.mem_comap.2 (Subring.subset_closure (Or.inr ⟨σ, i, b, hb, ?_⟩))
      simp only [letB, map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, RingHom.coe_coe, eF_embF]
  exact key hP

end

theorem eF_transfer : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (Λ : GenLat E n), (∀ β : c.F, BetaIs (Dw := Dw) c Λ β → BetaIs (Dw := Dw) d.c₂ Λ (d.eF β)) ∧ (∀ (w : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmL c Λ w → MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P ∈ harmL d.c₂ Λ w ∧ P.totalDegree ≤ Formalism.L2.Pj.DF Dw w) ∧ ∀ (w : (E →+* ℂ) × ℕ → ℕ) (α : 𝓞 E), d.eF (nrm Dw c w α) = nrm Dw d.c₂ w α := by
  intro E _ _ _ H Dw l Xo c n d Λ
  refine ⟨?_, ?_, ?_⟩
  · intro β hβ
    unfold BetaIs idealAt at hβ ⊢
    exact span_mul_prod_of_eq d.hF (detSet Λ.La) (detSet Λ.Ln) (fun τ => embF c τ) (fun τ => embF d.c₂ τ)
      (fun τ x => (eF_embF d τ x).symm) Dw.mult β hβ
  · intro w P hP
    obtain ⟨hH, hS⟩ := hP
    refine ⟨⟨GlobalTheory.map_mem_HHa Dw.mult n (d.eF : c.F →+* d.c₂.F) d.eF.surjective ComplexEmbedding.conjugate
      (InPsi H) (fun τ i => w (τ, i)) P hH, map_eF_mem_symO d Λ P hS⟩, ?_⟩
    exact totalDegree_le_of_rowDeg Dw.mult n (fun τ i => w (τ, i)) P hH.2.2
  · intro w α
    simp only [nrm, embK, map_prod, map_pow, RingHom.comp_apply, eF_embF]

end GlobalTheory.PlaceInt
