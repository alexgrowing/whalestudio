import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
import Formalism.LocalToGlobal.ProjectiveLattices.CompOrd
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHoldStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIdempotentWeightZeroSectionOfComponentStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SectionEqZeroOfGenericFramedPointValues
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsGenericComponentPointsOffMeagreStatement

open NumberField Topology ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.GenericDetect

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem rdU_eq_zero_iff (hL : GlobalTheory.Reg.EvLaws Xo c) (U : Unf Xo c σ r) (h : GenFrEx Xo c) (k : U.Comp)
    (Z : Comp Xo c) (x : (U.X k).dom) (φ : Om Z →ₐ[c.F] CAt σ) (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ)
    (hm : FrMap φ (genFr h Z) y') (hb : FrBor t (U.un k x) y') {u : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c}
    (hf : f ∈ sec Xo c u n) : rdU U f k x = 0 ↔ evC h Z f = 0 := by
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  have h1 : evR Xo c f y' = φ (evC h Z f) := by
    obtain ⟨q, χ, y₀, hy₀⟩ := hL.test (Om Z) (genFr h Z)
    unfold evC
    rw [GlobalTheory.Reg.evR_eq_map_of_test_point hL hf q χ y₀ _ hy₀,
      GlobalTheory.Reg.evR_eq_map_of_test_point hL hf q (φ.comp χ) y₀ y' (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans χ φ hy₀ hm)]
    rfl
  have h2 : evR Xo c f y' = wchar (ex Dw u n) t * evR Xo c f (U.un k x) :=
    hL.wt u n f hf (CAt σ) t _ _ (hL.test _ _) (hL.test _ _) hb
  have h3 : wchar (ex Dw u n) t ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (t i).ne_zero
  have h4 : rdU U f k x = toC (evR Xo c f (U.un k x)) := by
    simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk]
    rw [dif_pos x.2]
  have h5 : φ (evC h Z f) = 0 ↔ evC h Z f = 0 := map_eq_zero_iff φ φ.toRingHom.injective
  rw [h4, ← h5, ← h1, h2, mul_eq_zero, or_iff_right h3]
  rfl

theorem eq_zero_of_off_meagre {V : Type} [TopologicalSpace V] [BaireSpace V] {D : Set V} (hD : IsOpen D)
    {S : ℕ → Set V} (hS : ∀ n, IsClosed (S n) ∧ interior (S n) = ∅) {g : V → ℂ} (hg : ContinuousOn g D)
    (h0 : ∀ x ∈ D, (∀ n, x ∉ S n) → g x = 0) : ∀ x ∈ D, g x = 0 := by
  have hd : Dense (⋂ n, (S n)ᶜ) :=
    dense_iInter_of_isOpen (fun n => (hS n).1.isOpen_compl) fun n => interior_eq_empty_iff_dense_compl.1 (hS n).2
  intro x hx
  by_contra hne
  have ho : IsOpen (D ∩ g ⁻¹' {0}ᶜ) := hg.isOpen_inter_preimage hD isOpen_compl_singleton
  obtain ⟨y, hy, hy'⟩ := hd.inter_open_nonempty _ ho ⟨x, hx, hne⟩
  exact hy.2 (h0 y hy.1 (Set.mem_iInter.1 hy'))

end GlobalTheory.GenericDetect

open GlobalTheory.GenericDetect in

theorem GlobalTheory.evC_eq_zero_iff_rdU_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → ∀ (h : GenFrEx Xo c) (k : U.Comp) (Z : Comp Xo c) (x₀ : (U.X k).dom), (∃ (φ : Om Z →ₐ[c.F] CAt σ) (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), FrMap φ (genFr h Z) y' ∧ FrBor t (U.un k x₀) y') → (∀ (u : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom u n → ∀ f ∈ sec Xo c u n, evC h Z f = 0 ↔ ∀ x ∈ (U.X k).dom, rdU U f k x = 0) := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU h k Z x₀ ⟨φ, y', t, hm, hb⟩ u n hd f hf
  obtain ⟨hL, -, -, hA⟩ := GlobalTheory.T.evaluation_laws_generic_frames_atlas_hold E H Dw l Xo c
  refine ⟨fun h0 => ?_, fun h0 => (rdU_eq_zero_iff hL U h k Z x₀ φ y' t hm hb hf).1 (h0 _ x₀.2)⟩
  obtain ⟨Z', S, hS, hg⟩ := GlobalTheory.T.exists_genericComponentPoints_off_meagre E H Dw l Xo c σ r U hσ hU h k
  have hO : IsOpen (U.X k).dom := FourierCoefficientDomain.isOpen_dom _
  have key : ∀ (a : (E →+* ℂ) × ℕ → ℕ) (m : ℕ), Dom a m → ∀ g ∈ sec Xo c a m, evC h Z' g = 0 →
      ∀ x ∈ (U.X k).dom, rdU U g k x = 0 := by
    intro a m ha g hgs hg0
    refine eq_zero_of_off_meagre hO hS (hU.2.2.2.2.1 a m ha g hgs k).1.continuousOn fun x hx hxS => ?_
    obtain ⟨ψ, z, s, hm', hb'⟩ := hg ⟨x, hx⟩ hxS
    exact (rdU_eq_zero_iff hL U h k Z' ⟨x, hx⟩ ψ z s hm' hb' hgs).2 hg0
  have hZ : Z' = Z := by
    by_contra hne
    obtain ⟨χ, hχ, -, h1, hz⟩ := GlobalTheory.T.exists_idempotent_weightZero_section_of_component E H Dw l Xo c hL h (hA h) Z
    have hD : Dom (E := E) 0 0 := ⟨fun τ _ _ _ => le_rfl, Even.zero⟩
    have := (rdU_eq_zero_iff hL U h k Z x₀ φ y' t hm hb hχ).1 (key 0 0 hD χ hχ (hz Z' hne) _ x₀.2)
    rw [h1] at this
    exact one_ne_zero this
  subst hZ
  exact key u n hd f hf h0

end
