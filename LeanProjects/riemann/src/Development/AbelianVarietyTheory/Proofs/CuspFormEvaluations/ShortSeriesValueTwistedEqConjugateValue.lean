import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.XLaterHarmonicNotMemSpan
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsNabTwist

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GalTw

namespace GlobalTheory.GalTw

theorem colSum_eq_of_isNab (hC : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]
    (nab nab' : NabV Xo c) (h : IsNab Xo c nab) (h' : IsNab Xo c nab') {n : ℕ} (a : (E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN Dw n) c.F)
    (hP : P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)))
    (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (K : ℤ) (k : ℕ) (hK : K = (k : ℤ))
    (G : Fin n → LB.Sec (ReciprocityTheory.ChartRestriction.G.Out.LPow Xo.univ.t.G Xo.univ.t.PP.L K (ptO Xo y.x))) :
    ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y K (G b) (colOf m b) =
      ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab' y K (G b) (colOf m b) := by
  subst hK
  exact GlobalTheory.NabUniqCompare.thExprUniqSt_iff_top.1 (Formalism.MainNotions.ModuliIntegralCharts.H1.thExprUniq_of_chartIndep2 hC) E H Dw l Xo c
    nab nab' h h' S y k n G P
    ⟨(GlobalTheory.NabUniqCompare.isHarmonic_iff_cmType c P).2 hP.1, hP.2.1, a, hP.2.2⟩

theorem coeffAutFixesCMConjugatesAndBase_symm {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} {l : Level H} {c : Coeff l} {ta : c.F ≃+* c.F} (h : Fixes c ta) : Fixes c ta.symm :=
  ⟨fun τ a => (ta.symm_apply_eq).2 (h.emb τ a).symm, fun a => (ta.symm_apply_eq).2 (h.base a).symm⟩

theorem algebraMap_tw_symm {K : Type} [Field K] (ta : K ≃+* K) (S : Type) [CommRing S] [Algebra K S] (x : K) :
    (algebraMap K (Tw ta.symm S) (ta x)).val = algebraMap K S x := by
  change algebraMap K S (ta.symm (ta x)) = _
  rw [RingEquiv.symm_apply_apply]

theorem shortValAt_conj : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (ta : c.F ≃+* c.F) (h : Fixes c ta), ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), ∀ (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (b : c.F) (N : ℕ) (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : Tw ta S), ShortValAt Xo c nab w Λ b N P (twPt h y) v → ShortValAt Xo c nab (fun q => ta (w q)) Λ (ta b) N (MvPolynomial.map (ta : c.F →+* c.F) P) y v.val := by
  intro hC E _ _ _ H Dw l Xo c ta h _ nab hnab n a P hP w Λ b N S _ _ y v hv
  obtain ⟨S', i1, i2, φ, y', z, tp, F, hff, hmap, hz, hgeo, htp, hF, hv⟩ := hv
  have h' : Fixes c ta.symm := coeffAutFixesCMConjugatesAndBase_symm h
  have hnab' := GlobalTheory.GalTw.isNab_twist E H Dw l Xo c ta.symm h' nab hnab
  let φ' : S →ₐ[c.F] Tw ta.symm S' :=
    { toRingHom := φ.toRingHom
      commutes' := fun x => by
        have := φ.commutes (ta.symm x)
        change φ (algebraMap c.F S (ta (ta.symm x))) = _ at this
        rw [RingEquiv.apply_symm_apply] at this
        exact this }
  have hinj : Function.Injective (ta : c.F →+* c.F) := ta.injective
  have hsupp : (MvPolynomial.map (ta : c.F →+* c.F) P).support = P.support :=
    MvPolynomial.support_map_of_injective P hinj
  have hdeg : (MvPolynomial.map (ta : c.F →+* c.F) P).totalDegree = P.totalDegree := by
    unfold MvPolynomial.totalDegree
    rw [hsupp]
  refine ⟨Tw ta.symm S', inferInstance, inferInstance, φ', twPt h' y', z, tp, F, hff, hmap, hz, hgeo, htp, hF, ?_⟩
  have e1 : (ta b)⁻¹ * ((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((Nat.card (Fin n → LevQ Dw l) : c.F))⁻¹ *
        ((N : c.F) ^ P.totalDegree)⁻¹ = ta (b⁻¹ * ((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ *
        ((Nat.card (Fin n → LevQ Dw l) : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹) := by
    simp only [map_mul, map_inv₀, map_pow, map_natCast]
  rw [hsupp, hdeg, e1]
  refine hv.trans ?_
  refine congrArg₂ (fun s t : S' => s * t) (algebraMap_tw_symm ta S' _).symm ?_
  refine finsum_congr fun q => ?_
  refine congrArg₂ (fun s t : S' => s * t) (algebraMap_tw_symm ta S' _).symm ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  refine (colSum_eq_of_isNab hC Xo c _ _ hnab hnab' a P hP S' y' _ (N ^ 2) (Nat.cast_pow N 2).symm (F q i)).trans ?_
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_map]
  exact congrArg₂ (fun s t : S' => s * t) (algebraMap_tw_symm ta S' _).symm rfl

end GlobalTheory.GalTw
