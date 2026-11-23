import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.HostTraceIdentity
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SaturationChartsHolds
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDirectionsAreEigenvectors
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EigenvectorMemSpanBlockOfBasis
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.SaturatedBlocksSummand
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.VVAlgebraMapNonnegDvr

open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj Formalism.L2.FormalSeriesBounds NumberField

namespace GlobalTheory.LabelledDirections

theorem ge_zero_of_isIntegral {C : Type} [Field C] (V : VF C) {x : C} (hx : IsIntegral ℤ x) : V.Ge 0 x := by
  let A : ValuationSubring C :=
    { VF.RR V with
      mem_or_inv_mem' := by
        intro z
        by_cases hz : z = 0
        · left; rw [hz]; exact VF.Ge.zero 0
        · by_contra hc
          push Not at hc
          obtain ⟨h1, h2⟩ := hc
          have h1' : V.v z < 0 := lt_of_not_ge h1
          have h2' : V.v z⁻¹ < 0 := lt_of_not_ge h2
          have h3 : V.v (z * z⁻¹) = 0 := by rw [mul_inv_cancel₀ hz]; simp
          rw [V.v.map_mul] at h3
          have h4 : V.v z + V.v z⁻¹ ≤ V.v z + 0 := add_le_add le_rfl h2'.le
          rw [h3, add_zero] at h4
          exact absurd h1' (not_lt.2 h4) }
  have h : IsIntegral A x := hx.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (K := C) h
  rw [← hy]
  exact y.2

theorem exists_dual {R : Type} [CommRing R] {d m : ℕ} (w : Fin d → Fin d → R) (emb : Fin m ↪ Fin d)
    (hw : ∀ v : Fin d → R, ∃! a : Fin d → R, ∀ j, ∑ k, a k * w k j = v j) :
    ∃ W : Fin d → Fin m → R, ∀ i i', ∑ s, w (emb i) s * W s i' = if i = i' then 1 else 0 := by
  classical
  let U : Matrix (Fin d) (Fin d) R := Matrix.of w
  let W : Matrix (Fin d) (Fin d) R := Matrix.of fun t => (hw (Pi.single t 1)).exists.choose
  have hWU : W * U = 1 := by
    ext t s
    have := (hw (Pi.single t 1)).exists.choose_spec s
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [W, U, Matrix.of_apply]
    rw [this, Pi.single_apply]
    simp [eq_comm]
  have hUW : U * W = 1 := mul_eq_one_comm.1 hWU
  refine ⟨fun s i' => W s (emb i'), fun i i' => ?_⟩
  have := congrFun (congrFun hUW (emb i)) (emb i')
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  simpa [U] using this

theorem labGeoSt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], Formalism.L2.FormalSeriesBounds.LabGeoSt Xo c := by
  intro E _ _ _ H Dw l Xo c _ hs T io y C3 C _ _ V ι hι k Y hY Orb d _ lab ha
  classical
  letI := io.toAlgebra
  have hval : ∀ x : T.V, V.Ge 0 (ι (algebraMap T.V T.Fr x)) :=
    (GlobalTheory.nval_eq_of_extension T C V.v V.l V.l_prime.ne_zero V.v_l ι hι).1
  have huv : ∀ ℓ i, chartUnitVectors C3 ℓ i = algebraMap T.V T.Fr (C3.uvecT ℓ i) := fun ℓ i =>
    C3.gen.1.2.2.2.2.2.2 ℓ i
  have hint : ∀ (τ : E →+* ℂ) (x : 𝓞 E), V.Ge 0 (emA3 io ι τ x) := fun τ x =>
    ge_zero_of_isIntegral V (map_isIntegral_int (emA3 io ι τ) (Algebra.IsIntegral.isIntegral x))
  let M : 𝓞 E → Matrix (Fin (chD C3.ch)) (Fin (chD C3.ch)) C := fun a i j =>
    MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (Y.B.A.act a i)
  have hM : ∀ a z, linAct (Y.B.A.act a) z = (M a).mulVec z := fun a z => rfl
  have heig : ∀ (a : 𝓞 E) (ℓ : Lt1 Dw), (M a).mulVec (fun s => ι (chartUnitVectors C3 ℓ s)) =
      emA3 io ι ℓ.1 a • fun s => ι (chartUnitVectors C3 ℓ s) := by
    intro a ℓ
    funext i
    have h := congrArg ι (GlobalTheory.EigDir.linEig_holds E H Dw l Xo c T.Fr y.1 C3.ch a ℓ i)
    rw [map_sum, map_mul] at h
    refine Eq.trans ?_ h
    show ∑ j, M a i j * ι (chartUnitVectors C3 ℓ j) = _
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    simp only [M, hY.act, MvPowerSeries.coeff_map]
    rfl
  refine ⟨fun o g a x => hint _ x, ?_, ?_, ?_, ?_, ?_⟩
  · intro o a x
    have h : embK c (ComplexEmbedding.conjugate (lab.tau o 0 a)) x = embK c (lab.tau o 0 a) (H.bar x) := by
      apply Subtype.ext
      rw [embK_coe, embK_coe, ComplexEmbedding.conjugate_coe_eq, H.bar_eq,
        IsCMField.complexEmbedding_complexConj]
    rw [ha.conj, hs]
    exact congrArg (ι.comp io) h
  · intro o g x i
    unfold lieBasisVector
    rw [huv]
    exact hval _
  · intro o g x a
    exact heig a ⟨lab.tau o g x.1, x.2⟩
  · intro o g
    have key := GlobalTheory.SatBlocks.saturated_blocks_summand C V.v (𝓞 E) (ZMod d)
      (fun a => Dw.mult (lab.tau o g a)) (chD C3.ch) M (fun a x => emA3 io ι (lab.tau o g a) x)
      (lieBasisVector C3 ι lab o g) (fun x i j => Y.intAct x i _) (fun a x => hint _ x)
      (fun x q => heig x ⟨lab.tau o g q.1, q.2⟩)
      (fun a a' h => ha.sep (o, g, a) (o, g, a') (fun e => h (congrArg (fun p => p.2.2) e)))
      (fun a => by
        obtain ⟨⟨w, emb, hw1, hw2⟩, -⟩ := Formalism.L2.Pj.SaturatedCharts.saturation_charts_holds Xo c T io y C3 (lab.tau o g a)
        obtain ⟨W, hW⟩ := exists_dual w emb hw2
        refine ⟨fun s i => ι (algebraMap T.V T.Fr (W s i)), fun s i => hval _, fun i i' => ?_⟩
        have := congrArg (ι.comp (algebraMap T.V T.Fr)) (hW i i')
        rw [map_sum, apply_ite (ι.comp (algebraMap T.V T.Fr)), map_one, map_zero] at this
        refine Eq.trans ?_ this
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [map_mul, hw1]
        unfold lieBasisVector
        rw [huv]
        rfl)
    obtain ⟨w, h1, h2⟩ := key
    exact ⟨w, h1, fun q q' => by convert h2 q q'⟩
  · intro o g a v hv
    have hinj : Function.Injective fun (τ : E →+* ℂ) (x : 𝓞 E) => emA3 io ι τ x := by
      intro τ τ' h
      by_contra hne
      obtain ⟨b, hb⟩ := GlobalTheory.EigDir.embK_sep c τ τ' hne
      exact hb ((ι.comp io).injective (congrFun h b))
    obtain ⟨b, hb⟩ := GlobalTheory.eigenvector_mem_span_block_of_basis T.Fr C ι (𝓞 E) (E →+* ℂ) Dw.mult (chD C3.ch) M
      (fun τ x => emA3 io ι τ x) (chartUnitVectors C3) hinj heig C3.ch.chart.basis (lab.tau o g a) v hv
    refine ⟨fun q => if h : q.1 = a then b (Fin.cast (by rw [h]) q.2) else 0, fun q hq => dif_neg hq, ?_⟩
    rw [hb, Fintype.sum_sigma, Finset.sum_eq_single a]
    · refine Finset.sum_congr rfl fun i _ => ?_
      dsimp only
      rw [dif_pos rfl]
      rfl
    · intro a' _ ha'
      refine Finset.sum_eq_zero fun i _ => ?_
      dsimp only
      rw [dif_neg ha', zero_smul]
    · intro h
      exact absurd (Finset.mem_univ a) h

end GlobalTheory.LabelledDirections
