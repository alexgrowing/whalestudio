import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.IsSelfOf
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GeZeroOfIsIntegral

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.SeparatedDirections

theorem directions_typed_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y → ∀ (A : Type) [Fintype A] (tau : A → (E →+* ℂ)), (∀ s s', s ≠ s' → ∃ x : 𝓞 E, V.v (emA3 io ι (tau s) x - emA3 io ι (tau s') x) = 0) → (∀ s (x : Fin (Dw.mult (tau s))) i, V.Ge 0 (ι (chartUnitVectors C3 ⟨tau s, x⟩ i))) ∧ (∀ s (x : Fin (Dw.mult (tau s))) (a : 𝓞 E), linAct (Y.B.A.act a) (fun i => ι (chartUnitVectors C3 ⟨tau s, x⟩ i)) = emA3 io ι (tau s) a • fun i => ι (chartUnitVectors C3 ⟨tau s, x⟩ i)) ∧ (∃ w : Fin (chD C3.ch) → (Σ s : A, Fin (Dw.mult (tau s))) → C, (∀ i q, V.Ge 0 (w i q)) ∧ ∀ q q' : (Σ s : A, Fin (Dw.mult (tau s))), ∑ i, ι (chartUnitVectors C3 ⟨tau q.1, q.2⟩ i) * w i q' = if q = q' then 1 else 0) ∧ ∀ s (v : Fin (chD C3.ch) → C), (∀ a : 𝓞 E, linAct (Y.B.A.act a) v = emA3 io ι (tau s) a • v) → ∃ b : Fin (Dw.mult (tau s)) → C, v = ∑ x, b x • fun i => ι (chartUnitVectors C3 ⟨tau s, x⟩ i) := by
  intro E _ _ _ H Dw l Xo c _ hs T io y C3 C _ _ V ι hι k Y hY A _ tau hsep
  letI := io.toAlgebra
  have hval : ∀ x : T.V, V.Ge 0 (ι (algebraMap T.V T.Fr x)) :=
    (GlobalTheory.nval_eq_of_extension T C V.v V.l V.l_prime.ne_zero V.v_l ι hι).1
  have huv : ∀ ℓ i, chartUnitVectors C3 ℓ i = algebraMap T.V T.Fr (C3.uvecT ℓ i) := fun ℓ i =>
    C3.gen.1.2.2.2.2.2.2 ℓ i
  have hint : ∀ (τ : E →+* ℂ) (x : 𝓞 E), V.Ge 0 (emA3 io ι τ x) := fun τ x =>
    GlobalTheory.LabelledDirections.ge_zero_of_isIntegral V
      (map_isIntegral_int (emA3 io ι τ) (Algebra.IsIntegral.isIntegral x))
  let M : 𝓞 E → Matrix (Fin (chD C3.ch)) (Fin (chD C3.ch)) C := fun a i j =>
    MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (Y.B.A.act a i)
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
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s x i
    rw [huv]
    exact hval _
  · intro s x a
    exact heig a ⟨tau s, x⟩
  · have key := GlobalTheory.SatBlocks.saturated_blocks_summand C V.v (𝓞 E) A
      (fun a => Dw.mult (tau a)) (chD C3.ch) M (fun a x => emA3 io ι (tau a) x)
      (fun q i => ι (chartUnitVectors C3 ⟨tau q.1, q.2⟩ i)) (fun x i j => Y.intAct x i _) (fun a x => hint _ x)
      (fun x q => heig x ⟨tau q.1, q.2⟩)
      hsep
      (fun a => by
        obtain ⟨⟨w, emb, hw1, hw2⟩, -⟩ := Formalism.L2.Pj.SaturatedCharts.saturation_charts_holds Xo c T io y C3 (tau a)
        obtain ⟨W, hW⟩ := GlobalTheory.LabelledDirections.exists_dual w emb hw2
        refine ⟨fun s i => ι (algebraMap T.V T.Fr (W s i)), fun s i => hval _, fun i i' => ?_⟩
        have := congrArg (ι.comp (algebraMap T.V T.Fr)) (hW i i')
        rw [map_sum, apply_ite (ι.comp (algebraMap T.V T.Fr)), map_one, map_zero] at this
        refine Eq.trans ?_ this
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [map_mul, hw1]
        dsimp only
        rw [huv]
        rfl)
    obtain ⟨w, h1, h2⟩ := key
    exact ⟨w, h1, fun q q' => by convert h2 q q'⟩
  · intro a v hv
    have hinj : Function.Injective fun (τ : E →+* ℂ) (x : 𝓞 E) => emA3 io ι τ x := by
      intro τ τ' h
      by_contra hne
      obtain ⟨b, hb⟩ := GlobalTheory.EigDir.embK_sep c τ τ' hne
      exact hb ((ι.comp io).injective (congrFun h b))
    exact GlobalTheory.eigenvector_mem_span_block_of_basis T.Fr C ι (𝓞 E) (E →+* ℂ) Dw.mult (chD C3.ch) M
      (fun τ x => emA3 io ι τ x) (chartUnitVectors C3) hinj heig C3.ch.chart.basis (tau a) v hv

end GlobalTheory.SeparatedDirections
