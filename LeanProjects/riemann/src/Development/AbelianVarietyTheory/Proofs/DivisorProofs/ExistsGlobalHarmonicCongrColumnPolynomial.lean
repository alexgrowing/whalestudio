import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PolyBetween
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LocalValuationColumns
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.FiniteNotLocFrOne
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAlgebraMapEqOfValVLeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormEqNegOne
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TotalDegreeLeAndExistsCombinationOfMemFFV

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RefGlob

theorem sum_smul_mem_HaO {Ty : Type} {r : Ty → ℕ} {n : ℕ} {k : Type} [Field k] (O : Subring k) (cc : Ty → Ty)
    (isX : Ty → Prop) (a : Ty → ℕ → ℕ) {m : ℕ} (x : Fin m → k) (P : Fin m → MvPolynomial (Letter Ty r n) k)
    (hx : ∀ i, x i ∈ O) (hP : ∀ i, P i ∈ HaO r n k O cc isX a) : ∑ i, x i • P i ∈ HaO r n k O cc isX a := by
  classical
  refine ⟨⟨Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hP i).1.1, fun σ i i' hi t => ?_,
    fun q hq => ?_⟩, fun q => ?_⟩
  · rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, (hP j).1.2.1 σ i i' hi t]
  · obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 (MvPolynomial.support_sum hq)
    exact (hP j).1.2.2 q (MvPolynomial.support_smul hj)
  · rw [MvPolynomial.coeff_sum]
    exact O.sum_mem fun j _ => by
      rw [MvPolynomial.coeff_smul, smul_eq_mul]
      exact O.mul_mem (hx j) ((hP j).2 q)

theorem exists_integer_congr {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (T₀ : CDVR)
    (io₀ : K →+* T₀.Fr) (ho : OverLa w T₀.V io₀ 1)
    (hini : ∀ (T : CDVR) (io : K →+* T.Fr) (e : ℕ), OverLa w T.V io e → ∃ (g : T₀.V →+* T.V) (χ : T₀.Fr →+* T.Fr),
      IsLocalHom g ∧ χ.comp io₀ = io ∧ χ.comp (algebraMap T₀.V T₀.Fr) = (algebraMap T.V T.Fr).comp g ∧
        ∀ ϖ : T₀.V, Irreducible ϖ → vV (K' := T.Fr) T.V (algebraMap T.V T.Fr (g ϖ)) = e)
    (d : ℕ) (hd : d ≠ 0) (v : T₀.V) :
    ∃ (x : 𝓞 K) (z : T₀.V), io₀ (x : K) = algebraMap T₀.V T₀.Fr v + (d : T₀.Fr) * algebraMap T₀.V T₀.Fr z := by
  obtain ⟨k, h, e⟩ := GlobalTheory.DefPt.Model.denseIn_of_initial w T₀ io₀ hini (algebraMap T₀.V T₀.Fr v) (d : T₀.V) (Nat.cast_ne_zero.2 hd)
  have hval : ∀ y : K, valV T₀.V (io₀ y) = w.valuation K y := fun y => by
    rw [GlobalTheory.PlaceCompletion.valV_eq_pow_of_overLa ho, pow_one]
  have hk : io₀ k = algebraMap T₀.V T₀.Fr (v - d * h) := by rw [map_sub, e]; ring
  have hk1 : w.valuation K k ≤ 1 := by
    rw [← hval, hk]
    exact GlobalTheory.PlaceCompletion.valV_algebraMap_le_one _
  have hdK : (d : K) ≠ 0 := Nat.cast_ne_zero.2 hd
  have hd0 : w.valuation K (d : K) ≠ 0 := by simpa using hd
  obtain ⟨x, hx⟩ := w.exists_valuation_sub_lt_of_integer hk1 (Units.mk0 _ hd0)
  obtain ⟨z, hz⟩ := GlobalTheory.PlaceCompletion.exists_algebraMap_eq_of_valV_le_one (V := T₀.V)
    (x := io₀ ((algebraMap (𝓞 K) K x - k) / d)) (by
      rw [hval, map_div₀]
      exact div_le_one_of_le₀ hx.le zero_le)
  refine ⟨x, z - h, ?_⟩
  have h2 : io₀ (x : K) = io₀ k + (d : T₀.Fr) * algebraMap T₀.V T₀.Fr z := by
    rw [hz, ← map_natCast io₀, ← map_mul, ← map_add, mul_div_cancel₀ _ hdK]
    exact congrArg io₀ (by simp)
  rw [h2, hk]
  simp only [map_sub, map_mul, map_natCast]
  ring

section Push

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {c : Coeff l} {T₀ T : CDVR} (g : T₀.V →+* T.V) (χ : T₀.Fr →+* T.Fr)
  (hχ : ∀ x, χ (algebraMap T₀.V T₀.Fr x) = algebraMap T.V T.Fr (g x))

include hχ

theorem isCols_map {io₀ : c.F →+* T₀.Fr} {p n : ℕ} {cx : Lt1 Dw → ℕ} {B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T₀.V}
    (hB : IsCols c T₀ io₀ p cx B) : IsCols c T (χ.comp io₀) p cx fun f b j => g (B f b j) := by
  obtain ⟨blk, hb⟩ := hB
  refine ⟨blk, fun f => ?_⟩
  obtain ⟨h1, ⟨r, h2⟩, h3⟩ := hb f
  refine ⟨fun b j hj => (congrArg g (h1 b j hj)).trans (map_zero g), ⟨r, ?_⟩, fun N => ?_⟩
  · have := h2.map g
    rw [RingHom.map_det] at this
    exact this
  · obtain ⟨x, hx1, hx2, hx3⟩ := h3 N
    refine ⟨x, hx1, fun b j => ?_, hx3⟩
    obtain ⟨z, hz⟩ := hx2 b j
    refine ⟨g z, ?_⟩
    rw [RingHom.comp_apply, hz, hχ]
    simp only [map_add, map_mul, map_pow, map_natCast]

theorem map_polyT {n : ℕ} (cx : Lt1 Dw → ℕ) (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T₀.V) :
    MvPolynomial.map χ (polyT B cx) = polyT (fun f b j => g (B f b j)) cx := by
  simp only [polyT, polyP, map_prod, map_pow]
  refine Finset.prod_congr rfl fun f _ => ?_
  rw [RingHom.map_det]
  congr 2
  ext ρ i : 2
  simp [GlobalTheory.CombMinor.cMat, hχ]

end Push

theorem exists_harmA_congr_polyT : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c) (a : (E →+* ℂ) × ℕ → ℕ), (∀ τ, Antitone fun i => a (τ, i)) → ∀ n : ℕ, ∑ f : Lt1 Dw, 2 * rk f ≤ n → ∀ N : ℕ, ∃ P₁ ∈ harmA (Dw := Dw) c a n, ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∃ (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V) (R : MvPolynomial (LtN Dw n) T.Fr), IsCols c T io p (gap Dw a) B ∧ R ∈ FFV (Dw := Dw) T a n ∧ MvPolynomial.map io P₁ = polyT B (gap Dw a) + ((p : T.Fr) ^ N) • R := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro p hp la a ha n hn N
  obtain ⟨T₀, io₀, ho₀, -, hini⟩ := GlobalTheory.PlaceCompletion.exists_initial_completion c.F la.1
  obtain ⟨B₀, hB₀⟩ := GlobalTheory.IsoCols.exists_isCols E H Dw l Xo c p la T₀ io₀ 1 ho₀ (gap Dw a) n
    (le_trans (Finset.sum_le_sum fun f _ => by split_ifs <;> simp) hn)
  obtain ⟨-, k, cf, Pi, hPi, hsum⟩ := GlobalTheory.totalDegree_le_and_exists_combination_of_mem_FFV E H Dw l Xo c T₀ io₀ a n _
    (polyT_mem_FFV ha hB₀)
  choose x z hxz using fun i => exists_integer_congr la.1 T₀ io₀ ho₀ hini (p ^ N)
    (pow_ne_zero N hp.out.ne_zero) (cf i)
  refine ⟨∑ i, (x i : c.F) • Pi i, sum_smul_mem_HaO _ _ _ _ _ _ (fun i => (x i).2) hPi, fun T io e ho => ?_⟩
  obtain ⟨g, χ, -, rfl, h2, -⟩ := hini T io e ho
  have hχ : ∀ y, χ (algebraMap T₀.V T₀.Fr y) = algebraMap T.V T.Fr (g y) := RingHom.congr_fun h2
  refine ⟨fun f b j => g (B₀ f b j), ∑ i, algebraMap T.V T.Fr (g (z i)) • MvPolynomial.map (χ.comp io₀) (Pi i),
    isCols_map g χ hχ hB₀, sum_smul_mem_HaO _ _ _ _ _ _ (fun i => ⟨_, rfl⟩)
      (fun i => PullbackSections.ffvMap E H Dw l c a n _ (hPi i) T _), ?_⟩
  rw [← map_polyT g χ hχ, hsum, map_sum, map_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, MvPolynomial.map_map, RingHom.comp_apply, hxz i,
    map_add, hχ, map_natCast, Nat.cast_pow, map_pow]
  ring

end GlobalTheory.RefGlob
