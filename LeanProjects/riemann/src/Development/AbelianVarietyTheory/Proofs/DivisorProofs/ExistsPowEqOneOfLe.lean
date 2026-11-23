import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorSupportBoundedByUniformizerPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorVanishesUnlessLastRowBounded
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAtOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PadOneMemSecondBlockTriangular
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun

noncomputable section

namespace GlobalTheory.PhaseField

open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem exists_field_roots {n : ℕ} (hn : 0 < n) : ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧
    ∀ z : ℂ, z ^ n = 1 → z ∈ Set.range (algebraMap M ℂ) := by
  classical
  set S : Set ℂ := {z | z ^ n = 1} with hSdef
  have hS : S = ((Polynomial.nthRoots n (1 : ℂ)).toFinset : Set ℂ) := by
    ext z; simp [S, Polynomial.mem_nthRoots hn]
  haveI : Finite S := by rw [hS]; infer_instance
  have hint : ∀ z ∈ S, IsIntegral ℚ z := fun z hz =>
    ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C _ hn.ne', by
      simp [Polynomial.eval₂_sub, show z ^ n = 1 from hz]⟩
  exact ⟨IntermediateField.adjoin ℚ S, IntermediateField.finiteDimensional_adjoin hint,
    fun z hz => ⟨⟨z, IntermediateField.subset_adjoin ℚ S hz⟩, rfl⟩⟩

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_resCard_le {ϖ : kˣ} (hϖ : IsUnif ϖ) : valuation k ((Nat.card 𝓀[k] : ℕ) : k) ≤ valuation k (ϖ : k) := by
  classical
  letI := Fintype.ofFinite 𝓀[k]
  have h0 : IsLocalRing.residue 𝒪[k] ((Nat.card 𝓀[k] : ℕ) : 𝒪[k]) = 0 := by
    rw [map_natCast, Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero _
  have hmem : ((Nat.card 𝓀[k] : ℕ) : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k] :=
    (IsLocalRing.residue_eq_zero_iff _).1 h0
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one] at hmem
  rw [hϖ, le_uniformizer_iff]
  simpa using hmem

theorem exists_pow_eq_one_of_le {ψ : AddChar k Circle} {ϖ : kˣ} (hψ : HasConductor ψ 1) (hϖ : IsUnif ϖ) (N : ℕ) :
    ∃ n : ℕ, 0 < n ∧ ∀ z : k, valuation k z ≤ valuation k (((ϖ ^ N)⁻¹ : kˣ) : k) → ((ψ z : Circle) : ℂ) ^ n = 1 := by
  have hq : 0 < Nat.card 𝓀[k] := Nat.card_pos
  refine ⟨Nat.card 𝓀[k] ^ N, pow_pos hq N, fun z hz => ?_⟩
  have h1 : valuation k (((Nat.card 𝓀[k] ^ N : ℕ) : k) * z) ≤ 1 := by
    rw [map_mul, Nat.cast_pow, map_pow]
    calc valuation k ((Nat.card 𝓀[k] : ℕ) : k) ^ N * valuation k z
        ≤ valuation k (ϖ : k) ^ N * valuation k (((ϖ ^ N)⁻¹ : kˣ) : k) :=
          mul_le_mul' (pow_le_pow_left₀ zero_le' (val_resCard_le hϖ) N) hz
      _ = 1 := by
          rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_inv₀, map_pow]
          exact mul_inv_cancel₀ (pow_ne_zero _ (by simp))
  have h2 : ψ (((Nat.card 𝓀[k] ^ N : ℕ) : k) * z) = 1 :=
    (hψ 1).2 le_rfl _ (by simpa using h1)
  rw [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow] at h2
  rw [← Circle.coe_pow, h2, Circle.coe_one]

end Local

open GlobalTheory.RootEx Matrix in

theorem phase_bounded {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k)
    [ν.IsAddHaarMeasure] (ϖ : kˣ) (e : ℕ) (T : G.Args → ℂ) (keep : Bool) (g : G.VertexGroup) (hm : 2 ≤ G.m)
    (hϖ : IsUnif ϖ) (hψ : HasConductor ψ 1) (hT : G.IsTensor ϖ e (oppositePath G.m) T) :
    ∃ N : ℕ, ∀ (x : ColArgs G) (y : RowArgs G) (v : Vars G), flatTensor hs ψ ν (moved G keep g T) x y ≠ 0 →
      moved G keep g T (fill hs x y v) ≠ 0 → valuation k (phase x v) ≤ valuation k (((ϖ ^ N)⁻¹ : kˣ) : k) := by
  classical
  obtain ⟨n1, hsupp⟩ := FlatSupp.flatTensor_support G hs ψ ν ϖ e T keep g hϖ hT
  obtain ⟨n2, hlast⟩ := FlatLast.flatTensor_lastRow_bounded G hs ψ ν ϖ e T keep g hm hϖ hψ hT
  choose N hN using fun b : Edge =>
    FlatSupp.exists_bound_conj hϖ (Assignment.one.read (g b.tgt)) (Assignment.one.read (g b.src))
  set K := max n1 (max n2 ((oppositePath G.m).toFinset.sup N)) with hK
  set c := valuation k (((ϖ ^ K)⁻¹ : kˣ) : k) with hc
  have hc1 : 1 ≤ c := by
    have := FlatSupp.val_inv_pow_mono hϖ (Nat.zero_le K)
    rwa [show valuation k (((ϖ ^ 0)⁻¹ : kˣ) : k) = 1 by simp] at this
  have hcc : valuation k (((ϖ ^ (K + K))⁻¹ : kˣ) : k) = c * c := by
    rw [hc, FlatSupp.val_inv_pow, FlatSupp.val_inv_pow, pow_add, mul_inv]
  refine ⟨K + K, fun x y v hF hM => ?_⟩
  rw [hcc]
  have hT0 : T (G.moveArgs .one g (fill hs x y v)) ≠ 0 := by
    intro h0
    apply hM
    simp [moved, Grid.pathAct, h0]
  have key : ∀ b ∈ oppositePath G.m, ∀ r s, valuation k (fill hs x y v b r s) ≤ c := by
    intro b hb r s
    refine le_trans (hN b _ (fun r s => ?_) r s) (FlatSupp.val_inv_pow_mono hϖ
      ((Finset.le_sup (f := N) (List.mem_toFinset.2 hb)).trans ((le_max_right _ _).trans (le_max_right _ _))))
    have hm' : (G.moveArgs .one g (fill hs x y v)) b ∈ matLat _ (GlobalTheory.SplitFlip.stdLat k _) := by
      by_contra h
      exact hT0 (hT.2.1 _ b hb h)
    exact mem_matLat_stdLat.1 hm' r s
  have hstep : ∀ (j : Fin (G.m - 1)) p q, valuation k (stepPt (x j) (v j) p q) ≤ c := by
    intro j p q
    have hmem : Edge.theta G.m j ∈ oppositePath G.m := by simp [oppositePath]; omega
    have hj' : (j : ℕ) < G.m - 1 := j.2
    have h := key _ hmem
      (frame (a := topRank G j) (b := G.rank (G.m, j)) (c := G.m - 2 - j + 1) (by have := topRank_add hs j; omega) q)
      (frame (a := topRank G (j + 1)) (b := G.rank (G.m, j + 1)) (c := G.m - 2 - j)
        (by have := topRank_add hs (j + 1); omega) p)
    rw [fill_theta, transpose_apply, downMap, dif_pos hj'] at h
    simpa [reindex_apply, submatrix_apply, Equiv.symm_apply_apply] using h
  have hx : ∀ j, j < G.m → ∀ r s, valuation k (x j r s) ≤ c := by
    intro j hj r s
    by_cases hr : j + 1 = G.m ∧ r = topLast G (j + 1)
    · obtain ⟨h1, rfl⟩ := hr
      obtain rfl : j = G.m - 1 := by omega
      exact (hlast x y hF s).trans (FlatSupp.val_inv_pow_mono hϖ ((le_max_left _ _).trans (le_max_right _ _)))
    · exact ((hsupp x y hF).1 j hj r s fun h h' => hr ⟨h, h'⟩).trans (FlatSupp.val_inv_pow_mono hϖ (le_max_left _ _))
  have hcol : ∀ j r, valuation k (colVar x v j r) ≤ c := fun j r => hstep j _ _
  have hrow : ∀ (j : Fin (G.m - 1)) r, valuation k (rowVar x v (j + 1) r) ≤ c := by
    intro j r
    unfold rowVar
    split_ifs with h
    · refine Valuation.map_sum_le _ fun l _ => ?_
      split_ifs
      · exact hstep ⟨_, h⟩ _ _
      · simp
    · exact hx _ (by omega) _ _
  have hch : ∀ j : Fin (G.m - 1), valuation k (ch (stepPt (x j) (v j))) ≤ c := fun j =>
    Valuation.map_sum_le _ fun i _ => hstep j _ _
  unfold phase
  refine Valuation.map_sum_le _ fun j _ => ?_
  refine Valuation.map_add_le _ ((hch j).trans (le_mul_of_one_le_right' hc1)) ?_
  split_ifs
  · refine Valuation.map_sum_le _ fun r _ => ?_
    rw [map_mul]
    exact mul_le_mul' (hrow j r) (hcol j r)
  · simp

theorem phases_core {D : D7} {T : Type} [Finite T] {L : LevCh D T} {sc : Consts} {μ₀ : T} (hL : L.Is μ₀) {G : GridData L sc}
    {W : G.Weil} {U : Set T} (S : GridChoice W U) (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ t, ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∀ t Φ, ∀ β ∈ S.supp t Φ, PhasesIn (algebraMap M ℂ) S t Φ β := by
  classical
  have hm : 2 ≤ D.R.m := D.R.two_le_m
  have hloc : ∀ t Φ (β : CosFam G t) (w : locPl G t), ∃ n : ℕ, 0 < n ∧ ∀ x y e, (S.term t Φ β w).datum x y ≠ 0 →
      moved (locGrid G t w) (keepAt G w) ((repsAt G t w).elt (β w)) (Tflip W S.B t Φ w) (fill one_le_sLen x y e) ≠ 0 →
      ((psiAt W w.1 (phase x e) : Circle) : ℂ) ^ n = 1 := by
    intro t Φ β w
    have hg := (Good.locGrid_isGood hL G W t hde (hc t)).1 w.1 w.2
    have h00 := hg.square 0 (by change 0 < D.R.m; omega) 0 (by change 0 < D.R.m; omega)
    haveI := (isUnitVol_unitVol w.1).1
    obtain ⟨N, hN⟩ := phase_bounded (locGrid G t w.1) one_le_sLen (psiAt W w.1) (unitVol w.1) (unifAt w.1) (depthAt G w.1)
      (Tflip W S.B t Φ w.1) (keepAt G w.1) ((repsAt G t w.1).elt (β w)) hm h00.unif h00.cond
      (isTensor_Tflip hL W S.B t Φ hde (hc t) w.2)
    obtain ⟨n, hn, hpow⟩ := exists_pow_eq_one_of_le h00.cond h00.unif N
    exact ⟨n, hn, fun x y e h1 h2 => hpow _ (hN x y e h1 h2)⟩
  choose nf hnf hpow using hloc
  haveI : ∀ t Φ, Finite (S.supp t Φ) := fun t Φ => ((S.sumOK_flat_fin_ex hL t Φ hde (hc t)).2.1).to_subtype
  haveI : Finite G.Datum := G.finite_datum (GlobalTheory.DiagLiftFix.isLattice_of_isFrame (hL.βY 0 (by omega)).choose_spec.1).fg
  letI : Fintype (Σ t : T, Σ Φ : G.Datum, (S.supp t Φ) × locPl G t) := Fintype.ofFinite _
  set n := ∏ i : (Σ t : T, Σ Φ : G.Datum, (S.supp t Φ) × locPl G t), nf i.1 i.2.1 i.2.2.1.1 i.2.2.2 with hn
  have hn0 : 0 < n := Finset.prod_pos fun i _ => hnf _ _ _ _
  obtain ⟨M, hM, hMr⟩ := exists_field_roots hn0
  refine ⟨M, hM, fun t Φ β hβ w x y e h1 h2 => hMr _ ?_⟩
  obtain ⟨c, hc'⟩ : nf t Φ β w ∣ n :=
    Finset.dvd_prod_of_mem (fun i : (Σ t : T, Σ Φ : G.Datum, (S.supp t Φ) × locPl G t) => nf i.1 i.2.1 i.2.2.1.1 i.2.2.2)
      (Finset.mem_univ ⟨t, Φ, ⟨β, hβ⟩, w⟩)
  rw [hc', pow_mul, hpow t Φ β w x y e h1 h2, one_pow]

end GlobalTheory.PhaseField

namespace GlobalTheory.BigTop.Fun

end GlobalTheory.BigTop.Fun
