import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.MatchSmulAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubiniHolds

noncomputable section

open MeasureTheory NumberField IsDedekindDomain ValuativeRel Matrix GroundTheory.Global GroundTheory.Global.SemiLocal
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc
open GlobalTheory.SmGL hiding iwahori
open PositivityTheory.Rg.Tf.Geo (incFin galFin)
open UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.L

section Alg

variable {k E : Type} [Field k] [Field E] [Algebra k E] {n : ℕ}

private theorem iter_eq (σ : E ≃ₐ[k] E) (j : ℕ) (x : E) : (σ : E ≃+* E)^[j] x = (σ ^ j) x := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ', AlgEquiv.mul_apply]
    rfl

private theorem norm_prod [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E)
    (hg : ∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) (x : E) :
    algebraMap k E (Algebra.norm k x) = ∏ j ∈ Finset.range (Module.finrank k E), (σ : E ≃+* E)^[j] x := by
  rw [Algebra.norm_eq_prod_automorphisms]
  have hN : Module.finrank k E = orderOf σ := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, ← IsGalois.card_aut_eq_finrank]
  rw [hN]
  symm
  refine Finset.prod_bij (fun j _ => σ ^ j) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro a ha b hb hab
    exact pow_injOn_Iio_orderOf (by simpa using ha) (by simpa using hb) hab
  · intro τ _
    have hτ : τ ∈ Submonoid.powers σ := mem_powers_iff_mem_zpowers.mpr (hg τ)
    rw [mem_powers_iff_mem_range_orderOf, Finset.mem_image] at hτ
    obtain ⟨m, hm, h⟩ := hτ
    exact ⟨m, hm, h⟩
  · intro j _
    exact iter_eq σ j x

private theorem map_diag {F : Type} [Field F] (f : E →+* F) (u : Fin n → Eˣ) :
    Matrix.GeneralLinearGroup.map f (diagT E (Fin n) u) = diagT F (Fin n) fun i => Units.map (f : E →* F) (u i) := by
  ext i j
  simp [GlobalTheory.SmGL.val_diagT, Matrix.diagonal_apply]
  split_ifs <;> simp

private theorem nrm_diag (σ : E ≃+* E) (q : ℕ) (u : Fin n → Eˣ) :
    (UpperTheory.ConvolutionTheory.Loc.nrm σ q (diagT E (Fin n) u)).val = Matrix.diagonal fun i => ∏ j ∈ Finset.range q, σ^[j] (u i) := by
  induction q with
  | zero =>
    ext i j
    simp [UpperTheory.ConvolutionTheory.Loc.nrm, Matrix.one_apply, Matrix.diagonal_apply]
  | succ q ih =>
    rw [UpperTheory.ConvolutionTheory.Loc.nrm_succ, Units.val_mul, ih]
    have h2 : (((⇑(sg σ))^[q] (diagT E (Fin n) u)) : Matrix (Fin n) (Fin n) E)
        = Matrix.diagonal fun i => σ^[q] (u i) := by
      ext i j
      rw [sg_iterate_apply, GlobalTheory.SmGL.val_diagT, Matrix.diagonal_apply, Matrix.diagonal_apply]
      split_ifs <;> simp [iterate_map_zero]
    rw [h2, Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    rw [Finset.prod_range_succ]

private theorem nrmT_mul (a b : Fin n → Eˣ) : nrmT k (a * b) = nrmT k a * nrmT k b := by
  funext i
  ext
  simp [nrmT, map_mul]

private theorem nrmT_div (a b : Fin n → Eˣ) : nrmT k (a / b) = nrmT k a / nrmT k b := by
  funext i
  ext
  simp [nrmT, map_div₀]

private theorem nrmT_sg [FiniteDimensional k E] (σ : E ≃ₐ[k] E) (u : Fin n → Eˣ) :
    nrmT k (sgT (σ : E ≃+* E) u) = nrmT k u := by
  funext i
  ext
  simp only [nrmT, sgT, Units.coe_map, MonoidHom.coe_coe]
  exact Algebra.norm_eq_of_algEquiv σ _

private theorem h90 [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E)
    (hg : ∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) (z : Fin n → Eˣ) (hz : nrmT k z = 1) :
    ∃ w : Fin n → Eˣ, sgT (σ : E ≃+* E) w / w = z := by
  haveI : IsCyclic (E ≃ₐ[k] E) := ⟨⟨σ, hg⟩⟩
  have hzi : ∀ i, Algebra.norm k ((z i : Eˣ) : E) = 1 := by
    intro i
    have h1 := congrArg Units.val (congrFun hz i)
    simpa [nrmT] using h1
  choose y hy using fun i => groupCohomology.exists_div_of_norm_eq_one (K := k) (g := σ) hg (hzi i)
  refine ⟨fun i => (y i)⁻¹, ?_⟩
  funext i
  apply Units.ext
  rw [← hy i]
  simp [sgT]
  ring

end Alg

section Top

variable {k E : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] {n : ℕ}

variable (k E) in
private theorem emb_alg : Topology.IsEmbedding (algebraMap k E) := by
  have key : ∀ a b : k, valuation E (algebraMap k E a) < valuation E (algebraMap k E b) ↔
      valuation k a < valuation k b := by
    intro a b
    rw [lt_iff_not_ge, lt_iff_not_ge, ← (valuation E).vle_iff_le, ← (valuation k).vle_iff_le,
      ValuativeExtension.vle_iff_vle]
  obtain ⟨π, hπ0, hπ1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  have hfπ : valuation E (algebraMap k E π) < 1 := by
    have h1 := (key π 1).mpr (by rwa [map_one])
    rwa [map_one, map_one] at h1
  refine ⟨?_, (algebraMap k E).injective⟩
  rw [IsTopologicalAddGroup.isInducing_iff_nhds_zero]
  ext s
  rw [Filter.mem_comap, IsValuativeTopology.mem_nhds_iff]
  constructor
  · rintro ⟨δ, hδ⟩
    obtain ⟨N, hN⟩ := exists_pow_lt₀ hπ1 δ
    have hb0 : valuation E (algebraMap k E (π ^ N)) ≠ 0 := by
      rw [map_pow, map_pow]
      exact pow_ne_zero _ ((Valuation.ne_zero_iff _).mpr ((map_ne_zero _).mpr hπ0))
    refine ⟨{z | valuation E z < valuation E (algebraMap k E (π ^ N))}, ?_, ?_⟩
    · rw [IsValuativeTopology.mem_nhds_iff]
      refine ⟨Units.mk0 _ hb0, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      show valuation E (0 + z) < _
      rw [zero_add]
      exact hz
    · intro a ha
      apply hδ
      refine ⟨a, ?_, zero_add a⟩
      have h2 := (key a (π ^ N)).mp ha
      rw [map_pow] at h2
      exact lt_trans h2 hN
  · rintro ⟨t, ht, hts⟩
    rw [IsValuativeTopology.mem_nhds_iff] at ht
    obtain ⟨γ, hγ⟩ := ht
    obtain ⟨N, hN⟩ := exists_pow_lt₀ hfπ γ
    have hb0 : valuation k (π ^ N) ≠ 0 := by
      rw [map_pow]
      exact pow_ne_zero _ ((Valuation.ne_zero_iff _).mpr hπ0)
    refine ⟨Units.mk0 _ hb0, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    apply hts
    show algebraMap k E (0 + a) ∈ t
    rw [zero_add]
    apply hγ
    refine ⟨algebraMap k E a, ?_, zero_add _⟩
    have h2 := (key a (π ^ N)).mpr ha
    rw [map_pow, map_pow] at h2
    exact lt_trans h2 hN

private theorem cont_sg {σ : E ≃+* E} (hσ : Isom σ) : Continuous σ := by
  rw [continuous_iff_continuousAt]
  intro x s hs
  rw [IsValuativeTopology.mem_nhds_iff] at hs
  obtain ⟨γ, hγ⟩ := hs
  rw [Filter.mem_map, IsValuativeTopology.mem_nhds_iff]
  refine ⟨γ, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  show σ (x + z) ∈ s
  rw [map_add]
  refine hγ ⟨σ z, ?_, rfl⟩
  show valuation E (σ z) < _
  rw [hσ z]
  exact hz

private theorem cont_norm [IsGalois k E] (σ : E ≃ₐ[k] E) (hg : ∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ)
    (hσ : Isom (σ : E ≃+* E)) : Continuous (Algebra.norm k : E → k) := by
  rw [(emb_alg k E).continuous_iff]
  have h : (algebraMap k E ∘ (Algebra.norm k : E → k)) =
      fun x => ∏ j ∈ Finset.range (Module.finrank k E), (σ : E ≃+* E)^[j] x := by
    funext x
    exact norm_prod σ hg x
  rw [h]
  exact continuous_finset_prod _ fun j _ => (cont_sg hσ).iterate j

private theorem near_compact {r : ValueGroupWithZero E} (hr : r < 1) :
    IsCompact {u : Eˣ | valuation E ((u : E) - 1) ≤ r} := by
  have hB : IsCompact ((fun x : E => x + 1) '' {x | valuation E x ≤ r}) :=
    (IsNonarchimedeanLocalField.isCompact_closedBall E r).image (continuous_add_right 1)
  rw [Units.isEmbedding_val₀.isCompact_iff]
  convert hB using 1
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨(u : E) - 1, hu, sub_add_cancel _ _⟩
  · rintro ⟨y, hy, rfl⟩
    have hne : y + 1 ≠ 0 := by
      intro h0
      have h3 : y = -1 := eq_neg_of_add_eq_zero_left h0
      rw [h3, Valuation.map_neg, map_one] at hy
      exact (not_le.mpr hr) hy
    exact ⟨Units.mk0 _ hne, by simpa using hy, rfl⟩

end Top

end UpperTheory.Gal.InertialTypesAlt.L

open UpperTheory.Gal.InertialTypesAlt.L in
theorem UpperTheory.Gal.InertialTypesAlt.L.normDiag :
    UpperTheory.Gal.InertialTypesAlt.L.NormDiag := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ hg n
  obtain ⟨hcyc, -, hbr⟩ := bridge k E σ
  obtain ⟨-, hnrm, -, -, -⟩ := hbr n
  have hiso : Isom (σ : E ≃+* E) := hcyc.isom
  have hq : 0 < Module.finrank k E := hcyc.pos
  have hit : ∀ (j : ℕ) (x : E), valuation E ((σ : E ≃+* E)^[j] x) = valuation E x := by
    intro j
    induction j with
    | zero => intro x; rfl
    | succ j ih => intro x; rw [Function.iterate_succ_apply', hiso, ih]
  have hvn : ∀ x : E, valuation E (algebraMap k E (Algebra.norm k x)) = valuation E x ^ Module.finrank k E := by
    intro x
    rw [norm_prod σ hg x, map_prod]
    simp only [hit, Finset.prod_const, Finset.card_range]
  have hstrict : ∀ d : Fin n → Eˣ, Strict d → Strict (nrmT k d) := by
    intro d hd i j hij
    rw [← (ValuativeExtension.mapValueGroupWithZero_strictMono (A := k) (B := E)).lt_iff_lt,
      ValuativeExtension.mapValueGroupWithZero_valuation, ValuativeExtension.mapValueGroupWithZero_valuation]
    show valuation E (algebraMap k E (Algebra.norm k (d i : E))) < valuation E (algebraMap k E (Algebra.norm k (d j : E)))
    rw [hvn, hvn]
    exact pow_lt_pow_left₀ (hd i j hij) zero_le' hq.ne'
  have hdiag : ∀ d : Fin n → Eˣ, normGL σ (diagT E (Fin n) d) = incl (diagT k (Fin n) (nrmT k d)) := by
    intro d
    rw [← hnrm]
    apply Units.ext
    rw [nrm_diag]
    show _ = ((diagT k (Fin n) (nrmT k d)).val).map (algebraMap k E)
    rw [val_diagT, Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    exact (norm_prod σ hg (d i)).symm
  have hreg : ∀ d : Fin n → Eˣ, Strict d → IsRegSemisimple (diagT k (Fin n) (nrmT k d)) := by
    intro d hd
    show ((diagT k (Fin n) (nrmT k d)).val).charpoly.Separable
    rw [val_diagT, Matrix.charpoly_diagonal, Polynomial.separable_prod_X_sub_C_iff]
    intro i j h
    simp only at h
    by_contra hne
    rcases lt_or_gt_of_ne hne with h1 | h1
    · have h2 := hstrict d hd i j h1
      rw [h] at h2
      exact lt_irrefl _ h2
    · have h2 := hstrict d hd j i h1
      rw [h] at h2
      exact lt_irrefl _ h2
  have hsg_inv : ∀ w : Fin n → Eˣ, sgT σ.toRingEquiv w⁻¹ = (sgT σ.toRingEquiv w)⁻¹ := by
    intro w
    funext i
    simp [sgT]
  have hpart2 : ∀ (r : ValueGroupWithZero E) (d t : Fin n → Eˣ),
      (∃ u, Near r (d * sgT σ.toRingEquiv u / u / t)) ↔ nrmT k d ∈ nrmSet k r t := by
    intro r d t
    constructor
    · rintro ⟨u, hu⟩
      refine ⟨d * sgT σ.toRingEquiv u / u / t, hu, ?_⟩
      have e1 : t * (d * sgT σ.toRingEquiv u / u / t) = d * sgT σ.toRingEquiv u / u := by
        rw [mul_comm]
        exact div_mul_cancel _ _
      rw [e1, nrmT_div, nrmT_mul, nrmT_sg σ u, mul_div_assoc, div_self', mul_one]
    · rintro ⟨s, hs, hx⟩
      have h1 : nrmT k (d / (t * s)) = 1 := by rw [nrmT_div, ← hx, div_self']
      obtain ⟨w, hw⟩ := h90 σ hg _ h1
      refine ⟨w⁻¹, ?_⟩
      have e3 : sgT σ.toRingEquiv w = d / (t * s) * w := by
        rw [← hw, div_mul_cancel]
      have e2 : d * sgT σ.toRingEquiv w⁻¹ / w⁻¹ / t = s := by
        rw [hsg_inv, e3]
        funext i
        apply Units.ext
        simp only [Pi.div_apply, Pi.mul_apply, Pi.inv_apply, Units.val_div_eq_div_val, Units.val_mul,
          Units.val_inv_eq_inv_val]
        have := (w i).ne_zero
        have := (t i).ne_zero
        have := (s i).ne_zero
        have := (d i).ne_zero
        field_simp
      rw [e2]
      exact hs
  refine ⟨fun d => ⟨hdiag d, hstrict d, hreg d⟩, hpart2, fun r hr t ht => ⟨?_, ?_⟩⟩
  · rintro x ⟨u, hu, rfl⟩
    apply hstrict
    intro i j hij
    have hu1 : ∀ i, valuation E (u i : E) = 1 := by
      intro i
      have h := Valuation.map_one_add_of_lt (valuation E) (lt_of_le_of_lt (hu i) hr)
      rwa [add_sub_cancel] at h
    show valuation E ((t i : E) * u i) < valuation E ((t j : E) * u j)
    rw [map_mul, map_mul, hu1, hu1, mul_one, mul_one]
    exact ht i j hij
  · have hS : nrmSet k r t = (fun u => nrmT k (t * u)) ''
        Set.pi Set.univ (fun _ => {u : Eˣ | valuation E ((u : E) - 1) ≤ r}) := by
      ext x
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨u, fun i _ => hu i, rfl⟩
      · rintro ⟨u, hu, rfl⟩
        exact ⟨u, fun i => hu i (Set.mem_univ i), rfl⟩
    rw [hS]
    apply IsCompact.image (isCompact_univ_pi fun _ => near_compact hr)
    have hc : Continuous (Units.map (Algebra.norm k : E →* k)) := Continuous.units_map _ (cont_norm σ hg hiso)
    exact continuous_pi fun i => hc.comp ((continuous_apply i).comp (continuous_const.mul continuous_id))
