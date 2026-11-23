import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.SmallRadAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.BallSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubiniHolds

open ValuativeRel Matrix Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc UpperTheory.Gal.Join
open GlobalTheory.SmGL hiding iwahori

namespace UpperTheory.Gal.InertialTypesAlt.L

section SlopeTestRemainingChoices

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem exists_rad {γ : ValueGroupWithZero k} (hγ : γ ≠ 0) :
    ∃ r : ValueGroupWithZero k, 0 < r ∧ r < 1 ∧ r < γ := by
  obtain ⟨x, hx0, hx1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  have hc0 : 0 < valuation k x := zero_lt_iff.2 ((valuation k).ne_zero_iff.2 hx0)
  have hm0 : 0 < min γ 1 := lt_min (zero_lt_iff.2 hγ) zero_lt_one
  have hlt : valuation k x * min γ 1 < min γ 1 := mul_lt_of_lt_one_left hm0 hx1
  exact ⟨valuation k x * min γ 1, mul_pos hc0 hm0, hlt.trans_le (min_le_right _ _), hlt.trans_le (min_le_left _ _)⟩

private theorem nhds_rad {x : k} {W : Set k} (hW : W ∈ 𝓝 x) :
    ∃ r : ValueGroupWithZero k, 0 < r ∧ r < 1 ∧ {y | valuation k (y - x) ≤ r} ⊆ W := by
  obtain ⟨γ, hγ, hs⟩ := (IsValuativeTopology.hasBasis_nhds' x).mem_iff.1 hW
  obtain ⟨r, h0, h1, h2⟩ := exists_rad hγ
  exact ⟨r, h0, h1, fun y hy => hs (lt_of_le_of_lt hy h2)⟩

private theorem fin_rad {ι : Type} [Finite ι] (R : ι → ValueGroupWithZero k) (h0 : ∀ i, 0 < R i) (h1 : ∀ i, R i < 1) :
    ∃ r : ValueGroupWithZero k, 0 < r ∧ r < 1 ∧ ∀ i, r ≤ R i := by
  obtain ⟨c, hc0, hc1, -⟩ := exists_rad (k := k) one_ne_zero
  obtain ⟨o, ho⟩ := Finite.exists_min (fun o : Option ι => o.elim c R)
  refine ⟨o.elim c R, ?_, ?_, fun i => ho (some i)⟩
  · cases o with
    | none => exact hc0
    | some i => exact h0 i
  · cases o with
    | none => exact hc1
    | some i => exact h1 i

private theorem pi_rad {ι : Type} [Finite ι] {X : ι → Type} [∀ i, TopologicalSpace (X i)] (x : ∀ i, X i)
    (P : ∀ i, ValueGroupWithZero k → Set (X i))
    (hP : ∀ i, ∀ W ∈ 𝓝 (x i), ∃ r : ValueGroupWithZero k, 0 < r ∧ r < 1 ∧ P i r ⊆ W)
    (hm : ∀ i r r', r' ≤ r → P i r' ⊆ P i r) {V : Set (∀ i, X i)} (hV : V ∈ 𝓝 x) :
    ∃ r : ValueGroupWithZero k, 0 < r ∧ r < 1 ∧ {y | ∀ i, y i ∈ P i r} ⊆ V := by
  rw [nhds_pi, Filter.mem_pi'] at hV
  obtain ⟨I, t, ht, hsub⟩ := hV
  choose R h0 h1 hR using fun i => hP i (t i) (ht i)
  obtain ⟨r, hr0, hr1, hr⟩ := fin_rad R h0 h1
  exact ⟨r, hr0, hr1, fun y hy => hsub fun i _ => hR i (hm i _ _ (hr i) (hy i))⟩

private theorem mat_rad {n : ℕ} {V : Set (Matrix (Fin n) (Fin n) k)} (hV : V ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) k)) :
    ∃ r : ValueGroupWithZero k, 0 < r ∧ r < 1 ∧
      {M : Matrix (Fin n) (Fin n) k | ∀ i j, valuation k (M i j - (1 : Matrix (Fin n) (Fin n) k) i j) ≤ r} ⊆ V := by
  refine pi_rad (X := fun _ : Fin n => Fin n → k) (fun i j => (1 : Matrix (Fin n) (Fin n) k) i j)
    (fun i r => {y | ∀ j, valuation k (y j - (1 : Matrix (Fin n) (Fin n) k) i j) ≤ r}) (fun i W hW => ?_)
    (fun i r r' h y hy j => (hy j).trans h) hV
  exact pi_rad (X := fun _ : Fin n => k) (fun j => (1 : Matrix (Fin n) (Fin n) k) i j)
    (fun j r => {y | valuation k (y - (1 : Matrix (Fin n) (Fin n) k) i j) ≤ r}) (fun j W hW => nhds_rad hW)
    (fun j r r' h y hy => (show valuation k (y - (1 : Matrix (Fin n) (Fin n) k) i j) ≤ r from le_trans hy h)) hW

private theorem unit_nhds {A : Type} [Monoid A] [TopologicalSpace A] {U : Set Aˣ} (hU : U ∈ 𝓝 (1 : Aˣ)) :
    ∃ V ∈ 𝓝 (1 : A), ∀ g : Aˣ, (g : A) ∈ V → ((g⁻¹ : Aˣ) : A) ∈ V → g ∈ U := by
  rw [Units.isEmbedding_embedProduct.isInducing.nhds_eq_comap, Filter.mem_comap] at hU
  obtain ⟨T, hT, hTU⟩ := hU
  obtain ⟨a, ha, b, hb, hab⟩ := mem_nhds_prod_iff.1 (by simpa using hT)
  refine ⟨a ∩ MulOpposite.op ⁻¹' b, Filter.inter_mem ha
    (MulOpposite.continuous_op.continuousAt.preimage_mem_nhds (by simpa using hb)), fun g h1 h2 => hTU ?_⟩
  exact hab ⟨h1.1, h2.2⟩

private theorem val_near {r : ValueGroupWithZero k} (h1 : r < 1) {x : k} (hx : valuation k (x - 1) ≤ r) :
    valuation k x = 1 := by
  have h := Valuation.map_one_add_of_lt (valuation k) (lt_of_le_of_lt hx h1)
  simpa using h

private theorem near_mul' {r : ValueGroupWithZero k} (h1 : r < 1) {x y : k} (hx : valuation k (x - 1) ≤ r)
    (hy : valuation k (y - 1) ≤ r) : valuation k (x * y - 1) ≤ r := by
  have e : x * y - 1 = x * (y - 1) + (x - 1) := by ring
  rw [e]
  refine Valuation.map_add_le _ ?_ hx
  rw [map_mul, val_near h1 hx, one_mul]
  exact hy

private theorem near_inv' {r : ValueGroupWithZero k} (h1 : r < 1) (x : kˣ) (hx : valuation k ((x : k) - 1) ≤ r) :
    valuation k (((x⁻¹ : kˣ) : k) - 1) ≤ r := by
  have hv := val_near h1 hx
  have e : ((x⁻¹ : kˣ) : k) - 1 = -((x : k) - 1) * ((x⁻¹ : kˣ) : k) := by
    rw [neg_mul, sub_mul, Units.mul_inv]
    ring
  have hv' : valuation k ((x⁻¹ : kˣ) : k) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hv, inv_one]
  rw [e, map_mul, hv', mul_one, Valuation.map_neg]
  exact hx

private theorem t2 : T2Space k := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  letI : (Valued.v (R := k)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  infer_instance

private theorem compact_units (r : ValueGroupWithZero k) (h1 : r < 1) :
    IsCompact {x : kˣ | valuation k ((x : k) - 1) ≤ r} := by
  haveI : T2Space k := t2
  have hC : IsCompact {x : k | valuation k (x - 1) ≤ r} := by
    have h := (IsNonarchimedeanLocalField.isCompact_closedBall k r).image (f := fun x => x + 1) (by fun_prop)
    convert h using 1
    ext x
    constructor
    · intro hx
      exact ⟨x - 1, hx, sub_add_cancel _ _⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  have h := (Units.isClosedEmbedding_embedProduct (α := k)).isCompact_preimage
    (hC.prod (hC.image MulOpposite.continuous_op))
  convert h using 1
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod,
    MulOpposite.op_injective.mem_set_image]
  exact ⟨fun hx => ⟨hx, near_inv' h1 x hx⟩, fun hx => hx.1⟩

end SlopeTestRemainingChoices

theorem smallRad :
    UpperTheory.Gal.InertialTypesAlt.L.SmallRad := by
  intro k _ _ _ _ n
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro U hU
    obtain ⟨V, hV, hVU⟩ := unit_nhds hU
    obtain ⟨r, h0, h1, hr⟩ := mat_rad hV
    obtain ⟨K, hK, -, -⟩ := UpperTheory.ConvolutionTheory.Loc.ballSub k n r h0 h1
    refine ⟨r, h0, h1, fun r' hr' g hg => ?_⟩
    have hg' : g ∈ ball n r := fun i j => (hg i j).trans hr'
    have hgK : g ∈ K := by
      have : g ∈ (K : Set (GL (Fin n) k)) := hK ▸ hg'
      exact this
    have hinv : g⁻¹ ∈ ball n r := by
      have : g⁻¹ ∈ (K : Set (GL (Fin n) k)) := K.inv_mem hgK
      exact hK ▸ this
    exact hVU g (hr hg') (hr hinv)
  · intro W hW
    obtain ⟨r, h0, h1, hr⟩ := pi_rad (X := fun _ : Fin n => kˣ) (1 : Fin n → kˣ)
      (fun _ r => {u : kˣ | valuation k ((u : k) - 1) ≤ r}) (fun i Y hY => by
        obtain ⟨V, hV, hVU⟩ := unit_nhds hY
        obtain ⟨r, h0, h1, hr⟩ := nhds_rad hV
        exact ⟨r, h0, h1, fun u hu => hVU u (hr hu) (hr (near_inv' h1 u hu))⟩)
      (fun _ r r' h y hy => (show valuation k ((y : k) - 1) ≤ r from le_trans hy h)) hW
    exact ⟨r, h0, h1, fun r' hr' u hu => hr fun i => (hu i).trans hr'⟩
  · intro r h1
    refine ⟨{ carrier := {u | Near r u}
              one_mem' := fun i => by simp
              mul_mem' := fun {a b} ha hb i => by
                simpa using near_mul' h1 (ha i) (hb i)
              inv_mem' := fun {a} ha i => by
                simpa using near_inv' h1 (a i) (ha i) }, fun u => Iff.rfl, ?_⟩
    have h := isCompact_univ_pi (fun _ : Fin n => compact_units r h1)
    convert h using 1
    ext u
    simp [Near, Set.mem_pi]
  · exact (continuous_leviEmb k (points (Fin n))).comp (continuous_leviTorus k (Fin n))
  · obtain ⟨x, hx0, hx1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
    refine ⟨fun i => Units.mk0 x hx0 ^ (n - (i : ℕ)), fun i j hij => ?_⟩
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0, map_pow]
    have hij' : (i : ℕ) < j := hij
    exact pow_lt_pow_right_of_lt_one₀ (zero_lt_iff.2 ((valuation k).ne_zero_iff.2 hx0)) hx1 (by omega)
  · intro t₀ t h₀ ht i j hij
    have a := h₀ i j hij
    have b := ht i j hij
    have c : 0 < valuation k (t j : k) := zero_lt_iff.2 (by simp)
    simp only [Pi.mul_apply, Units.val_mul, map_mul]
    calc valuation k (t₀ i : k) * valuation k (t i : k) ≤ valuation k (t₀ i : k) * valuation k (t j : k) :=
          mul_le_mul_right b _
      _ < valuation k (t₀ j : k) * valuation k (t j : k) := mul_lt_mul_of_pos_right a c

end UpperTheory.Gal.InertialTypesAlt.L
