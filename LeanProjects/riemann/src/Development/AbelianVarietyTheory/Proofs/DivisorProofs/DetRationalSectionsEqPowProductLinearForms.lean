import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankDeepestFiltrationStepEqRationalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianMultiplicationFlatColumnsEvalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingMapDetFiltrationWithSymbolsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonomialCountsDegreeAndWeightedSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymbolsOfEvaluatedColumnsHermitianMultSystemStatement
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSShort

theorem det_symbolBlock {E ι κ : Type} [Field E] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (w : κ → E) (e : ℕ) (r : κ → κ → E) :
    (Matrix.of fun (i i' : ι × κ) => if i.1 = i'.1 then w i.2 ^ e * r i'.2 i.2 else 0).det =
      (∏ p, w p) ^ (e * Fintype.card ι) *
        (Matrix.of fun (i i' : ι × κ) => if i.1 = i'.1 then r i'.2 i.2 else 0).det := by
  have h : (Matrix.of fun (i i' : ι × κ) => if i.1 = i'.1 then w i.2 ^ e * r i'.2 i.2 else 0) =
      Matrix.diagonal (fun i : ι × κ => w i.2 ^ e) *
        Matrix.of fun (i i' : ι × κ) => if i.1 = i'.1 then r i'.2 i.2 else 0 := by
    ext i i'
    simp only [Matrix.of_apply, Matrix.diagonal_mul]
    split_ifs <;> simp
  rw [h, Matrix.det_mul, Matrix.det_diagonal, Fintype.prod_prod_type]
  simp only [Finset.prod_pow, Finset.prod_const, Finset.card_univ]
  rw [← pow_mul, mul_comm (Fintype.card ι)]

theorem det_rational_eq_pow : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (E A' : Type) [Field E] [Algebra F E] [AddCommGroup A'] [Module E A'] (s : Fin S.D → Fin S.N → F) (δ : ℕ) (Φ : S.Flat E A' (fun i k => algebraMap F E (s i k)) δ) (d : ℕ) (b : Module.Basis (Fin d) F (S.V S.T)) (c : Fin d → A →ₗ[F] F), S.IsCo b c → ∀ (col : Fin d → S.Col) (m : Fin δ → S.V 0) (ix : (Σ a : Fin (S.T - S.D), MonoDeg (Fin S.D) a) × Fin δ ↪ Fin d), S.Shape δ col m ix → S.deepRank s ≤ (Finset.univ.filter fun k => (col k).j = S.D).card → ∃ γ : E, ∀ l : Fin S.N → E, aeval (join (fun i k => algebraMap F E (s i k)) l) (S.det c col) = γ * (∏ p, ∑ k, l k * Φ.y p k) ^ S.expo := by
  intro F A _ _ _ _ _ _ S hS E A' _ _ _ _ s δ Φ d b c hc col m ix hsh hrank
  classical
  obtain ⟨c', -, hev⟩ := GlobalTheory.T.hermitianMultiplicationFlat_columns_eval F A S hS E A' (fun i k => algebraMap F E (s i k)) δ Φ d b c hc
  have hsym := GlobalTheory.T.symbols_of_evaluated_columns_hermitianMultSystem F A S hS E A' (fun i k => algebraMap F E (s i k)) δ Φ d col m ix hsh
  obtain ⟨hfd, hfr, -⟩ := GlobalTheory.T.finrank_deepestFiltrationStep_eq_rational F A S hS E A' s δ Φ
  obtain ⟨hcard, -, -⟩ := GlobalTheory.T.monomial_counts_degree_and_weighted_sum S.D S.T hS.one_le hS.le_T
  let v : (Fin S.N → E) → Fin d → A' := fun l k =>
    word Φ.mul (fun q j => join (fun i k => algebraMap F E (s i k)) l ((col k).β q, j)) (Φ.ι (col k).x)
  let ω : A' [⋀^Fin d]→ₗ[E] E := (Matrix.detRowAlternating).compLinearMap (LinearMap.pi c')
  have hdet : ∀ l, aeval (join (fun i k => algebraMap F E (s i k)) l) (S.det c col) = ω (v l) := by
    intro l
    rw [Sys.det, AlgHom.map_det, AlternatingMap.compLinearMap_apply]
    change _ = Matrix.det (fun k i => c' i (v l k))
    rw [← Matrix.det_transpose]
    congr 1
    ext i k
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.transpose_apply]
    exact (hev (col i) (join (fun i k => algebraMap F E (s i k)) l)).2 k

  let ix' : (Σ a : Fin (S.T - S.D), MonoDeg (Fin S.D) a × Fin δ) ↪ Fin d :=
    (Equiv.sigmaProdDistrib (fun a : Fin (S.T - S.D) => MonoDeg (Fin S.D) a) (Fin δ)).symm.toEmbedding.trans ix
  have hix' : ∀ q, ix' q = ix (⟨q.1, q.2.1⟩, q.2.2) := fun q => rfl

  have hind : ∀ l k, k ∉ Set.range ix → v l k = v 0 k := by
    intro l k hk
    have hL : (fun q j => join (fun i k => algebraMap F E (s i k)) l ((col k).β q, j)) = (fun q j => join (fun i k => algebraMap F E (s i k)) 0 ((col k).β q, j)) := by
      rcases hsh.rest k hk with ⟨-, hβ⟩ | hj
      · funext q j
        obtain ⟨i, hi⟩ := Fin.exists_castSucc_eq.mpr (hβ q)
        rw [← hi]
        simp [join]
      · have ht : (col k).t = 0 := by have := (col k).add; omega
        funext q
        exact absurd q.isLt (by omega)
    show word Φ.mul _ _ = word Φ.mul _ _
    rw [hL]

  have hzq : ∀ q : (Σ a : Fin (S.T - S.D), MonoDeg (Fin S.D) a × Fin δ),
      ∃ x : A', ∃ hx : x ∈ Φ.U q.1, Φ.sym q.1 ⟨x, hx⟩ = Pi.single q.2 1 := by
    rintro ⟨a, α, p⟩
    obtain ⟨k₀, hk₀⟩ := Function.ne_iff.mp (Φ.y_ne p)
    have hk₀' : Φ.y p k₀ ≠ 0 := hk₀
    have ht : Φ.y p k₀ ^ (S.T - (a : ℕ)) ≠ 0 := pow_ne_zero _ hk₀'
    have hmem : (Pi.single p (Φ.y p k₀ ^ (S.T - (a : ℕ)))⁻¹ : Fin δ → E) ∈
        (Submodule.span E (Φ.ι '' S.V 0)).map Φ.res := by
      rw [Φ.onto]; exact Submodule.mem_top
    obtain ⟨m₀, hm₀, hres⟩ := hmem
    obtain ⟨h, hh⟩ := Φ.mono a a.2 α (fun _ => Pi.single k₀ 1) m₀ hm₀
    refine ⟨_, h, ?_⟩
    funext i
    obtain ⟨α', p'⟩ := i
    rw [hh, hres]
    by_cases hp : p' = p
    · rw [hp]
      by_cases hα : α' = α
      · rw [hα]
        simp [Finset.prod_const, Pi.single_apply, ht]
      · have hα' : α'.1 ≠ α.1 := fun e => hα (Subtype.ext e)
        simp [hα', hα]
    · simp [hp, Pi.single_apply]
  choose zq hzqU hzqS using hzq
  let z : Fin d → A' := Function.extend ix' zq (v 0)
  have hz_ix : ∀ q, z (ix' q) = zq q := fun q => ix'.injective.extend_apply zq (v 0) q
  have hz : ∀ q, z (ix' q) ∈ Φ.U q.1 := fun q => (hz_ix q).symm ▸ hzqU q
  have hzs : ∀ q, Φ.sym q.1 ⟨z (ix' q), hz q⟩ = Pi.single q.2 1 := by
    intro q
    have e : (⟨z (ix' q), hz q⟩ : Φ.U q.1) = ⟨zq q, hzqU q⟩ := Subtype.ext (hz_ix q)
    rw [e]; exact hzqS q
  have hzout : ∀ l k, k ∉ Set.range ix' → z k = v l k := by
    intro l k hk
    show Function.extend ix' zq (v 0) k = _
    rw [Function.extend_apply' _ _ _ hk]
    have hk' : k ∉ Set.range ix := by
      rintro ⟨q, rfl⟩; exact hk ⟨(Equiv.sigmaProdDistrib _ _) q, rfl⟩
    exact (hind l k hk').symm

  let J : Finset (Fin d) := Finset.univ.filter fun k => (col k).j = S.D
  have hnotix : ∀ k, (col k).j = S.D → k ∉ Set.range ix := by
    rintro k hk ⟨q, rfl⟩
    have := hsh.x_j q
    have := hS.one_le
    omega
  have hv : ∀ l q, v l (ix' q) ∈ Φ.U q.1 := fun l q => ((hsym l).1 q.1 q.2.1 q.2.2).fst
  have hJ : ∀ l, ∀ k ∈ J, k ∉ Set.range ix' ∧ v l k ∈ Φ.U (S.T - S.D) := by
    intro l k hk
    have hk' : (col k).j = S.D := (Finset.mem_filter.mp hk).2
    refine ⟨?_, (hsym l).2 k (hnotix k hk') hk'⟩
    rintro ⟨q, hq⟩
    exact hnotix k hk' ⟨_, (hix' q).symm.trans hq⟩
  haveI := hfd
  have hrank' : Module.finrank E (Φ.U (S.T - S.D)) ≤ J.card := hfr ▸ hrank
  let B : ∀ a : Fin (S.T - S.D), Matrix (MonoDeg (Fin S.D) a × Fin δ) (MonoDeg (Fin S.D) a × Fin δ) E :=
    fun a => Matrix.of fun i i' => if i.1 = i'.1 then Φ.res (Φ.ι (m i'.2)) i.2 else 0
  have hexp : ∑ a : Fin (S.T - S.D), (S.T - (a : ℕ)) * Fintype.card (MonoDeg (Fin S.D) a) = S.expo := by
    rw [Sys.expo, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Nat.card_eq_fintype_card, hcard, mul_comm]
  refine ⟨(∏ a, (B a).det) * ω z, fun l => ?_⟩
  rw [hdet]
  have key := GlobalTheory.T.alternatingMap_det_filtration_with_symbols E A' (S.T - S.D) d (fun a => MonoDeg (Fin S.D) a × Fin δ) Φ.U (fun a => Φ.sym a)
    Φ.le (fun a x => Φ.ker a a.2 x) ix' J (v l) (hv l) (hJ l) hrank' z hz hzs (hzout l) ω
  rw [key]
  have hblock : ∀ a : Fin (S.T - S.D),
      (Matrix.of fun i i' : MonoDeg (Fin S.D) a × Fin δ => Φ.sym a ⟨v l (ix' ⟨a, i'⟩), hv l ⟨a, i'⟩⟩ i).det =
        (∏ p, ∑ k, l k * Φ.y p k) ^ ((S.T - (a : ℕ)) * Fintype.card (MonoDeg (Fin S.D) a)) * (B a).det := by
    intro a
    have hM : (Matrix.of fun i i' : MonoDeg (Fin S.D) a × Fin δ => Φ.sym a ⟨v l (ix' ⟨a, i'⟩), hv l ⟨a, i'⟩⟩ i) =
        Matrix.of fun (i i' : MonoDeg (Fin S.D) a × Fin δ) =>
          if i.1 = i'.1 then (∑ k, l k * Φ.y i.2 k) ^ (S.T - (a : ℕ)) * Φ.res (Φ.ι (m i'.2)) i.2 else 0 := by
      ext i i'
      refine (((hsym l).1 a i'.1 i'.2).snd i.1 i.2).trans ?_
      simp only [Matrix.of_apply, Subtype.val_inj]
    rw [hM, det_symbolBlock (ι := MonoDeg (Fin S.D) a) (fun p => ∑ k, l k * Φ.y p k) (S.T - (a : ℕ))
      (fun p' p => Φ.res (Φ.ι (m p')) p)]
  simp only [hblock]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hexp]
  ring

end GlobalTheory.HSShort
