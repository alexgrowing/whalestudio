import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField

noncomputable section

open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (cosetInd mainDatum Lifts InDual)
open GlobalTheory.FinPl.Comm (fpair)

namespace GlobalTheory.FinPl.CosetPairing

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n]

theorem exists_lifts [DecidableEq n] (P : Pair k n) : ∃ F, Lifts P.lat F P.red := by
  obtain ⟨g, hg⟩ := Module.projective_lifting_property (Algebra.linearMap 𝒪[k] 𝓀[k]) P.fn residue_surjective
  let b := Module.Free.chooseBasis 𝒪[k] P.lat
  let G : (n → k) →ₗ[k] k := (b.extendOfIsLattice k).constr k fun i => (g (b i) : k)
  have h1 : (G.restrictScalars 𝒪[k]) ∘ₗ P.lat.subtype = (Algebra.linearMap 𝒪[k] k) ∘ₗ g := b.ext fun i => by
    have := (b.extendOfIsLattice k).constr_basis k (fun i => (g (b i) : k)) i
    rw [Module.Basis.extendOfIsLattice_apply] at this
    exact this
  refine ⟨fun i => G (Pi.single i 1), fun y => ⟨g y, ?_, LinearMap.congr_fun hg y⟩⟩
  have h2 : G y = (g y : k) := LinearMap.congr_fun h1 y
  rw [← h2, LinearMap.pi_apply_eq_sum_univ G]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul, mul_comm]
  congr 2
  ext j
  simp [Pi.single_apply, eq_comm]

theorem inDual_of_lifts (q : Unif k) {L : Submodule 𝒪[k] (n → k)} {f : Module.Dual 𝓀[k] (Red L)} {F F' : n → k}
    (hF : Lifts L F f) (hF' : Lifts L F' f) : InDual L (q.inv • F - q.inv • F') := fun y hy => by
  obtain ⟨s, hs, hr⟩ := hF ⟨y, hy⟩
  obtain ⟨t, ht, hr'⟩ := hF' ⟨y, hy⟩
  obtain ⟨u, hu⟩ := q.mem_max_iff.1 ((residue_eq_zero_iff (s - t)).1 (by rw [map_sub, hr, hr', sub_self]))
  have hu' : (s : k) - t = q.1 * u := by exact_mod_cast congrArg Subtype.val hu
  rw [← smul_sub, smul_dotProduct, sub_dotProduct, ← hs, ← ht, hu', smul_eq_mul, Unif.inv,
    inv_mul_cancel_left₀ q.ne_zero]
  exact u.2

theorem cosetInd_add (q : Unif k) {L : Submodule 𝒪[k] (n → k)} {f : Module.Dual 𝓀[k] (Red L)} {F : n → k}
    (hF : Lifts L F f) (η : n → k) : cosetInd q L f (η + q.inv • F) = dualInd L η := by
  classical
  refine if_congr ⟨?_, fun h => ⟨F, hF, by simpa using h⟩⟩ rfl rfl
  rintro ⟨F', hF', h⟩ y hy
  have := sub_mem (h y hy) (inDual_of_lifts q hF hF' y hy)
  rwa [← sub_dotProduct, show η + q.inv • F - q.inv • F' - (q.inv • F - q.inv • F') = η by abel] at this

variable {χ : AddChar k Circle} (hχ : HasConductor χ 1) {e : k}

include hχ in

theorem char_dual (he : e = 1 ∨ e = -1) {L : Submodule 𝒪[k] (n → k)} {η y : n → k} (hη : InDual L η) (hy : y ∈ L) :
    χ (e * (η ⬝ᵥ y)) = 1 := by
  rcases he with rfl | rfl
  · simpa using apply_int_eq_one hχ ⟨_, hη y hy⟩
  · simpa using apply_int_eq_one hχ (-⟨_, hη y hy⟩)

theorem char_coset (q : Unif k) {ε : 𝓀[k]ˣ} (he : (e = 1 ∧ ε = 1) ∨ (e = -1 ∧ ε = -1)) {P : Pair k n} {F η y : n → k}
    (hF : Lifts P.lat F P.red) (hη : InDual P.lat η) (hy : y ∈ P.lat) :
    (χ (e * ((η + q.inv • F) ⬝ᵥ y)) : ℂ) = resChar χ hχ q (ε * P.ev y) := by
  obtain ⟨s, hs, hr⟩ := hF ⟨y, hy⟩
  have hr' : P.ev y = residue 𝒪[k] s := ((P.hasVal_fn ⟨y, hy⟩).ev_eq).trans hr.symm
  rw [add_dotProduct, mul_add, AddChar.map_add_eq_mul, char_dual hχ (he.imp And.left And.left) hη hy, one_mul,
    smul_dotProduct, ← hs, hr']
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [resChar_residue]
  · have := resChar_residue hχ q (-s)
    simpa using this.symm

theorem exists_char_ne (q : Unif k) {ε : 𝓀[k]ˣ} (hε : ε = 1 ∨ ε = -1) {Q Q'' : Pair k n} (h : Q''.lat = Q.lat)
    (hne : Q'' ≠ ε • Q) : ∃ y ∈ Q.lat, resChar χ hχ q (-Q.ev y + ε * Q''.ev y) ≠ 1 := by
  have hi : ε⁻¹ = ε := by rcases hε with rfl | rfl <;> simp
  obtain ⟨y, hy, hc⟩ : ∃ y ∈ Q.lat, -Q.ev y + ε * Q''.ev y ≠ 0 := by
    by_contra hc
    push Not at hc
    refine hne (Pair.ext fun x a => ?_)
    rw [Pair.dia_hasVal, hi]
    constructor
    · intro hx
      have hx' := h ▸ hx.mem
      have := hc x hx'
      rw [hx.ev_eq, neg_add_eq_zero] at this
      exact this ▸ Pair.hasVal_ev hx'
    · intro hx
      have := hc x hx.mem
      rw [hx.ev_eq, neg_add_eq_zero, Units.mul_right_inj] at this
      exact this ▸ Pair.hasVal_ev (h ▸ hx.mem)
  obtain ⟨a, ha⟩ := AddChar.ne_one_iff.1 (resChar_ne_one hχ q)
  obtain ⟨s, hs⟩ := residue_surjective (R := 𝒪[k]) (a * (-Q.ev y + ε * Q''.ev y)⁻¹)
  refine ⟨s • y, Q.lat.smul_mem s hy, ?_⟩
  rw [((Pair.hasVal_ev hy).smul s).ev_eq, ((Pair.hasVal_ev (h ▸ hy : y ∈ Q''.lat)).smul s).ev_eq]
  convert ha using 2
  rw [← inv_mul_cancel_right₀ hc a, ← hs]
  ring

theorem fpair_charInd_cosetInd (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (χ : AddChar k Circle)
    (hχ : HasConductor χ 1) (e : k) (ε : 𝓀[k]ˣ) (he : (e = 1 ∧ ε = 1) ∨ (e = -1 ∧ ε = -1)) (μ : Measure (n → k))
    [μ.IsAddHaarMeasure] (Q Q'' : Pair k n) (h : Q''.lat = Q.lat) :
    (Q'' = ε • Q → fpair χ e μ (charInd (resChar χ hχ q) Q) (cosetInd q Q''.lat Q''.red) =
      fpair χ e μ (vecInd Q.lat) (dualInd Q.lat)) ∧
    (Q'' ≠ ε • Q → fpair χ e μ (charInd (resChar χ hχ q) Q) (cosetInd q Q''.lat Q''.red) = 0) := by
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  haveI := secondCountable k
  obtain ⟨F, hF⟩ := exists_lifts Q''
  have hε : ε = 1 ∨ ε = -1 := he.imp And.right And.right
  have key : fpair χ e μ (charInd (resChar χ hχ q) Q) (cosetInd q Q''.lat Q''.red) =
      ∫ η, (∫ y, vecInd Q.lat y * resChar χ hχ q (-Q.ev y + ε * Q''.ev y) ∂μ) * dualInd Q.lat η ∂μ := by
    unfold fpair
    rw [← integral_add_right_eq_self _ (q.inv • F)]
    congr 1
    funext η
    rw [cosetInd_add q hF, h]
    by_cases hη : InDual Q.lat η
    swap
    · rw [dualInd, if_neg hη, mul_zero, mul_zero]
    congr 2
    funext y
    by_cases hy : y ∈ Q.lat
    · rw [char_coset hχ q he hF (h ▸ hη) (h ▸ hy), charInd, AddChar.map_add_eq_mul]
      ring
    · rw [charInd, vecInd, if_neg hy, mul_zero, zero_mul, zero_mul]
  rw [key]
  constructor
  · rintro rfl
    unfold fpair
    congr 1
    funext η
    by_cases hη : InDual Q.lat η
    swap
    · rw [dualInd, if_neg hη, mul_zero, mul_zero]
    congr 2
    funext y
    by_cases hy : y ∈ Q.lat
    · have h1 : Q.ev y = (ε⁻¹ : 𝓀[k]ˣ) * (ε • Q).ev y := (Pair.dia_hasVal.1 (Pair.hasVal_ev (P := ε • Q) hy)).ev_eq
      have hi : ε⁻¹ = ε := by rcases hε with rfl | rfl <;> simp
      rw [hi] at h1
      rw [char_dual hχ (he.imp And.left And.left) hη hy, ← h1, neg_add_cancel]
      simp
    · rw [vecInd, if_neg hy, zero_mul, zero_mul]
  · intro hne
    obtain ⟨y₀, hy₀, hc⟩ := exists_char_ne hχ q hε h hne
    have e1 := integral_add_right_eq_self (μ := μ)
      (fun y => vecInd Q.lat y * resChar χ hχ q (-Q.ev y + ε * Q''.ev y)) y₀
    have e2 : ∀ y, vecInd Q.lat (y + y₀) * resChar χ hχ q (-Q.ev (y + y₀) + ε * Q''.ev (y + y₀)) =
        resChar χ hχ q (-Q.ev y₀ + ε * Q''.ev y₀) * (vecInd Q.lat y * resChar χ hχ q (-Q.ev y + ε * Q''.ev y)) := fun y => by
      by_cases hy : y ∈ Q.lat
      · rw [vecInd, vecInd, if_pos hy, if_pos (add_mem hy hy₀), one_mul, one_mul, ← AddChar.map_add_eq_mul,
          ((Pair.hasVal_ev hy).add (Pair.hasVal_ev hy₀)).ev_eq,
          ((Pair.hasVal_ev (h ▸ hy : y ∈ Q''.lat)).add (Pair.hasVal_ev (h ▸ hy₀ : y₀ ∈ Q''.lat))).ev_eq]
        congr 1
        ring
      · rw [vecInd, vecInd, if_neg hy, if_neg fun h' => hy ((Q.lat.add_mem_iff_left hy₀).1 h')]
        simp
    simp only [e2] at e1
    rw [integral_const_mul] at e1
    have h0 : ∫ y, vecInd Q.lat y * resChar χ hχ q (-Q.ev y + ε * Q''.ev y) ∂μ = 0 := by
      by_contra h0
      exact hc ((mul_eq_right₀ h0).1 e1)
    simp [h0]

end GlobalTheory.FinPl.CosetPairing

end
