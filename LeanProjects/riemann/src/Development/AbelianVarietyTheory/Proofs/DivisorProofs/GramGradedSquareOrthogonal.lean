import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LnStepFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameCombinationCoeffUnique
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.HeightParts
open GlobalTheory.GradedNorm GlobalTheory.LieHt
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LieSmooth

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieSmooth.BlockGr

open Matrix
open scoped ComplexOrder

variable {m r : ℕ}

theorem quad_sub (M : Matrix (Fin m) (Fin m) ℂ) {p : Fin r → Fin m} (hp : Function.Injective p) (v : Fin m → ℂ)
    (hv : ∀ a ∉ Set.range p, v a = 0) :
    star v ⬝ᵥ M *ᵥ v = star (v ∘ p) ⬝ᵥ M.submatrix p p *ᵥ (v ∘ p) := by
  simp only [dotProduct, mulVec, Function.comp_apply, submatrix_apply, Pi.star_apply]
  symm
  refine Fintype.sum_of_injective p hp _ _ (fun a ha => by simp [hv a ha]) fun i => ?_
  congr 1
  exact Fintype.sum_of_injective p hp _ _ (fun a ha => by simp [hv a ha]) fun j => rfl

theorem quad_sub_le {M : Matrix (Fin m) (Fin m) ℂ} (hM : M.PosSemidef) {p : Fin r → Fin m} (hp : Function.Injective p)
    (ho : ∀ a b, a ∈ Set.range p → b ∉ Set.range p → M a b = 0 ∧ M b a = 0) (v : Fin m → ℂ) :
    (star (v ∘ p) ⬝ᵥ M.submatrix p p *ᵥ (v ∘ p)).re ≤ (star v ⬝ᵥ M *ᵥ v).re := by
  classical
  let S : Fin m → ℂ := fun a => if a ∈ Set.range p then v a else 0
  let R : Fin m → ℂ := fun a => if a ∈ Set.range p then 0 else v a
  have S1 : ∀ a ∈ Set.range p, S a = v a := fun a h => if_pos h
  have S0 : ∀ a ∉ Set.range p, S a = 0 := fun a h => if_neg h
  have R1 : ∀ a ∉ Set.range p, R a = v a := fun a h => if_neg h
  have R0 : ∀ a ∈ Set.range p, R a = 0 := fun a h => if_pos h
  have hv : v = S + R := funext fun a => by
    by_cases h : a ∈ Set.range p
    · rw [Pi.add_apply, S1 a h, R0 a h, add_zero]
    · rw [Pi.add_apply, S0 a h, R1 a h, zero_add]
  have hSp : S ∘ p = v ∘ p := funext fun i => S1 _ ⟨i, rfl⟩
  have c1 : star S ⬝ᵥ M *ᵥ R = 0 := by
    simp only [dotProduct, mulVec]
    refine Finset.sum_eq_zero fun a _ => ?_
    by_cases ha : a ∈ Set.range p
    · refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun b _ => ?_)
      by_cases hb : b ∈ Set.range p
      · rw [R0 b hb, mul_zero]
      · rw [(ho a b ha hb).1, zero_mul]
    · rw [Pi.star_apply, S0 a ha, star_zero, zero_mul]
  have c2 : star R ⬝ᵥ M *ᵥ S = 0 := by
    simp only [dotProduct, mulVec]
    refine Finset.sum_eq_zero fun a _ => ?_
    by_cases ha : a ∈ Set.range p
    · rw [Pi.star_apply, R0 a ha, star_zero, zero_mul]
    · refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun b _ => ?_)
      by_cases hb : b ∈ Set.range p
      · rw [(ho b a hb ha).2, zero_mul]
      · rw [S0 b hb, mul_zero]
  have e : star v ⬝ᵥ M *ᵥ v = star S ⬝ᵥ M *ᵥ S + star R ⬝ᵥ M *ᵥ R := by
    rw [hv, star_add, mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, c1, c2]
    ring
  rw [e, ← hSp, ← quad_sub M hp S S0, Complex.add_re]
  have := hM.re_dotProduct_nonneg R
  simp only [RCLike.re_to_complex] at this
  linarith

end GlobalTheory.LieSmooth.BlockGr

namespace GlobalTheory.LieSmooth.BlockGr

open Matrix
open scoped ComplexOrder

variable {m r : ℕ}

theorem grSq_block {M : Matrix (Fin m) (Fin m) ℂ} (hM : M.PosDef) {p : Fin r → Fin m} (hp : Function.Injective p)
    (ho : ∀ a b, a ∈ Set.range p → b ∉ Set.range p → M a b = 0 ∧ M b a = 0) {k : Fin m} {i : Fin r} (hk : p i = k)
    (h1 : ∀ i', i < i' → k < p i') (h2 : ∀ i', k < p i' → i < i') :
    grSq M k = grSq (M.submatrix p p) i := by
  have hS : (M.submatrix p p).PosDef := hM.submatrix hp
  refine le_antisymm ?_ ?_
  · obtain ⟨⟨w, hw1, hw2, hw⟩, -⟩ := isLeast_grSq hS i
    rw [hw]
    refine (isLeast_grSq hM k).2 ⟨Function.extend p w 0, ?_, fun j hj => ?_, ?_⟩
    · rw [← hk, hp.extend_apply, hw1]
    · by_cases h : j ∈ Set.range p
      · obtain ⟨i', rfl⟩ := h
        rw [hp.extend_apply, hw2 _ (h2 _ hj)]
      · rw [Function.extend_apply' _ _ _ fun ⟨a, ha⟩ => h ⟨a, ha⟩, Pi.zero_apply]
    · rw [quad_sub M hp _ fun a ha => by
        rw [Function.extend_apply' _ _ _ fun ⟨b, hb⟩ => ha ⟨b, hb⟩, Pi.zero_apply]]
      have e : Function.extend p w 0 ∘ p = w := funext fun a => hp.extend_apply _ _ _
      rw [e]
  · obtain ⟨⟨v, hv1, hv2, hv⟩, -⟩ := isLeast_grSq hM k
    rw [hv]
    refine le_trans ((isLeast_grSq hS i).2 ⟨v ∘ p, ?_, fun i' hi' => hv2 _ (h1 _ hi'), rfl⟩) (quad_sub_le hM.posSemidef hp ho v)
    rw [Function.comp_apply, hk, hv1]

end GlobalTheory.LieSmooth.BlockGr

namespace GlobalTheory.LieSmooth

open Matrix
open scoped ComplexOrder

theorem grSq_allFr_tauFr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {K : Type} [Field K] [NumberField K] {n : ℕ} (e : Fin n ≃ Letter Dw) (h : HermFam K (Fin n → K))
    (σ : K →+* ℂ)
    (horth : ∀ z z' : Letter Dw, z.1 ≠ z'.1 → h.form σ (tauFr K e z.1 z.2) (tauFr K e z'.1 z'.2) = 0) :
    ∀ k : Fin (letters Dw).length,
      grSq (h.gram σ (allFr K e)) k = grSq (h.gram σ (tauFr K e ((letters Dw).get k).1)) ((letters Dw).get k).2 := by
  classical
  let eq := Equiv.ofBijective _ (GlobalTheory.Proof.frame_combination_coeff_unique.get_bijective Dw)
  have hpw := List.pairwise_iff_get.1 (GlobalTheory.Proof.frame_combination_coeff_unique.pairwise_letters Dw)
  have hli : LinearIndependent K (allFr K e) := by
    have : allFr K e = (Pi.basisFun K (Fin n)) ∘ (fun j => e.symm ((letters Dw).get j)) :=
      funext fun j => (Pi.basisFun_apply K (Fin n) _).symm
    rw [this]
    exact (Pi.basisFun K (Fin n)).linearIndependent.comp _ (e.symm.injective.comp (GlobalTheory.Proof.frame_combination_coeff_unique.get_bijective Dw).1)
  have hM : (h.gram σ (allFr K e)).PosDef := h.posDef σ _ _ hli
  have hz : ∀ a b, ((letters Dw).get a).1 ≠ ((letters Dw).get b).1 → h.gram σ (allFr K e) a b = 0 :=
    fun a b hab => horth _ _ hab
  suffices key : ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) (k : Fin (letters Dw).length), (letters Dw).get k = ⟨τ, i⟩ →
      grSq (h.gram σ (allFr K e)) k = grSq (h.gram σ (tauFr K e τ)) i from fun k => key _ _ k rfl
  intro τ i k hk
  let p : Fin (Dw.mult τ) → Fin (letters Dw).length := fun i' => eq.symm ⟨τ, i'⟩
  have hg : ∀ i', (letters Dw).get (p i') = ⟨τ, i'⟩ := fun i' => eq.apply_symm_apply _
  have hp : Function.Injective p := fun a b hab => by
    have := congrArg (fun j => (letters Dw).get j) hab
    simp only [hg] at this
    exact eq_of_heq (Sigma.mk.inj this).2
  have hpk : p i = k := eq.symm_apply_eq.2 hk.symm
  have hsub : h.gram σ (tauFr K e τ) = (h.gram σ (allFr K e)).submatrix p p := by
    ext a b
    simp only [HermFam.gram, submatrix_apply, of_apply, allFr, tauFr, hg]
  have hout : ∀ b, b ∉ Set.range p → ((letters Dw).get b).1 ≠ τ := by
    intro b hb hτ
    rcases hgb : (letters Dw).get b with ⟨τ', j⟩
    rw [hgb] at hτ
    subst hτ
    exact hb ⟨j, eq.symm_apply_eq.2 hgb.symm⟩
  have ho : ∀ a b, a ∈ Set.range p → b ∉ Set.range p →
      h.gram σ (allFr K e) a b = 0 ∧ h.gram σ (allFr K e) b a = 0 := by
    rintro _ b ⟨a, rfl⟩ hb
    have h1 : ((letters Dw).get (p a)).1 ≠ ((letters Dw).get b).1 := by rw [hg]; exact (hout b hb).symm
    exact ⟨hz _ _ h1, hz _ _ h1.symm⟩
  rw [hsub]
  refine BlockGr.grSq_block hM hp ho hpk (fun i' hi' => ?_) (fun i' hi' => ?_)
  · by_contra hle
    have hlt : p i' < k := lt_of_le_of_ne (not_lt.1 hle) fun h' => hi'.ne (hp (hpk.trans h'.symm))
    have := hpw _ _ hlt
    rw [hg, hk] at this
    exact absurd (this rfl) (not_lt.2 hi'.le)
  · have := hpw _ _ hi'
    rw [hg, hk] at this
    exact this rfl

end GlobalTheory.LieSmooth

example : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {K : Type} [Field K] [NumberField K] {n : ℕ} (e : Fin n ≃ Letter Dw) (h : HermFam K (Fin n → K)) (σ : K →+* ℂ), (∀ z z' : Letter Dw, z.1 ≠ z'.1 → h.form σ (tauFr K e z.1 z.2) (tauFr K e z'.1 z'.2) = 0) → ∀ k : Fin (letters Dw).length, grSq (h.gram σ (allFr K e)) k = grSq (h.gram σ (tauFr K e ((letters Dw).get k).1)) ((letters Dw).get k).2 := @GlobalTheory.LieSmooth.grSq_allFr_tauFr

end
