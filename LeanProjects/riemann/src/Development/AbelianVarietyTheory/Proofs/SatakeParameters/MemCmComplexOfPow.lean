import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.Bridge
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassPresBasic
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HasRatBasisOfAct

open Formalism.IndefR.Bridge Formalism.L2.DIV Formalism.DivisionValues Formalism.L2.Col NumberField MeasureTheory Polynomial

noncomputable section

namespace GlobalTheory.PresRat

def conjAlg : algebraicClosure ℚ ℂ →+* algebraicClosure ℚ ℂ :=
  ((starRingEnd ℂ).comp (algebraicClosure ℚ ℂ).val.toRingHom).codRestrict (algebraicClosure ℚ ℂ) fun x => by
    have hx : IsAlgebraic ℚ (x : ℂ) := mem_algebraicClosure_iff.1 x.2
    exact mem_algebraicClosure_iff.2 (hx.algHom (starRingEnd ℂ).toRatAlgHom)

def cmComplex : Subfield ℂ :=
  (⨅ τ : algebraicClosure ℚ ℂ →+* ℂ, RingHom.eqLocusField (τ.comp conjAlg) ((starRingEnd ℂ).comp τ)).map
    (algebraicClosure ℚ ℂ).val.toRingHom

theorem mem_cmComplex {z : ℂ} : z ∈ cmComplex ↔ ∃ x : algebraicClosure ℚ ℂ, (x : ℂ) = z ∧
    ∀ τ : algebraicClosure ℚ ℂ →+* ℂ, τ (conjAlg x) = starRingEnd ℂ (τ x) := by
  unfold cmComplex
  rw [Subfield.mem_map]
  refine exists_congr fun x => ?_
  rw [Subfield.mem_iInf, and_comm]
  rfl

theorem conj_eq_inv_of_pow {z : ℂ} {n : ℕ} (hn : 0 < n) (hz : z ^ n = 1) : starRingEnd ℂ z = z⁻¹ :=
  (Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one hz hn.ne')).symm

theorem mem_cmComplex_of_pow {z : ℂ} {n : ℕ} (hn : 0 < n) (hz : z ^ n = 1) : z ∈ cmComplex := by
  have ha : IsAlgebraic ℚ z := IsAlgebraic.of_pow hn (by rw [hz]; exact isAlgebraic_one)
  refine mem_cmComplex.2 ⟨⟨z, mem_algebraicClosure_iff.2 ha⟩, rfl, fun τ => ?_⟩
  set x : algebraicClosure ℚ ℂ := ⟨z, mem_algebraicClosure_iff.2 ha⟩
  have hx : x ^ n = 1 := Subtype.ext hz
  have h1 : conjAlg x = x⁻¹ := Subtype.ext (conj_eq_inv_of_pow hn hz)
  rw [h1, map_inv₀, conj_eq_inv_of_pow hn (by rw [← map_pow, hx, map_one])]

theorem mem_cmComplex_iff {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ)
    (hσ : ∀ a : K, σ (star a) = starRingEnd ℂ (σ a)) (a : K) : σ a ∈ cmComplex ↔ a ∈ cmMax K := by
  let s : K →+* algebraicClosure ℚ ℂ := σ.codRestrict (algebraicClosure ℚ ℂ) fun x =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom σ.toRatAlgHom)
  have hs : conjAlg (s a) = s (star a) := Subtype.ext (hσ a).symm
  rw [mem_cmComplex]
  constructor
  · rintro ⟨x, hx, h⟩ φ
    have hx' : x = s a := Subtype.ext hx
    let _ : Algebra K (algebraicClosure ℚ ℂ) := s.toAlgebra
    have : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := by
      convert algebraicClosure.isAlgebraic ℚ ℂ
      · rfl
      · exact Subsingleton.elim _ _
    have : Algebra.IsAlgebraic K (algebraicClosure ℚ ℂ) :=
      Algebra.IsAlgebraic.tower_top (K := ℚ) K
    have h1 := h (ComplexEmbedding.lift (algebraicClosure ℚ ℂ) φ)
    rw [hx', hs] at h1
    have e : ∀ b, ComplexEmbedding.lift (algebraicClosure ℚ ℂ) φ (s b) = φ b := fun b =>
      ComplexEmbedding.lift_algebraMap_apply _ φ b
    rw [e, e] at h1
    exact h1
  · intro h
    exact ⟨s a, rfl, fun τ => by rw [hs]; exact h (τ.comp s)⟩

variable {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K]
  [NumberField K] [StarRing K] {ι : Γ →* G} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W}
  {J : Subgroup G} {χ : J →* ℂˣ} (P : ClassPres ι S σ ρ J χ)

theorem act_mem (hσ : ∀ a : K, σ (star a) = starRingEnd ℂ (σ a)) (hχ : ∀ k, ∃ n : ℕ, 0 < n ∧ χ k ^ n = 1)
    (hρ : ∀ γ j, ∃ c : S.ιV → K, (∀ i, c i ∈ cmMax K) ∧ ρ γ (P.coef (S.bV j)) = ∑ i, σ (c i) • P.coef (S.bV i))
    (k : J) (γ : Γ) (x : S.V) (hx : ∀ i, S.bV.repr x i ∈ cmMax K) (i : S.ιV) :
    (PresBasic.bW P).repr ((χ k : ℂ) • ρ γ (P.coef x)) i ∈ cmComplex := by
  obtain ⟨n, hn, hk⟩ := hχ k
  have h1 : (χ k : ℂ) ∈ cmComplex :=
    mem_cmComplex_of_pow hn (by rw [← Units.val_pow_eq_pow_val, hk, Units.val_one])
  have h2 : P.coef x = ∑ j, σ (S.bV.repr x j) • P.coef (S.bV j) := by
    conv_lhs => rw [← S.bV.sum_repr x]
    rw [map_sum]
    simp only [map_smulₛₗ]
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, h2]
  refine cmComplex.mul_mem h1 ?_
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  refine cmComplex.sum_mem fun j _ => cmComplex.mul_mem ((mem_cmComplex_iff σ hσ _).2 (hx j)) ?_
  obtain ⟨c, hc, e⟩ := hρ γ j
  rw [e]
  simp only [← PresBasic.bW_apply]
  rw [Module.Basis.repr_sum_self]
  exact (mem_cmComplex_iff σ hσ _).2 (hc i)

end GlobalTheory.PresRat

namespace GlobalTheory

theorem classPres_dcOp_rat : ∀ {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K] [NumberField K] [StarRing K] (ι : Γ →* G) (S : CSD K) (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (P : ClassPres ι S σ ρ J χ) (A : Finset G) (T : Module.End K S.Forms), (∀ a : K, σ (star a) = starRingEnd ℂ (σ a)) → (∀ k, ∃ n : ℕ, 0 < n ∧ χ k ^ n = 1) → (∀ γ j, ∃ c : S.ιV → K, (∀ i, c i ∈ cmMax K) ∧ ρ γ (P.coef (S.bV j)) = ∑ i, σ (c i) • P.coef (S.bV i)) → (∀ f : S.Forms, P.ext ((T f : S.Forms) : S.Cl → S.V) = dcOp A (P.ext (f : S.Cl → S.V))) → S.HasRatBasis ∧ ∀ a b, LinearMap.toMatrix S.basis S.basis T a b ∈ cmMax K := by
  intro G Γ W K _ _ _ _ _ _ _ ι S σ ρ J χ P A T hσ hχ hρ hT
  have hb : S.HasRatBasis := by
    refine (forms_rat S).1 fun c γ i j => ?_
    rw [← PresRat.mem_cmComplex_iff σ hσ, ← PresBasic.repr_coef P, P.coef_act]
    refine PresRat.act_mem P hσ hχ hρ _ _ _ (fun l => ?_) i
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  refine ⟨hb, (forms_rat S).2 T hb fun f hf c i => ?_⟩
  rw [← PresRat.mem_cmComplex_iff σ hσ, ← PresBasic.repr_coef P, ← PresBasic.ext_y P, hT]
  unfold dcOp
  rw [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  exact PresRat.cmComplex.sum_mem fun a _ => PresRat.act_mem P hσ hχ hρ _ _ _ (hf _) i

end GlobalTheory
