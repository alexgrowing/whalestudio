import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.ModuleStructureOfCommuting
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryPointProperties
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevelUR2OrdPt

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance 2000] UpperTheory.V.W.coefLocal
set_option synthInstance.maxHeartbeats 200000
private theorem hecke_poly_coeff_formula {A : Type} [CommRing A] (n q : ℕ) (a : ℕ → A) (j : ℕ) (hj : j ≤ n) :
    (heckePol n q a).coeff (n - j) = (-1) ^ j * (q : A) ^ (j * (j - 1) / 2) * a j := by
  rw [mul_assoc, ← JEx.heckePol_coeff n q a j hj, ← mul_assoc, ← mul_pow]
  simp
private theorem hecke_poly_coeff_zero {A : Type} [CommRing A] (n q : ℕ) (a : ℕ → A) (i : ℕ) (hi : n < i) :
    (heckePol n q a).coeff i = 0 := by
  rw [Hi.heckePol, finset_sum_coeff]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [coeff_C_mul_X_pow, if_neg]
  omega
private theorem norm_lt_one_of_residue_zero {l : ℕ} [Fact l.Prime] (c : Coef l) (b : c.O) (hb : residue c.O b = 0) :
    ‖algebraMap c.O (Qbar l) b‖ < 1 := by
  have e : algebraMap c.O (Qbar l) b = (b : PadicAlgCl l) := rfl
  rw [e]
  rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff] at hb
  rcases eq_or_ne b 0 with rfl | h0
  · simp
  have h := UpperTheory.V.Base.normO l c.O b h0
  have hl : ((l : ℝ)⁻¹) < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hv : (IsDiscreteValuationRing.addVal c.O b).toNat ≠ 0 := by
    rw [Ne, ENat.toNat_eq_zero, IsDiscreteValuationRing.addVal_eq_zero_iff, IsDiscreteValuationRing.addVal_eq_top_iff]
    exact fun h => h.elim hb h0
  have h1 := pow_lt_one₀ (by positivity) hl hv
  rw [← h] at h1
  by_contra hn
  exact absurd h1 (not_lt.2 (one_le_pow₀ (not_lt.1 hn)))
private theorem hecke_poly_coeff_congruence_iff {l : ℕ} [Fact l.Prime] (c : Coef l) (n q : ℕ) (hq : ‖(q : Qbar l)‖ = 1) (a : ℕ → Qbar l) (b : ℕ → c.O) :
    (∀ j ≤ n, ‖a j - algebraMap c.O (Qbar l) (b j)‖ < 1) ↔
      ∀ (i : ℕ) (b' : c.O), residue c.O b' = (heckePol n q fun j => residue c.O (b j)).coeff i →
        ‖(heckePol n q a).coeff i - algebraMap c.O (Qbar l) b'‖ < 1 := by
  have e : ∀ j ≤ n, ‖(heckePol n q a).coeff (n - j) - algebraMap c.O (Qbar l) ((heckePol n q b).coeff (n - j))‖ =
      ‖a j - algebraMap c.O (Qbar l) (b j)‖ := fun j hj => by
    rw [← coeff_map, JEx.heckePol_map, hecke_poly_coeff_formula _ _ _ _ hj, hecke_poly_coeff_formula _ _ _ _ hj, ← mul_sub]
    simp [hq]
  rw [← JEx.heckePol_map]
  constructor
  · intro h i b' hb
    rw [coeff_map] at hb
    have h1 : ‖algebraMap c.O (Qbar l) ((heckePol n q b).coeff i) - algebraMap c.O (Qbar l) b'‖ < 1 := by
      rw [← map_sub]
      exact norm_lt_one_of_residue_zero c _ (by rw [map_sub, hb, sub_self])
    have h2 : ‖(heckePol n q a).coeff i - algebraMap c.O (Qbar l) ((heckePol n q b).coeff i)‖ < 1 := by
      rcases le_or_gt i n with hi | hi
      · have := e (n - i) (Nat.sub_le _ _)
        rw [Nat.sub_sub_self hi] at this
        rw [this]
        exact h _ (Nat.sub_le _ _)
      · rw [hecke_poly_coeff_zero _ _ _ _ hi, hecke_poly_coeff_zero _ _ _ _ hi]
        simp
    rw [← sub_add_sub_cancel _ (algebraMap c.O (Qbar l) ((heckePol n q b).coeff i))]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h2 h1)
  · intro h j hj
    rw [← e j hj]
    exact h _ _ (coeff_map _ _).symm
private theorem hecke_part_frobenius {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) (hH : H.Ax) (ι : Qbar l ≃+* ℂ) {lam : Wt L l n} {d : ℕ}
    {ξ : GV n H.Sl →* GL (Fin d) ℂ} (Y : H.PartAltAlt ι lam ξ) (a : H.Op → c.O) (w : H.Wp) (B : ValuationSubring Ω) (σ : G L Ω)
    (hB : IsPlaceOver B w.1) (hσ : IsFrob B (normV w.1) σ) :
    (∀ k : Fin n, ‖ι.symm (Y.a w (k + 1)) - algebraMap c.O (Qbar l) (a (.inl (w, k)))‖ < 1) ↔
      ∀ (i : ℕ) (b : c.O), residue c.O b = (heckePol n (normV w.1) fun j =>
          if h : 0 < j ∧ j - 1 < n then residue c.O (a (.inl (w, ⟨j - 1, h.2⟩))) else 1).coeff i →
        ‖(Y.r (H.prj σ⁻¹) : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i - algebraMap c.O (Qbar l) b‖ < 1 := by
  have hq : ‖((normV w.1 : ℕ) : Qbar l)‖ = 1 := by
    have h0 := (cycZ L Ω l σ).isUnit
    rw [cycZ_of_isFrob (hH.Wp_away w.1 w.2) hB hσ, PadicInt.isUnit_iff] at h0
    rw [← map_natCast (algebraMap ℚ_[l] (Qbar l)), norm_algebraMap', ← h0, PadicInt.norm_def, PadicInt.coe_natCast]
  have e : (Y.r (H.prj σ⁻¹) : Matrix (Fin n) (Fin n) (Qbar l)).charpoly = heckePol n (normV w.1) fun j => ι.symm (Y.a w j) := by
    refine Polynomial.map_injective ι.toRingHom ι.injective ?_
    rw [Y.frob w B σ hB hσ, JEx.heckePol_map]
    simp
  have e2 : (fun j => if h : 0 < j ∧ j - 1 < n then residue c.O (a (.inl (w, ⟨j - 1, h.2⟩))) else 1) =
      fun j => residue c.O (if h : 0 < j ∧ j - 1 < n then a (.inl (w, ⟨j - 1, h.2⟩)) else 1) := by
    funext j
    split_ifs
    · rfl
    · exact (map_one _).symm
  rw [e, e2, ← hecke_poly_coeff_congruence_iff c n _ hq]
  constructor
  · intro h j hj
    rcases j with _ | j
    · rw [Y.a_zero, dif_neg (by omega)]
      simp
    · rw [dif_pos ⟨Nat.succ_pos _, hj⟩]
      exact h ⟨j, hj⟩
  · intro h k
    have := h (k + 1) k.2
    rw [dif_pos ⟨Nat.succ_pos _, k.2⟩] at this
    exact this
theorem UpperTheory.V.Hi.levelUR2H3Abs_alt :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    IsDomain A → ∀ (ι : Qbar l ≃+* ℂ) (P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop), H.AutomorphicHeckeSet ι P → ∀ lam0 ∈ H.admitted, H.DenseWt θ lam0 → ∀ (a : H.Op → c.O) (K : H.Lev) (φ : H.Gq → (ResidueField c.O)[X]), IsLocallyConstant φ → (∀ (w : H.Wp) (B : ValuationSubring Ω) (σ : G L Ω), IsPlaceOver B w.1 → IsFrob B (normV w.1) σ → φ (H.prj σ⁻¹) = heckePol n (normV w.1) fun j => if h : 0 < j ∧ j - 1 < n then residue c.O (a (.inl (w, ⟨j - 1, h.2⟩))) else 1) → ∀ (ι' : Type) (j : ι' → H.Op), (∀ x, Sum.inr x ∈ Set.range j) → Dense {g : H.Gq | ∃ w : H.Wp, (∀ k, Sum.inl (w, k) ∈ Set.range j) ∧ ∃ (B : ValuationSubring Ω) (σ : G L Ω), IsPlaceOver B w.1 ∧ IsFrob B (normV w.1) σ ∧ g = H.prj σ⁻¹} → locPart (H.X.Ord (H.τA A) θ (H.lev K)) (fun i => H.op A (j i)) (fun i => algebraMap c.O A (a (j i))) = H.MK θ a K := by
  intro _ L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ hA ι P hP lam0 _ hd a K φ hφ hφ2 ι' j hj hD
  obtain ⟨hC, hfi, hfr, -⟩ := hiComm L Ω l n c H hH A θ hθ K
  haveI : Fact (CommOn (H.X.Ord (H.τA A) θ (H.lev K)) (H.op A)) := ⟨hC⟩
  obtain ⟨x, hx⟩ : ∃ x : A →ₐ[c.O] Qbar l, H.Good θ x lam0 := by
    by_contra h
    exact one_ne_zero (hd 1 fun x hx => absurd ⟨x, hx⟩ h)
  obtain ⟨d, ξ, c0, sp, hsp⟩ := spec L Ω l n c H hH A θ hθ ι x lam0 hx.2.1
  refine levelUR2LocSub l c A _ _ ι' _ (H.op A) j a x fun z hz h => ?_
  obtain ⟨Y, hY⟩ := _root_.UpperTheory.V.Hi.levelUR2OrdPt_alt L Ω l n c H hH A θ hθ ι P hP x lam0 d ξ c0 sp hsp hx.1 K z hz
  have hall := levelUR2GalRes l c H.Gq n Y.r Y.cont φ hφ _ hD (by
    rintro _ ⟨w, hw, B, σ, hB, hσ, rfl⟩
    rw [hφ2 w B σ hB hσ]
    refine (hecke_part_frobenius H hH ι Y a w B σ hB hσ).1 fun k => ?_
    obtain ⟨i, hi⟩ := hw k
    rw [hY, ι.symm_apply_apply, ← hi]
    exact h i)
  rintro (⟨w, k⟩ | y)
  · obtain ⟨B, hB⟩ := exists_isPlaceOver Ω w.1
    obtain ⟨σ, hσ⟩ := exists_isFrob hB
    have := (hecke_part_frobenius H hH ι Y a w B σ hB hσ).2 (by
      rw [← hφ2 w B σ hB hσ]
      exact hall _) k
    rwa [hY, ι.symm_apply_apply] at this
  · obtain ⟨i, hi⟩ := hj y
    rw [← hi]
    exact h i
end
