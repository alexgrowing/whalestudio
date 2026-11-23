import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ShCocOn
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLocallyConstantCycMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaTorsionQuotientConjInvariantDecomposition
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemCoc
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormCompatibleSystemFrobeniusEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoboundaryOfPadicAlgClUniformApproxStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegralCoboundaryWildInertiaAwayFromLStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaCocycleEqZeroOfVanishWildTameGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FgInertiaCocyclesModCoboundariesCoefRingStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory.InertCoh

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem norm_le_one_of_isIntegral (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  have hc : ∀ c : ℤ_[l], ‖algebraMap ℤ_[l] (PadicAlgCl l) c‖ ≤ 1 := by
    intro c
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap']
    exact c.2
  by_contra h
  push_neg at h
  obtain ⟨p, hm, hp⟩ := hx
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hm.coeff_natDegree, map_one, one_mul] at hp
  have h1 : x ^ p.natDegree = - ∑ i ∈ Finset.range p.natDegree, algebraMap ℤ_[l] (PadicAlgCl l) (p.coeff i) * x ^ i :=
    eq_neg_of_add_eq_zero_right hp
  rcases Nat.eq_zero_or_pos p.natDegree with hz | hz
  · rw [hz] at h1; simp at h1
  have h2 : ‖∑ i ∈ Finset.range p.natDegree, algebraMap ℤ_[l] (PadicAlgCl l) (p.coeff i) * x ^ i‖ ≤
      ‖x‖ ^ (p.natDegree - 1) := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    rw [norm_mul, norm_pow]
    have hi' := Finset.mem_range.1 hi
    calc _ ≤ 1 * ‖x‖ ^ i := mul_le_mul_of_nonneg_right (hc _) (by positivity)
      _ ≤ _ := by rw [one_mul]; exact pow_le_pow_right₀ h.le (by omega)
  rw [← norm_neg, ← h1, norm_pow] at h2
  exact absurd h2 (not_le.2 (pow_lt_pow_right₀ h (by omega)))

theorem norm_le_one_of_mem_O (c : Coef l) {x : Qbar l} (hx : x ∈ c.O) : ‖x‖ ≤ 1 :=
  norm_le_one_of_isIntegral x ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val)

theorem mat_mul (W : R2 Ω l) (s t : G ℚ Ω) : mat W (s * t) = mat W s * mat W t := by
  simp [mat, map_mul, Units.val_mul]

def frobOp (W : R2 Ω l) (c : Coef l) (φ : G ℚ Ω) :
    (G ℚ Ω → Fin 2 → Qbar l) →ₗ[c.O] (G ℚ Ω → Fin 2 → Qbar l) where
  toFun z s := mat W φ *ᵥ z (φ⁻¹ * s * φ)
  map_add' a b := by funext s; simp [Matrix.mulVec_add]
  map_smul' k a := by funext s; simp [Matrix.mulVec_smul]

theorem frobOp_apply (W : R2 Ω l) (c : Coef l) (φ : G ℚ Ω) (z : G ℚ Ω → Fin 2 → Qbar l) (s : G ℚ Ω) :
    frobOp W c φ z s = mat W φ *ᵥ z (φ⁻¹ * s * φ) := rfl

theorem conj_mem_Ine' {B : ValuationSubring Ω} {φ s : G ℚ Ω} (hφ : φ ∈ Dec (F := ℚ) B)
    (hs : s ∈ Ine (F := ℚ) B) : φ⁻¹ * s * φ ∈ Ine (F := ℚ) B := by
  have := conj_mem_Ine ((Dec (F := ℚ) B).inv_mem hφ) hs
  rwa [inv_inv] at this

theorem frobOp_cob (W : R2 Ω l) (c : Coef l) (B : ValuationSubring Ω) {φ : G ℚ Ω} (hφ : φ ∈ Dec (F := ℚ) B) :
    cob W c (Ine (F := ℚ) B) ≤ (cob W c (Ine (F := ℚ) B)).comap (frobOp W c φ) := by
  rintro z ⟨v, hv⟩
  refine ⟨mat W φ *ᵥ v, fun s hs => ?_⟩
  rw [frobOp_apply, hv _ (conj_mem_Ine' hφ hs), Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    ← mat_mul, ← mat_mul]
  congr 2
  group

theorem frobOp_coc (W : R2 Ω l) (c : Coef l) (B : ValuationSubring Ω) (hWO : ∀ s i j, mat W s i j ∈ c.O)
    {φ : G ℚ Ω} (hφ : φ ∈ Dec (F := ℚ) B) :
    ∀ z ∈ coc W c (Ine (F := ℚ) B), frobOp W c φ z ∈ coc W c (Ine (F := ℚ) B) := by
  rintro z ⟨h1, h2, h3⟩
  have hconj : Continuous fun s : G ℚ Ω => φ⁻¹ * s * φ := (continuous_const.mul continuous_id).mul continuous_const
  refine ⟨fun i => ?_, fun s i => ?_, fun s hs t ht => ?_⟩
  · simp only [frobOp_apply, Matrix.mulVec, dotProduct]
    exact continuous_finset_sum _ fun j _ => continuous_const.mul ((h1 j).comp hconj)
  · simp only [frobOp_apply, Matrix.mulVec, dotProduct]
    exact Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (hWO _ _ _) (h2 _ _)
  · simp only [frobOp_apply]
    have e : φ⁻¹ * (s * t) * φ = (φ⁻¹ * s * φ) * (φ⁻¹ * t * φ) := by group
    rw [e, h3 _ (conj_mem_Ine' hφ hs) _ (conj_mem_Ine' hφ ht), Matrix.mulVec_add, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, ← mat_mul, ← mat_mul]
    congr 3
    group

variable [IsAlgClosure ℚ Ω]

theorem cycMod_eq_one_of_mem_Ine {B : ValuationSubring Ω} {q : Pl} (hB : IsPlaceOver B q)
    (hl : ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal) (r : ℕ) {s : G ℚ Ω} (hs : s ∈ Ine (F := ℚ) B) :
    cycMod ℚ Ω l r s = 1 := by
  have h := cycZ_toZModPow_eq hl hB (q := 1) (fun x hx => by simpa using hs.2 x hx) r
  ext
  simp only [cycMod, MonoidHom.coe_comp, Function.comp_apply, Units.coe_map, Units.val_one]
  rw [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, h]
  simp

theorem coprime_normV {q : Pl} (hl : ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal) : Nat.Coprime (normV q) l := by
  have hp := GlobalTheory.TameConjInv.prime_normV q
  refine (Nat.coprime_primes hp (Fact.out : l.Prime)).2 fun h => hl ?_
  have hmem : ((normV q : ℕ) : 𝓞 ℚ) ∈ q.asIdeal := Ideal.absNorm_mem q.asIdeal
  rwa [h] at hmem

theorem cycMod_frob {B : ValuationSubring Ω} {q : Pl} (hB : IsPlaceOver B q) (hl : ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal)
    {φ : G ℚ Ω} (hφ : IsFrob B (normV q) φ) (r : ℕ) :
    cycMod ℚ Ω l r φ = ZMod.unitOfCoprime (normV q) (Nat.Coprime.pow_right r (coprime_normV hl)) := by
  have h := cycZ_of_isFrob hl hB hφ
  ext
  simp only [cycMod, MonoidHom.coe_comp, Function.comp_apply, Units.coe_map, ZMod.coe_unitOfCoprime]
  rw [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, h]
  simp

end GlobalTheory.InertCoh

namespace GlobalTheory.InertCoh

theorem not_isUnit_natCast_O {l : ℕ} [Fact l.Prime] (c : Coef l) : ¬ IsUnit ((l : ℕ) : c.O) := by
  rintro ⟨u, hu⟩
  have h1 : ((u : c.O) : Qbar l) * ((u⁻¹ : c.Oˣ) : c.O) = 1 := by
    rw [← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one]
  have h2 : ((u : c.O) : Qbar l) = ((l : ℕ) : Qbar l) := by rw [hu]; simp
  have hl : ‖((l : ℕ) : Qbar l)‖ < 1 := by
    have e : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by rw [map_natCast]
    rw [e, PadicAlgCl.norm_extends l (l : ℚ_[l]), Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have h3 := norm_le_one_of_mem_O c (((u⁻¹ : c.Oˣ) : c.O)).2
  have h4 := congrArg norm h1
  rw [norm_mul, norm_one, h2] at h4
  have : ‖((l : ℕ) : Qbar l)‖ * ‖(((u⁻¹ : c.Oˣ) : c.O) : Qbar l)‖ < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) h3) hl
  linarith

theorem unr_of_limit_spec : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c : Coef l) (Y : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) (η : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (y : G ℚ Ω → Fin 2 → Qbar l), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∀ r x i, Continuous fun s => Y r s x i) → (∀ r s x i, Y r s x i ∈ c.O) → (∀ r, ShCoc (mat W) (cycMod ℚ Ω l r)⁻¹ (Y r)) → (∀ r s, Y r s = push (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) (Y (r + 1)) s) → (∀ r x, η r x ∈ c.O) → (∀ r s i, ‖y s i - spec (η r) (Y r) s i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → ∀ q : Pl, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∃ B : ValuationSubring Ω, IsPlaceOver B q ∧ ∃ v : Fin 2 → Qbar l, ∀ s ∈ Ine (F := ℚ) B, y s = mat W s *ᵥ v - v := by
  intro l _ Ω _ _ _ W c Y η y hW hWO hYc hYO hsh hnorm hη hy q hl
  obtain ⟨B, hB⟩ := exists_isPlaceOver Ω q
  refine ⟨B, hB, ?_⟩
  obtain ⟨φ, hφ⟩ := exists_isFrob hB
  obtain ⟨γ, hγ⟩ := GlobalTheory.TameInertiaGen.exists_tameGenAt ℚ Ω q B hB
  have hq := coprime_normV hl
  let u : ∀ r : ℕ, (ZMod (l ^ r))ˣ := fun r => ZMod.unitOfCoprime (normV q) (Nat.Coprime.pow_right r hq)
  let z : ∀ r : ℕ, (ZMod (l ^ r))ˣ → G ℚ Ω → Fin 2 → Qbar l := fun r x s => Y r s x
  have hzZ : ∀ r x, z r x ∈ coc W c (Ine (F := ℚ) B) := by
    intro r x
    refine ⟨fun i => hYc r x i, fun s i => hYO r s x i, fun s hs t _ => ?_⟩
    have h := hsh r s t x
    simp only [MonoidHom.inv_apply, cycMod_eq_one_of_mem_Ine hB hl r hs, inv_one, mul_one] at h
    exact h
  have hFB := frobOp_cob W c B hφ.1
  let FH := (cob W c (Ine (F := ℚ) B)).mapQ (cob W c (Ine (F := ℚ) B)) (frobOp W c φ) hFB
  have hFM : ∀ x ∈ (coc W c (Ine (F := ℚ) B)).map (cob W c (Ine (F := ℚ) B)).mkQ,
      FH x ∈ (coc W c (Ine (F := ℚ) B)).map (cob W c (Ine (F := ℚ) B)).mkQ := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨frobOp W c φ w, frobOp_coc W c B hWO hφ.1 w hw, rfl⟩
  have hfrob : ∀ r x, FH ((cob W c (Ine (F := ℚ) B)).mkQ (z r x)) =
      (cob W c (Ine (F := ℚ) B)).mkQ (z r (x * u r)) := by
    intro r x
    show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero]
    refine ⟨Y r φ (x * u r), fun s hs => ?_⟩
    have h1 := hsh r φ (φ⁻¹ * s * φ) (x * u r)
    have h2 := hsh r s φ (x * u r)
    rw [MonoidHom.inv_apply, cycMod_frob hB hl hφ r] at h1
    rw [MonoidHom.inv_apply, cycMod_eq_one_of_mem_Ine hB hl r hs, inv_one, mul_one] at h2
    have e : φ * (φ⁻¹ * s * φ) = s * φ := by group
    rw [e, h2, mul_inv_cancel_right] at h1
    show mat W φ *ᵥ Y r (φ⁻¹ * s * φ) x - Y r s (x * u r) = mat W s *ᵥ Y r φ (x * u r) - Y r φ (x * u r)
    calc mat W φ *ᵥ Y r (φ⁻¹ * s * φ) x - Y r s (x * u r)
        = (Y r φ (x * u r) + mat W φ *ᵥ Y r (φ⁻¹ * s * φ) x) - Y r φ (x * u r) - Y r s (x * u r) := by abel
      _ = (Y r s (x * u r) + mat W s *ᵥ Y r φ (x * u r)) - Y r φ (x * u r) - Y r s (x * u r) := by rw [h1]
      _ = _ := by abel
  have hN : ∀ r x, (cob W c (Ine (F := ℚ) B)).mkQ (z r x) = ∑ x' ∈ Finset.univ.filter (fun x' : (ZMod (l ^ (r + 1)))ˣ =>
      Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom x' = x),
      (cob W c (Ine (F := ℚ) B)).mkQ (z (r + 1) x') := by
    intro r x
    rw [← map_sum]
    congr 1
    funext s
    rw [Finset.sum_apply]
    show Y r s x = _
    rw [hnorm r s]
    rfl
  have hFG : ((coc W c (Ine (F := ℚ) B)).map (cob W c (Ine (F := ℚ) B)).mkQ).FG :=
    GlobalTheory.T.fg_inertiaCocycles_mod_coboundaries_coefRing l Ω W c (Ine (F := ℚ) B) {σ | ∀ y : Ω, y ≠ 0 → B.valuation (σ y / y - 1) < 1} γ hW hWO
      (fun w hw => GlobalTheory.T.exists_integral_coboundary_wildInertia_away_from_l l Ω W c B q hW hWO hB hl w hw)
      (fun w hw hP h0 => GlobalTheory.T.inertiaCocycle_eq_zero_of_vanish_wild_tameGenerator l Ω W B γ hγ w hw.1 hw.2.2 (fun σ hσ => hP σ hσ) h0)
  have hlO : ¬ IsUnit ((l : ℕ) : c.O) := not_isUnit_natCast_O c
  haveI : IsLocalRing c.O := IsDiscreteValuationRing.toIsLocalRing
  haveI : IsNoetherianRing c.O := inferInstance
  have hzero := GlobalTheory.T.normCompatible_system_frobenius_eq_zero c.O _ l hlO (normV q) hq (GlobalTheory.TameConjInv.prime_normV q).two_le
    ((coc W c (Ine (F := ℚ) B)).map (cob W c (Ine (F := ℚ) B)).mkQ) hFG FH hFM
    (fun r x => (cob W c (Ine (F := ℚ) B)).mkQ (z r x)) (fun r x => Submodule.mem_map_of_mem (hzZ r x)) hfrob hN
  have hspec : ∀ r, spec (η r) (Y r) ∈ cob W c (Ine (F := ℚ) B) := by
    intro r
    have e : spec (η r) (Y r) = ∑ x, (⟨η r x, hη r x⟩ : c.O) • z r x := by
      funext s
      simp only [spec, Finset.sum_apply, Pi.smul_apply, Subalgebra.smul_def]
      rfl
    rw [e]
    refine Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ ?_
    have h := hzero r x
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
  exact GlobalTheory.T.coboundary_of_padicAlgCl_uniform_approx l (G ℚ Ω) (Ine (F := ℚ) B : Set (G ℚ Ω)) (mat W) (fun r => spec (η r) (Y r)) y
    (fun s i j => norm_le_one_of_mem_O c (hWO s i j)) (fun r => hspec r) hy

end GlobalTheory.InertCoh

end
