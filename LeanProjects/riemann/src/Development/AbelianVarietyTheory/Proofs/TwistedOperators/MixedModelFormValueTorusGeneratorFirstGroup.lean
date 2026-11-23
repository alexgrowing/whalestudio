import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumOpTransversal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergQuotientOpSumVacuumCommensurableSelfDuStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeisenbergInvariantLinearFormIsotropicVacuStatement
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SphTheta.TorusFirst

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def dTor (ϖ : L) (n : ℕ) (k : Fin (n / 2)) (j : Fin n) : L :=
  if j = lo n k then ϖ else if j = (lo n k).rev then ϖ⁻¹ else 1

def dInv (ϖ : L) (n : ℕ) (k : Fin (n / 2)) (j : Fin n) : L :=
  if j = lo n k then ϖ⁻¹ else if j = (lo n k).rev then ϖ else 1

theorem lo_ne_rev (n : ℕ) (k : Fin (n / 2)) : lo n k ≠ (lo n k).rev := by
  intro h
  have := congrArg Fin.val h
  simp only [lo, Fin.val_rev] at this
  omega

theorem tMat_single (ϖ : L) (n : ℕ) (k : Fin (n / 2)) :
    tMat ϖ n (n / 2) (Pi.single k 1) = diagonal (dTor ϖ n k) := by
  unfold tMat
  congr 1
  funext i
  simp only [dTor, Fin.ext_iff, lo, Fin.val_rev, Pi.single_apply]
  have hk := k.isLt
  have hi := i.isLt
  split_ifs <;> first | rfl | (exfalso; omega) | simp_all | skip

theorem dTor_mul {σ : L →+* L} {ϖ : L} (hσϖ : σ ϖ = ϖ) (hϖ : ϖ ≠ 0) {n : ℕ} (k : Fin (n / 2)) (j : Fin n) :
    dTor ϖ n k j * σ (dTor ϖ n k j.rev) = 1 := by
  have hne := lo_ne_rev n k
  unfold dTor
  by_cases h1 : j = lo n k
  · subst h1; simp [hne.symm, hσϖ, hϖ]
  by_cases h2 : j = (lo n k).rev
  · subst h2; simp [hne, hne.symm, hσϖ, hϖ]
  have h3 : j.rev ≠ lo n k := fun h => h2 (by rw [← h, Fin.rev_rev])
  have h4 : j.rev ≠ (lo n k).rev := fun h => h1 (Fin.rev_injective h)
  simp [h1, h2, h3, h4]

theorem dInv_mul_dTor {ϖ : L} (hϖ : ϖ ≠ 0) {n : ℕ} (k : Fin (n / 2)) :
    diagonal (dInv ϖ n k) * diagonal (dTor ϖ n k) = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext j
  unfold dInv dTor
  split_ifs <;> simp [hϖ]

theorem dTor_mul_dInv {ϖ : L} (hϖ : ϖ ≠ 0) {n : ℕ} (k : Fin (n / 2)) :
    diagonal (dTor ϖ n k) * diagonal (dInv ϖ n k) = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext j
  unfold dInv dTor
  split_ifs <;> simp [hϖ]

theorem pairing_mul_diagonal {σ : L →+* L} {δ : L} {ψ : AddChar L ℂ} {n n' : ℕ} (d : Fin n → L)
    (hd : ∀ j, d j * σ (d j.rev) = 1) (x y : Matrix (Fin n') (Fin n) L) :
    pairing σ δ ψ (x * diagonal d) (y * diagonal d) = pairing σ δ ψ x y := by
  have : ∀ i j, (x * diagonal d) i j * σ ((y * diagonal d) i.rev j.rev) = x i j * σ (y i.rev j.rev) := by
    intro i j
    rw [mul_diagonal, mul_diagonal, map_mul]
    calc x i j * d j * (σ (y i.rev j.rev) * σ (d j.rev)) = x i j * σ (y i.rev j.rev) * (d j * σ (d j.rev)) := by ring
      _ = _ := by rw [hd, mul_one]
  simp only [pairing, this]

def latT (ϖ : L) (n n' : ℕ) (k : Fin (n / 2)) : Submodule (intL L) (Matrix (Fin n') (Fin n) L) where
  carrier := {x | x * diagonal (dTor ϖ n k) ∈ intMat L (Fin n') (Fin n)}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, Matrix.add_mul] at *
    exact add_mem ha hb
  zero_mem' := by simp only [Set.mem_setOf_eq, Matrix.zero_mul]; exact zero_mem _
  smul_mem' r x hx := by
    simp only [Set.mem_setOf_eq, Matrix.smul_mul] at *
    exact (intMat L (Fin n') (Fin n)).smul_mem r hx

theorem mem_latT {ϖ : L} {n n' : ℕ} {k : Fin (n / 2)} {x : Matrix (Fin n') (Fin n) L} :
    x ∈ latT ϖ n n' k ↔ x * diagonal (dTor ϖ n k) ∈ intMat L (Fin n') (Fin n) := Iff.rfl

theorem selfDual_latT {σ : L →+* L} {δ : L} {ψ : AddChar L ℂ} {ϖ : L} (hσϖ : σ ϖ = ϖ) (hϖ : ϖ ≠ 0) {n n' : ℕ}
    (k : Fin (n / 2)) (h : SelfDual (pairing σ δ ψ) (intMat L (Fin n') (Fin n))) :
    SelfDual (pairing σ δ ψ) (latT ϖ n n' k) := by
  intro x
  rw [mem_latT, h]
  constructor
  · intro hx b hb
    rw [← pairing_mul_diagonal _ (dTor_mul hσϖ hϖ k)]
    exact hx _ hb
  · intro hx a ha
    have hb : a * diagonal (dInv ϖ n k) ∈ latT ϖ n n' k := by
      rw [mem_latT, Matrix.mul_assoc, dInv_mul_dTor hϖ, Matrix.mul_one]; exact ha
    have := hx _ hb
    rw [← pairing_mul_diagonal _ (dTor_mul hσϖ hϖ k), Matrix.mul_assoc, dInv_mul_dTor hϖ, Matrix.mul_one] at this
    exact this

theorem mem_intL_iff_mul {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (z : L) :
    z ∈ intL L ↔ Valued.v (ϖ * z) < 1 := by
  have hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  rw [mem_intL, map_mul, hϖ]
  by_cases hz : Valued.v z = 0
  · simp [hz]
  · rw [← WithZero.exp_log hz, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp, WithZero.exp_lt_exp]
    omega

variable (L) in

abbrev OV : ValuationSubring L := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring

variable (L) in

abbrev ResF : Type := OV L ⧸ IsLocalRing.maximalIdeal (OV L)

theorem card_resF {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) : Nat.card (ResF L) = q ^ 2 :=
  hU.2.2.2.2.2.2

def liftO (c : ResF L) : OV L := if c = 0 then 0 else Function.surjInv Ideal.Quotient.mk_surjective c

theorem mk_liftO (c : ResF L) : Ideal.Quotient.mk (IsLocalRing.maximalIdeal (OV L)) (liftO c) = c := by
  unfold liftO
  split_ifs with h
  · rw [map_zero, h]
  · exact Function.surjInv_eq _ c

def liftR (c : ResF L) : L := (liftO c : L)

theorem liftR_zero : liftR (0 : ResF L) = 0 := by simp [liftR, liftO]

theorem liftR_mem (c : ResF L) : liftR c ∈ intL L := (liftO c).2

theorem sub_mem_iff {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (hϖ : ϖ ≠ 0) {z : L} (hz : ϖ * z ∈ intL L)
    (c : ResF L) : z - ϖ⁻¹ * liftR c ∈ intL L ↔ c = Ideal.Quotient.mk (IsLocalRing.maximalIdeal (OV L)) (⟨ϖ * z, hz⟩ : OV L) := by
  have e : ϖ * (z - ϖ⁻¹ * liftR c) = (((⟨ϖ * z, hz⟩ : OV L) - liftO c : OV L) : L) := by
    rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ hϖ, one_mul]
    rfl
  rw [mem_intL_iff_mul hU, e, ← Valuation.mem_maximalIdeal_iff, ← Ideal.Quotient.eq, mk_liftO, eq_comm]

theorem card_sum_vanish {F : Type} [Fintype F] [Zero F] [DecidableEq F] (N m : ℕ) (hm : m ≤ N) :
    ∑ y : Fin N → F, (if ∀ r : Fin N, m ≤ r.val → y r = 0 then (1 : ℂ) else 0) = (Fintype.card F : ℂ) ^ m := by
  have h1 : ∀ y : Fin N → F, (if ∀ r : Fin N, m ≤ r.val → y r = 0 then (1 : ℂ) else 0) =
      ∏ r : Fin N, (if m ≤ r.val then (if y r = 0 then (1 : ℂ) else 0) else 1) := by
    intro y
    split_ifs with h
    · refine (Finset.prod_eq_one fun r _ => ?_).symm
      by_cases hr : m ≤ r.val
      · rw [if_pos hr, if_pos (h r hr)]
      · rw [if_neg hr]
    · push_neg at h
      obtain ⟨r, hr, hy⟩ := h
      exact (Finset.prod_eq_zero (Finset.mem_univ r) (by rw [if_pos hr, if_neg hy])).symm
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun (r : Fin N) (c : F) => if m ≤ r.val then (if c = 0 then (1 : ℂ) else 0) else 1)]
  have h2 : ∀ r : Fin N, ∑ c : F, (if m ≤ r.val then (if c = 0 then (1 : ℂ) else 0) else 1) =
      if m ≤ r.val then 1 else (Fintype.card F : ℂ) := by
    intro r
    split_ifs <;> simp
  simp_rw [h2]
  rw [Fin.prod_univ_eq_prod_range (fun i => if m ≤ i then (1 : ℂ) else (Fintype.card F : ℂ)) N,
    ← Finset.prod_range_mul_prod_Ico _ hm,
    Finset.prod_congr rfl (fun i hi => if_neg (by simp only [Finset.mem_range] at hi; omega)), Finset.prod_const,
    Finset.card_range, Finset.prod_eq_one (fun i hi => if_pos (by simp only [Finset.mem_Ico] at hi; omega)), mul_one]

theorem val_one_add_dInv {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (h2 : Valued.v (2 : L) = 1) {n : ℕ}
    (k : Fin (n / 2)) (j : Fin n) :
    Valued.v (1 + dInv ϖ n k j) = if j = lo n k then WithZero.exp (1 : ℤ) else 1 := by
  have hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  have hne := lo_ne_rev n k
  unfold dInv
  by_cases h1 : j = lo n k
  · subst h1
    have hi : Valued.v ϖ⁻¹ = WithZero.exp (1 : ℤ) := by rw [map_inv₀, hϖ, ← WithZero.exp_neg, neg_neg]
    rw [if_pos rfl, if_pos rfl, Valuation.map_add_eq_of_lt_right, hi]
    rw [hi, map_one, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  by_cases h2' : j = (lo n k).rev
  · rw [if_neg h1, if_pos h2', if_neg h1, Valuation.map_add_eq_of_lt_left, map_one]
    rw [hϖ, map_one, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  · rw [if_neg h1, if_neg h2', if_neg h1, one_add_one_eq_two, h2]

theorem ordL_of_val {x : L} (hx : Valued.v x = WithZero.exp (1 : ℤ)) : ordL x = -1 := by
  have key : ∀ (w : WithZero (Multiplicative ℤ)) (h : w ≠ 0), w = WithZero.exp (1 : ℤ) →
      -Multiplicative.toAdd (WithZero.unzero h) = -1 := by
    rintro _ h rfl; rfl
  unfold ordL
  rw [dif_neg (by rw [hx]; exact WithZero.exp_ne_zero)]
  exact key _ _ hx

theorem cayley_dInv {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (h2 : Valued.v (2 : L) = 1) {n : ℕ}
    (k : Fin (n / 2)) :
    (1 + diagonal (dInv ϖ n k)).det ≠ 0 ∧ (1 + diagonal (dInv ϖ n k))⁻¹ ∈ intMat L (Fin n) (Fin n) ∧
      ordL (1 + diagonal (dInv ϖ n k)).det = -1 := by
  have hd : 1 + diagonal (dInv ϖ n k) = diagonal (fun j => 1 + dInv ϖ n k j) := by
    rw [← diagonal_one, diagonal_add]
  have hv := val_one_add_dInv hU h2 k
  have hc0 : ∀ j, 1 + dInv ϖ n k j ≠ 0 := fun j h => by
    have := hv j
    rw [h, map_zero] at this
    split_ifs at this with h'
    · exact WithZero.exp_ne_zero this.symm
    · exact zero_ne_one this
  have hvdet : Valued.v (1 + diagonal (dInv ϖ n k)).det = WithZero.exp (1 : ℤ) := by
    rw [hd, det_diagonal, map_prod]
    simp_rw [hv]
    simp [Finset.prod_ite_eq']
  refine ⟨fun h => by rw [h, map_zero] at hvdet; exact WithZero.exp_ne_zero hvdet.symm, ?_, ordL_of_val hvdet⟩
  rw [hd, Matrix.inv_eq_right_inv (B := diagonal (fun j => (1 + dInv ϖ n k j)⁻¹))]
  · intro i j
    rw [diagonal_apply]
    split_ifs with hij
    · rw [mem_intL, map_inv₀, hv]
      split_ifs
      · rw [← WithZero.exp_neg, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num
      · rw [inv_one]
    · exact zero_mem _
  · rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext j
    exact mul_inv_cancel₀ (hc0 j)

def fT (ϖ : L) (n n' : ℕ) (k : Fin (n / 2)) (y : Fin n' → ResF L) : Matrix (Fin n') (Fin n) L :=
  fun r j => if j = lo n k then ϖ⁻¹ * liftR (y r) else 0

theorem fT_mem {ϖ : L} (hϖ : ϖ ≠ 0) {n n' : ℕ} (k : Fin (n / 2)) (y : Fin n' → ResF L) :
    fT ϖ n n' k y ∈ latT ϖ n n' k := by
  rw [mem_latT]
  intro r j
  rw [mul_diagonal]
  unfold fT dTor
  split_ifs with h
  · rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ hϖ, one_mul]; exact liftR_mem _
  · rw [zero_mul]; exact zero_mem _
  · rw [zero_mul]; exact zero_mem _

theorem fT_unique {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (hϖ : ϖ ≠ 0) {n n' : ℕ} (k : Fin (n / 2)) :
    ∀ b ∈ latT ϖ n n' k, ∃! y : Fin n' → ResF L, b - fT ϖ n n' k y ∈ intMat L (Fin n') (Fin n) := by
  intro b hb
  have hb' : ∀ r j, b r j * dTor ϖ n k j ∈ intL L := fun r j => by
    have := hb r j
    rwa [mul_diagonal] at this
  have hϖi : ϖ ∈ intL L := by
    rw [mem_intL, hU.2.2.2.1]; exact le_of_lt (by rw [← WithZero.coe_one, WithZero.coe_lt_coe]; decide)
  have hlo : ∀ r, ϖ * b r (lo n k) ∈ intL L := fun r => by
    have := hb' r (lo n k)
    unfold dTor at this
    rw [if_pos rfl, mul_comm] at this
    exact this
  have hother : ∀ r j, j ≠ lo n k → b r j ∈ intL L := fun r j hj => by
    have := hb' r j
    unfold dTor at this
    rw [if_neg hj] at this
    split_ifs at this with h
    · have e : b r j = b r j * ϖ⁻¹ * ϖ := by rw [mul_assoc, inv_mul_cancel₀ hϖ, mul_one]
      rw [e]; exact mul_mem this hϖi
    · rwa [mul_one] at this
  refine ⟨fun r => Ideal.Quotient.mk (IsLocalRing.maximalIdeal (OV L)) (⟨ϖ * b r (lo n k), hlo r⟩ : OV L), ?_, ?_⟩
  · intro r j
    show b r j - fT ϖ n n' k _ r j ∈ intL L
    unfold fT
    split_ifs with h
    · subst h; exact (sub_mem_iff hU hϖ (hlo r) _).2 rfl
    · rw [sub_zero]; exact hother r j h
  · intro y hy
    funext r
    have := hy r (lo n k)
    change b r (lo n k) - fT ϖ n n' k y r (lo n k) ∈ intL L at this
    unfold fT at this
    rw [if_pos rfl] at this
    exact (sub_mem_iff hU hϖ (hlo r) _).1 this

theorem value_torus_first : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) (n n' : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M), IsStd ϖ σ q δ ψ ρ ω s → CayleyRule q n' ρ (ω.comp (MonoidHom.inl _ _)) s → ∀ ℓ : M →ₗ[ℂ] ℂ, ℓ s = 1 → (∀ a ∈ mixLat L n' n, ∀ v, ℓ (ρ a v) = ℓ v) → (∀ x, (¬ ∃ a ∈ mixLat L n' n, x - a ∈ intMat L (Fin n') (Fin n)) → ℓ (ρ x s) = 0) → ∀ (k : Fin (n / 2)) (t : GU σ n), t.1.1 = tMat ϖ n (n / 2) (Pi.single k 1) → ℓ (ω (t, 1) s) = (-1) ^ n' * (q : ℂ) ^ (2 * ((n' / 2 : ℕ) : ℤ) - n') := by
  intro L _ _ ϖ σ q δ ψ n n' M _ _ ρ ω s hS hC ℓ hℓs hℓinv hℓ0 k t ht
  have hU := hS.1.unr
  have hϖ0 : ϖ ≠ 0 := fun h => by
    have := hU.2.2.2.1
    rw [h, map_zero] at this
    exact WithZero.zero_ne_coe this
  have hσϖ : σ ϖ = ϖ := hU.2.2.1
  have hH := hS.isHeis
  have hSD := hS.selfDual
  have hSD' : SelfDual (pairing σ δ ψ) (latT ϖ n n' k) := selfDual_latT hσϖ hϖ0 k hSD
  have htinv : (((t : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = diagonal (dInv ϖ n k) := by
    rw [Matrix.coe_units_inv, show ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = _ from ht, tMat_single]
    exact Matrix.inv_eq_right_inv (dTor_mul_dInv hϖ0 k)
  have hfixv : Fixes ρ (latT ϖ n n' k) (ω (t, 1) s) := by
    intro b hb
    have hn := hS.1.norm t 1 (b * diagonal (dTor ϖ n k))
    simp only [OneMemClass.coe_one, Units.val_one, Matrix.one_mul] at hn
    rw [htinv, Matrix.mul_assoc, dTor_mul_dInv hϖ0 k, Matrix.mul_one] at hn
    have := congrArg (fun f => f s) hn
    simp only [Module.End.mul_apply] at this
    refine this.symm.trans (congrArg _ (hS.fixes _ hb))
  obtain ⟨e, he1, he⟩ := GlobalTheory.T.exists_heisenbergInvariant_linearForm_isotropic_vacuum hH _ hSD s hS.2.1 hS.fixes hS.2.2.2 _ (fun a ha b hb => (hSD a).1 ha b hb)
  have hev : e (ω (t, 1) s) = ((-1) ^ n' * (q : ℂ) ^ n') ^ (-1 : ℤ) := by
    obtain ⟨hdet, hint, hord⟩ := cayley_dInv hU hS.v_two k
    have hg : (t⁻¹ : GU σ n).1.1 = diagonal (dInv ϖ n k) := htinv
    have := hC e he t⁻¹ (by rw [hg]; exact hdet) (by rw [hg]; exact hint)
    rw [hg, hord, he1, mul_one] at this
    simpa using this
  haveI : Finite (ResF L) := Nat.finite_of_card_ne_zero (by rw [card_resF hU]; have := hU.2.2.2.2.2.1; positivity)
  letI : Fintype (ResF L) := Fintype.ofFinite _
  obtain ⟨hsum, hidx⟩ := (sumOp_transversal hH _ _ hSD').1 s hS.fixes (Fin n' → ResF L) (fT ϖ n n' k)
    (fT_mem hϖ0 k) (fT_unique hU hϖ0 k)
  have hidx0 : idx (intMat L (Fin n') (Fin n)) (latT ϖ n n' k) ≠ 0 := by rw [hidx]; exact Fintype.card_ne_zero
  have hv := (GlobalTheory.T.heisenbergQuotientOpSum_vacuum_commensurable_selfDualLattice hH _ hSD s hS.2.1 hS.fixes hS.2.2.2 _ hSD' hidx0).2 e he1 he _ hfixv
  have hterm : ∀ y : Fin n' → ResF L, ℓ (ρ (fT ϖ n n' k y) s) =
      if ∀ r : Fin n', n' / 2 ≤ r.val → y r = 0 then 1 else 0 := by
    intro y
    split_ifs with hy
    · rw [hℓinv _ ?_ s, hℓs]
      intro r c
      have h0 : n' / 2 ≤ r.val → fT ϖ n n' k y r c = 0 := fun hr => by
        unfold fT
        split_ifs
        · rw [hy r hr, liftR_zero, mul_zero]
        · rfl
      refine ⟨fun hr => h0 (by omega), fun hr _ => by rw [h0 hr]; exact zero_mem _⟩
    · push_neg at hy
      obtain ⟨r, hr, hyr⟩ := hy
      refine hℓ0 _ ?_
      rintro ⟨a, ha, hxa⟩
      have h1 := hxa r (lo n k)
      have h2 : a r (lo n k) = 0 := (ha r (lo n k)).1 (Or.inr ⟨hr, by simp [lo]⟩)
      change fT ϖ n n' k y r (lo n k) - a r (lo n k) ∈ intL L at h1
      rw [h2, sub_zero] at h1
      unfold fT at h1
      rw [if_pos rfl] at h1
      have h3 := (sub_mem_iff hU hϖ0 (z := 0) (by rw [mul_zero]; exact zero_mem _) (y r)).1
        (by rw [zero_sub]; exact neg_mem h1)
      exact hyr (h3.trans ((Ideal.Quotient.eq_zero_iff_mem).2 ((Valuation.mem_maximalIdeal_iff _ _).2 (by simp))))
  rw [hv, map_smul, hsum, map_sum, hev, smul_eq_mul]
  simp_rw [hterm]
  have hc : (∑ y : Fin n' → ResF L, (if ∀ r : Fin n', n' / 2 ≤ r.val → y r = 0 then (1 : ℂ) else 0)) =
      ((Fintype.card (ResF L) : ℕ) : ℂ) ^ (n' / 2) := by
    convert card_sum_vanish (F := ResF L) n' (n' / 2) (Nat.div_le_self _ _)
  rw [Fintype.card_eq_nat_card, card_resF hU] at hc
  rw [hc]
  have hq : (q : ℂ) ≠ 0 := by have := hU.2.2.2.2.2.1; exact_mod_cast (by omega : q ≠ 0)
  have h1 : ((-1 : ℂ) ^ n')⁻¹ = (-1) ^ n' := by rw [← inv_pow, inv_neg, inv_one]
  rw [_root_.zpow_neg_one, zpow_sub₀ hq, show (2 * ((n' / 2 : ℕ) : ℤ)) = ((2 * (n' / 2) : ℕ) : ℤ) by push_cast; ring,
    zpow_natCast, zpow_natCast, mul_inv, h1, pow_mul]
  push_cast
  ring

end GlobalTheory.SphTheta.TorusFirst
