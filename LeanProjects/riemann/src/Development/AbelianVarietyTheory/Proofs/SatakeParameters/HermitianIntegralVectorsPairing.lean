import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DvdPowZeroIff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqZeroOfForallDvdPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MulSelfEqOneIffOfLinearOrderedCommGroupWithZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WittFreeTuplesFin
open Matrix

noncomputable section

namespace GlobalTheory.Hk3.ResWitt

open Formalism.UG GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

abbrev OV (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] : ValuationSubring L :=
  (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring

abbrev Res (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] : Type :=
  IsLocalRing.ResidueField (OV L)

theorem isUnit_iff (x : OV L) : IsUnit x ↔ Valued.v (x : L) = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 : Valued.v ((u : OV L) : L) ≤ 1 := (u : OV L).2
    have h2 : Valued.v (((u⁻¹ : (OV L)ˣ) : OV L) : L) ≤ 1 := ((u⁻¹ : (OV L)ˣ) : OV L).2
    have h3 : ((u : OV L) : L) * (((u⁻¹ : (OV L)ˣ) : OV L) : L) = 1 := by
      rw [show ((u : OV L) : L) * (((u⁻¹ : (OV L)ˣ) : OV L) : L) = (((u : OV L) * ((u⁻¹ : (OV L)ˣ) : OV L) : OV L) : L) from rfl, Units.mul_inv]; rfl
    have h4 : Valued.v ((u : OV L) : L) * Valued.v (((u⁻¹ : (OV L)ˣ) : OV L) : L) = 1 := by
      rw [← map_mul, h3, map_one]
    refine le_antisymm h1 ?_
    calc (1 : WithZero (Multiplicative ℤ)) = _ := h4.symm
      _ ≤ Valued.v ((u : OV L) : L) * 1 := mul_le_mul' le_rfl h2
      _ = _ := mul_one _
  · intro h
    have hx : (x : L) ≠ 0 := by
      intro h0; rw [h0, map_zero] at h; exact zero_ne_one h
    have hm : (x : L)⁻¹ ∈ OV L := by
      show Valued.v (x : L)⁻¹ ≤ 1
      rw [map_inv₀, h, inv_one]
    exact IsUnit.of_mul_eq_one (b := (⟨_, hm⟩ : OV L)) (Subtype.ext (mul_inv_cancel₀ hx))

theorem lt_one_iff_le {a : WithZero (Multiplicative ℤ)} :
    a < 1 ↔ a ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  rcases eq_or_ne a 0 with rfl | h0
  · simp
  · obtain ⟨m, rfl⟩ : ∃ m, a = WithZero.exp m := ⟨_, (WithZero.exp_log h0).symm⟩
    show WithZero.exp m < WithZero.exp 0 ↔ WithZero.exp m ≤ WithZero.exp (-1)
    rw [WithZero.exp_lt_exp, WithZero.exp_le_exp]; omega

theorem residue_eq_zero_iff {ϖ : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (x : OV L) : IsLocalRing.residue (OV L) x = 0 ↔ DvdPow ϖ 1 (x : L) := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff]
  have hϖ0 : ϖ ≠ 0 := by intro h0; rw [h0, map_zero] at hϖ; exact WithZero.zero_ne_coe hϖ
  have hx1 : Valued.v (x : L) ≤ 1 := x.2
  constructor
  · intro h
    have hlt : Valued.v (x : L) < 1 := lt_of_le_of_ne hx1 h
    rw [lt_one_iff_le, ← hϖ] at hlt
    refine ⟨(x : L) / ϖ, ?_, by field_simp⟩
    show Valued.v ((x : L) / ϖ) ≤ 1
    rw [map_div₀]
    exact div_le_one_of_le₀ hlt zero_le'
  · rintro ⟨b, hb, hxb⟩ h
    have hb' : Valued.v b ≤ 1 := hb
    have : Valued.v (x : L) ≤ Valued.v ϖ := by
      rw [hxb, map_mul, pow_one]
      calc Valued.v ϖ * Valued.v b ≤ Valued.v ϖ * 1 := mul_le_mul' le_rfl hb'
        _ = _ := mul_one _
    rw [h, hϖ] at this
    exact absurd (lt_one_iff_le.2 le_rfl) (not_lt.2 this)

def sigO (σ : L →+* L) (hσv : ∀ x, Valued.v (σ x) = Valued.v x) : OV L →+* OV L :=
  (σ.comp (OV L).subtype).codRestrict (OV L) fun x => by
    show Valued.v (σ (x : L)) ≤ 1
    rw [hσv]; exact x.2

theorem sigO_coe (σ : L →+* L) (hσv : ∀ x, Valued.v (σ x) = Valued.v x) (x : OV L) :
    ((sigO σ hσv x : OV L) : L) = σ x := rfl

theorem sigO_le (σ : L →+* L) (hσv : ∀ x, Valued.v (σ x) = Valued.v x) :
    IsLocalRing.maximalIdeal (OV L) ≤ Ideal.comap (sigO σ hσv) (IsLocalRing.maximalIdeal (OV L)) := by
  intro x hx
  rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff, sigO_coe, hσv,
    ← isUnit_iff, ← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal]
  exact hx

def sigK (σ : L →+* L) (hσv : ∀ x, Valued.v (σ x) = Valued.v x) : Res L →+* Res L :=
  Ideal.quotientMap (IsLocalRing.maximalIdeal (OV L)) (sigO σ hσv) (sigO_le σ hσv)

theorem sigK_residue (σ : L →+* L) (hσv : ∀ x, Valued.v (σ x) = Valued.v x) (x : OV L) :
    sigK σ hσv (IsLocalRing.residue (OV L) x) = IsLocalRing.residue (OV L) (sigO σ hσv x) := rfl

end GlobalTheory.Hk3.ResWitt

end

namespace GlobalTheory.Hk3.ResWitt

open Formalism.UG GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

open Classical in

noncomputable def redL (x : L) : Res L := if h : x ∈ OV L then IsLocalRing.residue (OV L) ⟨x, h⟩ else 0

theorem redL_coe (x : OV L) : redL (x : L) = IsLocalRing.residue (OV L) x := by
  unfold redL; rw [dif_pos x.2]

theorem redL_of_mem {x : L} (hx : x ∈ intL L) : redL x = IsLocalRing.residue (OV L) ⟨x, hx⟩ :=
  redL_coe ⟨x, hx⟩

theorem redL_add {x y : L} (hx : x ∈ intL L) (hy : y ∈ intL L) : redL (x + y) = redL x + redL y := by
  rw [redL_of_mem hx, redL_of_mem hy, redL_of_mem ((intL L).add_mem hx hy), ← map_add]; rfl

theorem redL_mul {x y : L} (hx : x ∈ intL L) (hy : y ∈ intL L) : redL (x * y) = redL x * redL y := by
  rw [redL_of_mem hx, redL_of_mem hy, redL_of_mem ((intL L).mul_mem hx hy), ← map_mul]; rfl

theorem redL_sub {x y : L} (hx : x ∈ intL L) (hy : y ∈ intL L) : redL (x - y) = redL x - redL y := by
  rw [redL_of_mem hx, redL_of_mem hy, redL_of_mem ((intL L).sub_mem hx hy), ← map_sub]; rfl

theorem redL_sum {ι : Type} (s : Finset ι) (f : ι → L) (hf : ∀ i, f i ∈ intL L) :
    redL (∑ i ∈ s, f i) = ∑ i ∈ s, redL (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, redL_of_mem (intL L).zero_mem]; exact map_zero _
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, redL_add (hf j) (Subring.sum_mem _ fun i _ => hf i), ih]

theorem redL_sigma (σ : L →+* L) (hσv : ∀ x, Valued.v (σ x) = Valued.v x) {x : L} (hx : x ∈ intL L) :
    redL (σ x) = sigK σ hσv (redL x) := by
  have hσx : σ x ∈ intL L := by show Valued.v (σ x) ≤ 1; rw [hσv]; exact hx
  rw [redL_of_mem hx, redL_of_mem hσx, sigK_residue]; rfl

theorem redL_eq_zero_iff {ϖ : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    {x : L} (hx : x ∈ intL L) : redL x = 0 ↔ DvdPow ϖ 1 x := by
  rw [redL_of_mem hx]; exact residue_eq_zero_iff hϖ ⟨x, hx⟩

theorem redL_surj (a : Res L) : ∃ x ∈ intL L, redL x = a := by
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective a
  exact ⟨y, y.2, redL_coe y⟩

theorem redL_ne_zero_of_v {x : L} (hx : Valued.v x = 1) : redL x ≠ 0 := by
  have hxi : x ∈ intL L := by show Valued.v x ≤ 1; rw [hx]
  rw [redL_of_mem hxi, Ne, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    not_not, isUnit_iff]
  exact hx

theorem sigK_invol (σ : L →+* L) (hσv : ∀ x, Valued.v (σ x) = Valued.v x) (hσσ : ∀ x, σ (σ x) = x) (a : Res L) :
    sigK σ hσv (sigK σ hσv a) = a := by
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective a
  rw [sigK_residue, sigK_residue]; congr 1; exact Subtype.ext (hσσ _)

theorem isQA_sigK {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (hq : Odd q) :
    GlobalTheory.SgAlg.IsQA (sigK σ h.2.1) := by
  obtain ⟨hσσ, hσv, -, -, ⟨x, hx, hxv⟩, -⟩ := id h
  refine ⟨sigK_invol σ _ hσσ, ⟨redL x, ?_⟩, inferInstance, ?_, fun y _ hy => hy.isUnit⟩
  · intro he
    have hσx : σ x ∈ intL L := by show Valued.v (σ x) ≤ 1; rw [hσv]; exact hx
    apply redL_ne_zero_of_v hxv
    rw [redL_sub hσx hx, redL_sigma σ hσv hx, he, sub_self]
  · have h2 : Valued.v (2 : L) = 1 := GlobalTheory.Hk3.Inh.v_two h hq
    have hne := redL_ne_zero_of_v h2
    have h2i : (2 : L) ∈ intL L := by show Valued.v (2 : L) ≤ 1; rw [h2]
    have : redL (2 : L) = 2 := by
      rw [show (2 : L) = 1 + 1 by norm_num, redL_add (intL L).one_mem (intL L).one_mem,
        redL_of_mem (intL L).one_mem]
      rw [show (⟨1, (intL L).one_mem⟩ : OV L) = 1 from rfl, map_one]; norm_num
    rw [this] at hne
    exact hne.isUnit

end GlobalTheory.Hk3.ResWitt

namespace GlobalTheory.Hk3.ResWitt

open Formalism.UG GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

noncomputable def redM {a b : Type} (A : Matrix a b L) : Matrix a b (Res L) := A.map redL

def IntM {a b : Type} (A : Matrix a b L) : Prop := ∀ i j, A i j ∈ intL L

theorem intM_mul {a b c : Type} [Fintype b] {A : Matrix a b L} {B : Matrix b c L} (hA : IntM A) (hB : IntM B) :
    IntM (A * B) := by
  intro i j; rw [Matrix.mul_apply]; exact Subring.sum_mem _ fun l _ => (intL L).mul_mem (hA i l) (hB l j)

theorem intM_cT {σ : L →+* L} (hσv : ∀ x, Valued.v (σ x) = Valued.v x) {a b : Type} {A : Matrix a b L}
    (hA : IntM A) : IntM (Formalism.UG.cT σ A) := by
  intro i j; show Valued.v (σ (A j i)) ≤ 1; rw [hσv]; exact hA j i

theorem redM_mul {a b c : Type} [Fintype b] {A : Matrix a b L} {B : Matrix b c L} (hA : IntM A) (hB : IntM B) :
    redM (A * B) = redM A * redM B := by
  ext i j
  simp only [redM, Matrix.map_apply, Matrix.mul_apply]
  rw [redL_sum _ _ fun l => (intL L).mul_mem (hA i l) (hB l j)]
  exact Finset.sum_congr rfl fun l _ => redL_mul (hA i l) (hB l j)

theorem redM_sub {a b : Type} {A B : Matrix a b L} (hA : IntM A) (hB : IntM B) :
    redM (A - B) = redM A - redM B := by
  ext i j; simp only [redM, Matrix.map_apply, Matrix.sub_apply]; exact redL_sub (hA i j) (hB i j)

theorem redM_cT (σ : L →+* L) (hσv : ∀ x, Valued.v (σ x) = Valued.v x) {a b : Type} {A : Matrix a b L}
    (hA : IntM A) : redM (Formalism.UG.cT σ A) = GlobalTheory.SgAlg.cT (sigK σ hσv) (redM A) := by
  ext i j
  show redL (σ (A j i)) = sigK σ hσv (redL (A j i))
  exact redL_sigma σ hσv (hA j i)

theorem redM_eq_zero_iff {ϖ : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    {a b : Type} {A : Matrix a b L} (hA : IntM A) : redM A = 0 ↔ ∀ i j, DvdPow ϖ 1 (A i j) := by
  constructor
  · intro h i j; rw [← redL_eq_zero_iff hϖ (hA i j)]; exact congrFun (congrFun h i) j
  · intro h; ext i j; exact (redL_eq_zero_iff hϖ (hA i j)).2 (h i j)

theorem redM_one {a : Type} [DecidableEq a] : redM (1 : Matrix a a L) = 1 := by
  ext i j
  simp only [redM, Matrix.map_apply, Matrix.one_apply]
  split_ifs
  · rw [redL_of_mem (intL L).one_mem]; exact map_one _
  · rw [redL_of_mem (intL L).zero_mem]; exact map_zero _

theorem free_redM {ϖ : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} {z : ι → Fin n → L} (hz : ∀ i r, z i r ∈ intL L)
    (hI : IndepMod ϖ z) : GlobalTheory.SgAlg.Free (redM (Matrix.of fun r i => z i r)) := by
  set X : Matrix (Fin n) ι (Res L) := redM (Matrix.of fun r i => z i r)
  have hinj : LinearMap.ker (Matrix.toLin' X) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro e he
    choose d hd hde using fun i => redL_surj (e i)
    have hs : ∀ r, DvdPow ϖ 1 (∑ i, d i * z i r) := by
      intro r
      rw [← redL_eq_zero_iff hϖ (Subring.sum_mem _ fun i _ => (intL L).mul_mem (hd i) (hz i r)),
        redL_sum _ _ fun i => (intL L).mul_mem (hd i) (hz i r)]
      have := congrFun he r
      rw [Matrix.toLin'_apply, Matrix.mulVec, dotProduct] at this
      rw [Pi.zero_apply] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [redL_mul (hd i) (hz i r), hde, mul_comm]; rfl
    have h0 := hI d hd hs
    funext i
    rw [← hde i]
    exact (redL_eq_zero_iff hϖ (hd i)).2 (h0 i)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' X) hinj
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have := congrArg LinearMap.toMatrix' hg
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this

theorem hform_eq_entry (σ : L →+* L) {n : ℕ} {ι : Type} (J : Matrix (Fin n) (Fin n) L) (z : ι → Fin n → L) (a b : ι) :
    Formalism.UG.hform σ J (z a) (z b) = (Formalism.UG.cT σ (Matrix.of fun r i => z i r) * J * Matrix.of fun r i => z i r) a b := by
  simp only [Formalism.UG.hform, Formalism.UG.cT, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]

end GlobalTheory.Hk3.ResWitt

namespace GlobalTheory.Hk3.ResWitt

open Formalism.UG GlobalTheory.Hk3.IntWitt

theorem exists_int_unitary_mod_of_gram_mod : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n' : ℕ) (JT : GL (Fin n') L),
    JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ (ι : Type) [Fintype ι] (z z' : ι → Fin n' → L), (∀ i r, z i r ∈ Formalism.UG.intL L) → (∀ i r, z' i r ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.IntWitt.IndepMod ϖ z → GlobalTheory.Hk3.IntWitt.IndepMod ϖ z' →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z' i) (z' j) -
      Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z i) (z j))) →
    ∃ g : Matrix (Fin n') (Fin n') L, (∀ i j, g i j ∈ Formalism.UG.intL L) ∧
      (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1
        ((Formalism.UG.cT σ g * (JT : Matrix (Fin n') (Fin n') L) * g - (JT : Matrix (Fin n') (Fin n') L)) i j)) ∧
      ∀ i r, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 ((g *ᵥ z i) r - z' i r) := by
  intro L _ _ ϖ σ q hU hq n' JT hJT hJh ι _ z z' hz hz' hI hI' hG
  classical
  have hσv : ∀ x, Valued.v (σ x) = Valued.v x := hU.2.1
  have hϖ := hU.2.2.2.1
  set J : Matrix (Fin n') (Fin n') L := (JT : Matrix (Fin n') (Fin n') L) with hJdef
  obtain ⟨g0, hg0⟩ := hJT
  have hJi : IntM J := by
    intro i j; rw [hJdef, ← hg0]; exact ((g0 : Matrix (Fin n') (Fin n') (intL L)) i j).2
  have hJinv : IntM ((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) := by
    intro i j; rw [← hg0, ← map_inv]; exact (((g0⁻¹ : GL (Fin n') (intL L)) : Matrix (Fin n') (Fin n') (intL L)) i j).2
  set X : Matrix (Fin n') ι L := Matrix.of fun r i => z i r with hXdef
  set X' : Matrix (Fin n') ι L := Matrix.of fun r i => z' i r with hX'def
  have hXi : IntM X := fun r i => hz i r
  have hX'i : IntM X' := fun r i => hz' i r

  have hHerm : GlobalTheory.SgAlg.IsHermU (sigK σ hσv) (redM J) := by
    refine ⟨?_, ?_⟩
    · rw [← redM_cT σ hσv hJi]; congr 1; ext i j; exact hJh j i
    · refine Matrix.isUnit_det_of_right_inverse (B := redM ((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L)) ?_
      rw [← redM_mul hJi hJinv, hJdef, ← Units.val_mul, mul_inv_cancel, Units.val_one, redM_one]
  have hgram : ∀ (Y : Matrix (Fin n') ι L), IntM Y →
      GlobalTheory.SgAlg.pairM (sigK σ hσv) (redM J) (redM Y) (redM Y) = redM (Formalism.UG.cT σ Y * J * Y) := by
    intro Y hY
    rw [redM_mul (intM_mul (intM_cT hσv hY) hJi) hY, redM_mul (intM_cT hσv hY) hJi, redM_cT σ hσv hY]
    rfl
  have hP : GlobalTheory.SgAlg.pairM (sigK σ hσv) (redM J) (redM X) (redM X) =
      GlobalTheory.SgAlg.pairM (sigK σ hσv) (redM J) (redM X') (redM X') := by
    rw [hgram X hXi, hgram X' hX'i]
    have hint : ∀ Y : Matrix (Fin n') ι L, IntM Y → IntM (Formalism.UG.cT σ Y * J * Y) :=
      fun Y hY => intM_mul (intM_mul (intM_cT hσv hY) hJi) hY
    have h0 : redM (Formalism.UG.cT σ X' * J * X' - Formalism.UG.cT σ X * J * X) = 0 := by
      rw [redM_eq_zero_iff hϖ (A := Formalism.UG.cT σ X' * J * X' - Formalism.UG.cT σ X * J * X) (fun i j => (intL L).sub_mem (hint X' hX'i i j) (hint X hXi i j))]
      intro a b
      have := hG a b
      rwa [hform_eq_entry, hform_eq_entry] at this
    rw [redM_sub (hint X' hX'i) (hint X hXi), sub_eq_zero] at h0
    exact h0.symm
  obtain ⟨gb, hgU, hgX⟩ := GlobalTheory.witt_free_tuples (sigK σ hσv) (isQA_sigK hU hq) (redM J) hHerm (redM X) (redM X')
    (free_redM hϖ hz hI) (free_redM hϖ hz' hI') hP
  choose g hgi hge using fun i j => redL_surj (gb i j)
  have hgI : IntM (Matrix.of g) := fun i j => hgi i j
  have hred : redM (Matrix.of g) = gb := by ext i j; exact hge i j
  refine ⟨Matrix.of g, hgi, ?_, ?_⟩
  · have hint1 : IntM (Formalism.UG.cT σ (Matrix.of g) * J * Matrix.of g) := intM_mul (intM_mul (intM_cT hσv hgI) hJi) hgI
    refine (redM_eq_zero_iff hϖ (A := Formalism.UG.cT σ (Matrix.of g) * J * Matrix.of g - J) (fun i j => (intL L).sub_mem (hint1 i j) (hJi i j))).1 ?_
    rw [redM_sub hint1 hJi, redM_mul (intM_mul (intM_cT hσv hgI) hJi) hgI, redM_mul (intM_cT hσv hgI) hJi,
      redM_cT σ hσv hgI, hred]
    exact sub_eq_zero.2 hgU
  · intro i r
    have hint2 : IntM (Matrix.of g * X) := intM_mul hgI hXi
    have h0 : redM (Matrix.of g * X - X') = 0 := by
      rw [redM_sub hint2 hX'i, redM_mul hgI hXi, hred, hgX, sub_self]
    have := (redM_eq_zero_iff hϖ (A := Matrix.of g * X - X') (fun i j => (intL L).sub_mem (hint2 i j) (hX'i i j))).1 h0 r i
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, hXdef, hX'def] using this

end GlobalTheory.Hk3.ResWitt
