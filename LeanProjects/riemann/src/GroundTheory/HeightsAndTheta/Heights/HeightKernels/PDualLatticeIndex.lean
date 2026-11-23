import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualLatticeIndex
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesIsLattice
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesGenIndexTrans
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesLatticeBasis
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesGenIndexDet
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesIdealLatticeFG
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BoxBounds
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField Matrix
open scoped nonZeroDivisors

noncomputable section

namespace DualLatticeIndexAlt

variable {K : Type} [Field K] [NumberField K] {i : ℕ}

def dual (L : Submodule (𝓞 K) (Fin i → K)) : Submodule (𝓞 K) (Fin i → K) where
  carrier := {φ | ∀ x ∈ L, φ ⬝ᵥ x ∈ (algebraMap (𝓞 K) K).range}
  add_mem' {φ ψ} hφ hψ x hx := by
    rw [add_dotProduct]
    exact add_mem (hφ x hx) (hψ x hx)
  zero_mem' x _ := by
    rw [zero_dotProduct]
    exact zero_mem _
  smul_mem' c φ hφ x hx := by
    obtain ⟨a, ha⟩ := hφ x hx
    refine ⟨c * a, ?_⟩
    show _ = (c • φ) ⬝ᵥ x
    rw [smul_dotProduct, Algebra.smul_def, map_mul, ha]

theorem mem_dual {L : Submodule (𝓞 K) (Fin i → K)} {φ : Fin i → K} :
    φ ∈ dual L ↔ ∀ x ∈ L, φ ⬝ᵥ x ∈ (algebraMap (𝓞 K) K).range := Iff.rfl

theorem dual_anti {L L' : Submodule (𝓞 K) (Fin i → K)} (h : L ≤ L') : dual L' ≤ dual L :=
  fun _ hφ x hx => hφ x (h hx)

theorem dual_toAddSubgroup (F : HermLattice K i) :
    (dual F.lattice).toAddSubgroup = (dualLattice F).toAddSubgroup := rfl

theorem mem_dual_sup {L : Submodule (𝓞 K) (Fin i → K)} {x₀ φ : Fin i → K} :
    φ ∈ dual (L ⊔ (𝓞 K) ∙ x₀) ↔ φ ∈ dual L ∧ φ ⬝ᵥ x₀ ∈ (algebraMap (𝓞 K) K).range := by
  constructor
  · intro h
    exact ⟨fun x hx => h x (le_sup_left (a := L) hx),
      h x₀ (le_sup_right (b := (𝓞 K) ∙ x₀) (Submodule.mem_span_singleton_self x₀))⟩
  · rintro ⟨h1, c, hc⟩ x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
    rw [dotProduct_add, dotProduct_smul]
    refine add_mem (h1 y hy) ⟨a * c, ?_⟩
    rw [map_mul, hc, Algebra.smul_def]

theorem absNorm_eq_index (I : Ideal (𝓞 K)) : Ideal.absNorm I = I.toAddSubgroup.index := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rfl

theorem mem_integralClosure_of_mem_range {y : K} (h : y ∈ (algebraMap (𝓞 K) K).range) :
    y ∈ integralClosure ℤ K := by
  obtain ⟨a, rfl⟩ := h
  exact RingOfIntegers.isIntegral_coe a

def pairInt (L : Submodule (𝓞 K) (Fin i → K)) (w : Fin i → K) (hw : w ∈ L) : dual L →ₗ[𝓞 K] 𝓞 K where
  toFun φ := (⟨(φ : Fin i → K) ⬝ᵥ w, mem_integralClosure_of_mem_range (mem_dual.mp φ.2 w hw)⟩ : 𝓞 K)
  map_add' φ ψ := RingOfIntegers.coe_injective (add_dotProduct (φ : Fin i → K) ψ w)
  map_smul' c φ := RingOfIntegers.coe_injective (by
    show ((c • φ : dual L) : Fin i → K) ⬝ᵥ w = algebraMap (𝓞 K) K c * ((φ : Fin i → K) ⬝ᵥ w)
    rw [Submodule.coe_smul, smul_dotProduct, Algebra.smul_def])

theorem coe_pairInt (L : Submodule (𝓞 K) (Fin i → K)) (w : Fin i → K) (hw : w ∈ L) (φ : dual L) :
    algebraMap (𝓞 K) K (pairInt L w hw φ) = (φ : Fin i → K) ⬝ᵥ w := rfl

theorem relIndex_eq_of_pair {M : Type*} [AddCommGroup M] [Module (𝓞 K) M] (P Q : Submodule (𝓞 K) M)
    (ψ : Q →ₗ[𝓞 K] 𝓞 K) (I : Ideal (𝓞 K)) (h : ∀ φ : Q, (φ : M) ∈ P ↔ ψ φ ∈ I) :
    P.toAddSubgroup.relIndex Q.toAddSubgroup =
      I.toAddSubgroup.relIndex (LinearMap.range ψ).toAddSubgroup := by
  have e : P.toAddSubgroup.addSubgroupOf Q.toAddSubgroup = I.toAddSubgroup.comap ψ.toAddMonoidHom := by
    ext φ
    exact h φ
  show (P.toAddSubgroup.addSubgroupOf Q.toAddSubgroup).index = _
  rw [e, AddSubgroup.index_comap, LinearMap.range_toAddSubgroup]

theorem dual_step (L : Submodule (𝓞 K) (Fin i → K)) (x₀ : Fin i → K)
    (hk : L.toAddSubgroup.relIndex (L ⊔ (𝓞 K) ∙ x₀).toAddSubgroup ≠ 0) :
    (dual (L ⊔ (𝓞 K) ∙ x₀)).toAddSubgroup.relIndex (dual L).toAddSubgroup ≤
      L.toAddSubgroup.relIndex (L ⊔ (𝓞 K) ∙ x₀).toAddSubgroup := by
  set k := L.toAddSubgroup.relIndex (L ⊔ (𝓞 K) ∙ x₀).toAddSubgroup with hk_def
  let a : Ideal (𝓞 K) := L.comap (LinearMap.toSpanSingleton (𝓞 K) (Fin i → K) x₀)
  have ha : Ideal.absNorm a = k := by
    rw [absNorm_eq_index]
    have e1 : a.toAddSubgroup =
        L.toAddSubgroup.comap (LinearMap.toSpanSingleton (𝓞 K) (Fin i → K) x₀).toAddMonoidHom := rfl
    rw [e1, AddSubgroup.index_comap, hk_def, Submodule.sup_toAddSubgroup, AddSubgroup.relIndex_sup_left,
      ← LinearMap.range_toAddSubgroup, ← LinearMap.span_singleton_eq_range]
  have ha0 : a ≠ ⊥ := fun h => hk (by rw [← ha, Ideal.absNorm_eq_zero_iff]; exact h)
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ha0
  have hw : d • x₀ ∈ L := hd
  let ψ := pairInt L (d • x₀) hw
  have hdK : algebraMap (𝓞 K) K d ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hd0
  have key : ∀ φ : dual L, (φ : Fin i → K) ∈ dual (L ⊔ (𝓞 K) ∙ x₀) ↔ ψ φ ∈ Ideal.span {d} := by
    intro φ
    rw [mem_dual_sup, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨-, c, hc⟩
      refine ⟨c, RingOfIntegers.coe_injective ?_⟩
      rw [map_mul, coe_pairInt, dotProduct_smul, Algebra.smul_def, hc, mul_comm]
    · rintro ⟨c, hc⟩
      refine ⟨φ.2, c, ?_⟩
      have h1 := congrArg (algebraMap (𝓞 K) K) hc
      rw [map_mul, coe_pairInt, dotProduct_smul, Algebra.smul_def] at h1
      exact mul_right_cancel₀ hdK (h1.trans (mul_comm _ _))
  have hidx := relIndex_eq_of_pair _ _ ψ _ key
  let b : Ideal (𝓞 K) := LinearMap.range ψ ⊔ Ideal.span {d}
  have hsup : (Ideal.span {d}).toAddSubgroup.relIndex (LinearMap.range ψ).toAddSubgroup =
      (Ideal.span {d}).toAddSubgroup.relIndex b.toAddSubgroup := by
    rw [Submodule.sup_toAddSubgroup, AddSubgroup.relIndex_sup_right]
  have hdb : Ideal.span {d} ≤ b := le_sup_right
  have htower : (Ideal.span {d}).toAddSubgroup.relIndex b.toAddSubgroup * Ideal.absNorm b =
      Ideal.absNorm (Ideal.span {d}) := by
    rw [absNorm_eq_index, absNorm_eq_index, ← AddSubgroup.relIndex_top_right,
      ← AddSubgroup.relIndex_top_right]
    exact AddSubgroup.relIndex_mul_relIndex _ _ _
      (show (Ideal.span {d}).toAddSubgroup ≤ b.toAddSubgroup from hdb) le_top
  have hmul : b * a ≤ Ideal.span {d} := by
    rw [Ideal.mul_le]
    intro r hr s hs
    obtain ⟨y, ⟨φ, rfl⟩, z, hz, rfl⟩ := Submodule.mem_sup.mp hr
    rw [add_mul]
    refine add_mem ?_ (Ideal.mul_mem_right _ _ hz)
    have hs' : s • x₀ ∈ L := hs
    obtain ⟨e, he⟩ := mem_dual.mp φ.2 (s • x₀) hs'
    rw [Ideal.mem_span_singleton']
    refine ⟨e, RingOfIntegers.coe_injective ?_⟩
    rw [map_mul, map_mul, coe_pairInt, he]
    simp only [dotProduct_smul, Algebra.smul_def]
    ring
  have hdvd : Ideal.absNorm (Ideal.span {d}) ∣ Ideal.absNorm b * Ideal.absNorm a := by
    rw [← map_mul]
    exact Ideal.absNorm_dvd_absNorm_of_le hmul
  have hb0 : Ideal.absNorm b ≠ 0 := by
    intro h
    rw [Ideal.absNorm_eq_zero_iff] at h
    have h2 := hdb
    rw [h, le_bot_iff, Ideal.span_singleton_eq_bot] at h2
    exact hd0 h2
  rw [hidx, hsup]
  have hle : Ideal.absNorm (Ideal.span {d}) ≤ Ideal.absNorm b * k := by
    rw [← ha]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero (mul_ne_zero hb0 (by rw [ha]; exact hk))) hdvd
  rw [← htower, mul_comm (Ideal.absNorm b)] at hle
  exact Nat.le_of_mul_le_mul_right hle (Nat.pos_of_ne_zero hb0)

theorem dual_index_le (n : ℕ) : ∀ (L' L : Submodule (𝓞 K) (Fin i → K)), L' ≤ L →
    L'.toAddSubgroup.relIndex L.toAddSubgroup = n → n ≠ 0 →
      (dual L).toAddSubgroup.relIndex (dual L').toAddSubgroup ≤ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro L' L hle hn hn0
  by_cases hLL : L ≤ L'
  · have h := le_antisymm hle hLL
    subst h
    rw [AddSubgroup.relIndex_self] at hn
    rw [AddSubgroup.relIndex_self]
    omega
  · obtain ⟨x₀, hx₀L, hx₀⟩ := SetLike.not_le_iff_exists.mp hLL
    have h1 : L' ≤ L' ⊔ (𝓞 K) ∙ x₀ := le_sup_left
    have h2 : L' ⊔ (𝓞 K) ∙ x₀ ≤ L := sup_le hle ((Submodule.span_singleton_le_iff_mem _ _).mpr hx₀L)
    have htow := AddSubgroup.relIndex_mul_relIndex _ _ _
      (show L'.toAddSubgroup ≤ (L' ⊔ (𝓞 K) ∙ x₀).toAddSubgroup from h1)
      (show (L' ⊔ (𝓞 K) ∙ x₀).toAddSubgroup ≤ L.toAddSubgroup from h2)
    rw [hn] at htow
    have hk1 : L'.toAddSubgroup.relIndex (L' ⊔ (𝓞 K) ∙ x₀).toAddSubgroup ≠ 1 := by
      rw [Ne, AddSubgroup.relIndex_eq_one]
      intro h
      exact hx₀ (h (show x₀ ∈ L' ⊔ (𝓞 K) ∙ x₀ from
        le_sup_right (a := L') (Submodule.mem_span_singleton_self x₀)))
    set k := L'.toAddSubgroup.relIndex (L' ⊔ (𝓞 K) ∙ x₀).toAddSubgroup with hk
    set m := (L' ⊔ (𝓞 K) ∙ x₀).toAddSubgroup.relIndex L.toAddSubgroup with hm
    have hk0 : k ≠ 0 := fun h => hn0 (by rw [← htow, h, zero_mul])
    have hm0 : m ≠ 0 := fun h => hn0 (by rw [← htow, h, mul_zero])
    have hmn : m < n := by
      rw [← htow]
      have : 2 ≤ k := by omega
      have : 0 < m := Nat.pos_of_ne_zero hm0
      nlinarith
    have hA := ih m hmn _ L h2 hm.symm hm0
    have hB := dual_step L' x₀ hk0
    have hD := AddSubgroup.relIndex_mul_relIndex _ _ _
      (show (dual L).toAddSubgroup ≤ (dual (L' ⊔ (𝓞 K) ∙ x₀)).toAddSubgroup from dual_anti h2)
      (show (dual (L' ⊔ (𝓞 K) ∙ x₀)).toAddSubgroup ≤ (dual L').toAddSubgroup from dual_anti h1)
    rw [← hD, ← htow, mul_comm k m]
    exact Nat.mul_le_mul hA hB

def box (c : K) : Submodule (𝓞 K) (Fin i → K) := Submodule.pi Set.univ fun _ => (𝓞 K) ∙ c

theorem mem_box {c : K} {x : Fin i → K} : x ∈ box c ↔ ∀ j, ∃ a : 𝓞 K, a • c = x j := by
  simp only [box, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_span_singleton]

theorem dual_box {c : K} (hc : c ≠ 0) : dual (box (i := i) c) = box c⁻¹ := by
  ext φ
  rw [mem_dual, mem_box]
  constructor
  · intro h j
    have hx : (Pi.single j c : Fin i → K) ∈ box c := by
      rw [mem_box]
      intro l
      by_cases hl : l = j
      · subst hl
        exact ⟨1, by simp⟩
      · exact ⟨0, by simp [hl]⟩
    obtain ⟨a, ha⟩ := h _ hx
    rw [dotProduct_single] at ha
    refine ⟨a, ?_⟩
    rw [Algebra.smul_def, ha, mul_assoc, mul_inv_cancel₀ hc, mul_one]
  · intro h x hx
    rw [mem_box] at hx
    choose a ha using h
    choose b hb using hx
    refine ⟨∑ j, a j * b j, ?_⟩
    rw [map_sum, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← ha j, ← hb j, Algebra.smul_def, Algebra.smul_def, map_mul]
    field_simp

theorem box_le_box {c c' : K} (a : 𝓞 K) (h : c = algebraMap (𝓞 K) K a * c') : box (i := i) c ≤ box c' := by
  intro x hx
  rw [mem_box] at hx ⊢
  intro j
  obtain ⟨b, hb⟩ := hx j
  exact ⟨b * a, by rw [← hb, h, Algebra.smul_def, Algebra.smul_def, map_mul, mul_assoc]⟩

theorem exists_box_le (L : Submodule (𝓞 K) (Fin i → K))
    (hL : Submodule.span K (L : Set (Fin i → K)) = ⊤) :
    ∃ e : 𝓞 K, e ≠ 0 ∧ box (algebraMap (𝓞 K) K e) ≤ L :=
  _root_.UpperTheory.Reformulated.B.BoxBounds.exists_box_le L hL

theorem exists_common_denom {T : Type*} [Fintype T] (y : T → K) :
    ∃ e : 𝓞 K, e ≠ 0 ∧ ∀ t, algebraMap (𝓞 K) K e * y t ∈ (algebraMap (𝓞 K) K).range := by
  classical
  choose p q hq hpq using fun t => IsFractionRing.div_surjective (A := 𝓞 K) (y t)
  refine ⟨∏ t, q t, Finset.prod_ne_zero_iff.mpr fun t _ => nonZeroDivisors.ne_zero (hq t), fun t => ?_⟩
  refine ⟨(∏ l ∈ Finset.univ.erase t, q l) * p t, ?_⟩
  have hqK : algebraMap (𝓞 K) K (q t) ≠ 0 :=
    RingOfIntegers.coe_ne_zero_iff.mpr (nonZeroDivisors.ne_zero (hq t))
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ t), map_mul, map_mul, ← hpq t]
  field_simp

theorem exists_le_box (L : Submodule (𝓞 K) (Fin i → K)) (hL : L.FG) :
    ∃ e : 𝓞 K, e ≠ 0 ∧ L ≤ box (algebraMap (𝓞 K) K e)⁻¹ := by
  obtain ⟨s, rfl⟩ := hL
  obtain ⟨e, he0, he⟩ := exists_common_denom (fun t : s × Fin i => (t.1 : Fin i → K) t.2)
  have heK : algebraMap (𝓞 K) K e ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr he0
  refine ⟨e, he0, Submodule.span_le.mpr fun g hg => ?_⟩
  rw [SetLike.mem_coe, mem_box]
  intro j
  obtain ⟨a, ha⟩ := he (⟨g, Finset.mem_coe.mp hg⟩, j)
  refine ⟨a, ?_⟩
  rw [Algebra.smul_def, ha]
  field_simp

theorem box_relIndex_ne_zero {c : K} (hc : c ≠ 0) :
    (box (i := i) c).toAddSubgroup.relIndex (box c⁻¹).toAddSubgroup ≠ 0 := by
  have hid : ∀ c : K, box (i := i) c =
      idealLattice (fun _ : Fin i => FractionalIdeal.spanSingleton (𝓞 K)⁰ c) := fun c => by
    simp only [box, idealLattice, FractionalIdeal.coe_spanSingleton]
  have lat : ∀ c : K, c ≠ 0 → Submodule.IsLattice ℚ ((box (i := i) c).restrictScalars ℤ) := by
    intro c hc
    obtain ⟨hfg, hspan⟩ := LinesIdealLatticeFG.proof K i (fun _ => FractionalIdeal.spanSingleton (𝓞 K)⁰ c)
      (fun _ => by rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact hc)
    rw [← hid] at hfg hspan
    exact LinesIsLattice.proof K (Fin i) (box c) (hfg.restrictScalars) hspan
  have hpos := (LinesGenIndexTrans.proof LinesLatticeBasis.proof
    (LinesGenIndexDet.proof LinesLatticeBasis.proof) (Fin i → K)
    ((box (i := i) c⁻¹).restrictScalars ℤ) ((box c).restrictScalars ℤ) ((box c).restrictScalars ℤ)
    (lat _ (inv_ne_zero hc)) (lat c hc) (lat c hc)).1
  intro h0
  have e1 : ((box (i := i) c).restrictScalars ℤ).toAddSubgroup = (box (i := i) c).toAddSubgroup := rfl
  have e2 : ((box (i := i) c⁻¹).restrictScalars ℤ).toAddSubgroup = (box (i := i) c⁻¹).toAddSubgroup := rfl
  rw [genIndex, e1, e2, h0, Nat.cast_zero, zero_div] at hpos
  exact lt_irrefl _ hpos

theorem eq_of_le_of_prod {a₁ a₂ a₃ b₁ b₂ b₃ : ℕ} (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) (h₃ : a₃ ≤ b₃)
    (h : a₁ * a₂ * a₃ = b₁ * b₂ * b₃) (h₀ : b₁ * b₂ * b₃ ≠ 0) : a₂ = b₂ := by
  rcases lt_or_eq_of_le h₂ with hlt | heq
  · exfalso
    have hb₁ : 0 < b₁ := Nat.pos_of_ne_zero fun h' => h₀ (by rw [h', zero_mul, zero_mul])
    have hb₃ : 0 < b₃ := Nat.pos_of_ne_zero fun h' => h₀ (by rw [h', mul_zero])
    have hle : a₁ * a₂ * a₃ ≤ b₁ * a₂ * b₃ := Nat.mul_le_mul (Nat.mul_le_mul h₁ le_rfl) h₃
    have hlt' : b₁ * a₂ * b₃ < b₁ * b₂ * b₃ :=
      Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_left hlt hb₁) hb₃
    omega
  · exact heq

end DualLatticeIndexAlt

open DualLatticeIndexAlt in

theorem DualLatticeIndex.proof : DualLatticeIndex.Statement := by
  intro K _ _ i F F' hle
  obtain ⟨e₁, he₁, hlo⟩ := exists_box_le F'.lattice F'.span_eq
  obtain ⟨e₂, he₂, hhi⟩ := exists_le_box F.lattice F.fg
  have h₁ : algebraMap (𝓞 K) K e₁ ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr he₁
  have h₂ : algebraMap (𝓞 K) K e₂ ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr he₂
  set c : K := algebraMap (𝓞 K) K (e₁ * e₂) with hc_def
  have hc : c ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr (mul_ne_zero he₁ he₂)
  have hLo : box c ≤ F'.lattice := (box_le_box e₂ (by rw [hc_def, map_mul, mul_comm])).trans hlo
  have hHi : F.lattice ≤ box c⁻¹ :=
    hhi.trans (box_le_box e₁ (by rw [hc_def, map_mul]; field_simp))
  have hdLo : dual (box (i := i) c) = box c⁻¹ := dual_box hc
  have hdHi : dual (box (i := i) c⁻¹) = box c := by rw [dual_box (inv_ne_zero hc), inv_inv]
  have hN := box_relIndex_ne_zero (i := i) hc
  have t1 := AddSubgroup.relIndex_mul_relIndex _ _ _
    (show (box c).toAddSubgroup ≤ F'.lattice.toAddSubgroup from hLo)
    (show F'.lattice.toAddSubgroup ≤ F.lattice.toAddSubgroup from hle)
  have t2 := AddSubgroup.relIndex_mul_relIndex _ _ _
    (show (box c).toAddSubgroup ≤ F.lattice.toAddSubgroup from hLo.trans hle)
    (show F.lattice.toAddSubgroup ≤ (box c⁻¹).toAddSubgroup from hHi)
  have s1 := AddSubgroup.relIndex_mul_relIndex _ _ _
    (show (dual (box c⁻¹)).toAddSubgroup ≤ (dual F.lattice).toAddSubgroup from dual_anti hHi)
    (show (dual F.lattice).toAddSubgroup ≤ (dual F'.lattice).toAddSubgroup from dual_anti hle)
  have s2 := AddSubgroup.relIndex_mul_relIndex _ _ _
    (show (dual (box c⁻¹)).toAddSubgroup ≤ (dual F'.lattice).toAddSubgroup from
      dual_anti (hle.trans hHi))
    (show (dual F'.lattice).toAddSubgroup ≤ (dual (box c)).toAddSubgroup from dual_anti hLo)
  rw [hdLo, hdHi] at s2
  rw [hdHi] at s1
  set b₁ := (box c).toAddSubgroup.relIndex F'.lattice.toAddSubgroup
  set b₂ := F'.lattice.toAddSubgroup.relIndex F.lattice.toAddSubgroup
  set b₃ := F.lattice.toAddSubgroup.relIndex (box c⁻¹).toAddSubgroup
  have hb : b₁ * b₂ * b₃ = (box (i := i) c).toAddSubgroup.relIndex (box c⁻¹).toAddSubgroup := by rw [t1, t2]
  have hb0 : b₁ * b₂ * b₃ ≠ 0 := by rw [hb]; exact hN
  have hb₁ : b₁ ≠ 0 := fun h => hb0 (by rw [h, zero_mul, zero_mul])
  have hb₂ : b₂ ≠ 0 := fun h => hb0 (by rw [h, mul_zero, zero_mul])
  have hb₃ : b₃ ≠ 0 := fun h => hb0 (by rw [h, mul_zero])
  have a₁ := dual_index_le b₁ _ _ hLo rfl hb₁
  have a₂ := dual_index_le b₂ _ _ hle rfl hb₂
  have a₃ := dual_index_le b₃ _ _ hHi rfl hb₃
  rw [hdLo] at a₁
  rw [hdHi] at a₃
  have hprod : (dual F'.lattice).toAddSubgroup.relIndex (box c⁻¹).toAddSubgroup *
      (dual F.lattice).toAddSubgroup.relIndex (dual F'.lattice).toAddSubgroup *
      (box (i := i) c).toAddSubgroup.relIndex (dual F.lattice).toAddSubgroup = b₁ * b₂ * b₃ := by
    rw [hb, ← s2, ← s1]
    ring
  rw [← dual_toAddSubgroup, ← dual_toAddSubgroup]
  exact eq_of_le_of_prod a₁ a₂ a₃ hprod hb0

example : (dualLattice (HermLattice.standard ℚ 1)).toAddSubgroup.relIndex
      (dualLattice HermLattice.twiceStandardExample).toAddSubgroup =
    HermLattice.twiceStandardExample.lattice.toAddSubgroup.relIndex
      (HermLattice.standard ℚ 1).lattice.toAddSubgroup :=
  DualLatticeIndex.proof ℚ 1 _ _ twiceStandardExample_le

end

end GroundTheory.Heights₂.Heights
