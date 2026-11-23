import Mathlib
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ExampleSatisfiesConditionsAtFive
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CharIdem
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.IndexUBound
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MirabIndex
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.IsMackeyPiUpperUnipotentProdCharacter
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnipVal

open Module NumberField IsDedekindDomain CategoryTheory

namespace Formalism.L2.Indef.Tree

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem vw_level (w : HeightOneSpectrum (𝓞 K)) {g1 g2 : ℕ} (h1 : g1.Prime) (h2 : g2.Prime) (h12 : g1 ≠ g2) (a : ℕ) :
    (vw w (((g1 ^ a * g2 ^ a : ℕ)) : K) : ℝ) =
      (ramw w : ℝ) * (if plc w = g1 ∨ plc w = g2 then (a : ℝ) else 0) :=
  (unipVal K w).2 g1 g2 a h1 h2 h12

section Level

variable {ι : Type} [Fintype ι] [DecidableEq ι] (kf : ι → Type) [∀ v, Field (kf v)] [∀ v, Fintype (kf v)] (n : ℕ)

def IsLevelGroups (Pm : ∀ v, Subgroup (GL (Fin (n + 1)) (kf v))) (Uv : ∀ v, Subgroup (Pm v)) : Prop :=
  (∀ v (h : GL (Fin (n + 1)) (kf v)), h ∈ Pm v ↔ IsMirab (h : Matrix (Fin (n + 1)) (Fin (n + 1)) (kf v))) ∧
  ∀ v (h : Pm v), h ∈ Uv v ↔ IsUniU ((h : GL (Fin (n + 1)) (kf v)) : Matrix (Fin (n + 1)) (Fin (n + 1)) (kf v))

def IsGenericChar (χ : ∀ v, AddChar (kf v) (𝓞 K)) : Prop := ∀ v, χ v ≠ 1

def psiU (χ : ∀ v, AddChar (kf v) (𝓞 K)) (Pm : ∀ v, Subgroup (GL (Fin (n + 1)) (kf v))) : (∀ v, Pm v) → 𝓞 K :=
  fun h => ∏ v, χ v (supd (((h v : Pm v) : GL (Fin (n + 1)) (kf v)) : Matrix (Fin (n + 1)) (Fin (n + 1)) (kf v)))

end Level

section Ties

variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {c : OnConst}
variable {ι : Type} [Fintype ι] [DecidableEq ι] {kf : ι → Type} [∀ v, Field (kf v)] [∀ v, Fintype (kf v)] {n : ℕ}

def TieU {Pm : ∀ v, Subgroup (GL (Fin (n + 1)) (kf v))} (O : OnObj S (∀ v, Pm v) c) (Uv : ∀ v, Subgroup (Pm v)) : Prop :=
  O.U = Subgroup.pi Set.univ Uv

def TiePsi {Pm : ∀ v, Subgroup (GL (Fin (n + 1)) (kf v))} (O : OnObj S (∀ v, Pm v) c) (χ : ∀ v, AddChar (kf v) (𝓞 K)) :
    Prop :=
  O.ψ = psiU kf n χ Pm

def TieLevelNum {P : Type} [Group P] [Finite P] (O : OnObj S P c) (n fN : ℕ) : Prop :=
  O.f = (fN : ℝ) ∧ O.rr = (n : ℝ) + 1

def LeafLevelSq {P : Type} [Group P] [Finite P] (O : OnObj S P c) (kf : ι → Type) [∀ v, Field (kf v)] [∀ v, Fintype (kf v)]
    (fN : ℕ) : Prop :=
  O.g1.Prime ∧ O.g2.Prime ∧ O.g1 ≠ O.g2 ∧ (∀ v, Fintype.card (kf v) = O.g1 ∨ Fintype.card (kf v) = O.g2) ∧
    (Finset.univ.filter fun v => Fintype.card (kf v) = O.g1).card = fN ∧
    (Finset.univ.filter fun v => Fintype.card (kf v) = O.g2).card = fN

def LeafYBound {P : Type} [Group P] [Finite P] (O : OnObj S P c) : Prop :=
  2 * O.f / (((min O.g1 O.g2 : ℕ) : ℝ) - 1) ≤ O.y

end Ties

section Orders

variable {ι : Type} [Fintype ι] [DecidableEq ι] {kf : ι → Type} [∀ v, Field (kf v)] [∀ v, Fintype (kf v)] {n : ℕ}
variable {Pm : ∀ v, Subgroup (GL (Fin (n + 1)) (kf v))} {Uv : ∀ v, Subgroup (Pm v)}

theorem card_Uv_uni (hG : IsLevelGroups kf n Pm Uv) (v : ι) :
    Nat.card (Uv v) =
      Nat.card {u : GL (Fin (n + 1)) (kf v) // PI.MirabIndex.IsUniU (u : Matrix (Fin (n + 1)) (Fin (n + 1)) (kf v))} :=
  Nat.card_congr
    { toFun := fun h => ⟨((h : Pm v) : GL (Fin (n + 1)) (kf v)), (hG.2 v h).1 h.2⟩
      invFun := fun u => ⟨⟨u.1, (hG.1 v u.1).2 (isMirab_of_isUniU _ u.2)⟩, (hG.2 v _).2 u.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_Uv (hG : IsLevelGroups kf n Pm Uv) (v : ι) :
    Nat.card (Uv v) = Fintype.card (kf v) ^ ((n + 1) * n / 2) := by
  rw [card_Uv_uni hG v, PI.MirabolicIndex₂.card_uni]

theorem card_Pm (hG : IsLevelGroups kf n Pm Uv) (v : ι) :
    Nat.card (Pm v) = Nat.card (Uv v) * ∏ i ∈ Finset.Ico 1 (n + 1), (Fintype.card (kf v) ^ i - 1) := by
  rw [card_Uv_uni hG v, ← mirabolic_index (kf v) n]
  exact Nat.card_congr (Equiv.subtypeEquivRight (hG.1 v))

theorem index_Uv (hG : IsLevelGroups kf n Pm Uv) (v : ι) :
    (Uv v).index = ∏ i ∈ Finset.Ico 1 (n + 1), (Fintype.card (kf v) ^ i - 1) := by
  have h1 := Subgroup.card_mul_index (Uv v)
  rw [card_Pm hG v] at h1
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1

theorem card_piU : Nat.card (Subgroup.pi Set.univ Uv) = ∏ v, Nat.card (Uv v) := by
  rw [← Nat.card_pi]
  exact Nat.card_congr
    { toFun := fun x v => ⟨x.1 v, (Subgroup.mem_pi _).mp x.2 v (Set.mem_univ v)⟩
      invFun := fun y => ⟨fun v => (y v).1, (Subgroup.mem_pi _).mpr fun v _ => (y v).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem index_piU (hG : IsLevelGroups kf n Pm Uv) :
    (Subgroup.pi Set.univ Uv).index = ∏ v, ∏ i ∈ Finset.Ico 1 (n + 1), (Fintype.card (kf v) ^ i - 1) := by
  have h1 := Subgroup.card_mul_index (Subgroup.pi Set.univ Uv)
  rw [Nat.card_pi] at h1
  simp only [card_Pm hG] at h1
  rw [Finset.prod_mul_distrib, ← card_piU] at h1
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1

theorem card_piU_eq (hG : IsLevelGroups kf n Pm Uv) :
    Nat.card (Subgroup.pi Set.univ Uv) = ∏ v, Fintype.card (kf v) ^ ((n + 1) * n / 2) := by
  rw [card_piU]
  exact Finset.prod_congr rfl fun v _ => card_Uv hG v

end Orders

section Discharge

variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {c : OnConst}
variable {ι : Type} [Fintype ι] [DecidableEq ι] {kf : ι → Type} [∀ v, Field (kf v)] [∀ v, Fintype (kf v)] {n : ℕ}
variable {Pm : ∀ v, Subgroup (GL (Fin (n + 1)) (kf v))} {Uv : ∀ v, Subgroup (Pm v)}

theorem leafMackey_of (O : OnObj S (∀ v, Pm v) c) (χ : ∀ v, AddChar (kf v) (𝓞 K))
    (hG : IsLevelGroups kf n Pm Uv) (hχ : IsGenericChar kf χ) (hU : TieU O Uv) (hψ : TiePsi O χ) : LeafMackey O := by
  unfold LeafMackey
  rw [hU, hψ]
  exact isMackey_pi_upper_unipotent_prod_character K ι kf n χ hχ Pm Uv hG.1 hG.2

theorem sum_inv_le_y {P : Type} [Group P] [Finite P] (O : OnObj S P c) (fN : ℕ) (hSq : LeafLevelSq O kf fN)
    (hf : O.f = (fN : ℝ)) (hY : LeafYBound O) :
    ∑ v, 1 / ((Fintype.card (kf v) : ℝ) - 1) ≤ O.y := by
  classical
  obtain ⟨hp1, hp2, h12, hor, hc1, hc2⟩ := hSq
  have hY2 : (2 : ℝ) ≤ ((min O.g1 O.g2 : ℕ) : ℝ) := by
    have : 2 ≤ min O.g1 O.g2 := le_min hp1.two_le hp2.two_le
    exact_mod_cast this
  have hle : ∀ v, 1 / ((Fintype.card (kf v) : ℝ) - 1) ≤ 1 / (((min O.g1 O.g2 : ℕ) : ℝ) - 1) := by
    intro v
    have hYv : ((min O.g1 O.g2 : ℕ) : ℝ) ≤ (Fintype.card (kf v) : ℝ) := by
      have : min O.g1 O.g2 ≤ Fintype.card (kf v) := by
        rcases hor v with h | h <;> rw [h]
        · exact min_le_left _ _
        · exact min_le_right _ _
      exact_mod_cast this
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  have hcard : (Finset.univ : Finset ι).card = 2 * fN := by
    have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset ι))
      (fun v => Fintype.card (kf v) = O.g1)
    have hfilt : (Finset.univ.filter fun v => ¬ Fintype.card (kf v) = O.g1) =
        (Finset.univ.filter fun v => Fintype.card (kf v) = O.g2) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h; exact (hor v).resolve_left h
      · intro h h'; exact h12 (h'.symm.trans h)
    rw [hfilt, hc1, hc2] at hsplit
    omega
  calc ∑ v, 1 / ((Fintype.card (kf v) : ℝ) - 1) ≤ ∑ _v : ι, 1 / (((min O.g1 O.g2 : ℕ) : ℝ) - 1) :=
        Finset.sum_le_sum fun v _ => hle v
    _ = 2 * O.f / (((min O.g1 O.g2 : ℕ) : ℝ) - 1) := by
      rw [Finset.sum_const, nsmul_eq_mul, hcard, hf]
      push_cast
      ring
    _ ≤ O.y := hY

theorem leafIndexU_of (O : OnObj S (∀ v, Pm v) c) (fN : ℕ) (hG : IsLevelGroups kf n Pm Uv)
    (hSq : LeafLevelSq O kf fN) (hY : LeafYBound O) (hU : TieU O Uv) (hN : TieLevelNum O n fN) : LeafIndexU O := by
  unfold LeafIndexU
  rw [hU, index_piU hG, card_piU_eq hG]
  have hsum := sum_inv_le_y O fN hSq hN.1 hY
  have hB := product_lowerBound ι Finset.univ (fun v => Fintype.card (kf v)) (n + 1) O.y
    (fun v _ => Fintype.one_lt_card) hsum
  simp only [Nat.add_sub_cancel] at hB
  have hcast : ((∏ v, ∏ i ∈ Finset.Ico 1 (n + 1), (Fintype.card (kf v) ^ i - 1) : ℕ) : ℝ) =
      ∏ v, ∏ i ∈ Finset.Ico 1 (n + 1), ((Fintype.card (kf v) : ℝ) ^ i - 1) := by
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Nat.cast_sub (Nat.one_le_pow _ _ Fintype.card_pos)]
    push_cast
    ring
  rw [hcast]
  push_cast
  exact hB

theorem card_piU_level (hG : IsLevelGroups kf n Pm Uv) (g1 g2 fN : ℕ) (h12 : g1 ≠ g2)
    (hor : ∀ v, Fintype.card (kf v) = g1 ∨ Fintype.card (kf v) = g2)
    (hc1 : (Finset.univ.filter fun v => Fintype.card (kf v) = g1).card = fN)
    (hc2 : (Finset.univ.filter fun v => Fintype.card (kf v) = g2).card = fN) :
    Nat.card (Subgroup.pi Set.univ Uv) = g1 ^ ((n + 1) * n / 2 * fN) * g2 ^ ((n + 1) * n / 2 * fN) := by
  classical
  rw [card_piU_eq hG, ← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun v => Fintype.card (kf v) = g1)]
  have hfilt : (Finset.univ.filter fun v => ¬ Fintype.card (kf v) = g1) =
      (Finset.univ.filter fun v => Fintype.card (kf v) = g2) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; exact (hor v).resolve_left h
    · intro h h'; exact h12 (h'.symm.trans h)
  rw [hfilt]
  have e1 : ∏ v ∈ Finset.univ.filter (fun v => Fintype.card (kf v) = g1), Fintype.card (kf v) ^ ((n + 1) * n / 2) =
      ∏ _v ∈ Finset.univ.filter (fun v => Fintype.card (kf v) = g1), g1 ^ ((n + 1) * n / 2) :=
    Finset.prod_congr rfl fun v hv => by rw [(Finset.mem_filter.mp hv).2]
  have e2 : ∏ v ∈ Finset.univ.filter (fun v => Fintype.card (kf v) = g2), Fintype.card (kf v) ^ ((n + 1) * n / 2) =
      ∏ _v ∈ Finset.univ.filter (fun v => Fintype.card (kf v) = g2), g2 ^ ((n + 1) * n / 2) :=
    Finset.prod_congr rfl fun v hv => by rw [(Finset.mem_filter.mp hv).2]
  rw [e1, e2, Finset.prod_const, Finset.prod_const, hc1, hc2, ← pow_mul, ← pow_mul]

theorem leafUnip_of (O : OnObj S (∀ v, Pm v) c) (fN : ℕ) (hG : IsLevelGroups kf n Pm Uv)
    (hSq : LeafLevelSq O kf fN) (hU : TieU O Uv) (hN : TieLevelNum O n fN) : LeafUnip O := by
  obtain ⟨hp1, hp2, h12, hor, hc1, hc2⟩ := hSq
  obtain ⟨hf, hr⟩ := hN
  refine ⟨by rw [hr]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)], fun w _ => ?_⟩
  rw [hU, card_piU_level hG O.g1 O.g2 fN h12 hor hc1 hc2, vw_level w hp1 hp2 h12, hf, hr]
  have hev : 2 ∣ (n + 1) * n := by
    have := Nat.even_mul_succ_self n
    rw [mul_comm] at this
    exact even_iff_two_dvd.mp this
  have hT : (((n + 1) * n / 2 : ℕ) : ℝ) = ((n : ℝ) + 1) * n / 2 := by
    rw [Nat.cast_div hev (by norm_num)]
    push_cast
    ring
  congr 1
  split_ifs
  · push_cast
    rw [hT]
    ring
  · rfl

def IsTypeList {G : Type} [Group G] [Fintype G] {τ : Type} (V : τ → FDRep ℂ G) : Prop :=
  (∀ t, Simple (V t)) ∧ ∀ t u, t ≠ u → IsEmpty (V t ≅ V u)

def IsGoodIdem {G : Type} [Group G] [Fintype G] (σ : K →+* ℂ) {τ : Type} [Fintype τ] (V : τ → FDRep ℂ G)
    (ε : MonoidAlgebra K G) : Prop :=
  MonoidAlgebra.mapRingHom G σ ε = ∑ t, PI.CharIdem.charIdem (V t)

def TieProj {G : Type} [Group G] {P : Type} [Group P] [Finite P] (O : OnObj S P c)
    (ρG : ∀ j, Representation K G (Fin (O.nZ j) → K)) (ε : Bs.J → MonoidAlgebra K G) : Prop :=
  ∀ j, O.e j = (ρG j).asAlgebraHom (ε j) ∧ O.V₀ j = LinearMap.range (O.e j)

end Discharge

section Builder

variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {c : OnConst}

abbrev regroup {P' : Type} [Group P'] [Finite P'] (T : OnObj S P' c) (P : Type) [Group P] [Finite P]
    (ρ : ∀ j, Representation K P (Fin (T.nZ j) → K)) (U : Subgroup P) (ψ : P → 𝓞 K)
    (V₀ : ∀ j, Submodule K (Fin (T.nZ j) → K)) (e : ∀ j, (Fin (T.nZ j) → K) →ₗ[K] (Fin (T.nZ j) → K))
    (f rr k : ℝ) (g1 g2 : ℕ) : OnObj S P c where
  nZ := T.nZ
  ρ := ρ
  U := U
  ψ := ψ
  V₀ := V₀
  e := e
  Ms := T.Ms
  φ := T.φ
  Th1 := T.Th1
  Th := T.Th
  ThK := T.ThK
  Th0 := T.Th0
  ThJ := T.ThJ
  X₃ := T.X₃
  σ := T.σ
  a := T.a
  E := T.E
  r1 := T.r1
  r2 := T.r2
  pde := T.pde
  ε0 := T.ε0
  nX := T.nX
  θ' := T.θ'
  eX := T.eX
  pr := T.pr
  Mt := T.Mt
  nnK := T.nnK
  Jp := T.Jp
  k := k
  m := T.m
  f := f
  bp := T.bp
  Sc := T.Sc
  eta := T.eta
  T := T.T
  DF := T.DF
  X2 := T.X2
  x := T.x
  eps := T.eps
  vd := T.vd
  rr := rr
  de2 := T.de2
  Nc := T.Nc
  wt := T.wt
  th := T.th
  ad := T.ad
  T2 := T.T2
  g1 := g1
  g2 := g2
  q1 := T.q1
  dd := T.dd
  sm := T.sm

end Builder

section Groups

def mirabSub (k : Type) [Field k] [Fintype k] (n : ℕ) : Subgroup (GL (Fin (n + 1)) k) where
  carrier := {h | IsMirab (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)}
  mul_mem' := by
    intro a b ha hb
    show PI.MirabIndex.IsMirab _
    rw [PI.MirabolicIndex₂.isMirab_iff, PI.MirabolicIndex₂.row_mul_of_mirab n a b ha]
    exact (PI.MirabolicIndex₂.isMirab_iff n _).mp hb
  one_mem' := by
    show PI.MirabIndex.IsMirab _
    rw [PI.MirabolicIndex₂.isMirab_iff, Units.val_one]
    exact PI.MirabolicIndex₂.one_last n
  inv_mem' := by
    intro h hh
    have := PI.MirabolicIndex₂.mirab_mul_inv n 1 h (by
      rw [Units.val_one, PI.MirabolicIndex₂.one_last]
      exact ((PI.MirabolicIndex₂.isMirab_iff n _).mp hh).symm)
    rwa [one_mul] at this

theorem isUniU_mul {k : Type} [Field k] {n : ℕ} {a b : Matrix (Fin (n + 1)) (Fin (n + 1)) k}
    (ha : IsUniU a) (hb : IsUniU b) : IsUniU (a * b) := by
  have hta : a.BlockTriangular id := fun i j hij => ha.2 i j hij
  have htb : b.BlockTriangular id := fun i j hij => hb.2 i j hij
  refine ⟨fun i => ?_, fun i j hij => (hta.mul htb) hij⟩
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [ha.1 i, hb.1 i, one_mul]
  · intro m _ hm
    rcases lt_or_gt_of_ne hm with h | h
    · rw [ha.2 i m h, zero_mul]
    · rw [hb.2 m i h, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem isUniU_one {k : Type} [Field k] {n : ℕ} : IsUniU (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) :=
  ⟨fun i => Matrix.one_apply_eq i, fun _ _ hij => Matrix.one_apply_ne (ne_of_gt hij)⟩

def uniSub (k : Type) [Field k] [Fintype k] (n : ℕ) : Subgroup (mirabSub k n) where
  carrier := {h | IsUniU (((h : mirabSub k n) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)}
  mul_mem' := by
    intro a b ha hb
    show IsUniU ((((a * b : mirabSub k n) : GL (Fin (n + 1)) k)) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)
    rw [Subgroup.coe_mul, Units.val_mul]
    exact isUniU_mul ha hb
  one_mem' := by
    show IsUniU ((((1 : mirabSub k n) : GL (Fin (n + 1)) k)) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)
    rw [OneMemClass.coe_one, Units.val_one]
    exact isUniU_one
  inv_mem' := by
    intro x hx
    have hpow : ∀ m : ℕ, IsUniU ((((x ^ m : mirabSub k n) : GL (Fin (n + 1)) k)) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := by
      intro m
      induction m with
      | zero =>
        rw [pow_zero, OneMemClass.coe_one, Units.val_one]
        exact isUniU_one
      | succ m ih =>
        rw [pow_succ, Subgroup.coe_mul, Units.val_mul]
        exact isUniU_mul ih hx
    have hinv : x⁻¹ = x ^ (orderOf x - 1) := by
      refine (eq_inv_of_mul_eq_one_left ?_).symm
      rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
    show IsUniU ((((x⁻¹ : mirabSub k n) : GL (Fin (n + 1)) k)) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)
    rw [hinv]
    exact hpow _

theorem mirab_levelGroups {ι : Type} (kf : ι → Type) [∀ v, Field (kf v)] [∀ v, Fintype (kf v)] (n : ℕ) :
    IsLevelGroups kf n (fun v => mirabSub (kf v) n) (fun v => uniSub (kf v) n) :=
  ⟨fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩

end Groups

section ToyLevel

def toyG : Fin 2 → ℕ := ![11, 13]

instance fact_prime_examplePrime (v : Fin 2) : Fact (toyG v).Prime := ⟨by fin_cases v <;> norm_num [toyG]⟩

instance neZero_examplePrime (v : Fin 2) : NeZero (toyG v) := ⟨(fact_prime_examplePrime v).out.ne_zero⟩

abbrev ExampleFiniteField (v : Fin 2) : Type := ZMod (toyG v)

abbrev KC : Type := CyclotomicField 143 ℚ

@[instance_reducible] noncomputable def starKC : StarRing KC := starRingOfComm

theorem one_hundred_forty_three_ne_zero : NeZero ((143 : ℕ) : ℚ) := ⟨by norm_num⟩

attribute [local instance] starKC one_hundred_forty_three_ne_zero

theorem cycKC : IsCyclotomicExtension {143} ℚ KC := CyclotomicField.isCyclotomicExtension 143 ℚ

attribute [local instance] cycKC

noncomputable def zC : 𝓞 KC := (IsCyclotomicExtension.zeta_spec 143 ℚ KC).toInteger

theorem zC_prim : IsPrimitiveRoot zC 143 := (IsCyclotomicExtension.zeta_spec 143 ℚ KC).toInteger_isPrimitiveRoot

theorem toyRoot_prim (v : Fin 2) : IsPrimitiveRoot (zC ^ (143 / toyG v)) (toyG v) :=
  zC_prim.pow (by norm_num) (by fin_cases v <;> norm_num [toyG])

noncomputable def toyAddChar (v : Fin 2) : AddChar (ExampleFiniteField v) (𝓞 KC) :=
  AddChar.zmodChar (toyG v) (toyRoot_prim v).pow_eq_one

abbrev ExampleMirabolicGroup : Type := ∀ v : Fin 2, mirabSub (ExampleFiniteField v) 1

noncomputable abbrev mirabolicExample (v0 : InfinitePlace KC) (Tw0 : Finset (HeightOneSpectrum (𝓞 KC))) :
    OnObj (exampleIndefiniteData KC v0 Tw0 0) ExampleMirabolicGroup exampleC :=
  regroup (exampleObject KC v0 Tw0) ExampleMirabolicGroup (fun _ => 1) (Subgroup.pi Set.univ fun v => uniSub (ExampleFiniteField v) 1)
    (psiU ExampleFiniteField 1 toyAddChar fun v => mirabSub (ExampleFiniteField v) 1) (fun _ => ⊥) (fun _ => 0) 1 2 1 11 13

variable (v0 : InfinitePlace KC) (Tw0 : Finset (HeightOneSpectrum (𝓞 KC)))

end ToyLevel

section NotProjectiveExample

variable (K)
variable (v0 : InfinitePlace K) (Tw0 : Finset (HeightOneSpectrum (𝓞 K)))

end NotProjectiveExample

end Formalism.L2.Indef.Tree
