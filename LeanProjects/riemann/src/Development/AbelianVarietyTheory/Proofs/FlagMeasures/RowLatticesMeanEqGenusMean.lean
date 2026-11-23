import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Formalism.HermitianLattices.HermitianLatticesProofs.IsomAct
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRepsOfFinite
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticesSameMiddleConjugateUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowBaseLatticesMemSameHermitianGenusStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardMiddleLatticesOverGenusLatticeStatement

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MeanGenus

section Abstract

variable {G A B ι : Type} [Group G] [MulAction G A] [MulAction G B]

theorem card_fibre_orbit (p : A → B) (hp : ∀ (g : G) a, p (g • a) = g • p a) (a₀ : A) :
    Nat.card {a | a ∈ MulAction.orbit G a₀ ∧ p a = p a₀} * Nat.card (MulAction.stabilizer G a₀) =
      Nat.card (MulAction.stabilizer G (p a₀)) := by
  set H := MulAction.stabilizer G (p a₀) with hH
  have hS : {a | a ∈ MulAction.orbit G a₀ ∧ p a = p a₀} = MulAction.orbit H a₀ := by
    ext a
    simp only [Set.mem_setOf_eq, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨⟨g, rfl⟩, hg⟩
      refine ⟨⟨g, ?_⟩, rfl⟩
      rw [MulAction.mem_stabilizer_iff, ← hp]
      exact hg
    · rintro ⟨h, rfl⟩
      refine ⟨⟨(h : G), rfl⟩, ?_⟩
      rw [Subgroup.smul_def, hp]
      exact h.2
  have hle : MulAction.stabilizer G a₀ ≤ H := fun g hg => by
    rw [MulAction.mem_stabilizer_iff] at hg ⊢
    rw [← hp, hg]
  have hsub : MulAction.stabilizer H a₀ = (MulAction.stabilizer G a₀).subgroupOf H := by
    ext x
    simp [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff, Subgroup.smul_def]
  have hstab : Nat.card (MulAction.stabilizer H a₀) = Nat.card (MulAction.stabilizer G a₀) := by
    rw [hsub]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [hS, Nat.card_congr (MulAction.orbitEquivQuotientStabilizer H a₀), ← hstab]
  exact (Subgroup.card_eq_card_quotient_mul_card_subgroup _).symm
private lemma natCast_mul_ofReal_inv_eq_ofReal_inv_of_mul_eq (f s S : ℕ) (hf : f ≠ 0) (h : f * s = S) :
    (f : ℝ≥0∞) * ENNReal.ofReal ((S : ℝ))⁻¹ = ENNReal.ofReal ((s : ℝ))⁻¹ := by
  subst h
  rcases Nat.eq_zero_or_pos s with hs | hs
  · simp [hs]
  · have hf' : (f : ℝ) ≠ 0 := by exact_mod_cast hf
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    congr 1
    push_cast
    rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hf', one_mul]

theorem sum_over_fibres (p : A → B) (hp : ∀ (g : G) a, p (g • a) = g • p a) (𝒜 : Set A)
    (h𝒜 : ∀ (g : G), ∀ a ∈ 𝒜, g • a ∈ 𝒜) (what₂ : Finset ι) (m : ι → A) (hm : ∀ i ∈ what₂, m i ∈ 𝒜)
    (hrow : ∀ a ∈ 𝒜, ∃! i, i ∈ what₂ ∧ ∃ g : G, g • m i = a) (reps : Finset B)
    (hreps : ∀ a ∈ 𝒜, ∃! M, M ∈ reps ∧ ∃ g : G, g • M = p a) (c : ℕ) (hc : c ≠ 0)
    (hcount : ∀ M ∈ reps, {a | a ∈ 𝒜 ∧ p a = M}.ncard = c) (N : B → ℝ≥0∞)
    (hN : ∀ (g : G) M, N (g • M) = N M) :
    ∑ i ∈ what₂, ENNReal.ofReal ((Nat.card (MulAction.stabilizer G (m i)) : ℝ))⁻¹ * N (p (m i)) =
      c * ∑ M ∈ reps, ENNReal.ofReal ((Nat.card (MulAction.stabilizer G M) : ℝ))⁻¹ * N M := by
  classical
  by_cases hne : what₂.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    have hreps0 : reps = ∅ := by
      rw [← Finset.not_nonempty_iff_eq_empty]
      rintro ⟨M, hM⟩
      obtain ⟨a, ha, -⟩ := Set.nonempty_of_ncard_ne_zero (s := {a | a ∈ 𝒜 ∧ p a = M}) (by rw [hcount M hM]; exact hc)
      obtain ⟨i, ⟨hi, -⟩, -⟩ := hrow a ha
      simp [hne] at hi
    simp [hne, hreps0]
  obtain ⟨i0, hi0⟩ := hne
  have : Nonempty B := ⟨p (m i0)⟩
  have : Nonempty ι := ⟨i0⟩
  choose! Mof hMof using fun i (hi : i ∈ what₂) => (hreps (m i) (hm i hi)).exists
  choose! r hr using fun a (ha : a ∈ 𝒜) => (hrow a ha).exists
  have hL : ∑ i ∈ what₂, ENNReal.ofReal ((Nat.card (MulAction.stabilizer G (m i)) : ℝ))⁻¹ * N (p (m i)) =
      ∑ i ∈ what₂, ENNReal.ofReal ((Nat.card (MulAction.stabilizer G (m i)) : ℝ))⁻¹ * N (Mof i) :=
    Finset.sum_congr rfl fun i hi => by
      obtain ⟨g, hg⟩ := (hMof i hi).2
      rw [← hg, hN]
  have hfib : ∑ i ∈ what₂, ENNReal.ofReal ((Nat.card (MulAction.stabilizer G (m i)) : ℝ))⁻¹ * N (Mof i) =
      ∑ M ∈ reps, ∑ i ∈ what₂.filter (fun i => Mof i = M),
        ENNReal.ofReal ((Nat.card (MulAction.stabilizer G (m i)) : ℝ))⁻¹ * N (Mof i) :=
    (Finset.sum_fiberwise_of_maps_to (fun i hi => (hMof i hi).1) _).symm
  rw [hL, hfib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun M hM => ?_
  have hN' : ∀ i ∈ what₂.filter (fun i => Mof i = M),
      ENNReal.ofReal ((Nat.card (MulAction.stabilizer G (m i)) : ℝ))⁻¹ * N (Mof i) =
      ENNReal.ofReal ((Nat.card (MulAction.stabilizer G (m i)) : ℝ))⁻¹ * N M := fun i hi => by
    rw [(Finset.mem_filter.1 hi).2]
  rw [Finset.sum_congr rfl hN', ← Finset.sum_mul, ← mul_assoc]
  congr 1
  have hFne : ({a | a ∈ 𝒜 ∧ p a = M} : Set A).ncard ≠ 0 := by rw [hcount M hM]; exact hc
  have hFfin := Set.finite_of_ncard_ne_zero hFne
  have hrow_fib : ∀ i ∈ what₂.filter (fun i => Mof i = M),
      ((Nat.card {a | a ∈ MulAction.orbit G (m i) ∧ p a = M} : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal ((Nat.card (MulAction.stabilizer G M) : ℝ))⁻¹ =
      ENNReal.ofReal ((Nat.card (MulAction.stabilizer G (m i)) : ℝ))⁻¹ := by
    intro i hi
    obtain ⟨hi, hiM⟩ := Finset.mem_filter.1 hi
    obtain ⟨g, hg⟩ := (hMof i hi).2
    rw [hiM] at hg
    have hp0 : p (g⁻¹ • m i) = M := by rw [hp, ← hg, inv_smul_smul]
    have key := card_fibre_orbit p hp (g⁻¹ • m i)
    rw [MulAction.orbit_smul, hp0] at key
    have hs : Nat.card (MulAction.stabilizer G (g⁻¹ • m i)) = Nat.card (MulAction.stabilizer G (m i)) :=
      (Nat.card_congr (MulAction.stabilizerEquivStabilizer (g := g⁻¹) (a := m i) rfl).toEquiv).symm
    rw [hs] at key
    refine natCast_mul_ofReal_inv_eq_ofReal_inv_of_mul_eq _ _ _ ?_ key
    have hsub : ({a | a ∈ MulAction.orbit G (m i) ∧ p a = M} : Set A) ⊆ {a | a ∈ 𝒜 ∧ p a = M} := by
      rintro a ⟨⟨g', rfl⟩, hpa⟩
      exact ⟨h𝒜 g' _ (hm i hi), hpa⟩
    have hfin : ({a | a ∈ MulAction.orbit G (m i) ∧ p a = M} : Set A).Finite := hFfin.subset hsub
    have hmem : g⁻¹ • m i ∈ ({a | a ∈ MulAction.orbit G (m i) ∧ p a = M} : Set A) :=
      ⟨⟨g⁻¹, rfl⟩, hp0⟩
    haveI := hfin.to_subtype
    have : Nonempty ({a | a ∈ MulAction.orbit G (m i) ∧ p a = M} : Set A) := ⟨⟨_, hmem⟩⟩
    exact Nat.card_pos.ne'
  have hB : ∑ i ∈ what₂.filter (fun i => Mof i = M),
      Nat.card {a | a ∈ MulAction.orbit G (m i) ∧ p a = M} = c := by
    rw [← hcount M hM, Set.ncard_eq_toFinset_card _ hFfin,
      Finset.card_eq_sum_card_fiberwise (f := r) (t := what₂.filter (fun i => Mof i = M))]
    · refine Finset.sum_congr rfl fun i hi => ?_
      obtain ⟨hi, hiM⟩ := Finset.mem_filter.1 hi
      symm
      rw [Nat.card_coe_set_eq, ← Set.ncard_coe_finset]
      congr 1
      ext a
      simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨⟨ha, hpa⟩, hra⟩
        obtain ⟨-, g, hg⟩ := hr a ha
        rw [hra] at hg
        exact ⟨⟨g, hg⟩, hpa⟩
      · rintro ⟨⟨g, rfl⟩, hpa⟩
        have ha : g • m i ∈ 𝒜 := h𝒜 g _ (hm i hi)
        exact ⟨⟨ha, hpa⟩, (hrow _ ha).unique (hr _ ha) ⟨hi, g, rfl⟩⟩
    · intro a ha
      rw [Finset.mem_coe, Set.Finite.mem_toFinset] at ha
      obtain ⟨ha, hpa⟩ := ha
      obtain ⟨hra, g, hg⟩ := hr a ha
      rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨hra, ?_⟩
      have hma : m (r a) = g⁻¹ • a := eq_inv_smul_iff.2 hg
      exact (hreps (m (r a)) (hm _ hra)).unique (hMof _ hra) ⟨hM, g⁻¹, by rw [hma, hp, hpa]⟩
  rw [← Finset.sum_congr rfl hrow_fib, ← Finset.sum_mul]
  congr 1
  rw [← hB, Nat.cast_sum]

end Abstract

section Geometry

open GlobalTheory.IndefiniteRowSideFullHecke.DiscriminantKernelAutomorphisms GlobalTheory.RowMassCompare

theorem mem_gmap {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (γ : V ≃ₗ[K] V) (M : Submodule (𝓞 K) V) (x : V) :
    γ x ∈ Formalism.HermitianLatticesTheory.gmap γ M ↔ x ∈ M := by
  unfold Formalism.HermitianLatticesTheory.gmap
  simp only [Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, hy, hxy⟩
    rw [γ.injective hxy] at hy
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem hT_swap {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) {x y : S.V}
    (h : S.hT x y = 0) : S.hT y x = 0 := S.herm.eq_iff.1 h

variable (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

theorem mem_orth {U : Submodule D.host.E (hS D).V} {v : (hS D).V} :
    v ∈ orth (hS D) U ↔ ∀ x ∈ U, (hS D).hT x v = 0 := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]

theorem mem_orthX {v : (hS D).V} : v ∈ orth (hS D) F0.X ↔ ∀ a, (hS D).hT (F0.e a) v = 0 := by
  rw [mem_orth D]
  constructor
  · intro h a
    exact h _ (Submodule.subset_span ⟨a, rfl⟩)
  · intro h x hx
    have hle : F0.X ≤ LinearMap.ker ((hS D).hT.flip v) :=
      Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; simpa using h a)
    simpa using hle hx

theorem X_le_orth : F0.X ≤ orth (hS D) F0.X := by
  intro x hx
  rw [mem_orthX D F0]
  intro a
  have hle : F0.X ≤ LinearMap.ker ((hS D).hT (F0.e a)) :=
    Submodule.span_le.2 (by rintro _ ⟨b, rfl⟩; exact F0.e_iso a b)
  exact hle hx

theorem Xa_top : F0.Xa D.R.rS = F0.X := by
  unfold FlagG.Xa FlagG.X
  congr 1
  ext x
  simp

theorem mem_Lsub {Λ : LatV D} {v : (hS D).V} :
    v ∈ Lsub Λ (lf D F0) ↔ v ∈ orth (hS D) F0.X ∧ ∃ l ∈ Λ, l ∈ orth (hS D) F0.X ∧ v - l ∈ F0.X := by
  show v ∈ ((Λ ⊓ toO (hS D) (orth (hS D) F0.X)) ⊔ toO (hS D) F0.X) ⊓ toO (hS D) (orth (hS D) F0.X) ↔ _
  rw [Submodule.mem_inf, Submodule.mem_sup]
  simp only [Submodule.mem_inf, toO, Submodule.restrictScalars_mem]
  constructor
  · rintro ⟨⟨l, ⟨hl, hlo⟩, b, hb, rfl⟩, hv⟩
    exact ⟨hv, l, hl, hlo, by simpa using hb⟩
  · rintro ⟨hv, l, hl, hlo, hvl⟩
    exact ⟨⟨l, ⟨hl, hlo⟩, v - l, hvl, by abel⟩, hv⟩

theorem Lsub_congr {Λ : LatV D} {v v' : (hS D).V} (h : v - v' ∈ F0.X) :
    v ∈ Lsub Λ (lf D F0) ↔ v' ∈ Lsub Λ (lf D F0) := by
  have hX : v - v' ∈ orth (hS D) F0.X := X_le_orth D F0 h
  rw [mem_Lsub D F0, mem_Lsub D F0]
  constructor
  · rintro ⟨hv, l, hl, hlo, hvl⟩
    refine ⟨?_, l, hl, hlo, ?_⟩
    · have := (orth (hS D) F0.X).sub_mem hv hX
      convert this using 1
      abel
    · have := F0.X.sub_mem hvl h
      convert this using 1
      abel
  · rintro ⟨hv, l, hl, hlo, hvl⟩
    refine ⟨?_, l, hl, hlo, ?_⟩
    · have := (orth (hS D) F0.X).add_mem hv hX
      convert this using 1
      abel
    · have := F0.X.add_mem hvl h
      convert this using 1
      abel

variable {D F0}

theorem stab_X {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) {x : (VS D).V} :
    γ x ∈ F0.X ↔ x ∈ F0.X := by
  have h := hγ.2.1 D.R.rS
  rw [Xa_top] at h
  constructor
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 hx
    have hyx' : y = x := γ.injective (by simpa using hyx)
    rw [← hyx']
    exact hy
  · intro hx
    rw [← h]
    exact Submodule.mem_map_of_mem hx

theorem stab_orth {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) {x : (VS D).V} :
    γ x ∈ orth (hS D) F0.X ↔ x ∈ orth (hS D) F0.X := by
  have hiso : ∀ a b, (hS D).hT (γ a) (γ b) = (hS D).hT a b := hγ.1
  rw [mem_orth D, mem_orth D]
  constructor
  · intro h y hy
    rw [← hiso]
    exact h _ ((stab_X hγ).2 hy)
  · intro h y hy
    obtain ⟨y', rfl⟩ : ∃ y', γ y' = y := ⟨γ.symm y, by simp⟩
    rw [hiso]
    exact h _ ((stab_X hγ).1 hy)

theorem Lsub_gmap {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) (Λ : LatV D) {v : (VS D).V} :
    γ v ∈ Lsub (Formalism.HermitianLatticesTheory.gmap γ Λ) (lf D F0) ↔ v ∈ Lsub Λ (lf D F0) := by
  rw [mem_Lsub, mem_Lsub, stab_orth hγ]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨l, hl, hlo, hvl⟩
    obtain ⟨l', rfl⟩ : ∃ l', γ l' = l := ⟨γ.symm l, by simp⟩
    refine ⟨l', (mem_gmap γ Λ l').1 hl, (stab_orth hγ).1 hlo, ?_⟩
    rw [← map_sub] at hvl
    exact (stab_X hγ).1 hvl
  · rintro ⟨l, hl, hlo, hvl⟩
    refine ⟨γ l, (mem_gmap γ Λ l).2 hl, (stab_orth hγ).2 hlo, ?_⟩
    rw [← map_sub]
    exact (stab_X hγ).2 hvl

theorem rowLat_gmap {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) (he : ∀ a, γ (F0.e a) = F0.e a)
    {Λ : LatV D} (hΛ : IsRowLat D F0 Λ) : IsRowLat D F0 (Formalism.HermitianLatticesTheory.gmap γ Λ) := by
  obtain ⟨hgen, ⟨hlat, hunim, ⟨hzΛ, hzt⟩, hloc, hprim⟩, hXS⟩ := hΛ
  have hz : γ F0.z = F0.z := hγ.2.2
  have hiso : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hγ.1
  have hiso' : ∀ a b, (VS D).hT (γ a) (γ b) = (VS D).hT a b := hγ.1
  have hfixX : ∀ x ∈ F0.X, γ x = x := fun x hx =>
    LinearMap.eqOn_span (f := (γ : (VS D).V →ₗ[D.host.E] (VS D).V)) (g := LinearMap.id)
      (by rintro _ ⟨a, rfl⟩; simp [he a]) hx
  have hXL : XLam (Formalism.HermitianLatticesTheory.gmap γ Λ) (lf D F0) = XLam Λ (lf D F0) := by
    ext x
    show x ∈ Formalism.HermitianLatticesTheory.gmap γ Λ ∧ x ∈ F0.X ↔ x ∈ Λ ∧ x ∈ F0.X
    constructor
    · rintro ⟨hx, hxX⟩
      refine ⟨(mem_gmap γ Λ x).1 ?_, hxX⟩
      rwa [hfixX x hxX]
    · rintro ⟨hx, hxX⟩
      refine ⟨?_, hxX⟩
      rw [← hfixX x hxX]
      exact (mem_gmap γ Λ x).2 hx
  have hlocg : ∀ p : Ideal (𝓞 D.host.E), Formalism.HermitianLatticesTheory.loc (K := D.host.E) p (Formalism.HermitianLatticesTheory.gmap γ Λ) =
      Formalism.HermitianLatticesTheory.gmap γ (Formalism.HermitianLatticesTheory.loc (K := D.host.E) p Λ) := by
    intro p
    ext x
    simp only [Formalism.HermitianLatticesTheory.loc, Formalism.HermitianLatticesTheory.isomAct_mem_locS, Formalism.HermitianLatticesTheory.isomAct_mem_gmap,
      Formalism.HermitianLatticesTheory.isomAct_smul]
  have hdual : Formalism.HermitianLatticesTheory.dual (VS D).hT (Formalism.HermitianLatticesTheory.gmap γ Λ) =
      Formalism.HermitianLatticesTheory.gmap γ (Formalism.HermitianLatticesTheory.dual (VS D).hT Λ) := by
    ext x
    rw [Formalism.HermitianLatticesTheory.isomAct_mem_dual, Formalism.HermitianLatticesTheory.isomAct_mem_gmap, Formalism.HermitianLatticesTheory.isomAct_mem_dual]
    have key : ∀ y, (VS D).hT (γ y) x = (VS D).hT y (γ.symm x) := fun y => by
      rw [← hiso' y (γ.symm x), LinearEquiv.apply_symm_apply]
    constructor
    · intro H y hy
      have := H (γ y) ((mem_gmap γ Λ y).2 hy)
      rwa [key] at this
    · intro H y hy
      obtain ⟨y', rfl⟩ : ∃ y', γ y' = y := ⟨γ.symm y, by simp⟩
      rw [key]
      exact H y' ((mem_gmap γ Λ y').1 hy)
  refine ⟨⟨Formalism.HermitianLatticesTheory.isomAct_lattice γ Λ hgen.1, fun p hp => ?_⟩,
    ⟨Formalism.HermitianLatticesTheory.isomAct_lattice γ Λ hlat, ?_, ⟨?_, hzt⟩, ?_, ?_⟩, hXL.trans hXS⟩
  · obtain ⟨g, hg, hgl⟩ := hgen.2 p hp
    refine ⟨γ * g, mul_mem hiso hg, ?_⟩
    rw [gmap_mul', hgl, hlocg]
  · show Formalism.HermitianLatticesTheory.dual _ _ = _
    rw [hdual]
    exact congrArg (Formalism.HermitianLatticesTheory.gmap γ) hunim
  · show F0.z ∈ Formalism.HermitianLatticesTheory.gmap γ Λ
    have := (mem_gmap γ Λ F0.z).2 hzΛ
    rwa [hz] at this
  · intro P
    obtain ⟨c, hc0, hcg, hcl⟩ := hloc P
    exact ⟨c, hc0, hcg, by rw [hXL]; exact hcl⟩
  · intro c hc
    apply hprim c
    have h1 : γ (c • F0.z) = c • F0.z := by rw [map_smul, hz]
    apply (Lsub_gmap hγ Λ).1
    rw [h1]
    exact hc

end Geometry

section Standard

open GlobalTheory.IndefiniteRowSideFullHecke.DiscriminantKernelAutomorphisms GlobalTheory.RowMassCompare

variable {D : D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

def cplMap : (D.host.E × ((Fin D.R.rS → D.host.E) × (Fin D.R.rS → D.host.E))) →ₗ[D.host.E] (VS D).V :=
  (LinearMap.toSpanSingleton D.host.E (VS D).V F0.z).coprod
    ((Fintype.linearCombination D.host.E F0.e).coprod (Fintype.linearCombination D.host.E D.sp.hypF))

def decMap : ((D.sp.X 0).V × (D.host.E × ((Fin D.R.rS → D.host.E) × (Fin D.R.rS → D.host.E)))) →ₗ[D.host.E]
    (VS D).V := (D.sp.iXY 0).coprod (cplMap F0)

theorem cplMap_apply (c : D.host.E) (a b : Fin D.R.rS → D.host.E) :
    cplMap F0 (c, a, b) = c • F0.z + (∑ i, a i • F0.e i + ∑ i, b i • D.sp.hypF i) := by
  simp only [cplMap, LinearMap.coprod_apply, LinearMap.toSpanSingleton_apply, Fintype.linearCombination_apply]

theorem decMap_apply (w : (D.sp.X 0).V) (q) : decMap F0 (w, q) = D.sp.iXY 0 w + cplMap F0 q := rfl

theorem sumMap_apply (w : (D.sp.X 0).V) (c : D.host.E) : sumMap D F0 (w, c) = D.sp.iXY 0 w + c • F0.z := rfl

theorem iota_isom (x y : (D.sp.X 0).V) : (VS D).hT (D.sp.iXY 0 x) (D.sp.iXY 0 y) = (D.sp.X 0).hT x y := D.sp.iXY_isom 0 (by have := D.R.two_le_m; omega) x y

variable {F0} (he : F0.e = D.sp.hypE) {t : D.host.E} (hz : F0.z = t • D.sp.zm) (hT : T ≠ 0)

include hz in
theorem definiteInclusion_orthogonal_negativeVector (w : (D.sp.X 0).V) : (VS D).hT (D.sp.iXY 0 w) F0.z = 0 := by
  rw [hz]
  simp [D.sp.zm_orth]

include he in
theorem iota_e (w : (D.sp.X 0).V) (a) : (VS D).hT (D.sp.iXY 0 w) (F0.e a) = 0 := by
  rw [he]
  exact (D.sp.hyp_orthX a w).1

include he in
theorem iota_orth (w : (D.sp.X 0).V) : D.sp.iXY 0 w ∈ orth (hS D) F0.X := (mem_orthX D F0).2 fun a => hT_swap _ (iota_e he w a)

theorem z_orthX : F0.z ∈ orth (hS D) F0.X := (mem_orthX D F0).2 F0.z_orth

include he hz in
theorem iota_cpl (w : (D.sp.X 0).V) (q) : (VS D).hT (D.sp.iXY 0 w) (cplMap F0 q) = 0 := by
  obtain ⟨c, a, b⟩ := q
  rw [cplMap_apply]
  have h3 : ∀ i, (VS D).hT (D.sp.iXY 0 w) (D.sp.hypF i) = 0 := fun i => (D.sp.hyp_orthX i w).2
  simp [definiteInclusion_orthogonal_negativeVector hz, iota_e he, h3]

include he in
theorem e_dec (j) (w : (D.sp.X 0).V) (c a b) : (VS D).hT (F0.e j) (decMap F0 (w, c, a, b)) = b j := by
  rw [decMap_apply, cplMap_apply]
  have h1 : (VS D).hT (F0.e j) (D.sp.iXY 0 w) = 0 := hT_swap _ (iota_e he w j)
  have h2 : (VS D).hT (F0.e j) F0.z = 0 := F0.z_orth j
  have h3 : ∀ i, (VS D).hT (F0.e j) (F0.e i) = 0 := fun i => F0.e_iso j i
  have h4 : ∀ i, (VS D).hT (F0.e j) (D.sp.hypF i) = if j = i then 1 else 0 := fun i => by
    rw [he]
    exact D.sp.hyp_ef j i
  simp [h1, h2, h3, h4]

include he hz in
theorem z_dec (w : (D.sp.X 0).V) (c a b) : (VS D).hT F0.z (decMap F0 (w, c, a, b)) = c * -T := by
  rw [decMap_apply, cplMap_apply]
  have h1 : (VS D).hT F0.z (D.sp.iXY 0 w) = 0 := hT_swap _ (definiteInclusion_orthogonal_negativeVector hz w)
  have h2 : (VS D).hT F0.z F0.z = -T := F0.z_norm
  have h3 : ∀ i, (VS D).hT F0.z (F0.e i) = 0 := fun i => hT_swap _ (F0.z_orth i)
  have h4 : ∀ i, (VS D).hT F0.z (D.sp.hypF i) = 0 := fun i => by
    rw [hz]
    simp [(D.sp.hyp_orthz i).2]
  simp [h1, h2, h3, h4]

include he hz hT in
theorem dec_bij : Function.Bijective (decMap F0) := by
  have hinj : Function.Injective (decMap F0) := by
    refine (injective_iff_map_eq_zero (decMap F0)).2 ?_
    rintro ⟨w, c, a, b⟩ h0
    have hb : ∀ j, b j = 0 := fun j => by
      have := e_dec he j w c a b
      rw [h0, map_zero] at this
      exact this.symm
    have hc : c = 0 := by
      have := z_dec he hz w c a b
      rw [h0, map_zero] at this
      exact (mul_eq_zero.1 this.symm).resolve_right (neg_ne_zero.2 hT)
    have hb' : b = 0 := funext hb
    subst hb' hc
    rw [decMap_apply, cplMap_apply] at h0
    simp only [zero_smul, Pi.zero_apply, Finset.sum_const_zero, add_zero, zero_add] at h0
    have ha : ∀ j, a j = 0 := fun j => by
      have := congrArg (fun v => (VS D).hT v (D.sp.hypF j)) h0
      have hx : (VS D).hT (D.sp.iXY 0 w) (D.sp.hypF j) = 0 := (D.sp.hyp_orthX j w).2
      have he' : ∀ i, (VS D).hT (F0.e i) (D.sp.hypF j) = if i = j then 1 else 0 := fun i => by
        rw [he]
        exact D.sp.hyp_ef i j
      simpa [hx, he'] using this
    have ha' : a = 0 := funext ha
    subst ha'
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero] at h0
    have hw : w = 0 := (D.sp.X 0).nondeg.1 w fun y => by
      rw [← iota_isom, h0, map_zero, LinearMap.zero_apply]
    subst hw
    rfl
  have hdim : Module.finrank D.host.E ((D.sp.X 0).V × (D.host.E × ((Fin D.R.rS → D.host.E) × (Fin D.R.rS → D.host.E)))) =
      Module.finrank D.host.E (VS D).V := by
    have h1 : Module.finrank D.host.E (D.sp.X 0).V = D.R.N 0 :=
      (D.sp.X 0).rank_eq.trans (D.sp.X_rank 0 (Nat.zero_le _))
    have h2 : Module.finrank D.host.E (VS D).V = D.R.rankY 0 :=
      (D.sp.Y 0).rank_eq.trans (D.sp.Y_rank 0 (Nat.zero_le _))
    rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_prod, Module.finrank_self,
      Module.finrank_fin_fun, h1, h2]
    obtain ⟨j, hj⟩ := D.R.m_even
    have h2m := D.R.two_le_m
    simp only [Ranks.N, Ranks.rankY, Ranks.r, Ranks.rS, zero_mul, add_zero]
    omega
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj⟩

include he in
theorem sumMap_orth (p) : sumMap D F0 p ∈ orth (hS D) F0.X := by
  obtain ⟨w, c⟩ := p
  rw [sumMap_apply]
  exact add_mem (iota_orth he w) (Submodule.smul_mem _ c z_orthX)

include he hz hT in
theorem exists_sumMap {v : (VS D).V} (hv : v ∈ orth (hS D) F0.X) : ∃ p, v - sumMap D F0 p ∈ F0.X := by
  obtain ⟨⟨w, c, a, b⟩, rfl⟩ := (dec_bij he hz hT).2 v
  have hb : ∀ j, b j = 0 := fun j => by
    rw [← e_dec he j w c a b]
    exact (mem_orthX D F0).1 hv j
  refine ⟨(w, c), ?_⟩
  have hb' : b = 0 := funext hb
  subst hb'
  rw [decMap_apply, cplMap_apply, sumMap_apply]
  simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]
  have hmem : ∑ i, a i • F0.e i ∈ F0.X := Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (by unfold FlagG.X; exact Submodule.subset_span ⟨i, rfl⟩)
  convert hmem using 1
  abel

include he hz hT in
theorem eq_zero_of_sumMap {p} (hp : sumMap D F0 p ∈ F0.X) : p = 0 := by
  obtain ⟨w, c⟩ := p
  have hX : sumMap D F0 (w, c) ∈ Submodule.span D.host.E (Set.range F0.e) := hp
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (R := D.host.E)).1 hX
  rw [sumMap_apply] at ha
  have h0 : decMap F0 (w, c, -a, 0) = 0 := by
    rw [decMap_apply, cplMap_apply]
    simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, Pi.zero_apply, zero_smul,
      Finset.sum_const_zero, add_zero]
    rw [ha]
    abel
  have h1 := (dec_bij he hz hT).1 (h0.trans (map_zero (decMap F0)).symm)
  have hw : w = 0 := congrArg Prod.fst h1
  have hc : c = 0 := congrArg (fun x => x.2.1) h1
  rw [hw, hc]
  rfl
private lemma hT_decMap_eq_add_hT_cplMap (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (he : F0.e = D.sp.hypE) {t : D.host.E} (hz : F0.z = t • D.sp.zm) (w w' : (D.sp.X 0).V)
    (q q' : (D.host.E × ((Fin D.R.rS → D.host.E) × (Fin D.R.rS → D.host.E)))) :
    (VS D).hT (decMap F0 (w, q)) (decMap F0 (w', q')) =
      (D.sp.X 0).hT w w' + (VS D).hT (cplMap F0 q) (cplMap F0 q') := by
  rw [decMap_apply, decMap_apply]
  simp only [map_add, LinearMap.add_apply, iota_isom, iota_cpl he hz, hT_swap (VS D) (iota_cpl he hz w' q),
    zero_add, add_zero]

abbrev hat (g : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) :
    ((D.sp.X 0).V × D.host.E) ≃ₗ[D.host.E] ((D.sp.X 0).V × D.host.E) :=
  g.prodCongr (LinearEquiv.refl D.host.E D.host.E)

variable (F0) in

def Induces (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (g : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) : Prop :=
  ∀ p, γ (sumMap D F0 p) - sumMap D F0 (hat g p) ∈ F0.X

include he hz hT in

theorem exists_ext {g} (hg : g ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT) :
    ∃ γ ∈ stabF D F0, (∀ a, γ (F0.e a) = F0.e a) ∧ Induces F0 γ g := by
  have hg' : ∀ x y, (D.sp.X 0).hT (g x) (g y) = (D.sp.X 0).hT x y := hg
  let φ := LinearEquiv.ofBijective (decMap F0) (dec_bij he hz hT)
  let G : ((D.sp.X 0).V × (D.host.E × ((Fin D.R.rS → D.host.E) × (Fin D.R.rS → D.host.E)))) ≃ₗ[D.host.E] ((D.sp.X 0).V × (D.host.E × ((Fin D.R.rS → D.host.E) × (Fin D.R.rS → D.host.E)))) :=
    g.prodCongr (LinearEquiv.refl D.host.E (D.host.E × ((Fin D.R.rS → D.host.E) × (Fin D.R.rS → D.host.E))))
  let γ : (VS D).V ≃ₗ[D.host.E] (VS D).V := φ.symm.trans (G.trans φ)
  have hγ : ∀ u, γ (decMap F0 u) = decMap F0 (G u) := by
    intro u
    have h1 : decMap F0 u = φ u := rfl
    rw [h1]
    simp only [γ, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rfl
  have hG0 : ∀ q, G (0, q) = (0, q) := by
    intro q
    simp [G]
  have he' : ∀ a, F0.e a = decMap F0 (0, 0, Pi.single a 1, 0) := by
    intro a
    rw [decMap_apply, cplMap_apply]
    simp [Pi.single_apply, ite_smul]
  have hz' : F0.z = decMap F0 (0, 1, 0, 0) := by
    rw [decMap_apply, cplMap_apply]
    simp
  have hsum : ∀ w c, sumMap D F0 (w, c) = decMap F0 (w, c, 0, 0) := by
    intro w c
    rw [sumMap_apply, decMap_apply, cplMap_apply]
    simp
  have hγe : ∀ a, γ (F0.e a) = F0.e a := by
    intro a
    rw [he' a, hγ, hG0]
  have hγz : γ F0.z = F0.z := by
    rw [hz', hγ, hG0]
  have hiso : ∀ x y, (VS D).hT (γ x) (γ y) = (VS D).hT x y := by
    intro x y
    obtain ⟨⟨w, q⟩, rfl⟩ := (dec_bij he hz hT).2 x
    obtain ⟨⟨w', q'⟩, rfl⟩ := (dec_bij he hz hT).2 y
    rw [hγ, hγ]
    have hGa : ∀ w q, G (w, q) = (g w, q) := fun _ _ => rfl
    rw [hGa, hGa, hT_decMap_eq_add_hT_cplMap D F0 he hz, hT_decMap_eq_add_hT_cplMap D F0 he hz, hg']
  have hXa : ∀ j, (F0.Xa j).map (γ : (VS D).V →ₗ[D.host.E] (VS D).V) = F0.Xa j := by
    intro j
    simp only [FlagG.Xa, Submodule.map_span, Set.image_image, LinearEquiv.coe_coe, hγe]
  refine ⟨γ, ⟨hiso, hXa, hγz⟩, hγe, ?_⟩
  intro p
  obtain ⟨w, c⟩ := p
  have hh : hat g (w, c) = (g w, c) := rfl
  rw [hh, hsum, hsum, hγ]
  have hGa : G (w, c, 0, 0) = (g w, c, 0, 0) := rfl
  rw [hGa, sub_self]
  exact F0.X.zero_mem
private lemma hT_sub_of_mem_orth_of_mem (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    {v v' x x' : (VS D).V} (hv : v ∈ orth (hS D) F0.X) (hv' : v' ∈ orth (hS D) F0.X)
    (hx : x ∈ F0.X) (hx' : x' ∈ F0.X) :
    (VS D).hT (v - x) (v' - x') = (VS D).hT v v' := by
  have h1 : (VS D).hT x v' = 0 := (mem_orth D).1 hv' x hx
  have h2 : (VS D).hT x' v = 0 := (mem_orth D).1 hv x' hx'
  have h3 : (VS D).hT x x' = 0 := (mem_orth D).1 (X_le_orth D F0 hx') x hx
  have h4 : (VS D).hT v x' = 0 := hT_swap (VS D) h2
  simp only [map_sub, LinearMap.sub_apply, h1, h3, h4, sub_zero]

include he hz hT in

theorem exists_res {γ} (hγ : γ ∈ stabF D F0) : ∃ g ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT, Induces F0 γ g := by
  have hγi : ∀ x y, (VS D).hT (γ x) (γ y) = (VS D).hT x y := hγ.1
  have hγz : γ F0.z = F0.z := hγ.2.2
  let φ := LinearEquiv.ofBijective (decMap F0) (dec_bij he hz hT)
  let g₀ : (D.sp.X 0).V →ₗ[D.host.E] (D.sp.X 0).V :=
    (LinearMap.fst D.host.E (D.sp.X 0).V (D.host.E × ((Fin D.R.rS → D.host.E) × (Fin D.R.rS → D.host.E)))) ∘ₗ
      (φ.symm : (VS D).V →ₗ[D.host.E] ((D.sp.X 0).V × (D.host.E × ((Fin D.R.rS → D.host.E) × (Fin D.R.rS → D.host.E))))) ∘ₗ
      (γ : (VS D).V →ₗ[D.host.E] (VS D).V) ∘ₗ (D.sp.iXY 0)
  have horth : ∀ w, γ (D.sp.iXY 0 w) ∈ orth (hS D) F0.X := fun w => (stab_orth hγ).2 (iota_orth he w)
  have hK : ∀ w, γ (D.sp.iXY 0 w) - D.sp.iXY 0 (g₀ w) ∈ F0.X := by
    intro w
    have hu : decMap F0 (φ.symm (γ (D.sp.iXY 0 w))) = γ (D.sp.iXY 0 w) := φ.apply_symm_apply _
    have hg0 : g₀ w = (φ.symm (γ (D.sp.iXY 0 w))).1 := rfl
    rw [hg0]
    generalize φ.symm (γ (D.sp.iXY 0 w)) = u at hu ⊢
    obtain ⟨w', c, a, b⟩ := u
    have hb : b = 0 := by
      funext j
      have h1 := e_dec he j w' c a b
      rw [hu] at h1
      rw [← h1]
      exact (mem_orthX D F0).1 (horth w) j
    have hc : c = 0 := by
      have h1 := z_dec he hz w' c a b
      rw [hu] at h1
      have h2 : (VS D).hT F0.z (γ (D.sp.iXY 0 w)) = 0 := by
        rw [← hγz, hγi]
        exact hT_swap (VS D) (definiteInclusion_orthogonal_negativeVector hz w)
      rw [h2] at h1
      have h3 : c * T = 0 := by linear_combination h1
      exact (mul_eq_zero.1 h3).resolve_right hT
    subst hb
    subst hc
    have hmem : (∑ i, a i • F0.e i) ∈ F0.X :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (s := Set.range F0.e) ⟨i, rfl⟩)
    rw [← hu, decMap_apply, cplMap_apply]
    convert hmem using 1
    simp
  have hiso0 : ∀ x y, (D.sp.X 0).hT (g₀ x) (g₀ y) = (D.sp.X 0).hT x y := by
    intro x y
    rw [← iota_isom, ← iota_isom]
    have hx' : D.sp.iXY 0 (g₀ x) = γ (D.sp.iXY 0 x) - (γ (D.sp.iXY 0 x) - D.sp.iXY 0 (g₀ x)) := by abel
    have hy' : D.sp.iXY 0 (g₀ y) = γ (D.sp.iXY 0 y) - (γ (D.sp.iXY 0 y) - D.sp.iXY 0 (g₀ y)) := by abel
    rw [hx', hy', hT_sub_of_mem_orth_of_mem D F0 (horth x) (horth y) (hK x) (hK y), hγi]
  have hinj : Function.Injective g₀ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    apply (D.sp.X 0).nondeg.1 w
    intro y
    rw [← hiso0, hw, map_zero, LinearMap.zero_apply]
  let g : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V :=
    LinearEquiv.ofBijective g₀ ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩
  refine ⟨g, hiso0, ?_⟩
  intro p
  obtain ⟨w, c⟩ := p
  have hh : hat g (w, c) = (g₀ w, c) := rfl
  rw [hh, sumMap_apply, sumMap_apply, map_add, map_smul, hγz]
  have h5 : γ (D.sp.iXY 0 w) + c • F0.z - (D.sp.iXY 0 (g₀ w) + c • F0.z) =
      γ (D.sp.iXY 0 w) - D.sp.iXY 0 (g₀ w) := by abel
  rw [h5]
  exact hK w

theorem latL_gmap {γ g} (hγ : γ ∈ stabF D F0) (h : Induces F0 γ g) (Λ : LatV D) :
    latL D F0 (Formalism.HermitianLatticesTheory.gmap γ Λ) = Formalism.HermitianLatticesTheory.gmap (hat g) (latL D F0 Λ) := by
  ext p
  rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap]
  change sumMap D F0 p ∈ Lsub (Formalism.HermitianLatticesTheory.gmap γ Λ) (lf D F0) ↔
    sumMap D F0 ((hat g).symm p) ∈ Lsub Λ (lf D F0)
  obtain ⟨q, rfl⟩ : ∃ q, p = hat g q := ⟨(hat g).symm p, ((hat g).apply_symm_apply p).symm⟩
  rw [LinearEquiv.symm_apply_apply, ← Lsub_gmap hγ Λ]
  refine Lsub_congr D F0 ?_
  rw [← neg_sub]
  exact F0.X.neg_mem (h q)

include he hz hT in
theorem Lsub_eq_of_latL {Λ Λ' : LatV D} (h : latL D F0 Λ = latL D F0 Λ') :
    Lsub Λ (lf D F0) = Lsub Λ' (lf D F0) := by
  ext v
  by_cases hv : v ∈ orth (hS D) F0.X
  · obtain ⟨p, hp⟩ := exists_sumMap he hz hT hv
    rw [Lsub_congr D F0 hp, Lsub_congr D F0 hp]
    change p ∈ latL D F0 Λ ↔ p ∈ latL D F0 Λ'
    rw [h]
  · have h1 : ∀ Λ'' : LatV D, v ∉ Lsub Λ'' (lf D F0) := fun Λ'' hm => hv (Submodule.mem_inf.1 hm).2
    exact iff_of_false (h1 Λ) (h1 Λ')

end Standard

section Count

open GlobalTheory.IndefiniteRowSideFullHecke.DiscriminantKernelAutomorphisms GlobalTheory.RowMassCompare

variable {D : D7} {T : D.host.E} {F0 : FlagG (VS D) D.R.rS T}
  (he : F0.e = D.sp.hypE) {t : D.host.E} (hz : F0.z = t • D.sp.zm) (hT : T ≠ 0)

theorem mem_perpS {v : (VS D).V} : v ∈ perpS (VS D) F0.X ↔ v ∈ orth (hS D) F0.X := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  exact Iff.rfl

theorem mk_eq_mk {x y : perpS (VS D) F0.X} :
    (Submodule.Quotient.mk x : WbQ D F0) = Submodule.Quotient.mk y ↔ x.1 - y.1 ∈ F0.X := by
  rw [Submodule.Quotient.eq]
  exact Iff.rfl

def quotEquiv : ((D.sp.X 0).V × D.host.E) ≃ WbQ D F0 :=
  Equiv.ofBijective (fun p => Submodule.Quotient.mk ⟨sumMap D F0 p, mem_perpS.2 (sumMap_orth he p)⟩) (by
    constructor
    · intro p p' h
      have := mk_eq_mk.1 h
      simp only [← map_sub] at this
      exact sub_eq_zero.1 (eq_zero_of_sumMap he hz hT this)
    · intro c
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ c
      obtain ⟨p, hp⟩ := exists_sumMap he hz hT (mem_perpS.1 x.2)
      exact ⟨p, (mk_eq_mk.2 hp).symm⟩)

theorem induced_eq {γ g} (hγ : γ ∈ stabF D F0) (h : Induces F0 γ g) (x : perpS (VS D) F0.X)
    (hx : γ x.1 ∈ perpS (VS D) F0.X) :
    quotEquiv he hz hT (hat g ((quotEquiv he hz hT).symm (Submodule.Quotient.mk x))) =
      Submodule.Quotient.mk ⟨γ x.1, hx⟩ := by
  obtain ⟨p, hp⟩ : ∃ p, (quotEquiv he hz hT).symm (Submodule.Quotient.mk x) = p := ⟨_, rfl⟩
  have hp' : quotEquiv he hz hT p = Submodule.Quotient.mk x := by
    rw [← hp]
    exact Equiv.apply_symm_apply _ _
  rw [hp]
  have h1 : sumMap D F0 p - x.1 ∈ F0.X :=
    mk_eq_mk.1 (show (Submodule.Quotient.mk ⟨sumMap D F0 p, mem_perpS.2 (sumMap_orth he p)⟩ : WbQ D F0) =
      Submodule.Quotient.mk x from hp')
  show (Submodule.Quotient.mk ⟨sumMap D F0 (hat g p), mem_perpS.2 (sumMap_orth he (hat g p))⟩ : WbQ D F0) =
    Submodule.Quotient.mk ⟨γ x.1, hx⟩
  rw [mk_eq_mk]
  have h2 := h p
  have h3 : γ (sumMap D F0 p - x.1) ∈ F0.X := (stab_X hγ).2 h1
  have h4 : sumMap D F0 (hat g p) - γ x.1 =
      γ (sumMap D F0 p - x.1) - (γ (sumMap D F0 p) - sumMap D F0 (hat g p)) := by
    rw [map_sub]
    abel
  rw [h4]
  exact F0.X.sub_mem h3 h2

include he hz hT in

theorem card_autLz
    (hlift : ∀ Λ₁ Λ₂ : LatV D, IsRowLat D F0 Λ₁ → IsRowLat D F0 Λ₂ → Lsub Λ₁ (lf D F0) = Lsub Λ₂ (lf D F0) →
      ∃ n ∈ stabF D F0, (∀ x ∈ orth (hS D) F0.X, n x - x ∈ F0.X) ∧ Formalism.HermitianLatticesTheory.gmap n Λ₁ = Λ₂)
    {Λ : LatV D} (hΛ : IsRowLat D F0 Λ) :
    Nat.card (autLz D F0 Λ) =
      Nat.card {g : Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT // Formalism.HermitianLatticesTheory.gmap (hat g.1) (latL D F0 Λ) = latL D F0 Λ} := by
  have hPhi : ∀ g : Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT, Formalism.HermitianLatticesTheory.gmap (hat g.1) (latL D F0 Λ) = latL D F0 Λ →
      (fun y => quotEquiv he hz hT (hat g.1 ((quotEquiv he hz hT).symm y))) ∈ autLz D F0 Λ := by
    intro g hg
    obtain ⟨γ, hγ, hγe, hind⟩ := exists_ext he hz hT g.2
    have hrow : IsRowLat D F0 (Formalism.HermitianLatticesTheory.gmap γ Λ) := rowLat_gmap hγ hγe hΛ
    have hL : Lsub (Formalism.HermitianLatticesTheory.gmap γ Λ) (lf D F0) = Lsub Λ (lf D F0) := by
      apply Lsub_eq_of_latL he hz hT
      rw [latL_gmap hγ hind, hg]
    obtain ⟨n, hn, hnX, hnΛ⟩ := hlift _ _ hrow hΛ hL
    simp only [autLz, Set.mem_ofPred_eq]
    refine ⟨n * γ, GlobalTheory.RowMassCompare.mul_mem_stabF D F0 hn hγ, ?_, ?_⟩
    · rw [GlobalTheory.RowMassCompare.gmap_mul', hnΛ]
    · intro x hx
      have hx1 : γ x.1 ∈ perpS (VS D) F0.X := mem_perpS.2 ((stab_orth hγ).2 (mem_perpS.1 x.2))
      rw [induced_eq he hz hT hγ hind x hx1, mk_eq_mk]
      show γ x.1 - n (γ x.1) ∈ F0.X
      rw [← neg_sub]
      exact F0.X.neg_mem (hnX _ (mem_perpS.1 hx1))
  let Ψ : {g : Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT // Formalism.HermitianLatticesTheory.gmap (hat g.1) (latL D F0 Λ) = latL D F0 Λ} →
      autLz D F0 Λ := fun g => ⟨_, hPhi g.1 g.2⟩
  have hinj : Function.Injective Ψ := by
    intro g g' hgg
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.ext
    intro w
    have h2 : quotEquiv he hz hT (hat g.1.1 ((quotEquiv he hz hT).symm (quotEquiv he hz hT (w, 0)))) =
        quotEquiv he hz hT (hat g'.1.1 ((quotEquiv he hz hT).symm (quotEquiv he hz hT (w, 0)))) :=
      congrFun (congrArg Subtype.val hgg) _
    rw [Equiv.symm_apply_apply] at h2
    exact congrArg Prod.fst ((quotEquiv he hz hT).injective h2)
  have hsurj : Function.Surjective Ψ := by
    rintro ⟨φ, γ, hγ, hγΛ, hφ⟩
    obtain ⟨g, hg, hind⟩ := exists_res he hz hT hγ
    refine ⟨⟨⟨g, hg⟩, ?_⟩, ?_⟩
    · rw [← latL_gmap hγ hind, hγΛ]
    · apply Subtype.ext
      funext y
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      have hx1 : γ x.1 ∈ perpS (VS D) F0.X := mem_perpS.2 ((stab_orth hγ).2 (mem_perpS.1 x.2))
      show quotEquiv he hz hT (hat g ((quotEquiv he hz hT).symm (Submodule.Quotient.mk x))) =
        φ (Submodule.Quotient.mk x)
      rw [hφ x hx1, induced_eq he hz hT hγ hind x hx1]
  exact Nat.card_congr (Equiv.ofBijective Ψ ⟨hinj, hsurj⟩).symm

variable (D) in

@[reducible] def actW : MulAction (Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT) (LatW D) where
  smul g L := Formalism.HermitianLatticesTheory.gmap g.1 L
  one_smul L := gmap_one' L
  mul_smul g g' L := gmap_mul' g.1 g'.1 L

variable (D) in

@[reducible] def actWE : MulAction (Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT)
    (Submodule (𝓞 D.host.E) ((D.sp.X 0).V × D.host.E)) where
  smul g L := Formalism.HermitianLatticesTheory.gmap (hat g.1) L
  one_smul L := gmap_one' L
  mul_smul g g' L := gmap_mul' (hat g.1) (hat g'.1) L

end Count

open GlobalTheory.IndefiniteRowSideFullHecke.DiscriminantKernelAutomorphisms GlobalTheory.RowMassCompare in

theorem rows_sum (D : D7) (u : D.what₂.Word) (hp : (Tu D u).Prime) (h3 : 3 ≤ Tu D u)
    (hs : SplitsCompletely (E := D.host.E) (Tu D u)) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (he : F0.e = D.sp.hypE) (hz : F0.z = D.zmOf u) (what₂ : Finset (LatV D)) (hrows : IsRowReps D F0 what₂)
    (Λ₀ : LatV D) (hΛ₀ : IsRowLat D F0 Λ₀) (reps : Finset (LatW D))
    (hreps : Formalism.ThetaLiftIndependence.IsClassReps (D.sp.X 0).hT (L0X D Λ₀ (lf D F0)) reps) (N : LatW D → ℝ≥0∞)
    (hN : ∀ γ ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT, ∀ L, N (Formalism.HermitianLatticesTheory.gmap γ L) = N L) :
    ∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ) * N (L0X D Λ (lf D F0)) =
      (((Tu D u - 1) ^ D.R.f : ℕ) : ℝ≥0∞) *
        ∑ L' ∈ reps, ENNReal.ofReal ((Nat.card (Formalism.ThetaLiftIndependence.autL (D.sp.X 0).hT L') : ℝ))⁻¹ * N L' := by
  classical
  letI iW : MulAction (Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT) (LatW D) := actW D
  letI iWE : MulAction (Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT)
      (Submodule (𝓞 D.host.E) ((D.sp.X 0).V × D.host.E)) := actWE D
  have hT0 : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hz' : F0.z = (D.cOf u)⁻¹ • D.sp.zm := hz.trans rfl
  have hlift := GlobalTheory.T.row_lattices_same_middle_conjugate_unipotent D u hp h3 hs F0 he hz
  let p : Submodule (𝓞 D.host.E) ((D.sp.X 0).V × D.host.E) → LatW D := fun 𝓛 =>
    𝓛.comap ((LinearMap.inl D.host.E (D.sp.X 0).V D.host.E).restrictScalars (𝓞 D.host.E))
  have hp_eq : ∀ (g : Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT) 𝓛, p (g • 𝓛) = g • p 𝓛 := by
    intro g 𝓛
    ext w
    show (w, (0 : D.host.E)) ∈ Formalism.HermitianLatticesTheory.gmap (hat g.1) 𝓛 ↔ w ∈ Formalism.HermitianLatticesTheory.gmap g.1 (p 𝓛)
    rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap, Formalism.HermitianLatticesTheory.isomAct_mem_gmap]
    rfl
  let 𝒜 : Set (Submodule (𝓞 D.host.E) ((D.sp.X 0).V × D.host.E)) :=
    {𝓛 | ∃ Λ', IsRowLat D F0 Λ' ∧ latL D F0 Λ' = 𝓛}
  have h𝒜 : ∀ (g : Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT), ∀ a ∈ 𝒜, g • a ∈ 𝒜 := by
    rintro g _ ⟨Λ', hΛ', rfl⟩
    obtain ⟨γ, hγ, hγe, hind⟩ := exists_ext he hz' hT0 g.2
    exact ⟨Formalism.HermitianLatticesTheory.gmap γ Λ', rowLat_gmap hγ hγe hΛ', latL_gmap hγ hind Λ'⟩
  have hrow : ∀ a ∈ 𝒜, ∃! Λ, Λ ∈ what₂ ∧
      ∃ g : Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT, g • latL D F0 Λ = a := by
    rintro _ ⟨Λ', hΛ', rfl⟩
    obtain ⟨Λ'', ⟨hΛ''s, γ, hγ, hγΛ⟩, huniq⟩ := hrows.2 Λ' hΛ'
    obtain ⟨g, hg, hind⟩ := exists_res he hz' hT0 hγ
    refine ⟨Λ'', ⟨hΛ''s, ⟨g, hg⟩, ?_⟩, ?_⟩
    · show Formalism.HermitianLatticesTheory.gmap (hat g) (latL D F0 Λ'') = latL D F0 Λ'
      rw [← hγΛ, latL_gmap hγ hind]
    · rintro Λ₁ ⟨hΛ₁s, g₁, hg₁⟩
      apply huniq
      refine ⟨hΛ₁s, ?_⟩
      obtain ⟨γ₁, hγ₁, hγ₁e, hind₁⟩ := exists_ext he hz' hT0 g₁.2
      have hrow₁ : IsRowLat D F0 Λ₁ := hrows.1 Λ₁ hΛ₁s
      have hL : latL D F0 (Formalism.HermitianLatticesTheory.gmap γ₁ Λ₁) = latL D F0 Λ' := by
        rw [latL_gmap hγ₁ hind₁]
        exact hg₁
      have hLs := Lsub_eq_of_latL he hz' hT0 hL
      obtain ⟨n, hn, -, hnΛ⟩ := hlift _ _ (rowLat_gmap hγ₁ hγ₁e hrow₁) hΛ' hLs
      exact ⟨n * γ₁, mul_mem_stabF D F0 hn hγ₁, by rw [GlobalTheory.RowMassCompare.gmap_mul', hnΛ]⟩
  have hpL : ∀ Λ, p (latL D F0 Λ) = L0X D Λ (lf D F0) := by
    intro Λ
    ext w
    exact (GlobalTheory.IndefiniteRowSideFullHecke.DiscriminantKernelAutomorphisms.mem_orthModIsotropicLatticePerpNegative_iff D u F0 hz Λ w).symm
  have hreps' : ∀ a ∈ 𝒜, ∃! M, M ∈ reps ∧ ∃ g : Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT, g • M = p a := by
    rintro _ ⟨Λ', hΛ', rfl⟩
    rw [hpL]
    obtain ⟨M, ⟨hMs, g, hg, hgM⟩, huniq⟩ :=
      hreps.2 _ (GlobalTheory.T.rowBaseLattices_mem_same_hermitianGenus D u hp h3 hs F0 he hz Λ₀ hΛ₀ Λ' hΛ')
    refine ⟨M, ⟨hMs, ⟨g, hg⟩, hgM⟩, ?_⟩
    rintro M' ⟨hM's, g', hg'⟩
    exact huniq M' ⟨hM's, g'.1, g'.2, hg'⟩
  have hcount : ∀ M ∈ reps, {a | a ∈ 𝒜 ∧ p a = M}.ncard = (Tu D u - 1) ^ D.R.f := by
    intro M hM
    exact GlobalTheory.T.card_middleLattices_over_genus_lattice D u hp h3 hs F0 he hz Λ₀ hΛ₀ M (hreps.1 M hM)
  have hc : (Tu D u - 1) ^ D.R.f ≠ 0 := pow_ne_zero _ (by omega)
  have key := sum_over_fibres p hp_eq 𝒜 h𝒜 what₂ (latL D F0)
    (fun Λ hΛ => ⟨Λ, hrows.1 Λ hΛ, rfl⟩) hrow reps hreps' ((Tu D u - 1) ^ D.R.f) hc hcount N
    (fun g M => hN g.1 g.2 M)
  have hL : ∀ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ) * N (L0X D Λ (lf D F0)) =
      ENNReal.ofReal ((Nat.card (MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT)
        (latL D F0 Λ)) : ℝ))⁻¹ * N (p (latL D F0 Λ)) := by
    intro Λ hΛ
    have hc' : Nat.card (autLz D F0 Λ) =
        Nat.card (MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT) (latL D F0 Λ)) := by
      rw [card_autLz he hz' hT0 hlift (hrows.1 Λ hΛ)]
      exact Nat.card_congr (Equiv.subtypeEquivRight (fun g => Iff.rfl))
    show ENNReal.ofReal ((Nat.card (autLz D F0 Λ) : ℝ))⁻¹ * _ = _
    rw [hc', hpL]
  have hR : ∀ M ∈ reps, ENNReal.ofReal ((Nat.card (Formalism.ThetaLiftIndependence.autL (D.sp.X 0).hT M) : ℝ))⁻¹ * N M =
      ENNReal.ofReal ((Nat.card (MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT) M) : ℝ))⁻¹ *
        N M := by
    intro M _
    have e : Nat.card (Formalism.ThetaLiftIndependence.autL (D.sp.X 0).hT M) =
        Nat.card (MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT) M) :=
      Nat.card_congr
        { toFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
          invFun := fun y => ⟨y.1.1, show _ ∧ _ from ⟨y.1.2, y.2⟩⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    rw [e]
  rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR]
  exact key

theorem mean_rows_eq_mean_genus : ∀ (D : D7) (u : D.what₂.Word), (Tu D u).Prime → 3 ≤ Tu D u → SplitsCompletely (E := D.host.E) (Tu D u) → ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u → ∀ what₂ : Finset (LatV D), IsRowReps D F0 what₂ → ∀ Λ₀ : LatV D, IsRowLat D F0 Λ₀ → ∀ reps : Finset (LatW D), Formalism.ThetaLiftIndependence.IsClassReps (D.sp.X 0).hT (L0X D Λ₀ (lf D F0)) reps → ∀ N : LatW D → ℕ∞, (∀ γ ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT, ∀ L, N (Formalism.HermitianLatticesTheory.gmap γ L) = N L) → (∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ) * (N (L0X D Λ (lf D F0)) : ℝ≥0∞)) * ENNReal.ofReal (Formalism.HermitianLatticesTheory.mass (D.sp.X 0).hT (L0X D Λ₀ (lf D F0))) = (∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ)) * ∑ L' ∈ reps, ENNReal.ofReal ((Nat.card (Formalism.ThetaLiftIndependence.autL (D.sp.X 0).hT L') : ℝ))⁻¹ * (N L' : ℝ≥0∞) := by
  intro D u hp h3 hs F0 he hz what₂ hrows Λ₀ hΛ₀ reps hreps N hN
  classical
  have hex : ∃ s, Formalism.ThetaLiftIndependence.IsClassReps (D.sp.X 0).hT (L0X D Λ₀ (lf D F0)) s := ⟨reps, hreps⟩
  have h1 := rows_sum D u hp h3 hs F0 he hz what₂ hrows Λ₀ hΛ₀ reps hreps (fun L => (N L : ℝ≥0∞))
    (fun γ hγ L => by simp only [hN γ hγ L])
  have h2 := rows_sum D u hp h3 hs F0 he hz what₂ hrows Λ₀ hΛ₀ hex.choose hex.choose_spec
    (fun _ => 1) (fun _ _ _ => rfl)
  have hm : ENNReal.ofReal (Formalism.HermitianLatticesTheory.mass (D.sp.X 0).hT (L0X D Λ₀ (lf D F0))) =
      ∑ L' ∈ hex.choose, ENNReal.ofReal ((Nat.card (Formalism.ThetaLiftIndependence.autL (D.sp.X 0).hT L') : ℝ))⁻¹ := by
    rw [Formalism.HermitianLatticesTheory.mass, dif_pos hex, ENNReal.ofReal_sum_of_nonneg]
    intro L' _
    positivity
  beta_reduce at h1 h2
  simp only [mul_one] at h2
  rw [h1, hm, h2]
  ring

end GlobalTheory.MeanGenus

end
