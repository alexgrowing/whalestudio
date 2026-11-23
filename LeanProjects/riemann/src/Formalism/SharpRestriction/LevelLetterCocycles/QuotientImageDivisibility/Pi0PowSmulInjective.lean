import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LatticeBoundsOfThreeParts
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.CmpOfMemX

set_option linter.unusedVariables false

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.RL

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

section Map

variable {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)

theorem map_smulA (a : LetA O n) (x : W.DD T₁) : W.map F (a • x) = a • W.map F x := by
  rw [← algebraMap_smul W.EE a x, LinearMap.map_smul, algebraMap_smul]

theorem map_γ' (x : W.DD T₁) : W.map F (W.γ T₁ x) = W.γ T₂ (W.map F x) := W.map_γ F W.gam x

variable (hc₁ : IsCrys PD T₁.ρ) (hc₂ : IsCrys PD T₂.ρ)
include hc₁ hc₂

theorem inPN_map {k : ℕ} {x : W.DD T₁} (h : Formalism.MainNotions.CrystallineLiftingInputs.InPN W T₁ k x) :
    Formalism.MainNotions.CrystallineLiftingInputs.InPN W T₂ k (W.map F x) := by
  obtain ⟨y, hy, hΔ, rfl⟩ := h
  exact ⟨W.map F y, W.map_N F hc₁ hc₂ y hy, fun δ hδ => by rw [← W.map_γ, hΔ δ hδ],
    map_smulA W F _ y⟩

theorem dl_map {i : ZMod n} {x : W.DD T₁} (h : Formalism.MainNotions.CrystallineLiftingInputs.DL W T₁ i x) :
    Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ i (W.map F x) :=
  ⟨by rw [← map_smulA, h.1], fun δ hδ => by rw [← W.map_γ, h.2 δ hδ]⟩

theorem polesFin_map {x : W.DD T₁} (h : Formalism.MainNotions.CrystallineLiftingInputs.PolesFin W T₁ x) :
    Formalism.MainNotions.CrystallineLiftingInputs.PolesFin W T₂ (W.map F x) := by
  obtain ⟨k, K, hK⟩ := h
  exact ⟨k, K, by rw [← map_smulA]; exact W.map_N F hc₁ hc₂ _ hK⟩

theorem inI_map {i : ZMod n} {x : W.DD T₁} (h : Formalism.MainNotions.CrystallineLiftingInputs.InI W T₁ i x) :
    Formalism.MainNotions.CrystallineLiftingInputs.InI W T₂ i (W.map F x) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨dl_map W F hc₁ hc₂ h1, polesFin_map W F hc₁ hc₂ h2, ?_⟩
  rw [← map_γ', ← map_sub]
  exact inPN_map W F hc₁ hc₂ h3

end Map

theorem mem_Z1DΔ_iff (T : LocLat G Qp LL O) (p : W.DD T × W.DD T) :
    p ∈ W.wachCocyclesDelta T ↔ (W.γD T W.gamK p.1 - p.1 = W.φD T p.2 - p.2) ∧
      ∀ δ ∈ W.DelF, W.γD T δ p.1 = p.1 ∧ W.γD T δ p.2 = p.2 := by
  simp only [LocWach.wachCocyclesDelta, herrZ1Δ, herrCocycles, Submodule.mem_inf, LinearMap.mem_ker,
    LinearMap.coprod_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.neg_apply,
    Submodule.mem_iInf, LinearMap.prodMap_apply, Prod.ext_iff, Prod.fst_sub, Prod.snd_sub,
    Prod.fst_zero, Prod.snd_zero, sub_zero, add_neg_eq_zero, sub_eq_zero]

theorem map_mem_Z1DΔ {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (p : ↥(W.wachCocyclesDelta T₁)) :
    ((W.map F (p : W.DD T₁ × W.DD T₁).1, W.map F (p : W.DD T₁ × W.DD T₁).2) : W.DD T₂ × W.DD T₂) ∈
      W.wachCocyclesDelta T₂ := by
  obtain ⟨h1, h2⟩ := (mem_Z1DΔ_iff W T₁ _).1 p.2
  refine (mem_Z1DΔ_iff W T₂ _).2 ⟨?_, fun δ hδ => ?_⟩
  · simp only
    rw [← W.map_γ, ← W.map_φ, ← map_sub, ← map_sub, h1]
  · simp only
    rw [← W.map_γ, ← W.map_γ, (h2 δ hδ).1, (h2 δ hδ).2]
    exact ⟨rfl, rfl⟩

theorem letE_mul_self' (c : ZMod n) : (letE c : LetA O n) * letE c = letE c := by
  funext i
  by_cases h : i = c
  · subst h; simp [letE]
  · simp [letE, h]

theorem pullJ_letter (T : LocLat G Qp LL O) (c : ZMod n) {P : W.DD T}
    (hP : P ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T c 1) : (letE (c + 1) : LetA O n) • P = P := by
  unfold Formalism.MainNotions.CrystallineLiftingInputs.pullJ at hP
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, ⟨-, hyD⟩, rfl⟩ := hx
    rw [pow_one]
    exact Formalism.MainNotions.N.Pv.LocalLengthBound.letter_phi W T (c + 1) (by rw [add_sub_cancel_right]; exact hyD.1)
  | zero => exact smul_zero _
  | add x y _ _ hx hy => rw [smul_add, hx, hy]
  | smul a x _ hx => rw [smul_comm, hx]

theorem pullJ_le_φpull (T : LocLat G Qp LL O) (c : ZMod n) :
    Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T c 1 ≤ W.φpull T := by
  unfold Formalism.MainNotions.CrystallineLiftingInputs.pullJ LocWach.φpull
  refine Submodule.span_mono ?_
  rintro _ ⟨y, ⟨hy, -⟩, rfl⟩
  exact ⟨y, hy, by rw [pow_one]⟩

theorem trunc_letter (T : LocLat G Qp LL O) (c : ZMod n) {M X σ : ℕ} {w z : W.DD T}
    (hw : (letE c : LetA O n) • w = w) (hz : Formalism.MainNotions.CrystallineLiftingInputs.IsTrunc W T c 1 M X σ w z) :
    (letE (c + 1) : LetA O n) • z = z := by
  obtain ⟨cs, r, s, hser, -, rfl⟩ := hz
  have hφ : ∀ y : W.DD T, (letE c : LetA O n) • y = y →
      (letE (c + 1) : LetA O n) • ((W.φD T) ^ 1) y = ((W.φD T) ^ 1) y := by
    intro y hy
    rw [pow_one]
    exact Formalism.MainNotions.N.Pv.LocalLengthBound.letter_phi W T (c + 1) (by rw [add_sub_cancel_right]; exact hy)
  rw [smul_sub, smul_comm, hφ w hw, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [smul_comm, hφ _ (hser.2.1 y).1.1]

theorem pk_succ (j : ℕ) : W.φA (Formalism.MainNotions.LiftingTheory.pk W j) = Formalism.MainNotions.LiftingTheory.pk W (j + 1) := by
  simp only [Formalism.MainNotions.LiftingTheory.pk, pow_succ', AlgHom.mul_apply]

theorem trunc_polesFin (T : LocLat G Qp LL O) (c : ZMod n) (η σ : ℕ) {w z : W.DD T}
    (hw : Formalism.MainNotions.CrystallineLiftingInputs.InI W T c w)
    (hz : (letE (c + 1) : LetA O n) • z = z)
    (hpull : z - ((PD.p : ℕ) : O) ^ σ • ((W.φD T) ^ 1) w ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T c 1)
    (h4 : ∀ x : W.DD T, x ∈ W.φpull T → (letE (c + 1) : LetA O n) • x = x →
      Formalism.MainNotions.LiftingTheory.qp W ^ η • x ∈ W.N T) :
    Formalism.MainNotions.CrystallineLiftingInputs.PolesFin W T z := by
  obtain ⟨⟨hwc, -⟩, ⟨k, K, hK⟩, -⟩ := hw
  set P := z - ((PD.p : ℕ) : O) ^ σ • ((W.φD T) ^ 1) w with hPdef
  have hwl : (letE (c + 1) : LetA O n) • W.φD T w = W.φD T w :=
    Formalism.MainNotions.N.Pv.LocalLengthBound.letter_phi W T (c + 1) (by rw [add_sub_cancel_right]; exact hwc)
  have hPl : (letE (c + 1) : LetA O n) • P = P := pullJ_letter W T c hpull
  have hP : Formalism.MainNotions.LiftingTheory.qp W ^ η • P ∈ W.N T := h4 P (pullJ_le_φpull W T c hpull) hPl
  set a : LetA O n := (∏ j ∈ Finset.range k, Formalism.MainNotions.LiftingTheory.pk W j) ^ K with ha
  set Pq : LetA O n := ∏ j ∈ Finset.range k, Formalism.MainNotions.LiftingTheory.pk W (j + 1) with hPq
  have hφa : W.φD T (a • w) = Pq ^ K • W.φD T w := by
    have e := Formalism.MainNotions.UnusedSlot80.Relay2.φpow_smul W T 1 a w
    rw [pow_one, pow_one] at e
    rw [e, ha, map_pow, map_prod]
    simp only [pk_succ, hPq]
  have hφN : Pq ^ K • W.φD T w ∈ W.φpull T := by
    rw [← hφa]
    exact Submodule.subset_span ⟨a • w, hK, rfl⟩
  have hφl : (letE (c + 1) : LetA O n) • (Pq ^ K • W.φD T w) = Pq ^ K • W.φD T w := by
    rw [smul_comm, hwl]
  have hφq : Formalism.MainNotions.LiftingTheory.qp W ^ η • (Pq ^ K • W.φD T w) ∈ W.N T := h4 _ hφN hφl
  refine ⟨k + 1, K + η, ?_⟩
  have hprod : ∏ j ∈ Finset.range (k + 1), Formalism.MainNotions.LiftingTheory.pk W j = Pq * Formalism.MainNotions.LiftingTheory.qp W := by
    rw [Finset.prod_range_succ']
    simp [Formalism.MainNotions.LiftingTheory.pk, hPq]
  rw [hprod]
  have hz' : z = P + ((PD.p : ℕ) : O) ^ σ • W.φD T w := by rw [hPdef, pow_one, sub_add_cancel]
  rw [hz', smul_add]
  refine (W.N T).add_mem ?_ ?_
  · have e : (Pq * Formalism.MainNotions.LiftingTheory.qp W) ^ (K + η) =
        (Pq ^ (K + η) * Formalism.MainNotions.LiftingTheory.qp W ^ K) * Formalism.MainNotions.LiftingTheory.qp W ^ η := by ring
    rw [e, mul_smul]
    exact (W.N T).smul_mem _ hP
  · have e : (Pq * Formalism.MainNotions.LiftingTheory.qp W) ^ (K + η) =
        (Pq ^ η * Formalism.MainNotions.LiftingTheory.qp W ^ K) * (Formalism.MainNotions.LiftingTheory.qp W ^ η * Pq ^ K) := by ring
    rw [e, smul_comm _ (((PD.p : ℕ) : O) ^ σ), mul_smul]
    refine Submodule.smul_of_tower_mem _ _ ((W.N T).smul_mem _ ?_)
    rw [mul_smul]
    exact hφq

theorem pi0_pow_smul_injective (T : LocLat G Qp LL O)
    (hu : ∃ u : (LetA O n)ˣ, W.π₀ = (u : LetA O n) * letπ ^ (PD.p - 1)) (M : ℕ) {y y' : W.DD T}
    (h : W.π₀ ^ M • y = W.π₀ ^ M • y') : y = y' := by
  obtain ⟨u, hu⟩ := hu
  have hunit : IsUnit (algebraMap (LetA O n) W.EE (W.π₀ ^ M)) := by
    rw [map_pow, hu, map_mul, map_pow]
    exact IsUnit.pow _ (IsUnit.mul (u.isUnit.map _) (W.EE_π.pow _))
  rw [← algebraMap_smul W.EE (W.π₀ ^ M) y, ← algebraMap_smul W.EE (W.π₀ ^ M) y'] at h
  exact (hunit.smul_left_cancel).1 h

theorem γD_smulA (T : LocLat G Qp LL O) (g : W.Gam) (a : LetA O n) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  rw [← algebraMap_smul W.EE a x, W.γD_smul, W.γE_ext, algebraMap_smul]
  rfl

theorem inPN_of_inv (T : LocLat G Qp LL O)
    (hu : ∃ u : (LetA O n)ˣ, W.π₀ = (u : LetA O n) * letπ ^ (PD.p - 1))
    (hΔπ : ∀ δ ∈ W.DelF, W.γA δ W.π₀ = W.π₀) (M : ℕ) {x y : W.DD T} (hy : y ∈ W.N T)
    (hx : x = W.π₀ ^ M • y) (hxΔ : ∀ δ ∈ W.DelF, W.γD T δ x = x) :
    Formalism.MainNotions.CrystallineLiftingInputs.InPN W T M x := by
  refine ⟨y, hy, fun δ hδ => pi0_pow_smul_injective W T hu M ?_, hx⟩
  have := hxΔ δ hδ
  rw [hx, γD_smulA, map_pow, hΔπ δ hδ] at this
  exact this

theorem mem_ImF_of_cls {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (p : ↥(latticeCocycles T₂.L))
    (h : Submodule.Quotient.mk p ∈ (latticeFiniteCohomology PD T₁.L).map F.H1map) : (p : G → T₂.V) ∈ F.ImF PD := by
  obtain ⟨x, hx, hxp⟩ := h
  obtain ⟨c, hc, rfl⟩ := Submodule.mem_map.1 hx
  have hcZ : (c : G → T₁.V) ∈ latticeCocycles T₁.L := c.2
  have h0 : (Submodule.Quotient.mk (p - ⟨F.post c, F.post_Z1T c hcZ⟩) : LatticeCohomology T₂.L) = 0 := by
    rw [Submodule.Quotient.mk_sub, ← hxp]
    simp only [Submodule.mkQ_apply]
    rw [sub_eq_zero]
    rfl
  rw [Submodule.Quotient.mk_eq_zero] at h0
  have h2 : (p : G → T₂.V) = F.post c + ((p - ⟨F.post c, F.post_Z1T c hcZ⟩ : ↥(latticeCocycles T₂.L)) : G → T₂.V) := by
    simp
  rw [h2]
  exact Submodule.add_mem_sup (Submodule.mem_map_of_mem hc) h0

end Formalism.MainNotions.N.Pv.LocalLengthBound.RL
