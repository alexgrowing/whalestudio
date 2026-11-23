import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

noncomputable section

namespace GlobalTheory.IsotConjFix

open Formalism.IndefR.principalLevelFrame

section Gen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
variable {A : Type} [AddCommGroup A] [Module ℂ A]

theorem rt_apply (h : Formalism.AUTREP.GAf L n) (f : Formalism.AUTREP.GAf L n → ℂ) (g : Formalism.AUTREP.GAf L n) :
    Formalism.L2.NG.rt L n h f g = f (g * h) := rfl

theorem range_equivariantMap_stable {ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A} {σ : Formalism.L2.NG.FinTyp L n} {Φ : σ.S →ₗ[ℂ] A}
    (hΦ : IsEqvA ρ σ Φ) (h : Formalism.AUTREP.GAf L n) (y : A) (hy : y ∈ LinearMap.range Φ) :
    ρ h y ∈ LinearMap.range Φ := by
  obtain ⟨f, rfl⟩ := LinearMap.mem_range.1 hy
  exact ⟨_, hΦ h f⟩

theorem zero_or_inj {ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A} {σ : Formalism.L2.NG.FinTyp L n} {Φ : σ.S →ₗ[ℂ] A}
    (hΦ : IsEqvA ρ σ Φ) : Φ = 0 ∨ Function.Injective Φ := by
  let K : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ) := (LinearMap.ker Φ).map σ.S.subtype
  have hle : K ≤ σ.S := by
    rintro _ ⟨f, -, rfl⟩
    exact f.2
  have hst : ∀ h, ∀ f ∈ K, Formalism.L2.NG.rt L n h f ∈ K := by
    rintro h _ ⟨f, hf, rfl⟩
    refine ⟨⟨_, σ.stable h f f.2⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker] at hf ⊢
    rw [hΦ h f, hf, map_zero]
  rcases σ.irr K hle hst with hK | hK
  · right
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro f hf
    have hm : (f : Formalism.AUTREP.GAf L n → ℂ) ∈ K := ⟨f, hf, rfl⟩
    rw [hK, Submodule.mem_bot] at hm
    exact (Submodule.mem_bot _).2 (Subtype.ext hm)
  · left
    apply LinearMap.ext
    intro f
    have hm : (f : Formalism.AUTREP.GAf L n → ℂ) ∈ K := by rw [hK]; exact f.2
    obtain ⟨g, hg, hgf⟩ := hm
    have e : g = f := Subtype.ext hgf
    subst e
    simpa using hg

theorem inf_bot_or_le {ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A} {σ : Formalism.L2.NG.FinTyp L n} {Φ : σ.S →ₗ[ℂ] A}
    (hΦ : IsEqvA ρ σ Φ) (W : Submodule ℂ A) (hW : ∀ h, ∀ y ∈ W, ρ h y ∈ W) :
    LinearMap.range Φ ⊓ W = ⊥ ∨ LinearMap.range Φ ≤ W := by
  let K : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ) := (W.comap Φ).map σ.S.subtype
  have hle : K ≤ σ.S := by
    rintro _ ⟨f, -, rfl⟩
    exact f.2
  have hst : ∀ h, ∀ f ∈ K, Formalism.L2.NG.rt L n h f ∈ K := by
    rintro h _ ⟨f, hf, rfl⟩
    refine ⟨⟨_, σ.stable h f f.2⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap] at hf ⊢
    rw [hΦ h f]
    exact hW h _ hf
  rcases σ.irr K hle hst with hK | hK
  · left
    rw [eq_bot_iff]
    intro y hy
    rw [Submodule.mem_inf, LinearMap.mem_range] at hy
    obtain ⟨⟨f, rfl⟩, hy⟩ := hy
    have hm : (f : Formalism.AUTREP.GAf L n → ℂ) ∈ K := ⟨f, hy, rfl⟩
    rw [hK, Submodule.mem_bot] at hm
    have e : f = 0 := Subtype.ext hm
    rw [e, map_zero]
    exact Submodule.zero_mem _
  · right
    intro y hy
    rw [LinearMap.mem_range] at hy
    obtain ⟨f, rfl⟩ := hy
    have hm : (f : Formalism.AUTREP.GAf L n → ℂ) ∈ K := by rw [hK]; exact f.2
    obtain ⟨g, hg, hgf⟩ := hm
    have e : g = f := Subtype.ext hgf
    subst e
    exact hg

def Indep {J : Type} (R : J → Submodule ℂ A) (t : Finset J) : Prop :=
  ∀ v : J → A, (∀ j ∈ t, v j ∈ R j) → ∑ j ∈ t, v j = 0 → ∀ j ∈ t, v j = 0

theorem select {ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A} {J : Type} [DecidableEq J] (R : J → Submodule ℂ A)
    (hst : ∀ j h, ∀ y ∈ R j, ρ h y ∈ R j)
    (hirr : ∀ j (W : Submodule ℂ A), (∀ h, ∀ y ∈ W, ρ h y ∈ W) → R j ⊓ W = ⊥ ∨ R j ≤ W) (s : Finset J) :
    ∃ t ⊆ s, Indep R t ∧ ⨆ j ∈ t, R j = ⨆ j ∈ s, R j := by
  have stab : ∀ t : Finset J, ∀ h, ∀ y ∈ ⨆ j ∈ t, R j, ρ h y ∈ ⨆ j ∈ t, R j := by
    intro t h y hy
    have hle : (⨆ j ∈ t, R j) ≤ (⨆ j ∈ t, R j).comap (ρ h) := by
      refine iSup₂_le fun j hj => ?_
      intro z hz
      exact (le_iSup₂ (f := fun j (_ : j ∈ t) => R j) j hj) (hst j h z hz)
    exact hle hy
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨∅, subset_rfl, fun v _ _ j hj => by simp at hj, rfl⟩
  | insert k s hk ih =>
    obtain ⟨t, hts, hind, heq⟩ := ih
    rcases hirr k (⨆ j ∈ t, R j) (stab t) with hd | hle
    · have hkt : k ∉ t := fun h => hk (hts h)
      refine ⟨insert k t, Finset.insert_subset_insert k hts, ?_, ?_⟩
      · intro v hv hsum j hj
        rw [Finset.sum_insert hkt] at hsum
        have hvk : v k = 0 := by
          have h1 : v k ∈ R k ⊓ ⨆ j ∈ t, R j := by
            refine Submodule.mem_inf.2 ⟨hv k (Finset.mem_insert_self k t), ?_⟩
            have e : v k = -∑ j ∈ t, v j := eq_neg_of_add_eq_zero_left hsum
            rw [e]
            refine Submodule.neg_mem _ (Submodule.sum_mem _ fun j hj => ?_)
            exact le_iSup₂ (f := fun j (_ : j ∈ t) => R j) j hj (hv j (Finset.mem_insert_of_mem hj))
          rw [hd] at h1
          exact (Submodule.mem_bot _).1 h1
        rcases Finset.mem_insert.1 hj with rfl | hj
        · exact hvk
        · rw [hvk, zero_add] at hsum
          exact hind v (fun i hi => hv i (Finset.mem_insert_of_mem hi)) hsum j hj
      · rw [Finset.iSup_insert, Finset.iSup_insert, heq]
    · refine ⟨t, hts.trans (Finset.subset_insert k s), hind, ?_⟩
      rw [Finset.iSup_insert, ← heq, sup_eq_right.2 hle]

theorem fix_sum_of_mem {ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A} {σ : Formalism.L2.NG.FinTyp L n}
    (P : (σ.S →ₗ[ℂ] A) → Prop) (U : Set (Formalism.AUTREP.GAf L n)) {ι : Type} [Fintype ι] (b : ι → ℂ)
    (lf : ι → Formalism.AUTREP.GAf L n)
    (H : ∀ ψ ∈ σ.S, (∀ κ ∈ U, Formalism.L2.NG.rt L n κ ψ = ψ) → ∑ i, b i • Formalism.L2.NG.rt L n (lf i) ψ = ψ)
    (x : A) (hx : x ∈ ⨆ (Φ : σ.S →ₗ[ℂ] A) (_ : IsEqvA ρ σ Φ ∧ P Φ), LinearMap.range Φ)
    (hU : ∀ κ ∈ U, ρ κ x = x) : ∑ i, b i • ρ (lf i) x = x := by
  classical
  let J := {Φ : σ.S →ₗ[ℂ] A // IsEqvA ρ σ Φ ∧ P Φ}
  let R : J → Submodule ℂ A := fun j => LinearMap.range j.1
  rw [iSup_subtype'] at hx
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hx
  obtain ⟨t, -, hind, heq⟩ := select (ρ := ρ) R (fun j h y hy => range_equivariantMap_stable j.2.1 h y hy)
    (fun j W hW => inf_bot_or_le j.2.1 W hW) s
  rw [← heq] at hs
  obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ _).1 hs
  have hψ : ∀ j : J, ∃ ψ : σ.S, j.1 ψ = μ j := fun j => LinearMap.mem_range.1 (μ j).2
  choose ψ hψ using hψ
  have hx' : x = ∑ j ∈ t, j.1 (ψ j) := by
    rw [← hμ]
    exact Finset.sum_congr rfl fun j _ => (hψ j).symm
  have hfix : ∀ j ∈ t, ∀ κ ∈ U, j.1 ⟨Formalism.L2.NG.rt L n κ (ψ j), σ.stable κ _ (ψ j).2⟩ = j.1 (ψ j) := by
    intro j hj κ hκ
    have h0 := hind (fun j => j.1 ⟨Formalism.L2.NG.rt L n κ (ψ j), σ.stable κ _ (ψ j).2⟩ - j.1 (ψ j))
      (fun j _ => Submodule.sub_mem _ (LinearMap.mem_range_self _ _) (LinearMap.mem_range_self _ _)) ?_ j hj
    · exact sub_eq_zero.1 h0
    · rw [Finset.sum_sub_distrib]
      have e : ∑ j ∈ t, j.1 ⟨Formalism.L2.NG.rt L n κ (ψ j), σ.stable κ _ (ψ j).2⟩ = ρ κ x := by
        rw [hx', map_sum]
        exact Finset.sum_congr rfl fun j _ => j.2.1 κ (ψ j)
      rw [e, hU κ hκ, ← hx', sub_self]
  have hterm : ∀ j ∈ t, ∑ i, b i • ρ (lf i) (j.1 (ψ j)) = j.1 (ψ j) := by
    intro j hj
    rcases zero_or_inj j.2.1 with h0 | hinj
    · simp [h0]
    · have hψfix : ∀ κ ∈ U, Formalism.L2.NG.rt L n κ ((ψ j : σ.S) : Formalism.AUTREP.GAf L n → ℂ) = ψ j :=
        fun κ hκ => congrArg Subtype.val (hinj (hfix j hj κ hκ))
      have hH := H _ (ψ j).2 hψfix
      have e : ∑ i, b i • (⟨Formalism.L2.NG.rt L n (lf i) (ψ j), σ.stable (lf i) _ (ψ j).2⟩ : σ.S) = ψ j := by
        apply Subtype.ext
        rw [Submodule.coe_sum]
        simpa using hH
      calc ∑ i, b i • ρ (lf i) (j.1 (ψ j))
          = j.1 (∑ i, b i • (⟨Formalism.L2.NG.rt L n (lf i) (ψ j), σ.stable (lf i) _ (ψ j).2⟩ : σ.S)) := by
            rw [map_sum]
            exact Finset.sum_congr rfl fun i _ => by rw [map_smul, j.2.1 (lf i) (ψ j)]
        _ = j.1 (ψ j) := by rw [e]
  calc ∑ i, b i • ρ (lf i) x = ∑ j ∈ t, ∑ i, b i • ρ (lf i) (j.1 (ψ j)) := by
        rw [hx']
        simp only [map_sum, Finset.smul_sum]
        exact Finset.sum_comm
    _ = x := by
        rw [Finset.sum_congr rfl hterm, ← hx']

end Gen

theorem isotIn_conjT_fix_sum : ∀ (D : D7) (n : ℕ) (A : Type) [AddCommGroup A] [Module ℂ A] (ρ : GAf D.host.E n →* Module.End ℂ A) (C : Submodule ℂ A) (π : Formalism.L2.NG.FinTyp D.host.E n) (U : Set (GAf D.host.E n)) (ι : Type) [Finite ι] (a : ι → ℂ) (lf : ι → GAf D.host.E n), (∀ φ ∈ π.S, (∀ κ ∈ U, Formalism.L2.NG.rt D.host.E n κ φ = φ) → ∑ᶠ i, a i • Formalism.L2.NG.rt D.host.E n (lf i) φ = φ) → ∀ S ∈ isotIn ρ C (FinTyp.conjT π), (∀ κ ∈ U, ρ κ S = S) → ∑ᶠ i, star (a i) • ρ (lf i) S = S := by
  intro D n A _ _ ρ C π U ι _ a lf hyp S hS hU
  haveI := Fintype.ofFinite ι
  rw [finsum_eq_sum_of_fintype]
  refine fix_sum_of_mem (σ := FinTyp.conjT π) (fun Φ => LinearMap.range Φ ≤ C) U (fun i => star (a i)) lf ?_ S hS hU
  intro ψ hψ hfix
  have hφ : (fun g => star (ψ g)) ∈ π.S := hψ
  have h1 := hyp _ hφ (fun κ hκ => by rw [← conj_rt, hfix κ hκ])
  rw [finsum_eq_sum_of_fintype] at h1
  funext g
  have h2 := congrArg star (congrFun h1 g)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, star_sum, star_mul', star_star, rt_apply] at h2
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, rt_apply]
  exact h2

end GlobalTheory.IsotConjFix
