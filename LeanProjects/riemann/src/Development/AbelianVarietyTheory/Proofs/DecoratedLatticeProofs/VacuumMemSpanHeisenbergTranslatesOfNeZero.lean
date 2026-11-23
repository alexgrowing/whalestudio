import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainStepsAreGridArrows
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacCyclic

theorem exists_mem_of_eigen {X ι U : Type} [AddCommGroup X] [Module ℂ X] (v : ι → X) (A : U → X →ₗ[ℂ] X) (χ : ι → U → ℂ)
    (hA : ∀ i u, A u (v i) = χ i u • v i) (hp : ∀ i j, (∀ u, χ i u = χ j u) → v i ∈ Submodule.span ℂ {v j})
    (W : Submodule ℂ X) (hW : ∀ u, ∀ x ∈ W, A u x ∈ W) (s : Finset ι) :
    ∀ f ∈ Submodule.span ℂ (v '' s), f ∈ W → f ≠ 0 → ∃ i, v i ∈ W := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
  intro f hf hfW hf0

  have hrem : ∀ i ∈ s, ∀ u, A u f - χ i u • f ∈ Submodule.span ℂ (v '' (s.erase i : Finset ι)) := by
    intro i _ u
    have : Submodule.span ℂ (v '' s) ≤
        (Submodule.span ℂ (v '' (s.erase i : Finset ι))).comap (A u - χ i u • LinearMap.id) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, hj, rfl⟩
      show A u (v j) - χ i u • v j ∈ Submodule.span ℂ (v '' (s.erase i : Finset ι))
      rw [hA, ← sub_smul]
      by_cases h : j = i
      · rw [h, sub_self, zero_smul]; exact zero_mem _
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, Finset.mem_coe.2 (Finset.mem_erase.2 ⟨h, hj⟩), rfl⟩)
    exact this hf
  rcases s.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
  · simp at hf; exact absurd hf hf0
  by_cases hall : ∀ j ∈ s, ∀ u, χ j u = χ i u
  · have : Submodule.span ℂ (v '' s) ≤ Submodule.span ℂ {v i} := by
      rw [Submodule.span_le]
      rintro _ ⟨j, hj, rfl⟩
      exact hp j i (hall j hj)
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 (this hf)
    have hc : c ≠ 0 := by rintro rfl; exact hf0 (zero_smul _ _)
    exact ⟨i, (W.smul_mem_iff hc).1 hfW⟩
  · push Not at hall
    obtain ⟨j, hj, u, hu⟩ := hall
    have hm : ∀ k, A u f - χ k u • f ∈ W := fun k => W.sub_mem (hW u f hfW) (W.smul_mem _ hfW)
    by_cases h0 : A u f - χ i u • f = 0
    · refine ih _ (Finset.erase_ssubset hj) _ (hrem j hj u) (hm j) fun h1 => hf0 ?_
      have : (χ j u - χ i u) • f = 0 := by
        rw [sub_smul, ← sub_eq_zero.1 h0, ← sub_eq_zero.1 h1, sub_self]
      exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hu)
    · exact ih _ (Finset.erase_ssubset hi) _ (hrem i hi u) (hm i) h0

theorem psi_ne_zero {A : Type} [AddCommGroup A] (ψ : AddChar A ℂ) (x : A) : ψ x ≠ 0 := fun h => by
  have := ψ.map_add_eq_mul x (-x)
  rw [add_neg_cancel, ψ.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

theorem fin_add {D : D7} {S T : HSp D} {a b : WO S T} (ha : a.map (infPart D) = 0) (hb : b.map (infPart D) = 0) :
    (a + b).map (infPart D) = 0 := by
  ext i j
  have h1 : infPart D (a i j) = 0 := congrFun (congrFun ha i) j
  have h2 : infPart D (b i j) = 0 := congrFun (congrFun hb i) j
  show infPart D (a i j + b i j) = 0
  rw [RingHom.map_add, h1, h2, add_zero]

theorem fin_neg {D : D7} {S T : HSp D} {a : WO S T} (ha : a.map (infPart D) = 0) : (-a).map (infPart D) = 0 := by
  ext i j
  have h1 : infPart D (a i j) = 0 := congrFun (congrFun ha i) j
  show infPart D (-a i j) = 0
  rw [RingHom.map_neg, h1, neg_zero]

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem fin_zero : (0 : WO S T).map (infPart D) = 0 := by
  ext i j
  show infPart D (0 : AE D) = 0
  exact RingHom.map_zero _

theorem symplO_neg_right (u b : WO S T) : symplO S T u (-b) = -symplO S T u b := by
  refine eq_neg_of_add_eq_zero_left ?_
  rw [← GlobalTheory.LatVac.symplO_add_right, neg_add_cancel, GlobalTheory.SplitScalar.symplO_zero_right]

theorem psi_diff {u a b : WO S T} (h : ψ (symplO S T u a) = ψ (symplO S T u b)) : ψ (symplO S T (-b + a) u) = 1 := by
  rw [GlobalTheory.SplitScalar.symplO_skew S T u, GlobalTheory.LatVac.symplO_add_right, symplO_neg_right, neg_add, neg_neg,
    ψ.map_add_eq_mul, ← h, ← ψ.map_add_eq_mul, add_neg_cancel, ψ.map_zero_eq_one]

theorem prop_of_eigen {a b : WO S T} {f₀ : WO S T → ℂ} {ε : ℂ} (h : heisO ψ S T (-b + a) f₀ = ε • f₀) :
    heisO ψ S T a f₀ ∈ Submodule.span ℂ {heisO ψ S T b f₀} := by
  have e := GlobalTheory.LatVac.heisO_heisO ψ b (-b + a) f₀
  rw [h, GlobalTheory.LatVac.heisO_smul, add_neg_cancel_left] at e
  refine (Submodule.smul_mem_iff _ (psi_ne_zero ψ (symplOH S T b (-b + a)))).1 ?_
  rw [← e]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem heis_mem_span {f x : WO S T → ℂ} {b : WO S T} (hb : b.map (infPart D) = 0)
    (hx : x ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f)) :
    heisO ψ S T b x ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f) := by
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hx
  rw [← GlobalTheory.SplitScalar.heisL_apply, Finsupp.sum, map_sum]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [map_smul, GlobalTheory.SplitScalar.heisL_apply, GlobalTheory.LatVac.heisO_heisO]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨b + a, fin_add hb a.2⟩, rfl⟩))

theorem mem_of_heis_mem {W : Submodule ℂ (WO S T → ℂ)} {f₀ : WO S T → ℂ} {a : WO S T}
    (h : heisO ψ S T (-a) (heisO ψ S T a f₀) ∈ W) : f₀ ∈ W := by
  rw [GlobalTheory.LatVac.heisO_heisO, neg_add_cancel, GlobalTheory.LatVac.heisO_zero] at h
  exact (W.smul_mem_iff (psi_ne_zero ψ _)).1 h

theorem mem_span_of_dual (Λ : AddSubgroup (WO S T)) (hfin : ∀ u ∈ Λ, u.map (infPart D) = 0)
    (hdual : ∀ u : WO S T, u.map (infPart D) = 0 → (∀ u' ∈ Λ, ψ (symplO S T u u') = 1) → u ∈ Λ) {f₀ f : WO S T → ℂ}
    (hε : ∀ u : Λ, ∃ ε : ℂ, ε ≠ 0 ∧ heisO ψ S T u f₀ = ε • f₀)
    (hf : f ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f₀))
    (hf0 : f ≠ 0) :
    f₀ ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f) := by
  choose ε hε0 hε using hε
  have hfW : f ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f) :=
    Submodule.subset_span ⟨⟨0, fin_zero⟩, GlobalTheory.LatVac.heisO_zero ψ f⟩
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hf
  have hfs : f ∈ Submodule.span ℂ ((fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f₀) '' c.support) := by
    rw [← hc]
    exact Submodule.sum_mem _ fun a ha => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)
  obtain ⟨a, ha⟩ := exists_mem_of_eigen (fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f₀)
    (fun u : Λ => GlobalTheory.SplitScalar.heisL ψ S T u) (fun a u => ψ (symplO S T u a) * ε u)
    (fun a u => by
      rw [GlobalTheory.SplitScalar.heisL_apply, GlobalTheory.SplitScalar.heisO_comm, hε, GlobalTheory.LatVac.heisO_smul, smul_smul])
    (fun a b h => prop_of_eigen (hε ⟨_, hdual _ (fin_add (fin_neg b.2) a.2) fun u hu =>
      psi_diff (mul_right_cancel₀ (hε0 ⟨u, hu⟩) (h ⟨u, hu⟩))⟩))
    _ (fun u x hx => by
      rw [GlobalTheory.SplitScalar.heisL_apply]
      exact heis_mem_span (hfin u u.2) hx) c.support f hfs hfW hf0
  exact mem_of_heis_mem (heis_mem_span (fin_neg a.2) ha)

theorem vac_mem_span : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {f₀ f : WO S T → ℂ}, IsVacO ψ θ S T sS sT ΛS ΛT f₀ → IsSelfDualC S ΛS → IsSelfDualC T ΛT → f ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f₀) → f ≠ 0 → f₀ ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f) := by
  intro D ψ θ S T sS sT ΛS ΛT f₀ f hv hS hT hf hf0
  obtain ⟨hdual, -, hsign⟩ := GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hv.1 hS hT
  refine mem_span_of_dual _ (fun u hu => GlobalTheory.SplitScalar.latO_fin hu) (fun u hu h => (hdual u hu).2 h) (fun u => ?_) hf hf0
  obtain ⟨ε, h1, h2⟩ := hsign f₀ hv.2.lat u u.2
  refine ⟨ε, ?_, h2 f₀ hv.2.lat⟩
  rcases h1 with rfl | rfl <;> simp

end GlobalTheory.VacCyclic

end
