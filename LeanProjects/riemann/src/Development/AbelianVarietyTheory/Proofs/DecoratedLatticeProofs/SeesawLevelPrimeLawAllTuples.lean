import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLevelPrimeLawDoubleStepStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPrimeLawLastTwoStepsAllTuplesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedOperatorsBijectiveAtPlaces

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevPrimeAll

variable {D : D7}

open GlobalTheory.FinPl.AllBij in

theorem ram_sOp {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
    {p : ι → SplitPt D k} {n : Type} [Fintype n] [DecidableEq n] {A : HSp D} (α : ∀ i, Frame (p i) A n) (P : ι → Pair k n)
    (hinj : Function.Injective fun i => (p i).v) (q : Unif k) (χ : AddChar k Circle) (hχ : HasConductor χ 1) (ε : 𝓀[k]ˣ) (i : ι)
    (φ : GA D A → ℂ) (hφ : IsContAut A φ ∧ ∀ j, RamAt (α j) (P j) φ) :
    IsContAut A (sOp (α i) (P i) q (resChar χ hχ q) ε φ) ∧ ∀ j, RamAt (α j) (P j) (sOp (α i) (P i) q (resChar χ hχ q) ε φ) := by
  obtain ⟨hbij, -, c, c', hc, -⟩ := GlobalTheory.T.ramifiedOperator_bijective_finite_translation_combination D k (p i) n q χ hχ _ rfl ε A (α i) (P i)
  have hC := mapDomain_mem _ (gl_mem (α i)) c
  have hT : ∀ φ, sOp (α i) (P i) q (resChar χ hχ q) ε φ = act (Finsupp.mapDomain (α i).gl c) φ :=
    fun φ => (hc φ).trans (sum_rep_eq _ _ _)
  refine ⟨?_, fun j => ?_⟩
  · rw [hT]; exact isContAut_act _ hφ.1
  · rcases eq_or_ne j i with rfl | hj
    · exact hbij.mapsTo (hφ.2 j)
    · rw [hT]
      exact ramAt_act _ _ _ (fun x hx g => grpAt_comm A (fun e => hj (hinj e)) (hC x hx) (gl_mem _ g)) (hφ.2 j)

theorem ram_S {c : Comm D} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
    (o : TDat c k ι) (hinj : Function.Injective fun i => (o.p i).v) (ε : ℕ → ι → 𝓀[k]ˣ) (j : ℕ) (φ : GA D (c.X j) → ℂ)
    (hφ : φ ∈ o.Ram j) : o.S ε j φ ∈ o.Ram j := by
  unfold TDat.S
  induction o.I with
  | nil => exact hφ
  | cons i l ih => exact ram_sOp (o.β j) (o.Q j) hinj o.q (o.χ i) (o.hχ i) (ε j i) i _ ih

theorem exists_choice (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι) (hc : c.Is) (hv : v.Is) (hS : ShapeOff v o) (j : ℕ) :
    ∃ (ε : ι → 𝓀[k]ˣ) (op : BiOp (c.X j) (c.X (j + 1)) (c.X (j + 1 + 1))) (r : ι → ℝ) (e : ι → ℤ), (∀ i, 0 < r i) ∧
      OpAt (· ∈ v.tP) op ∧
      (∀ σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∀ t : Tup c, t.Is → WeilOK (t := t) v → t.UnrOn (· ∈ v.tP) → ∀ Ψ₁ Ψ₂,
        Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.tP) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ v.tP) Ψ₂ →
        BiVacAt c.ψ (c.x j).L (c.x (j + 1)).L (c.x (j + 1 + 1)).L (· ∈ v.tP)
          (op.app c.ψ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂)) ∧
        ∀ d d', CombAt (· ∉ v.tP) d → CombAt (· ∉ v.tP) d' → ∀ φ ∈ o.Ram j,
          c.bl j (t.kom j) (t.kom (j + 1)) φ (biComb c.ψ _ _ _ d d' (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂)) =
            o.mono r e (t.sBF j (σ + 1) h).χW • c.bl j (t.kom j) (t.kom (j + 1)) (o.S (fun _ => ε) j φ)
              (biComb c.ψ _ _ _ d d' (biComb c.ψ _ _ _ (v.dT j) (v.dT (j + 1))
                (op.app c.ψ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂))))) ∧
      ∀ (h : j + 2 * 0 + 2 = D.R.m), ∀ t : Tup c, t.Is → WeilOK (t := t) v → t.UnrOn (· ∈ v.tP) → t.UnrK (· ∈ v.tP) → ∀ Ψ₁ Ψ₂,
        Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.tP) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) v.NT (· ∈ v.tP) Ψ₂ →
        BiVacAt c.ψ (c.x j).L (c.x (j + 1)).L (c.x (j + 1 + 1)).L (· ∈ v.tP)
          (op.app c.ψ (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)) ∧
        ∀ d d', CombAt (· ∉ v.tP) d → CombAt (· ∉ v.tP) d' → ∀ φ ∈ o.Ram j, ∀ f, IsContAut c.T f →
          ∫ h' in c.volT.𝓕, f h' * c.bl j (t.kom j) (t.kom (j + 1)) φ
              (biComb c.ψ _ _ _ d d' (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)) ((c.oT (j + 1 + 1) h).emb (h', 1)) ∂c.volT.μ =
            o.mono r e (t.sBF j 0 h).χW * ∫ h' in c.volT.𝓕, f h' * c.bl j (t.kom j) (t.kom (j + 1)) (o.S (fun _ => ε) j φ)
              (biComb c.ψ _ _ _ d d' (biComb c.ψ _ _ _ (v.dT j) (v.dT (j + 1))
                (op.app c.ψ (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)))) ((c.oT (j + 1 + 1) h).emb (h', 1)) ∂c.volT.μ := by
  by_cases h1 : ∃ σ, j + 2 * (σ + 1) + 2 = D.R.m
  · obtain ⟨σ, h⟩ := h1
    obtain ⟨ε, op, r, e, hr, hop, H⟩ := GlobalTheory.T.seeSawLevelPrimeLaw_doubleStep D c v k ι o hc hv hS j σ h
    refine ⟨ε, op, r, e, hr, hop, fun σ' h' => ?_, fun h' => absurd h' (by omega)⟩
    obtain rfl : σ = σ' := by omega
    exact H
  · by_cases h2 : j + 2 * 0 + 2 = D.R.m
    · obtain ⟨ε, op, r, e, hr, hop, H⟩ := GlobalTheory.T.levelPrime_law_last_two_steps_all_tuples D c v k ι o hc hv hS j h2
      exact ⟨ε, op, r, e, hr, hop, fun σ h => absurd ⟨σ, h⟩ h1, fun _ => H⟩
    · exact ⟨fun _ => 1, ⟨0, Fin.elim0, Fin.elim0⟩, fun _ => 1, fun _ => 0, fun _ => one_pos, fun i => i.elim0,
        fun σ h => absurd ⟨σ, h⟩ h1, fun h => absurd h h2⟩

theorem lawLevelPrime_all : ∀ D : D7, GlobalTheory.SeeSaw.TOfShape D := by
  intro D c v k _ _ _ _ ι o hc hv hS
  choose ε op r e hr hop Hm Hl using exists_choice c v k ι o hc hv hS
  refine ⟨ε, op, r, e, hr, ?_, fun t w ht hW hU hK hT => ⟨?_, ?_⟩⟩
  · refine ⟨hv.disj, hv.sd, hv.sdT, hv.b, hv.bT, hv.Ψ, hv.ΨT, hv.JG, hv.atG, fun j => ⟨(hv.atT j).1, hop j⟩, fun j φ hφ => ?_⟩
    refine ⟨(hv.ram j φ hφ).1, ?_⟩
    change o.S ε j φ ∈ v.RamAd j
    change φ ∈ v.RamAd j at hφ
    rw [hS.ram j] at hφ ⊢
    exact ram_S o hS.pre.inj ε j φ hφ
  · intro j σ h Ψ₁ Ψ₂ h₁ h₂
    obtain ⟨H1, H2⟩ := Hm j σ h t ht hW hU Ψ₁ Ψ₂ h₁ h₂
    refine ⟨H1, fun d d' hd hd' φ hφ => ?_⟩
    rw [hT j (σ + 1) h]
    exact H2 d d' hd hd' φ (hS.ram j ▸ hφ)
  · intro j h Ψ₁ Ψ₂ h₁ h₂
    obtain ⟨H1, H2⟩ := Hl j h t ht hW hU hK Ψ₁ Ψ₂ h₁ h₂
    refine ⟨H1, fun d d' hd hd' φ hφ f hf _ => ?_⟩
    rw [hT j 0 h]
    exact H2 d d' hd hd' φ (hS.ram j ▸ hφ) f hf

end GlobalTheory.LevPrimeAll

end
