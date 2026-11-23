import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
open NumberField IsDedekindDomain ReciprocityTheory.Aut

noncomputable section

namespace GlobalTheory.SumTransIso

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

theorem sumRt_iso {ρ : Representation ℂ (GQ L n) W} {S S' : Submodule ℂ (Formalism.AUTREP.GAf L n → W)}
    (hS : Formalism.L2.NG.IsSubrep ρ S) (hiso : Formalism.L2.NG.IsoRep S S')
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) {ι : Type} (R : Finset ι) (r : ι → Formalism.AUTREP.GAf L n) (c : ℂ)
    (hc : ∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ f = f) →
      ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f)
    (f' : Formalism.AUTREP.GAf L n → W) (hf' : f' ∈ S')
    (hfix : ∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ f' = f') :
    ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f' = c • f' := by
  obtain ⟨T, hT⟩ := hiso
  set f : S := T.symm ⟨f', hf'⟩ with hfdef
  have hTf : T f = ⟨f', hf'⟩ := T.apply_symm_apply _
  have hrt : ∀ h : Formalism.AUTREP.GAf L n,
      ((T ⟨Formalism.L2.NG.rt L n h f, hS.stable h _ f.2⟩ : S') : Formalism.AUTREP.GAf L n → W) = Formalism.L2.NG.rt L n h f' := by
    intro h
    have := hT h f ⟨_, hS.stable h _ f.2⟩ rfl
    rw [this, hTf]
  have hffix : ∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ (f : Formalism.AUTREP.GAf L n → W) = f := by
    intro κ hκ ht
    have h1 := hrt κ
    rw [hfix κ hκ ht] at h1
    have h2 : T ⟨_, hS.stable κ _ f.2⟩ = T f := Subtype.ext (by rw [h1, hTf])
    exact congrArg Subtype.val (T.injective h2)
  have hcf := hc f f.2 hffix
  let σ : S := ∑ γ ∈ R, (⟨Formalism.L2.NG.rt L n (r γ) f, hS.stable _ _ f.2⟩ : S)
  have hσ : (σ : Formalism.AUTREP.GAf L n → W) = ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f := by
    simp only [σ, Submodule.coe_sum]
  have hTσ : ((T σ : S') : Formalism.AUTREP.GAf L n → W) = ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f' := by
    simp only [σ, map_sum, Submodule.coe_sum]
    exact Finset.sum_congr rfl fun γ _ => hrt _
  have key : σ = c • f := Subtype.ext (by rw [hσ, Submodule.coe_smul]; exact hcf)
  have h3 := congrArg (fun y => ((T y : S') : Formalism.AUTREP.GAf L n → W)) key
  simp only [map_smul, Submodule.coe_smul, hTσ, hTf] at h3
  exact h3

theorem iSup_finset_stable (t : Finset (Submodule ℂ (Formalism.AUTREP.GAf L n → W)))
    (ht : ∀ i ∈ t, ∀ h, ∀ f ∈ i, Formalism.L2.NG.rt L n h f ∈ i) (h : Formalism.AUTREP.GAf L n) :
    ∀ f ∈ (⨆ i ∈ t, i), Formalism.L2.NG.rt L n h f ∈ (⨆ i ∈ t, i) := by
  have hle : (⨆ i ∈ t, i) ≤ (⨆ i ∈ t, i).comap (Formalism.L2.NG.rt L n h) := by
    refine iSup₂_le fun i hi => ?_
    intro f hf
    exact (le_iSup₂ (f := fun i (_ : i ∈ t) => i) i hi) (ht i hi h f hf)
  exact fun f hf => hle hf

theorem sumRt_finset_sum {ρ : Representation ℂ (GQ L n) W} {S : Submodule ℂ (Formalism.AUTREP.GAf L n → W)}
    (hS : Formalism.L2.NG.IsIrrRep ρ S)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) {ι : Type} (R : Finset ι) (r : ι → Formalism.AUTREP.GAf L n) (c : ℂ)
    (hc : ∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ f = f) →
      ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f)
    (t : Finset (Submodule ℂ (Formalism.AUTREP.GAf L n → W))) :
    ((↑t : Set (Submodule ℂ (Formalism.AUTREP.GAf L n → W))) ⊆ {S' | Formalism.L2.NG.IsIrrRep ρ S' ∧ Formalism.L2.NG.IsoRep S S'}) → ∀ f ∈ (⨆ i ∈ t, i),
      (∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ f = f) →
      ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro _ f hf _
    simp only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot] at hf
    subst hf
    simp
  | insert a t ha ih =>
    intro hsub f hf hfix
    have haF : Formalism.L2.NG.IsIrrRep ρ a ∧ Formalism.L2.NG.IsoRep S a := hsub (Finset.mem_insert_self a t)
    have htF : (↑t : Set _) ⊆ {S' | Formalism.L2.NG.IsIrrRep ρ S' ∧ Formalism.L2.NG.IsoRep S S'} :=
      fun x hx => hsub (Finset.mem_insert_of_mem hx)
    rw [Finset.iSup_insert] at hf
    have hMst : ∀ h, ∀ g ∈ (⨆ i ∈ t, i), Formalism.L2.NG.rt L n h g ∈ (⨆ i ∈ t, i) :=
      iSup_finset_stable t (fun i hi => (htF hi).1.1.stable)
    have hsubrep : Formalism.L2.NG.IsSubrep ρ (a ⊓ ⨆ i ∈ t, i) :=
      ⟨inf_le_left.trans haF.1.1.le, fun h g hg => ⟨haF.1.1.stable h g hg.1, hMst h g hg.2⟩⟩
    rcases haF.1.2.2 _ hsubrep inf_le_left with h0 | htop
    · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hf
      have hyfix : ∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ y = y := by
        intro κ hκ hκt
        have e := hfix κ hκ hκt
        rw [map_add] at e
        have hd : Formalism.L2.NG.rt L n κ y - y ∈ a ⊓ ⨆ i ∈ t, i := by
          refine ⟨Submodule.sub_mem _ (haF.1.1.stable κ y hy) hy, ?_⟩
          have h4 : Formalism.L2.NG.rt L n κ y - y = z - Formalism.L2.NG.rt L n κ z := by
            rw [sub_eq_sub_iff_add_eq_add, e]
            exact add_comm _ _
          rw [h4]
          exact Submodule.sub_mem _ hz (hMst κ z hz)
        rw [h0, Submodule.mem_bot, sub_eq_zero] at hd
        exact hd
      have hzfix : ∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ z = z := by
        intro κ hκ hκt
        have e := hfix κ hκ hκt
        rw [map_add, hyfix κ hκ hκt] at e
        exact add_left_cancel e
      have e1 := sumRt_iso hS.1 haF.2 v R r c hc y hy hyfix
      have e2 := ih htF z hz hzfix
      simp only [map_add, Finset.sum_add_distrib, e1, e2, smul_add]
    · have hle : a ≤ ⨆ i ∈ t, i := inf_eq_left.1 htop
      exact ih htF f ((sup_le hle le_rfl) hf) hfix

theorem sumRt_isoTyp : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : Formalism.L2.NG.AlgWt L n)
    (S : Submodule ℂ (Formalism.AUTREP.GAf L n → a.W)), Formalism.L2.NG.IsIrrRep a.ρ S →
    ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (ι : Type) (R : Finset ι) (r : ι → Formalism.AUTREP.GAf L n) (c : ℂ),
    (∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ f = f) →
      ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f) →
    ∀ f ∈ Formalism.L2.NG.isoTyp a.ρ S, (∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ f = f) →
      ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f := by
  intro L _ _ _ n a S hS v ι R r c hc f hf hfix
  obtain ⟨t, ht, hft⟩ := Submodule.mem_sSup_iff_exists_finset.1 hf
  exact sumRt_finset_sum hS v R r c hc t ht f hft hfix

end GlobalTheory.SumTransIso
