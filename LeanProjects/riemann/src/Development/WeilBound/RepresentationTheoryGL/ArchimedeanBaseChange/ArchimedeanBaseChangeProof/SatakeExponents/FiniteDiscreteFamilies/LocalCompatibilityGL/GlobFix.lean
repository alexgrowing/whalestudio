import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.LocalCompatibilityGL.FinDiscNOf
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.EventuallySatV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocEqOneOfMemGam
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsIrreducibleIff

noncomputable section

open NumberField IsDedekindDomain Matrix Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CuspRep.LocEx

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.F5.Bo

namespace GlobalFixedVectorsAlt

section A

variable {G U V ι : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]

end A

section C

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

omit [IsCMField E] in

theorem tendsto_of_eq_on (c : Af E) (hc : ∀ u, pLoc E u c ∈ u.adicCompletionIntegers E)
    (x : Finset (HeightOneSpectrum (𝓞 E)) → Af E) (hx : ∀ F u, pLoc E u (x F) ∈ u.adicCompletionIntegers E)
    (hxc : ∀ F, ∀ u ∈ F, pLoc E u (x F) = pLoc E u c) : Tendsto x atTop (𝓝 c) := by
  let A : ∀ w : HeightOneSpectrum (𝓞 E), Set (w.adicCompletion E) := fun w => w.adicCompletionIntegers E
  let y : Finset (HeightOneSpectrum (𝓞 E)) → ∀ w, A w := fun F w => ⟨pLoc E w (x F), hx F w⟩
  let y0 : ∀ w, A w := fun w => ⟨pLoc E w c, hc w⟩
  have hy : Tendsto y atTop (𝓝 y0) := by
    rw [tendsto_pi_nhds]
    intro w
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop {w}] with F hF
    exact Subtype.ext (hxc F w (hF (Finset.mem_singleton_self w))).symm
  have h2 := ((RestrictedProduct.isEmbedding_structureMap (A := A) (𝓕 := cofinite)).continuous.tendsto y0).comp hy
  exact h2

theorem exists_finset_of_mem_nhds {H : Set (GL (Fin N) (Af E))} (hH : H ∈ 𝓝 1) :
    ∃ F : Finset (HeightOneSpectrum (𝓞 E)), ∀ g : GL (Fin N) (Af E),
      (∀ u, GeneralLinearGroup.map (pLoc E u) g ∈ GlobalTheory.LFun.KGL u N) →
      (∀ u ∈ F, GeneralLinearGroup.map (pLoc E u) g = 1) → g ∈ H := by
  by_contra hc
  push Not at hc
  choose g hgK hg1 hgH using hc
  have hone : ∀ (u : HeightOneSpectrum (𝓞 E)) (i j : Fin N),
      pLoc E u ((1 : Matrix (Fin N) (Fin N) (Af E)) i j) = (1 : Matrix (Fin N) (Fin N) (u.adicCompletion E)) i j := by
    intro u i j
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have honeI : ∀ (u : HeightOneSpectrum (𝓞 E)) (i j : Fin N),
      pLoc E u ((1 : Matrix (Fin N) (Fin N) (Af E)) i j) ∈ u.adicCompletionIntegers E := by
    intro u i j
    rw [hone, Matrix.one_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  have ht : Tendsto g atTop (𝓝 1) := by
    rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
    refine Tendsto.prodMk_nhds ?_ ((MulOpposite.continuous_op.tendsto _).comp ?_)
    · refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
      refine tendsto_of_eq_on _ (fun u => honeI u i j) (fun F => (g F).val i j)
        (fun F u => (GlobalTheory.EulerTwRestr.mem_KGL_iff.1 (hgK F u)).1 i j) (fun F u hu => ?_)
      rw [hone]
      exact congrArg (fun x : GL (Fin N) (u.adicCompletion E) => x.1 i j) (hg1 F u hu)
    · refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
      refine tendsto_of_eq_on _ (fun u => honeI u i j) (fun F => ((g F)⁻¹).val i j)
        (fun F u => by
          have := (GlobalTheory.EulerTwRestr.mem_KGL_iff.1 (hgK F u)).2 i j
          rwa [GlobalTheory.EulerTwRestr.loc_inv_val] at this) (fun F u hu => ?_)
      rw [hone]
      have h1 : GeneralLinearGroup.map (pLoc E u) (g F)⁻¹ = 1 := by rw [map_inv, hg1 F u hu, inv_one]
      exact congrArg (fun x : GL (Fin N) (u.adicCompletion E) => x.1 i j) h1
  obtain ⟨F, hF⟩ := (ht.eventually_mem hH).exists
  exact hgH F hF

end C

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

def TyW (W : Submodule ℂ (Kinf E N → ℂ)) (χ : Sm E N) : Prop :=
  ∀ g, (fun k : Kinf E N => χ.1 (g * infGL E N (Unitary.toUnits k))) ∈ W

def FixAt (Kf : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin N) (w.adicCompletion E)))
    (u : HeightOneSpectrum (𝓞 E)) (χ : Sm E N) : Prop :=
  ∀ k ∈ Kf u, finRep E N (locGL E N u k) χ = χ

theorem fixAt_locGL {Kf : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin N) (w.adicCompletion E))}
    {u w : HeightOneSpectrum (𝓞 E)} (h : u ≠ w) {χ : Sm E N} (hχ : FixAt Kf u χ)
    (g : GL (Fin N) (w.adicCompletion E)) : FixAt Kf u (finRep E N (locGL E N w g) χ) := by
  intro k hk
  rw [← Module.End.mul_apply, ← map_mul,
    LocSph.comm_locGL w (locGL E N u k) (pLoc_locGL_of_ne (Ne.symm h) k) g, map_mul, Module.End.mul_apply,
    hχ k hk]

theorem fix_of_fixAll {Kf : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin N) (w.adicCompletion E))}
    (hcof : ∀ᶠ w in Filter.cofinite, Kf w = GlobalTheory.LFun.KGL w N) {χ : Sm E N} (hχ : IsAutForm χ)
    (hfix : ∀ u, FixAt Kf u χ) : ∀ v ∈ globL Kf, finRep E N v χ = χ := by
  classical
  obtain ⟨F, hF⟩ := exists_finset_of_mem_nhds (N := N) (E := E) (hχ.level.mem_nhds (by simp))
  have key : ∀ T : Finset (HeightOneSpectrum (𝓞 E)), ∀ v : GL (Fin N) (Af E),
      (∀ u ∈ T, GeneralLinearGroup.map (pLoc E u) v ∈ Kf u) →
      (∀ u ∉ T, GeneralLinearGroup.map (pLoc E u) v ∈ GlobalTheory.LFun.KGL u N ∧
        (u ∈ F → GeneralLinearGroup.map (pLoc E u) v = 1)) → finRep E N v χ = χ := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro v _ h2
      exact hF v (fun u => (h2 u (Finset.notMem_empty u)).1) fun u hu => (h2 u (Finset.notMem_empty u)).2 hu
    | insert w T hwT ih =>
      intro v h1 h2
      set a := locGL E N w (GeneralLinearGroup.map (pLoc E w) v) with ha
      have hc : ∀ u, GeneralLinearGroup.map (pLoc E u) (a⁻¹ * v) =
          if u = w then 1 else GeneralLinearGroup.map (pLoc E u) v := fun u => by
        split_ifs with e
        · subst e; rw [map_mul, map_inv, ha, pLoc_locGL, inv_mul_cancel]
        · rw [map_mul, map_inv, ha, pLoc_locGL_of_ne e, inv_one, one_mul]
      have h3 : finRep E N (a⁻¹ * v) χ = χ := ih _ (fun u hu => by
          rw [hc, if_neg (fun e : u = w => hwT (by rw [← e]; exact hu))]; exact h1 u (Finset.mem_insert_of_mem hu))
        fun u hu => by
          rw [hc]
          split_ifs with e
          · exact ⟨one_mem _, fun _ => rfl⟩
          · exact h2 u (by simp [e, hu])
      rw [← mul_inv_cancel_left a v, map_mul, Module.End.mul_apply, h3]
      exact hfix w _ (h1 w (Finset.mem_insert_self w T))
  intro v hv
  have hv' : ∀ u, GeneralLinearGroup.map (pLoc E u) v ∈ Kf u := fun u => by
    simpa [globL, Subgroup.mem_iInf] using Subgroup.mem_iInf.1 hv u
  have hfin := Filter.eventually_cofinite.1 hcof
  refine key (F ∪ hfin.toFinset) v (fun u _ => hv' u) fun u hu => ?_
  simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_or, not_not] at hu
  exact ⟨hu.2 ▸ hv' u, fun h => absurd h hu.1⟩

end GlobalFixedVectorsAlt

end PositivityTheory.Rg.BcB.F.F5.Bo

end
