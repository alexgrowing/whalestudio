import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.IndexExponentDegree
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PerOComponents

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.ThetaMove.VolumePos

section Index

variable {E : Type} [Field E] [NumberField E] {W : Type} [AddCommGroup W] [Module (𝓞 E) W]

theorem relIndex_ne_zero {M₀ M : Submodule (𝓞 E) W} (h₀ : Full M₀) (hM : M.FG) :
    M₀.toAddSubgroup.relIndex M.toAddSubgroup ≠ 0 := by
  haveI : Module.Finite (𝓞 E) M := Module.Finite.iff_fg.2 hM
  haveI : Module.Finite ℤ M := Module.Finite.trans (𝓞 E) M
  haveI : AddGroup.FG M.toAddSubgroup := Module.Finite.iff_addGroup_fg.1 ‹Module.Finite ℤ M›
  have : Finite (M.toAddSubgroup ⧸ M₀.toAddSubgroup.addSubgroupOf M.toAddSubgroup) := by
    apply AddCommGroup.finite_of_fg_torsion
    intro q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨n, hn, hx⟩ := h₀ x
    refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, hn, ?_⟩
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    rw [Nat.cast_smul_eq_nsmul] at hx
    exact hx
  exact AddSubgroup.index_ne_zero_of_finite

theorem relIndex_localized_ne_zero (P : HeightOneSpectrum (𝓞 E)) {M₀ M : Submodule (𝓞 E) W} (h₀ : Full M₀) (h : Full M) (hM : M.FG) :
    (localization₂ P.asIdeal M₀).toAddSubgroup.relIndex (localization₂ P.asIdeal M).toAddSubgroup ≠ 0 := by
  intro h0
  have hle : (localization₂ P.asIdeal M).toAddSubgroup ≤ M.toAddSubgroup ⊔ (localization₂ P.asIdeal M₀).toAddSubgroup := by
    intro x hx
    obtain ⟨t, h1, h2⟩ := (h.inf h₀).approx {P} x
    have h3 := h1 P (Finset.mem_singleton_self P)
    have ht : t ∈ M := mem_of_locP fun Q => by
      by_cases hQ : Q = P
      · subst hQ
        have := (localization₂ Q.asIdeal M).add_mem (localization_mono Q inf_le_left h3) hx
        rwa [sub_add_cancel] at this
      · exact localization_mono Q inf_le_left (h2 Q (by simpa using hQ))
    have : x = t - (t - x) := by abel
    rw [this]
    exact sub_mem (AddSubgroup.mem_sup_left ht) (AddSubgroup.mem_sup_right (localization_mono P inf_le_right h3))
  have h4 := AddSubgroup.relIndex_eq_zero_of_le_right hle h0
  rw [AddSubgroup.relIndex_sup_right] at h4
  exact relIndex_ne_zero h₀ hM
    (AddSubgroup.relIndex_eq_zero_of_le_left (fun x hx => mem_localization_of_mem P hx) h4)

end Index

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

theorem homO_fg {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)} (hN : N.FG) (hN' : N'.FG)
    (hs : Submodule.span E (N : Set (Sp E a)) = ⊤) : (homO N N').FG := by
  obtain ⟨T, rfl⟩ := hN
  let φ : HomE E a b →ₗ[𝓞 E] (T → Sp E b) :=
    { toFun := fun x y => x y.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hφ : Function.Injective φ := by
    intro x y hxy
    rw [Submodule.span_span_of_tower] at hs
    exact LinearMap.ext_on hs fun v hv => congrFun hxy ⟨v, hv⟩
  refine Submodule.fg_of_fg_map_injective φ hφ ?_
  refine Submodule.FG.of_le (Submodule.fg_pi (p := fun _ : T => N') fun _ => hN') ?_
  rintro _ ⟨x, hx, rfl⟩ y _
  exact hx _ (Submodule.subset_span y.2)

theorem perO_fg {AA : Submodule (𝓞 E) E} {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)} (hA : AA.FG)
    (hH : (homO N N').FG) : (perO AA N N').FG := by
  let B : E →ₗ[𝓞 E] HomE E a b →ₗ[𝓞 E] HomE E a b :=
    LinearMap.mk₂ (𝓞 E) (fun r x => r • x) (fun _ _ _ => add_smul _ _ _) (fun _ _ _ => smul_assoc _ _ _)
      (fun _ _ _ => smul_add _ _ _) (fun _ _ _ => smul_comm _ _ _)
  refine Submodule.FG.of_le (Submodule.FG.map₂ B hA hH) (Submodule.span_le.2 ?_)
  rintro _ ⟨r, hr, x, hx, rfl⟩
  exact Submodule.apply_mem_map₂ B hr hx

theorem volC_pos : Formalism.L2.Ker.VolCPos := by
  intro E _ _ _ a b AA S N N' hN hN' hs hs' hA hA0
  have la : Submodule.IsLattice E (Formalism.L2.Col.stdLat E a) := Formalism.L2.Col.stdLat_lattice
  have lb : Submodule.IsLattice E (Formalism.L2.Col.stdLat E b) := Formalism.L2.Col.stdLat_lattice
  have f₀ := PeriodComp.full AA _ _ la.fg lb hA0
  have f₁ := PeriodComp.full AA N N' hN ⟨hN', hs'⟩ hA0
  have g₀ := perO_fg hA (homO_fg la.fg lb.fg la.span_eq_top)
  have g₁ := perO_fg hA (homO_fg hN hN' hs)
  refine Finset.prod_pos fun P _ => div_pos ?_ ?_
  · exact Nat.cast_pos.2 (Nat.pos_of_ne_zero (relIndex_localized_ne_zero P f₀ f₁ g₁))
  · exact Nat.cast_pos.2 (Nat.pos_of_ne_zero (relIndex_localized_ne_zero P f₁ f₀ g₀))

end GlobalTheory.ThetaMove.VolumePos
