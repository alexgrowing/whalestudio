import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantInducedIsAdmissible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixedPiTensor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProductTwoRepsEquivTwoBlockInduction
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.IrreducibleAdmissibleReps.Assembly

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace PositivityTheory.PfBern.Props1

section Equiv

variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W]

theorem isAdmissible_of_equiv {σ : Representation ℂ G V} {τ : Representation ℂ G W} (E : σ.Equiv τ)
    (h : IsAdmissible τ) : IsAdmissible σ := by
  let L : V →ₗ[ℂ] W := E.toIntertwiningMap.toLinearMap
  have hL : ∀ y, L y = E.toLinearEquiv y := fun _ => rfl
  have hLi : Function.Injective L := fun a b hab => E.toLinearEquiv.injective (by rw [← hL, ← hL, hab])
  have hcomm : ∀ g y, L (σ g y) = τ g (L y) := fun g y => LinearMap.congr_fun (E.isIntertwining' g) y
  refine ⟨fun v => ?_, fun K hKo hKc => ?_⟩
  · have : {g : G | σ g v = v} = {g : G | τ g (L v) = L v} := by
      ext g
      simp only [Set.mem_ofPred_eq, ← hcomm]
      exact hLi.eq_iff.symm
    rw [this]
    exact h.1 (L v)
  · have := h.2 K hKo hKc
    let M : GlobalTheory.PRep.fixed σ K →ₗ[ℂ] GlobalTheory.PRep.fixed τ K :=
      { toFun := fun v => ⟨L v.1, GlobalTheory.ContraRefl.mem_fix.2 fun g hg => by
          rw [← hcomm, GlobalTheory.ContraRefl.mem_fix.1 v.2 g hg]⟩
        map_add' := fun _ _ => Subtype.ext (map_add L _ _)
        map_smul' := fun _ _ => Subtype.ext (map_smul L _ _) }
    exact Module.Finite.of_injective M fun a b hab =>
      Subtype.ext (hLi (congrArg Subtype.val hab))

end Equiv

section ParInd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
  {W : Type} [AddCommGroup W] [Module ℂ W]

theorem isAdmissible_parInd_of (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W)
    (hρ : IsAdmissible ρ) : IsAdmissible (parInd e ρ) := by
  refine ⟨isSmooth_parInd e ρ, fun K hKo hKc => ?_⟩
  obtain ⟨R, hR⟩ := ParIndAdm.exists_finset_KO_cover K hKo
  let KM : Subgroup (Levi k m) := Subgroup.pi Set.univ fun a => KO k (m a)
  have hKMo : IsOpen (KM : Set (Levi k m)) := by
    rw [Subgroup.coe_pi]
    exact isOpen_set_pi Set.finite_univ fun a _ => GlobalTheory.SplitFlip.isOpen_KO
  have hKMc : IsCompact (KM : Set (Levi k m)) := by
    rw [Subgroup.coe_pi]
    exact isCompact_univ_pi fun a => GlobalTheory.SplitFlip.isCompact_KO
  let φ : GL n k → Levi k m →* GL n k := fun r => (MulAut.conj r⁻¹).toMonoidHom.comp (leviEmb k e)
  have hφ : ∀ r, Continuous (φ r) := fun r => by
    show Continuous fun g => r⁻¹ * leviEmb k e g * r⁻¹⁻¹
    have := continuous_leviEmb (R := k) e
    fun_prop
  let H : GL n k → Subgroup (Levi k m) := fun r => K.comap (φ r) ⊓ KM ⊓ (deltaHalf k m).ker
  have hHo : ∀ r, IsOpen (H r : Set (Levi k m)) := fun r => by
    refine IsOpen.inter (IsOpen.inter (hKo.preimage (hφ r)) hKMo) ?_
    exact isSmoothChar_deltaHalf k (m := m)
  have hHc : ∀ r, IsCompact (H r : Set (Levi k m)) := fun r =>
    hKMc.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ (hHo r)) fun x hx => hx.1.2
  have hfin : ∀ r, FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρ (H r)) := fun r => hρ.2 _ (hHo r) (hHc r)

  have hval : ∀ (f : GlobalTheory.PRep.fixed (parInd e ρ) K) (r : GL n k),
      f.1.1.1 r ∈ GlobalTheory.PRep.fixed ρ (H r) := by
    intro f r
    refine GlobalTheory.ContraRefl.mem_fix.2 fun h hh => ?_
    have hK : r⁻¹ * leviEmb k e h * r ∈ K := by
      have := hh.1.1
      simpa [φ, MulAut.conj_apply] using this
    have hδ : deltaHalf k m h = 1 := hh.2
    have hfix := GlobalTheory.ContraRefl.mem_fix.1 f.2 _ hK
    have h1 : f.1.1.1 (leviEmb k e h * r) = f.1.1.1 r := by
      have := congrArg (fun φ : IndSp e ρ => φ.1.1 r) hfix
      simpa using this
    have h2 := parInd_law e ρ f.1 ⟨leviEmb k e h, leviEmb_mem_parab k e h⟩ r
    have h4 : leviProj k e ⟨leviEmb k e h, leviEmb_mem_parab k e h⟩ = h := leviProj_leviEmb k e h
    rw [h4, hδ, Units.val_one, one_smul] at h2
    rw [← h2]
    exact h1
  let L : GlobalTheory.PRep.fixed (parInd e ρ) K →ₗ[ℂ] ((r : R) → GlobalTheory.PRep.fixed ρ (H r.1)) :=
    { toFun := fun f r => ⟨f.1.1.1 r.1, hval f r.1⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective L fun f g hfg => ?_
  rw [← sub_eq_zero]
  have h := ParIndAdm.eq_zero_of_fixed e ρ K R hR (f - g).1 (f - g).2 fun r hr => by
    have := congrArg Subtype.val (congrFun hfg ⟨r, hr⟩)
    show f.1.1.1 r - g.1.1.1 r = 0
    rw [show f.1.1.1 r = g.1.1.1 r from this, sub_self]
  exact Subtype.ext h

end ParInd

theorem admissibleProd_holds : PositivityTheory.PfBern.Assembly.AdmissibleProd := by
  intro k _ _ _ _ r t V W _ _ _ _ π₁ π₂ h₁ h₂
  obtain ⟨E⟩ := GlobalTheory.SmGL.Exponents.prod₂_equiv_multiProd k r t V W π₁ π₂
  refine isAdmissible_of_equiv E ?_
  refine isAdmissible_parInd_of _ _ ?_
  refine GlobalTheory.ContraProd.isAdmissible_piTensor _ _ fun x => ?_
  cases x
  · exact h₁
  · exact h₂

end PositivityTheory.PfBern.Props1
