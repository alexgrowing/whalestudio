import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StDualIndexFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W]

theorem DualIndexFinite.proof (h : HermitianForm F E W) : DualIndexFinite.Statement h := by
  classical
  intro La hLa _
  obtain ⟨s, hs⟩ := hLa.fg
  have hsLa : ∀ l ∈ s, l ∈ La := fun l hl => hs ▸ AddSubgroup.subset_closure hl

  have hspan : Submodule.span E (s : Set W) = ⊤ := by
    rw [← hLa.span_eq_top]
    refine le_antisymm (Submodule.span_mono fun l hl => hsLa l hl) (Submodule.span_le.2 ?_)
    rw [← hs]
    intro x hx
    have : AddSubgroup.closure (s : Set W) ≤ (Submodule.span E (s : Set W)).toAddSubgroup :=
      (AddSubgroup.closure_le _).2 Submodule.subset_span
    exact this hx
  set K := dualLattice h La

  let ψ : K →+ (s → 𝓞 E) :=
    { toFun := fun y l => ⟨h.toSesq y l, y.2 l (hsLa l l.2)⟩
      map_zero' := by
        funext l; apply RingOfIntegers.ext
        change h.toSesq 0 l = 0
        rw [map_zero, LinearMap.zero_apply]
      map_add' := by
        intro a b; funext l; apply RingOfIntegers.ext
        change h.toSesq ((a : W) + b) l = h.toSesq a l + h.toSesq b l
        rw [map_add, LinearMap.add_apply] }
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    have h0 : h.toSesq (y : W) = 0 := by
      refine LinearMap.ext_on hspan fun l hl => ?_
      have := congrArg (fun f : s → 𝓞 E => ((f ⟨l, hl⟩ : 𝓞 E) : E)) hy
      exact this
    apply Subtype.ext
    apply h.nonsingular.1
    rw [h0]
    exact (map_zero h.toSesq).symm
  have : IsNoetherian ℤ K := isNoetherian_of_injective ψ.toIntLinearMap hψ
  have : AddGroup.FG K := Module.Finite.iff_addGroup_fg.1 inferInstance
  have : Module.Finite ℤ (K ⧸ La.addSubgroupOf K) := Module.Finite.iff_addGroup_fg.2 inferInstance

  have htors : Module.IsTorsion ℤ (K ⧸ La.addSubgroupOf K) := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
    have hy : (y : W) ∈ Submodule.span E (s : Set W) := hspan ▸ Submodule.mem_top
    obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.1 hy
    obtain ⟨δ, hδ, hint⟩ := exists_integral_multiples ℤ ℚ (s.image c)
    refine ⟨⟨δ, mem_nonZeroDivisors_of_ne_zero hδ⟩, ?_⟩
    change δ • (QuotientAddGroup.mk y : K ⧸ La.addSubgroupOf K) = 0
    rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf,
      AddSubgroup.coe_zsmul, ← hc, Finset.smul_sum]
    refine AddSubgroup.sum_mem _ fun l hl => ?_
    have hi := hint (c l) (Finset.mem_image_of_mem c hl)
    let a : 𝓞 E := ⟨δ • c l, (mem_integralClosure_iff ℤ E).mpr hi⟩
    rw [show δ • c l • l = (a : E) • l from (smul_assoc δ (c l) l).symm]
    exact hLa.smul_mem a l (hsLa l hl)
  have : Finite (K ⧸ La.addSubgroupOf K) := Module.finite_of_fg_torsion _ htors
  exact AddSubgroup.index_ne_zero_of_finite

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
