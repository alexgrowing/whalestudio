import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.RingInverseAlgebraMap
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.LGSmall
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.TrDual
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.DApprox
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.T2SpaceOfNonarchimedeanLocalField
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TrDualLoc
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.PsiTower
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.AddCharKernel
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.GoodRDeltaC

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc ValuativeRel

namespace GlobalTheory.LocDiffGen

variable {D : D7}

theorem iF_int (p : PlF D) (a : 𝓞 D.host.F) :
    (D.s.atP p).ιF (a : D.host.F) ∈ 𝒪[(D.s.atP p).Fp] := by
  have h1 : (D.s.atP p).ιF (a : D.host.F) ≤ᵥ (D.s.atP p).ιF 1 := by
    rw [(D.s.atP p).val, map_one]
    exact p.valuation_le_one (K := D.host.F) a
  rw [map_one, Valuation.Compatible.vle_iff_le (v := valuation (D.s.atP p).Fp), map_one] at h1
  exact (Valuation.mem_integer_iff _ _).2 h1

theorem dual_sub (Z : LocDat D) (p : PlF D) (z : (D.s.atP p).Fp)
    (hz : haveI := (D.s.atP p).ellPrime; ∀ c ∈ 𝒪[(D.s.atP p).Fp],
      ‖Algebra.trace ℚ_[Loc.resChar p] (D.s.atP p).Fp (c * z)‖ ≤ 1) :
    Z.δ p * z ∈ 𝒪[(D.s.atP p).Fp] := by
  haveI : Fact (Loc.resChar p).Prime := (D.s.atP p).ellPrime
  obtain ⟨-, hδ, -, hO, hpsi, -⟩ := Z.agree p
  have hx : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p * z) ∈ (Z.M p).L.O := by
    rw [← (Z.M p).L.additive_character_dual_ring]
    intro y hy
    rw [hO] at hy
    rw [hpsi]
    have e : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p * z) * y *
        algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p)⁻¹ = y * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep z := by
      have e2 : Z.δ p * z * (Z.δ p)⁻¹ = z := by field_simp
      rw [← e2, map_mul (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep) (Z.δ p * z) (Z.δ p)⁻¹, e2]
      ring
    rw [e]
    refine (PI.LocDualGen.Top.psi_tower PI.LocDualGen.Psi.addCharKernel (D.s.atP p) _).2 ?_
    rw [map_neg, PI.LocDualGen.Top.tr_smul, map_neg, norm_neg]
    exact hz _ (PI.UnitaryGroupMassFormula.CntFormula.DeltaC.trace_mem (D.s.atP p) hy)
  rw [hO, (D.s.atP p).O_def] at hx
  have hi : IsIntegral 𝒪[(D.s.atP p).Fp] (Z.δ p * z) :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom 𝒪[(D.s.atP p).Fp] (D.s.atP p).Fp (D.s.atP p).Ep)
      (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep).injective).1 hx
  exact PI.UnitaryGroupMassFormula.CntFormula.DeltaC.mem_of_isIntegral_fp (D.s.atP p) hi

theorem diff_sub (Z : LocDat D) (p : PlF D) (x : 𝓞 D.host.F) (hx : x ∈ differentIdeal ℤ (𝓞 D.host.F)) :
    (Z.δ p)⁻¹ * (D.s.atP p).ιF (x : D.host.F) ∈ 𝒪[(D.s.atP p).Fp] := by
  obtain ⟨t, ht, hne, -, hinv⟩ := PI.CntNotIntW.locDiff_of PI.CntNotIntW.trace_dual_lattice
    (PI.CntNotIntW.dualApprox_of PI.CntNotIntW.small_powers_bound PI.CntNotIntW.tensorLiftSurjective)
    PI.CntNotIntW.small_powers_bound D Z.δ Z.M Z.agree p
  have hB := PI.CntNotIntW.dual_mul_different_integral D t ht x hx
  let w : 𝓞 D.host.F := ⟨_, (mem_integralClosure_iff ℤ D.host.F).2 hB⟩
  have hw : (D.s.atP p).ιF (w : D.host.F) ∈ 𝒪[(D.s.atP p).Fp] := iF_int p w
  have hw' : (D.s.atP p).ιF (w : D.host.F) = (D.s.atP p).ιF t * (D.s.atP p).ιF (x : D.host.F) := by
    rw [← map_mul]; rfl
  have ht0 : (D.s.atP p).ιF t ≠ 0 := right_ne_zero_of_mul hne
  have hδ0 : Z.δ p ≠ 0 := left_ne_zero_of_mul hne
  have e : (Z.δ p)⁻¹ * (D.s.atP p).ιF (x : D.host.F) =
      (D.s.atP p).ιF (w : D.host.F) * (Z.δ p * (D.s.atP p).ιF t)⁻¹ := by
    rw [hw']; field_simp
  rw [e]
  exact mul_mem hw hinv

theorem dual_glob (Z : LocDat D) (p : PlF D) (t : D.host.F)
    (ht : ∀ a : 𝓞 D.host.F, ∃ n : ℤ, Algebra.trace ℚ D.host.F (t * a) = n) :
    Z.δ p * (D.s.atP p).ιF t ∈ 𝒪[(D.s.atP p).Fp] := by
  haveI : Fact (Loc.resChar p).Prime := (D.s.atP p).ellPrime
  haveI := (D.s.atP p).lf
  exact dual_sub Z p _ (fun c hc => trace_dual_local D.host.F p (D.s.atP p).Fp (D.s.atP p).qlCont
    (D.s.atP p).qlFin (D.s.atP p).ιF (D.s.atP p).dense (D.s.atP p).val t ht c hc)

theorem span_different_eq : ∀ (D : D7) (Z : LocDat D) (p : PlF D), Submodule.span (Z.M p).L.O ((fun x : 𝓞 D.host.F => (D.s.atP p).ιE (algebraMap D.host.F D.host.E x)) '' (differentIdeal ℤ (𝓞 D.host.F) : Set (𝓞 D.host.F))) = Submodule.span (Z.M p).L.O {algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p)} := by
  intro D Z p
  obtain ⟨-, hδ, -, hO, -, -⟩ := Z.agree p
  have hmem : ∀ c ∈ 𝒪[(D.s.atP p).Fp], algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c ∈ (Z.M p).L.O := by
    intro c hc; rw [hO]; exact PI.CntNotIntW.algMap_mem_O D p c hc
  have hf : ∀ x : 𝓞 D.host.F, (D.s.atP p).ιE (algebraMap D.host.F D.host.E x) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (x : D.host.F)) :=
    fun x => (D.s.atP p).compat _
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_span_singleton]
    refine ⟨⟨_, hmem _ (diff_sub Z p x hx)⟩, ?_⟩
    show algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((Z.δ p)⁻¹ * (D.s.atP p).ιF (x : D.host.F)) *
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p) = _
    rw [← map_mul]
    show _ = (D.s.atP p).ιE (algebraMap D.host.F D.host.E (x : D.host.F))
    rw [hf]
    congr 1
    field_simp
  · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    set N := Submodule.span (Z.M p).L.O ((fun x : 𝓞 D.host.F => (D.s.atP p).ιE (algebraMap D.host.F D.host.E x)) '' (differentIdeal ℤ (𝓞 D.host.F) : Set (𝓞 D.host.F))) with hN
    have h10 : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F) ≠ 0 := one_ne_zero
    have hIJ : ((differentIdeal ℤ (𝓞 D.host.F) : Ideal (𝓞 D.host.F)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F) *
        FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F) = 1 := by
      rw [coeIdeal_differentIdeal (A := ℤ) (K := ℚ) (L := D.host.F) (B := 𝓞 D.host.F)]
      exact inv_mul_cancel₀ (FractionalIdeal.dual_ne_zero ℤ ℚ h10)
    have key : ∀ y : D.host.F, y ∈ (((differentIdeal ℤ (𝓞 D.host.F) : Ideal (𝓞 D.host.F)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F) *
        FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F)) →
        algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p * (D.s.atP p).ιF y) ∈ N := by
      intro y hy
      rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_mul] at hy
      refine Submodule.mul_induction_on hy ?_ ?_
      · intro m hm n hn
        obtain ⟨x, hx, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hm
        have hn' := (FractionalIdeal.mem_dual h10).1 hn
        have ht : ∀ a : 𝓞 D.host.F, ∃ k : ℤ, Algebra.trace ℚ D.host.F (n * a) = k := by
          intro a
          obtain ⟨k, hk⟩ := hn' _ ((FractionalIdeal.mem_one_iff _).2 ⟨a, rfl⟩)
          exact ⟨k, by rw [← Algebra.traceForm_apply, ← hk]; simp⟩
        have hc := dual_glob Z p n ht
        have e : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p * (D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F x * n)) =
            (⟨_, hmem _ hc⟩ : (Z.M p).L.O) • (D.s.atP p).ιE (algebraMap D.host.F D.host.E (x : D.host.F)) := by
          rw [hf, Subring.smul_def]
          show _ = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p * (D.s.atP p).ιF n) * _
          rw [← map_mul, map_mul (D.s.atP p).ιF]
          congr 1
          show _ = _ * (D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F x)
          ring
        rw [e]
        exact N.smul_mem _ (Submodule.subset_span ⟨x, hx, rfl⟩)
      · intro a b ha hb
        rw [map_add, mul_add, map_add]
        exact N.add_mem ha hb
    have h1 := key 1 (by rw [hIJ]; exact (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩)
    have e1 : Z.δ p * (D.s.atP p).ιF 1 = Z.δ p := by rw [map_one, mul_one]
    rw [e1] at h1
    exact h1

end GlobalTheory.LocDiffGen
