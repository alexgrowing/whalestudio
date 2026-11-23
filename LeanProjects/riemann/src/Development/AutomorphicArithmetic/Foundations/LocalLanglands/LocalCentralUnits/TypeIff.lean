import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.DiscreteGroups.GlobalIrreducibility.DzIneEq
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.FinrankK

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
open scoped Pointwise

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC

private theorem restrict_mem_ine {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω]
    [Algebra E E'] [Algebra E Ω] [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω]
    (A : ValuationSubring Ω) (t : G E' Ω) (ht : t ∈ Ine (F := E') A) :
    AlgEquiv.restrictScalars E t ∈ Ine (F := E) A := by
  refine ⟨?_, fun x hx => ht.2 x hx⟩
  show AlgEquiv.restrictScalars E t • A = A
  have hd : t • A = A := ht.1
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  conv_rhs => rw [← hd]
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  exact Iff.rfl

end UpperTheory.Zero.LLC

theorem UpperTheory.Zero.LLC.typeIff :
    UpperTheory.Zero.LLC.TypeIff := by
  intro E Ω _ _ _ _ _ A w h rc
  constructor
  · intro H x g _ i hi n hn D R hR θ hθ τ hτ hNm σ hσ hinf
    subst hσ
    have main := H D.E' g D.w' D.h' i hi n hn D.unr D.card D.a' D.ha' D.K D.red D.surj D.ker θ hθ τ hτ hNm σ hinf
    refine ⟨main.1, fun t => ?_⟩
    obtain ⟨t', ht', e⟩ := DiscreteGroups.sglob.DzType.ine_lift g A w h D.w' D.h' n hn D.unr D.card (t : G E Ω) t.2
    obtain ⟨x, hx⟩ := DiscreteGroups.sglob.DzType.exists_int_approx_compl D.w' _
      (DiscreteGroups.sglob.DzType.val_artin_ine D.ha' (⟨t', ht'⟩ : Ine (F := D.E') A)).le
    have hne := DiscreteGroups.sglob.DzType.red_ne_zero_of_approx D.ha' D.ker hx
    have hz : R t = Units.mk0 (D.red x) hne := hR t ⟨t', ht'⟩ x _ e.symm rfl hx
    have key := main.2 ⟨t', ht'⟩ x (Units.mk0 _ hne) rfl hx
    rw [hz, ← e]
    exact key
  · intro H E' _ _ _ _ _ _ g _ w' h' i hi n hn unr card a' ha' K _ _ red surj ker θ hθ τ hτ hNm σ hinf
    let D : Ext h g n :=
      { E' := E', w' := w', h' := h', unr := unr, card := card, a' := a', ha' := ha', K := K, red := red,
        surj := surj, ker := ker }
    obtain ⟨R, hR⟩ := (UpperTheory.Zero.LLC.resEx E Ω A w h g i hi n hn D).1
    have main := H (cls σ) g i hi n hn D R hR θ hθ τ hτ hNm σ rfl hinf
    refine ⟨main.1, fun t x z hz hx => ?_⟩
    have hm := restrict_mem_ine (E := E) A (t : G E' Ω) t.2
    have e : R ⟨_, hm⟩ = z := hR ⟨_, hm⟩ t x z rfl hz hx
    have key := main.2 ⟨_, hm⟩
    rw [e] at key
    exact key

end
