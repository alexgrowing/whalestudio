import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace CrystallineSemistableComparison

open GlobalTheory.EtC

namespace KummerTwistLemmas

theorem twLift {Q : ℕ} [NeZero Q] (i : ℤ) (G : Shv (ZMod Q)) (e : ∀ (U : Scheme.{0}), Prim Q Γ(U, ⊤) → Sec G U)
    (he : ∀ {V U : Scheme.{0}} (g : V ⟶ U) ζ, Sec.res g (e U ζ) = e V (ζ.map g.appTop.hom))
    (hr : ∀ (U : Scheme.{0}) (ζ ξ : Prim Q Γ(U, ⊤)) (a : (ZMod Q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod Q).val →
      e U ξ = (ULift.up ((a ^ i : (ZMod Q)ˣ) : ZMod Q) : ULift.{1} (ZMod Q)) • e U ζ) :
    ∃ f : tw Q i ⟶ G, ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)), Sec.map f (twGen i ζ) = e U ζ := by
  let L : ∀ (U : Scheme.{0}), (Prim Q Γ(U, ⊤) →₀ ULift.{1} (ZMod Q)) →ₗ[ULift.{1} (ZMod Q)] Sec G U :=
    fun U => Finsupp.linearCombination (ULift.{1} (ZMod Q)) (e U)
  have hL : ∀ (U : Scheme.{0}), twRel Q i Γ(U, ⊤) ≤ LinearMap.ker (L U) := by
    intro U
    refine Submodule.span_le.2 ?_
    rintro x ⟨ζ, ξ, a, h, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, L, Finsupp.linearCombination_single, one_smul]
    rw [hr U ζ ξ a h, sub_self]
  let η : (Scheme.Γ ⋙ twF Q i) ⟶ G.obj :=
    { app := fun U => ModuleCat.ofHom ((twRel Q i Γ(U.unop, ⊤)).liftQ (L U.unop) (hL U.unop))
      naturality := fun U V g => by
        refine ModuleCat.hom_ext (Submodule.linearMap_qext _ (Finsupp.lhom_ext fun ζ c => ?_))
        change (twRel Q i Γ(V.unop, ⊤)).liftQ (L V.unop) (hL V.unop)
            (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map (Scheme.Γ.map g).hom) (Finsupp.single ζ c))) =
          (G.obj.map g).hom ((twRel Q i Γ(U.unop, ⊤)).liftQ (L U.unop) (hL U.unop) (Submodule.Quotient.mk (Finsupp.single ζ c)))
        rw [Submodule.liftQ_apply, Submodule.liftQ_apply, Finsupp.mapDomain_single]
        simp only [L, Finsupp.linearCombination_single, map_smul]
        congr 1
        exact (he g.unop ζ).symm }
  refine ⟨((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} (ZMod Q)))).homEquiv _ _).symm η,
    fun U ζ => ?_⟩
  have h := ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} (ZMod Q)))).homEquiv _ G).apply_symm_apply η
  have h2 := ConcreteCategory.congr_hom (congrArg (fun φ => NatTrans.app φ (op U)) h)
    (Submodule.Quotient.mk (Finsupp.single ζ 1) : (Prim Q Γ(U, ⊤) →₀ ULift.{1} (ZMod Q)) ⧸ twRel Q i Γ(U, ⊤))
  refine h2.trans ?_
  change (twRel Q i Γ(U, ⊤)).liftQ (L U) (hL U) (Submodule.Quotient.mk (Finsupp.single ζ 1)) = e U ζ
  rw [Submodule.liftQ_apply]
  simp [L]

end KummerTwistLemmas

end CrystallineSemistableComparison
