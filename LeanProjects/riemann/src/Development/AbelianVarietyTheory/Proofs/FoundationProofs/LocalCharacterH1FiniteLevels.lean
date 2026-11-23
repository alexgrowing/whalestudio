import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoLocCard
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoScal
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDualEmb
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoAdicCont
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CoboundaryOfDualCoboundaries

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.LocChar

private def repOverZMod {O Γ M : Type} [CommRing O] [Group Γ] [AddCommGroup M] [Module O M] (N : ℕ)
    [Module (ZMod N) M] (ρ : Representation O Γ M) : Representation (ZMod N) Γ M where
  toFun g := (ρ g).toAddMonoidHom.toZModLinearMap N
  map_one' := LinearMap.ext fun m => by
    show ρ 1 m = m
    rw [map_one, Module.End.one_apply]
  map_mul' g h := LinearMap.ext fun m => by
    show ρ (g * h) m = ρ g (ρ h m)
    rw [map_mul, Module.End.mul_apply]

theorem local_character_h1_bound : LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (A : ValuationSubring Ω), OverL l A → ∀ θ : ↥(Dec (F := ℚ) A) →* c.Oˣ, Continuous (fun g => ((θ g : c.Oˣ) : c.O)) → (∃ g, θ g ≠ 1) → (∃ g, θ g ≠ (UpperTheory.V.Base.chiO ℚ Ω l c.O).comp (Dec (F := ℚ) A).subtype g) → ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n → Finite (H1 (Formalism.GaloisCohomology.scalRep (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) θ)) ∧ Nat.card (H1 (Formalism.GaloisCohomology.scalRep (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) θ)) ≤ C * Nat.card (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) := by
  open Formalism.GaloisCohomology IsLocalRing UpperTheory.V.Base UpperTheory.V.X in
  intro hF hT hE l _ Ω _ _ _ c A hA θ hθc hne₁ hne₂
  obtain ⟨g₁, hne₁⟩ := hne₁
  obtain ⟨g₂, hne₂⟩ := hne₂
  obtain ⟨v, hv, hlv⟩ := hA
  have hd₁ : (θ g₁ : c.O) - 1 ≠ 0 := fun h => hne₁ (Units.ext (sub_eq_zero.1 h))
  have hd₂ : ((chiO ℚ Ω l c.O (g₂ : G ℚ Ω) * θ g₂⁻¹ : c.Oˣ) : c.O) - 1 ≠ 0 := fun h => hne₂ (by
    have h' : chiO ℚ Ω l c.O (g₂ : G ℚ Ω) * θ g₂⁻¹ = 1 := Units.ext (sub_eq_zero.1 h)
    rw [map_inv, mul_inv_eq_one] at h'
    exact h'.symm)
  set d₂ := ((chiO ℚ Ω l c.O (g₂ : G ℚ Ω) * θ g₂⁻¹ : c.Oˣ) : c.O) - 1 with hd₂def
  have hK : Finite (LinearMap.ker (d₂ • (LinearMap.id : QO l c.O →ₗ[c.O] QO l c.O))) := by
    rw [← ((So.cardLen l c.O).2 _).1, (qoFacts l c.O).2.2.2]
    exact fun h => hd₂ (IsDiscreteValuationRing.addVal_eq_top_iff.1 h)
  refine ⟨Nat.card (c.O ⧸ Ideal.span {(θ g₁ : c.O) - 1}) *
    Nat.card (LinearMap.ker (d₂ • (LinearMap.id : QO l c.O →ₗ[c.O] QO l c.O))), fun n hn => ?_⟩
  have hl0 : ((l : ℕ) : c.O) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have ha : ((l : ℕ) : c.O) ^ n ≠ 0 := pow_ne_zero _ hl0
  set a := ((l : ℕ) : c.O) ^ n with hadef
  obtain ⟨hM, ⟨r, hr, hkill⟩, htor⟩ := So.levFacts l c.O a ha (Lev a) ⟨LinearEquiv.refl c.O _⟩
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨_⟩ : Nonempty (Module (ZMod (l ^ r)) (Lev a)) := ⟨AddCommGroup.zmodModule hkill⟩
  set ρ := Formalism.GaloisCohomology.scalRep (Lev a) θ with hρ
  let ρ' : Representation (ZMod (l ^ r)) (Dec (F := ℚ) A) (Lev a) := repOverZMod (l ^ r) ρ
  have hact : ∀ (g : Dec (F := ℚ) A) (m : Lev a), ρ' g m = (θ g : c.O) • m := fun g m => rfl
  have hc : ContAction ρ' := by
    refine continuous_prod_of_discrete_right.2 fun m => ?_
    obtain ⟨x, rfl⟩ := Lev.mk_surjective a m
    have h1 : Continuous fun g : Dec (F := ℚ) A => Lev.mk a ((θ g : c.O) * x) :=
      ((So.adicCont l c).1 a ha).comp (hθc.mul continuous_const)
    refine h1.congr fun g => ?_
    show Lev.mk a ((θ g : c.O) * x) = (θ g : c.O) • Lev.mk a x
    rw [← smul_eq_mul, map_smul]
  obtain ⟨f1, -, c2⟩ := So.locCard hF hT ℚ Ω l r hr v A hv (Lev a) ρ' hc
    (twDual ((cycMod ℚ Ω l r).comp (Dec (F := ℚ) A).subtype) ρ') fun g φ m => twDual_apply _ _ _ _ _
  have he := (hE ℚ Ω l r (Lev a) A ρ' v hr hv hc).1 hlv
  rw [GlobalTheory.OrdLoc.Dcmp.locDeg_rat hlv, pow_one] at he
  obtain ⟨-, ⟨e1⟩, -⟩ := So.scal c.O (ZMod (l ^ r)) _ (Lev a) ρ ρ' fun _ _ => rfl
  refine ⟨Finite.of_equiv _ e1.symm.toEquiv, ?_⟩
  rw [Nat.card_congr e1.toEquiv, he, c2]
  refine Nat.mul_le_mul (Nat.mul_le_mul (le_trans ?_ (htor _ hd₁)) ?_) le_rfl
  · refine Nat.card_le_card_of_injective (fun x => ⟨x.1, ?_⟩)
      fun x y hxy => Subtype.ext (Subtype.mk.inj hxy)
    have := (mem_riemannRochSpace_iff_regularAt_everywhere _ _).1 x.2 g₁
    rw [hact] at this
    exact (sub_smul _ _ _).trans (by rw [one_smul, this, sub_self])
  · obtain ⟨ι, hι, -, hιs⟩ := So.dualEmb l c.O a ha r (Lev a) ⟨LinearEquiv.refl c.O _⟩
    refine Nat.card_le_card_of_injective (fun x => ⟨ι x.1, ?_⟩)
      fun x y hxy => Subtype.ext (hι (congrArg Subtype.val hxy))
    have hx := (Representation.mem_invariants _ _).1 x.2 g₂
    have := hιs (cycZ ℚ Ω l (g₂ : G ℚ Ω) : ℤ_[l]ˣ) ((θ g₂⁻¹ : c.Oˣ) : c.O) x.1 x.1 fun m => by
      conv_lhs => rw [← hx, twDual_apply, hact]
      rfl
    rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, hd₂def, sub_smul, one_smul, sub_eq_zero]
    exact this.symm

end GlobalTheory.LocChar
