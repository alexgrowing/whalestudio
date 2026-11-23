import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.IsFirstChernThickening
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.MuNat

theorem muB_nat : ∀ {K B₁ B₂ : Type} [CommRing K] [CommRing B₁] [CommRing B₂] [Algebra K B₁] [Algebra K B₂] {I₁ : Ideal B₁} {I₂ : Ideal B₂}
    {γ₁ : DividedPowers I₁} {γ₂ : DividedPowers I₂} {X₁ X₂ : Scheme.{0}} {q₁ : X₁ ⟶ Spec (CommRingCat.of K)}
    {q₂ : X₂ ⟶ Spec (CommRingCat.of K)} {σ : B₁ →+* B₂} (nm : NMor γ₁ q₁ (κA K I₁) γ₂ q₂ (κA K I₂) σ) (hu : nm.u ≫ q₁ = q₂) (l s : ℕ),
    (∀ k, σ (algebraMap K B₁ k) = algebraMap K B₂ k) → ∀ (j : ℕ) (x : HdR q₁ j),
    nmHO nm l s j (muB γ₁ q₁ l s {⊤} j x) = muB γ₂ q₂ l s {⊤} j (pullR j nm.u hu x) := by
  intro K B₁ B₂ _ _ _ _ _ I₁ I₂ γ₁ γ₂ X₁ X₂ q₁ q₂ σ nm hu l s hσ j x
  letI t1 : RingHomCompTriple (algebraMap K B₁) σ (algebraMap K B₂) := ⟨RingHom.ext hσ⟩
  let r₁ := CH.Mor.restrict (O (smFun X₁ q₁)) (TO q₁ l s {⊤}).ι
  let r₂ := CH.Mor.restrict (O (smFun X₂ q₂)) (TO q₂ l s {⊤}).ι
  let a₁ := (smO γ₁ q₁ l s {⊤}).o
  let a₂ := (smO γ₂ q₂ l s {⊤}).o
  let n := (nmS nm l s).o
  let MS : CH.Mor (O (smFun X₁ q₁)) (O (smFun X₂ q₂)) (RingHom.id K) := CH.Mor.ofBlk
    { G := (smMor nm.u hu).functor
      τ := fun _ => { toFun := fun z => z, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
      nat := fun _ _ => rfl }
  let L1 : CH.Mor _ _ (algebraMap K B₁) := r₁.comp a₁
  let ML : CH.Mor _ _ (algebraMap K B₂) := L1.comp n
  let R1 : CH.Mor _ _ (RingHom.id K) := MS.comp r₂
  let MR : CH.Mor _ _ (algebraMap K B₂) := R1.comp a₂
  have hL1 := (CrystallineSemistableComparison.P.pull_comp (σ'' := algebraMap K B₁) r₁ a₁ j x).1
  have hL2 := (CrystallineSemistableComparison.P.pull_comp (σ'' := algebraMap K B₂) L1 n j x).1
  have hR1 := (CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id K) MS r₂ j x).1
  have hR2 := (CrystallineSemistableComparison.P.pull_comp (σ'' := algebraMap K B₂) R1 a₂ j x).1
  let η : ML.G ⟶ MR.G :=
    { app := fun T => mkH (γ := dividedPowersBot K) (p := 0) (q := q₁) (κ := Ideal.Quotient.mk ⊥)
        (T := ML.G.obj T) (T' := MR.G.obj T) (RingHom.id T.obj.B)
        (fun r => congrArg T.obj.i (hσ r)) ⟨le_of_eq (Ideal.map_id _), fun x hx => rfl⟩ (fun x hx => hx) (by
          refine Subtype.ext (Prod.ext ?_ ?_)
          · refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
            have hw1 := (ML.G.obj T).w r
            have hw2 := (MR.G.obj T).w r
            have h3 : Ideal.Quotient.mk T.obj.J ((ML.G.obj T).i r) = Ideal.Quotient.mk T.obj.J ((MR.G.obj T).i r) :=
              congrArg (Ideal.Quotient.mk T.obj.J) (congrArg T.obj.i (hσ r))
            exact (congrArg (Ideal.quotientMap T.obj.J (RingHom.id T.obj.B) (fun x hx => hx)) hw1).trans (h3.trans hw2.symm)
          · have e : CommRingCat.ofHom (Ideal.quotientMap T.obj.J (RingHom.id T.obj.B) (fun x hx => hx)) =
                𝟙 (CommRingCat.of (T.obj.B ⧸ T.obj.J)) :=
              CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl))
            have e2 : Spec.map (CommRingCat.ofHom (Ideal.quotientMap T.obj.J (RingHom.id T.obj.B) (fun x hx => hx))) =
                𝟙 (Spec (CommRingCat.of (T.obj.B ⧸ T.obj.J))) := (congrArg Spec.map e).trans (Spec.map_id _)
            change Spec.map (CommRingCat.ofHom (Ideal.quotientMap T.obj.J (RingHom.id T.obj.B) (fun x hx => hx))) ≫
                ((T.obj.y.1.2 ≫ nm.u) ≫ 𝟙 X₁) = (T.obj.y.1.2 ≫ 𝟙 X₂) ≫ nm.u
            rw [e2, Category.id_comp, Category.comp_id, Category.comp_id])
      naturality := fun T T' f => hom_ext (γ := dividedPowersBot K) (p := 0) (q := q₁) (κ := Ideal.Quotient.mk ⊥)
        (RingHom.ext fun _ => rfl) }
  have h4 := CrystallineSemistableComparison.P.prism ML MR η (fun T y => rfl) j x
  exact (congrArg (n.pull j) hL1.symm).trans (hL2.symm.trans (h4.trans (hR2.trans (congrArg (a₂.pull j) hR1))))

end GlobalTheory.CompanionTheory.MuNat
