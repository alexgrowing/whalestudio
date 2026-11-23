import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoNormalisedRespectsLaws
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsoEqOfMapsAlongSection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HalfBC GlobalTheory.PrimCocycle

namespace GlobalTheory.TautUniq

theorem lamVal_eq_of_rig : ∀ {S S' : Scheme.{0}} {B : Over S} {B' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] {M : LB B.left} {M' : LB B'.left} {β₂ : (G2 B').left ⟶ (G2 B).left}, M.IsLB → M'.IsLB → IsAbelianScheme B' → ∀ (w₁ w₂ : LB.Iso (abelian₂ B' M') ((abelian₂ B M).pull β₂)), w₁.IsGen → w₂.IsGen → (∀ (T : Over S') (z : T.left) J J', Good M z J → Good M' z J' → lamVal w₁ (lift (1 : T ⟶ B') (1 : T ⟶ B')).left z J J' = 1) → (∀ (T : Over S') (z : T.left) J J', Good M z J → Good M' z J' → lamVal w₂ (lift (1 : T ⟶ B') (1 : T ⟶ B')).left z J J' = 1) → ∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 B').left) (z : Z) J J', Good M z J → Good M' z J' → lamVal w₁ p z J J' = lamVal w₂ p z J J' := by
  intro S S' B B' _ _ _ _ M M' β₂ hM hM' hB' w₁ w₂ h₁ h₂ n₁ n₂ Z p z J J' hJ hJ'
  have hG := GlobalTheory.globalFns_holds
  have he2 : (lift (1 : 𝟙_ (Over S') ⟶ B') 1).left ≫ (snd B' B').left ≫ B'.hom = 𝟙 _ := by
    rw [Over.w]; exact Over.w (lift (1 : 𝟙_ (Over S') ⟶ B') 1)
  have hp := surj_comp (surj_snd hG hB' _) (hG _ _ hB').2
  have mem : ∀ {Y : Scheme.{0}} (q : Y ⟶ (G2 B').left) (y : Y) {J₀ : (Y ⟶ B.left) → M.ι}
      {J₀' : (Y ⟶ B'.left) → M'.ι}, Good M y J₀ → Good M' y J₀' →
      q y ∈ (LB.div ((abelian₂ B M).pull β₂) (abelian₂ B' M')).U
        (fun _ I => J₀ (q ≫ β₂ ≫ (psum B (x2 B) I.down).left), fun I => J₀' (q ≫ (psum B' (x2 B') I.down).left)) :=
    fun q y J₀ J₀' h h' => TopologicalSpace.Opens.mem_inf.2
      ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun I => h (q ≫ β₂ ≫ (psum B (x2 B) I.down).left),
       h'.mem (fun I : ULift (Finset (Fin 2)) => (psum B' (x2 B') I.down).left) q⟩
  have hw : w₁ = w₂ := by
    refine gen_eq_of_eq_along_section (fun y => ?_) _ _ he2 hp h₁ h₂ (fun s a ha => ?_)
    · obtain ⟨J₁, hJ₁⟩ := GlobalTheory.UU.exists_good_pt hM y
      obtain ⟨J₁', hJ₁'⟩ := GlobalTheory.UU.exists_good_pt hM' y
      exact ⟨_, mem (𝟙 _) y hJ₁ hJ₁'⟩
    · obtain ⟨J₁, hJ₁⟩ := GlobalTheory.UU.exists_good_pt hM s
      obtain ⟨J₁', hJ₁'⟩ := GlobalTheory.UU.exists_good_pt hM' s
      have hb := mem (lift (1 : 𝟙_ (Over S') ⟶ B') 1).left s hJ₁ hJ₁'
      have tr : ∀ {w : LB.Iso (abelian₂ B' M') ((abelian₂ B M).pull β₂)}, w.IsGen → lamVal w (lift (1 : 𝟙_ (Over S') ⟶ B') 1).left s J₁ J₁' = 1 →
          gm (lift (1 : 𝟙_ (Over S') ⟶ B') 1).left s ((LB.div ((abelian₂ B M).pull β₂) (abelian₂ B' M')).U a) (w.s a) =
            gm (lift (1 : 𝟙_ (Over S') ⟶ B') 1).left s
              ((LB.div ((abelian₂ B M).pull β₂) (abelian₂ B' M')).U a ⊓ (LB.div ((abelian₂ B M).pull β₂) (abelian₂ B' M')).U
                (fun _ I => J₁ ((lift (1 : 𝟙_ (Over S') ⟶ B') 1).left ≫ β₂ ≫ (psum B (x2 B) I.down).left),
                 fun I => J₁' ((lift (1 : 𝟙_ (Over S') ⟶ B') 1).left ≫ (psum B' (x2 B') I.down).left)))
              ((LB.div ((abelian₂ B M).pull β₂) (abelian₂ B' M')).g a
                (fun _ I => J₁ ((lift (1 : 𝟙_ (Over S') ⟶ B') 1).left ≫ β₂ ≫ (psum B (x2 B) I.down).left),
                 fun I => J₁' ((lift (1 : 𝟙_ (Over S') ⟶ B') 1).left ≫ (psum B' (x2 B') I.down).left))) := by
        intro w hw hv
        have := congrArg (gm (lift (1 : 𝟙_ (Over S') ⟶ B') 1).left s _) (hw a
          (fun _ I => J₁ ((lift (1 : 𝟙_ (Over S') ⟶ B') 1).left ≫ β₂ ≫ (psum B (x2 B) I.down).left),
           fun I => J₁' ((lift (1 : 𝟙_ (Over S') ⟶ B') 1).left ≫ (psum B' (x2 B') I.down).left)))
        rw [map_mul, gm_res _ s _ (TopologicalSpace.Opens.mem_inf.2 ⟨ha, hb⟩),
          gm_res _ s _ (TopologicalSpace.Opens.mem_inf.2 ⟨ha, hb⟩)] at this
        rw [this]
        unfold lamVal at hv
        rw [hv, _root_.mul_one]
      rw [tr h₁ (n₁ _ s J₁ J₁' hJ₁ hJ₁'), tr h₂ (n₂ _ s J₁ J₁' hJ₁ hJ₁')]
  rw [hw]

end GlobalTheory.TautUniq
