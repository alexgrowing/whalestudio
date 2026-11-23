import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KeyPBIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianSectionsIrreducibleThetaGroup
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ThetaGrpActsLinearly
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsIsGenOfInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslateThetaPullbackNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulOfTwistedPullbacksSameBundleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.TSpan

noncomputable def actL {K : Type} [Field K] (P : PolAV (Sp K)) (k : ℕ)
    (ρ : ThetaGrp P.A P.L (k : ℤ) (baseOver (Sp K)) → (SecM P.A P.L (k : ℤ) (baseOver (Sp K)) ≃ₗ[Γ((baseOver (Sp K)).left, ⊤)] SecM P.A P.L (k : ℤ) (baseOver (Sp K))))
    (θ : ThetaGrp P.A P.L (k : ℤ) (baseOver (Sp K))) : EA P (𝟙 (Sp K)) k →ₗ[K] EA P (𝟙 (Sp K)) k where
  toFun w := SecMod.mk _ (SecM.toSec P.A (ρ θ (SecM.ofSec P.A w.sec)))
  map_add' a b := by
    show SecMod.mk _ (SecM.toSec P.A (ρ θ (SecM.ofSec P.A a.sec + SecM.ofSec P.A b.sec))) = _
    rw [map_add]; rfl
  map_smul' c w := by
    show SecMod.mk _ (SecM.toSec P.A (ρ θ ((Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv c • SecM.ofSec P.A w.sec))) = _
    rw [map_smul]; rfl

theorem span_eq_top : ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x : KeyIn K) (m : ℕ), Odd m → 3 ≤ m →
    ∀ (I : Type) (pt : I → (baseOver (Sp K) ⟶ x.P.A)), (∀ z : baseOver (Sp K) ⟶ x.P.A, z ^ (m ^ 2) = 1 → ∃ i, pt i = z) →
    ∀ (th : LB.Sec (LPow x.P.A x.P.L ((1 : ℕ) : ℤ) (baseOver (Sp K)))), IsPolAVSectionInverseImage x.P (baseOver (Sp K)) x.th th →
    ∀ (U : I → ThetaGrp x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp K)))
      (t : I → LB.Sec (LPow x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp K)))),
    (∀ i, SymLift x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) (pt i) (U i) ∧ Tr x.P x.rig m th (U i) (t i)) →
    Submodule.span K (Set.range fun i =>
      (SecMod.mk (fst (baseOver (Sp K)) x.P.A).left (t i) : EA x.P (𝟙 (Sp K)) (m ^ 2))) = ⊤ := by
  intro K _ _ _ x m hm hm3 I pt hpt th hth U t hUt
  haveI : IsLocallyNoetherian (Sp K) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of K)))
  haveI := x.P.isAb.comm
  have hm0 : m ≠ 0 := by omega
  have hN : ((m ^ 2 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (pow_ne_zero 2 hm0)
  have hN1 : 1 ≤ m ^ 2 := Nat.one_le_iff_ne_zero.2 (pow_ne_zero 2 hm0)
  obtain ⟨-, hirr⟩ := GlobalTheory.ThetaIrred.main GlobalTheory.allSixLaws.1 GlobalTheory.allSixLaws.2.1 (Sp K) x.P K (𝟙 _) (m ^ 2) hN
  obtain ⟨ρ, hact, -, hrat, hmul⟩ := GlobalTheory.thetaGrp_acts_linearly GlobalTheory.allSixLaws.1.globalFns (Sp K) x.P ((m ^ 2 : ℕ) : ℤ)
    (baseOver (Sp K))
  let f := actL x.P (m ^ 2) ρ
  have hf : ∀ θ (a b : LB.Sec (LPow x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp K)))), IsActOf x.P.A x.P.L _ θ a b →
      f θ (SecMod.mk _ a) = SecMod.mk _ b := fun θ a b h => by
    show SecMod.mk _ (SecM.toSec x.P.A (ρ θ (SecM.ofSec x.P.A a))) = _
    rw [(hact θ a b).1 h]; rfl
  have hf' : ∀ θ (a : LB.Sec (LPow x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp K)))),
      IsActOf x.P.A x.P.L _ θ a (f θ (SecMod.mk _ a)).sec := fun θ a => (hact θ _ _).2 rfl

  have hker : ∀ θ : ThetaGrp x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp K)), θ.pt ^ (m ^ 2) = 1 := fun θ =>
    (GlobalTheory.allSixLaws.1.kerPow (Sp K) x.P (m ^ 2) hN1 _ θ.pt).1 fun _ =>
      ⟨⊤, trivial, GlobalTheory.exists_isGen_pull _ θ.φ θ.isGen _⟩
  let Wsp := Submodule.span K (Set.range fun i =>
    (SecMod.mk (fst (baseOver (Sp K)) x.P.A).left (t i) : EA x.P (𝟙 (Sp K)) (m ^ 2)))
  refine (hirr Wsp fun θ hθ v v' hvv' hv => ?_).resolve_left fun h => ?_
  · have e0 : f θ v = v' := hf θ v.sec v'.sec hvv'
    rw [← e0]
    refine (Submodule.span_le.2 ?_ : Wsp ≤ Wsp.comap (f θ)) hv
    rintro _ ⟨i, rfl⟩
    obtain ⟨-, α, s₁, hα, -, htw, ha⟩ := hUt i
    obtain ⟨θ₂, hp₂, hv₂⟩ := hmul θ (U i)
    obtain ⟨k, hk⟩ := hpt (θ.pt * pt i) (by rw [mul_pow, hθ, ← (hUt i).1.pt_eq, hker, _root_.mul_one])
    obtain ⟨-, α', s₁', hα', -, htw', ha'⟩ := hUt k
    obtain ⟨c, hc⟩ := GlobalTheory.T.exists_smul_of_twistedPullbacks_sameBundle K x.P m (by omega) th α' α s₁' s₁ hα' hα htw' htw
    obtain ⟨d, hd⟩ := hrat (U k) θ₂ (by rw [hp₂, (hUt k).1.pt_eq, (hUt i).1.pt_eq, hk])
    have e : f θ (SecMod.mk _ (t i)) = f θ₂ (SecMod.mk _ s₁) := by
      rw [← hf _ _ _ ha]
      show SecMod.mk _ (SecM.toSec x.P.A (ρ θ _)) = SecMod.mk _ (SecM.toSec x.P.A (ρ θ₂ _))
      rw [hv₂]; rfl
    have e₂ : f θ₂ (SecMod.mk _ s₁) =
        ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (d : Γ((baseOver (Sp K)).left, ⊤))) • f (U k) (SecMod.mk _ s₁) := by
      show SecMod.mk _ (SecM.toSec x.P.A (ρ θ₂ _)) = _
      rw [hd]
      have e3 : (d : Γ((baseOver (Sp K)).left, ⊤)) = (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
          ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (d : Γ((baseOver (Sp K)).left, ⊤))) := by
        simp [Iso.commRingCatIsoToRingEquiv]
      conv_lhs => rw [e3]
      rfl
    show f θ (SecMod.mk _ (t i)) ∈ Wsp
    rw [e, e₂, hc, map_smul, hf _ _ _ ha']
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
  · obtain ⟨i, hi⟩ := GlobalTheory.T.exists_translate_thetaPullback_ne_zero K x m hm hm3 I pt hpt th hth U t hUt
    exact hi ((Submodule.eq_bot_iff _).1 h _ (Submodule.subset_span ⟨i, rfl⟩))

end GlobalTheory.TSpan
