import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverCompImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyUnramifiedAdjointRingActionScheme
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleSpreadSubring
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetOfGeom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SympAtPullbackIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelSectionsExactKernelLocusOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenLocusTorsionPointsAreLevelSectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricBundleLevelOdd

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.SympLevLocus

theorem range_sub_iff {X : Scheme.{0}} {k : Type} [Field k] (x : Sp k ⟶ X) (W : Set X) (p₀ : Sp k) :
    Set.range x.base ⊆ W ↔ x.base p₀ ∈ W := by
  refine ⟨fun H => H ⟨p₀, rfl⟩, ?_⟩
  rintro H _ ⟨p, rfl⟩
  rwa [Subsingleton.elim p p₀]

open GlobalTheory.SiegelPull in

theorem exists_open_sympLev : ∀ (h M : ℕ) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (t : S' ⟶ Sp (cycAway M)) (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S') ⟶ G)), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → 3 ≤ M → Odd M → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ M = 1) → ∃ U : S'.Opens, (∀ V : S'.Opens, V ≤ U → IsSympLev (P.pull (Pdiv.PullbackComparison.pφ₂ V.ι G)) h M (zetaAway M) (V.ι ≫ t) (fun a => GlobalTheory.SiegelPull.secPull (Pdiv.PullbackComparison.isGrpPullback V.ι G) (lev a))) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S') (c' : SiegPre h M (zetaAway M) (g ≫ t)) (φ : c'.A.left ⟶ G.left) (φ₂ : (G2 c'.A).left ⟶ (G2 G).left), IsGrpPullback c'.A G g φ → IsSquare φ φ₂ → LBIso c'.P (P.pull φ₂) → (∀ a, (c'.lev a).left ≫ φ = g ≫ (lev a).left) → Set.range g.base ⊆ (U : Set S') := by
  intro h M S' _ t G _ _ P lev hab hP hr₁ hr₂ hsy hM hodd hadd htor
  let Good : S'.Opens → Prop := fun W => ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S')
    (β : cycAway M →+* k) (z : kˣ), Set.range x.base ⊆ W → x ≫ t = spMap β → (z : k) = β (zetaAway M) →
      SympAt P h M lev k x z
  have hsup : ∀ (k : Type) [Field k] (x : Sp k ⟶ S'), Set.range x.base ⊆ (sSup {W | Good W} : S'.Opens) →
      ∃ W, Good W ∧ Set.range x.base ⊆ W := by
    intro k _ x hx
    let p₀ : Sp k := (⊥ : PrimeSpectrum k)
    rw [range_sub_iff x _ p₀] at hx
    obtain ⟨W, hW, hpW⟩ := TopologicalSpace.Opens.mem_sSup.1 hx
    exact ⟨W, hW, (range_sub_iff x _ p₀).2 hpW⟩
  refine ⟨sSup {W | Good W}, fun V hV => ?_, ?_⟩
  · have pb := Pdiv.PullbackComparison.isGrpPullback V.ι G
    refine (isSympLev_iff _ _ _ _ _ _).2 ⟨fun a b => push_injective pb _ ?_, fun a => push_injective pb _ ?_,
      fun k _ _ x β z hx hz => ?_⟩
    · rw [map_mul, push_secPull', push_secPull', push_secPull', hadd, MonObj.comp_mul]
    · rw [map_pow, map_one, push_secPull', ← MonObj.comp_pow, htor, MonObj.comp_one]
    · rw [sympAt_pullback_iff V.ι hP (pull_isLB hP _) pb (Pdiv.PullbackComparison.isSquare V.ι G)
        (Pdiv.PullbackComparison.gen_refl _ (pull_isLB hP _)) (fun a => secPull_left pb _)]
      obtain ⟨W, hW, hxW⟩ := hsup k (x ≫ V.ι) (by
        rintro _ ⟨p, rfl⟩
        exact hV (by first | exact (x.base p).2 | simp | (rw [← Scheme.Opens.range_ι V]; exact ⟨_, rfl⟩)))
      exact hW k (x ≫ V.ι) β z hxW (by rw [Category.assoc]; exact hx) hz
  · intro T g c' φ φ₂ pb sq iso hl
    rintro _ ⟨τ, rfl⟩
    obtain ⟨K, _, _, x₀, ⟨q, hq⟩⟩ := GlobalTheory.SiegelTypings.exists_geomPt τ
    obtain ⟨β, hβ⟩ := (⟨(Spec.preimage (x₀ ≫ g ≫ t)).hom, by simp [spMap]⟩ : ∃ β : cycAway M →+* K, spMap β = x₀ ≫ g ≫ t)
    let z : Kˣ := ((GlobalTheory.LowChart.isUnit_zetaAway M hM).map β).unit
    have hc : SympAt c'.P h M c'.lev K x₀ z := c'.geom K x₀ β z hβ.symm rfl
    obtain ⟨hS₁, hS₂, hS₃⟩ := (sympAt_pullback_iff g hP c'.isLB pb sq iso hl K x₀ z).1 hc
    have e₁ := GlobalTheory.T.level_sections_exact_kernel_locus_open S' M t G h lev hab hM hadd htor K (x₀ ≫ g)
    have e₂ := GlobalTheory.T.exists_open_locus_torsion_points_are_level_sections S' M t G h lev hab hM hadd htor K (x₀ ≫ g)
    have e₃ := GlobalTheory.T.symmetric_bundle_level_odd S' M t G P h lev hab hP hr₁ hr₂ hsy hM hodd hadd htor K (x₀ ≫ g) β z (by rw [Category.assoc, hβ]) rfl
    obtain ⟨W₁, hW₁, H₁⟩ := e₁ hS₁
    obtain ⟨W₂, hW₂, H₂⟩ := e₂ hS₂
    obtain ⟨W₃, hW₃, H₃⟩ := e₃ hS₃
    have hgood : Good (W₁ ⊓ W₂ ⊓ W₃) := fun k _ _ x β' z' hx hxt hz' =>
      ⟨H₁ k x (hx.trans (le_trans inf_le_left inf_le_left)), H₂ k x (hx.trans (le_trans inf_le_left inf_le_right)),
        H₃ k x β' z' (hx.trans inf_le_right) hxt hz'⟩
    have hmem : g.base τ ∈ (W₁ ⊓ W₂ ⊓ W₃ : S'.Opens) := by
      have e : (x₀ ≫ g).base q = g.base τ := by first | simp [← hq] | (rw [Scheme.Hom.comp_apply, hq]) | (rw [Scheme.comp_base_apply, hq])
      rw [← e]
      exact ⟨⟨hW₁ ⟨q, rfl⟩, hW₂ ⟨q, rfl⟩⟩, hW₃ ⟨q, rfl⟩⟩
    exact (le_sSup (show W₁ ⊓ W₂ ⊓ W₃ ∈ {W | Good W} from hgood)) hmem

end GlobalTheory.SympLevLocus
