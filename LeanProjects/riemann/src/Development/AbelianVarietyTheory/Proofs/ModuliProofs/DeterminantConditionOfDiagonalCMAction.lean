import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HolomorphicUniformizationTangentUnimodularRiemann
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueSumSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLieBasisOfHolUnif
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DetCondIffOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DetCondOfEigenbasis

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem GlobalTheory.detCond_of_diagonal_action : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (act : OAct (𝓞 E) P.A) (ty : Fin P.g → (E →+* ℂ)), u.IsAH Hm χ → IsTypeFn H D.p D.q ty → (∀ (a : 𝓞 E) z, u.ex (fun i => ty i (a : E) * z i) = u.ex z ≫ act.act a) → ∀ (K : Type) [Field K] [IsAlgClosed K] (β : ℂ →+* K), DetCond D act (spMap β) (β H.rt0) := by
  intro _ _ _ unif E _ _ _ H D P u _ _ act ty _ hty hact K _ _ β
  obtain ⟨h₁, h₂, -⟩ := GlobalTheory.AnyUnif.tangent_and_unimodular unif P u
  have hs : Smooth P.A.hom := P.isAb.smooth
  obtain ⟨v, hv, heig⟩ := GlobalTheory.exists_lieBasis_of_holUnif P.A P.L P.g u hs h₁ h₂
  have key : ∀ τ₀ : E →+* ℂ, LieMult act (𝟙 (Sp ℂ)) (τ₀.comp (algebraMap (𝓞 E) E))
      (Nat.card {i // ty i = τ₀}) := fun τ₀ => by
    have h := GlobalTheory.lieMult_of_eigenbasis ℂ (𝓞 E) P.A act P.g v (fun i => (ty i).comp (algebraMap (𝓞 E) E)) hs hv
      (fun i a => heig _ _ (act.hom a) (hact a) i) (τ₀.comp (algebraMap (𝓞 E) E))
    convert h using 1
    exact Nat.card_congr (Equiv.subtypeEquivRight fun i =>
      ⟨fun e => by rw [e], fun e => IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) e⟩)
  have hd : DetCond D act (𝟙 (Sp ℂ)) H.rt0 := fun τ => by
    obtain ⟨τ₀, rfl⟩ := GlobalTheory.PeriodPoint.exists_embedding (RingHom.id ℂ) τ
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [← (hty τ₀).1 h]; exact key τ₀
    · rw [← (hty τ₀).2 h]; exact key τ₀
  have := (GlobalTheory.detCond_iff_of_field_extension E H D _ P.A ℂ K β (𝟙 _) act H.rt0 hs).2 hd
  rwa [Category.comp_id] at this
