import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LinearUniformisationTorsionIsomorphism
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalWeilPairingEq
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamilyFibreEqUniformisedPullbackGenericFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreePerpLabelKernelWeights
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GaloisHolds
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.GenTors

theorem exists_torsMap_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) [CharZero R], AdmBase R (maximalIdeal R) →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k →
    ∃ f : QkPt P.D.toPre F k → (TF (R := R) F ⟶ t.G),
      (∀ q v, GlobalTheory.FlatTors.IsImage P F k q v ↔ v = (f q).left) ∧ (∀ q, f q ^ k = 1) ∧ (∀ x, x ^ k = 1 → ∃ q, f q = x) ∧
      (∀ p p' p'', QkAdd p p' p'' → f p'' = f p * f p') ∧
      (∀ p p' τ, p.y = 0 → GlobalTheory.UT.IsTor τ p.g →
        GlobalTheory.UU.CubWeil t.cub k (f p) (f p') (unitOn (τ (Multiplicative.ofAdd p'.y)))) ∧
      ∀ (σ : F →ₐ[FractionRing R] F) p p', QkExt σ.toRingHom p p' → (f p').left = spMap σ.toRingHom ≫ (f p).left := by
  intro E _ _ _ H R _ _ _ t P _ hR F _ _ _ k hk
  letI := H.starRing
  obtain ⟨f₀, h1, h2, -, h4, -, h6⟩ := GlobalTheory.FlatTors.torsionIso_holds E H R (maximalIdeal R) hR t P F k hk
  obtain ⟨g₁, g₂, -⟩ := GlobalTheory.Ex.GenericFibre.unif_generic P
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv g₁ (TFK (R := R) F) (jFK (R := R) F ≫ jK R) rfl
  have hpow : ∀ q, f₀ q ^ k = 1 := fun q => by
    obtain ⟨w, hw⟩ := P.U.toUnifPre.ext
    exact ((h1 q (f₀ q)).2 rfl w hw).1
  have hpow' : ∀ q, e (f₀ q) ^ k = 1 := fun q => by rw [← map_pow, hpow, map_one]
  refine ⟨fun q => e (f₀ q), ?_, hpow', ?_, ?_, ?_, ?_⟩
  · intro q v
    constructor
    · rintro ⟨a, ha, hq⟩
      rw [(h1 q a).1 hq] at ha
      rw [← ha, he]
    · intro hv
      exact ⟨f₀ q, by rw [hv, he], (h1 q (f₀ q)).2 rfl⟩
  · intro x hx
    obtain ⟨q, hq⟩ := h2 (e.symm x) (by rw [← map_pow, hx, map_one])
    exact ⟨q, by simp only [hq, MulEquiv.apply_symm_apply]⟩
  · intro p p' p'' h
    simp only [h4 p p' p'' h, map_mul]
  · intro p p' τ hy hτ
    have hw : WeilIs P.A.A P.A.L k (f₀ p) (f₀ p') (unitOn (τ (Multiplicative.ofAdd p'.y))) :=
      (h6 p p' _).1 (GlobalTheory.ZH.TorusPerp.weilQkIs_tor GlobalTheory.firstFiveLaws.1.globalFns p p' hy hτ)
    have hpr : IsProper (pullback.snd t.G.hom (jK R)) := by
      have := P.A.isAb.proper
      have := isIso_inv_left P.U.gen.symm
      have h : IsProper ((Over.pullback (jK R)).obj t.G).hom := by
        rw [← Over.w P.U.gen.symm.inv]; infer_instance
      exact h
    have one : ∀ c : Fˣ, GlobalTheory.UU.CubWeil t.cub k (e (f₀ p)) (e (f₀ p')) (unitOn c) →
        WeilIs P.A.A P.A.L (k : ℤ) (f₀ p) (f₀ p') (unitOn c) := fun c h =>
      (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ t.G P.A.A (jK R) _ t.PP.L P.A.L t.PP.isLB P.A.isLB g₁ g₂
        (TFK (R := R) F) k (f₀ p) (f₀ p') (e (f₀ p)) (e (f₀ p')) (unitOn c) (he _) (he _)).2
        (GlobalTheory.FlatTors.weilIs_of_cubWeil_of_proper (jK R) t.G t.semi hpr t.cub k (TFK (R := R) F) _ _ _ h)
    obtain ⟨ζ, hζ, -⟩ := (GlobalTheory.UU.cubWeil_basic _ t.G t.PP t.cub k _).1 (e (f₀ p)) (e (f₀ p')) (hpow' p) (hpow' p')
    obtain ⟨c, rfl⟩ : ∃ c : Fˣ, unitOn c = ζ :=
      ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.toMonoidHom ζ,
        Units.ext ((Scheme.ΓSpecIso (CommRingCat.of F)).hom_inv_id_apply _)⟩
    have ec : c = τ (Multiplicative.ofAdd p'.y) :=
      GlobalTheory.weilIs_unique_fieldPoint _ P.A.A P.A.L P.A.isLB F _ k (f₀ p) (f₀ p') c _ (one c hζ) hw
    exact ec ▸ hζ
  · intro σ p p' hpp'
    obtain ⟨-, hx, hiff⟩ := GlobalTheory.UT.Cl.galois_holds R (maximalIdeal R) hR P.D P.A t.G t.semi P.U F F σ k hk p
    obtain ⟨x', hx'⟩ := hx (f₀ p)
    have e' : x' = f₀ p' := (h1 p' x').1 ((hiff p' (f₀ p) x' hpp' hx').1 ((h1 p (f₀ p)).2 rfl))
    subst e'
    rw [he, he, hx', Category.assoc]

end GlobalTheory.GenTors
