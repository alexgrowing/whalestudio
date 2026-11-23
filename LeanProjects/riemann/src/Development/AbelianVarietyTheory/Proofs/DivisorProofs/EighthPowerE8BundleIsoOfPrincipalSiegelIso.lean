import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsLinearLiftAdditiveHolomorphicAbelian
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSquareUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePointsCycAway
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIffEighthPowerPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaObjectEighthPowerPrincipalSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarisedE8ThetaPowerOverModuli
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelLevelLoweringQuotientRepresentsReduced
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.SiegLev GlobalTheory.SiegLevCalc GlobalTheory.SiegelPullComp GlobalTheory.SiegelPull
open GlobalTheory.CechPic

noncomputable section

namespace GlobalTheory.SharpIso

theorem iso_of_sRel : ∀ (g n N : ℕ) (B : Type) [CommRing B] (ζ : B) (K : Type) [Field K] (s : Sp K ⟶ Sp B) (c : SiegPre g n ζ s) (b : TBase K N) (C : SiegPre g N (b.ζ : K) (𝟙 (Sp K))) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * (8 * g)) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin g ⊕ Fin g → ℤ))) (t : TObj (8 * g) N J b (𝟙 (Sp K))) (Q : PolAV (Sp K)) (pr : Fin 8 → (Q.A ⟶ c.A)), (∀ u, IsMonHom (pr u)) → (∀ (T' : Over (Sp K)) (y : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ Q.A, ∀ u, x ≫ pr u = y u) → LBIso Q.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) → SRel C c 0 0 (𝟙 _) → IsSharp W a bas t C → ∃ φ : t.A ≅ Q.A, IsMonHom φ.hom ∧ LBIso t.L (Q.L.pull φ.hom.left) := by
  intro g n N B _ ζ K _ s c b C W J a bas t Q pr hpr huniv hQ hrel hsharp
  obtain ⟨φ, hpb, ⟨φ₂, hsq, hP⟩, -⟩ := hrel
  obtain ⟨pr', hpr', huniv', ht, -, -⟩ := hsharp
  have w : φ ≫ c.A.hom = C.A.hom := by simpa using hpb.1.w
  let f : C.A ⟶ c.A := Over.homMk φ w
  haveI : IsIso φ := hpb.1.isIso_fst_of_isIso
  haveI : IsIso f := by
    have : IsIso ((Over.forget _).map f) := by simpa [f] using (inferInstance : IsIso φ)
    exact isIso_of_reflects_iso f (Over.forget _)
  haveI hf : IsMonHom f := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isMonHom_of_mul f
    (fun _ x y => GlobalTheory.AbelianLetters.mul_comp_of_isGrpPullback_id f hpb x y)
  obtain ⟨ψ, hψ, -⟩ := huniv t.A (fun u => pr' u ≫ f)
  obtain ⟨χ, hχ, -⟩ := huniv' Q.A (fun u => pr u ≫ inv f)
  have h1 : ψ ≫ χ = 𝟙 _ := (huniv' t.A pr').unique (fun u => by
      rw [Category.assoc, hχ, ← Category.assoc, hψ, Category.assoc, IsIso.hom_inv_id, Category.comp_id])
    (fun u => Category.id_comp _)
  have h2 : χ ≫ ψ = 𝟙 _ := (huniv Q.A pr).unique (fun u => by
      rw [Category.assoc, hψ, ← Category.assoc, hχ, Category.assoc, IsIso.inv_hom_id, Category.comp_id])
    (fun u => Category.id_comp _)
  have hm : ∀ u, IsMonHom (ψ ≫ pr u) := fun u => by
    rw [hψ]; haveI := hpr' u; infer_instance
  have hψm : IsMonHom ψ := by
    refine ⟨(huniv _ fun u => η[Q.A] ≫ pr u).unique (fun u => ?_) fun _ => rfl,
      (huniv _ fun u => μ[t.A] ≫ ψ ≫ pr u).unique (fun u => Category.assoc _ _ _) fun u => ?_⟩
    · have := hm u
      have := hpr u
      rw [Category.assoc, IsMonHom.one_hom, IsMonHom.one_hom]
    · have := hm u
      have := hpr u
      rw [Category.assoc, IsMonHom.mul_hom, IsMonHom.mul_hom, ← Category.assoc, tensorHom_comp_tensorHom]
  refine ⟨⟨ψ, χ, h1, h2⟩, hψm, ?_⟩
  have hsq' : Geo.Tor.IsSquare φ (f ⊗ₘ f).left :=
    ⟨by rw [← Over.comp_left, tensorHom_fst]; rfl, by rw [← Over.comp_left, tensorHom_snd]; rfl⟩
  obtain rfl := GlobalTheory.LamPull.isSquare_unique hsq hsq'
  have key : ∀ uv : Fin 8 × Fin 8, (lift (pr' uv.1) (pr' uv.2)).left ≫ (f ⊗ₘ f).left =
      ψ.left ≫ (lift (pr uv.1) (pr uv.2)).left := fun uv => by
    rw [← Over.comp_left, ← Over.comp_left, lift_map, comp_lift, hψ, hψ]
  rw [← cls_eq_iff t.isLB (pull_isLB Q.isLB _), (cls_eq_iff t.isLB (LB.isLB_linComb C.isLB _ _)).2 ht,
    cls_linComb C.isLB, (cls_eq_iff C.isLB (pull_isLB c.isLB _)).2 hP, cls_pull c.isLB,
    cls_pull Q.isLB, (cls_eq_iff Q.isLB (LB.isLB_linComb c.isLB _ _)).2 hQ, cls_linComb c.isLB]
  simp only [map_sum, map_zsmul, ← pull_comp, key]

end GlobalTheory.SharpIso
