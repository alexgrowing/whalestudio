import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeRegularAtLocalPoint
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalAtLocalRingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeTangentVectorsAffineOpen

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeMetric.FrameDual

theorem exists_frame_dual_sq : ∀ (S X : Scheme.{0}) (G : Over S) [GrpObj G] (Gx : Over X) [GrpObj Gx] [IsCommMonObj Gx] [Smooth Gx.hom] (φ : Gx.left ⟶ G.left) (Ω₁ : Type) [Field Ω₁] (ξ : Spec (CommRingCat.of Ω₁) ⟶ X), IsCptGen ξ → ∀ (Li : Type) [AddCommGroup Li] [Module Ω₁ Li] (M : LieModel Gx ξ Li) (F : Type) [Field F] (θ : Ω₁ →+* F) (A : Subring F) [IsLocalRing A] (z : Spec (CommRingCat.of A) ⟶ X) (h : genPt ξ ⤳ centre z), (∀ s : X.presheaf.stalk (centre z), (((Scheme.stalkClosedPointTo z).hom s : A) : F) = θ (genMap ξ ⟨centre z, h⟩ s)) → ∀ (ER : Type) [AddCommGroup ER] [Module A ER] (MR : LieModel Gx z ER) (xF : Spec (CommRingCat.of F) ⟶ S) (V : Type) [AddCommGroup V] [Module F V] (MV : LieModel G xF V) (io : ER → V) (Lm : Li → V), (∀ x, (MV.pt (io x)).left = Spec.map (CommRingCat.ofHom (dualMap A.subtype)) ≫ (MR.pt x).left ≫ φ) → (∀ e, (MV.pt (Lm e)).left = Spec.map (CommRingCat.ofHom (dualMap θ)) ≫ (M.pt e).left ≫ φ) → ∀ (r : ℕ) (b : Fin r → Li) (π : Fin r → Module.Dual Ω₁ Li) (m : ℕ), (∀ i, (m : Ω₁) • b i ∈ M.lat ⟨centre z, h⟩) → (∀ i j, π i (b j) = if i = j then 1 else 0) → (∀ i, ∀ e ∈ M.lat ⟨centre z, h⟩, (m : Ω₁) * π i e ∈ regAt ξ ⟨centre z, h⟩) → ∃ (β : Fin r → ER) (g : Fin r → ER →ₗ[A] A), (∀ k, io (β k) = Lm ((m : Ω₁) • b k)) ∧ ∀ i k, ((g i (β k) : A) : F) = if k = i then (m : F) ^ 2 else 0 := by
  intro S X G _ Gx _ _ _ φ Ω₁ _ ξ hξ Li _ _ M F _ θ A _ z h hs ER _ _ MR xF V _ _ MV io Lm hio hLm r b π m hm hπ hreg
  obtain ⟨ev, hev, -, -⟩ := GlobalTheory.T.lie_lattice_eval_at_local_ring X Gx Ω₁ ξ Li M A z h ER MR hξ inferInstance
  let β : Fin r → ER := fun k => ev ⟨(m : Ω₁) • b k, hm k⟩
  have hval : ∀ k, M.ValAt z ((m : Ω₁) • b k) (MR.pt (β k)) := fun k => (hev _ _).2 ⟨hm k, rfl⟩
  have hcomp : A.subtype.comp (Scheme.stalkClosedPointTo z).hom = θ.comp (genMap ξ ⟨centre z, h⟩) :=
    RingHom.ext fun s => hs s
  have hg : ∀ i, ∃ g : ER →ₗ[A] A, ∀ (e : Li) (x : ER) (u : A), M.ValAt z e (MR.pt x) →
      ValAt ξ z (((m : Ω₁) • π i) e) u → g x = u := fun i =>
    GlobalTheory.CompanionTheory.Ar.RootHt.exists_lieFunctional X Gx Ω₁ ξ Li M A z h ER MR ((m : Ω₁) • π i) hξ
      (fun e he => by simpa [smul_eq_mul] using hreg i e he)
  choose g hg using hg
  refine ⟨β, g, fun k => ?_, fun i k => ?_⟩
  · obtain ⟨h', v, hext, hw⟩ := hval k
    have e1 := GlobalTheory.CompanionTheory.Ar.HodgeMetric.FrameExt.spec_dual_comp (Scheme.stalkClosedPointTo z).hom A.subtype
    have e2 := GlobalTheory.CompanionTheory.Ar.HodgeMetric.FrameExt.spec_dual_comp (genMap ξ ⟨centre z, h⟩) θ
    apply MV.inj
    apply Over.OverMorphism.ext
    rw [hio, hLm, hext.2, hw]
    simp only [Category.assoc]
    rw [← Category.assoc (Spec.map (CommRingCat.ofHom (dualMap A.subtype))),
      ← Category.assoc (Spec.map (CommRingCat.ofHom (dualMap θ))), e1, e2, hcomp]
  · have hnat : ∀ n : ℕ, ValAt ξ z (n : Ω₁) (n : A) := fun n =>
      ⟨h, (n : X.presheaf.stalk (centre z)), map_natCast _ n, map_natCast _ n⟩
    have hv : ((m : Ω₁) • π i) ((m : Ω₁) • b k) = ((if k = i then m ^ 2 else 0 : ℕ) : Ω₁) := by
      by_cases e : k = i
      · subst e
        simp [hπ, smul_eq_mul, pow_two]
      · have e' : ¬ i = k := fun q => e q.symm
        simp [hπ, e, e']
    have h1 := hg i _ (β k) _ (hval k) (hv ▸ hnat _)
    rw [h1]
    by_cases e : k = i <;> simp [e]

end GlobalTheory.CompanionTheory.Ar.HodgeMetric.FrameDual
