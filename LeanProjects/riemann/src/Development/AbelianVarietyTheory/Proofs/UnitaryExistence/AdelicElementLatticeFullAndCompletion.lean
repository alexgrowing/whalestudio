import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGram
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionRationalPointsAndApproximation
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeRationalVectorsInAdelicTranslate
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ZeroMemLatOf
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum

noncomputable section

namespace GlobalTheory.Member

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem latOf_one_eq (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (L : Submodule (𝓞 E) (Fin n → E)) (h1 : L.FG) (h2 : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    GlobalTheory.AdLat.latOf F (1 : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E)) (L : Set (Fin n → E)) = L := by
  ext v
  have h := (GlobalTheory.AdLat.hat_rational_points_and_approx F E n L h1 h2).1 v
  simp only [GlobalTheory.AdLat.latOf, Set.mem_ofPred_eq, Set.mem_image, Matrix.one_mulVec, exists_eq_right,
    SetLike.mem_coe]
  exact h

theorem latG_eq_span_latOf (D : D7) (V : HSp D) (g : GA D V) :
    latG V g = Submodule.span (𝓞 D.host.E) {w | ∃ a ∈ D.host.AA,
      ∃ v ∈ GlobalTheory.AdLat.latOf D.host.F (finHom V g).1 (latC V : Set (Fin V.rank → D.host.E)), w = a • v} := by
  have hh := (latHat_eq_hat_and_gram D V).1
  unfold latG gLat
  rw [hh]
  rfl

theorem latGHat_eq_closure (D : D7) (V : HSp D) (g : GA D V) :
    latGHat V g = AddSubgroup.closure {w | ∃ a ∈ D.host.AA,
      ∃ z ∈ (finHom V g).1.mulVec '' (GlobalTheory.AdLat.hat D.host.F (latC V : Set (Fin V.rank → D.host.E))),
        w = fun i => ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] a) * z i} := by
  have hh := (latHat_eq_hat_and_gram D V).1
  unfold latGHat gLat
  rw [hh]

theorem latG_lattice_and_completion : ∀ (D : D7) (V : HSp D), ∀ g : GA D V, (latG V g).FG ∧ Submodule.span D.host.E (latG V g : Set (Fin V.rank → D.host.E)) = ⊤ ∧ (latG V g : Set (Fin V.rank → D.host.E)) = GlobalTheory.AdLat.latOf D.host.F (finHom V g).1 (latG V 1 : Set (Fin V.rank → D.host.E)) ∧ (latGHat V g : Set (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E)) = (finHom V g).1.mulVec '' (GlobalTheory.AdLat.hat D.host.F (latG V 1 : Set (Fin V.rank → D.host.E))) ∧ latGHat V g = GlobalTheory.AdLat.hat D.host.F (latG V g : Set (Fin V.rank → D.host.E)) ∧ latG V 1 = Submodule.span (𝓞 D.host.E) {w | ∃ a ∈ D.host.AA, ∃ x ∈ latC V, w = a • x} := by
  intro D V g
  obtain ⟨-, -, hfg, hsp, -⟩ := latHat_eq_hat_and_gram D V
  have hA : D.host.AA ≠ 0 := AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D
  have h6 : latG V 1 = Submodule.span (𝓞 D.host.E) {w | ∃ a ∈ D.host.AA, ∃ x ∈ latC V, w = a • x} := by
    rw [latG_eq_span_latOf, map_one, Units.val_one, latOf_one_eq _ _ _ _ hfg hsp]
    rfl
  obtain ⟨s1, s2, s3, s4⟩ := GlobalTheory.AdLat.scale_latOf D.host.F D.host.E V.rank (latC V) (finHom V g) D.host.AA
    (latG V 1) hfg hsp hA h6
  have h3 : (latG V g : Set (Fin V.rank → D.host.E)) =
      GlobalTheory.AdLat.latOf D.host.F (finHom V g).1 (latG V 1 : Set (Fin V.rank → D.host.E)) := by
    rw [latG_eq_span_latOf D V g]; exact s1
  have h4 : (latGHat V g : Set (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E)) =
      (finHom V g).1.mulVec '' (GlobalTheory.AdLat.hat D.host.F (latG V 1 : Set (Fin V.rank → D.host.E))) := by
    rw [latGHat_eq_closure D V g]; exact s2
  obtain ⟨Λ, l1, l2, l3, l4⟩ := GlobalTheory.AdLat.exists_lattice_latOf D.host.F D.host.E V.rank (latG V 1) (finHom V g) s3 s4
  have hΛ : Λ = latG V g := SetLike.coe_injective (l1.trans h3.symm)
  subst hΛ
  exact ⟨l2, l3, h3, h4, SetLike.coe_injective (h4.trans l4.symm), h6⟩

end GlobalTheory.Member
