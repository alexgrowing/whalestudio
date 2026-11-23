import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegCover

theorem unitOn_pow' {R : Type} [CommRing R] (u : Rˣ) (m : ℕ) : unitOn (u ^ m) = unitOn u ^ m := by
  unfold unitOn; exact map_pow _ u m

theorem unitOn_one' {R : Type} [CommRing R] : unitOn (1 : Rˣ) = 1 := by
  unfold unitOn; exact map_one _

theorem weilIs_congr_base {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {m : ℤ} {k : Type} [Field k]
    {y y' : Sp k ⟶ S} (e : y = y') {x₁ x₂ : Over.mk y ⟶ A} {x₁' x₂' : Over.mk y' ⟶ A}
    (h₁ : x₁.left = x₁'.left) (h₂ : x₂.left = x₂'.left) {c : Γ(Sp k, ⊤)ˣ} (H : Out.WeilIs A L m x₁ x₂ c) :
    Out.WeilIs A L m x₁' x₂' c := by
  subst e
  rwa [← Over.OverMorphism.ext h₁, ← Over.OverMorphism.ext h₂]

theorem weilTransport : ∀ (h N m : ℕ) (B B₁ : Type) [CommRing B] [CommRing B₁] (ζ : B) (ζ₁ : B₁) (S T : Scheme.{0}) (s : S ⟶ Sp B) (sT : T ⟶ Sp B₁) (c : SiegPre h m ζ s) (C' : SiegPre h N ζ₁ sT) (t : T ⟶ S) (φ : C'.A.left ⟶ c.A.left), IsGrpPullback C'.A c.A t φ → (∃ φ₂ : (G2 C'.A).left ⟶ (G2 c.A).left, IsSquare φ φ₂ ∧ LBIso C'.P (c.P.pull φ₂)) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T) (β : B₁ →+* k) (z : kˣ) (y : Sp k ⟶ S) (g g' : Over.mk y ⟶ c.A) (a a' : Fin h ⊕ Fin h → ℤ), x ≫ sT = spMap β → (z : k) = β ζ₁ → y = x ≫ t → g.left = x ≫ (C'.lev a).left ≫ φ → g'.left = x ≫ (C'.lev a').left ≫ φ → Out.WeilIs c.A c.diag N g g' (unitOn (z ^ (2 * omegaStd a a'))) := by
  intro h N m B B₁ _ _ ζ ζ₁ S T s sT c C' t φ pb hφ k _ _ x β z y g g' a a' hx hz hy hg hg'
  obtain ⟨φ₂, sq, iso⟩ := hφ
  subst hy
  obtain ⟨-, -, g₃⟩ := C'.geom k x β z hx hz
  exact (weilIs_grpPullback_of_comm S T c.A C'.A t φ _ _ (pull_isLB c.isLB _) (pull_isLB C'.isLB _) pb
    (SiegelPull.diag_iso sq iso) (Over.mk x) N _ _ g g' _
    (by rw [hg, Over.comp_left, Over.toUnit_left, Category.assoc]; rfl)
    (by rw [hg', Over.comp_left, Over.toUnit_left, Category.assoc]; rfl)).1 (g₃ a a')

theorem omegaStd_add_nsmul {h : ℕ} (N : ℕ) (a a' c₁ c₂ : Fin h ⊕ Fin h → ℤ) :
    omegaStd (a + N • c₁) (a' + N • c₂) =
      omegaStd a a' + N * (omegaStd c₁ a' + omegaStd a c₂ + N * omegaStd c₁ c₂) := by
  simp only [omegaStd, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply, mul_add,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

end GlobalTheory.SiegCover
