import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasValues
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueTangentDualNumberStatement

noncomputable section

namespace PositivityTheory.HtPt.Htat

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

theorem valAt_comp_top {B : Type} [CommRing B] {X Y : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (f : X ⟶ Y)
    (s : Γ(Y, ⊤)) : valAt (x ≫ f) ⊤ le_top s = valAt x ⊤ le_top (f.appTop.hom s) := by
  unfold valAt
  congr 1

theorem tors_ext {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] {Γ : QFGroup R T} {S : Scheme.{0}}
    {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ} {i : Γ.G.left ⟶ G.left}
    (h : Γ.IsTorsionAlong G x N i) {Y : Scheme.{0}} {v v' : Y ⟶ Γ.G.left} (h1 : v ≫ Γ.G.hom = v' ≫ Γ.G.hom)
    (h2 : v ≫ i = v' ≫ i) : v = v' :=
  congrArg (·.left) (h.inj (Over.mk (v ≫ Γ.G.hom)) (Over.homMk v rfl) (Over.homMk v' h1.symm) h2)

theorem ht_add : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (χ χ' : T →* Rˣ) (w w' : Module.Dual R L), Γ.IsHT i M N χ w → Γ.IsHT i M N χ' w' → Γ.IsHT i M N (χ * χ') (w + w') := by
  intro R _ _ T _ _ Γ S G _ _ x N i h L _ _ M χ χ' w w' ⟨s, hs, hv⟩ ⟨s', hs', hv'⟩
  have hm : ∀ {B : Type} [CommRing B] (y : Spec (CommRingCat.of B) ⟶ Γ.G.left),
      valAt y ⊤ le_top (s * s') = valAt y ⊤ le_top s * valAt y ⊤ le_top s' := fun y => by simp [valAt]
  refine ⟨s * s', fun t => ?_, fun e => ?_⟩
  · rw [hm, hs t, hs' t, ← map_mul]; rfl
  · obtain ⟨v, h1, h2, h3⟩ := hv e
    obtain ⟨v', h1', h2', h3'⟩ := hv' e
    obtain rfl : v = v' := tors_ext h (h1.trans h1'.symm) (h2.trans h2'.symm)
    refine ⟨v, h1, h2, ?_⟩
    rw [hm, h3, h3']
    ext <;> simp [add_comm]

theorem ht_olin : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (a : G ⟶ G) [IsMonHom a] (α : T →* T) (A : L →ₗ[R] L), (∀ t, (Γ.pt (α t)).left ≫ i = (Γ.pt t).left ≫ i ≫ a.left) → M.IsDiffOf a A → ∀ (χ : T →* Rˣ) (w : Module.Dual R L), Γ.IsHT i M N χ w → Γ.IsHT i M N (χ.comp α) (w ∘ₗ A) := by
  intro R _ _ T _ _ Γ S G _ _ x N i h L _ _ M a _ α A hα hA χ w ⟨s, hs, hv⟩
  let g : Over.mk (Γ.G.hom ≫ x) ⟶ G := Over.homMk i h.isOver
  have hg : g ^ N = 1 := (h.kernel Γ.G g).2 ⟨𝟙 _, Category.id_comp _⟩
  have hga : (g ≫ a) ^ N = 1 := by
    have : ∀ n : ℕ, (g ≫ a) ^ n = (g ^ n) ≫ a := fun n => by
      induction n with
      | zero => simp [MonObj.one_comp]
      | succ n ih => rw [pow_succ, pow_succ, ih, MonObj.mul_comp]
    rw [this, hg, MonObj.one_comp]
  obtain ⟨a', ha'⟩ := (h.kernel Γ.G (g ≫ a)).1 hga
  replace ha' : a'.left ≫ i = i ≫ a.left := ha'
  refine ⟨a'.left.appTop.hom s, fun t => ?_, fun e => ?_⟩
  · have : (Γ.pt t).left ≫ a'.left = (Γ.pt (α t)).left :=
      tors_ext h (by rw [Category.assoc, Over.w, Over.w, Over.w]) (by rw [Category.assoc, ha', hα])
    rw [← valAt_comp_top, this]
    exact hs (α t)
  · obtain ⟨v, ⟨h1, h2⟩, -⟩ := GlobalTheory.T.existsUnique_tangent_dual_number R T Γ S G x N i h L M e
    obtain ⟨v', h1', h2', h3'⟩ := hv (A e)
    have : v ≫ a'.left = v' := tors_ext h (by rw [Category.assoc, Over.w, h1, h1']) (by
      rw [Category.assoc, ha', ← Category.assoc, h2, h2', hA e, Over.comp_left, Category.assoc])
    exact ⟨v, h1, h2, by rw [← valAt_comp_top, this, h3']; rfl⟩

end PositivityTheory.HtPt.Htat
