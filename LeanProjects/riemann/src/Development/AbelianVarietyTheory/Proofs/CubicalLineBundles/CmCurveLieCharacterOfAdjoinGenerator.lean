import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.LieChar

variable {R : Type} [CommRing R] {G G' : Over (Sp R)} [GrpObj G] [GrpObj G']

theorem isLieComb_one_iff (c : R) (v w : epsR R ⟶ G) :
    IsLieComb ![c] ![v] w ↔ w.left = spMap (epsScaleR c) ≫ v.left := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa using hu 0
  · intro h
    exact ⟨![w], fun i => by fin_cases i; exact h, by simp⟩

theorem isLieComb_comp {c : R} {v w : epsR R ⟶ G} (h : IsLieComb ![c] ![v] w) (f : G ⟶ G') :
    IsLieComb ![c] ![v ≫ f] (w ≫ f) := by
  rw [isLieComb_one_iff] at h ⊢
  simp [h]

theorem isTangent_comp {v : epsR R ⟶ G} (h : IsTangent v) (f : G ⟶ G') [IsMonHom f] :
    IsTangent (v ≫ f) := by
  unfold IsTangent at h ⊢
  rw [Over.comp_left, ← Category.assoc, h, ← Over.comp_left, IsMonHom.one_hom]

theorem spMap_epsScaleR_one : spMap (epsScaleR (1 : R)) = 𝟙 _ := by
  have : epsScaleR (1 : R) = RingHom.id _ := by
    ext x <;> simp [epsScaleR]
  rw [this]
  exact Spec.map_id _

theorem isLieComb_mul (x y : epsR R ⟶ G) : IsLieComb ![(1 : R), 1] ![x, y] (x * y) :=
  ⟨![x, y], fun i => by fin_cases i <;> simp [spMap_epsScaleR_one], by simp⟩

theorem exists_char [IsCommMonObj G] {O : Type} [CommRing O] (act : OAct O G) {v : epsR R ⟶ G}
    (hv : IsLieBasis ![v]) :
    ∃ τ : O →+* R, (∀ c, IsLieComb ![τ c] ![v] (v ≫ act.act c)) ∧
      ∀ c r, IsLieComb ![r] ![v] (v ≫ act.act c) → τ c = r := by
  have ht : ∀ c, IsTangent (v ≫ act.act c) := fun c => by
    haveI := act.hom c
    exact isTangent_comp (hv.1 0) _
  have e1 : ∀ d : Fin 1 → R, d = ![d 0] := fun d => by
    funext i; fin_cases i; rfl
  choose d hd hu using fun c => hv.2 _ (ht c)
  have hτ : ∀ c, IsLieComb ![d c 0] ![v] (v ≫ act.act c) := fun c => by
    rw [← e1]; exact hd c
  have huq : ∀ c r, IsLieComb ![r] ![v] (v ≫ act.act c) → d c 0 = r := fun c r h => by
    rw [← hu c _ h]; rfl
  obtain ⟨-, -, hcomp, -, -⟩ := GlobalTheory.LieComb.lieComb_algebra R G 1 ![v] hv.1
  have hone : d 1 0 = 1 := huq _ _ (by
    rw [isLieComb_one_iff, act.one, spMap_epsScaleR_one]; simp)
  have hmul : ∀ a b, d (a * b) 0 = d a 0 * d b 0 := fun a b => huq _ _ (by
    have := hcomp 1 ![![d b 0]] ![v ≫ act.act b] ![d a 0] _
      (fun i => by fin_cases i; exact hτ b) (isLieComb_comp (hτ a) (act.act b))
    rw [act.mul, ← Category.assoc]
    convert this using 1
    funext i; fin_cases i; simp)
  have hadd : ∀ a b, d (a + b) 0 = d a 0 + d b 0 := fun a b => huq _ _ (by
    have := hcomp 2 ![![d a 0], ![d b 0]] ![v ≫ act.act a, v ≫ act.act b] ![1, 1] _
      (fun i => by
        fin_cases i
        · exact hτ a
        · exact hτ b) (isLieComb_mul _ _)
    rw [act.add, MonObj.comp_mul]
    convert this using 1
    funext i; fin_cases i; simp)
  exact ⟨RingHom.mk' ⟨⟨fun c => d c 0, hone⟩, hmul⟩ hadd, hτ, huq⟩

theorem ell_char : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (ω : R)
    (C : Ell H R ω), ∃ τ₀ : OK H →+* R, τ₀ (wK H) = ω ∧ ∀ c, IsLieComb ![τ₀ c] ![C.v] (C.v ≫ C.act.act c) := by
  intro E _ _ _ H R _ ω C
  obtain ⟨τ, h, hu⟩ := exists_char C.act C.basis
  exact ⟨τ, hu _ _ C.eig, h⟩

end GlobalTheory.CM.LieChar
end
