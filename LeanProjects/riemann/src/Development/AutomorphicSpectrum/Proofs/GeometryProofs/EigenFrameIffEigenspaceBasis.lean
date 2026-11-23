import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeAt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenvectorLinearCombination
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.LieEigFrame

variable {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G] {x : Sp R ⟶ S} {Em : Type}
  [AddCommGroup Em] [Module R Em]

theorem isComb_pt_iff (M : LieModel G x Em) {n : ℕ} (b : Fin n → Em) (cf : Fin n → R) (w : epsAt x ⟶ G) :
    IsComb cf (fun i => M.pt (b i)) w ↔ w = M.pt (∑ i, cf i • b i) := by
  have hsum : M.pt (∑ i, cf i • b i) = (List.ofFn fun i => M.pt (cf i • b i)).prod :=
    GlobalTheory.CompanionTheory.Ar.CombEig.pt_sum M fun i => cf i • b i
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hue : u = fun i => M.pt (cf i • b i) :=
      funext fun i => Over.OverMorphism.ext (by rw [hu i, M.smul])
    rw [hsum, hue]
  · rintro rfl
    exact ⟨fun i => M.pt (cf i • b i), fun i => M.smul _ _, hsum⟩

theorem isEigVec_pt_iff {Oe : Type} [CommRing Oe] (M : LieModel G x Em) (act : OAct Oe G)
    {ρ : Oe →+* Module.End R Em} (τ : Oe →+* R) (hρ : M.IsActOf act.act ρ) (e : Em) :
    IsEigVec act x τ (M.pt e) ↔ e ∈ eigSp ρ τ := by
  have hmem : e ∈ eigSp ρ τ ↔ ∀ a, ρ a e = τ a • e := by
    simp [eigSp, Submodule.mem_iInf, sub_eq_zero]
  rw [hmem]
  constructor
  · intro h a
    exact M.inj (Over.OverMorphism.ext (by rw [hρ a e, M.smul]; exact h.2 a))
  · intro h
    exact ⟨M.tan e, fun a => by rw [← hρ a e, h a, M.smul]⟩

theorem isEigFrame_pt_iff : ∀ (S : Scheme.{0}) (R : Type) [CommRing R] (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Sp R ⟶ S) (Em : Type)
    [AddCommGroup Em] [Module R Em] (M : LieModel G x Em) (Oe : Type) [CommRing Oe] (act : OAct Oe G)
    (ρ : Oe →+* Module.End R Em) (τ : Oe →+* R) (n : ℕ) (b : Fin n → Em), M.IsActOf act.act ρ →
    (IsEigFrame act x τ (fun i => M.pt (b i)) ↔
      (∀ i, b i ∈ eigSp ρ τ) ∧ ∀ e ∈ eigSp ρ τ, ∃! cf : Fin n → R, e = ∑ i, cf i • b i) := by
  intro S R _ G _ _ x Em _ _ M Oe _ act ρ τ n b hρ
  have eig := isEigVec_pt_iff M act τ hρ
  have key := isComb_pt_iff M b
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => (eig _).1 (h1 i), fun e he => ?_⟩
    obtain ⟨c, hc, hu⟩ := h2 (M.pt e) ((eig e).2 he)
    exact ⟨c, M.inj ((key c _).1 hc), fun c' hc' => hu c' ((key c' _).2 (congrArg M.pt hc'))⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => (eig _).2 (h1 i), fun w hw => ?_⟩
    obtain ⟨e, rfl⟩ := M.onto w hw.1
    obtain ⟨c, hc, hu⟩ := h2 e ((eig e).1 hw)
    exact ⟨c, (key c _).2 (congrArg M.pt hc), fun c' hc' => hu c' (M.inj ((key c' _).1 hc'))⟩

end GlobalTheory.CompanionTheory.Ar.Flat.LieEigFrame
