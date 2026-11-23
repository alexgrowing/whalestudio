import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsProperIffOfSplit
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH.AbelianPart

theorem isProper_snd_iff {Z A B T : Scheme.{0}} (e : A ≅ B) (f : A ⟶ Z) (g : B ⟶ Z) (h : e.hom ≫ g = f)
    (t : T ⟶ Z) : IsProper (pullback.snd f t) ↔ IsProper (pullback.snd g t) := by
  subst h
  have P : IsPullback (pullback.fst g t ≫ e.inv) (pullback.snd g t) (e.hom ≫ g) t :=
    IsPullback.of_iso (IsPullback.of_hasPullback g t) (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)
  constructor
  · intro h
    rw [← P.isoPullback_hom_snd]
    infer_instance
  · intro h
    rw [← P.isoPullback_inv_snd]
    infer_instance

theorem abLocus_congr {Z : Scheme.{0}} (A B : Over Z) (e : A.left ≅ B.left) (h : e.hom ≫ B.hom = A.hom) :
    abLocus A = abLocus B := by
  ext z
  exact ⟨fun H K _ _ t ht => (isProper_snd_iff e _ _ h t).1 (H K t ht),
    fun H K _ _ t ht => (isProper_snd_iff e _ _ h t).2 (H K t ht)⟩

theorem isProper_snd_of_le {Z A : Scheme.{0}} (f : A ⟶ Z) {U V : Z.Opens} (h : U ≤ V)
    [IsProper (pullback.snd f V.ι)] : IsProper (pullback.snd f U.ι) := by
  have P := (IsPullback.of_hasPullback (pullback.snd f V.ι) (Z.homOfLE h)).paste_horiz
    (IsPullback.of_hasPullback f V.ι)
  rw [Scheme.homOfLE_ι] at P
  rw [← P.isoPullback_inv_snd]
  infer_instance

theorem not_mem_abLocus (C : GlobalTheory.ZJ.Core) (L : C.Law) {p : ℕ} [Fact p.Prime] (y : Sp (GlobalTheory.ZJ.OO p) ⟶ C.Z)
    (τ : C.Test y) (h : ¬ IsProper (pullback.snd τ.H.hom (GlobalTheory.ZJ.rPt p ≫ spMap τ.j))) :
    y (GlobalTheory.ZJ.cPt p) ∉ abLocus C.GG := by
  intro hm
  obtain ⟨hsep, hlft, -⟩ := GlobalTheory.ZJ.core_basic C
  have hc : IsPullback τ.f τ.H.hom C.GG.hom τ.y₀ := (L.test p y τ).1
  have P := (IsPullback.of_hasPullback τ.H.hom (GlobalTheory.ZJ.rPt p ≫ spMap τ.j)).paste_horiz hc
  rw [Category.assoc, τ.fac] at P
  refine h ((GlobalTheory.ZJ.AbelianLocus.mem_abLocus_iff C.GG P (IsLocalRing.closedPoint (GlobalTheory.ZJ.kb p))).1 ?_)
  have e : GlobalTheory.ZJ.rPt p (IsLocalRing.closedPoint (GlobalTheory.ZJ.kb p)) = GlobalTheory.ZJ.cPt p :=
    IsLocalRing.comap_closedPoint (IsLocalRing.residue (GlobalTheory.ZJ.OO p))
  rw [← e] at hm
  exact hm

theorem ab : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Q : Clos ρ M U₀ EE) (ex : Q.Ext) (Z : ZHPre ρ M U₀), (∃ e : Z.G.left ≅ Q.G.toScheme, e.hom ≫ Q.G.ι ≫ Q.P.hom = Z.G.hom ∧ Z.u₀ = Q.u₀ ∧ HEq (Z.φ ≫ e.hom) ex.a) → Nonempty ex.core.Law → ex.core.HasTests → ex.core.HasCharts → IsOpen {z : M.Z | S.TT M z = ⊥} → (∀ w : Q.P.left, IsClosed ({w} : Set Q.P.left) → S.TT M (Q.P.hom w) = ⊥ → w ∈ Q.G) → (∀ z : M.Z, IsClosed ({z} : Set M.Z) → S.TT M z ≠ ⊥ → ∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (GlobalTheory.ZJ.OO p) ⟶ ex.core.Z) (τ : ex.core.Test y), y (GlobalTheory.ZJ.cPt p) = z ∧ ¬ IsProper (pullback.snd τ.H.hom (GlobalTheory.ZJ.rPt p ≫ spMap τ.j))) → Z.Ab := by
  rintro o Ω _ _ _ _ S ρ M U₀ EE Q ex Z ⟨e, he, -⟩ ⟨L⟩ hT hC hO h₁ h₂
  obtain ⟨hab, hpr⟩ := GlobalTheory.ZJ.AbelianLocus.abLocus_eq ex.core L hT hC ⟨_, hO⟩ h₁ (fun z hz hn => by
    obtain ⟨p, _, y, τ, rfl, h⟩ := h₂ z hz hn
    exact not_mem_abLocus ex.core L y τ h)
  have hE : abLocus Z.G = {z | S.TT M z = ⊥} := (abLocus_congr Z.G ex.core.GG e he).trans hab
  refine ⟨hE, fun W hW => ?_⟩
  rw [hE] at hW
  exact (isProper_snd_iff e _ _ he W.ι).2
    (@isProper_snd_of_le _ _ ex.core.GG.hom W ⟨_, hO⟩ hW hpr)

end GlobalTheory.ZH.AbelianPart
