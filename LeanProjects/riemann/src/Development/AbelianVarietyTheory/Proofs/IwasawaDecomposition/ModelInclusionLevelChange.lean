import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelDescentCoefficientField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNormalModelAboveFiniteCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientSubringDedekindCompatibleEmbed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.RaiseModel

theorem exists_model_above : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l : Level H) (B : BaseModel T l₀) (c : Coeff l) (R : Type) [CommRing R] (ω : R →+* c.F) (bR : RZ H (n * l₀.M) 1 →+* R), 0 < n → l₀.Dvd l → IsDedFrac ω → IsInc (RZ H (n * l₀.M) 1).subtype (c.F.val.toRingHom.comp ω) bR → ∃ (C : Model (Xo l) c ω) (k : KA l₀ →+* c.F) (r : (Xo l).XF c ⟶ (Xo l₀).X) (ν : SABMap C.oF.t (Xo l₀).univ.t r), r ≫ (Xo l₀).s = pullback.snd _ _ ≫ spMap k ∧ IsInc (KA l₀).val.toRingHom c.F.val.toRingHom k ∧ LevComp C.oF (Xo l₀).univ r ν ∧ Nonempty ((ofModel C).Above B.C bR r ν) := by
  intro L₁ L₂ L₃ E _ _ _ H D Xo n N T hN l₀ l B c R _ ω bR hn hdvd hω hbR
  obtain ⟨oF, ⟨m0⟩⟩ := GlobalTheory.obj_pull E H D l (KA l) (KA l) (baseKA l) (baseKA l) (RingHom.id _) (Xo l).X ((Xo l).XF c)
    (Xo l).s (pullback.fst _ _ ≫ (Xo l).s) (pullback.fst _ _) rfl rfl
    (by rw [LevelCover.spMap_id', Category.comp_id]) (Xo l).univ
  obtain ⟨k, r, ν, hr, hk, hlev, hfin, -, -⟩ :=
    GlobalTheory.LevelMapField.exists_levelMap L₁ L₂ L₃ E H D Xo hN l₀ l c oF m0 hdvd
  have hnormF : Geo.Tor.IsNormalScheme ((Xo l).XF c) := by
    have := (Xo l).smooth
    have : Smooth (Xo l).s := SmoothOfRelativeDimension.smooth D.dim _
    exact (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _
      (pullback.snd (Xo l).s (spMap (IntermediateField.inclusion c.le).toRingHom)) inferInstance).2.1
  have hS : 0 < n * l₀.M := Nat.mul_pos hn (lt_of_lt_of_le (by norm_num) l₀.three_le)
  have hB : IsDedFrac B.β := by
    have := GlobalTheory.BaseRing.isDedFrac_RZ E H l₀ (n * l₀.M) 0 hS (by simp [B.A_one])
    rw [B.A_one] at this
    exact this.2.2 _ B.β_inc
  have hcomp : ω.comp bR = k.comp B.β :=
    RingHom.ext fun x => Subtype.ext ((hbR x).trans ((B.β_inc x).symm.trans (hk _).symm))
  obtain ⟨C', ⟨A⟩⟩ := GlobalTheory.Models.Cpt.exists_above E H _ _ _ _ _ B.β ((Xo l).XF c) _ _ (pullback.snd _ _) oF.t ω B.C bR
    k r hr ν hB hω hcomp hnormF hfin
  let Y : Model (Xo l) c ω :=
    ⟨C'.X, C'.s, C'.normal, C'.proj, C'.flat, C'.jQ, C'.jQ_over, C'.jQ_open, C'.jQ_dense, C'.t, oF, m0, C'.m, C'.ab_gen⟩
  exact ⟨Y, k, r, ν, hr, hk, hlev, ⟨A⟩⟩

end GlobalTheory.RaiseModel
