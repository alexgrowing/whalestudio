import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePtOne
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ColSpanMap

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

noncomputable section

namespace GlobalTheory.TwV.Xc

theorem isPt_move_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n p : ℕ) (G : GAtP p) (A : LocAt F E n G) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E σ J T f bad), LocGood σ J A → LocInt A → LocHyp S A → A.ActB → (∀ w ∈ bad, ((p : ℕ) : 𝓞 F) ∉ w.asIdeal) → ∀ (i : G.comp) (γ : (G.lev i).Γ), A.gamI i γ ∈ UJ (σ : E →+* E) J → ∀ κa : S.U, A.IsAway i γ κa.1 → ∀ (g g' : (∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v))), (∀ v, colSpan (G.P.W v) (g' v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) = colSpan (G.P.W v) (((G.lev i).act v γ * g v : GL (Fin (G.P.m + 1)) (G.P.Qq v)) : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) → ∀ x x' : UPts σ J (FiniteAdeleRing (𝓞 F) F), A.IsPt i g x.1 → A.IsPt i g' x'.1 → ∃ κ : S.U, x'.1 = GlobalTheory.TwU.ratA F (A.gamI i γ) * x.1 * κ.1 ∧ S.chi κ * S.chi κa = 1 := by
  intro F E _ _ _ _ _ σ n p G A J T f bad S hG hW hH hA hbad i γ hγ κa hκa g g' hg x x' hx hx'
  have hy := A.isPt_smul hA i g x.1 κa.1 hx γ hκa
  have hyU : GlobalTheory.TwU.ratA F (A.gamI i γ) * x.1 * κa.1⁻¹ ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (ratInU _ hγ) x.2) (Subgroup.inv_mem _ ((S.U_eq κa.1).1 κa.2).1)
  obtain ⟨κ₁, e₁, hχ₁⟩ := ptOne_of (A := A) S hW hH hbad i (fun v => colSpan (G.P.W v)
      (((G.lev i).act v γ * g v : GL (Fin (G.P.m + 1)) (G.P.Qq v)) : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)))
    (fun v => (G.lev i).act v γ * g v) g' ⟨_, hyU⟩ x' (fun v => rfl) (fun v => (hg v).symm) hy hx'
  refine ⟨κa⁻¹ * κ₁, ?_, ?_⟩
  · rw [e₁]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc]
  · rw [map_mul, map_inv]
    apply Units.ext
    simp [hχ₁]

end GlobalTheory.TwV.Xc

end
