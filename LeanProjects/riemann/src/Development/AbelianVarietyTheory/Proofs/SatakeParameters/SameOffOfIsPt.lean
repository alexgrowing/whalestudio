import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePtOne
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

namespace GlobalTheory.TwV.Xc

theorem sameOff_of_isPt (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n p : ℕ) (G : GAtP p) (A : LocAt F E n G) (J : Matrix (Fin n) (Fin n) E) :
    LocGood σ J A → ∀ (i : G.comp) (g g' : (∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v))) (x x' : UPts σ J (FiniteAdeleRing (𝓞 F) F)), A.IsPt i g x.1 → A.IsPt i g' x'.1 → ∀ v, (∀ v', v' ≠ v → g v' = g' v') → SameOff (A.pl v).1 x.1 x'.1 := by
  intro H i g g' x x' hx hx' v hg w hw
  by_cases hp : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal
  · obtain ⟨v', rfl⟩ := LocGood.exists_pl A w hp
    have hv : v' ≠ v := fun h => hw (h ▸ rfl)
    have h1 := hx.2 v'
    have h2 := hx'.2 v'
    rw [hg v' hv] at h1
    have hmem : bc (prV (E := E) (A.pl v').1) ((x.1)⁻¹ * x'.1) ∈ UPts σ J ((A.pl v').1.adicCompletion F) :=
      Formalism.UG.P.afsplit_bc_mem σ J (A.pl v').1 _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ x.2) x'.2)
    have h3 := H.eq_one_of_ph v' _ hmem (by rw [map_mul, map_mul, map_inv, map_inv, h1, h2]; exact inv_mul_cancel _)
    rw [map_mul, map_inv] at h3
    exact (inv_mul_eq_one.1 h3)
  · rw [hx.1 w hp, hx'.1 w hp]

end GlobalTheory.TwV.Xc
