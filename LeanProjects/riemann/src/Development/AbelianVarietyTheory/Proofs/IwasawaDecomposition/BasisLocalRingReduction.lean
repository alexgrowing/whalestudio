import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinOfIsPull
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SectionPowerCalculusGeometricFibre
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LN GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorRef

section
variable {S : Scheme.{0}} {G : Over S} {L : LB G.left} {N : ℕ}

open GlobalTheory.FramePull in

theorem linA_at {T T' : Over S} {h : T' ⟶ T} {n : ℕ} {b : Fin n → LB.Sec (LPow G L (N : ℤ) T)}
    {c : Fin n → Γ(T'.left, ⊤)} {a : Γ(T'.left, ⊤)} {s : LB.Sec (LPow G L (N : ℤ) T')} (H : LinA G L N h b c a s)
    (W : Scheme.{0}) (r : W ⟶ (T' ⊗ G).left) (z : W) (J) (hJ : Good L z J) :
    gs (r ≫ (fst T' G).left) z ⊤ a * sv s r z J =
      ∑ i, gs (r ≫ (fst T' G).left) z ⊤ (c i) * sv (b i) (r ≫ (h ▷ G).left) z J := by
  have e := congrArg (r.stalkMap z).hom (H (r z) (fun ψ => J (r ≫ ψ)) (fun ψ => hJ (r ≫ ψ)))
  rw [map_sum, map_mul, ← gs_comp r _ z ⊤ trivial] at e
  have e₁ : sv s r z J = (r.stalkMap z).hom (sv s (𝟙 _) (r z) (fun ψ => J (r ≫ ψ))) :=
    (congrArg (fun q => sv s q z J) (Category.comp_id r).symm).trans (sval_comp _ r _ z hJ)
  rw [e₁]
  refine e.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [map_mul, ← gs_comp r _ z ⊤ trivial]
  exact congrArg _ (sval_comp _ r _ z hJ).symm

open GlobalTheory.FramePull in

theorem sv_zero {T : Over S} {W : Scheme.{0}} (r : W ⟶ (T ⊗ G).left) (z : W) {J} (hJ : Good L z J) :
    sv (N := N) (0 : LB.Sec (LPow G L (N : ℤ) T)) r z J = 0 := by
  show gs r z _ 0 = 0
  rw [gs_eq r z _ (hJ.mem _ r), map_zero, map_zero]

end

open GlobalTheory.FramePull in

theorem lin_residue_of_linA (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R]
    (t : SAB H (Sp R)) (N n : ℕ) (b : Fin n → LB.Sec (LPow t.G t.PP.L (N : ℤ) (Over.mk (𝟙 (Sp R)))))
    (W : Type) [CommRing W] [IsLocalRing W] (φ : R →+* W) (c : Fin n → W) (a : W)
    (s : LB.Sec (LPow t.G t.PP.L (N : ℤ) (Over.mk (spMap φ)))) (ha : a ∈ maximalIdeal W)
    (hl : LinA t.G t.PP.L N (toBase φ) b (fun i => GlobalTheory.OneBasis.fnR (c i)) (GlobalTheory.OneBasis.fnR a) s) :
    ∃ z : LB.Sec (LPow t.G t.PP.L (N : ℤ) (Over.mk (spMap ((residue W).comp φ)))),
      Lin t.G t.PP.L N (toBase ((residue W).comp φ)) b (fun i => GlobalTheory.OneBasis.fnR (residue W (c i))) z ∧
      Lin t.G t.PP.L N (toBase ((residue W).comp φ)) b (fun _ => 0) z := by
  have hres : residue W a = 0 := (residue_eq_zero_iff a).2 ha
  refine ⟨0, ?_, ?_⟩
  · rw [lin_iff]
    intro V r y J hJ
    have e := linA_at hl V (r ≫ (jC φ (residue W) ▷ t.G).left) y J hJ
    have hf : (r ≫ (jC φ (residue W) ▷ t.G).left) ≫ (fst (Over.mk (spMap φ)) t.G).left =
        (r ≫ (fst (Over.mk (spMap ((residue W).comp φ))) t.G).left) ≫ (jC φ (residue W)).left := by
      rw [Category.assoc, ← Over.comp_left, whiskerRight_fst, Over.comp_left, Category.assoc]
    have hb : (r ≫ (jC φ (residue W) ▷ t.G).left) ≫ (toBase φ ▷ t.G).left =
        r ≫ (toBase ((residue W).comp φ) ▷ t.G).left := by
      rw [Category.assoc, ← Over.comp_left, ← comp_whiskerRight, jC_toBase]
    have hg : ∀ x : W, gs ((r ≫ (jC φ (residue W) ▷ t.G).left) ≫ (fst (Over.mk (spMap φ)) t.G).left) y ⊤
        (GlobalTheory.OneBasis.fnR x) = gs (r ≫ (fst (Over.mk (spMap ((residue W).comp φ))) t.G).left) y ⊤
          (GlobalTheory.OneBasis.fnR (residue W x)) := fun x => by
      rw [hf, ← GlobalTheory.OneBasis.Calc.appTop_fnR (residue W) x]
      exact (gs_pull _ (jC φ (residue W)).left y ⊤ trivial _).symm
    rw [hg a, hres] at e
    simp only [hg, hb] at e
    rw [sv_zero r y hJ, ← e]
    have h0 : GlobalTheory.OneBasis.fnR (0 : ResidueField W) = 0 := map_zero _
    rw [h0, gs_eq _ y ⊤ trivial, map_zero, map_zero, MulZeroClass.zero_mul]
  · rw [lin_iff]
    intro V r y J hJ
    rw [sv_zero r y hJ]
    refine (Finset.sum_eq_zero fun i _ => ?_).symm
    rw [gs_eq _ y ⊤ trivial, map_zero, map_zero, MulZeroClass.zero_mul]

end GlobalTheory.TorRef
