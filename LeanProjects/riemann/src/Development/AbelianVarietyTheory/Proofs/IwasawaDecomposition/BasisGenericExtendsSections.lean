import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinOfIsPull
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DegenerationDataCoordsNeZeroLatticesIsomorphic
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidifiedPolarisedFibreAtFieldPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaBasisAfterEveryFieldExtension
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenOfFrames
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LN GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorRef.SpanPos

theorem exists_lin_of_injective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R] (t : SAB H (Sp R)) (_ : PELUnif (maximalIdeal R) t) (N n : ℕ)
    (b : Fin n → LB.Sec (LPow t.G t.PP.L (N : ℤ) (Over.mk (𝟙 (Sp R))))), 1 ≤ N →
    BasisAlong t.G t.PP.L N (toBase (algebraMap R (FractionRing R))) b →
    ∀ (F : Type) [Field F] (ψ : R →+* F), Function.Injective ψ →
    ∀ s : LB.Sec (LPow t.G t.PP.L (N : ℤ) (Over.mk (spMap ψ))), ∃ c, Lin t.G t.PP.L N (toBase ψ) b c s := by
  intro E _ _ _ H R _ _ _ t U N n b hN hb F _ ψ hψ
  obtain ⟨L1, L2, -⟩ := GlobalTheory.allSixLaws
  have hP := GlobalTheory.DatUniq.polAt_of_unif U
  obtain ⟨A, φ, w, ρ, hR⟩ := GlobalTheory.OneBasis.exists_rigPull_of_polAt L1 L2 E H (Sp R) t (FractionRing R) (jK R) hP
  obtain ⟨r, τ, hτ⟩ := GlobalTheory.OneBasis.AllExt.exists_allBasis L1 L2 (Sp R) t.G t.PP.L t.PP.isLB (FractionRing R) (jK R)
    A φ w hR.1 hR.2.1 N hN
  obtain ⟨M, hM⟩ := GlobalTheory.FrameGen.exists_rel t.PP.isLB hb (𝟙 (Over.mk (jK R))) τ
  obtain ⟨ψ', rfl⟩ : ∃ ψ' : FractionRing R →+* F, ψ'.comp (algebraMap R (FractionRing R)) = ψ :=
    ⟨IsFractionRing.lift hψ, RingHom.ext (IsFractionRing.lift_algebraMap hψ)⟩
  let g := jC (algebraMap R (FractionRing R)) ψ'
  have hM' := hM.pull g
  rw [Category.comp_id, jC_toBase] at hM'
  have hB : BasisAlong t.G t.PP.L N g τ := hτ F ψ' _ (jC (algebraMap R (FractionRing R)) ψ').w
  intro s
  obtain ⟨a, ha⟩ := (hB s).exists
  refine ⟨fun i => ∑ k, a k * M.map g.left.appTop.hom k i, ?_⟩
  intro z J hJ
  have e₁ := GlobalTheory.FrameGen.lin_all t.PP.isLB ha (𝟙 _) z hJ
  simp only [GlobalTheory.FrameGen.sv, Category.id_comp] at e₁
  rw [e₁]
  have e₂ : ∀ k, sval (L := t.PP.L) (φ := fun _ : Fin 1 => (snd (Over.mk (jK R)) t.G).left) (ε := fun _ => (N : ℤ))
      (τ k) (g ▷ t.G).left z J = ∑ i, GlobalTheory.FrameGen.gT (fst _ t.G).left z (M.map g.left.appTop.hom k i) *
        sval (L := t.PP.L) (φ := fun _ : Fin 1 => (snd (Over.mk (𝟙 (Sp R))) t.G).left) (ε := fun _ => (N : ℤ))
          (b i) (toBase (ψ'.comp (algebraMap R (FractionRing R))) ▷ t.G).left z J := by
    intro k
    have := hM' k _ (𝟙 _) z J hJ
    simp only [GlobalTheory.FrameGen.sv, Category.id_comp] at this
    exact this
  simp only [e₂, Finset.mul_sum, GlobalTheory.FrameGen.gs_top, map_sum, map_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

end GlobalTheory.TorRef.SpanPos
