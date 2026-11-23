import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormAdelicFunctionsIndependentGoodEmbedding

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.ConjRelation

theorem relation_conj {K C X : Type} [Field K] [AddCommGroup C] [Module K C] (σ : K →+* ℂ) (Φ : C →ₛₗ[σ] (X → ℂ))
    (hΦ : ∀ (m : ℕ) (b : Fin m → C), LinearIndependent K b → LinearIndependent ℂ fun k => Φ (b k))
    (τ : ℂ ≃+* ℂ) (hτ : ∀ x, τ (σ x) = σ x) {n : ℕ} (a : Fin n → ℂ) (f : Fin n → C)
    (h : ∀ g, (0 : ℂ) = ∑ k, a k * Φ (f k) g) (g : X) : (0 : ℂ) = ∑ k, τ (a k) * Φ (f k) g := by
  let S := Submodule.span K (Set.range f)
  haveI : FiniteDimensional K S := FiniteDimensional.span_of_finite K (Set.finite_range f)
  let b := Module.finBasis K S
  have hb := hΦ _ (fun l => (b l : C)) (b.linearIndependent.map' S.subtype (Submodule.ker_subtype _))
  let c : Fin n → Fin (Module.finrank K S) → K := fun k l => b.repr ⟨f k, Submodule.subset_span ⟨k, rfl⟩⟩ l
  have hf : ∀ k, f k = ∑ l, c k l • (b l : C) := fun k => by
    have h1 := congrArg S.subtype (b.sum_repr ⟨f k, Submodule.subset_span ⟨k, rfl⟩⟩)
    rw [map_sum] at h1
    exact h1.symm
  have key : ∀ (a' : Fin n → ℂ) (x : X), ∑ k, a' k * Φ (f k) x = ∑ l, (∑ k, a' k * σ (c k l)) * Φ (b l) x := by
    intro a' x
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hf k, map_sum, Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smulₛₗ, Pi.smul_apply, smul_eq_mul, mul_assoc]
  have h0 : ∀ l, ∑ k, a k * σ (c k l) = 0 := by
    refine Fintype.linearIndependent_iff.1 hb _ ?_
    funext x
    rw [Finset.sum_apply]
    exact ((h x).trans (key a x)).symm
  rw [key]
  refine (Finset.sum_eq_zero fun l _ => ?_).symm
  have h1 := congrArg τ (h0 l)
  simp only [map_sum, map_mul, hτ, map_zero] at h1
  rw [h1, zero_mul]

theorem exists_semilinear {D : D7} (T : CoreJ D) {j : ℕ} {σ : T.Q.c.F →+* ℂ} {W : HSp D} (hV : T.V j σ = W)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) :
    ∃ Φ : T.R j →ₛₗ[σ] (GA D W → ℂ), (∀ f, Φ f = phiC T hV a f) ∧ ∀ f g, Φ f g =
      ((lieFac (T.Q.Dw j) (xiR D) a : ℝ) : ℂ) * adel W (castDict hV (T.dict j σ))
        (muPin W (castDict hV (T.dict j σ)) (castDict hV (T.mu j σ)) (T.cE j σ)) (rdU (T.U j σ) f) g := by
  subst hV
  exact ⟨(((lieFac (T.Q.Dw j) (xiR D) a : ℝ) : ℂ) • adel (T.V j σ) (T.dict j σ)
    (muPin (T.V j σ) (T.dict j σ) (T.mu j σ) (T.cE j σ))).comp (rdU (T.U j σ)), fun _ => rfl, fun _ _ => rfl⟩

set_option maxHeartbeats 1000000 in

theorem expands_zero_conj : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ τ : ℂ ≃+* ℂ, (∀ a : T.Q.c.F, τ (a : ℂ) = (a : ℂ)) → ∀ (n : ℕ) (a : Fin n → ℂ) (f : Fin n → T.toCore.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n), Expands M (κ i) (fun _ => 0) a f → Expands M (κ i) (fun _ => 0) (fun k => τ (a k)) f := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ _ hfw i Tp tup M _ τ hτ n a f h
  obtain ⟨fw⟩ := hfw
  have hσ : GoodEmb T.Q.c M.s0 := T.toCore.good_σ₀
  have hex := exists_semilinear T M.hV (wtA (κ i))
  obtain ⟨Φ, h1, h2⟩ := hex
  have hI := GlobalTheory.PhiIndep.phiC_indep D T κ fw.laws i M.s0 hσ M.hV
  intro g
  have hr := relation_conj M.s0 (Φ.comp (T.toCore.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n).subtype)
    (fun m b hb => (funext fun k => h1 (b k : T.R ((i : ℕ) + 1))).symm ▸ hI m b hb) τ hτ a f
    (fun x => (h x).trans (Finset.sum_congr rfl fun k _ => congrArg (a k * ·) (h2 _ x).symm)) g
  exact hr.trans (Finset.sum_congr rfl fun k _ => congrArg (τ (a k) * ·) (h2 _ g))

end GlobalTheory.ConjRelation
