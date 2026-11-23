import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SvalEqSumOfHasVal
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsChartLoc

noncomputable section
namespace GlobalTheory.ArcPts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace SecTransport

variable {X Z : Scheme.{0}}

abbrev valH {L : LB X} {m : ℕ} (σ : Out.H0 L m) {R : Type} [CommRing R] (x : Sp R ⟶ X) (i : L.ι) : R :=
  valR x (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i)) (σ.f (fun _ => i))

theorem exists_pull {L L' : LB X} (h : L = L') (hL : L'.IsLB) {m : ℕ} (σ : Out.H0 L m) (π : Z ⟶ X) :
    ∃ s : SecP L' π m,
      (∀ (R : Type) [CommRing R] (p : Sp R ⟶ Z) (x : Sp R ⟶ X) (i : L.ι) (i' : L'.ι), p ≫ π = x → HEq i i' →
        ⊤ ≤ x ⁻¹ᵁ L'.U i' → ArcPts.sval s p i' = valH σ x i) ∧
      ∀ (A K : Type) [CommRing A] [IsLocalRing A] [Field K] (ρ : A →+* K) (x : Sp A ⟶ X) (p : Sp K ⟶ Z)
        (τ : L.ι → A) (τ' : L'.ι → K) (f : K), p ≫ π = spMap ρ ≫ x → IsFrm L' (p ≫ π) τ' →
        (∀ i i', HEq i i' → ⊤ ≤ x ⁻¹ᵁ L.U i → τ' i' = ρ (τ i)) →
        (∀ i, ⊤ ≤ x ⁻¹ᵁ L.U i → ρ (valH σ x i) = f * ρ (τ i) ^ m) → HasVal s p τ' f := by
  subst h
  have ex : ∀ π' : Z ⟶ X, π' = π ≫ 𝟙 X → ∃ s : SecP L π' m, ∀ (R : Type) [CommRing R] (p : Sp R ⟶ Z) (x : Sp R ⟶ X)
      (i : L.ι), p ≫ π = x → ⊤ ≤ x ⁻¹ᵁ L.U i → ArcPts.sval s p i = valH σ x i := by
    rintro _ rfl
    refine ⟨DVR.pullSec L (fun _ : Fin 1 => 𝟙 X) (fun _ => (m : ℤ)) σ π, fun R _ p x i hx hi => ?_⟩
    subst hx
    exact (HolHom.valR_res p _ _ (GenericPoints.le_wchart hi)).trans (HolHom.valR_comp p π _ _).symm
  obtain ⟨s, hs⟩ := ex π (Category.comp_id _).symm
  refine ⟨s, fun R _ p x i i' hx hi hi' => ?_, fun A K _ _ _ ρ x p τ τ' f hp hτ h₁ h₂ => ?_⟩
  · obtain rfl := eq_of_heq hi
    exact hs R p x i hx hi'
  · obtain ⟨i, hi⟩ := GenericPoints.exists_chart_loc hL x
    have hi' := FormalValue.top_le_comp hi (spMap ρ)
    refine GenericPoints.hasVal_of_chart s p hτ (j := i) (hp ▸ hi') ?_
    rw [hs K p _ i hp hi', h₁ i i HEq.rfl hi, ← h₂ i hi]
    exact HolHom.valR_spMap ρ x (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i))
      (fun _ hz => Set.mem_iInter.2 fun _ => hi hz) _

end SecTransport

theorem secVal_eq_mul_sval_sig : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (Ξ : ConstPts W Λ) (Φ : GenPts Λ.A W.t gen) (j : ℕ) [NeZero j] (α : Λ.A.X) (th : (Fin Λ.A.gB → ℂ) → ℂ) (r : ℂ⸨X⸩) (σ : Out.H0 W.P.U.LG.L j), Ξ.IsGen Φ → th ∈ Λ.A.Theta j α → Ξ.Vals σ (fun v => r * Λ.A.FSum j α th v) → ∀ (q : Over.mk gen ⟶ W.t.G) (jL : W.P.U.LG.L.ι) (i : W.t.PP.L.ι), HEq jL i → ⊤ ≤ q.left ⁻¹ᵁ W.t.PP.L.U i → FormalValue.secVal (S := ℂ⸨X⸩) W.P.U.toUnifPre σ q.left jL = r * sval (Φ.sig j α th) (fib q) i := by
  intro _ _ E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ Ξ Φ j _ α th r σ hgen hth hval q jL i hi hq
  obtain ⟨s, hs₁, hs₂⟩ := SecTransport.exists_pull (congrArg RigLB.L W.P.bundle) W.t.PP.isLB σ
    (pullback.fst W.t.G.hom gen)
  have hfib : ∀ p : Over.mk gen ⟶ W.t.G, fib p ≫ pullback.fst W.t.G.hom gen = p.left := fun p =>
    pullback.lift_fst _ _ _
  have hv : ∀ v, HasVal s (fib (Φ.x v)) (Φ.τ v) (r * Λ.A.FSum j α th v) := fun v =>
    hs₂ ℂ⟦X⟧ ℂ⸨X⸩ (algebraMap _ _) (Ξ.x v).left (fib (Φ.x v)) (Ξ.τ v) (Φ.τ v) _ ((hfib _).trans (hgen v).1)
      (by rw [hfib]; exact Φ.frm v) (hgen v).2 (hval v)
  have hq₂ : fib q ≫ pullback.snd W.t.G.hom gen = spMap (RingHom.id _) := by
    rw [fib, pullback.lift_snd]
    exact (Spec.map_id _).symm
  have key := sval_eq_sum_of_hasVal E H _ Λ.A W.t gen Φ j s 1 (fun _ => r) (fun _ => α) (fun _ => th) (fun _ => hth)
    (fun v => by rw [Fin.sum_univ_one]; exact hv v) ℂ⸨X⸩ (RingHom.id _) (fib q) hq₂ i (by rw [hfib]; exact hq)
  rw [Fin.sum_univ_one] at key
  exact (hs₁ _ (fib q) q.left jL i (hfib q) hi hq).symm.trans key

end GlobalTheory.ArcPts
