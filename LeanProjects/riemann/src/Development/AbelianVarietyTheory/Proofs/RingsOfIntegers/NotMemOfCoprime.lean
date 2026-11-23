import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ShortValDesc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ShortPlaceB
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPins
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.EqZeroOfComplex
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CardFunLevQ
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LatticeTrivialAtPrimeIndicesAndUnits
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsIntegralZpowOfPowEqOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShortUnits

open GlobalTheory.LatticeIndex GlobalTheory.TrivLattice

section Val
variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))

theorem valuation_nat {k : ℕ} (hk : (k : 𝓞 K) ∉ la.asIdeal) : la.valuation K (k : K) = 1 := by
  rw [← map_natCast (algebraMap (𝓞 K) K)]
  exact la.valuation_eq_one_iff_notMem.2 hk

theorem not_mem_of_coprime' {a b : ℕ} (h : Nat.Coprime a b) (ha : (a : 𝓞 K) ∈ la.asIdeal) :
    (b : 𝓞 K) ∉ la.asIdeal := fun hb => by
  obtain ⟨u, v, e⟩ : IsCoprime (a : 𝓞 K) (b : 𝓞 K) := h.cast
  exact la.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (e ▸ la.asIdeal.add_mem (la.asIdeal.mul_mem_left _ ha) (la.asIdeal.mul_mem_left _ hb)))

end Val

theorem vLa_beta {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (c : Coeff l) {n : ℕ} (Λ : GenLat E n) (la : HeightOneSpectrum (𝓞 c.F)) (hA : PullbackSections.AdaptAt Λ la) (β : c.F)
    (hβ : BetaIs (Dw := Dw) c Λ β) : vLa la β = 0 := by
  obtain ⟨k, hk, hk1, hk2⟩ := hA
  have h1 : ∀ v ∈ Λ.La, k • v ∈ stdLat E n := fun v hv => nsmul_mem_of_le hk1 hv
  have h2 : ∀ v ∈ stdLat E n, k • v ∈ Λ.La := fun v hv => nsmul_mem_of_le hk2 hv
  let w := la.valuation c.F
  have hw : ∀ r : 𝓞 c.F, w (algebraMap (𝓞 c.F) c.F r) ≤ 1 := fun r => la.valuation_le_one r
  have hwτ : ∀ τ, ∀ r : 𝓞 E, w.comap (embF c τ) (algebraMap (𝓞 E) E r) ≤ 1 := fun τ r =>
    hw ⟨_, map_isIntegral_int (embF c τ) r.isIntegral_coe⟩
  have hnat : ∀ τ, w.comap (embF c τ) (k : E) = 1 := fun τ => by
    simp only [w, Valuation.comap_apply, map_natCast]
    exact valuation_nat la hk
  have hm : ∀ (A : Submodule (𝓞 E) (Fin n → E)), (∀ v ∈ A, k • v ∈ stdLat E n) → (∀ v ∈ stdLat E n, k • v ∈ A) →
      HasMax w (∏ τ : E →+* ℂ, idealAt c A τ ^ Dw.mult τ) 1 := fun A a1 a2 => by
    have := hasMax_prod hw Finset.univ (fun τ => idealAt c A τ ^ Dw.mult τ) (fun _ => 1) fun τ => by
      obtain ⟨a, y, hy, b⟩ := detSet_max _ (hwτ τ) A (hnat τ) a1 a2
      have h : HasMax w (idealAt c A τ) 1 := by
        refine hasMax_span hw ?_ ⟨_, ⟨_, hy, rfl⟩, b⟩
        rintro _ ⟨y, hy, rfl⟩
        exact a y hy
      simpa using h.pow hw (Dw.mult τ)
    simpa using this
  have hb : HasMax w (Submodule.span (𝓞 c.F) {β}) (w β) := hasMax_span hw (by simp) (by simp)
  have f1 := hb.mul (hm Λ.La h1 h2)
  rw [hβ] at f1
  have f := f1.unique (hm Λ.Ln (fun v hv => h1 v hv.1)
    (fun v hv => ⟨h2 v hv, (stdLat E n).toAddSubgroup.nsmul_mem hv k⟩))
  rw [_root_.mul_one] at f
  have f' : la.valuation c.F β = 1 := f
  simp [vLa, f']

theorem vLa_betaH {D : D7} (T : Full D) (hF : LawsFull T) (j : ℕ) (hj : InR D j) {n : ℕ} (Λ : GenLat D.host.E n)
    (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (hU : Λ.Unimod) (hT : Λ.TrivAt (badN D)) (hA : PullbackSections.AdaptAt Λ la) :
    vLa la (betaH (Dw := T.Q.Dw j) T.Q.c Λ) = 0 := by
  have h := hF.sh.beta j hj n (hF.p.kPsi j hj) Λ hU hT
  refine vLa_beta (Dw := T.Q.Dw j) T.Q.c Λ la hA _ ?_
  unfold betaH
  rw [dif_pos h]
  exact h.choose_spec.2.1

end GlobalTheory.ShortUnits
