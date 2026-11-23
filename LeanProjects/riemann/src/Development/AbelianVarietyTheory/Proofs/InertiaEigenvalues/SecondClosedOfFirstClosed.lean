import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BlockHodgeTateJumps
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BlockJumpCount

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.BlockJumpsCompare

section Continuity

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
  [IsTopologicalRing O] {X : Type} [TopologicalSpace X]

theorem continuous_of_mul (had : IsAdic (IsLocalRing.maximalIdeal O)) {d : O} (hd : d ≠ 0) {f : X → O}
    (h : Continuous fun x => d * f x) : Continuous f := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hp
  have hm : ∀ (n : ℕ) (y : O), y ∈ (IsLocalRing.maximalIdeal O) ^ n ↔ p ^ n ∣ y := by
    intro n y
    rw [hp.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  rw [continuous_iff_continuousAt]
  intro x₀
  have h0 : Filter.Tendsto (fun x => (u : O) * p ^ k * (f x - f x₀)) (nhds x₀) (nhds 0) := by
    have := (h.sub (continuous_const (y := (u : O) * p ^ k * f x₀))).tendsto x₀
    simpa [mul_sub, Pi.sub_def] using this
  have h1 : Filter.Tendsto (fun x => f x - f x₀) (nhds x₀) (nhds 0) := by
    rw [had.hasBasis_nhds_zero.tendsto_right_iff] at h0 ⊢
    intro n _
    filter_upwards [h0 (k + n) trivial] with x hx
    have hx' := (hm _ _).1 hx
    refine (hm _ _).2 ?_
    rw [pow_add, mul_assoc, Units.dvd_mul_left] at hx'
    exact (mul_dvd_mul_iff_left (pow_ne_zero k hp.ne_zero)).1 hx'
  simpa [ContinuousAt] using h1.add_const (f x₀)

theorem continuous_of_comb (had : IsAdic (IsLocalRing.maximalIdeal O)) {ι : Type} [Fintype ι]
    (c : ι → FractionRing O) {h : ι → X → O} (hh : ∀ j, Continuous (h j)) {f : X → O}
    (hf : ∀ x, algebraMap O (FractionRing O) (f x) =
      ∑ j, c j * algebraMap O (FractionRing O) (h j x)) : Continuous f := by
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) c
  choose a ha using hd
  refine continuous_of_mul had (nonZeroDivisors.ne_zero d.2) ?_
  have : (fun x => (d : O) * f x) = fun x => ∑ j, a j * h j x := by
    funext x
    apply IsFractionRing.injective O (FractionRing O)
    simp only [map_mul, map_sum, hf, ha, Finset.mul_sum, Algebra.smul_def, mul_assoc]
  rw [this]
  exact continuous_finset_sum _ fun j _ => continuous_const.mul (hh j)

theorem continuous_of_splitsAs (had : IsAdic (IsLocalRing.maximalIdeal O)) {Γ : Type} [Group Γ]
    [TopologicalSpace Γ] {n r t : ℕ} {M : Γ →* Matrix (Fin n) (Fin n) O}
    {P : Γ →* Matrix (Fin r) (Fin r) O} {χ : Fin t → Γ → FractionRing O}
    (hs : GlobalTheory.IndefiniteRowSideFullHecke.BlockHodgeTateJumps.SplitsAs (mapM (algebraMap O (FractionRing O)) M)
      (mapM (algebraMap O (FractionRing O)) P) χ)
    (hM : Continuous fun g => M g) : Continuous fun g => P g := by
  obtain ⟨e, he⟩ := hs
  refine continuous_matrix fun a b => ?_
  set u : Fin n → FractionRing O := e.symm (Pi.single b 1, 0) with hu
  refine continuous_of_comb had
    (fun jk : Fin n × Fin n => (e (Pi.single jk.1 1)).1 a * u jk.2)
    (h := fun jk g => M g jk.1 jk.2) (fun jk => hM.matrix_elem jk.1 jk.2) fun g => ?_
  have h1 := congrFun (congrArg Prod.fst (he g u)) a
  have h2 : ∀ v : Fin n → FractionRing O, (e v).1 a = ∑ j, (e (Pi.single j 1)).1 a * v j := by
    intro v
    conv_lhs => rw [pi_eq_sum_univ' v]
    simp [map_sum, Prod.fst_sum, Finset.sum_apply, mul_comm]
  rw [h2] at h1
  simp only [hu, LinearEquiv.apply_symm_apply, Matrix.mulVec_single_one] at h1
  rw [← hu] at h1
  rw [Fintype.sum_prod_type]
  refine Eq.trans ?_ (h1.symm.trans ?_)
  · rfl
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    change _ * (algebraMap O (FractionRing O) (M g j k) * u k) = _
    ring

end Continuity

section Glob

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc)
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i)))

theorem blockSum_iff (π : N.X i) :
    GlobalTheory.IndefiniteRowSideFullHecke.BlockJumpCount.IsBlockSum N i r ρ π ↔ GlobalTheory.IndefiniteRowSideFullHecke.BlockHodgeTateJumps.BlockSplit N i r ρ π := Iff.rfl

theorem continuous_rho (π : N.X i) (hr : IsHeckeGalois N i π (r π))
    (hs : GlobalTheory.IndefiniteRowSideFullHecke.BlockJumpCount.IsBlockSum N i r ρ π) :
    Continuous (fun g => ((ρ π g : GL (Fin R.r) (N.O i)) : Matrix (Fin R.r) (Fin R.r) (N.O i))) :=
  continuous_of_splitsAs (M := rO N i r π) (P := rhoO N i ρ π) (N.O_adic i)
    ((blockSum_iff N i r ρ π).1 hs) hr.1

def HasGalois : Prop := ∃ r₀ : N.X i → (GE N →* GL (Fin R.nV) (N.O i)), GoodR N i r₀

end Glob

def FirstAt (D : D7) (i : D.nd.Loc) : Prop :=
  ∀ (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i),
    π ∈ D.nd.Z i → IsHeckeGalois D.nd i π (r π) → GlobalTheory.IndefiniteRowSideFullHecke.BlockJumpCount.IsBlockSum D.nd i r ρ π →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw),
      ∃ J : Multiset ℤ,
        GlobalTheory.IndefiniteRowSideFullHecke.BlockJumpCount.IsJumpMultiset (Br.PD D.loc D.nbr i w hw)
          (matRep (Br.loc D.nbr i w hw (WpO D.nd i ρ π))) τ J ∧
        GlobalTheory.IndefiniteRowSideFullHecke.BlockJumpCount.IsJumpMultiset (Br.PD D.loc D.nbr i w hw)
          (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r π))) τ (J + GlobalTheory.IndefiniteRowSideFullHecke.BlockJumpCount.blockJumps D.R.t)

end GlobalTheory.BlockJumpsCompare

end
