import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.VecCoord
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.IsDelNeZeroCoprimeDenominatorsDifferentGenerator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeOneOfIsIntegralInt
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

namespace UpperTheory.Gal.W2.Seed.IntRev

private theorem mem_range_map {R : Type} [CommRing R] (S : Subring R) {m : ℕ} (x : GL (Fin m) R)
    (h1 : ∀ i j, x.1 i j ∈ S) (h2 : ∀ i j, (x⁻¹).1 i j ∈ S) : x ∈ (GeneralLinearGroup.map S.subtype).range := by
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, ?_, ?_⟩, rfl⟩
  · refine Matrix.map_injective S.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.mul_inv
  · refine Matrix.map_injective S.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.inv_mul

variable {E : Type} [Field E] [NumberField E] {p : ℕ} [Fact p.Prime]

private theorem norm_le (τ : E →+* PadicAlgCl p) (x : E)
    (h : ∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → w.valuation E x ≤ 1) : ‖τ x‖ ≤ 1 := by
  have hp : p.Prime := Fact.out
  obtain ⟨N, -, hNc, hN⟩ := GlobalTheory.HilbertThetaSeries.DenP.exists_away hp x
  have hint : IsIntegral ℤ ((N : E) * x) := by
    refine (GlobalTheory.HilbertThetaSeries.DenP.isIntegral_iff_val _).2 fun w => ?_
    by_cases hw : ((p : ℕ) : 𝓞 E) ∈ w.asIdeal
    · rw [map_mul, GlobalTheory.HilbertThetaSeries.DenP.val_coprime hNc hw, one_mul]; exact h w hw
    · exact hN w hw
  have h1 : ‖τ ((N : E) * x)‖ ≤ 1 := GlobalTheory.CongW.PlaceEmb.norm_int_le τ ⟨_, hint⟩
  have h3 : ‖(N : ℚ_[p])‖ = 1 := (Padic.norm_natCast_eq_one_iff).2 hNc.symm
  have h2 : ‖(N : PadicAlgCl p)‖ = 1 := by
    rw [← h3, ← PadicAlgCl.norm_extends p, map_natCast]
  rwa [map_mul, map_natCast, norm_mul, h2, one_mul] at h1

variable [IsCMField E] {n : ℕ}

private theorem entry_le (y : Gam0 E n) (hy : ∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w (rat y) ∈ GlobalTheory.LFun.KGL w n)
    (τ : E →+* PadicAlgCl p) (i j : Fin n) : ‖τ (y.1.1.val i j)‖ ≤ 1 := by
  refine norm_le τ _ fun w hw => ?_
  have h1 : (comp w (rat y)).val i j ∈ w.adicCompletionIntegers E := (GlobalTheory.AdelicU.mem_GLint_iff.1 (hy w hw)).1 i j
  have h2 : (comp w (rat y)).val i j = ((y.1.1.val i j : E) : w.adicCompletion E) := rfl
  rw [h2, HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h1
  exact h1

private theorem hyp_inv (y : Gam0 E n) (hy : ∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w (rat y) ∈ GlobalTheory.LFun.KGL w n) :
    ∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w (rat y⁻¹) ∈ GlobalTheory.LFun.KGL w n := fun w hw => by
  rw [map_inv, map_inv]; exact inv_mem (hy w hw)

private theorem mult_le (hn : 0 < n) (τ : E →+* PadicAlgCl p) (y : Gam0 E n)
    (hy : ∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w (rat y) ∈ GlobalTheory.LFun.KGL w n) :
    algebraMap ℚ_[p] (PadicAlgCl p) (algebraMap ℚ ℚ_[p] (y.1.2 : ℚ)) ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.Obar p := by
  have h : (y.1.1.val.map (GlobalTheory.SplitPts.conjE E).toRingHom)ᵀ * y.1.1.val =
      algebraMap ℚ E y.1.2 • (1 : Matrix (Fin n) (Fin n) E) := y.2.1
  have h0 := congrArg τ (congrFun (congrFun h ⟨0, hn⟩) ⟨0, hn⟩)
  rw [Matrix.mul_apply, map_sum, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h0
  have e : algebraMap ℚ_[p] (PadicAlgCl p) (algebraMap ℚ ℚ_[p] (y.1.2 : ℚ)) = τ (algebraMap ℚ E y.1.2) := by
    simp only [eq_ratCast, map_ratCast]
  rw [e, ← h0]
  refine sum_mem fun k _ => ?_
  rw [map_mul]
  exact mul_mem (ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff.2 (entry_le y hy (τ.comp (GlobalTheory.SplitPts.conjE E).toRingHom) k ⟨0, hn⟩))
    (ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff.2 (entry_le y hy τ k ⟨0, hn⟩))

omit [NumberField E] [IsCMField E] in
private theorem incl_mem (τ : E →+* PadicAlgCl p) (x : E) (hx : ‖τ x‖ ≤ 1) :
    GlobalTheory.LKRes.inclK p (FwOf τ) 1 (embOf τ x) ∈ GlobalTheory.LKRes.intKQ p (FwOf τ) 1 :=
  Subring.subset_closure (Or.inl ⟨⟨embOf τ x, ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff.2 hx⟩, rfl⟩)

end UpperTheory.Gal.W2.Seed.IntRev

open UpperTheory.Gal.W2.Seed.IntRev in
theorem UpperTheory.Gal.W2.Seed.pPIntRev :
    IntConj → PIntRev := by
  intro _ E _ _ _ A n p _ S y hy
  have hn : 0 < n := S.facts.pos
  have hy' := hyp_inv y hy
  refine Subgroup.mem_prod.2 ⟨mem_range_map _ _ (fun i j => ?_) (fun i j => ?_),
    (Subgroup.mem_pi _).2 fun k _ => mem_range_map _ _ (fun i j => ?_) (fun i j => ?_)⟩
  · obtain rfl : i = j := Subsingleton.elim _ _
    have h := mult_le hn (S.P.iotaP.comp S.P.s) y hy
    show Matrix.scalar (Fin 1) _ i i ∈ _
    rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq]
    exact h
  · obtain rfl : i = j := Subsingleton.elim _ _
    have h := mult_le hn (S.P.iotaP.comp S.P.s) y⁻¹ hy'
    show Matrix.scalar (Fin 1) _ i i ∈ _
    rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq]
    exact h
  · exact incl_mem (S.P.emb k) (y.1.1.val i j) (entry_le y hy (S.P.emb k) i j)
  · exact incl_mem (S.P.emb k) ((y⁻¹).1.1.val i j) (entry_le y⁻¹ hy' (S.P.emb k) i j)
