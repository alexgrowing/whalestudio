import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidualChains.SeedRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PotentialModularityTower

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
section
variable {R R' : Type} [CommRing R] [CommRing R']
private theorem adj_map (j : R →+* R') (X : M4 R) : adj (X.map j) = (adj X).map j := by
  ext i i'
  simp only [adj_apply, Matrix.map_apply, map_zsmul]
private theorem conj_map (j : R →+* R') (n X : M4 R) :
    adj (n.map j) * X.map j * n.map j = (adj n * X * n).map j := by
  rw [Matrix.map_mul, Matrix.map_mul, adj_map]
private theorem isGSp_map (j : R →+* R') {ν : R} {X : M4 R} (hX : IsGSp ν X) : IsGSp (j ν) (X.map j) := by
  have h : (j ν) • (1 : M4 R') = (ν • (1 : M4 R)).map j := by
    ext i i'
    by_cases h : i = i' <;> simp [Matrix.one_apply, h]
  unfold IsGSp at hX ⊢
  rw [adj_map, ← Matrix.map_mul, h, hX]
private theorem isPair_map {O Γ : Type} [CommRing O] [Group Γ] (Φ : Fr O Γ) (a : O →+* R) (f : R →+* R')
    (P : PD Φ.ι Γ R) (h : Φ.IsPair a P) : Φ.IsPair (f.comp a) (P.map f) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hr : ∀ g, (P.map f).r g = (P.r g).map f := fun _ => rfl
  have hn : ∀ v, (P.map f).n v = (P.n v).map f := fun _ => rfl
  refine ⟨fun g => isGSp_map f (h1 g), fun g hg => ?_, ?_, fun v => ⟨?_, fun i => ?_, fun i j hij => ?_⟩,
    fun v s hs i j hij => ?_, fun v s hs i => ?_⟩
  · rw [hr, h2 g hg, Matrix.map_one _ (map_zero f) (map_one f)]
  · rw [hr]; exact h3.map (map_zero f)
  · have := isGSp_map f (h4 v).1
    rwa [map_one] at this
  · rw [hn, Matrix.map_apply, (h4 v).2.1, map_one]
  · rw [hn, Matrix.map_apply, (h4 v).2.2 i j hij, map_zero]
  · rw [hr, hn, conj_map, Matrix.map_apply, h5 v s hs i j hij, map_zero]
  · have := h6 v s hs i
    unfold PD.ψ at this ⊢
    rw [hr, hn, conj_map, Matrix.map_apply, this, map_one]
end
theorem UpperTheory.V.Ws.Chain.isRes_map_red_and_inV_ent_map_red_of_map_residue :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l) {c₁ : Coef l} (h : c.O ≤ c₁.O) (Q : PD T.ι (G T.F Ω) c₁.O),
      T.SeedPairAlt ι h Q → (T.fr ∅).IsRes (𝔞.red c) (Q.map (𝔞.red c₁)) ∧
        (Fr.InV (Φ := T.fr ∅) (Q.map (residue c₁.O)) → Fr.InV (Φ := T.fr ∅) (Q.map (𝔞.red c₁))) ∧
        ∀ w, Ent (Q.map (residue c₁.O)).r w → Ent (Q.map (𝔞.red c₁)).r w := by
  intro Ω _ _ _ l _ c D T ι 𝔞 c₁ h Q hQ
  have hj : Function.Injective (𝔞.j c₁) := (𝔞.j c₁).injective
  have hjr : ∀ x, 𝔞.red c₁ x = 𝔞.j c₁ (residue c₁.O x) := fun x => rfl
  have hQm : Q.map (𝔞.red c₁) = (Q.map (residue c₁.O)).map (𝔞.j c₁) := rfl
  have ha : 𝔞.red c = (𝔞.j c₁).comp ((residue c₁.O).comp (inc h)) := by
    ext x
    change residue _ (𝔞.a c x) = residue _ (𝔞.a c₁ (Subalgebra.inclusion h x))
    rw [𝔞.compat]
  have hres : (T.fr ∅).IsRes ((residue c₁.O).comp (inc h)) (Q.map (residue c₁.O)) := by
    refine ⟨isPair_map _ _ _ _ hQ.pair, hQ.res, fun i j N => ?_⟩
    have h1 := hQ.cont i j 1
    have h2 : IsLocallyConstant fun g => residue c₁.O (Q.r g i j) := by
      have := h1.comp (Ideal.Quotient.factor (show maximalIdeal c₁.O ^ 1 ≤ maximalIdeal c₁.O by rw [pow_one]))
      exact this
    exact h2.comp _
  refine ⟨?_, ?_, ?_⟩
  · rw [ha, hQm]
    exact (chainMap (T.fr ∅) _ (𝔞.j c₁) _).1.2 hres
  · rintro ⟨h1, h2⟩
    refine ⟨fun g i j hij hw => ?_, fun v => ⟨fun i j hij hw => ?_, fun h0 => (h2 v).2 ?_⟩⟩
    · exact (congrArg (𝔞.j c₁) (h1 g i j hij hw)).trans (map_zero _)
    · exact (congrArg (𝔞.j c₁) ((h2 v).1 i j hij hw)).trans (map_zero _)
    · exact hj (h0.trans (map_zero _).symm)
  · rintro w ⟨g, i, j, hw, hne⟩
    exact ⟨g, i, j, hw, fun h0 => hne (hj (h0.trans (map_zero _).symm))⟩
end
