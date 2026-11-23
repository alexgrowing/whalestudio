import Development.AutomorphicArithmetic.AdelicQuotients.ExistsCompactFundamentalSetOfHeightLe
import Development.AutomorphicArithmetic.AdelicQuotients.ExistsHeightBoundOfTwistedEllipticSupport
import Development.AutomorphicArithmetic.AdelicQuotients.ExistsIrreducibleCharpolyNormMatchOfTwistedEllip
import Development.AutomorphicArithmetic.AdelicQuotients.CharpolyEqOfNormEqOfTwistedConj
import Development.AutomorphicArithmetic.AdelicQuotients.AdelicGLGaloisBaseChangeDiagonalCompat
import Development.AutomorphicArithmetic.AdelicQuotients.ExistsClosedEmbeddingNormOneAdelicGLBaseChange
import Development.AutomorphicArithmetic.AdelicQuotients.UnimodularFiniteQuotientMeasureOfCocompact
import Development.AutomorphicArithmetic.AdelicQuotients.QuotientIntegralLtTopOfInvariantClosedEmbedding
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
open MeasureTheory NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Global GroundTheory.Global.SemiLocal
open GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped ENNReal NumberField.AdeleRing TensorProduct

noncomputable section

namespace UpperTheory.ConvolutionTheory.G.DiagonalEmbedding

private def d1 {K : Type} [Field K] [NumberField K] {n : ℕ} (δ : GL (Fin n) K) : G1 K n :=
  ⟨AdelicGLn.diagonal K n δ, rationalGL_le_normOneGL ⟨δ, rfl⟩⟩

private theorem differential_one_mem_scaled_lattice {K : Type} [Field K] [NumberField K] {n : ℕ} (δ : GL (Fin n) K) : d1 δ ∈ Gam K n :=
  ⟨δ, rfl⟩

private theorem exists_diagonalEmbed {K : Type} [Field K] [NumberField K] {n : ℕ} {g : G1 K n} (hg : g ∈ Gam K n) :
    ∃ δ, g = d1 δ := by
  obtain ⟨δ, h⟩ := hg
  exact ⟨δ, Subtype.ext h.symm⟩

private def tw {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (G1 K n)} [μ.IsHaarMeasure] (θ : Twist μ) :
    G1 K n →* G1 K n := θ.e.toMulEquiv.toMonoidHom

private instance discInf {K : Type} [Field K] [NumberField K] {n : ℕ} (S : Subgroup (G1 K n)) :
    DiscreteTopology ↥(Gam K n ⊓ S) :=
  DiscreteTopology.of_continuous_injective (f := Subgroup.inclusion (inf_le_left : Gam K n ⊓ S ≤ Gam K n))
    (continuous_subtype_val.subtype_mk _) (Subgroup.inclusion_injective _)

private instance discSub {K : Type} [Field K] [NumberField K] {n : ℕ} (S : Subgroup (G1 K n)) :
    DiscreteTopology ↥((Gam K n).subgroupOf S) :=
  DiscreteTopology.of_continuous_injective (β := Gam K n) (f := fun x => ⟨((x : S) : G1 K n), x.2⟩)
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
    fun _ _ h => by
      have h1 := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext h1)

private theorem closedCent {K : Type} [Field K] [NumberField K] {n : ℕ} (g : G1 K n) :
    IsClosed (Subgroup.centralizer {g} : Set (G1 K n)) := by
  have : (Subgroup.centralizer {g} : Set (G1 K n)) = {x | x * g = g * x} :=
    Set.ext fun x => Subgroup.mem_centralizer_singleton_iff
  rw [this]
  exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)

private instance lcCent {K : Type} [Field K] [NumberField K] {n : ℕ} (g : G1 K n) :
    LocallyCompactSpace (Subgroup.centralizer {g}) :=
  (closedCent g).isClosedEmbedding_subtypeVal.locallyCompactSpace

private instance scCent {K : Type} [Field K] [NumberField K] {n : ℕ} (g : G1 K n) :
    SecondCountableTopology (Subgroup.centralizer {g}) :=
  TopologicalSpace.Subtype.secondCountableTopology _

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] {σ : E ≃ₐ[F] E}
  {n : ℕ} {μ : Measure (G1 E n)} [μ.IsHaarMeasure] {θ : Twist μ}

omit [IsGalois F E] in
private theorem twist_diagonalEmbed (hθ : IsGalTwist σ θ) (h : GL (Fin n) E) : tw θ (d1 h) = d1 (sigmaGL σ h) :=
  Subtype.ext ((hθ (d1 h)).trans ((UpperTheory.adelicGL_galois_baseChange_diagonal_compat F E σ n).1 h))

omit [IsGalois F E] in
private theorem diagonalEmbed_conj_iff (hθ : IsGalTwist σ θ) (δ δ' h : GL (Fin n) E) :
    d1 δ' = (d1 h)⁻¹ * d1 δ * tw θ (d1 h) ↔ δ' = h⁻¹ * δ * sigmaGL σ h := by
  rw [twist_diagonalEmbed hθ, Subtype.ext_iff, ← (AdelicGLn.diagonal_injective E n).eq_iff, map_mul, map_mul, map_inv]
  rfl

private theorem side (h2 : G2) (hU : U1) (hσ : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) (hn : 0 < n)
    (hθ : IsGalTwist σ θ) (f : CC E n) (hf : Ell σ f) (ι : Type) (r : ι → GL (Fin n) E)
    (hex : ∀ δ, EllElt σ δ → ∃ i h, δ = h⁻¹ * r i * sigmaGL σ h)
    (hdi : ∀ i i' h, r i' = h⁻¹ * r i * sigmaGL σ h → i = i') :
    HasSum (fun i => ∫ y, f ((Quotient.out y)⁻¹ * d1 (r i) * tw θ (Quotient.out y))
        ∂quotientMeasure (Gam E n ⊓ twCent (tw θ) (d1 (r i))) μ) (twInt θ f) ∧
      ∀ i, Integrable (fun y => f ((Quotient.out y)⁻¹ * d1 (r i) * tw θ (Quotient.out y)))
        (quotientMeasure (Gam E n ⊓ twCent (tw θ) (d1 (r i))) μ) := by
  obtain ⟨R, hR⟩ := UpperTheory.exists_height_bound_of_twistedElliptic_support h2 F E σ hσ n hn μ θ hθ f hf
  obtain ⟨C, hC, hC'⟩ := UpperTheory.exists_compact_fundamental_set_of_height_le E n R
  refine hU (G1 E n) (Gam E n) μ (tw θ) θ.e.continuous (fun g hg => (θ.mem_gam g).2 hg) f
    ⟨C, hC, fun x δ hδ h => hC' x (hR x δ hδ h)⟩ ι (fun i => d1 (r i)) (fun i => differential_one_mem_scaled_lattice _) ?_ ?_
  · rintro δ hδ ⟨x, hx⟩
    obtain ⟨δ, rfl⟩ := exists_diagonalEmbed hδ
    obtain ⟨i, h, e⟩ := hex δ (hf δ x _ (by rw [← hθ x]; rfl) hx)
    exact ⟨i, d1 h, differential_one_mem_scaled_lattice h, (diagonalEmbed_conj_iff hθ _ _ _).2 e⟩
  · intro i i' g hg e
    obtain ⟨h, rfl⟩ := exists_diagonalEmbed hg
    exact hdi i i' h ((diagonalEmbed_conj_iff hθ _ _ _).1 e)
end

private theorem contTw {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (G1 K n)} [μ.IsHaarMeasure] (θ : Twist μ)
    (f : CC K n) (d : G1 K n) : Continuous fun x : G1 K n => f (x⁻¹ * d * tw θ x) :=
  f.continuous.comp ((continuous_id.inv.mul continuous_const).mul θ.e.continuous)

private theorem termF (hU : U2) {F : Type} [Field F] [NumberField F] {n : ℕ} (μ : Measure (G1 F n)) [μ.IsHaarMeasure]
    (f : CC F n) (g : G1 F n) (ν : Measure (Subgroup.centralizer {g})) [ν.IsHaarMeasure] [ν.IsInvInvariant]
    [ν.IsMulRightInvariant] (hv : quotientMeasure ((Gam F n).subgroupOf (Subgroup.centralizer {g})) ν Set.univ < ⊤)
    (hi : Integrable (fun y => f ((Quotient.out y)⁻¹ * g * tw (Twist.id μ) (Quotient.out y)))
        (quotientMeasure (Gam F n ⊓ twCent (tw (Twist.id μ)) g) μ)) :
    ∫ y, f ((Quotient.out y)⁻¹ * g * tw (Twist.id μ) (Quotient.out y))
        ∂quotientMeasure (Gam F n ⊓ twCent (tw (Twist.id μ)) g) μ =
      ((quotientMeasure ((Gam F n).subgroupOf (Subgroup.centralizer {g})) ν Set.univ).toReal : ℂ) *
        quotInt μ id (fun t : Subgroup.centralizer {g} => (t : G1 F n)) ν fun x => f (x⁻¹ * g * x) := by
  have hc : twCent (tw (Twist.id μ)) g = Subgroup.centralizer {g} := by
    ext x
    rw [Subgroup.mem_centralizer_singleton_iff]
    change x⁻¹ * g * x = g ↔ _
    rw [mul_assoc, inv_mul_eq_iff_eq_mul, eq_comm]
  refine (hU (G1 F n) (Subgroup.centralizer {g}) μ ν (Subgroup.centralizer {g}).subtype
    (closedCent g).isClosedEmbedding_subtypeVal _ (Gam F n ⊓ twCent (tw (Twist.id μ)) g) ?_ hv
    (fun x => f (x⁻¹ * g * tw (Twist.id μ) x)) (contTw _ f g) ?_ hi).1
  · rw [hc, Subgroup.subgroupOf_map_subtype]
  · intro t x
    exact congrArg f (twConj_mul_left (tw (Twist.id μ)) g (h := t) (hc.ge t.2) x)

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] {σ : E ≃ₐ[F] E}
  {n : ℕ} {μ : Measure (G1 E n)} [μ.IsHaarMeasure] {θ : Twist μ}

private theorem termE (hU : U2) (q1 : Q1) (q2 : Q2) (n3 : N3) (n5 : N5)
    (hσ : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) (hn : 0 < n) (hθ : IsGalTwist σ θ) (f : CC E n)
    (δ : GL (Fin n) E) (γ : GL (Fin n) F) (hγ : IsRegSemisimple γ) (hN : normGL σ δ = incl γ)
    (ν : Measure (Subgroup.centralizer {d1 γ})) [ν.IsHaarMeasure] [ν.IsInvInvariant] [ν.IsMulRightInvariant]
    (hv : quotientMeasure ((Gam F n).subgroupOf (Subgroup.centralizer {d1 γ})) ν Set.univ < ⊤)
    (hi : Integrable (fun y => f ((Quotient.out y)⁻¹ * d1 δ * tw θ (Quotient.out y)))
        (quotientMeasure (Gam E n ⊓ twCent (tw θ) (d1 δ)) μ)) :
    ∫ y, f ((Quotient.out y)⁻¹ * d1 δ * tw θ (Quotient.out y)) ∂quotientMeasure (Gam E n ⊓ twCent (tw θ) (d1 δ)) μ =
      ((quotientMeasure ((Gam F n).subgroupOf (Subgroup.centralizer {d1 γ})) ν Set.univ).toReal : ℂ) *
        quotInt μ (fun x : G1 E n => (x : AdelicGLn.AdelicGL E n))
          (fun t : Subgroup.centralizer {d1 γ} => mapGL n (adeleMap F E) ((t : G1 F n) : AdelicGLn.AdelicGL F n)) ν
          (fun x => ext0 f ((x : AdelicGLn.AdelicGL E n)⁻¹ * AdelicGLn.diagonal E n δ *
            mapGL n (galAd σ) (x : AdelicGLn.AdelicGL E n))) := by
  obtain ⟨j, hj, hj1, hj2⟩ := UpperTheory.exists_closedEmbedding_normOneAdelicGL_baseChange n5 F E σ hσ n hn
  obtain ⟨-, hd2, hd3⟩ := UpperTheory.adelicGL_galois_baseChange_diagonal_compat F E σ n
  let i : Subgroup.centralizer {d1 γ} →* G1 E n := j.comp (Subgroup.centralizer {d1 γ}).subtype
  have hic : Topology.IsClosedEmbedding i := hj.comp (closedCent _).isClosedEmbedding_subtypeVal
  have hcent : ∀ x : G1 E n, x ∈ twCent (tw θ) (d1 δ) ↔ ∃ t, x = i t := by
    intro x
    have h1 : x ∈ twCent (tw θ) (d1 δ) ↔ (x : AdelicGLn.AdelicGL E n)⁻¹ * AdelicGLn.diagonal E n δ *
        mapGL n (galAd σ) (x : AdelicGLn.AdelicGL E n) = AdelicGLn.diagonal E n δ := by
      rw [← hθ x]
      exact Subtype.ext_iff
    rw [h1, n3 F E σ hσ n hn δ γ hγ hN]
    constructor
    · rintro ⟨t, ht, e⟩
      exact ⟨⟨⟨t, hj2 t (e ▸ x.2)⟩, Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext ht)⟩,
        Subtype.ext (e.trans (hj1 ⟨t, _⟩).symm)⟩
    · rintro ⟨t, rfl⟩
      exact ⟨_, congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 t.2), hj1 t⟩
  have hmap : ((Gam F n).subgroupOf (Subgroup.centralizer {d1 γ})).map i = Gam E n ⊓ twCent (tw θ) (d1 δ) := by
    ext x
    constructor
    · rintro ⟨t, ⟨g, hg⟩, rfl⟩
      refine ⟨⟨incl g, ?_⟩, (hcent _).2 ⟨t, rfl⟩⟩
      rw [← hd2]
      exact (congrArg (mapGL n (adeleMap F E)) hg).trans (hj1 t).symm
    · rintro ⟨⟨h, hh⟩, hx⟩
      obtain ⟨t, rfl⟩ := (hcent x).1 hx
      obtain ⟨g, hg⟩ := hd3 _ h ((hj1 t).symm.trans hh.symm)
      exact ⟨t, ⟨g, hg.symm⟩, rfl⟩
  have hinv : ∀ t x, f ((i t * x)⁻¹ * d1 δ * tw θ (i t * x)) = f (x⁻¹ * d1 δ * tw θ x) := fun t x =>
    congrArg f (twConj_mul_left (tw θ) (d1 δ) ((hcent _).2 ⟨t, rfl⟩) x)
  obtain ⟨h1, h2⟩ := hU (G1 E n) (Subgroup.centralizer {d1 γ}) μ ν i hic _ _ hmap hv
    (fun x => f (x⁻¹ * d1 δ * tw θ x)) (contTw _ f _) hinv hi
  have h3 := UpperTheory.quotientIntegral_lt_top_of_invariant_closedEmbedding q1 q2 (AdelicGLn.AdelicGL E n) _ (normOneGL E n) isClosed_normOneGL μ ν i hic
    (fun x => f (x⁻¹ * d1 δ * tw θ x)) (contTw _ f _) hinv h2
  rw [h1, ← h3]
  congr 2
  · exact funext fun t => hj1 t
  · funext x
    rw [← hθ x, ext0]
    exact (dif_pos (x⁻¹ * d1 δ * tw θ x).2 (t := fun h => f ⟨_, h⟩) (e := fun _ => 0)).symm
end

private theorem norm_self {F : Type} [Field F] {n : ℕ} (γ : GL (Fin n) F) : normGL (1 : F ≃ₐ[F] F) γ = incl γ := by
  rw [normGL, Module.finrank_self, twNorm_succ, twNorm_zero, one_mul, pow_zero]
  ext a b
  rfl

end UpperTheory.ConvolutionTheory.G.DiagonalEmbedding

open UpperTheory.ConvolutionTheory.G.DiagonalEmbedding in
theorem UpperTheory.ConvolutionTheory.G.twisted_trace_formula_elliptic_expansion :
    G2 → U1 → U2 → Q1 → Q2 → N1 → N2 → N3 → N4 → N5 → G0 → G3 := by
  intro g2 u1 u2 q1 q2 n1 n2 n3 n4 n5 g0 F E _ _ _ _ _ _ σ hσ n hn μE _ μF _ θ hθ c fE fF hE hF hM
  classical
  have h1 : ∀ τ : F ≃ₐ[F] F, τ ∈ Subgroup.zpowers (1 : F ≃ₐ[F] F) := fun τ => by
    rw [Subsingleton.elim τ 1]; exact one_mem _
  let ι : Type := {p : F[X] // Irreducible p ∧ ∃ γ : GL (Fin n) F, (γ : Matrix (Fin n) (Fin n) F).charpoly = p}
  let γ : ι → GL (Fin n) F := fun p => p.2.2.choose
  have hγ : ∀ p : ι, (γ p : Matrix (Fin n) (Fin n) F).charpoly = p.1 := fun p => p.2.2.choose_spec
  have hirr : ∀ p : ι, Irreducible (γ p : Matrix (Fin n) (Fin n) F).charpoly := fun p => (hγ p).symm ▸ p.2.1
  let S : Set ι := {p | ∃ δ : GL (Fin n) E, normGL σ δ = incl (γ p)}
  let δ : S → GL (Fin n) E := fun p => p.2.choose
  have hδ : ∀ p : S, normGL σ (δ p) = incl (γ p.1) := fun p => p.2.choose_spec
  obtain ⟨sF, iF⟩ := side g2 u1 h1 hn (g0.2 F n μF) fF hF ι γ (fun d hd => by
      obtain ⟨g, hg, h⟩ := UpperTheory.exists_irreducible_charpoly_norm_match_of_twistedElliptic n1 n2 F F 1 h1 n hn d hd
      exact ⟨⟨_, hg, g, rfl⟩, (h _ (hγ _)).2 _ (norm_self _)⟩)
    fun p p' h e => Subtype.ext ((hγ p).symm.trans
      ((UpperTheory.charpoly_eq_of_norm_eq_of_twisted_conj F F 1 h1 n hn _ _ h _ _ (norm_self _) (norm_self _) e).trans (hγ p')))
  obtain ⟨sE, iE⟩ := side g2 u1 hσ hn hθ fE hE S δ (fun d hd => by
      obtain ⟨g, hg, h⟩ := UpperTheory.exists_irreducible_charpoly_norm_match_of_twistedElliptic n1 n2 F E σ hσ n hn d hd
      obtain ⟨ha, hb⟩ := h _ (hγ ⟨_, hg, g, rfl⟩)
      exact ⟨⟨_, ha⟩, hb _ (hδ _)⟩)
    fun p p' h e => Subtype.ext (Subtype.ext ((hγ p.1).symm.trans
      ((UpperTheory.charpoly_eq_of_norm_eq_of_twisted_conj F E σ hσ n hn _ _ h _ _ (hδ p) (hδ p') e).trans (hγ p'.1))))
  let ν : ∀ p : ι, Measure (Subgroup.centralizer {d1 (γ p)}) := fun p => Measure.haar
  have hν : ∀ p, (ν p).IsMulRightInvariant ∧ (ν p).IsInvInvariant ∧
      quotientMeasure ((Gam F n).subgroupOf (Subgroup.centralizer {d1 (γ p)})) (ν p) Set.univ < ⊤ := fun p =>
    UpperTheory.unimodular_finite_quotientMeasure_of_cocompact _ _ (ν p) (n4 F n (γ p) (d1 (γ p)) rfl (hirr p)).2
  refine sE.unique ?_
  have sF' := sF.mul_left c
  rw [← hasSum_subtype_iff_of_support_subset (s := S)] at sF'
  · refine Eq.mpr (congrArg (fun g => HasSum g (c * twInt (Twist.id μF) fF)) (funext fun p => ?_)) sF'
    obtain ⟨_, _, hv⟩ := hν p.1
    rw [Function.comp_apply, termF u2 μF fF _ (ν p.1) hv (iF p.1),
      termE u2 q1 q2 n3 n5 hσ hn hθ fE (δ p) (γ p.1) (hirr p.1).separable (hδ p) (ν p.1) hv (iE p),
      (hM (γ p.1) (d1 (γ p.1)) rfl (hirr p.1) (ν p.1) inferInstance).1 (δ p) (hδ p)]
    ring
  · intro p hp
    by_contra hS
    obtain ⟨_, _, hv⟩ := hν p
    apply hp
    beta_reduce
    rw [termF u2 μF fF _ (ν p) hv (iF p), (hM (γ p) (d1 (γ p)) rfl (hirr p) (ν p) inferInstance).2 hS, mul_zero, mul_zero]
