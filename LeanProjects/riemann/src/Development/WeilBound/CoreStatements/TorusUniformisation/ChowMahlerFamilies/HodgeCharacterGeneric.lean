import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.Xgn.HodgeCharacterGeneric

open Polynomial GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.HT.LatBasic TensorProduct

variable {E : Type} [Field E] [NumberField E] {K : Type} [Field K] [CharZero K]

theorem sum_emb [Fintype (E →+* K)] (h : Nat.card (E →+* K) = Module.finrank ℚ E) (x : E) :
    ∑ s : E →+* K, s x = algebraMap ℚ K (Algebra.trace ℚ E x) := by
  classical
  letI : CharZero (AlgebraicClosure K) :=
    charZero_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective
  let f : (E →+* K) → (E →ₐ[ℚ] AlgebraicClosure K) := fun s =>
    ((algebraMap K (AlgebraicClosure K)).comp s).toRatAlgHom
  have hf : Function.Injective f := by
    intro s t hst
    ext y
    have := congrArg (fun g : E →ₐ[ℚ] AlgebraicClosure K => g y) hst
    exact (algebraMap K (AlgebraicClosure K)).injective this
  have hcard : Fintype.card (E →+* K) = Fintype.card (E →ₐ[ℚ] AlgebraicClosure K) := by
    rw [AlgHom.card, ← h, Nat.card_eq_fintype_card]
  have hb : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, hcard⟩
  apply (algebraMap K (AlgebraicClosure K)).injective
  rw [map_sum]
  calc ∑ s : E →+* K, algebraMap K (AlgebraicClosure K) (s x) = ∑ s, f s x := rfl
    _ = ∑ σ : E →ₐ[ℚ] AlgebraicClosure K, σ x := hb.sum_comp (fun σ => σ x)
    _ = algebraMap ℚ (AlgebraicClosure K) (Algebra.trace ℚ E x) :=
        (trace_eq_sum_embeddings (AlgebraicClosure K) (x := x)).symm
    _ = _ := by simp [eq_ratCast]

variable {V : Type} [AddCommGroup V] [Module K V]

theorem sum_eigProj [Fintype (E →+* K)] (h : Nat.card (E →+* K) = Module.finrank ℚ E)
    (ρ : 𝓞 E →+* Module.End K V) : ∑ s, eigProj ρ s = 1 := by
  classical
  set b := RingOfIntegers.basis E with hb
  have h1 : (1 : E) = ∑ j, ((b.repr 1 j : ℤ) : E) * integralBasis E j := by
    have := congrArg (algebraMap (𝓞 E) E) (b.sum_repr 1)
    simpa [integralBasis_apply, map_sum, zsmul_eq_mul] using this.symm
  have hrep : ∀ k, Algebra.trace ℚ E (dualInt E k) = ((b.repr 1 k : ℤ) : ℚ) := by
    intro k
    conv_lhs => rw [← mul_one (dualInt E k), h1, Finset.mul_sum, map_sum]
    simp_rw [mul_left_comm (dualInt E _), ← zsmul_eq_mul, map_zsmul, trace_dualInt]
    simp
  simp only [eigProj]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, sum_emb h, hrep]
  calc ∑ k, algebraMap ℚ K ((b.repr 1 k : ℤ) : ℚ) • ρ (b k) = ρ (∑ k, b.repr 1 k • b k) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_zsmul, map_intCast, Int.cast_smul_eq_zsmul]
    _ = 1 := by rw [b.sum_repr, map_one]

theorem isInternal [Fintype (E →+* K)] [DecidableEq (E →+* K)] (h : Nat.card (E →+* K) = Module.finrank ℚ E)
    (ρ : 𝓞 E →+* Module.End K V) : DirectSum.IsInternal (HT.eigSp ρ) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · intro s
    rw [Submodule.disjoint_def]
    intro x hx hy
    have hk : (⨆ j, ⨆ (_ : j ≠ s), HT.eigSp ρ j) ≤ LinearMap.ker (eigProj ρ s) :=
      iSup₂_le fun j hj y hy => eigProj_of_ne hj.symm hy
    rw [← eigProj_of_mem hx]
    exact hk hy
  · rw [eq_top_iff]
    intro x _
    have : x = ∑ s, eigProj ρ s x := by
      rw [← LinearMap.sum_apply, sum_eigProj h]; rfl
    rw [this]
    exact Submodule.sum_mem _ fun s _ => Submodule.mem_iSup_of_mem s (eigProj_mem ρ s x)

theorem charpoly_eq [Fintype (E →+* K)] [FiniteDimensional K V]
    (h : Nat.card (E →+* K) = Module.finrank ℚ E) (ρ : 𝓞 E →+* Module.End K V) :
    (∀ a : 𝓞 E, (ρ a).charpoly =
      ∏ s : E →+* K, (X - Polynomial.C (s (a : E))) ^ Module.finrank K (HT.eigSp ρ s)) ∧
    ∑ s : E →+* K, Module.finrank K (HT.eigSp ρ s) = Module.finrank K V := by
  classical
  let b := (isInternal h ρ).collectedBasis fun s => Module.finBasis K (HT.eigSp ρ s)
  have hb : ∀ i, b i ∈ HT.eigSp ρ i.1 := fun i => (isInternal h ρ).collectedBasis_mem _ i
  refine ⟨fun a => ?_, ?_⟩
  · have hm : LinearMap.toMatrix b b (ρ a) = Matrix.diagonal fun i => i.1 (a : E) := by
      ext i j
      rw [LinearMap.toMatrix_apply, mem_eigSp.1 (hb j) a, map_smul, b.repr_self, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij, Finsupp.single_apply, Ne.symm hij]
    rw [← LinearMap.charpoly_toMatrix _ b, hm, Matrix.charpoly_diagonal, Fintype.prod_sigma]
    simp
  · rw [Module.finrank_eq_card_basis b]
    simp

theorem reg_ne (σ : E →+* K) : eigProj (regAct K E) σ 1 ≠ 0 := by
  classical
  intro h0
  have hne : Nonempty (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) := by
    by_contra hn
    rw [not_nonempty_iff] at hn
    have := sum_dualInt_mul (E := E)
    simp [Finset.univ_eq_empty] at this
  obtain ⟨k⟩ := hne
  simp only [eigProj, LinearMap.sum_apply, LinearMap.smul_apply, regAct_basis] at h0
  have hk := Fintype.linearIndependent_iff.mp
    (Algebra.TensorProduct.basis K (RingOfIntegers.basis E)).linearIndependent _ h0 k
  have hd : dualInt E k = 0 := by
    rw [← map_zero σ] at hk
    exact σ.injective hk
  have ht := trace_dualInt (E := E) k k
  simp [hd] at ht

theorem charpoly_lmul [Fintype (E →+* K)] (h : Nat.card (E →+* K) = Module.finrank ℚ E) (a : 𝓞 E) :
    (Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom K) =
      ∏ s : E →+* K, (X - Polynomial.C (s (a : E))) := by
  classical
  have hfr : Module.finrank K (K ⊗[ℤ] 𝓞 E) = Module.finrank ℚ E := by
    rw [Module.finrank_baseChange, RingOfIntegers.rank]
  obtain ⟨hc, hs⟩ := charpoly_eq h (regAct K E)
  have hpos : ∀ s : E →+* K, 1 ≤ Module.finrank K (HT.eigSp (regAct K E) s) := fun s =>
    Module.finrank_pos_iff_exists_ne_zero.mpr
      ⟨⟨_, eigProj_mem _ s 1⟩, fun h0 => reg_ne s (congrArg Subtype.val h0)⟩
  have hone : ∀ s, Module.finrank K (HT.eigSp (regAct K E) s) = 1 := by
    by_contra hn
    push_neg at hn
    obtain ⟨t, ht⟩ := hn
    have hlt : ∑ _s : E →+* K, 1 < ∑ s, Module.finrank K (HT.eigSp (regAct K E) s) :=
      Finset.sum_lt_sum (fun s _ => hpos s)
        ⟨t, Finset.mem_univ _, lt_of_le_of_ne (hpos t) (Ne.symm ht)⟩
    rw [hs, hfr, ← h, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hlt
    simp [Nat.card_eq_fintype_card] at hlt
  have hbc : regAct K E a = (Algebra.lmul ℤ (𝓞 E) a).baseChange K := by
    apply TensorProduct.AlgebraTensorModule.curry_injective
    ext c y
    simp [regAct]
  rw [← algebraMap_int_eq, ← LinearMap.charpoly_baseChange, ← hbc, hc a]
  simp [hone]

theorem charpoly_rhoH {O : Type} [CommRing O] [StarRing O] {d : ℕ} (B : Germ.FB K d O) (a : O) :
    (rhoH B a).charpoly = (rho B a).charpoly * (rho B (star a)).charpoly := by
  classical
  let b := (Pi.basisFun K (Fin d)).prod (Pi.basisFun K (Fin d))
  have hM : LinearMap.toMatrix b b (rhoH B a) =
      Matrix.fromBlocks (rho B a) 0 (-Matrix.transpose (bil (B.ad a) 1 1))
        (Matrix.transpose (rho B (star a))) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [b, LinearMap.toMatrix_apply, rhoH, Matrix.toLin'_apply, Matrix.mulVec_single_one]
  rw [← LinearMap.charpoly_toMatrix (rhoH B a) b, hM, Matrix.charpoly_fromBlocks_zero₁₂,
    Matrix.charpoly_transpose]

end PositivityTheory.Xgn.HodgeCharacterGeneric

theorem PositivityTheory.Xgn.hodge_character_generic : ∀ (E : Type) [Field E] [NumberField E] [StarRing (𝓞 E)] (K : Type) [Field K] [CharZero K] (d r : ℕ) (B : Germ.FB K d (𝓞 E)) (ρ : 𝓞 E →+* Module.End K (Fin d → K)), (∀ a v, ρ a v = (rho B a).mulVec v) → Nat.card (E →+* K) = Module.finrank ℚ E → (∀ s s' : E →+* K, (∀ a : 𝓞 E, s' (a : E) = s ((star a : 𝓞 E) : E)) → Module.finrank K (HT.eigSp ρ s) + Module.finrank K (HT.eigSp ρ s') = r) → HChar B r := by
  classical
  intro E _ _ _ K _ _ d r B ρ hρ h hdim
  have hinj : ∀ s : E →+* K,
      Function.Injective (s.comp ((algebraMap (𝓞 E) E).comp (starRingEnd (𝓞 E)))) :=
    fun s x y hxy => star_injective (IsFractionRing.injective (𝓞 E) E (s.injective hxy))
  let φ : (E →+* K) → (E →+* K) := fun s => IsFractionRing.lift (hinj s)
  have hφ : ∀ s (x : 𝓞 E), φ s (algebraMap (𝓞 E) E x) = s (algebraMap (𝓞 E) E (star x)) :=
    fun s x => IsFractionRing.lift_algebraMap (hinj s) x
  have hφφ : ∀ s, φ (φ s) = s := fun s =>
    IsFractionRing.ringHom_ext (A := 𝓞 E) fun x => by rw [hφ, hφ, star_star]
  have hbij : Function.Bijective φ := Function.Involutive.bijective hφφ
  have hsum : ∀ s, Module.finrank K (HT.eigSp ρ s) + Module.finrank K (HT.eigSp ρ (φ s)) = r :=
    fun s => hdim s (φ s) fun a => hφ s a
  have hrho : ∀ a, (rho B a).charpoly = (ρ a).charpoly := by
    intro a
    rw [← Matrix.charpoly_toLin']
    congr 1
    exact LinearMap.ext fun v => by rw [Matrix.toLin'_apply, hρ]
  obtain ⟨hc, -⟩ := PositivityTheory.Xgn.HodgeCharacterGeneric.charpoly_eq h ρ
  intro a
  rw [PositivityTheory.Xgn.HodgeCharacterGeneric.charpoly_rhoH, hrho, hrho, hc, hc,
    PositivityTheory.Xgn.HodgeCharacterGeneric.charpoly_lmul h, ← Finset.prod_pow]
  have h2 : ∏ s : E →+* K, (Polynomial.X - Polynomial.C (s ((star a : 𝓞 E) : E))) ^
        Module.finrank K (HT.eigSp ρ s) =
      ∏ s : E →+* K, (Polynomial.X - Polynomial.C (s (a : E))) ^
        Module.finrank K (HT.eigSp ρ (φ s)) := by
    symm
    refine Fintype.prod_bijective φ hbij _ _ fun s => ?_
    have := hφ s (star a)
    rw [star_star] at this
    simp only [this]
  rw [h2, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [← pow_add, hsum s]
