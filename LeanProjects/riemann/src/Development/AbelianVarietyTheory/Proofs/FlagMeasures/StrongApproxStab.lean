import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalExtend
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PatternUnitriangularStrongApproximationStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalCommonStabiliserBlockUnitriangularOnFrameStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlockUnitriangularRationalFromCommonStabiliserStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameMatrixCloseGivesLatticeCloseIntegralStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.StrongSt

theorem mat_step {K V : Type} [CommRing K] [AddCommGroup V] [Module K V] {m : ℕ} (v : Fin m → V)
    (n g' : V ≃ₗ[K] V) (s t : Matrix (Fin m) (Fin m) K) (hs : IsUnit s.det)
    (hn : ∀ j, n (v j) = ∑ i, s i j • v i) (hg : ∀ j, g' (v j) = ∑ i, t i j • v i) :
    ∀ j, (n⁻¹ * g') (v j) = ∑ i, (s⁻¹ * t) i j • v i := by
  have hw : ∀ i, n.symm (v i) = ∑ k, s⁻¹ k i • v k := by
    intro i
    apply n.injective
    rw [LinearEquiv.apply_symm_apply, map_sum]
    simp_rw [map_smul, hn, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    have h1 : s * s⁻¹ = 1 := Matrix.mul_nonsing_inv s hs
    have : ∀ l, ∑ k, s⁻¹ k i * s l k = (s * s⁻¹) l i := by
      intro l; rw [Matrix.mul_apply]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    simp_rw [← Finset.sum_smul, this, h1, Matrix.one_apply, ite_smul, one_smul, zero_smul]
    simp
  intro j
  change n.symm (g' (v j)) = _
  rw [hg, map_sum]
  simp_rw [map_smul, hw, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun k _ => by congr 1; exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end GlobalTheory.HL.StrongSt

namespace GlobalTheory.HL.StrongSt

theorem bc_sum {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : Places F E sig) (p : HeightOneSpectrum (𝓞 F)) {n m : ℕ}
    (a : Fin m → E) (x : Fin m → Fin n → E) :
    A.bc p (∑ i, a i • x i) = ∑ i, (A.loc p).ιE (a i) • A.bc p (x i) := by
  funext l
  simp [Places.bc, Finset.sum_apply, map_sum, map_mul]

theorem unit_of_pat {K : Type} [CommRing K] {m : ℕ} (P : Fin m → Fin m → Prop)
    (hP : ∀ i j, P i j → i < j) (s : Matrix (Fin m) (Fin m) K)
    (hs : ∀ i j, ¬ P i j → s i j = if i = j then 1 else 0) : IsUnit s.det := by
  have hup : s.BlockTriangular id := by
    intro i j hij
    have := hs i j (fun h => absurd (hP i j h) (not_lt.mpr (le_of_lt hij)))
    rw [this, if_neg (ne_of_gt (show j < i from hij))]
  rw [Matrix.det_of_upperTriangular hup]
  have : ∀ i, s i i = 1 := fun i => by rw [hs i i (fun h => absurd (hP i i h) (lt_irrefl _)), if_pos rfl]
  simp [this]

end GlobalTheory.HL.StrongSt

namespace GlobalTheory.HL.StrongSt

theorem strong_approx_stab : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ Λ : G.Lt, Submodule.IsLattice E Λ → ∀ c : ∀ p, ((A.loc p).Fp)ˣ, {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite → ∀ n : ∀ p, (G.S p).GLV, (∀ p, n p ∈ (G.S p).St) → {p | n p ∉ (G.S p).K0}.Finite → ∃ g ∈ G.St, ∀ p g', A.Ext p g g' → (n p)⁻¹ * g' ∈ (G.S p).K0 ∧ ∀ x ∈ A.lat p Λ, ∃ y ∈ A.lat p Λ, (n p).symm (g' x) - x = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) • y := by
  intro F E _ _ _ _ _ sig A r k G Λ hΛ c₁ hc₁ n hnSt hnK
  let c : ∀ p, ((A.loc p).Fp)ˣ := fun p => if ((c₁ p : (A.loc p).Fp) ∈ 𝒪[(A.loc p).Fp]) then c₁ p else 1
  have hcO : ∀ p, ((c p : (A.loc p).Fp) ∈ 𝒪[(A.loc p).Fp]) := by
    intro p
    by_cases h : ((c₁ p : (A.loc p).Fp) ∈ 𝒪[(A.loc p).Fp])
    · simp only [c, if_pos h]; exact h
    · simp only [c, if_neg h]; exact one_mem _
  have hc : {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite := by
    refine hc₁.subset fun p hp => ?_
    rintro ⟨u, hu⟩
    have h : ((c₁ p : (A.loc p).Fp) ∈ 𝒪[(A.loc p).Fp]) := hu ▸ (u : 𝒪[(A.loc p).Fp]).2
    exact hp ⟨u, by simp only [c, if_pos h]; exact hu⟩
  have hq : ∀ p, ∃ a ∈ 𝒪[(A.loc p).Fp], (c p : (A.loc p).Fp) = c₁ p * a := by
    intro p
    by_cases h : ((c₁ p : (A.loc p).Fp) ∈ 𝒪[(A.loc p).Fp])
    · exact ⟨1, one_mem _, by simp only [c, if_pos h, mul_one]⟩
    · refine ⟨(c₁ p : (A.loc p).Fp)⁻¹, ?_, by simp only [c, if_neg h]; simp⟩
      have h' : ¬ valuation (A.loc p).Fp (c₁ p : (A.loc p).Fp) ≤ 1 := h
      show valuation (A.loc p).Fp (c₁ p : (A.loc p).Fp)⁻¹ ≤ 1
      rw [map_inv₀]
      exact inv_le_one_of_one_le₀ (le_of_lt (not_le.1 h'))
  obtain ⟨d, hd0, hdfin, hd⟩ := GlobalTheory.T.frameMatrix_close_gives_lattice_close_integral A r k G Λ hΛ
  choose s hsP hsf hsI using fun p => GlobalTheory.T.localCommonStabiliser_blockUnitriangular_on_frame A r k G p (n p) (hnSt p)
  let c' : ∀ p, ((A.loc p).Fp)ˣ := fun p => c p * Units.mk0 (d p) (hd0 p)
  have hc' : {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c' p}.Finite := by
    refine (hc.union hdfin).subset fun p hp => ?_
    by_contra hq
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hq
    obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := hq
    exact hp ⟨u * v, by simp [c', hu, hv]⟩
  have hsI' : {p | ¬ IsIntM (A.L p) (s p)}.Finite := by
    refine (hnK.union G.c_unit).subset fun p hp => ?_
    by_contra hq
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hq
    exact hp (hsI p hq.2 hq.1)
  obtain ⟨t, htP, htc⟩ := GlobalTheory.T.pattern_unitriangular_strong_approximation A (r + 1) _ (fun i j h => h.1)
    (fun i j l hij hjl => ⟨hij.1.trans hjl.1, fun m h1 h2 => by
      by_cases hm : (m : ℕ) ≤ (j : ℕ)
      · exact hij.2 m h1 hm
      · exact hjl.2 m (by omega) h2⟩) c' hc' s hsP hsI'
  obtain ⟨g, hgSt, hgf⟩ := GlobalTheory.T.blockUnitriangular_rational_from_commonStabiliser A r k G t htP
  refine ⟨g, hgSt, fun p g' hg' => ?_⟩
  obtain ⟨g'', hg''St, hg''⟩ := hgSt p
  have hgg : g' = g'' := ((GlobalTheory.HL.RatExt.rational_extend A _ p).2.2.1 g).unique hg' hg''
  subst hgg
  have hh : (n p)⁻¹ * g' ∈ (G.S p).St := (G.S p).St.mul_mem ((G.S p).St.inv_mem (hnSt p)) hg''St
  have hgv : ∀ j, g' (A.bc p (G.f j)) = ∑ i, (t.map (A.loc p).ιE) i j • A.bc p (G.f i) := by
    intro j
    rw [hg' (G.f j), hgf j, bc_sum]
    rfl
  have hM := mat_step (fun j => A.bc p (G.f j)) (n p) g' (s p) (t.map (A.loc p).ιE)
    (unit_of_pat _ (fun i j h => h.1) (s p) (hsP p)) (hsf p) hgv
  obtain ⟨hK, hL⟩ := hd p (c p) _ _ (Units.ne_zero _) (hcO p) hh hM fun i j => by
    obtain ⟨o, ho, he⟩ := htc p i j
    exact ⟨o, ho, by rw [he]; simp [c']⟩
  refine ⟨hK, fun x hx => ?_⟩
  obtain ⟨y, hy, he⟩ := hL x hx
  obtain ⟨a, ha, hae⟩ := hq p
  have haO : algebraMap (A.loc p).Fp (A.loc p).Ep a ∈ (A.L p).O := by
    rw [(A.L p).O_def]
    exact isIntegral_algebraMap (R := 𝒪[(A.loc p).Fp]) (x := (⟨a, ha⟩ : 𝒪[(A.loc p).Fp]))
  refine ⟨(⟨_, haO⟩ : (A.L p).O) • y, Submodule.smul_mem _ _ hy, ?_⟩
  refine he.trans ?_
  rw [hae, map_mul, mul_smul]
  rfl

end GlobalTheory.HL.StrongSt
