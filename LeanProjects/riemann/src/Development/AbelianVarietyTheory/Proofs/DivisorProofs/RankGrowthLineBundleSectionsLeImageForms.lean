import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JoinCastSucc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfRingKrullDimConeIdeal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeDegreeGrowthChowFormIntegrality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearSystemHilbertFunctionEqFinrankConePiece
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatioMemValuationSubringAtGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralConeRingOfForallValuationSubring

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.CompHt
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open AlgebraicGeometry Filter GlobalTheory.Twist GlobalTheory.Points

namespace GlobalTheory.SecGrowth

section Ratio

variable {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]

def ratioSub (ev : V →ₗ[K] Ω) : Subfield Ω where
  carrier := {r | ∃ (e : ℕ) (h : Ω), h ∈ ((LinearMap.range ev) ^ e : Submodule K Ω) ∧ h ≠ 0 ∧
    r * h ∈ ((LinearMap.range ev) ^ e : Submodule K Ω)}
  mul_mem' := by
    rintro a c ⟨e1, h1, m1, n1, p1⟩ ⟨e2, h2, m2, n2, p2⟩
    refine ⟨e1 + e2, h1 * h2, ?_, mul_ne_zero n1 n2, ?_⟩
    · rw [pow_add]; exact Submodule.mul_mem_mul m1 m2
    · rw [pow_add, show a * c * (h1 * h2) = (a * h1) * (c * h2) by ring]; exact Submodule.mul_mem_mul p1 p2
  one_mem' := ⟨0, 1, by rw [pow_zero]; exact Submodule.mem_one.2 ⟨1, map_one _⟩, one_ne_zero,
    by rw [one_mul, pow_zero]; exact Submodule.mem_one.2 ⟨1, map_one _⟩⟩
  add_mem' := by
    rintro a c ⟨e1, h1, m1, n1, p1⟩ ⟨e2, h2, m2, n2, p2⟩
    refine ⟨e1 + e2, h1 * h2, ?_, mul_ne_zero n1 n2, ?_⟩
    · rw [pow_add]; exact Submodule.mul_mem_mul m1 m2
    · rw [pow_add, show (a + c) * (h1 * h2) = (a * h1) * h2 + h1 * (c * h2) by ring]
      exact add_mem (Submodule.mul_mem_mul p1 m2) (Submodule.mul_mem_mul m1 p2)
  zero_mem' := ⟨0, 1, by rw [pow_zero]; exact Submodule.mem_one.2 ⟨1, map_one _⟩, one_ne_zero,
    by rw [zero_mul]; exact zero_mem _⟩
  neg_mem' := by
    rintro a ⟨e, h, m, n, p⟩
    exact ⟨e, h, m, n, by rw [neg_mul]; exact neg_mem p⟩
  inv_mem' := by
    rintro a ⟨e, h, m, n, p⟩
    by_cases ha : a = 0
    · refine ⟨e, h, m, n, ?_⟩
      rw [ha, inv_zero, zero_mul]; exact zero_mem _
    · exact ⟨e, a * h, p, mul_ne_zero ha n, by rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]; exact m⟩

theorem algebraMap_mem_ratioSub (ev : V →ₗ[K] Ω) (c : K) : algebraMap K Ω c ∈ ratioSub ev :=
  ⟨0, 1, by rw [pow_zero]; exact Submodule.mem_one.2 ⟨1, map_one _⟩, one_ne_zero,
    by rw [mul_one, pow_zero]; exact Submodule.mem_one.2 ⟨c, rfl⟩⟩

theorem div_mem_ratioSub (ev : V →ₗ[K] Ω) (v w : V) : ev v / ev w ∈ ratioSub ev := by
  by_cases hw : ev w = 0
  · rw [hw, div_zero]; exact zero_mem _
  · refine ⟨1, ev w, by rw [pow_one]; exact LinearMap.mem_range_self ev w, hw, ?_⟩
    rw [div_mul_cancel₀ _ hw, pow_one]; exact LinearMap.mem_range_self ev v

theorem isRatio_of_mem {ev : V →ₗ[K] Ω} {τ : ℕ} {t w : Ω} (hw : w ∈ LinearMap.range ev) (hw0 : w ≠ 0)
    (ht : t / w ^ τ ∈ ratioSub ev) : DegCmp.IsRatio ev τ t := by
  obtain ⟨e, h, m, n, p⟩ := ht
  refine ⟨e, h, m, n, ?_⟩
  have : t * h = w ^ τ * (t / w ^ τ * h) := by field_simp
  rw [this, pow_add]
  exact Submodule.mul_mem_mul (Submodule.pow_mem_pow _ hw τ) p

end Ratio

section Integral

variable {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]

theorem eval₂_mem_coneAlg (ev : V →ₗ[K] Ω) {r : ℕ} (v : Fin r → V) (g : MvPolynomial (Fin r) K) :
    eval₂ (Polynomial.C.comp (algebraMap K Ω)) (fun i => Polynomial.C (ev (v i)) * Polynomial.X) g ∈
      DegCmp.coneAlg ev := by
  induction g using MvPolynomial.induction_on with
  | C a =>
    rw [eval₂_C, RingHom.comp_apply, ← Polynomial.algebraMap_apply]
    exact Subalgebra.algebraMap_mem _ a
  | add p q hp hq => rw [eval₂_add]; exact add_mem hp hq
  | mul_X p i hp =>
    rw [eval₂_mul, eval₂_X]
    refine mul_mem hp ?_
    rw [mul_comm]
    exact Algebra.subset_adjoin ⟨v i, rfl⟩

theorem isIntDeg_of_eq {ev : V →ₗ[K] Ω} {r : ℕ} (v : Fin r → V) {τ : ℕ} {t : Ω} {n : ℕ}
    (c : Fin n → MvPolynomial (Fin r) K)
    (h : (Polynomial.C t * Polynomial.X ^ τ) ^ n + ∑ k, eval₂ (Polynomial.C.comp (algebraMap K Ω))
      (fun i => Polynomial.C (ev (v i)) * Polynomial.X) (c k) * (Polynomial.C t * Polynomial.X ^ τ) ^ (k : ℕ) = 0) :
    DegCmp.IsIntDeg ev τ t := by
  let c' : Fin n → DegCmp.coneAlg ev := fun k => ⟨_, eval₂_mem_coneAlg ev v (c k)⟩
  refine ⟨Polynomial.X ^ n + ∑ k : Fin n, Polynomial.C (c' k) * Polynomial.X ^ (k : ℕ),
    Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt c'), ?_⟩
  rw [mul_comm (Polynomial.X ^ τ)]
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_finset_sum, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_X_pow]
  exact h

end Integral

variable {k : Type} [Field k] (S : LinSys k)

theorem comb_single (i : Fin S.N) : S.comb (Pi.single i 1) = S.b i := by
  rw [LinSys.comb, Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, map_zero, zero_smul])
    (fun h => (h (Finset.mem_univ i)).elim), Pi.single_eq_same, map_one, one_smul]

theorem sec_eq_zero_of_generic [IsReduced S.Y] {η : S.Y} (hη : IsGenericPoint η Set.univ) {m : ℤ}
    (s : (lbZPow S.L m).Sec) (h : η ∉ nonzeroLocus s) : s = 0 := by
  refine zglobal_ext fun i => ?_
  rw [zfun_zero, ← basicOpen_eq_bot_iff, basicOpen_zfun, eq_bot_iff]
  intro y hy
  exact (h ((hη.mem_open_set_iff (nonzeroLocus s).isOpen).2 ⟨y, trivial, hy.2⟩)).elim

theorem growth_mono (D : ℕ) {r r' : ℕ → ℕ∞} (h : ∀ τ, r τ ≤ r' τ) : growth D r ≤ growth D r' :=
  limsup_le_limsup (Eventually.of_forall fun τ => by
    simp only
    gcongr
    exact h τ)

theorem finrank_le_toENat (R M : Type) [Field R] [AddCommGroup M] [Module R M] :
    (Module.finrank R M : ℕ∞) ≤ Cardinal.toENat (Module.rank R M) := by
  by_cases h : Module.Finite R M
  · rw [← Module.finrank_eq_rank]; simp
  · rw [Module.finrank_of_not_finite h]; simp

def powValLin {Ω : Type} [Field Ω] [Algebra k Ω] (x : S.Pt Ω) (m : ℕ) :
    letI : Module k (lbPow S.L m).Sec := Module.compHom _ (algebraMap k Γ(S.Y, ⊤))
    (lbPow S.L m).Sec →ₗ[k] Ω :=
  letI : Module k (lbPow S.L m).Sec := Module.compHom _ (algebraMap k Γ(S.Y, ⊤))
  { toFun := fun s => S.powVal (m := (m : ℤ)) x.1 s
    map_add' := fun s t => by
      change S.powVal x.1 (s + t) = S.powVal x.1 s + S.powVal x.1 t
      rw [LinSys.powVal, LinSys.powVal, LinSys.powVal, zfun_add]
      exact valR_add x.1 _ (S.le_chartAt x.1) _ _
    map_smul' := fun c s => by
      rw [RingHom.id_apply, Algebra.smul_def]
      have e : c • s = algebraMap k Γ(S.Y, ⊤) c • s := rfl
      change S.powVal x.1 (c • s) = _
      rw [e]
      rw [LinSys.powVal, LinSys.powVal, zfun_smul]
      exact (valR_mul x.1 _ (S.le_chartAt x.1) _ _).trans (congrArg (· * _)
        ((valR_res x.1 le_top (S.le_chartAt x.1) _).trans ((S.valR_algebraMap x.1 c).trans
          (congrFun (congrArg DFunLike.coe (LinSys.baseHom_ptOver x)) c)))) }

theorem rankGrowth_lineBundleSections_le_image_forms : ∀ (k : Type) [Field k] [CharZero k] (S : LinSys k), S.IsVariety → S.BasePointFree →
    S.Birational → growth S.D (fun m => (lbH0 k (lbPow S.L m) : ℕ∞)) ≤
      growth S.D (fun m => (Module.finrank k (quotPiece S.imageIdeal (m : ℤ)) : ℕ∞)) := by
  intro k _ _ S hS hb hbir
  obtain ⟨η, hη, hrat⟩ := hbir
  have : IsIntegral S.Y := HeightExists.isIntegral hS
  letI : Algebra k (S.Y.residueField η) := (S.baseHom (resPt η)).toAlgebra
  let x : S.Pt (S.Y.residueField η) := ⟨resPt η, S.comp_str _⟩
  have hx : IsGenericPoint (ptOf x.1) Set.univ := by rw [ptOf_resPt]; exact hη
  let b := Pi.basisFun k (Fin S.N)
  let ev := b.constr k (S.coords (resPt η))
  have hev : ∀ j, ev (b j) = S.coords (resPt η) j := fun j => b.constr_basis k _ j
  have hI : S.imageIdeal = imageIdeal ev b := by
    rw [imageIdeal_eq_coneIdeal_of_generic k _ S x hx 1 (S.coords (resPt η)) one_ne_zero (one_smul _ _).symm,
      CompHt.imageIdeal]
    exact congrArg _ (funext fun j => (hev j).symm)
  have hR : (fun m : ℕ => (Module.finrank k (quotPiece S.imageIdeal (m : ℤ)) : ℕ∞)) =
      fun m => DegCmp.hilb ev (1 * m) := by
    funext m
    rw [one_mul, hI, DegCmp.hilb_eq_finrank_quotPiece k _ _ ev S.N b m]
  rw [hR]
  letI (m : ℕ) : Module k (lbPow S.L m).Sec := Module.compHom _ (algebraMap k Γ(S.Y, ⊤))
  haveI (m : ℕ) : IsScalarTower k Γ(S.Y, ⊤) (lbPow S.L m).Sec := IsScalarTower.of_compHom _ _ _
  have hinj : ∀ m, Function.Injective (powValLin S x m) := fun m => by
    refine (injective_iff_map_eq_zero _).2 fun s hs => sec_eq_zero_of_generic S hη (m := (m : ℤ)) s fun hm => ?_
    rw [← ptOf_resPt η] at hm
    exact (S.powVal_ne_zero_iff (resPt η) s).2 hm hs
  refine le_trans (growth_mono S.D fun m => ?_)
    (ConeDeg.growth_rank_le ev S.D 1 le_rfl (fun m => LinearMap.range (powValLin S x m)) ?_)
  · rw [rank_range_of_injective _ (hinj m), lineBundleGlobalSectionsDim_eq_finrank]
    exact finrank_le_toENat _ _
  · intro m t ht
    obtain ⟨s, rfl⟩ := ht
    rw [one_mul]
    obtain ⟨j, hj⟩ := Function.ne_iff.1 (hb.coords_ne_zero (resPt η))
    have hyj : S.coords (resPt η) j ≠ 0 := hj
    refine ⟨?_, ?_⟩
    · obtain ⟨n, c, hc⟩ := isIntegral_coneRing_of_forall_valuationSubring k (S.Y.residueField η) (algebraMap k _)
        S.N m (S.coords (resPt η)) (powValLin S x m s) fun V hV => by
          obtain ⟨i, hi, hV'⟩ := LinSys.exists_ratio_mem_of_point S hS S.N m (fun i => Pi.single i 1) s
            (fun y => by
              obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hb.ge (Set.mem_univ y))
              exact ⟨i, by rw [comb_single]; exact hi⟩) (resPt η) V hV
          have e : S.val (resPt η) (S.comb (Pi.single i 1)) = S.coords (resPt η) i := by rw [comb_single]; rfl
          rw [e] at hi hV'
          exact ⟨i, hi, hV'⟩
      exact isIntDeg_of_eq b c (by simpa only [hev] using hc)
    · refine isRatio_of_mem ⟨b j, hev j⟩ hyj ?_
      have hle : S.ratioField (resPt η) ≤ ratioSub ev := Subfield.closure_le.2 (Set.union_subset
        (by rintro _ ⟨c, rfl⟩; exact algebraMap_mem_ratioSub ev c)
        (by rintro _ ⟨i, i', rfl⟩; rw [← hev i, ← hev i']; exact div_mem_ratioSub ev _ _))
      exact hle (hrat ▸ Subfield.mem_top _)

end GlobalTheory.SecGrowth
