import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DetIdealSelfDualLatticeAndInterStandard
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ArakelovDegreeEqDegreeOfFamily
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGramOneZero

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LatIndexDeg
open NumberField IsDedekindDomain ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.FlatCM
open scoped nonZeroDivisors

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem ιMulti_ne_zero_of_li {m : ℕ} (v : Fin m → V) (hv : LinearIndependent K v) :
    exteriorPower.ιMulti K m v ≠ 0 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Fintype.linearCombination K v)
    (LinearMap.ker_eq_bot.2 (LinearIndependent.fintypeLinearCombination_injective hv))
  intro h
  have := congrArg (exteriorPower.alternatingMapLinearEquiv
    ((Matrix.detRowAlternating : (Fin m → K) [⋀^Fin m]→ₗ[K] K).compLinearMap g)) h
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, map_zero] at this
  have hgv : ∀ i, g (v i) = Pi.single i 1 := by
    intro i
    have : v i = Fintype.linearCombination K v (Pi.single i 1) := by simp
    rw [this, ← LinearMap.comp_apply, hg, LinearMap.id_apply]
  have e : (fun i => g (v i)) = fun i => Pi.single i 1 := funext hgv
  change Matrix.det (Matrix.of fun i => g (v i)) = 0 at this
  rw [e, show (Matrix.of fun i : Fin m => (Pi.single i 1 : Fin m → K)) = 1 from by
        ext i j; simp [Matrix.one_apply, Pi.single_apply, eq_comm], Matrix.det_one] at this
  exact one_ne_zero this

omit [IsScalarTower (𝓞 K) K V] [Module (𝓞 K) V] in

theorem colon_smul_cancel (𝔞 : Ideal (𝓞 K)) (D : Submodule (𝓞 K) K)
    (hD : IsFractional (𝓞 K)⁰ D) (h0 : D ≠ ⊥) : (𝔞 • D).colon (D : Set K) = 𝔞 := by
  ext r
  rw [Submodule.mem_colon]
  constructor
  · intro h
    set Df : FractionalIdeal (𝓞 K)⁰ K := ⟨D, hD⟩
    have hDf : Df ≠ 0 := fun e => h0 (by
      have := congrArg (fun I : FractionalIdeal (𝓞 K)⁰ K => (I : Submodule (𝓞 K) K)) e
      simpa [Df] using this)
    have hmem : ∀ x ∈ 𝔞 • D, x ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K) * Df := by
      intro x hx
      refine Submodule.smul_induction_on hx ?_ ?_
      · intro a ha d hd
        rw [Algebra.smul_def]
        exact FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal _).2 ⟨a, ha, rfl⟩) hd
      · intro x y hx hy
        exact Submodule.add_mem (((𝔞 : FractionalIdeal (𝓞 K)⁰ K) * Df : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) hx hy
    have key : FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K r) * Df ≤
        (𝔞 : FractionalIdeal (𝓞 K)⁰ K) * Df := by
      rw [FractionalIdeal.mul_le]
      intro i hi j hj
      obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hi
      have h1 := hmem _ (h j hj)
      rw [smul_mul_assoc]
      refine Submodule.smul_mem _ a ?_
      rwa [Algebra.smul_def] at h1
    have key2 := mul_le_mul_left key Df⁻¹
    rw [mul_assoc, mul_assoc, mul_inv_cancel₀ hDf, mul_one, mul_one] at key2
    have hr := key2 (FractionalIdeal.mem_spanSingleton_self _ _)
    obtain ⟨x, hx, e⟩ := (FractionalIdeal.mem_coeIdeal _).1 hr
    rwa [← (FaithfulSMul.algebraMap_injective (𝓞 K) K) e]
  · intro hr s hs
    exact Submodule.smul_mem_smul hr hs

variable {m : ℕ}

variable (K) in

def coordMap (v : Fin m → V) : (Fin m → K) →ₗ[𝓞 K] V :=
  (Fintype.linearCombination K v).restrictScalars (𝓞 K)

theorem coordMap_apply (v : Fin m → V) (x : Fin m → K) : coordMap K v x = ∑ i, x i • v i := by
  simp [coordMap, Fintype.linearCombination_apply]

variable (K) in

def lineMap (ω : ⋀[K]^m V) : K →ₗ[𝓞 K] ⋀[K]^m V :=
  (LinearMap.toSpanSingleton K _ ω).restrictScalars (𝓞 K)

theorem lineMap_apply (ω : ⋀[K]^m V) (t : K) : lineMap K ω t = t • ω := rfl

theorem detSpan_map_coord (v : Fin m → V) (M' : Submodule (𝓞 K) (Fin m → K)) :
    detSpan K m (M'.map (coordMap K v)) =
      (GlobalTheory.BetaEx.detSpan M').map (lineMap K (exteriorPower.ιMulti K m v)) := by
  unfold detSpan GlobalTheory.BetaEx.detSpan
  rw [Submodule.map_span]
  congr 1
  ext w
  constructor
  · rintro ⟨y, hy, rfl⟩
    choose x hx hxy using fun i => Submodule.mem_map.1 (hy i)
    refine ⟨(Matrix.of x).det, (GlobalTheory.BetaEx.mem_detSet M' _).2 ⟨Matrix.of x, hx, rfl⟩, ?_⟩
    have e : y = fun i => ∑ j, (Matrix.of x) i j • v j := funext fun i => by
      rw [← hxy i, coordMap_apply]; rfl
    rw [lineMap_apply, e, GlobalTheory.FlatCM.Model.ιMulti_comb]
  · rintro ⟨d, hd, rfl⟩
    obtain ⟨x, hx, rfl⟩ := (GlobalTheory.BetaEx.mem_detSet M' d).1 hd
    refine ⟨fun i => coordMap K v (x i), fun i => Submodule.mem_map_of_mem (hx i), ?_⟩
    have e : (fun i => coordMap K v (x i)) = fun i => ∑ j, x i j • v j := funext fun i => by
      rw [coordMap_apply]
    rw [lineMap_apply, e, GlobalTheory.FlatCM.Model.ιMulti_comb]

omit [IsScalarTower (𝓞 K) K V] [Module (𝓞 K) V] in

theorem colon_map_of_injective {A B : Type} [AddCommGroup A] [Module (𝓞 K) A] [AddCommGroup B] [Module (𝓞 K) B]
    (f : A →ₗ[𝓞 K] B) (hf : Function.Injective f) (P Q : Submodule (𝓞 K) A) :
    (P.map f).colon ((Q.map f : Submodule (𝓞 K) B) : Set B) = P.colon (Q : Set A) := by
  ext r
  simp only [Submodule.mem_colon]
  constructor
  · intro h q hq
    have := h (f q) (Submodule.mem_map_of_mem hq)
    rw [← map_smul] at this
    obtain ⟨p, hp, e⟩ := Submodule.mem_map.1 this
    rwa [hf e] at hp
  · intro h b hb
    obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.1 hb
    rw [← map_smul]
    exact Submodule.mem_map_of_mem (h q hq)

omit [IsScalarTower (𝓞 K) K V] [Module (𝓞 K) V] in

theorem bdd_of_fg {M : Submodule (𝓞 K) (Fin m → K)} (hM : M.FG) : GlobalTheory.BetaEx.Bdd M := by
  classical
  obtain ⟨s, rfl⟩ := hM
  obtain ⟨⟨b, hb⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finset (𝓞 K)⁰
    (s.biUnion fun x => Finset.univ.image x)
  refine ⟨b, nonZeroDivisors.ne_zero hb, fun v hv => ?_⟩
  induction hv using Submodule.span_induction with
  | mem x hx =>
    rw [GlobalTheory.BetaEx.mem_std]
    intro j
    obtain ⟨c, hc⟩ := hint (x j) (Finset.mem_biUnion.2 ⟨x, hx, Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩⟩)
    exact ⟨c, hc⟩
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ a hx

theorem span_eq_of_latRank_eq [FiniteDimensional K V] {N L : Submodule (𝓞 K) V} (hNL : N ≤ L)
    (hr : latRank K L = latRank K N) :
    Submodule.span K (N : Set V) = Submodule.span K (L : Set V) :=
  Submodule.eq_of_le_of_finrank_eq (Submodule.span_mono hNL) hr.symm

omit [IsScalarTower (𝓞 K) K V] in

theorem fg_of_le_fg' {N L : Submodule (𝓞 K) V} (hNL : N ≤ L) (hL : L.FG) : N.FG := by
  have : IsNoetherian (𝓞 K) L := isNoetherian_of_fg_of_noetherian L hL
  have hfg := IsNoetherian.noetherian (N.comap L.subtype)
  have e : (N.comap L.subtype).map L.subtype = N := by
    rw [Submodule.map_comap_subtype, inf_eq_right.2 hNL]
  exact e ▸ hfg.map _

theorem relIndex_eq_absNorm_idx [FiniteDimensional K V] {N L : Submodule (𝓞 K) V} (hNL : N ≤ L) (hL : L.FG)
    (hrL : latRank K L = m) (hrN : latRank K N = m) :
    idx K m L N ≠ ⊥ ∧ N.toAddSubgroup.relIndex L.toAddSubgroup = Ideal.absNorm (idx K m L N) := by
  have hN : N.FG := fg_of_le_fg' hNL hL
  obtain ⟨v, hv⟩ : ∃ v : Fin m → V, IsFrame K N v := hrN ▸ exists_isFrame N hN
  have hspanv : Submodule.span K (Set.range v) = Submodule.span K (N : Set V) := by
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 hv.2.2)
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span (hv.1 i)
  have hLv : (L : Set V) ⊆ Submodule.span K (Set.range v) := by
    rw [hspanv, span_eq_of_latRank_eq hNL (hrL.trans hrN.symm)]
    exact Submodule.subset_span
  set ψ := coordMap K v with hψ
  have hinj : Function.Injective ψ := hv.2.1.fintypeLinearCombination_injective
  have hrange : L ≤ LinearMap.range ψ := by
    intro x hx
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 (hLv hx)
    exact ⟨c, by rw [coordMap_apply]; exact hc⟩
  set L' := L.comap ψ with hL'def
  set N' := N.comap ψ with hN'def
  have hL' : L'.map ψ = L := Submodule.map_comap_eq_self hrange
  have hN' : N'.map ψ = N := Submodule.map_comap_eq_self (hNL.trans hrange)
  have hNL' : N' ≤ L' := Submodule.comap_mono hNL
  have hstd : ∀ x : Fin m → K, (∀ j, ∃ b : 𝓞 K, (b : K) = x j) → x ∈ N' := by
    intro x hx
    choose b hb using hx
    change ψ x ∈ N
    rw [coordMap_apply]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [← hb j, algebraMap_smul]
    exact N.smul_mem _ (hv.1 j)
  have hLfg : L'.FG := Submodule.fg_of_fg_map_injective ψ hinj (hL' ▸ hL)
  have hb : GlobalTheory.BetaEx.Bdd L' := bdd_of_fg hLfg
  have hb' : GlobalTheory.BetaEx.Bdd (N' ⊔ L') := by rwa [sup_eq_right.2 hNL']
  have ht : ∀ x ∈ L', ∃ a : 𝓞 K, a ≠ 0 ∧ a • x ∈ N' := by
    intro x hx
    obtain ⟨k, hk, h⟩ := hb
    exact ⟨k, hk, hstd _ ((GlobalTheory.BetaEx.mem_std _).1 (h x hx))⟩
  obtain ⟨𝔞, h0, h1, -, h2⟩ := GlobalTheory.DetIdeal.exists_index_ideal_pair L' N' hLfg hb' ht
  rw [inf_eq_right.2 hNL'] at h1 h2
  have hω := ιMulti_ne_zero_of_li v hv.2.1
  have hℓ : Function.Injective (lineMap K (exteriorPower.ιMulti K m v)) :=
    fun s t e => smul_left_injective K hω e
  have hD0 : GlobalTheory.BetaEx.detSpan L' ≠ ⊥ := by
    intro e
    have h1m := GlobalTheory.BetaEx.det_mem (M := L') (1 : Matrix (Fin m) (Fin m) K) fun i => hNL' (hstd _ fun j =>
      ⟨if i = j then 1 else 0, by by_cases hij : i = j <;> simp [Matrix.one_apply, hij]⟩)
    rw [e, Matrix.det_one] at h1m
    exact one_ne_zero ((Submodule.mem_bot _).1 h1m)
  have hidx : idx K m L N = 𝔞 := by
    unfold idx
    rw [← hL', ← hN', detSpan_map_coord, detSpan_map_coord, colon_map_of_injective _ hℓ, h1]
    exact colon_smul_cancel 𝔞 _ (GlobalTheory.BetaEx.frac_of_bdd hb) hD0
  refine ⟨hidx ▸ h0, ?_⟩
  rw [hidx, h2]
  have e : L'.toAddSubgroup.map ψ.toAddMonoidHom = L.toAddSubgroup := by
    ext x
    rw [← hL']
    simp [Submodule.mem_map]
  rw [← e]
  exact (AddSubgroup.relIndex_comap N.toAddSubgroup ψ.toAddMonoidHom L'.toAddSubgroup).symm

end GlobalTheory.LatIndexDeg

namespace GlobalTheory.LatIndexDeg
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM

theorem deg_eq_deg_add_log_absNorm_idx : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : HermFam K V) (m : ℕ) (L N : Submodule (𝓞 K) V), N ≤ L → L.FG → latRank K L = m → latRank K N = m → idx K m L N ≠ ⊥ ∧ deg h L = deg h N + Real.log (Ideal.absNorm (idx K m L N)) / Module.finrank ℚ K := by
  intro K V _ _ _ _ _ _ _ h m L N hNL hL hrL hrN
  obtain ⟨hne, hidx⟩ := relIndex_eq_absNorm_idx hNL hL hrL hrN
  refine ⟨hne, ?_⟩
  have hN : N.FG := fg_of_le_fg' hNL hL
  have hspan : (L : Set V) ⊆ Submodule.span K (N : Set V) := by
    rw [span_eq_of_latRank_eq hNL (hrL.trans hrN.symm)]
    exact Submodule.subset_span
  rw [deg_of_le h hN hL hNL hspan, hidx]
  ring

end GlobalTheory.LatIndexDeg
