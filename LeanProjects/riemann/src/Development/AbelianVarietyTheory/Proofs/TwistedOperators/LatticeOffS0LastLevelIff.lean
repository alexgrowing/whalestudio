import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TiltSc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneHomothetyCarriesSelfDualOfSplitComponentStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFrameFinitePartMulOfCarriesLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacuaStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FractionalIdealCompletionMulModulusOffExceptiona

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.RowShape.OffLat

variable {D : D7}

theorem latV_le_of_smul (S : HSp D) (L M : GlobalTheory.FinPl.Lat S) {v : GlobalTheory.FinPl.Pl D} {t : 𝓞 D.host.F} (ht : t ∉ v.asIdeal)
    (h : ∀ x ∈ L, algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t • x ∈ M) :
    GlobalTheory.FinPl.latV S L (· = v) ≤ GlobalTheory.FinPl.latV S M (· = v) := by
  unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul
  rw [AddSubgroup.closure_le]
  rintro y ⟨α, hα, hsupp, e, he, x, hx, rfl⟩
  rw [Set.mem_singleton_iff] at he
  subst he
  have ht0 : t ≠ 0 := fun h0 => ht (h0 ▸ v.asIdeal.zero_mem)
  have htF : (t : D.host.F) ≠ 0 := by exact_mod_cast ht0
  have hval : v.intValuation t = 1 :=
    le_antisymm (v.intValuation_le_one t) (not_lt.mp fun h => ht ((v.intValuation_lt_one_iff_mem t).mp h))
  have hcv : evalV D.host.F v (algebraMap D.host.F (Af D.host.F) (t : D.host.F)⁻¹) ∈
      v.adicCompletionIntegers D.host.F := by
    rw [AlgHom.commutes, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    change Valued.v ((((t : D.host.F)⁻¹ : D.host.F)) : v.adicCompletion D.host.F) ≤ 1
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀,
      show (t : D.host.F) = algebraMap (𝓞 D.host.F) D.host.F t from rfl,
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, hval, inv_one]
  apply AddSubgroup.subset_closure
  refine ⟨α * algebraMap D.host.F (Af D.host.F) (t : D.host.F)⁻¹, ?_, ?_, 1, rfl, _, h x hx, ?_⟩
  · intro w
    rw [map_mul]
    by_cases hw : w = v
    · subst hw
      exact Subring.mul_mem _ (hα w) hcv
    · rw [hsupp w hw, zero_mul]
      exact Subring.zero_mem _
  · intro w hw
    rw [map_mul, hsupp w hw, zero_mul]
  · funext i
    have hx' : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t • x i = (t : D.host.F) • x i := by
      rw [Algebra.smul_def, Algebra.smul_def]
      congr 1
    rw [Pi.smul_apply, one_mul, one_mul, hx', ← TensorProduct.smul_tmul]
    congr 1
    refine Prod.ext ?_ ?_
    · change (0 : InfiniteAdeleRing D.host.F) = (t : D.host.F) • (0 : InfiniteAdeleRing D.host.F)
      rw [smul_zero]
    · change α = (t : D.host.F) • (α * algebraMap D.host.F (Af D.host.F) (t : D.host.F)⁻¹)
      rw [Algebra.smul_def, mul_left_comm, ← map_mul, mul_inv_cancel₀ htF, map_one, mul_one]

theorem smul_mem_lat {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) {𝔟 𝔟' : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E}
    (r : 𝓞 D.host.E) (h : ∀ p, ∀ u ∈ 𝔟 p, r • u ∈ 𝔟' p) : ∀ x ∈ d.lat Λ 𝔟, r • x ∈ d.lat Λ 𝔟' := by
  intro x hx
  obtain ⟨y, hy, u, hu, rfl⟩ := hx
  refine ⟨r • y, Λ.smul_mem r hy, r • u, fun p => h p _ (hu p), ?_⟩
  rw [smul_add, Matrix.mulVec_smul, Matrix.mulVec_smul]

theorem smul_mem_of_mul {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (𝔟 : FractionalIdeal R⁰ K) {I J : Ideal R} {s : R} (hJ0 : J ≠ ⊥) (hJ : s ∈ J) {a b n : ℕ} (hn : b ≤ n) {u : K}
    (hu : u ∈ 𝔟 * (I : FractionalIdeal R⁰ K) ^ a * ((J : FractionalIdeal R⁰ K) ^ b)⁻¹) : s ^ n • u ∈ 𝔟 := by
  have hJb : ((J : FractionalIdeal R⁰ K) ^ b) ≠ 0 :=
    pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr hJ0)
  have hsb : algebraMap R K (s ^ b) ∈ (J : FractionalIdeal R⁰ K) ^ b := by
    rw [← FractionalIdeal.coeIdeal_pow, FractionalIdeal.mem_coeIdeal]
    exact ⟨s ^ b, Ideal.pow_mem_pow hJ b, rfl⟩
  have hprod := FractionalIdeal.mul_mem_mul hsb hu
  have hcancel : (J : FractionalIdeal R⁰ K) ^ b * (𝔟 * (I : FractionalIdeal R⁰ K) ^ a * ((J : FractionalIdeal R⁰ K) ^ b)⁻¹)
      = 𝔟 * (I : FractionalIdeal R⁰ K) ^ a := by
    rw [mul_comm, mul_assoc, inv_mul_cancel₀ hJb, mul_one]
  have hle : 𝔟 * (I : FractionalIdeal R⁰ K) ^ a ≤ 𝔟 :=
    mul_le_of_le_one_right' (pow_le_one' FractionalIdeal.coeIdeal_le_one _)
  have hb : s ^ b • u ∈ 𝔟 := by
    rw [Algebra.smul_def]
    exact hle (hcancel ▸ hprod)
  have hsplit : s ^ n • u = s ^ (n - b) • s ^ b • u := by
    rw [smul_smul, ← pow_add, Nat.sub_add_cancel hn]
  rw [hsplit]
  exact Submodule.smul_mem (𝔟 : Submodule R K) _ hb

theorem smul_mem_mul {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (𝔟 : FractionalIdeal R⁰ K) {I J : Ideal R} {s : R} (hI0 : I ≠ ⊥) (hJ0 : J ≠ ⊥) (hI : s ∈ I) {a b n : ℕ} (hn : a ≤ n)
    {u : K} (hu : u ∈ 𝔟) :
    s ^ n • u ∈ 𝔟 * (I : FractionalIdeal R⁰ K) ^ a * ((J : FractionalIdeal R⁰ K) ^ b)⁻¹ := by
  have hsa : algebraMap R K (s ^ a) ∈ (I : FractionalIdeal R⁰ K) ^ a := by
    rw [← FractionalIdeal.coeIdeal_pow, FractionalIdeal.mem_coeIdeal]
    exact ⟨s ^ a, Ideal.pow_mem_pow hI a, rfl⟩
  have hJb : ((J : FractionalIdeal R⁰ K) ^ b) ≠ 0 :=
    pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr hJ0)
  have hone : (1 : FractionalIdeal R⁰ K) ≤ ((J : FractionalIdeal R⁰ K) ^ b)⁻¹ := by
    have := FractionalIdeal.inv_anti_mono hJb one_ne_zero (pow_le_one' FractionalIdeal.coeIdeal_le_one _)
    simpa using this
  have hle : 𝔟 * (I : FractionalIdeal R⁰ K) ^ a ≤ 𝔟 * (I : FractionalIdeal R⁰ K) ^ a * ((J : FractionalIdeal R⁰ K) ^ b)⁻¹ :=
    le_mul_of_one_le_right' hone
  have ha : s ^ a • u ∈ 𝔟 * (I : FractionalIdeal R⁰ K) ^ a * ((J : FractionalIdeal R⁰ K) ^ b)⁻¹ := by
    rw [Algebra.smul_def, mul_comm (algebraMap R K (s ^ a)) u]
    exact hle (FractionalIdeal.mul_mem_mul hu hsa)
  have hsplit : s ^ n • u = s ^ (n - a) • s ^ a • u := by
    rw [smul_smul, ← pow_add, Nat.sub_add_cancel hn]
  rw [hsplit]
  exact Submodule.smul_mem ((𝔟 * (I : FractionalIdeal R⁰ K) ^ a * ((J : FractionalIdeal R⁰ K) ^ b)⁻¹ :
    FractionalIdeal R⁰ K) : Submodule R K) _ ha

end GlobalTheory.RowShape.OffLat

open GlobalTheory.RowShape.OffLat in

theorem GlobalTheory.RowShape.latV_grid_iff_rowN_zero : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (v : GlobalTheory.FinPl.Pl D), v ∉ G.pl.S0 → ∀ y : Fin (G.V (.grid D.R.m 0)).rank → AE D, (∀ i, y i ∈ idAt D (· = v)) → (y ∈ GlobalTheory.FinPl.latV _ (G.Λ (.grid D.R.m 0)) (· = v) ↔ y ∈ GlobalTheory.FinPl.latV _ (GlobalTheory.RowShape.rowN G 0) (· = v)) := by
  intro D T L sc G v hv y _
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hgrid : G.Λ (.grid D.R.m 0) =
      (G.rowDec 0 hm).lat (G.Λ (.top 0)) (stairId (G.pl.stA sc) (G.pl.stAbar sc) (D.R.m - 1 - 0)) :=
    G.sp.colLat D.R.m hm le_rfl
  have hrow : GlobalTheory.RowShape.rowN G 0 = (G.rowDec 0 hm).lat (G.Λ (.top 0)) (GlobalTheory.RowShape.rowId D 0) := by
    rw [GlobalTheory.RowShape.rowN, dif_pos hm]
  obtain ⟨s, hs, hsI⟩ := GlobalTheory.ModulUnit.exists_mem_modul G.pl sc hv
  obtain ⟨s', hs', hsJ⟩ := GlobalTheory.ModulUnit.exists_mem_modulBar G.pl sc hv
  have hinj : Function.Injective (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := by
    exact FaithfulSMul.algebraMap_injective _ _
  have hne : ∀ (I : Ideal (𝓞 D.host.E)) (r : 𝓞 D.host.F), r ∉ v.asIdeal →
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r ∈ I → I ≠ ⊥ := by
    intro I r hr hrI hI
    rw [hI, Ideal.mem_bot, ← map_zero (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))] at hrI
    exact hr (hinj hrI ▸ v.asIdeal.zero_mem)
  have hI0 := hne _ s hs hsI
  have hJ0 := hne _ s' hs' hsJ
  have hodd : ¬ Odd (0 : ℕ) := by simp
  have hid : ∀ p : Fin (D.R.m - 1 - 0), stairId (G.pl.stA sc) (G.pl.stAbar sc) (D.R.m - 1 - 0) p =
      GlobalTheory.RowShape.rowId D 0 p * ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ^ (p.1 + 1) *
        (((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ^ (D.R.m - 1 - 0 - p.1))⁻¹ := by
    intro p
    simp only [stairId, GlobalTheory.RowShape.rowId, GlobalTheory.RowShape.tiltSc, if_neg hodd, FractionalIdeal.spanSingleton_one,
      Places.stA, Places.stAbar, mul_pow, inv_pow, mul_inv, inv_inv, one_mul]
    ac_rfl
  have hA : ∀ x ∈ G.Λ (.grid D.R.m 0),
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (s' ^ (D.R.m - 1 - 0)) • x ∈ GlobalTheory.RowShape.rowN G 0 := by
    intro x hx
    rw [hgrid] at hx
    rw [hrow, map_pow]
    refine smul_mem_lat (G.rowDec 0 hm) (G.Λ (.top 0)) (𝔟 := stairId (G.pl.stA sc) (G.pl.stAbar sc) (D.R.m - 1 - 0))
      (𝔟' := GlobalTheory.RowShape.rowId D 0) _ ?_ x hx
    intro p u hu
    rw [hid p] at hu
    exact smul_mem_of_mul _ hJ0 hsJ (a := p.1 + 1) (b := D.R.m - 1 - 0 - p.1) (n := D.R.m - 1 - 0) (Nat.sub_le _ _) hu
  have hB : ∀ x ∈ GlobalTheory.RowShape.rowN G 0,
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (s ^ (D.R.m - 1 - 0)) • x ∈ G.Λ (.grid D.R.m 0) := by
    intro x hx
    rw [hrow] at hx
    rw [hgrid, map_pow]
    refine smul_mem_lat (G.rowDec 0 hm) (G.Λ (.top 0)) (𝔟 := GlobalTheory.RowShape.rowId D 0)
      (𝔟' := stairId (G.pl.stA sc) (G.pl.stAbar sc) (D.R.m - 1 - 0)) _ ?_ x hx
    intro p u hu
    rw [hid p]
    have hp := p.isLt
    exact smul_mem_mul _ hI0 hJ0 hsI (a := p.1 + 1) (b := D.R.m - 1 - 0 - p.1) (n := D.R.m - 1 - 0) (by omega) hu
  have hpow : ∀ r : 𝓞 D.host.F, r ∉ v.asIdeal → r ^ (D.R.m - 1 - 0) ∉ v.asIdeal :=
    fun r hr h => hr (v.isPrime.mem_of_pow_mem _ h)
  have h1 := latV_le_of_smul _ _ _ (hpow s' hs') hA
  have h2 := latV_le_of_smul _ _ _ (hpow s hs) hB
  exact ⟨fun h => h1 h, fun h => h2 h⟩
