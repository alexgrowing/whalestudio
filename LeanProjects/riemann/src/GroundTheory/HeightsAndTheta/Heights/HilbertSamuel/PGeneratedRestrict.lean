import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGeneratedRestrict
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace GeneratedRestrict

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]

abbrev locMap {M N : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] [AddCommGroup N]
    [Module (MRingOver S ι) N] (T : Submonoid (MRingOver S ι)) (g : M →ₗ[MRingOver S ι] N) :
    LocalizedModule T M →ₗ[MRingOver S ι] LocalizedModule T N :=
  IsLocalizedModule.map T (LocalizedModule.mkLinearMap T M) (LocalizedModule.mkLinearMap T N) g

section General

variable {M N : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] [AddCommGroup N]
    [Module (MRingOver S ι) N]

theorem locMap_mk (T : Submonoid (MRingOver S ι)) (g : M →ₗ[MRingOver S ι] N) (m : M) (t : T) :
    locMap T g (LocalizedModule.mk m t) = LocalizedModule.mk (g m) t := by
  rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.map_mk', ← IsLocalizedModule.mk_eq_mk']

theorem locMap_cellRes (g : M →ₗ[MRingOver S ι] N) (J I : ∀ k, Finset (ι k))
    (x : LocalizedModule (KH.cellMon S J) M) :
    locMap (KH.cellMon S I) g (KH.cellRes S M J I x) = KH.cellRes S N J I (locMap (KH.cellMon S J) g x) := by
  by_cases h : KH.cellMon S J ≤ KH.cellMon S I
  · induction x using LocalizedModule.induction_on with
    | h m t =>
      rw [GenTwistGenerated.cellRes_mk h, locMap_mk, locMap_mk, GenTwistGenerated.cellRes_mk h]
  · unfold KH.cellRes
    rw [dif_neg h, dif_neg h]
    simp

end General

variable {V W : Ideal (MRingOver S ι)}

abbrev quotMap (hVW : V ≤ W) : (MRingOver S ι ⧸ V) →ₗ[MRingOver S ι] (MRingOver S ι ⧸ W) :=
  (Ideal.Quotient.factorₐ (MRingOver S ι) hVW).toLinearMap

theorem quotMap_mul (hVW : V ≤ W) (x y : MRingOver S ι ⧸ V) :
    quotMap hVW (x * y) = quotMap hVW x * quotMap hVW y := by
  simp [quotMap]

theorem quotMap_smul (hVW : V ≤ W) (s : S) (x : MRingOver S ι ⧸ V) :
    quotMap hVW (s • x) = s • quotMap hVW x :=
  LinearMap.map_smul_of_tower _ s x

theorem locMap_smul (hVW : V ≤ W) (T : Submonoid (MRingOver S ι)) (s : S)
    (x : LocalizedModule T (MRingOver S ι ⧸ V)) :
    locMap T (quotMap hVW) (s • x) = s • locMap T (quotMap hVW) x := by
  induction x using LocalizedModule.induction_on with
  | h m t =>
    rw [LocalizedModule.smul'_mk, locMap_mk, locMap_mk, LocalizedModule.smul'_mk, quotMap_smul]

theorem locMap_mul (hVW : V ≤ W) (T : Submonoid (MRingOver S ι)) (x y : LocalizedModule T (MRingOver S ι ⧸ V)) :
    locMap T (quotMap hVW) (x * y) = locMap T (quotMap hVW) x * locMap T (quotMap hVW) y := by
  induction x using LocalizedModule.induction_on with
  | h m t =>
    induction y using LocalizedModule.induction_on with
    | h m' t' =>
      rw [LocalizedModule.mk_mul_mk, locMap_mk, locMap_mk, locMap_mk, LocalizedModule.mk_mul_mk, quotMap_mul]

theorem locMap_one (hVW : V ≤ W) (T : Submonoid (MRingOver S ι)) :
    locMap T (quotMap hVW) (1 : LocalizedModule T (MRingOver S ι ⧸ V)) = 1 := by
  have e : ∀ (P : Type) [CommRing P] [Algebra (MRingOver S ι) P],
      (1 : LocalizedModule T P) = LocalizedModule.mk 1 1 := fun _ _ _ => OreLocalization.one_def
  have h1 : quotMap hVW (1 : MRingOver S ι ⧸ V) = 1 := by simp [quotMap]
  rw [e, e, locMap_mk, h1]

theorem cechD_cechMap {M N : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] [AddCommGroup N]
    [Module (MRingOver S ι) N] (g : M →ₗ[MRingOver S ι] N) (n : ℕ) (f : KH.CechC S ι M n) :
    KH.cechD S ι N n (KH.cechMap S ι g n f) = KH.cechMap S ι g (n + 1) (KH.cechD S ι M n f) := by
  funext I
  simp only [KH.cechD, KH.cechMap, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · exact (congrArg (fun y => KH.faceSign I.1 k i • y) (locMap_cellRes g _ I.1 (f ⟨_, h⟩))).symm.trans
      (map_zsmul (locMap (KH.cellMon S I.1) g) _ _).symm
  · simp

theorem quotMap_mem_quotPart (hVW : V ≤ W) {c : K → ℤ} {x : MRingOver S ι ⧸ V}
    (hx : x ∈ KH.quotPart S V c) : quotMap hVW x ∈ KH.quotPart S W c := by
  unfold KH.quotPart at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, rfl⟩ := hx
    exact Submodule.subset_span ⟨p, hp, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul s x _ hx => rw [quotMap_smul]; exact Submodule.smul_mem _ s hx

theorem locMap_mem_locPart (hVW : V ≤ W) (T : Submonoid (MRingOver S ι)) {c : K → ℤ}
    {x : LocalizedModule T (MRingOver S ι ⧸ V)} (hx : x ∈ KH.locPart ι (KH.quotPart S V) T c) :
    locMap T (quotMap hVW) x ∈ KH.locPart ι (KH.quotPart S W) T c := by
  unfold KH.locPart at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, t, a, ht, hm, rfl⟩ := hx
    rw [locMap_mk]
    exact GenTwistGenerated.mk_mem_locPart _ t a ht (quotMap_mem_quotPart hVW hm)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul s x _ hx => rw [locMap_smul]; exact Submodule.smul_mem _ s hx

end GeneratedRestrict

open GeneratedRestrict in

theorem GeneratedRestrict.proof : GeneratedRestrict.Statement := by
  intro S _ K _ _ ι _ _ V W a hVW hV I
  obtain ⟨r, z, u, hz, hu, h1⟩ := hV I
  refine ⟨r, fun j => KH.cechMap S ι (quotMap hVW) 0 (z j), fun j => locMap _ (quotMap hVW) (u j),
    fun j => ?_, fun j => locMap_mem_locPart hVW _ (hu j), ?_⟩
  · obtain ⟨hzc, hzd⟩ := hz j
    refine GenTwistGenerated.mem_cechZc_zero (fun J => ?_) ?_
    · exact locMap_mem_locPart hVW _ ((Submodule.mem_pi.mp hzc) J (Set.mem_univ _))
    · rw [cechD_cechMap, LinearMap.mem_ker.mp hzd, map_zero]
  · have hc : ∀ j, KH.cechMap S ι (quotMap hVW) 0 (z j) I = locMap _ (quotMap hVW) (z j I) := fun j => rfl
    simp only [hc, ← locMap_mul, ← map_sum, h1, locMap_one]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
