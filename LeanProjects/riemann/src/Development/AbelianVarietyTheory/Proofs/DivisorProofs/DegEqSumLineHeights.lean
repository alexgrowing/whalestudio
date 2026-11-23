import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LnStepFalse
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ArakelovDegreeEqDegreeOfFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexMapMulRelIndexKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramDetSnocTriangular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsLnRatioMetLe

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.HeightParts
open GlobalTheory.GradedNorm GlobalTheory.LieHt
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LieSmooth

namespace GlobalTheory.LatFlag

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem exists_smul_mem (E : Submodule (𝓞 K) V) {x : V} (hx : x ∈ Submodule.span K (E : Set V)) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ E := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨d, hd, hdy⟩ := hy
    obtain ⟨d', hd', hdz⟩ := hz
    refine ⟨d * d', mul_ne_zero hd hd', ?_⟩
    rw [smul_add]
    exact E.add_mem (by rw [mul_comm, mul_smul]; exact E.smul_mem _ hdy) (by rw [mul_smul]; exact E.smul_mem _ hdz)
  | smul b y _ hy =>
    obtain ⟨d, hd, hdy⟩ := hy
    obtain ⟨n, m, hm, hnm⟩ := IsFractionRing.div_surjective (A := 𝓞 K) b
    have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm
    have hmK : algebraMap (𝓞 K) K m ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hm
    refine ⟨d * m, mul_ne_zero hd hm0, ?_⟩
    have : (d * m) • (b • y) = n • (d • y) := by
      rw [← hnm, ← algebraMap_smul K (d * m), ← algebraMap_smul K n, ← algebraMap_smul K d, smul_smul, smul_smul,
        map_mul]
      congr 1
      field_simp
    rw [this]
    exact E.smul_mem _ hdy

theorem grIdeal_castSucc (E : Submodule (𝓞 K) V) {r : ℕ} (v : Fin (r + 1) → V) (j : Fin r) :
    grIdeal (E ⊓ (Submodule.span K (Set.range fun k : Fin r => v k.castSucc)).restrictScalars (𝓞 K))
      (fun k : Fin r => v k.castSucc) j = grIdeal E v j.castSucc := by
  ext b
  constructor
  · rintro ⟨c, rfl, h1, h2⟩
    refine ⟨Fin.snoc c 0, by simp, fun k hk => ?_, ?_⟩
    · induction k using Fin.lastCases with
      | last => simp
      | cast k => simp only [Fin.snoc_castSucc]; exact h1 k (Fin.castSucc_lt_castSucc_iff.1 hk)
    · rw [Fin.sum_univ_castSucc]
      simpa using h2.1
  · rintro ⟨c, rfl, h1, h2⟩
    have hl : c (Fin.last r) = 0 := h1 _ (Fin.castSucc_lt_last j)
    have hs : ∑ k, c k • v k = ∑ k : Fin r, c k.castSucc • v k.castSucc := by
      rw [Fin.sum_univ_castSucc, hl, zero_smul, add_zero]
    refine ⟨fun k => c k.castSucc, rfl, fun k hk => h1 _ (Fin.castSucc_lt_castSucc_iff.2 hk), Submodule.mem_inf.2 ⟨?_, ?_⟩⟩
    · rw [← hs]; exact h2
    · rw [Submodule.restrictScalars_mem]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem lineHt_castSucc (h : HermFam K V) (E : Submodule (𝓞 K) V) {r : ℕ} (v : Fin (r + 1) → V) (j : Fin r) :
    lineHt h (E ⊓ (Submodule.span K (Set.range fun k : Fin r => v k.castSucc)).restrictScalars (𝓞 K))
      (fun k : Fin r => v k.castSucc) j = lineHt h E v j.castSucc := by
  unfold lineHt
  rw [grIdeal_castSucc]
  congr 3

end GlobalTheory.LatFlag

namespace GlobalTheory.LatFlag

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem fg_of_le {E N : Submodule (𝓞 K) V} (hE : E.FG) (hN : N ≤ E) : N.FG := by
  haveI := isNoetherian_of_fg_of_noetherian E hE
  have h1 : (N.comap E.subtype).FG := IsNoetherian.noetherian _
  have := h1.map E.subtype
  rwa [Submodule.map_comap_subtype, inf_eq_right.2 hN] at this

theorem gram_det_smul (h : HermFam K V) (σ : K →+* ℂ) {n : ℕ} (e : Fin n → V) (d : Fin n → K) :
    (h.gram σ (fun j => d j • e j)).det.re = (∏ j, ‖σ (d j)‖ ^ 2) * (h.gram σ e).det.re := by
  have hfam : (fun j => d j • e j) = fun j => ∑ k, Matrix.diagonal d k j • e k := by
    funext j
    simp [Matrix.diagonal_apply, ite_smul]
  rw [hfam, GlobalTheory.hermFam_gram_matrix_change, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
  have hmap : ((Matrix.diagonal d).map σ).det = σ (Matrix.diagonal d).det := by
    rw [RingHom.map_det]; rfl
  rw [hmap, Matrix.det_diagonal]
  set z := σ (∏ j, d j)
  have hz : star z * (h.gram σ e).det * z = ((‖z‖ ^ 2 : ℝ) : ℂ) * (h.gram σ e).det := by
    rw [mul_comm (star z * _) z, ← mul_assoc, Complex.star_def, Complex.mul_conj']
    push_cast; ring
  rw [hz, Complex.re_ofReal_mul]
  simp only [z, map_prod, norm_prod, Finset.prod_pow]

theorem det_re_pos (h : HermFam K V) (σ : K →+* ℂ) {n : ℕ} (v : Fin n → V) (hv : LinearIndependent K v) :
    0 < (h.gram σ v).det.re :=
  (Complex.pos_iff.1 ((h.posDef σ _ v hv).det_pos)).1

theorem grSq_last (h : HermFam K V) (σ : K →+* ℂ) {r : ℕ} (v : Fin (r + 1) → V) (hv : LinearIndependent K v) :
    grSq (h.gram σ v) (Fin.last r) = (h.gram σ v).det.re / (h.gram σ fun j : Fin r => v j.castSucc).det.re := by
  rw [GlobalTheory.GradedCompare.grSq_eq (M := h.gram σ v) (h.posDef σ _ v hv), Fin.succ_last]
  rfl

end GlobalTheory.LatFlag

namespace GlobalTheory.LatFlag

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem deg_snoc (h : HermFam K V) (E : Submodule (𝓞 K) V) {r : ℕ} (v : Fin (r + 1) → V) (hE : E.FG)
    (hli : LinearIndependent K v) (hspan : Submodule.span K (E : Set V) = Submodule.span K (Set.range v)) :
    deg h E = deg h (E ⊓ (Submodule.span K (Set.range fun k : Fin r => v k.castSucc)).restrictScalars (𝓞 K)) +
      lineHt h E v (Fin.last r) := by
  classical
  set v0 : Fin r → V := fun k => v k.castSucc with hv0
  set S := Submodule.span K (Set.range v0) with hS
  set E' := E ⊓ S.restrictScalars (𝓞 K) with hE'
  have hmemE' : ∀ x, x ∈ E' ↔ x ∈ E ∧ x ∈ S := fun x => Iff.rfl
  have hE'E : E' ≤ E := inf_le_left
  have hE'fg : E'.FG := fg_of_le hE hE'E
  have hvE : ∀ k, v k ∈ Submodule.span K (E : Set V) := fun k => by
    rw [hspan]; exact Submodule.subset_span ⟨k, rfl⟩
  choose d hd0 hdE using fun k => exists_smul_mem E (hvE k)
  set dK : Fin (r + 1) → K := fun k => algebraMap (𝓞 K) K (d k) with hdK_def
  have hdK : ∀ k, dK k ≠ 0 := fun k h0 =>
    hd0 k (FaithfulSMul.algebraMap_injective (𝓞 K) K (by simpa [dK] using h0))
  have hdKE : ∀ k, dK k • v k ∈ E := fun k => by simpa [dK, algebraMap_smul] using hdE k

  obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Finsupp.lapply (Fin.last r)).comp hli.repr)
  have hgv : ∀ k, g (v k) = if k = Fin.last r then 1 else 0 := by
    intro k
    have := LinearMap.congr_fun hg ⟨v k, Submodule.subset_span ⟨k, rfl⟩⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, Finsupp.lapply_apply] at this
    rw [this, hli.repr_eq_single k _ rfl, Finsupp.single_apply]
  have hgsum : ∀ c : Fin (r + 1) → K, g (∑ k, c k • v k) = c (Fin.last r) := by
    intro c
    simp [map_sum, hgv]
  have hrep : ∀ x ∈ Submodule.span K (Set.range v), ∃ c : Fin (r + 1) → K, x = ∑ k, c k • v k := by
    intro x hx
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hx
    exact ⟨c, hc.symm⟩
  have hSg : ∀ x ∈ S, g x = 0 := by
    intro x hx
    have : S ≤ LinearMap.ker g := by
      rw [hS, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      simp [v0, hgv, Fin.castSucc_ne_last]
    exact this hx
  have hSS : ∀ x ∈ Submodule.span K (Set.range v), g x = 0 → x ∈ S := by
    intro x hx hx0
    obtain ⟨c, rfl⟩ := hrep x hx
    rw [hgsum] at hx0
    rw [Fin.sum_univ_castSucc, hx0, zero_smul, add_zero]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hEv : ∀ x ∈ E, x ∈ Submodule.span K (Set.range v) := fun x hx => hspan ▸ Submodule.subset_span hx
  set f : V →ₗ[𝓞 K] K := g.restrictScalars (𝓞 K) with hf_def
  have hf : ∀ x, f x = g x := fun x => rfl

  have hex : ∃ a ∈ grIdeal E v (Fin.last r), a ≠ 0 := by
    refine ⟨dK (Fin.last r), ⟨Pi.single (Fin.last r) (dK (Fin.last r)), by simp,
      fun k hk => absurd hk (not_lt.2 (Fin.le_last k)), ?_⟩, hdK _⟩
    simpa [Pi.single_apply, ite_smul] using hdKE (Fin.last r)
  set a := hex.choose with ha_def
  obtain ⟨haI, ha0⟩ := hex.choose_spec
  rw [← ha_def] at haI ha0
  obtain ⟨c, hca, -, hcE⟩ := haI
  set w := ∑ k, c k • v k with hw_def
  have hgw : g w = a := by rw [hgsum, hca]
  have hwv : w ∈ Submodule.span K (Set.range v) :=
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hmapE : E.map f = grIdeal E v (Fin.last r) := by
    ext b
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨c', rfl⟩ := hrep x (hEv x hx)
      exact ⟨c', by rw [hf, hgsum], fun k hk => absurd hk (not_lt.2 (Fin.le_last k)), hx⟩
    · rintro ⟨c', rfl, -, hc'⟩
      exact ⟨_, hc', by rw [hf, hgsum]⟩

  set u : Fin r → V := fun j => dK j.castSucc • v0 j with hu_def
  have huS : ∀ j, u j ∈ S := fun j => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hli0 : LinearIndependent K v0 := hli.comp Fin.castSucc (Fin.castSucc_injective _)
  have huli : LinearIndependent K u := by
    have := hli0.units_smul (fun j => Units.mk0 (dK j.castSucc) (hdK _))
    convert this using 1
    ext j : 1
    simp [u, Units.smul_def]
  have hSu : S ≤ Submodule.span K (Set.range u) := by
    rw [hS, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have : v0 j = (dK j.castSucc)⁻¹ • u j := by
      simp [u, smul_smul, inv_mul_cancel₀ (hdK _)]
    show v0 j ∈ _
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have huS' : Submodule.span K (Set.range u) ≤ S := by
    rw [Submodule.span_le]; rintro _ ⟨j, rfl⟩; exact huS j
  have hu : IsFrame K E' u :=
    ⟨fun j => (hmemE' _).2 ⟨hdKE _, huS j⟩, huli, fun x hx => hSu ((hmemE' x).1 hx).2⟩
  set v' : Fin (r + 1) → V := Fin.snoc u w with hv'_def
  have hv' : IsFrame K E v' := by
    refine ⟨fun k => ?_, ?_, fun x hx => ?_⟩
    · induction k using Fin.lastCases with
      | last => simpa [v'] using hcE
      | cast j => simpa [v'] using hE'E (hu.1 j)
    · refine linearIndependent_finSnoc.2 ⟨huli, fun hmem => ha0 ?_⟩
      rw [← hgw]; exact hSg _ (huS' hmem)
    · have hy : x - (g x / a) • w ∈ S := by
        refine hSS _ (Submodule.sub_mem _ (hEv x hx) (Submodule.smul_mem _ _ hwv)) ?_
        simp [hgw, div_mul_cancel₀ _ ha0]
      rw [SetLike.mem_coe, show v' = Fin.snoc u w from rfl, Fin.range_snoc, Submodule.mem_span_insert]
      exact ⟨g x / a, x - (g x / a) • w, hSu hy, by abel⟩

  set U := Submodule.span (𝓞 K) (Set.range u) with hU_def
  set U' := Submodule.span (𝓞 K) (Set.range v') with hU'_def
  have hUS : ∀ z ∈ U, z ∈ S := fun z hz =>
    (Submodule.span_le (p := S.restrictScalars (𝓞 K))).2 (by rintro _ ⟨j, rfl⟩; exact huS j) hz
  have hU'E : U' ≤ E := Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hv'.1 k)
  have hmapU' : U'.map f = Submodule.span (𝓞 K) {a} := by
    rw [hU'_def, Submodule.map_span, hv'_def, Fin.range_snoc, Set.image_insert_eq]
    have hfw : f w = a := by rw [hf, hgw]
    rw [hfw]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ (rfl | ⟨_, ⟨j, rfl⟩, rfl⟩)
      · exact Submodule.subset_span rfl
      · rw [SetLike.mem_coe, hf, hSg _ (huS j)]; exact zero_mem _
    · exact Submodule.span_mono (Set.singleton_subset_iff.2 (Set.mem_insert _ _))
  have hU'ker : U' ⊓ LinearMap.ker f = U := by
    apply le_antisymm
    · rintro x ⟨hx, hxk⟩
      rw [hU'_def, hv'_def, Fin.range_snoc] at hx
      rw [SetLike.mem_coe, Submodule.mem_span_insert] at hx
      obtain ⟨b, z, hz, rfl⟩ := hx
      have hz0 : f z = 0 := by rw [hf]; exact hSg _ (hUS z hz)
      have hba : b • a = 0 := by
        have := LinearMap.mem_ker.1 hxk
        rwa [map_add, map_smul, hf w, hgw, hz0, add_zero] at this
      rw [(smul_eq_zero.1 hba).resolve_right ha0, zero_smul, zero_add]
      exact hz
    · refine le_inf ?_ fun z hz => LinearMap.mem_ker.2 (by rw [hf]; exact hSg _ (hUS z hz))
      rw [hU_def, hU'_def]
      refine Submodule.span_mono ?_
      rintro _ ⟨j, rfl⟩
      exact ⟨j.castSucc, by simp [v']⟩
  have hEker : E ⊓ LinearMap.ker f = E' := by
    apply le_antisymm
    · rintro x ⟨hx, hxk⟩
      exact (hmemE' x).2 ⟨hx, hSS _ (hEv x hx) (by rw [← hf x]; exact LinearMap.mem_ker.1 hxk)⟩
    · exact le_inf hE'E fun z hz => LinearMap.mem_ker.2 (by rw [hf]; exact hSg _ ((hmemE' z).1 hz).2)
  have hidx : U'.toAddSubgroup.relIndex E.toAddSubgroup =
      (Submodule.span (𝓞 K) {a}).toAddSubgroup.relIndex (grIdeal E v (Fin.last r)).toAddSubgroup *
        U.toAddSubgroup.relIndex E'.toAddSubgroup := by
    rw [GlobalTheory.submodule_relIndex_split f U' E hU'E, hmapU', hU'ker, hEker, hmapE]
  have hne' := hv'.relIndex_ne_zero hE
  have hne := hu.relIndex_ne_zero hE'fg
  have hne1 : (Submodule.span (𝓞 K) {a}).toAddSubgroup.relIndex (grIdeal E v (Fin.last r)).toAddSubgroup ≠ 0 := by
    intro h0; apply hne'; rw [← hU'_def, hidx, h0, zero_mul]

  have hG1 : ∀ σ : K →+* ℂ, (h.gram σ v').det.re =
      (∏ j : Fin r, ‖σ (dK j.castSucc)‖ ^ 2) * ‖σ a‖ ^ 2 * (h.gram σ v).det.re := by
    intro σ
    rw [hv'_def, hw_def, ← hca]
    exact GlobalTheory.hermFam_gram_det_triangular h σ v (fun j => dK j.castSucc) c
  have hG0 : ∀ σ : K →+* ℂ, (h.gram σ u).det.re =
      (∏ j : Fin r, ‖σ (dK j.castSucc)‖ ^ 2) * (h.gram σ v0).det.re := fun σ =>
    gram_det_smul h σ v0 (fun j => dK j.castSucc)
  have hP : ∀ σ : K →+* ℂ, 0 < ∏ j : Fin r, ‖σ (dK j.castSucc)‖ ^ 2 := fun σ =>
    Finset.prod_pos fun j _ => by
      have : σ (dK j.castSucc) ≠ 0 := (map_ne_zero σ).2 (hdK _)
      positivity
  have hA : ∀ σ : K →+* ℂ, 0 < ‖σ a‖ := fun σ => norm_pos_iff.2 ((map_ne_zero σ).2 ha0)
  have hkey : ∀ σ : K →+* ℂ, Real.log (h.gram σ v').det.re =
      Real.log (h.gram σ u).det.re + 2 * Real.log ‖σ a‖ + Real.log (grSq (h.gram σ v) (Fin.last r)) := by
    intro σ
    have p1 := det_re_pos h σ v hli
    have p0 := det_re_pos h σ v0 hli0
    rw [hG1, hG0, grSq_last h σ v hli, Real.log_div p1.ne' p0.ne',
      Real.log_mul (by have := hP σ; have := hA σ; positivity) p1.ne',
      Real.log_mul (hP σ).ne' (by have := hA σ; positivity), Real.log_pow,
      Real.log_mul (hP σ).ne' p0.ne']
    push_cast; ring
  rw [arakelovDegree_eq_degreeOfFamily h hE hv', arakelovDegree_eq_degreeOfFamily h hE'fg hu]
  unfold degreeOfFamily lineHt idealLog
  rw [dif_pos hex, ← ha_def, ← hU'_def, ← hU_def, hidx, Nat.cast_mul,
    Real.log_mul (by exact_mod_cast hne1) (by exact_mod_cast hne)]
  simp only [hkey, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end GlobalTheory.LatFlag

namespace GlobalTheory.LatFlag

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem deg_eq_sum_lineHt_of_span (h : HermFam K V) :
    ∀ (r : ℕ) (E : Submodule (𝓞 K) V) (v : Fin r → V), E.FG → LinearIndependent K v →
      Submodule.span K (E : Set V) = Submodule.span K (Set.range v) → deg h E = ∑ i, lineHt h E v i := by
  intro r
  induction r with
  | zero =>
    intro E v hE hli hspan
    have hE0 : E = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have : x ∈ Submodule.span K (Set.range v) := hspan ▸ Submodule.subset_span hx
      rw [Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot] at this
      exact (Submodule.mem_bot _).2 this
    have hv : IsFrame K E v := ⟨fun i => i.elim0, hli, fun x hx => hspan ▸ Submodule.subset_span hx⟩
    rw [arakelovDegree_eq_degreeOfFamily h hE hv, Finset.univ_eq_empty, Finset.sum_empty]
    unfold degreeOfFamily
    have hU : Submodule.span (𝓞 K) (Set.range v) = E := by
      rw [hE0, Set.range_eq_empty, Submodule.span_empty]
    rw [hU, AddSubgroup.relIndex_self]
    simp [Matrix.det_fin_zero]
  | succ r ih =>
    intro E v hE hli hspan
    set v0 : Fin r → V := fun k => v k.castSucc with hv0
    set E' := E ⊓ (Submodule.span K (Set.range v0)).restrictScalars (𝓞 K) with hE'
    have hE'fg : E'.FG := fg_of_le hE inf_le_left
    have hli0 : LinearIndependent K v0 := hli.comp Fin.castSucc (Fin.castSucc_injective _)
    have hspan0 : Submodule.span K (E' : Set V) = Submodule.span K (Set.range v0) := by
      apply le_antisymm
      · rw [Submodule.span_le]
        intro x hx
        exact hx.2
      · rw [Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        have hvE : v j.castSucc ∈ Submodule.span K (E : Set V) := by
          rw [hspan]; exact Submodule.subset_span ⟨_, rfl⟩
        obtain ⟨d, hd, hdE⟩ := exists_smul_mem E hvE
        have hdK : algebraMap (𝓞 K) K d ≠ 0 := fun h0 =>
          hd (FaithfulSMul.algebraMap_injective (𝓞 K) K (by simpa using h0))
        have hmem : algebraMap (𝓞 K) K d • v0 j ∈ E' := by
          refine Submodule.mem_inf.2 ⟨by simpa [algebraMap_smul] using hdE, ?_⟩
          rw [Submodule.restrictScalars_mem]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
        have : v0 j = (algebraMap (𝓞 K) K d)⁻¹ • (algebraMap (𝓞 K) K d • v0 j) := by
          rw [smul_smul, inv_mul_cancel₀ hdK, one_smul]
        show v0 j ∈ _
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
    rw [deg_snoc h E v hE hli hspan, ih E' v0 hE'fg hli0 hspan0, Fin.sum_univ_castSucc]
    congr 1
    exact Finset.sum_congr rfl fun j _ => lineHt_castSucc h E v j

theorem deg_eq_sum_lineHt : ∀ (K : Type) [Field K] [NumberField K] (V : Type) [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : HermFam K V) (E : Submodule (𝓞 K) V) (r : ℕ) (v : Fin r → V),
    E.FG → LinearIndependent K v → Submodule.span K (E : Set V) = Submodule.span K (Set.range v) →
      deg h E = ∑ i, lineHt h E v i :=
  fun _ _ _ _ _ _ _ _ h E r v hE hli hspan => deg_eq_sum_lineHt_of_span h r E v hE hli hspan

end GlobalTheory.LatFlag
