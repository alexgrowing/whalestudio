import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionLowerHeight
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericTrivialisationSectionAndPullback

namespace PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_nef

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ZH GlobalTheory.ZH.RatModel

theorem isNef_of_small {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (hX : IsArithVar p D)
    (L : HermLB p) (hs : L.SemiPos D) {ι : Type} [Finite ι] (u : ι → L.B.Sec) (hu : ∀ i, u i ∈ L.smallSec)
    (hg : ⨆ i, nonzeroLocus (u i) = ⊤) : L.IsNef D where
  semiPos := hs
  vertical := GlobalTheory.TrueGeo.OfLattice.nefFib_of_isGenerated hX L (isGenerated_of_finite u hg)
  horizontal Z i _ _ _ hc hd := by
    have hZ : IsArithVar (i ≫ p) 0 := hX.of_isClosedImmersion i hc hd
    have hm : i (genericPoint Z) ∈ ⨆ a, nonzeroLocus (u a) := by rw [hg]; trivial
    obtain ⟨a, ha⟩ := Opens.mem_iSup.1 hm
    have hgen : genericPoint Z ∈ nonzeroLocus (GlobalTheory.secPull (u a) i) := by
      rw [GlobalTheory.nonzeroLocus_secPull]; exact ha
    have h0 : ∀ σ (y : CxPts (i ≫ p) σ), y ∈ ptsIn _ σ (nonzeroLocus (GlobalTheory.secPull (u a) i)) := fun σ y => by
      refine mem_ptsIn.2 ?_
      have key : ∀ y : Sp ℂ ⟶ Z, y (IsLocalRing.closedPoint ℂ) = genericPoint Z := fun y =>
        GlobalTheory.HtSelfInter.eq_genericPoint hZ (Scheme.SpecToEquivOfField ℂ Z y).2.hom.charZero
      rw [key]
      exact hgen
    refine ⟨_, isRatSec_ratOfSec _ hgen, ?_⟩
    rw [HermLB.curveDeg_sec i (u a) hgen h0]
    refine sub_nonneg.2 (le_trans (b := 0) ?_ ?_)
    · refine finsum_induction (· ≤ (0 : ℝ)) le_rfl (fun _ _ => add_nonpos) fun σ =>
        finsum_induction (· ≤ (0 : ℝ)) le_rfl (fun _ _ => add_nonpos) fun y => ?_
      refine div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos ?_ (hu a σ _)) zero_le_two
      unfold Weight.nsq
      positivity
    · exact finsum_nonneg fun z =>
        mul_nonneg (Int.cast_nonneg (mult_divOfSec_nonneg z)) (Real.log_natCast_nonneg _)

variable {K V Ω : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
  {M : RatModel (𝓞 K) Ω}

theorem const_val {σ : K →+* ℂ} {y : Sp ℂ ⟶ M.Z} (hy : y ≫ M.s = spMap (σ.comp (algebraMap (𝓞 K) K))) (a : K) :
    algebraMap K Ω a ∈ M.O (y (IsLocalRing.closedPoint ℂ)) ∧ M.val y (algebraMap K Ω a) = σ a := by
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) a
  have hr := range_eq_singleton y (IsLocalRing.closedPoint ℂ)
  have hq0 : algebraMap (𝓞 K) K q ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
  have hσq : σ (algebraMap (𝓞 K) K q) ≠ 0 := (map_ne_zero σ).2 hq0
  have hv := fun c => val_algebraMap hy c
  have hu : IsUnit (⟨algebraMap (𝓞 K) Ω q, Subalgebra.algebraMap_mem _ q⟩ :
      M.O (y (IsLocalRing.closedPoint ℂ))) := (val_ne_zero_iff hr _).1 (by rw [hv]; exact hσq)
  obtain ⟨h0, hi⟩ := (isUnit_O_iff _).1 hu
  dsimp only at h0 hi
  have e : algebraMap K Ω (algebraMap (𝓞 K) K p / algebraMap (𝓞 K) K q) =
      algebraMap (𝓞 K) Ω p * (algebraMap (𝓞 K) Ω q)⁻¹ := by
    rw [map_div₀, div_eq_mul_inv, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hm : algebraMap (𝓞 K) Ω p * (algebraMap (𝓞 K) Ω q)⁻¹ ∈ M.O (y (IsLocalRing.closedPoint ℂ)) :=
    mul_mem (Subalgebra.algebraMap_mem _ p) hi
  rw [e]
  refine ⟨hm, ?_⟩
  have h1 := val_mul (specializes_of_range_eq hr) hm (Subalgebra.algebraMap_mem _ q)
  rw [inv_mul_cancel_right₀ h0, hv, hv] at h1
  rw [map_div₀, eq_div_iff hσq]
  exact h1.symm

theorem exists_coord {σ : K →+* ℂ} {y : Sp ℂ ⟶ M.Z} (hy : y ≫ M.s = spMap (σ.comp (algebraMap (𝓞 K) K)))
    (ev : V →ₗ[K] Ω) (c : Ω) {N : ℕ} (b : Module.Basis (Fin N) K V) {S : Set V} (hS : Submodule.span K S = ⊤)
    (hc : ∀ v ∈ S, ev v / c ∈ M.O (y (IsLocalRing.closedPoint ℂ))) :
    ∃ x : Fin N → ℂ, ∀ v, M.val y (ev v / c) = ∑ j, σ (b.repr v j) * x j := by
  have hr := specializes_of_range_eq (range_eq_singleton y (IsLocalRing.closedPoint ℂ))
  have hsm : ∀ (a : K) v, ev (a • v) / c = algebraMap K Ω a * (ev v / c) := fun a v => by
    rw [map_smul, Algebra.smul_def, mul_div_assoc]
  have hall : ∀ v, ev v / c ∈ M.O (y (IsLocalRing.closedPoint ℂ)) := fun v => by
    have hv : v ∈ Submodule.span K S := hS ▸ trivial
    induction hv using Submodule.span_induction with
    | mem _ h => exact hc _ h
    | zero => rw [map_zero, zero_div]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add, add_div]; exact add_mem ha hb
    | smul a v _ hv => rw [hsm]; exact mul_mem (const_val hy a).1 hv
  let ℓ : V →+ ℂ :=
    { toFun := fun v => M.val y (ev v / c)
      map_zero' := by rw [map_zero, zero_div]; exact val_zero y
      map_add' := fun a b => by rw [map_add, add_div]; exact val_add hr (hall a) (hall b) }
  refine ⟨fun j => ℓ (b j), fun v => ?_⟩
  change ℓ v = _
  conv_lhs => rw [← b.sum_repr v, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  change M.val y _ = _
  rw [hsm, val_mul hr (const_val hy _).1 (hall _), (const_val hy _).2]
  rfl

omit [NumberField K] in

theorem mem_O_of_span [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (ev : V →ₗ[K] Ω) (c : Ω) {z : M.Z} {S : Set V}
    (hc : ∀ v ∈ S, ev v / c ∈ M.O z) {v : V} (hv : v ∈ Submodule.span (𝓞 K) S) : ev v / c ∈ M.O z := by
  induction hv using Submodule.span_induction with
  | mem _ h => exact hc _ h
  | zero => rw [map_zero, zero_div]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add, add_div]; exact add_mem ha hb
  | smul a v _ hv =>
    rw [← algebraMap_smul K a v, map_smul, Algebra.smul_def, mul_div_assoc, ← IsScalarTower.algebraMap_apply]
    exact mul_mem (Subalgebra.algebraMap_mem _ a) hv

omit [NumberField K] in

theorem exists_isUnit (ev : V →ₗ[K] Ω) (c : Ω) {z : M.Z} {ι : Type} (w : ι → V)
    (hc : ∀ i, ev (w i) / c ∈ M.O z) {v : V} (hv : v ∈ Submodule.span ℤ (Set.range w)) (h : ev v / c ∈ M.O z)
    (hu : IsUnit (⟨_, h⟩ : M.O z)) : ∃ i, IsUnit (⟨_, hc i⟩ : M.O z) := by
  by_contra hn
  have key : ∃ a ∈ IsLocalRing.maximalIdeal (M.O z), (a : Ω) = ev v / c := by
    clear hu h
    induction hv using Submodule.span_induction with
    | mem _ h => obtain ⟨i, rfl⟩ := h; exact ⟨⟨_, hc i⟩, fun h => hn ⟨i, h⟩, rfl⟩
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨a', ha, ea⟩ := ha
      obtain ⟨b', hb, eb⟩ := hb
      exact ⟨a' + b', add_mem ha hb, by rw [map_add, add_div, ← ea, ← eb]; rfl⟩
    | smul n a _ ha =>
      obtain ⟨a', ha, ea⟩ := ha
      refine ⟨n • a', zsmul_mem ha n, ?_⟩
      rw [map_zsmul, zsmul_eq_mul, zsmul_eq_mul, mul_div_assoc, ← ea]
      simp
  obtain ⟨a, ha, ea⟩ := key
  obtain rfl : a = ⟨_, h⟩ := Subtype.ext ea
  exact ha hu

end PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_nef

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

theorem PositivityTheory.Xgn.t_xgz_height_r_vol_up_model_nef : Hypotheses2 → ∀ (K V Ω : Type) [Field K] [NumberField K] [IsTotallyComplex K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (L : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (d N m : ℕ) (b : Module.Basis (Fin N) K V) (g : Matrix (Fin N) (Fin m) K) (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (n : ℕ) (w : Fin n → V) (abelian₂ t : ℝ), IsFrame Nm L b g A → IsShortGen Nm L w abelian₂ → GlobalTheory.DegVal.GenRatios ev → Real.log abelian₂ ≤ t → ∀ (M : GlobalTheory.ZH.RatModel (𝓞 K) Ω), M.IsNm (fun k => ev (∑ j, g j k • b j)) → IsProjOver M.s → GlobalTheory.IsArithVar M.s d → ∀ (H : ReciprocityTheory.ChartRestriction.G.Semi.LB M.Z) (hH : H.IsLB) (e : H.ι → Ω), M.GenTriv H e → ∀ (s : Fin m → H.Sec), (∀ k, M.HasVal e (s k) (ev (∑ j, g j k • b j))) → ∀ (hs : ⨆ k, ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s k) = ⊤) (Mt : (𝓞 K →+* ℂ) → Matrix (Fin m) (Fin m) ℂ) (hdet : ∀ σ, (Mt σ).det ≠ 0) (hc : ∀ σ, ∃ U ∈ Matrix.unitaryGroup (Fin m) ℂ, Mt ((starRingEnd ℂ).comp σ) = (Mt σ).map (starRingEnd ℂ) * U), (∀ (σ : K →+* ℂ) (x : Fin N → ℂ), ∑ a, ‖∑ k, Mt (σ.comp (algebraMap (𝓞 K) K)) k a * ∑ j, σ (g j k) * x j‖ ^ 2 = GlobalTheory.Adelic.archSize (A σ) x ^ 2) → ((GlobalTheory.HermLB.fs M.s hH s hs Mt hdet hc).shift (fun _ => t) (fun _ => rfl)).IsNef d := by
  intro _ K V Ω _ _ _ _ _ _ _ _ _ Nm L ev d N m b g A n w abelian₂ t hF hW _ ht M _ _ hX H hH e he s hv hs Mt hdet hc hMt
  have hreg : ∀ l, ∀ z ∈ H.U l, ∀ v ∈ L, ev v / e l ∈ M.O z := fun l z hz v hvL => by
    refine PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_nef.mem_O_of_span ev _ ?_ (hF.span ▸ hvL)
    rintro _ ⟨k, rfl⟩
    rw [← hv k l ⟨z, hz⟩]
    exact GlobalTheory.ZH.RatModel.valF_mem_O hz _
  have hwL : ∀ i, w i ∈ L := fun i => (hW.gen _).2 (Submodule.subset_span ⟨i, rfl⟩)
  have hcL : ∀ k, (∑ j, g j k • b j) ∈ L := fun k => hF.span ▸ Submodule.subset_span ⟨k, rfl⟩
  choose u hu using fun i => he.exists_sec_hasVal (ev (w i)) fun l z hz => hreg l z hz _ (hwL i)
  refine PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_nef.isNef_of_small hX _
    ((GlobalTheory.HermLB.semiPos_fs hH s hs Mt hdet hc).shift _ _) u (fun i σ' y => ?_) ?_
  · obtain ⟨σ, rfl⟩ : ∃ σ : K →+* ℂ, σ.comp (algebraMap (𝓞 K) K) = σ' :=
      ⟨_, GlobalTheory.TrueGeo.OfLattice.extEmb_comp σ'⟩
    have hl := GlobalTheory.CxPts.mem_pick hH y
    generalize GlobalTheory.CxPts.pick hH y = l at hl
    have hz := GlobalTheory.CxPts.mem_ptsIn.1 hl
    have hspan : Submodule.span K (L : Set V) = ⊤ := by
      have h2 := congrArg (Submodule.map b.equivFun.symm.toLinearMap) hF.full
      rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, LinearEquiv.range] at h2
      refine eq_top_iff.2 (h2.ge.trans (Submodule.span_mono ?_))
      rintro _ ⟨k, rfl⟩
      change b.equivFun.symm (g.col k) ∈ L
      rw [Module.Basis.equivFun_symm_apply]
      exact hcL k
    obtain ⟨x, hx⟩ := PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_nef.exists_coord y.2 ev (e l) b hspan (hreg l _ hz)
    have hr : Set.range y.1 ⊆ H.U l := (GlobalTheory.ZH.top_le_preimage_iff _ _).1 hl
    have hval : ∀ (a : H.Sec) v, M.HasVal e a (ev v) →
        valR y.1 (H.U l) (a.f l) = ∑ j, σ (b.repr v j) * x j := fun a v ha =>
      (GlobalTheory.ZH.RatModel.val_eq hr (ha l ⟨_, hz⟩)).symm.trans (hx v)
    have hsk : ∀ k, valR y.1 (H.U l) ((s k).f l) = ∑ j, σ (g j k) * x j := fun k => by
      rw [hval _ _ (hv k)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [b.repr_sum_self]
    have hpos := (GlobalTheory.Weight.noCommonZero_combVal (p := M.s) (σ := σ.comp (algebraMap (𝓞 K) K)) hs
      (hdet (σ.comp (algebraMap (𝓞 K) K)))).sum_pos hl
    have hφ : ∑ a, ‖∑ k, Mt (σ.comp (algebraMap (𝓞 K) K)) k a * valR y.1 (H.U l) ((s k).f l)‖ ^ 2 =
        GlobalTheory.Adelic.archSize (A σ) x ^ 2 := by
      simp only [hsk]; exact hMt σ x
    have hpos' : 0 < GlobalTheory.Adelic.archSize (A σ) x ^ 2 := by
      rw [← hφ]
      simp only [GlobalTheory.Weight.combVal, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hpos
      exact hpos
    have hle := GlobalTheory.Adelic.norm_pairing_le (hF.herm σ) (fun j => σ (b.repr (w i) j)) x
    rw [hF.norm, ← hval _ _ (hu i)] at hle
    have hS : 0 ≤ GlobalTheory.Adelic.archSize (A σ) x := Real.sqrt_nonneg _
    have hLam : abelian₂ ≤ Real.exp t :=
      (Real.log_le_iff_le_exp (lt_of_lt_of_le one_pos hW.one_le)).1 ht
    have hle2 := hle.trans (mul_le_mul_of_nonneg_right ((hW.le i σ).trans hLam) hS)
    refine le_of_eq_of_le (((GlobalTheory.HermLB.fs M.s hH s hs Mt hdet hc).nsq_shift (fun _ => t) (fun _ => rfl) _ y).trans
      (congrArg (· * _) (GlobalTheory.Weight.nsq_eq _ (GlobalTheory.CxPts.secVal_mem (u i)) hl))) ?_
    have e1 : ((GlobalTheory.HermLB.fs M.s hH s hs Mt hdet hc).φ (σ.comp (algebraMap (𝓞 K) K))).φ l y =
        Real.log (GlobalTheory.Adelic.archSize (A σ) x ^ 2) := by
      rw [← hφ]; exact GlobalTheory.Weight.fsBasis_φ hH s hs _ (hdet _) l y
    rw [e1, Real.exp_neg, Real.exp_log hpos', Real.exp_neg, mul_assoc, ← mul_inv, ← div_eq_mul_inv,
      div_le_one (by positivity), two_mul, Real.exp_add, ← sq, ← mul_pow, mul_comm]
    exact pow_le_pow_left₀ (norm_nonneg _) hle2 2
  · refine eq_top_iff.2 fun z _ => ?_
    have hm : z ∈ ⨆ k, ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s k) := by rw [hs]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
    obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 hk
    have hz : z ∈ H.U l := M.Z.basicOpen_le _ hl
    have h1 := (GlobalTheory.ZH.RatModel.isUnit_valF_iff hz _).2 hl
    obtain ⟨i, hi⟩ := PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_nef.exists_isUnit ev (e l) w
      (fun i => hreg l z hz _ (hwL i)) ((hW.gen _).1 (hcL k)) (hreg l z hz _ (hcL k))
      (by convert h1 using 2; exact (hv k l ⟨z, hz⟩).symm)
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, TopologicalSpace.Opens.mem_iSup.2 ⟨l,
      (GlobalTheory.ZH.RatModel.isUnit_valF_iff hz _).1 ?_⟩⟩
    convert hi using 2
    exact hu i l ⟨z, hz⟩
