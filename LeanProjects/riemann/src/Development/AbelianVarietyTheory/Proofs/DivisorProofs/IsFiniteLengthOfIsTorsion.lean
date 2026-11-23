import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyHomologyEquiv

open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Pointwise TensorProduct

namespace GlobalTheory.FlatCons

private theorem isFiniteLength_of_isTorsion' {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Type} [AddCommGroup X] [Module R X] [Module.Finite R X] (hX : Module.IsTorsion R X) :
    IsFiniteLength R X := by
  obtain ⟨r, hr, hr0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors hX
  have hr' : Module.IsTorsionBySet R X (Ideal.span {r}) := by
    rw [Module.isTorsionBySet_span_singleton_iff]
    exact fun x ↦ Submodule.mem_annihilator.mp hr x trivial
  letI := hr'.module
  haveI : Module.Finite (R ⧸ Ideal.span {r}) X := Module.Finite.of_restrictScalars_finite R _ _
  haveI : IsArtinian R (R ⧸ Ideal.span {r}) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (isFiniteLength_quotient_span_singleton R hr0)).2
  haveI : IsArtinianRing (R ⧸ Ideal.span {r}) := isArtinian_of_tower R inferInstance
  exact isFiniteLength_iff_isNoetherian_isArtinian.2 ⟨inferInstance,
    isArtinian_of_surjective_algebraMap (R := R ⧸ Ideal.span {r}) Ideal.Quotient.mk_surjective⟩

private theorem length_quot_eq (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (T : Type) [AddCommGroup T]
    [Module O T] [Module.Finite O T] {g : O} (hg : g ≠ 0) :
    Module.length O (LinearMap.ker (LinearMap.lsmul O T g)) ≠ ⊤ ∧
      Module.length O (T ⧸ (g • ⊤ : Submodule O T)) = Module.length O (LinearMap.ker (LinearMap.lsmul O T g)) +
        IsDiscreteValuationRing.addVal O g * (Module.finrank O T : ℕ∞) := by
  let t := Submodule.torsion O T
  have ht : Module.length O t ≠ ⊤ :=
    Module.length_ne_top_iff.2 (isFiniteLength_of_isTorsion' (Submodule.torsion_isTorsion (R := O) (M := T)))
  have hreg : IsSMulRegular (T ⧸ t) g := IsSMulRegular.of_ne_zero hg
  have h1 := QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last (r := g)
    (f₁ := (0 : PUnit →ₗ[O] t)) (f₂ := t.subtype) (f₃ := t.mkQ)
    ((LinearMap.exact_zero_iff_injective _ _).2 t.injective_subtype) (LinearMap.exact_subtype_mkQ t) hreg
  have hinj : Function.Injective (QuotSMulTop.map g t.subtype) := by
    rw [map_zero] at h1
    exact (LinearMap.exact_zero_iff_injective _ _).1 h1
  have h2 := Module.length_eq_add_of_exact _ _ hinj (QuotSMulTop.map_surjective g t.mkQ_surjective)
    (QuotSMulTop.map_exact g (LinearMap.exact_subtype_mkQ t) t.mkQ_surjective)
  have h3 := length_quotient_smul_top_dvr (T ⧸ t) g
  have h4 : Module.finrank O (T ⧸ t) = Module.finrank O T := by
    exact finrank_quotient_eq_of_le_torsion le_rfl
  have hk : Module.length O (LinearMap.ker (LinearMap.lsmul O T g)) =
      Module.length O (LinearMap.ker (LinearMap.lsmul O t g)) := by
    have hle : LinearMap.ker (LinearMap.lsmul O T g) ≤ t := fun x hx => ⟨⟨g, mem_nonZeroDivisors_of_ne_zero hg⟩, hx⟩
    rw [← (Submodule.comapSubtypeEquivOfLe hle).length_eq]
    refine (LinearEquiv.ofEq _ _ ?_).length_eq
    ext x
    simp [Subtype.ext_iff]
  have h5 := length_eq_range_add_range (LinearMap.exact_subtype_ker_map (LinearMap.lsmul O t g))
  have h6 := Module.length_eq_add_of_exact _ _ (g • ⊤ : Submodule O t).injective_subtype
    (g • ⊤ : Submodule O t).mkQ_surjective (LinearMap.exact_subtype_mkQ _)
  rw [Submodule.range_subtype, show LinearMap.range (LinearMap.lsmul O t g) = g • ⊤ from
    (Submodule.map_top _).symm] at h5
  have h7 : Module.length O (g • ⊤ : Submodule O t) ≠ ⊤ := fun h => ht (by rw [h6, h, top_add])
  have h8 : Module.length O (t ⧸ (g • ⊤ : Submodule O t)) =
      Module.length O (LinearMap.ker (LinearMap.lsmul O t g)) := by
    rw [h6, add_comm] at h5
    exact WithTop.add_right_cancel h7 h5
  refine ⟨fun h => ht (by rw [h5, ← hk, h, top_add]), ?_⟩
  rw [hk, ← h8, ← h4, ← h3]
  exact h2

private theorem finrank_coh_eq_hdim (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Z : Model O)
    {M : LB Z.X} (hM : M.IsLB) (n : ℕ) :
    Module.finrank O (coh (twist (structureModule Z.X) M) n) =
      hdim Z.toBase.fnField (twist (structureModule Z.toBase.genFibre) (M.pull Z.toBase.genFibreι)) n := by
  let k := Z.toBase.fnField
  let φ : O →+* k := (Spec.preimage ((Model.base O).X.fromSpecResidueField (genericPoint _))).hom
  have hφ : Spec.map (CommRingCat.ofHom φ) = (Model.base O).X.fromSpecResidueField (genericPoint _) :=
    Spec.map_preimage _
  have hinj : Function.Injective φ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    have h₁ := Model.mem_gen_iff_eq_bot.1 (Model.base O).genericPoint_mem_gen
    have h₂ := Scheme.fromSpecResidueField_apply (genericPoint (Model.base O).X) (⊥ : PrimeSpectrum k)
    rw [← hφ] at h₂
    exact (congrArg PrimeSpectrum.asIdeal h₂).trans h₁
  letI := φ.toAlgebra
  have : FaithfulSMul O k := (faithfulSMul_iff_algebraMap_injective O k).2 hinj
  have H : IsPullback Z.toBase.genFibreι Z.toBase.genFibreStr Z.str (Spec.map (CommRingCat.ofHom (algebraMap O k))) := by
    have := Z.toBase.isPullback_genFibre
    rwa [← hφ] at this
  have := isAffineHom_diagonal_of_isSeparated Z.str
  obtain ⟨m, D, hD, hc⟩ := exists_fin_affine_cover (X := Z.X) (V := ⊤) isCompact_univ
  have hD' := isAffineOpen_finset_biInf hD
  obtain ⟨e₁⟩ := FieldChangeInter.nonempty_coh_equiv Z.str hM hc hD' n
  obtain ⟨e₂⟩ := FieldChangeInter.nonempty_coh_equiv Z.toBase.genFibreStr
    (ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_pull hM Z.toBase.genFibreι) (D := fun i => Z.toBase.genFibreι ⁻¹ᵁ D i)
    (by rw [← Scheme.Hom.preimage_iSup, hc]; rfl) (fun s hs => AbLaw.isAffineOpen_biInf_preimage H (hD' s hs)) n
  obtain ⟨e₃⟩ := FieldChangeInter.nonempty_homology_equiv k (AbLaw.cechLB Z.str M D) n
  have e₄ := ((HomologicalComplex.homologyFunctor _ _ n).mapIso (AbLaw.cechLBBaseChangeIso hM H hD')).toLinearEquiv
  rw [hdim_def, ← e₁.finrank_eq, ← e₂.finrank_eq]
  refine Eq.symm (e₄.finrank_eq.symm.trans (e₃.finrank_eq.trans ?_))
  exact (TensorProduct.isBaseChange O _ k).finrank_eq

private theorem sum_length_les (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {g : O} (hg : g ≠ 0)
    (T C : ℕ → Type) [∀ n, AddCommGroup (T n)] [∀ n, Module O (T n)] [∀ n, AddCommGroup (C n)]
    [∀ n, Module O (C n)] (hfin : ∀ n, Module.Finite O (T n)) (f : ∀ n, T n →ₗ[O] T n) (π : ∀ n, T n →ₗ[O] C n)
    (δ : ∀ n, C n →ₗ[O] T (n + 1)) (hm : ∀ n, f n = LinearMap.lsmul O (T n) g)
    (x₁ : ∀ n, Function.Exact (δ n) (f (n + 1))) (x₂ : ∀ n, Function.Exact (f n) (π n))
    (x₃ : ∀ n, Function.Exact (π n) (δ n)) (h0 : Function.Injective (f 0)) (N : ℕ)
    (hN : ∀ n, N ≤ n → Subsingleton (T n)) :
    ∑ n ∈ Finset.range N, (-1 : ℤ) ^ n * ((Module.length O (C n)).toNat : ℤ) =
      ((IsDiscreteValuationRing.addVal O g).toNat : ℤ) * ∑ᶠ n, (-1 : ℤ) ^ n * (Module.finrank O (T n) : ℤ) := by
  obtain rfl : f = fun n => LinearMap.lsmul O (T n) g := funext hm
  let a : ℕ → ℤ := fun n => (Module.length O (LinearMap.ker (LinearMap.lsmul O (T n) g))).toNat
  let v : ℤ := (IsDiscreteValuationRing.addVal O g).toNat
  let r : ℕ → ℤ := fun n => Module.finrank O (T n)
  have hv : IsDiscreteValuationRing.addVal O g ≠ ⊤ := mt IsDiscreteValuationRing.addVal_eq_top_iff.1 hg
  have step (n : ℕ) : ((Module.length O (C n)).toNat : ℤ) = a n + v * r n + a (n + 1) := by
    have e₃ := length_eq_range_add_range (x₃ n)
    rw [← (x₁ n).linearMap_ker_eq, ← (LinearMap.quotKerEquivRange (π n)).length_eq, (x₂ n).linearMap_ker_eq,
      show LinearMap.range (LinearMap.lsmul O (T n) g) = g • ⊤ from (Submodule.map_top _).symm] at e₃
    obtain ⟨h₁, h₂⟩ := length_quot_eq O (T n) hg
    obtain ⟨h₃, -⟩ := length_quot_eq O (T (n + 1)) hg
    have hvr : IsDiscreteValuationRing.addVal O g * (Module.finrank O (T n) : ℕ∞) ≠ ⊤ :=
      WithTop.mul_ne_top hv (ENat.coe_ne_top _)
    rw [e₃, h₂, ENat.toNat_add (WithTop.add_ne_top.2 ⟨h₁, hvr⟩) h₃, ENat.toNat_add h₁ hvr, ENat.toNat_mul,
      ENat.toNat_coe]
    push_cast
    rfl
  have key (K : ℕ) : ∑ n ∈ Finset.range K, (-1 : ℤ) ^ n * (a n + v * r n + a (n + 1)) =
      v * ∑ n ∈ Finset.range K, (-1 : ℤ) ^ n * r n + (a 0 - (-1) ^ K * a K) := by
    induction K with
    | zero => simp
    | succ K ih =>
      simp only [Finset.sum_range_succ, pow_succ]
      linear_combination ih
  have a0 : a 0 = 0 := by
    simp only [a]
    rw [LinearMap.ker_eq_bot.2 h0]
    simp
  have aN : a N = 0 := by
    have := hN N le_rfl
    simp [a, Module.length_eq_zero]
  have hs : ∑ᶠ n, (-1 : ℤ) ^ n * r n = ∑ n ∈ Finset.range N, (-1 : ℤ) ^ n * r n :=
    finsum_eq_sum_of_support_subset _ fun n hn => by
      by_contra h
      have := hN n (by simpa using h)
      exact hn (by simp [r, Module.finrank_zero_of_subsingleton])
  refine (Finset.sum_congr rfl fun n _ => congrArg ((-1 : ℤ) ^ n * ·) (step n)).trans ?_
  rw [key, a0, aN]
  change _ = v * ∑ᶠ n, (-1 : ℤ) ^ n * r n
  rw [hs]
  ring

private theorem chiLen_twist_effConst (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Z : Model O) {g : O}
    (hg : g ≠ 0) {M : LB Z.X} (hM : M.IsLB) :
    chiLen O (twist (divMod (Z.effConst g hg).1) M) = ((IsDiscreteValuationRing.addVal O g).toNat : ℤ) *
      ∑ᶠ n, (-1 : ℤ) ^ n * (Module.finrank O (coh (twist (structureModule Z.X) M) n) : ℤ) := by
  have := Twist.isFiniteQC_twist (F := structureModule Z.X) hM
  have hfin := finite_coh_of_isProjOver Z.const_eq (twist (structureModule Z.X) M) Z.isProjOver
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n, N ≤ n → Subsingleton (coh (twist (structureModule Z.X) M) n) :=
    ⟨Z.relDim + 2, fun n hn => subsingleton_coh_of_isProjOver Z.isProjOver _
      ((suppDim_le _).trans_lt (Z.dim_eq.trans_lt (by exact_mod_cast (by omega : Z.relDim + 1 < n))))⟩
  obtain ⟨e⟩ := nonempty_cokernel_iso (.principal (Z.const g) (Z.isRegularFn_const hg))
    (φ := smulHom (structureModule Z.X) (Z.const g)) fun _ _ _ => ⟨.refl _ _, fun _ => rfl⟩
  have : Mono (smulHom (structureModule Z.X) (Z.const g)) :=
    mono_of_locally_app_injective _ fun W x hx => ⟨W, hx, le_rfl, fun _ _ h =>
      (mul_cancel_left_mem_nonZeroDivisors (Z.isRegularFn_const hg W le_top)).1 h⟩
  have hS := Twist.shortExact_map hM (S := .mk _ (cokernel.π _)
    (cokernel.condition (smulHom (structureModule Z.X) (Z.const g))))
    { exact := ShortComplex.exact_cokernel _ }
  have hf : Twist.map M (smulHom (structureModule Z.X) (Z.const g)) = smulHom _ (Z.const g) :=
    Twist.hom_ext fun V s i => by
      rw [Twist.coord_map_app, smulHom_app_apply, smulHom_app_apply, Twist.coord_smul]
      exact congrArg (· • Twist.coord s i) (map_restrictGlobal (homOfLE inf_le_left) _).symm
  have hm (n : ℕ) : cohOn.map O (Twist.map M (smulHom (structureModule Z.X) (Z.const g))) ⊤ n =
      LinearMap.lsmul O (coh (twist (structureModule Z.X) M) n) g := by
    rw [hf]; rfl
  refine (chiLen_congr O ((twistFunctor M).mapIso e)).symm.trans ?_
  refine (chiLen_eq_sum_range O N fun n hn =>
    cohOn.subsingleton₃ hS ⊤ n (hN n hn) (hN (n + 1) (by omega))).trans ?_
  exact sum_length_les O hg (fun n => coh (twist (structureModule Z.X) M) n) _ hfin _ _ _ hm
    (fun n => cohOn.exact₁ O hS ⊤ n) (fun n => cohOn.exact₂ O hS ⊤ n) (fun n => cohOn.exact₃ O hS ⊤ n)
    (cohOn.injective_zero O hS ⊤) N hN

private theorem chiLenPic_divP (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime]
    [CharZero O] (Z : Model O) :
    chiLenPic O (divMod (Z.effConst p (natCast_ne_zero O p)).1) = fun c =>
      (ramIdx O p : ℤ) * chiPic Z.toBase.fnField (structureModule Z.toBase.genFibre) (pull Z.toBase.genFibreι c) := by
  funext c
  obtain ⟨M, hM, rfl⟩ := cls_surj c
  rw [chiLenPic_cls, chiLen_twist_effConst O Z _ hM, ← cls_pull hM _ (ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_pull hM _),
    chiPic_cls, chi]
  congr 1
  refine finsum_congr fun n => ?_
  rw [finrank_coh_eq_hdim O Z hM n]

private theorem capDeg_divP_eq_fibreDeg : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O) (Q : PicSym B.X), B.capDeg_vp p (GlobalTheory.Vert.Model.toQ (B.divP p)) Q = B.toBase.fibreDeg Q := by
  intro O _ _ _ p _ _ _ B Q
  refine LinearMap.congr_fun (picSym_linearMap_ext (l := B.capDeg_vp p (Model.toQ (B.divP p)))
    (l' := B.toBase.fibreDeg) fun n g => ?_) Q
  choose L hL hg using fun i => cls_surj (g i)
  simp only [← hg, firstChernPic_class]
  rw [Model.capDeg_vp_toQ, Model.divP, Model.div, Model.vDeg_ofEff_prod, Model.Hom.fibreDeg_prod, Model.relDim_toBase]
  split_ifs with h
  · have hL' : ∀ i, ((L i).pull B.toBase.genFibreι).IsLB := fun i => ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_pull (hL i) _
    rw [interLen_eq_multiDiff O _ hL, chiLenPic_divP O p B, interNum_eq_multiDiff _ _ hL']
    have e : (fun c => (ramIdx O p : ℤ) * chiPic B.toBase.fnField (structureModule B.toBase.genFibre)
        (pull B.toBase.genFibreι c)) = (AddMonoidHom.mulLeft (ramIdx O p : ℤ)) ∘
        (chiPic B.toBase.fnField (structureModule B.toBase.genFibre) ∘ pull B.toBase.genFibreι) := rfl
    rw [e, multiDiff_map, multiDiff_comap]
    simp only [Function.comp_apply, map_zero, AddMonoidHom.coe_mulLeft]
    have e2 : (pull B.toBase.genFibreι ∘ fun i => cls (L i) (hL i)) = fun i => cls _ (hL' i) :=
      funext fun i => (cls_pull (hL i) _ (hL' i)).symm
    rw [e2]
    have he : (ramIdx O p : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (ramIdx_ne_zero O p)
    push_cast
    field_simp
  · exact zero_div _

end GlobalTheory.FlatCons

theorem _root_.GlobalTheory.T.capDeg_divP_eq_fibreDeg' : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O) (Q : PicSym B.X), B.capDeg_vp p (GlobalTheory.Vert.Model.toQ (B.divP p)) Q = B.toBase.fibreDeg Q :=
  GlobalTheory.FlatCons.capDeg_divP_eq_fibreDeg
