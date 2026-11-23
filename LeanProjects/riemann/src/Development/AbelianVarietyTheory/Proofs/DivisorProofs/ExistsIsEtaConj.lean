import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitOpenAndCongrOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteIndexUnitIdlSup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes

namespace GlobalTheory.EtaConjExist

section General

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

variable {L : Type} [Field L] [NumberField L]

theorem fin_supp {M : Type} [CommGroup M] (c : HeightOneSpectrum (𝓞 L) → M) {n : HeightOneSpectrum (𝓞 L) → ℤ}
    (h : {v | n v ≠ 0}.Finite) : (Function.mulSupport fun v => c v ^ n v).Finite :=
  h.subset fun v hv h0 => hv (by simp only [h0, zpow_zero])

noncomputable def idealChar (c : HeightOneSpectrum (𝓞 L) → ℂˣ) : Ideles L →* ℂˣ :=
  MonoidHom.mk' (fun a => ∏ᶠ v, c v ^ GlobalTheory.Idele.ord_vw (GlobalTheory.HeckeProduct.finPart L a) v) fun a b => by
    rw [← finprod_mul_distrib (fin_supp c (Filter.eventually_cofinite.1 (GlobalTheory.Idele.ord_vw_eventually_zero _)))
      (fin_supp c (Filter.eventually_cofinite.1 (GlobalTheory.Idele.ord_vw_eventually_zero _)))]
    refine finprod_congr fun v => ?_
    rw [map_mul, GlobalTheory.Idele.ord_vw_mul, zpow_add]

theorem idealChar_apply (c : HeightOneSpectrum (𝓞 L) → ℂˣ) (a : Ideles L) :
    idealChar c a = ∏ᶠ v, c v ^ (-WithZero.log (Valued.v ((a : AdeleRing (𝓞 L) L).2 v))) := rfl

theorem idealChar_unit (c : HeightOneSpectrum (𝓞 L) → ℂˣ) {a : Ideles L} (ha : a ∈ unitIdl L) : idealChar c a = 1 := by
  rw [idealChar_apply]
  refine finprod_eq_one_of_forall_eq_one fun v => ?_
  rw [ha v, WithZero.log_one, neg_zero, zpow_zero]

theorem idealChar_local (c : HeightOneSpectrum (𝓞 L) → ℂˣ) (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    idealChar c (localIdele L v x) = c v ^ (-WithZero.log (Valued.v (x : v.adicCompletion L))) := by
  rw [idealChar_apply, finprod_eq_single _ v, GlobalTheory.HeckeProduct.localIdele_snd_self]
  intro w hw
  rw [GlobalTheory.HeckeProduct.localIdele_snd_ne L v w hw, map_one, WithZero.log_one, neg_zero, zpow_zero]

theorem exists_classChar (c : HeightOneSpectrum (𝓞 L) → ℂˣ) (h : ∀ k : Lˣ, ∏ᶠ v, c v ^ ordF v k = 1) :
    ∃ ξ : HChar L, ξ.IsUnitary ∧ (∀ v, ξ.UnrAt v) ∧ ∀ v, ξ.val v = c v := by
  have hd : ∀ k : Lˣ, idealChar c (diagUnits L k) = 1 := fun k => by
    rw [idealChar_apply, ← h k]
    refine finprod_congr fun v => ?_
    have hk : Valued.v ((diagUnits L k : AdeleRing (𝓞 L) L).2 v) = v.valuation L (k : L) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (k : L)
    rw [hk, ordF]
  have hc : Continuous (idealChar c) := by
    refine continuous_of_continuousAt_one _ ?_
    refine (continuousAt_const (y := (1 : ℂˣ))).congr ?_
    filter_upwards [GlobalTheory.Mem.UnitOpen.isOpen_unitIdl.mem_nhds (unitIdl L).one_mem] with a ha
    exact (idealChar_unit c ha).symm
  refine ⟨⟨idealChar c, hc, hd⟩, fun x => ?_, fun v x hx => ?_, fun v => ?_⟩
  · have := GlobalTheory.Mem.UnitIndex.finiteIndex_unitIdl_sup L
    obtain ⟨u, hu, _, ⟨k, rfl⟩, e⟩ := Subgroup.mem_sup.1 ((unitIdl L ⊔ (diagUnits L).range).pow_index_mem x)
    have e1 := congrArg (fun z => ((idealChar c z : ℂˣ) : ℂ)) e
    simp only [map_mul, map_pow, idealChar_unit c hu, hd, one_mul, Units.val_one, Units.val_pow_eq_pow_val] at e1
    exact Complex.norm_eq_one_of_pow_eq_one e1.symm this.index_ne_zero
  · refine (idealChar_local c v x).trans ?_
    rw [show Valued.v (x : v.adicCompletion L) = 1 from hx, WithZero.log_one, neg_zero, zpow_zero]
  · refine (idealChar_local c v _).trans ?_
    rw [show Valued.v ((atFin v (unif v) : (v.adicCompletion L)ˣ) : v.adicCompletion L) = _ from unif_spec v,
      WithZero.log_exp, neg_neg, zpow_one]

theorem finprod_sqrt [IsTotallyComplex L] {I : Type} [Fintype I] (φ : I → L →+* ℂ)
    (hφ : Function.Bijective fun i => InfinitePlace.mk (φ i)) (k : Lˣ) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 L), ((Real.sqrt (Ideal.absNorm v.asIdeal : ℕ))⁻¹ : ℝ) ^ ordF v k) *
      ∏ i, ‖φ i (k : L)‖ = 1 := by
  have h1 := prod_abs_eq_one k.ne_zero
  rw [← hφ.prod_comp, ← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm] at h1
  have h2 : ∀ i, (InfinitePlace.mk (φ i)) (k : L) ^ (InfinitePlace.mk (φ i)).mult = ‖φ i (k : L)‖ * ‖φ i (k : L)‖ := by
    intro i
    rw [InfinitePlace.apply, IsTotallyComplex.mult_eq, sq]
  have h3 : ∀ v : HeightOneSpectrum (𝓞 L), FinitePlace.equivHeightOneSpectrum.symm v (k : L) =
      ((Real.sqrt (Ideal.absNorm v.asIdeal : ℕ))⁻¹ : ℝ) ^ ordF v k *
        ((Real.sqrt (Ideal.absNorm v.asIdeal : ℕ))⁻¹ : ℝ) ^ ordF v k := fun v => by
    have h0 : v.valuation L (k : L) ≠ 0 := (Valuation.ne_zero_iff _).2 k.ne_zero
    rw [← mul_zpow, ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg _), inv_zpow',
      FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.norm_embedding, HeightOneSpectrum.adicAbv_def,
      WithZeroMulInt.toNNReal_neg_apply _ h0, ordF, neg_neg]
    push_cast
    congr 1
    exact WithZero.toAdd_unzero_eq_log h0
  have h4 : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 L) =>
      ((Real.sqrt (Ideal.absNorm v.asIdeal : ℕ))⁻¹ : ℝ) ^ ordF v k).Finite :=
    (GlobalTheory.HeckeProduct.finite_ordF k).subset fun v hv h0 => hv (by simp only [h0, zpow_zero])
  simp only [h2, h3] at h1
  rw [finprod_mul_distrib h4 h4, Finset.prod_mul_distrib] at h1
  refine (mul_self_eq_one_iff.1 (by linear_combination h1)).resolve_right fun h => ?_
  have : (0 : ℝ) ≤ -1 := h ▸ mul_nonneg (finprod_nonneg fun v => by positivity) (by positivity)
  linarith

theorem finprod_alg [IsTotallyComplex L] {I : Type} [Fintype I] (φ : I → L →+* ℂ)
    (hφ : Function.Bijective fun i => InfinitePlace.mk (φ i)) (χ : HChar L) (hu : ∀ v, χ.UnrAt v)
    (hi : χ.HasInf φ fun _ => 1) (w : HeightOneSpectrum (𝓞 L) → ℂˣ)
    (hw : ∀ v, (w v : ℂ) = χ.val v * (((Real.sqrt (Ideal.absNorm v.asIdeal : ℕ))⁻¹ : ℝ) : ℂ)) (k : Lˣ) :
    ((∏ᶠ v, w v ^ ordF v k : ℂˣ) : ℂ) * ∏ i, φ i (k : L) = 1 := by
  have e5 := GlobalTheory.HeckeProduct.productRule χ ∅ (fun v _ => hu v) k
  simp only [Finset.prod_empty, mul_one, Finset.notMem_empty, not_false_eq_true, finprod_true] at e5
  have e6 := finprod_sqrt φ hφ k
  have hs : ∀ {M : Type} [CommGroupWithZero M] (f : HeightOneSpectrum (𝓞 L) → M), ∏ᶠ v, f v ^ ordF v k =
      ∏ v ∈ (GlobalTheory.HeckeProduct.finite_ordF k).toFinset, f v ^ ordF v k := fun f =>
    finprod_eq_prod_of_mulSupport_subset _ fun v hv => by
      simp only [Set.Finite.coe_toFinset]
      exact fun h0 => hv (by simp only [h0, zpow_zero])
  have hs' : ∀ (f : HeightOneSpectrum (𝓞 L) → ℂˣ), ((∏ᶠ v, f v ^ ordF v k : ℂˣ) : ℂ) =
      ∏ v ∈ (GlobalTheory.HeckeProduct.finite_ordF k).toFinset, (f v : ℂ) ^ ordF v k := fun f => by
    rw [finprod_eq_prod_of_mulSupport_subset (s := (GlobalTheory.HeckeProduct.finite_ordF k).toFinset) _ fun v hv => by
      simp only [Set.Finite.coe_toFinset]
      exact fun h0 => hv (by simp only [h0, zpow_zero])]
    simp
  have e7 := congrArg Units.val e5
  have e8 := congrArg Complex.ofReal e6
  rw [Units.val_mul, hs', hi k, Units.val_one] at e7
  rw [hs] at e8
  simp only [Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_zpow, Complex.ofReal_one] at e8
  simp only [zpow_one, Finset.prod_div_distrib] at e7
  have h0 : ∏ i, ((‖φ i (k : L)‖ : ℝ) : ℂ) ≠ 0 := right_ne_zero_of_mul_eq_one e8
  rw [hs']
  simp only [hw, mul_zpow, Finset.prod_mul_distrib]
  rw [div_mul_eq_mul_div, div_eq_one_iff_eq h0] at e7
  rw [mul_right_comm, mul_comm _ (∏ i, φ i (k : L)), e7, mul_comm, e8]

theorem finprod_quot {M : Type} [Field M] (e σ : M →+* ℂ) (y : HeightOneSpectrum (𝓞 L) → Mˣ) (k : Lˣ) (n : M)
    (h : ((∏ᶠ v, Units.map e.toMonoidHom (y v) ^ ordF v k : ℂˣ) : ℂ) * e n = 1) (hn : σ n = e n) :
    ∏ᶠ v, (Units.map σ.toMonoidHom (y v) / Units.map e.toMonoidHom (y v)) ^ ordF v k = 1 := by
  have hf := GlobalTheory.HeckeProduct.finite_ordF k
  have hm : ∀ f : M →+* ℂ, ∏ᶠ v, Units.map f.toMonoidHom (y v) ^ ordF v k =
      Units.map f.toMonoidHom (∏ᶠ v, y v ^ ordF v k) := fun f => by
    rw [MonoidHom.map_finprod _ (fin_supp y hf)]
    simp only [map_zpow]
  simp only [div_zpow]
  rw [finprod_div_distrib (fin_supp _ hf) (fin_supp _ hf), hm, hm, div_eq_one]
  rw [hm] at h
  have h1 : ((∏ᶠ v, y v ^ ordF v k : Mˣ) : M) * n = 1 := e.injective (by rw [map_mul, map_one]; exact h)
  have h2 := congrArg σ h1
  rw [map_mul, map_one, hn, ← h] at h2
  exact Units.ext (mul_right_cancel₀ (right_ne_zero_of_mul_eq_one h) h2)

end General

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem unram_of_chrEq {D : D7} {c : (AE D)ˣ →* Circle} {χ : Formalism.L2.Host.HChar D.host.E} (hc : ChrEq c χ)
    (hu : ∀ P, χ.UnrAt P) : UnramEverywhere D c := by
  intro x hx h4 h5
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  apply Circle.ext
  rw [GlobalTheory.Mem.EtaTilde.val_finite D ι h1 h2 (GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3) c χ hc hu x hx, Circle.coe_one,
    Units.val_eq_one]
  refine finprod_eq_one_of_forall_eq_one fun P => ?_
  have e := GlobalTheory.Mem.EtaTilde.val_mul_inv (RingHom.id _) P (Units.map ((ι : _ →+* _).comp (finPart D)).toMonoidHom x)
  have e' : Valued.v (ι (finPart D (x : AE D)) P) * Valued.v (ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) P) = 1 := e
  have e1 : Valued.v (ι (finPart D (x : AE D)) P) = 1 := by
    refine le_antisymm ((h2 _).1 h4 P) ?_
    rw [← e']
    exact mul_le_of_le_one_right' ((h2 _).1 h5 P)
  rw [e1, WithZero.log_one, neg_zero, zpow_zero]

theorem exists_norm (D : D7) (k : D.host.E) :
    ∃ n ∈ D.host.K, D.what₂.embLL (D.embE n) = ∏ g, Formalism.L2.Host.embPsi D.host g k := by
  have hE := D.host.hostE_isGalois
  have h := Algebra.norm_eq_prod_automorphisms D.host.K k
  refine ⟨_, (Algebra.norm D.host.K k).2, (DFunLike.congr_fun D.embE_φ₀ _).trans ?_⟩
  change D.host.φ₀ (algebraMap D.host.K D.host.E _) = _
  rw [h, map_prod]
  exact (Fintype.prod_bijective _ (GlobalTheory.InducedType.galK_bijective D.host) _ _ fun _ => rfl).symm

theorem exists_conj {D : D7} (η : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (hc : ChrEq η χ)
    (hχ : Formalism.L2.Host.IsEtaT D.host χ)
    (hy : ∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ y : D.what₂.LL,
      D.what₂.embLL y = χ.val P * (((Real.sqrt (Ideal.absNorm P.asIdeal : ℕ))⁻¹ : ℝ) : ℂ))
    (σ : D.what₂.LL →+* ℂ) (hσ : OverK σ) : ∃ η', IsEtaConj σ η η' := by
  have hcm : IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨_, -, hd, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  choose y hy using hy
  have hy0 : ∀ P, D.what₂.embLL (y P) ≠ 0 := fun P => by
    have : (0 : ℝ) < (Ideal.absNorm P.asIdeal : ℕ) :=
      Nat.cast_pos.2 (Nat.pos_of_ne_zero fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h))
    rw [hy]
    exact mul_ne_zero (Units.ne_zero _) (Complex.ofReal_ne_zero.2 (inv_ne_zero (Real.sqrt_pos.2 this).ne'))
  let u : HeightOneSpectrum (𝓞 D.host.E) → D.what₂.LLˣ := fun P => Units.mk0 (y P) ((map_ne_zero _).1 (hy0 P))
  obtain ⟨ξ, x1, x2, x3⟩ := exists_classChar
    (fun P => Units.map σ.toMonoidHom (u P) / Units.map D.what₂.embLL.toMonoidHom (u P)) fun k => by
      obtain ⟨n, hn, hn'⟩ := exists_norm D k
      refine finprod_quot _ _ u k (D.embE n) ?_ (hσ n hn)
      rw [hn']
      exact finprod_alg _ hd.bij χ hχ.unr hχ.inf _ hy k
  obtain ⟨c, hc'⟩ := GlobalTheory.CharTransport.exists_chrEq D (χ * ξ) fun x => by
    change ‖((χ.1 x * ξ.1 x : ℂˣ) : ℂ)‖ = 1
    rw [Units.val_mul, norm_mul, hχ.unitary x, x1 x, one_mul]
  refine ⟨c, hc'.1, unram_of_chrEq hc' fun P x hx => ?_, fun P e he x hx => ⟨y P, ?_, ?_⟩⟩
  · rw [Formalism.L2.Host.HChar.loc_mul, hχ.unr P x hx, x2 P x hx, one_mul]
  · rw [hc.2 P e he _ x hx]
    exact hy P
  · have h1 : ((c x : Circle) : ℂ) = ((χ.val P * ξ.val P : ℂˣ) : ℂ) := hc'.2 P e he _ x hx
    rw [h1, x3, Units.val_mul, mul_right_comm, Units.val_div_eq_div_val]
    have h2 := hy P
    refine Eq.trans ?_ (congrArg (· * (σ (y P) / D.what₂.embLL (y P))) h2)
    exact (mul_div_cancel₀ _ (hy0 P)).symm

end GlobalTheory.EtaConjExist
