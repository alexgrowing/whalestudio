import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGalConjEta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaAtOfIsEtaConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPsiOfOverK
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharFiniteOrderOfTrivialAtInfinity
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResFinEqOneOfAway
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EtaConjType

open Formalism.L2.Host Formalism.L2.JoinChr

section General

variable {E : Type} [Field E] [NumberField E]

noncomputable def rt (P : HeightOneSpectrum (𝓞 E)) : ℝ := (Real.sqrt ((Ideal.absNorm P.asIdeal : ℕ) : ℝ))⁻¹

theorem rt_pos (P : HeightOneSpectrum (𝓞 E)) : 0 < rt P :=
  inv_pos.2 (Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 P.ne_bot))))

theorem rt_sq (P : HeightOneSpectrum (𝓞 E)) : rt P ^ 2 = ((Ideal.absNorm P.asIdeal : ℕ) : ℝ)⁻¹ := by
  rw [rt, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]

theorem mk_eq (P : HeightOneSpectrum (𝓞 E)) (k : Eˣ) : FinitePlace.mk P (k : E) = (rt P ^ ordF P k) ^ 2 := by
  obtain ⟨u, hu, hk⟩ := GlobalTheory.EtaConjChar.exists_unit_part P k
  generalize ordF P k = n at hk ⊢
  rw [hk, Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, GlobalTheory.EtaConjLocal.mk_unit P hu,
    GlobalTheory.EtaConjLocal.mk_unif, mul_one, ← rt_sq, sq, sq, mul_zpow]

theorem prod_rt [IsTotallyComplex E] {I : Type} [Fintype I] (φ : I → E →+* ℂ)
    (hφ : Function.Bijective fun i => InfinitePlace.mk (φ i)) (k : Eˣ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS : ∀ P, ordF P k ≠ 0 → P ∈ S) : (∏ i, ‖φ i k‖) * ∏ P ∈ S, rt P ^ ordF P k = 1 := by
  have h := prod_abs_eq_one k.ne_zero
  rw [← hφ.prod_comp, ← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm,
    finprod_eq_prod_of_mulSupport_subset (s := S)] at h
  · rw [← sq_eq_sq₀ (mul_nonneg (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      (Finset.prod_nonneg fun P _ => (zpow_pos (rt_pos P) _).le)) zero_le_one, one_pow, mul_pow, ← Finset.prod_pow,
      ← Finset.prod_pow, ← h]
    congr 1
    · exact Finset.prod_congr rfl fun i _ => by rw [InfinitePlace.apply, IsTotallyComplex.mult_eq]
    · exact Finset.prod_congr rfl fun P _ => (mk_eq P k).symm
  · intro P hP
    refine hS P fun h0 => hP ?_
    exact (mk_eq P k).trans (by rw [h0]; simp)

theorem prod_val (χ : HChar E) (hu : ∀ P, χ.UnrAt P) (k : Eˣ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS : ∀ P, ordF P k ≠ 0 → P ∈ S) :
    ((χ.inf k : ℂˣ) : ℂ) * ∏ P ∈ S, (((χ.val P : ℂˣ) : ℂ) * (rt P : ℂ)) ^ ordF P k =
      ((∏ P ∈ S, rt P ^ ordF P k : ℝ) : ℂ) := by
  have h := GlobalTheory.HeckeProduct.productRule χ ∅ (fun v _ => hu v) k
  simp only [Finset.prod_empty, mul_one, Finset.notMem_empty, not_false_eq_true, finprod_true] at h
  rw [finprod_eq_prod_of_mulSupport_subset (s := S) _ (fun P hP => hS P fun h0 => hP (by simp [h0]))] at h
  have h' := congrArg (Units.val : ℂˣ → ℂ) h
  simp only [Units.val_mul, Units.coe_prod, Units.val_zpow_eq_zpow_val, Units.val_one] at h'
  simp only [mul_zpow, Finset.prod_mul_distrib]
  rw [← mul_assoc, h', one_mul]
  push_cast
  rfl

theorem unrAt_of_locK (χ : HChar E) (P : HeightOneSpectrum (𝓞 E))
    (h : ∀ u : Eˣ, P.valuation E (u : E) = 1 → χ.locK P u = 1) : χ.UnrAt P := by
  intro x
  have hc : IsClopen {x : (P.adicCompletion E)ˣ | IsUnitAt P x} := by
    have := (Valued.isClopen_sphere (P.adicCompletion E) (r := 1) one_ne_zero).preimage
      (Units.continuous_val (M := P.adicCompletion E))
    convert this using 1
    ext x
    simp [IsUnitAt]
  refine (GlobalTheory.Mem.Chr.Determ.denseRange_atFin P).induction_on (p := fun x => IsUnitAt P x → χ.loc P x = 1) x ?_
    fun k hk => h k ((P.valuedAdicCompletion_eq_valuation' _).symm.trans hk)
  exact isClosed_imp hc.2 (isClosed_eq (χ.2.1.comp (GlobalTheory.Mem.UnrAe.continuous_localIdele P)) continuous_const)

variable {L : Type} [Field L] (ι σ : L →+* ℂ) {χ χ' : HChar E} (hu : ∀ P, χ.UnrAt P) (hu' : ∀ P, χ'.UnrAt P)
  (y : HeightOneSpectrum (𝓞 E) → L) (hy : ∀ P, ι (y P) = ((χ.val P : ℂˣ) : ℂ) * (rt P : ℂ))
  (hy' : ∀ P, σ (y P) = ((χ'.val P : ℂˣ) : ℂ) * (rt P : ℂ))

include hu hu' hy hy'

theorem inf_eq [IsTotallyComplex E] {I : Type} [Fintype I] (φ : I → E →+* ℂ)
    (hφ : Function.Bijective fun i => InfinitePlace.mk (φ i)) (hi : χ.HasInf φ fun _ => 1)
    (ht : ∀ k : E, ∃ t : L, ι t = ∏ i, φ i k ∧ σ t = ∏ i, φ i k) (k : Eˣ) : χ'.inf k = χ.inf k := by
  obtain ⟨t, ht1, ht2⟩ := ht k
  let S := (GlobalTheory.HeckeProduct.finite_ordF k).toFinset
  have hS : ∀ P, ordF P k ≠ 0 → P ∈ S := fun P hP => (Set.Finite.mem_toFinset _).2 hP
  have h1 := prod_val χ hu k S hS
  have h2 := prod_val χ' hu' k S hS
  have h3 := congrArg (fun r : ℝ => (r : ℂ)) (prod_rt φ hφ k S hS)
  have h4 : ((χ.inf k : ℂˣ) : ℂ) * ((∏ i, ‖φ i k‖ : ℝ) : ℂ) = ∏ i, φ i k := by
    rw [hi k, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [zpow_one, div_mul_cancel₀ _ (by simp)]
  simp only [← hy, ← hy', ← map_zpow₀, ← map_prod] at h1 h2
  simp only [Complex.ofReal_mul, Complex.ofReal_one] at h3
  generalize ∏ P ∈ S, y P ^ ordF P k = Y at h1 h2
  generalize ((∏ P ∈ S, rt P ^ ordF P k : ℝ) : ℂ) = r at h1 h2 h3
  generalize ((∏ i, ‖φ i k‖ : ℝ) : ℂ) = s at h3 h4
  have h5 : Y * t = 1 := ι.injective (by
    rw [map_mul, map_one, ht1, ← h4, ← h3, ← h1]
    ring)
  have h6 : σ Y * (∏ i, φ i k) = 1 := by rw [← ht2, ← map_mul, h5, map_one]
  refine Units.ext ?_
  calc ((χ'.inf k : ℂˣ) : ℂ) = (χ'.inf k : ℂˣ) * (σ Y * (((χ.inf k : ℂˣ) : ℂ) * s)) := by rw [h4, h6, mul_one]
    _ = (χ.inf k : ℂˣ) * (s * (((χ'.inf k : ℂˣ) : ℂ) * σ Y)) := by ring
    _ = _ := by rw [h2, h3, mul_one]

theorem resFin_eq {F : Type} [Field F] [NumberField F] [Algebra F E] (h2 : Module.finrank F E = 2)
    (hF : ∀ P : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 F) P.asIdeal) (hr : χ.ResEta F)
    (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) : χ'.resFin v k = χ.resFin v k := by
  have key : ∀ (ψ : HChar E), (∀ P, ψ.UnrAt P) →
      ∏ P ∈ aboveF (L := E) F v, (((ψ.val P : ℂˣ) : ℂ) * (rt P : ℂ)) ^ ordF v k =
        ((ψ.resFin v k : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)⁻¹ ^ ordF v k := by
    intro ψ hψ
    have h1 : ∏ P ∈ aboveF (L := E) F v, rt P = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ := by
      rw [← sq_eq_sq₀ (Finset.prod_nonneg fun P _ => (rt_pos P).le) (by positivity), ← Finset.prod_pow]
      simp only [rt_sq]
      rw [Finset.prod_inv_distrib, ← Nat.cast_prod, GlobalTheory.ToricDistribution.prod_absNorm hF, h2, Nat.cast_pow, inv_pow]
    simp only [mul_zpow, Finset.prod_mul_distrib]
    congr 1
    · rw [HChar.resFin_apply, Units.coe_prod]
      refine Finset.prod_congr rfl fun P hP => ?_
      rw [GlobalTheory.HeckeProduct.locK_unr ψ (hψ P), GlobalTheory.ToricDistribution.ordF_up hF, GlobalTheory.ToricDistribution.mem_aboveF.1 hP,
        Units.val_zpow_eq_zpow_val]
    · rw [Finset.prod_zpow, ← Complex.ofReal_prod, h1]
      simp
  have h1 := key χ hu
  have h3 := key χ' hu'
  simp only [← hy, ← hy', ← map_zpow₀, ← map_prod] at h1 h3
  obtain ⟨z, hz⟩ : ∃ z : L, ∀ f : L →+* ℂ, f z = ((χ.resFin v k : ℂˣ) : ℂ) := by
    rw [hr.1, etaFin]
    split_ifs
    · exact ⟨(-1) ^ ordF v k, fun f => by simp⟩
    · exact ⟨1, fun f => by simp⟩
  have h4 : ∏ P ∈ aboveF (L := E) F v, y P ^ ordF v k = z * ((Ideal.absNorm v.asIdeal : ℕ) : L)⁻¹ ^ ordF v k :=
    ι.injective (by rw [h1, map_mul, hz, map_zpow₀, map_inv₀, map_natCast])
  rw [h4, map_mul, hz, map_zpow₀, map_inv₀, map_natCast] at h3
  refine Units.ext (mul_right_cancel₀ (zpow_ne_zero _ (inv_ne_zero ?_)) h3.symm)
  exact Nat.cast_ne_zero.2 (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)

end General

theorem isEtaT_of_conj {D : D7} {σ : D.what₂.LL →+* ℂ} (hσ : OverK σ) {η η' : (AE D)ˣ →* Circle} {χ χ' : HChar D.host.E}
    (hc : ChrEq η χ) (hc' : ChrEq η' χ') (hχ : IsEtaT D.host χ) (hη : IsEtaConj σ η η') : IsEtaT D.host χ' := by
  have hu' : ∀ P, χ'.UnrAt P := fun P => unrAt_of_locK χ' P (GlobalTheory.EtaConjChar.locK_eq_one hc' hη.2.1 P)
  have hy : ∀ P, ∃ y : D.what₂.LL, D.what₂.embLL y = ((χ.val P : ℂˣ) : ℂ) * (rt P : ℂ) ∧
      σ y = ((χ'.val P : ℂˣ) : ℂ) * (rt P : ℂ) := by
    intro P
    obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
    obtain ⟨e, he, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
    obtain ⟨y, hy1, hy2⟩ := hη.2.2 P e he (locU he.1 (unif P)) rfl
    rw [hc.2 P e he _ (locU he.1 (unif P)) rfl] at hy1
    rw [hc'.2 P e he _ (locU he.1 (unif P)) rfl] at hy2
    exact ⟨y, hy1, hy2⟩
  choose y hy hy' using hy
  obtain ⟨c, -, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  haveI := hcm.cplx
  obtain ⟨hb, hl⟩ := (labels_overK σ).1 hσ
  have hinf : ∀ k, (χ' * χ⁻¹).inf k = 1 := fun k => by
    rw [HChar.inf_mul, HChar.inf_inv, mul_inv_eq_one]
    refine inf_eq D.what₂.embLL σ hχ.unr hu' y hy hy' (embPsi D.host) hcm.bij hχ.inf (fun a => ?_) k
    refine ⟨∏ τ, labLL D τ a, ?_, ?_⟩
    · rw [map_prod, ← D.eTau.prod_comp]
      exact Finset.prod_congr rfl fun τ _ => embLL_embE D _
    · rw [map_prod, ← D.eTau.prod_comp, ← hb.prod_comp]
      exact Finset.prod_congr rfl fun ρ _ => RingHom.congr_fun (hl ρ) a
  obtain ⟨n, hn, ho⟩ := GlobalTheory.Mem.FinOrder.finite_order_of_inf_eq_one _ _ hinf
  have hp : ∀ x, (χ' * χ⁻¹).1 x ^ n = 1 := fun x => congrArg (fun ξ : HChar D.host.E => ξ.1 x) ho
  have hξ : IsClsF D.host (χ' * χ⁻¹) := by
    refine ⟨HChar.isUnitary_of_order hn ho, fun P => (hu' P).mul (hχ.unr P).inv, hinf, fun v k => ?_, fun w k => ?_⟩
    · rw [HChar.resFin_mul, HChar.resFin_inv, mul_inv_eq_one]
      exact resFin_eq D.what₂.embLL σ hχ.unr hu' y hy hy' hcm.rank
        (GlobalTheory.BaseChangeExistsCompare.unram_of_cm D D.sp.cm) hχ.res v k
    · rw [HChar.resInf_apply]
      exact Finset.prod_eq_one fun w' _ => GlobalTheory.ToricDistribution.locInf_of_pow hn.ne' hp w' _
  have := hχ.mul_cls hξ
  rwa [mul_comm χ', mul_inv_cancel_left] at this

theorem resEta_hasInfExp_of_isEtaConj : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.Char F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), OverK σ → ∀ η', IsEtaConj σ R.eta η' → ResEta D η' 1 ∧ ∀ ρ, HasInfExp D η' ρ (1 / 2) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR _ σ hσ η' hη
  obtain ⟨χ', hc⟩ := GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D η' hη.1
  have h := isEtaT_of_conj hσ hR.lev.eta hc R.C.isEta hη
  have he := GlobalTheory.Mem.EtaTilde.isEta_res D η' χ' hc h
  refine ⟨⟨⟨_, he⟩, fun η hη' a => ?_⟩, fun τ => ⟨1, by norm_num, ?_, fun θ hθ x hx hx' => ?_⟩⟩
  · rw [(GlobalTheory.IdeleNormChar.existsUnique_isEta D).unique hη' he, pow_one, MonoidHom.comp_apply]
  · obtain ⟨⟨θ', hθ'⟩, -⟩ := GlobalTheory.Member.infiniteAdele_bijective D
    exact ⟨fun τ => θ' (tauE D τ), fun τ => hθ' _⟩
  · rw [GlobalTheory.Mem.EtaTilde.val_infinite D η' χ' hc h.unr _ h.inf θ hθ x hx,
      Finset.prod_eq_single τ (fun τ' _ hτ => by rw [hx' τ' hτ]; simp) (by simp)]

end GlobalTheory.EtaConjType
