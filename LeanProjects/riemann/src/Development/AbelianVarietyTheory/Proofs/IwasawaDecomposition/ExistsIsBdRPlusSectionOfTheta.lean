import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.MemLoc.SecEx

theorem exists_lift {K L S C : Type} [Field K] [Field L] [Algebra K L] [Algebra.IsSeparable K L]
    [CommRing S] [CommRing C] (q : K →+* S) (T : S →+* C) (hT : Function.Surjective T) (I : Ideal S)
    (hI : I = RingHom.ker T) (f : L →+* C) (hf : ∀ k, f (algebraMap K L k) = T (q k)) :
    ∃ g : L →+* AdicCompletion I S,
      (∀ x, ∃ s, AdicCompletion.evalₐ I 1 (g x) = Ideal.Quotient.mk _ s ∧ T s = f x) ∧
      ∀ k, g (algebraMap K L k) = algebraMap S _ (q k) := by
  subst hI
  letI : Algebra K S := q.toAlgebra
  haveI : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
  let e := RingHom.quotientKerEquivOfSurjective hT
  have he : ∀ s, e (Ideal.Quotient.mk _ s) = T s := fun s => rfl
  let f' : L →ₐ[K] S ⧸ RingHom.ker T :=
    { (e.symm : C →+* S ⧸ RingHom.ker T).comp f with
      commutes' := fun k => by
        change e.symm (f (algebraMap K L k)) = Ideal.Quotient.mk _ (q k)
        rw [hf, ← he, RingEquiv.symm_apply_apply] }
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_adicCompletionEvalOneₐ_comp_eq f'
  refine ⟨g.toRingHom, fun x => ?_, fun k => ?_⟩
  · obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (RingHom.ker T) 1 (g x))
    refine ⟨s, hs.symm, ?_⟩
    have h1 : AdicCompletion.evalOneₐ (RingHom.ker T) (g x) = e.symm (f x) := congr($hg x)
    rw [← AdicCompletion.factorₐ_evalₐ_one, ← hs] at h1
    rw [← he]
    exact (e.eq_symm_apply).1 h1
  · exact g.commutes k

variable (l : ℕ) [Fact l.Prime]

theorem ker_localizedTheta_eq_span_eisenstein : Per.kerP l = RingHom.ker (Per.θP l) := by
  ext a
  refine ⟨fun h => GlobalTheory.RingBasics.fontaineTheta_eq_zero_of_mem_ker l a (by rwa [pow_one]), fun h => ?_⟩
  obtain ⟨⟨x, s⟩, hx⟩ := IsLocalization.surj (Submonoid.powers ((l : ℕ) : Per.Ainf l)) a
  have h0 : Per.θP l a = 0 := h
  have h1 := congrArg (Per.θP l) hx
  rw [map_mul, h0, zero_mul, GlobalTheory.RingIface.fontaineTheta_algebraMap] at h1
  have h2 : Per.θ l x = 0 := Subtype.ext h1.symm
  have h3 := GlobalTheory.RingIface.alg_mem_kerP l h2
  rw [← hx] at h3
  exact (Ideal.mul_unit_mem_iff_mem _ (IsLocalization.map_units (Per.AinfP l) s)).1 h3

theorem fontaineTheta_algebraMap₂ (a : Per.Ainf l) : Per.θP l (algebraMap _ _ a) = (Per.θ l a : ℂ_[l]) :=
  GlobalTheory.RingIface.fontaineTheta_algebraMap l a

theorem θ_surjective : Function.Surjective (Per.θ l) := by
  refine surjective_fontaineTheta fun x => ?_
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (y : ℂ_[l]) (Fact.out : l.Prime).pos
  have hz1 : ‖z‖ ≤ 1 := by
    have := (GlobalTheory.RingBasics.mem_OC _).1 y.2
    rw [← hz, norm_pow] at this
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) (Fact.out : l.Prime).ne_zero).1 this
  refine ⟨Ideal.Quotient.mk _ ⟨z, (GlobalTheory.RingBasics.mem_OC _).2 hz1⟩, ?_⟩
  rw [frobenius_def]
  exact (map_pow (Ideal.Quotient.mk _) _ _).symm.trans (congrArg _ (Subtype.ext hz))

theorem fontaineTheta_surjective : Function.Surjective (Per.θP l) := by
  intro c
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ‖(l : ℂ_[l])‖ ^ n * ‖c‖ ≤ 1 := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (GlobalTheory.RingBasics.norm_p_lt (p := l))).mul_const ‖c‖
    rw [zero_mul] at h
    exact (h.eventually (ge_mem_nhds one_pos)).exists
  obtain ⟨a, ha⟩ := θ_surjective l ⟨(l : ℂ_[l]) ^ n * c, (GlobalTheory.RingBasics.mem_OC _).2 (by rwa [norm_mul, norm_pow])⟩
  obtain ⟨u, hu⟩ := (GlobalTheory.RingBasics.isUnit_l l).exists_right_inv
  have h1 := congrArg (Per.θP l) hu
  rw [map_mul, map_natCast, map_one] at h1
  refine ⟨u ^ n * algebraMap _ _ a, ?_⟩
  rw [map_mul, map_pow, fontaineTheta_algebraMap₂, ha]
  change Per.θP l u ^ n * ((l : ℂ_[l]) ^ n * c) = c
  rw [← mul_assoc, ← mul_pow, mul_comm _ (l : ℂ_[l]), h1, one_pow, one_mul]

theorem θ_zA (z : ℤ_[l]) :
    (Per.θ l (Per.zA l z) : ℂ_[l]) = ((algebraMap ℚ_[l] (Om l) (z : ℚ_[l]) : Om l) : ℂ_[l]) := by
  let F : ℤ_[l] →+* ℂ_[l] := (algebraMap (Per.OC l) ℂ_[l]).comp ((Per.θ l).comp (Per.zA l))
  let G : ℤ_[l] →+* ℂ_[l] :=
    (algebraMap (Om l) ℂ_[l]).comp ((algebraMap ℚ_[l] (Om l)).comp (algebraMap ℤ_[l] ℚ_[l]))
  have hF : ∀ w, ‖F w‖ ≤ 1 := fun w => (GlobalTheory.RingBasics.mem_OC _).1 (Per.θ l (Per.zA l w)).2
  have hG : ∀ w, ‖G w‖ ≤ 1 := fun w => by
    change ‖((algebraMap ℚ_[l] (Om l) (w : ℚ_[l]) : Om l) : ℂ_[l])‖ ≤ 1
    rw [PadicComplex.norm_extends, PadicAlgCl.norm_extends]
    exact w.2
  change F z = G z
  have hb : ∀ n : ℕ, ‖F z - G z‖ ≤ ‖(l : ℂ_[l])‖ ^ n * 2 := fun n => by
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n z)
    have hz : z = (z.appr n : ℤ_[l]) + (l : ℤ_[l]) ^ n * w := by rw [mul_comm, hw]; ring
    have : F z - G z = (l : ℂ_[l]) ^ n * (F w - G w) := by
      rw [hz]
      simp only [map_add, map_mul, map_pow, map_natCast]
      ring
    rw [this, norm_mul, norm_pow]
    refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans ?_) (by positivity)
    linarith [hF w, hG w]
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (GlobalTheory.RingBasics.norm_p_lt (p := l))).mul_const 2
  rw [zero_mul] at h
  exact sub_eq_zero.1 (norm_le_zero_iff.1 (ge_of_tendsto' h hb))

theorem isUnit_padicIntMap (y : nonZeroDivisors ℤ_[l]) : IsUnit (Per.zP l y) := by
  have h0 : (y : ℤ_[l]) ≠ 0 := nonZeroDivisors.ne_zero y.2
  have h1 := congrArg (Per.zP l) (PadicInt.unitCoeff_spec h0)
  rw [map_mul, map_pow, map_natCast] at h1
  rw [h1]
  exact ((PadicInt.unitCoeff h0).isUnit.map _).mul ((GlobalTheory.RingBasics.isUnit_l l).pow _)

def qP : ℚ_[l] →+* Per.AinfP l := IsLocalization.lift (isUnit_padicIntMap l)

theorem qP_coe (z : ℤ_[l]) : qP l (z : ℚ_[l]) = Per.zP l z := IsLocalization.lift_eq (isUnit_padicIntMap l) z

theorem algebraMap_eq_fontaineTheta_padicMap (k : ℚ_[l]) :
    algebraMap (Om l) ℂ_[l] (algebraMap ℚ_[l] (Om l) k) = Per.θP l (qP l k) := by
  refine RingHom.congr_fun (IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[l])
    (j := (algebraMap (Om l) ℂ_[l]).comp (algebraMap ℚ_[l] (Om l)))
    (k := (Per.θP l).comp (qP l)) (RingHom.ext fun z => ?_)) k
  change algebraMap (Om l) ℂ_[l] (algebraMap ℚ_[l] (Om l) (z : ℚ_[l])) = Per.θP l (qP l (z : ℚ_[l]))
  rw [qP_coe, GlobalTheory.RingIface.padicIntMap_eq_algebraMap_comp]
  exact ((fontaineTheta_algebraMap₂ l _).trans (θ_zA l z)).symm

theorem exists_isSec (l : ℕ) [Fact l.Prime] : ∃ o : Om l →+* Per.BdRp l, IsSec o := by
  obtain ⟨g, h1, h2⟩ := exists_lift (qP l) (Per.θP l) (fontaineTheta_surjective l) (Per.kerP l) (ker_localizedTheta_eq_span_eisenstein l)
    (algebraMap (Om l) ℂ_[l]) (algebraMap_eq_fontaineTheta_padicMap l)
  obtain ⟨e, he1, he2⟩ := GlobalTheory.RingIface.exists_bdRp_equiv l
  refine ⟨(e.symm : _ →+* Per.BdRp l).comp g, fun x => ?_, fun z => ?_⟩
  · obtain ⟨s, hs, hs'⟩ := h1 x
    have h3 : Per.ev l 1 (e.symm (g x)) = Ideal.Quotient.mk _ s := by
      rw [← he2, RingEquiv.apply_symm_apply, hs]
    have h4 : e.symm (g x) - algebraMap (Per.AinfP l) (Per.BdRp l) s ∈ Per.FilP l 1 := by
      rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, map_sub, h3, GlobalTheory.RingIface.ev_alg, sub_self]
    have h5 := GlobalTheory.RingIface.thetaD_of_mem_FilP l h4
    rw [map_sub, GlobalTheory.RingIface.thetaD_alg, sub_eq_zero] at h5
    exact h5.trans hs'
  · have h3 : e.symm (g (algebraMap ℚ_[l] (Om l) (z : ℚ_[l]))) =
        algebraMap (Per.AinfP l) (Per.BdRp l) (algebraMap (Per.Ainf l) (Per.AinfP l) (Per.zA l z)) := by
      rw [h2, qP_coe, GlobalTheory.RingIface.padicIntMap_eq_algebraMap_comp, ← he1, RingEquiv.symm_apply_apply]
    exact h3

end GlobalTheory.MemLoc.SecEx
