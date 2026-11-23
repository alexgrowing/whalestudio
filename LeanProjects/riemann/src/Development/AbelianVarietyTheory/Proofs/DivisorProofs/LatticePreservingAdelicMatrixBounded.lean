import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncMatTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCompactLatticeStabilizerBoundedReal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.ContinuousTensMap
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.EntriesCompact

open PI.UnitaryGroupMassFormula.MeasWCore Formalism.L2.SG.Measures

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem tensMap_smul {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']
    (φ : R →ₐ[F] R') (c : R) (x : R ⊗[F] E) : tensMap φ (c • x) = φ c • tensMap φ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [tensMap, TensorProduct.smul_tmul', smul_eq_mul, map_mul]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

theorem tensMap_inclR {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']
    (φ : R →ₐ[F] R') (e : E) : tensMap φ (inclR R e) = inclR R' e := by
  simp [tensMap, inclR]

theorem crd_inclR {n : ℕ} (b : Module.Basis (Fin n) F E) (R : Type) [CommRing R] [Algebra F R]
    (e : E) (l : Fin n) : crd b R (inclR R e) l = algebraMap F R (b.repr e l) := by
  simp [crd, inclR, Algebra.TensorProduct.basis_repr_tmul]

end SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}

theorem mem_intRing_iff (a : Af F) :
    a ∈ GlobalTheory.HolDict.ShortVec.intRing F ↔ ∀ v : Pl F, evalV F v a ∈ HeightOneSpectrum.adicCompletionIntegers F v := by
  simp [GlobalTheory.HolDict.ShortVec.intRing, Subring.mem_iInf]

theorem at_liftV_one (v : Pl F) : At (evFin F v) (GlobalTheory.LatVac.liftV v 1) := by
  intro u hu
  change u * GlobalTheory.LatVac.liftV v 1 = 0
  refine Prod.ext ?_ (af_ext fun t => ?_)
  · change u.1 * 0 = 0
    exact mul_zero _
  change evalV F t (u.2 * singleFin v 1) = evalV F t 0
  rw [map_mul, map_zero]
  by_cases h : t = v
  · subst h
    rw [evalV_singleFin_self, mul_one]
    exact hu
  · rw [evalV_singleFin_ne h, mul_zero]

theorem test_mem (W : Spc F E d) (v : Pl F) (y : Fin d → E) (hy : y ∈ W.L) :
    (GlobalTheory.LatVac.liftV v 1 • fun i => inclR (AF F) (y i)) ∈ GlobalTheory.InertSph.latAt W v :=
  AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v 1, at_liftV_one v,
    by rw [GlobalTheory.LatVac.evFin_liftV]; exact one_mem _, y, hy, rfl⟩

def intAt (v : Pl F) : Subring (Af F) :=
  (HeightOneSpectrum.adicCompletionIntegers F v).toSubring.comap (evalV F v).toRingHom

theorem mem_intAt (v : Pl F) (a : Af F) :
    a ∈ intAt v ↔ evalV F v a ∈ HeightOneSpectrum.adicCompletionIntegers F v := Iff.rfl

theorem coord_mem {n : ℕ} (b : Module.Basis (Fin n) F E) (W : Spc F E d) (v : Pl F) (N : ℕ) {m : ℕ}
    (x : Fin m → Fin d → E) (hx : Submodule.span ℤ (Set.range x) = W.L.restrictScalars ℤ)
    (hN : ∀ k i l, (N : Af F) * algebraMap F (Af F) (b.repr (x k i) l) ∈ intAt v) :
    ∀ z ∈ GlobalTheory.InertSph.latAt W v, ∀ i l,
      (N : Af F) * crd b (Af F) (tensMap (sndA F) (z i)) l ∈ intAt v := by
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, -, ha, y, hy, rfl⟩ := hz
    have hy' : y ∈ Submodule.span ℤ (Set.range x) := by rw [hx]; exact hy
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hy'
    intro i l
    have ha' : sndA F a ∈ intAt v := ha
    rw [Pi.smul_apply, tensMap_smul, tensMap_inclR, map_smul, Pi.smul_apply, crd_inclR, smul_eq_mul]
    have hrep : b.repr ((∑ k, c k • x k) i) l = ∑ k, (c k : F) * b.repr (x k i) l := by
      rw [Finset.sum_apply, map_sum, Finsupp.finset_sum_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Pi.smul_apply, map_zsmul, Finsupp.smul_apply, zsmul_eq_mul]
    rw [hrep, map_sum, Finset.mul_sum, Finset.mul_sum]
    refine Subring.sum_mem _ fun k _ => ?_
    rw [map_mul, map_intCast]
    have e : (N : Af F) * (sndA F a * ((c k : Af F) * algebraMap F (Af F) (b.repr (x k i) l))) =
        sndA F a * ((c k : Af F) * ((N : Af F) * algebraMap F (Af F) (b.repr (x k i) l))) := by ring
    rw [e]
    exact mul_mem ha' (mul_mem (intCast_mem _ _) (hN k i l))
  | zero =>
    intro i l
    simp only [Pi.zero_apply, map_zero, mul_zero]
    exact zero_mem _
  | add y z _ _ hy hz =>
    intro i l
    simp only [Pi.add_apply, map_add, mul_add]
    exact add_mem (hy i l) (hz i l)
  | neg y _ hy =>
    intro i l
    simp only [Pi.neg_apply, map_neg, mul_neg]
    exact neg_mem (hy i l)

theorem entries_mem_compact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (W : Spc F E d), W.L.IsLattice E → ∃ K : Set (AE F E), IsCompact K ∧ ∀ A : Matrix (Fin d) (Fin d) (AE F E), At (fun a : AF F => a.2) (A - 1) → (∀ v : Pl F, ∀ z ∈ GlobalTheory.InertSph.latAt W v, A *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) → ∀ i j, A i j ∈ K := by
  intro F E _ _ _ _ _ d W hL
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hfg : W.L.FG := Submodule.IsLattice.fg (A := E)
  have hsp : Submodule.span E (W.L : Set (Fin d → E)) = ⊤ := Submodule.IsLattice.span_eq_top
  obtain ⟨m, x, hx⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (hfg.restrictScalars (R := ℤ))
  choose e he0 heI using fun p : Fin m × Fin d × Fin (Module.finrank F E) =>
    GlobalTheory.HolDict.ShortVec.exists_denom_adele (F := F)
      (algebraMap F (Af F) ((Module.finBasis F E).repr (x p.1 p.2.1) p.2.2))
  have hN : ∀ v k i l, ((∏ p, e p : ℕ) : Af F) *
      algebraMap F (Af F) ((Module.finBasis F E).repr (x k i) l) ∈ intAt v := by
    intro v k i l
    have h := (mem_intRing_iff _).1 (heI (k, i, l)) v
    have he : ((∏ p, e p : ℕ) : Af F) =
        ((∏ p ∈ Finset.univ.erase (k, i, l), e p : ℕ) : Af F) * (e (k, i, l) : Af F) := by
      rw [← Nat.cast_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ _)]
    rw [he, mul_assoc]
    exact mul_mem (natCast_mem _ _) h
  have hN0 : 0 < ∏ p, e p := Finset.prod_pos fun p _ => he0 p
  choose dd hdd0 hddL using fun j : Fin d => GlobalTheory.AdLat.OpenLat.exists_denom W.L hsp (Pi.single j 1)
  let I : Set (Af F) := {a | ∀ v : HeightOneSpectrum (𝓞 F), a v ∈ HeightOneSpectrum.adicCompletionIntegers F v}
  have hI : IsCompact I := GlobalTheory.AdeleCocompact.isCompact_integral F
  let S : Set (Fin (Module.finrank F E) → AF F) := ⋃ j : Fin d, ⋃ c ∈ ({0, 1} : Set (AE F E)),
    Set.pi Set.univ fun l => (({crd (Module.finBasis F E) (Ainf F) (tensMap (fstA F) c) l} : Set (Ainf F)) ×ˢ
      ((fun y => algebraMap F (Af F) (((∏ p, e p) * dd j : ℕ) : F)⁻¹ * y) '' I) : Set (Ainf F × Af F))
  have hS : IsCompact S := isCompact_iUnion fun j =>
    (Set.toFinite ({0, 1} : Set (AE F E))).isCompact_biUnion fun c _ =>
      isCompact_univ_pi fun l => isCompact_singleton.prod (hI.image (continuous_const.mul continuous_id))
  refine ⟨(crdH (Module.finBasis F E) (AF F)).symm '' S, hS.image (crdH _ (AF F)).symm.continuous,
    fun A hA hAL i j => ?_⟩
  refine ⟨crd (Module.finBasis F E) (AF F) (A i j), ?_, by
    rw [crdH_symm_apply, LinearEquiv.symm_apply_apply]⟩
  have harch : tensMap (fstA F) (A i j) = tensMap (fstA F) ((1 : Matrix (Fin d) (Fin d) (AE F E)) i j) := by
    let u : AF F := (1, 0)
    have h : u • (A i j - (1 : Matrix (Fin d) (Fin d) (AE F E)) i j) = 0 :=
      congrArg (fun M : Matrix (Fin d) (Fin d) (AE F E) => M i j) (hA u rfl)
    have h2 := congrArg (tensMap (E := E) (fstA F)) h
    rw [tensMap_smul, map_sub, map_zero] at h2
    have h1 : fstA F u = 1 := rfl
    rw [h1, one_smul, sub_eq_zero] at h2
    exact h2
  have hfin : ∀ l, ((((∏ p, e p) * dd j : ℕ)) : Af F) *
      crd (Module.finBasis F E) (Af F) (tensMap (sndA F) (A i j)) l ∈ I := by
    intro l v
    have hz := hAL v _ (test_mem W v _ (hddL j))
    have h := coord_mem (Module.finBasis F E) W v _ x hx (fun k i l => hN v k i l) _ hz i l
    have hcomp : (A *ᵥ (GlobalTheory.LatVac.liftV v 1 • fun k =>
        inclR (AF F) ((dd j • Pi.single j 1 : Fin d → E) k))) i =
        GlobalTheory.LatVac.liftV v 1 • ((dd j : AE F E) * A i j) := by
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply]
      rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp)]
      simp [mul_comm]
    have hcrd : ∀ w : Af F ⊗[F] E, crd (Module.finBasis F E) (Af F) ((dd j : Af F ⊗[F] E) * w) l =
        (dd j : Af F) * crd (Module.finBasis F E) (Af F) w l := by
      intro w
      rw [← nsmul_eq_mul, map_nsmul, Pi.smul_apply, nsmul_eq_mul]
    rw [hcomp, tensMap_smul, map_mul, map_natCast, map_smul, Pi.smul_apply, smul_eq_mul, hcrd] at h
    have h1 : evalV F v (sndA F (GlobalTheory.LatVac.liftV v 1)) = 1 := GlobalTheory.LatVac.evFin_liftV v 1
    have e2 : ((∏ p, e p : ℕ) : Af F) * (sndA F (GlobalTheory.LatVac.liftV v 1) * ((dd j : Af F) *
        crd (Module.finBasis F E) (Af F) (tensMap (sndA F) (A i j)) l)) =
        sndA F (GlobalTheory.LatVac.liftV v 1) * ((((∏ p, e p) * dd j : ℕ) : Af F) *
        crd (Module.finBasis F E) (Af F) (tensMap (sndA F) (A i j)) l) := by
      push_cast; ring
    rw [e2, mem_intAt, map_mul, h1, one_mul] at h
    exact h
  refine Set.mem_iUnion.2 ⟨j, Set.mem_iUnion₂.2 ⟨(1 : Matrix (Fin d) (Fin d) (AE F E)) i j, ?_,
    fun l _ => ?_⟩⟩
  · rw [Matrix.one_apply]
    split_ifs <;> simp
  · rw [crd_AF, splT_apply]
    refine ⟨by rw [harch]; rfl, _, hfin l, ?_⟩
    have hne : ((((∏ p, e p) * dd j : ℕ)) : F) ≠ 0 :=
      Nat.cast_ne_zero.2 (Nat.mul_pos hN0 (hdd0 j)).ne'
    show algebraMap F (Af F) (((∏ p, e p) * dd j : ℕ) : F)⁻¹ *
      ((((∏ p, e p) * dd j : ℕ) : Af F) * crd (Module.finBasis F E) (Af F) (tensMap (sndA F) (A i j)) l) = _
    rw [← mul_assoc, ← map_natCast (algebraMap F (Af F)), ← map_mul, inv_mul_cancel₀ hne, map_one, one_mul]

end GlobalTheory.EntriesCompact
