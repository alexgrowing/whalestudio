import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IntegralFiniteAdeleCompactClosedMultiples

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem denom_fin {K : Set (Af F)} (hK : IsCompact K) :
    ∃ m : ℕ, 0 < m ∧ ∀ x : F, algebraMap F (Af F) x ∈ K → IsIntegral ℤ ((m : F) * x) := by
  have hopen : IsOpen {a : Af F | ∀ v, a v ∈ HeightOneSpectrum.adicCompletionIntegers F v} :=
    RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)
  have hNe : Nonempty {M : ℕ // 0 < M} := ⟨⟨1, Nat.one_pos⟩⟩
  obtain ⟨M, hM⟩ := hK.elim_directed_cover
    (fun M : {M : ℕ // 0 < M} => ⋃ d ∈ {d : ℕ | 0 < d ∧ d ∣ M.1},
      (fun a : Af F => (d : Af F) * a) ⁻¹' {a : Af F | ∀ v, a v ∈ HeightOneSpectrum.adicCompletionIntegers F v})
    (fun M => isOpen_biUnion fun d _ => hopen.preimage (continuous_const.mul continuous_id))
    (fun a _ => by
      obtain ⟨d, hd, h⟩ := GlobalTheory.IntegralFinAdele.exists_nat_mul_integral F a
      exact Set.mem_iUnion.2 ⟨⟨d, hd⟩, Set.mem_iUnion₂.2 ⟨d, ⟨hd, dvd_refl d⟩, h⟩⟩)
    (fun M N => ⟨⟨M.1 * N.1, Nat.mul_pos M.2 N.2⟩, fun a ha => by
      obtain ⟨d, hd, h⟩ := Set.mem_iUnion₂.1 ha
      exact Set.mem_iUnion₂.2 ⟨d, ⟨hd.1, hd.2.mul_right _⟩, h⟩, fun a ha => by
      obtain ⟨d, hd, h⟩ := Set.mem_iUnion₂.1 ha
      exact Set.mem_iUnion₂.2 ⟨d, ⟨hd.1, hd.2.mul_left _⟩, h⟩⟩)
  refine ⟨M.1, M.2, fun x hx => ?_⟩
  obtain ⟨d, hd, h⟩ := Set.mem_iUnion₂.1 (hM hx)
  have h2 : ∀ v, (algebraMap F (Af F) ((d : F) * x)) v ∈ HeightOneSpectrum.adicCompletionIntegers F v := by
    rw [map_mul, map_natCast]
    exact h
  obtain ⟨y, hy⟩ := (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 _ h2
  have hdx : IsIntegral ℤ ((d : F) * x) := by
    rw [hy]
    exact y.isIntegral_coe
  obtain ⟨e, he⟩ := hd.2
  have hei : IsIntegral ℤ (e : F) := by
    have h3 := isIntegral_algebraMap (R := ℤ) (A := F) (x := (e : ℤ))
    simpa using h3
  rw [he, Nat.cast_mul, mul_comm (d : F) (e : F), mul_assoc]
  exact hei.mul hdx

variable (F) in

def uFin : AF F := pairA F 0 1

theorem evI_uFin : evI F (uFin F) = 0 := by
  unfold evI uFin pairA
  exact map_zero _

theorem snd_uFin_mul (a : AF F) : sndA F (uFin F * a) = sndA F a := by
  show (1 : Af F) * a.2 = a.2
  exact one_mul _

theorem uFin_mul_rId (t : ℝ) : uFin F * rId F t = uFin F := by
  show pairA F 0 1 * rId F t = pairA F 0 1
  refine Prod.ext ?_ ?_
  · show (0 : Ainf F) * (rId F t).1 = 0
    exact zero_mul _
  · show (1 : Af F) * ((1 : Af F) + 0) = 1
    simp

theorem exists_int_mul (x : E) : ∃ m : ℕ, 0 < m ∧ IsIntegral ℤ ((m : E) * x) := by
  have hq : IsAlgebraic ℚ x := (Algebra.IsIntegral.isIntegral x).isAlgebraic
  have hz : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr hq
  obtain ⟨d, hd, hy⟩ := hz.exists_integral_multiple
  rw [Algebra.smul_def, eq_intCast] at hy
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg d
  · refine ⟨k, by omega, ?_⟩
    simpa using hy
  · refine ⟨k, by omega, ?_⟩
    have h2 := hy.neg
    simpa using h2
private theorem isIntegral_natCast_mul_of_dvd {A : Type} [CommRing A] {a b : ℕ} (hab : a ∣ b) {y : A}
    (h : IsIntegral ℤ ((a : A) * y)) : IsIntegral ℤ ((b : A) * y) := by
  obtain ⟨e, rfl⟩ := hab
  have he : IsIntegral ℤ (e : A) := by
    have h3 := isIntegral_algebraMap (R := ℤ) (A := A) (x := (e : ℤ))
    simpa using h3
  rw [Nat.cast_mul, mul_comm (a : A) (e : A), mul_assoc]
  exact he.mul h

theorem denom_AE {K : Set (AE F E)} (hK : IsCompact K) :
    ∃ m : ℕ, 0 < m ∧ ∀ x : E, (∃ c ∈ K, uFin F • inclR (F := F) (AF F) x = uFin F • c) → IsIntegral ℤ ((m : E) * x) := by
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.modTop (F := F) (E := E)
  let b := Module.finBasis F E
  let B : Module.Basis (Fin (Module.finrank F E)) (AF F) (AE F E) := Algebra.TensorProduct.basis (AF F) b
  have hcont : ∀ i, Continuous fun c : AE F E => sndA F (B.coord i c) := fun i =>
    continuous_snd.comp (IsModuleTopology.continuous_of_linearMap (B.coord i))
  choose m hm hint using fun i => denom_fin (hK.image (hcont i))
  choose n hn hbi using fun i => exists_int_mul (b i)
  refine ⟨(∏ i, m i) * ∏ i, n i, Nat.mul_pos (Finset.prod_pos fun i _ => hm i) (Finset.prod_pos fun i _ => hn i), ?_⟩
  rintro x ⟨c, hcK, hxc⟩
  have hcoord : ∀ i, algebraMap F (Af F) (b.repr x i) = sndA F (B.coord i c) := by
    intro i
    have h1 := congrArg (fun y => sndA F (B.coord i y)) hxc
    simp only [LinearMap.map_smul, smul_eq_mul, snd_uFin_mul] at h1
    rw [← h1]
    simp [B, inclR, Algebra.TensorProduct.basis_repr_tmul]
  have hr : ∀ i, IsIntegral ℤ (((∏ j, m j : ℕ) : F) * b.repr x i) := fun i =>
    isIntegral_natCast_mul_of_dvd (Finset.dvd_prod_of_mem m (Finset.mem_univ i)) (hint i _ ⟨c, hcK, (hcoord i).symm⟩)
  have hbb : ∀ i, IsIntegral ℤ (((∏ j, n j : ℕ) : E) * b i) := fun i =>
    isIntegral_natCast_mul_of_dvd (Finset.dvd_prod_of_mem n (Finset.mem_univ i)) (hbi i)
  have hx : (((∏ i, m i) * ∏ i, n i : ℕ) : E) * x =
      ∑ i, algebraMap F E (((∏ j, m j : ℕ) : F) * b.repr x i) * (((∏ j, n j : ℕ) : E) * b i) := by
    conv_lhs => rw [← b.sum_repr x]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, map_mul, map_natCast]
    push_cast
    ring
  rw [hx]
  exact (integralClosure ℤ E).sum_mem fun i _ => (hr i).algebraMap.mul (hbb i)

omit [NumberField E] in
theorem piInf_inclR {w : InfinitePlace F} (τ : EmbOver E w) (x : E) : piInf τ (inclR (F := F) (AF F) x) = τ.1 x := by
  simp [piInf, inclR, compInf, infEmb]

omit [NumberField E] in
theorem piInf_rId {w : InfinitePlace F} (τ : EmbOver E w) (t : ℝ) :
    piInf τ (algebraMap (AF F) (AE F E) (rId F t)) = (Real.exp t : ℝ) := by
  simp only [piInf, compInf, infEmb, RingHom.comp_apply, Algebra.TensorProduct.algebraMap_apply,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one]
  show InfinitePlace.Completion.extensionEmbedding w ((rId F t).1 w) = ((Real.exp t : ℝ) : ℂ)
  have hy : InfiniteAdeleRing.ringEquiv_mixedSpace F (rId F t).1 =
      ((fun _ => Real.exp t), (fun _ => ((Real.exp t : ℝ) : ℂ))) := by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (1 + (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
      (algebraMap ℝ (mixedEmbedding.mixedSpace F) (Real.exp t - 1))) = _
    rw [map_add, map_one, RingEquiv.apply_symm_apply]
    refine Prod.ext ?_ ?_ <;> funext v <;> simp
  by_cases hw : w.IsReal
  · have h1 := congrArg (fun z => z.1 ⟨w, hw⟩) hy
    simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply] at h1
    rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw, h1]
  · have h1 := congrArg (fun z => z.2 ⟨w, InfinitePlace.not_isReal_iff_isComplex.1 hw⟩) hy
    simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply] at h1
    exact h1

end PositivityTheory.ThKEst

end
