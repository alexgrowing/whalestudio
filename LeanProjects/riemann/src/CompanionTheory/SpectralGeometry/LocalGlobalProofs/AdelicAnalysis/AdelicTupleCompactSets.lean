import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Cpt

section Adele

variable (F : Type) [Field F] [NumberField F]

def intAd : Set (Af F) := {a | ∀ v, a v ∈ v.adicCompletionIntegers F}

def latN (N : ℕ) : Set (Af F) := {y | (N : Af F) * y ∈ intAd F}

theorem isOpen_intAd : IsOpen (intAd F) :=
  RestrictedProduct.isOpen_forall_mem (fun _ => Valued.isOpen_valuationSubring _)

theorem isOpen_latN (N : ℕ) : IsOpen (latN F N) :=
  (isOpen_intAd F).preimage (continuous_const.mul continuous_id)

theorem isCompact_latN (N : ℕ) (hN : 0 < N) : IsCompact (latN F N) := by
  have hN' : (N : F) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  set u : Af F := algebraMap F (Af F) (N : F)⁻¹ with hu
  have hNu : (N : Af F) * u = 1 := by
    have : (N : Af F) = algebraMap F (Af F) (N : F) := by simp
    rw [this, hu, ← map_mul, mul_inv_cancel₀ hN', map_one]
  have h : latN F N = (fun y => u * y) '' intAd F := by
    ext y
    constructor
    · intro hy
      exact ⟨(N : Af F) * y, hy, by
        change u * ((N : Af F) * y) = y
        rw [← mul_assoc, mul_comm u, hNu, one_mul]⟩
    · rintro ⟨z, hz, rfl⟩
      change (N : Af F) * (u * z) ∈ intAd F
      rwa [← mul_assoc, hNu, one_mul]
  rw [h]
  exact (GlobalTheory.AdeleCocompact.isCompact_integral F).image (continuous_const.mul continuous_id)

theorem natCast_apply (c : ℕ) (y : Af F) (v : HeightOneSpectrum (𝓞 F)) :
    ((c : Af F) * y) v = (c : v.adicCompletion F) * y v := by
  have h : ((c : Af F)) v = (c : v.adicCompletion F) := map_natCast (evalV F v) c
  rw [← h]
  rfl

theorem mem_latN_iff (N : ℕ) (y : Af F) :
    y ∈ latN F N ↔ ∀ v, (N : v.adicCompletion F) * y v ∈ v.adicCompletionIntegers F := by
  change (∀ v, ((N : Af F) * y) v ∈ _) ↔ _
  simp only [natCast_apply]

theorem latN_mono {N N' : ℕ} (h : N ∣ N') : latN F N ⊆ latN F N' := by
  obtain ⟨c, rfl⟩ := h
  intro y hy
  rw [mem_latN_iff] at hy ⊢
  intro v
  have := mul_mem (natCast_mem (v.adicCompletionIntegers F) c) (hy v)
  convert this using 1
  push_cast
  ring

theorem exists_nat_mul_mem (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    ∃ N : ℕ, 0 < N ∧ (N : v.adicCompletion F) * x ∈ v.adicCompletionIntegers F := by
  obtain ⟨b, hb, hbx⟩ := HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hN : Ideal.absNorm (Ideal.span {b}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    simpa using hb0
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {b}))
  refine ⟨_, Nat.pos_of_ne_zero hN, ?_⟩
  have hcast : ((Ideal.absNorm (Ideal.span {b}) : ℕ) : v.adicCompletion F) =
      algebraMap (𝓞 F) (v.adicCompletion F) c * algebraMap (𝓞 F) (v.adicCompletion F) b := by
    rw [← map_mul, hc, map_natCast]
  rw [hcast]
  have hcm : algebraMap (𝓞 F) (v.adicCompletion F) c ∈ v.adicCompletionIntegers F :=
    HeightOneSpectrum.coe_mem_adicCompletionIntegers v c
  have hm : algebraMap (𝓞 F) (v.adicCompletion F) c *
      (x * algebraMap (𝓞 F) (v.adicCompletion F) b) ∈ v.adicCompletionIntegers F := mul_mem hcm hbx
  convert hm using 1
  ring

theorem exists_mem_latN (y : Af F) : ∃ N : ℕ, 0 < N ∧ y ∈ latN F N := by
  classical
  choose Nf hpos hNf using fun v => exists_nat_mul_mem F v (y v)
  have hfin : {v | y v ∉ v.adicCompletionIntegers F}.Finite := y.2
  refine ⟨∏ v ∈ hfin.toFinset, Nf v, Finset.prod_pos fun v _ => hpos v, ?_⟩
  rw [mem_latN_iff]
  intro v
  by_cases hv : y v ∈ v.adicCompletionIntegers F
  · exact mul_mem (natCast_mem _ _) hv
  · obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem Nf (hfin.mem_toFinset.mpr hv)
    rw [hc]
    have := mul_mem (natCast_mem (v.adicCompletionIntegers F) c) (hNf v)
    convert this using 1
    push_cast
    ring

theorem exists_latN_of_isCompact {L : Set (Af F)} (hL : IsCompact L) :
    ∃ N : ℕ, 0 < N ∧ L ⊆ latN F N := by
  obtain ⟨⟨N, hN⟩, h⟩ := hL.elim_directed_cover (fun N : {N : ℕ // 0 < N} => latN F N.1)
    (fun N => isOpen_latN F N.1)
    (fun y _ => by
      obtain ⟨N, hN, hy⟩ := exists_mem_latN F y
      exact Set.mem_iUnion.mpr ⟨⟨N, hN⟩, hy⟩)
    (fun N N' => ⟨⟨N.1 * N'.1, Nat.mul_pos N.2 N'.2⟩, latN_mono F (Dvd.intro _ rfl),
      latN_mono F (Dvd.intro_left _ rfl)⟩)
  exact ⟨N, hN, h⟩

end Adele

section Tens

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem repr_map {d : ℕ} (b : Module.Basis (Fin d) F E) {R R' : Type} [CommRing R] [CommRing R']
    [Algebra F R] [Algebra F R'] (f : R →ₐ[F] R') (y : R ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map f (AlgHom.id F E) y) k =
      f ((Algebra.TensorProduct.basis R b).repr y k) := by
  induction y with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul r e =>
    simp [Algebra.TensorProduct.basis_repr_tmul, Finsupp.mapRange_apply]

theorem repr_natCast_mul {d : ℕ} (b : Module.Basis (Fin d) F E) {R : Type} [CommRing R]
    [Algebra F R] (N : ℕ) (y : R ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis R b).repr ((N : R ⊗[F] E) * y) k =
      (N : R) * (Algebra.TensorProduct.basis R b).repr y k := by
  rw [← nsmul_eq_mul, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]

end Tens

section Coord

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def coordA {d n M : ℕ} (b : Module.Basis (Fin d) F E) (X : Fin n → Fin M → AF F ⊗[F] E) :
    Fin n → Fin M → Fin d → AF F :=
  fun a i k => (Algebra.TensorProduct.basis (AF F) b).repr (X a i) k

def sizeA {d n M : ℕ} (Z : Fin n → Fin M → Fin d → AF F) : ℝ :=
  ∑ a, ∑ i, ∑ k, ∑ v : InfinitePlace F, ‖fstA F (Z a i k) v‖

theorem fin_iff {d n M : ℕ} (b : Module.Basis (Fin d) F E) (N : ℕ)
    (X : Fin n → Fin M → AF F ⊗[F] E) :
    (∀ v, (fun a i => (N : Fv F v ⊗[F] E) * projV v (projFin X) a i) ∈ latV b v) ↔
      ∀ a i k, sndA F (coordA b X a i k) ∈ latN F N := by
  have key : ∀ v a i k, (Algebra.TensorProduct.basis (Fv F v) b).repr
      ((N : Fv F v ⊗[F] E) * projV v (projFin X) a i) k =
        (N : Fv F v) * (sndA F (coordA b X a i k)) v := by
    intro v a i k
    rw [repr_natCast_mul]
    simp only [projV, projFin, coordA]
    rw [repr_map, repr_map]
    rfl
  constructor
  · intro h a i k
    rw [mem_latN_iff]
    intro v
    rw [← key]
    exact h v a i k
  · intro h v a i k
    change (Algebra.TensorProduct.basis (Fv F v) b).repr
      ((N : Fv F v ⊗[F] E) * projV v (projFin X) a i) k ∈ _
    rw [key]
    exact (mem_latN_iff F N _).1 (h a i k) v

theorem size_eq {d n M : ℕ} (b : Module.Basis (Fin d) F E) (X : Fin n → Fin M → AF F ⊗[F] E) :
    sizeTup b (projInf X) = sizeA (coordA b X) := by
  simp only [sizeTup, sizeInf, sizeA, projInf, coordA, repr_map]

theorem continuous_fstA : Continuous (fstA F) := continuous_fst

theorem continuous_sndA : Continuous (sndA F) := continuous_snd

theorem continuous_coord {d n M : ℕ} (a : Fin n) (i : Fin M) (k : Fin d) :
    Continuous fun Z : Fin n → Fin M → Fin d → AF F => Z a i k :=
  (continuous_apply k).comp ((continuous_apply i).comp (continuous_apply a))

theorem continuous_sizeA {d n M : ℕ} :
    Continuous (sizeA : (Fin n → Fin M → Fin d → AF F) → ℝ) := by
  unfold sizeA
  refine continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun i _ =>
    continuous_finset_sum _ fun k _ => continuous_finset_sum _ fun v _ => ?_
  exact (((continuous_apply v).comp (continuous_fstA.comp
    (continuous_coord a i k)))).norm

theorem norm_le_sizeA {d n M : ℕ} (Z : Fin n → Fin M → Fin d → AF F) (a i k)
    (v : InfinitePlace F) : ‖fstA F (Z a i k) v‖ ≤ sizeA Z := by
  have h1 : ‖fstA F (Z a i k) v‖ ≤ ∑ v : InfinitePlace F, ‖fstA F (Z a i k) v‖ :=
    Finset.single_le_sum (f := fun v : InfinitePlace F => ‖fstA F (Z a i k) v‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ v)
  have h2 : ∑ v : InfinitePlace F, ‖fstA F (Z a i k) v‖ ≤
      ∑ k, ∑ v : InfinitePlace F, ‖fstA F (Z a i k) v‖ :=
    Finset.single_le_sum (f := fun k => ∑ v : InfinitePlace F, ‖fstA F (Z a i k) v‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ k)
  have h3 : ∑ k, ∑ v : InfinitePlace F, ‖fstA F (Z a i k) v‖ ≤
      ∑ i, ∑ k, ∑ v : InfinitePlace F, ‖fstA F (Z a i k) v‖ :=
    Finset.single_le_sum (f := fun i => ∑ k, ∑ v : InfinitePlace F, ‖fstA F (Z a i k) v‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (Finset.mem_univ i)
  have h4 : ∑ i, ∑ k, ∑ v : InfinitePlace F, ‖fstA F (Z a i k) v‖ ≤ sizeA Z :=
    Finset.single_le_sum (f := fun a => ∑ i, ∑ k, ∑ v : InfinitePlace F, ‖fstA F (Z a i k) v‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ a)
  exact h1.trans (h2.trans (h3.trans h4))

variable (F) in

def boxT (d n M N : ℕ) (r : ℝ) : Set (Fin n → Fin M → Fin d → AF F) :=
  {Z | (∀ a i k, sndA F (Z a i k) ∈ latN F N) ∧ sizeA Z ≤ r}

theorem isCompact_boxT (d n M N : ℕ) (r : ℝ) (hN : 0 < N) : IsCompact (boxT F d n M N r) := by
  haveI := GlobalTheory.AdeleCocompact.properSpace_completion F
  haveI := GlobalTheory.CompanionTheory.AdeleTop.t2Space_finiteAdeleRing_of_numberField F
  have hB : IsCompact (Set.pi Set.univ fun v : InfinitePlace F => Metric.closedBall (0 : v.Completion) r) :=
    isCompact_univ_pi fun v => isCompact_closedBall _ _
  have hP : IsCompact ((Set.pi Set.univ fun v : InfinitePlace F => Metric.closedBall (0 : v.Completion) r) ×ˢ
      latN F N : Set (AF F)) := hB.prod (isCompact_latN F N hN)
  have hBig : IsCompact (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin M =>
      Set.pi Set.univ fun _ : Fin d =>
        ((Set.pi Set.univ fun v : InfinitePlace F => Metric.closedBall (0 : v.Completion) r) ×ˢ
          latN F N : Set (AF F))) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hP
  refine hBig.of_isClosed_subset ?_ ?_
  · have h1 : IsClosed {Z : Fin n → Fin M → Fin d → AF F | ∀ a i k, sndA F (Z a i k) ∈ latN F N} := by
      simp only [Set.setOf_forall]
      refine isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun k => ?_
      exact (isCompact_latN F N hN).isClosed.preimage (continuous_sndA.comp
        (continuous_coord a i k))
    exact h1.inter (isClosed_le continuous_sizeA continuous_const)
  · rintro Z ⟨h1, h2⟩ a - i - k -
    refine ⟨fun v _ => ?_, h1 a i k⟩
    rw [mem_closedBall_zero_iff]
    exact (norm_le_sizeA Z a i k v).trans h2

end Coord

theorem compact_tuples : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ), (∀ (N : ℕ) (r : ℝ), 0 < N → IsCompact {X : (Fin n → Fin M → AF F ⊗[F] E) | (∀ v, (fun a i => (N : Fv F v ⊗[F] E) * projV v (projFin X) a i) ∈ latV b v) ∧ sizeTup b (projInf X) ≤ r}) ∧ ∀ K : Set (Fin n → Fin M → AF F ⊗[F] E), IsCompact K → ∃ (N : ℕ) (r : ℝ), 0 < N ∧ 0 < r ∧ ∀ X ∈ K, (∀ v, (fun a i => (N : Fv F v ⊗[F] E) * projV v (projFin X) a i) ∈ latV b v) ∧ sizeTup b (projInf X) ≤ r := by
  intro F E _ _ _ _ _ σ hσ d b n M
  obtain ⟨⟨h1, h2, h3⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  have hh := (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (AF F)).2.2.2.2.2.2.1 d b
  let e1 : (AF F ⊗[F] E) ≃ₜ (Fin d → AF F) := hh.homeomorph
  let e : (Fin n → Fin M → AF F ⊗[F] E) ≃ₜ (Fin n → Fin M → Fin d → AF F) :=
    Homeomorph.piCongrRight fun _ => Homeomorph.piCongrRight fun _ => e1
  have he : ∀ X, e X = coordA b X := fun _ => rfl
  constructor
  · intro N r hN
    have hset : {X : (Fin n → Fin M → AF F ⊗[F] E) |
        (∀ v, (fun a i => (N : Fv F v ⊗[F] E) * projV v (projFin X) a i) ∈ latV b v) ∧
          sizeTup b (projInf X) ≤ r} = e ⁻¹' boxT F d n M N r := by
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_preimage, boxT, he, fin_iff, size_eq]
    rw [hset, e.isCompact_preimage]
    exact isCompact_boxT d n M N r hN
  · intro K hK
    have hK' : IsCompact (e '' K) := hK.image e.continuous
    have hL : IsCompact (⋃ a, ⋃ i, ⋃ k, (fun Z : Fin n → Fin M → Fin d → AF F => sndA F (Z a i k)) '' (e '' K)) :=
      isCompact_iUnion fun a => isCompact_iUnion fun i => isCompact_iUnion fun k =>
        hK'.image (continuous_sndA.comp
          (continuous_coord a i k))
    obtain ⟨N, hN, hNL⟩ := exists_latN_of_isCompact F hL
    obtain ⟨r, hr⟩ := (hK'.image continuous_sizeA).bddAbove
    refine ⟨N, max r 1, hN, lt_max_of_lt_right one_pos, fun X hX => ⟨?_, ?_⟩⟩
    · rw [fin_iff]
      intro a i k
      exact hNL (Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨k,
        ⟨e X, ⟨X, hX, rfl⟩, rfl⟩⟩⟩⟩)
    · rw [size_eq]
      exact (hr ⟨e X, ⟨X, hX, rfl⟩, rfl⟩).trans (le_max_left _ _)

end GlobalTheory.CompanionTheory.SW.Cpt
