import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.FibInfEx

noncomputable section

namespace PI.VolStabSW.FiniteThetaCoordinates

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)

def crd (R : Type) [CommRing R] [Algebra F R] (y : R ⊗[F] E) (k : Fin d) : R :=
  (Algebra.TensorProduct.basis R b).repr y k

theorem crd_map {R S : Type} [CommRing R] [Algebra F R] [CommRing S] [Algebra F S]
    (φ : R →ₐ[F] S) (y : R ⊗[F] E) (k : Fin d) :
    crd b S (Algebra.TensorProduct.map φ (AlgHom.id F E) y) k = φ (crd b R y k) := by
  induction y using TensorProduct.induction_on with
  | zero => simp [crd]
  | tmul r e =>
    simp [crd, Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.map_tmul]
  | add x y hx hy =>
    simp only [crd] at hx hy ⊢
    rw [map_add, map_add, Finsupp.add_apply, hx, hy, map_add, Finsupp.add_apply, map_add]

theorem crd_incl (R : Type) [CommRing R] [Algebra F R] (x : E) (k : Fin d) :
    crd b R (inclR R x) k = algebraMap F R (b.repr x k) := by
  simp [crd, inclR, Algebra.TensorProduct.basis_repr_tmul]

theorem crd_add (R : Type) [CommRing R] [Algebra F R] (y z : R ⊗[F] E) (k : Fin d) :
    crd b R (y + z) k = crd b R y k + crd b R z k := by
  simp [crd]

theorem crd_sum (R : Type) [CommRing R] [Algebra F R] {ι : Type} (s : Finset ι) (y : ι → R ⊗[F] E)
    (k : Fin d) : crd b R (∑ i ∈ s, y i) k = ∑ i ∈ s, crd b R (y i) k := by
  simp [crd, map_sum, Finsupp.finsetSum_apply]

theorem eq_sum_crd (R : Type) [CommRing R] [Algebra F R] (y : R ⊗[F] E) :
    y = ∑ i, crd b R y i • ((1 : R) ⊗ₜ[F] b i) := by
  have := (Algebra.TensorProduct.basis R b).sum_repr y
  simp only [Algebra.TensorProduct.basis_apply] at this
  exact this.symm

theorem crd_mul (R : Type) [CommRing R] [Algebra F R] (y z : R ⊗[F] E) (k : Fin d) :
    crd b R (y * z) k = ∑ i, ∑ j, crd b R y i * crd b R z j *
      algebraMap F R (b.repr (b i * b j) k) := by
  conv_lhs => rw [eq_sum_crd b R y, eq_sum_crd b R z]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul, crd_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [crd, map_smul, Finsupp.smul_apply, Algebra.TensorProduct.basis_repr_tmul, smul_eq_mul,
    Finsupp.mapRange_apply, one_mul]

end Coord

section Bounds

variable {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)

theorem crd_mulVec (R : Type) [CommRing R] [Algebra F R] {M : ℕ}
    (m : Matrix (Fin M) (Fin M) (R ⊗[F] E)) (y : Fin M → R ⊗[F] E) (i : Fin M) (k : Fin d) :
    crd b R ((m.mulVec y) i) k = ∑ j, ∑ p, ∑ q, crd b R (m i j) p * crd b R (y j) q *
      algebraMap F R (b.repr (b p * b q) k) := by
  simp only [Matrix.mulVec, dotProduct, crd_sum, crd_mul]

theorem norm_crd_mulVec_le {R K : Type} [CommRing R] [Algebra F R] [NormedField K] (φ : R →+* K)
    {M : ℕ} (m : Matrix (Fin M) (Fin M) (R ⊗[F] E)) (y : Fin M → R ⊗[F] E) {A B C : ℝ}
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : ∀ i j p, ‖φ (crd b R (m i j) p)‖ ≤ A) (hB : ∀ j q, ‖φ (crd b R (y j) q)‖ ≤ B)
    (hC : ∀ p q k, ‖φ (algebraMap F R (b.repr (b p * b q) k))‖ ≤ C) (i : Fin M) (k : Fin d) :
    ‖φ (crd b R ((m.mulVec y) i) k)‖ ≤ M * (d * (d * (A * B * C))) := by
  rw [crd_mulVec]
  simp only [map_sum, map_mul]
  have hterm : ∀ j p q, ‖φ (crd b R (m i j) p) * φ (crd b R (y j) q) *
      φ (algebraMap F R (b.repr (b p * b q) k))‖ ≤ A * B * C := by
    intro j p q
    rw [norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul (hA i j p) (hB j q) (norm_nonneg _) hA0) (hC p q k) (norm_nonneg _)
      (mul_nonneg hA0 hB0)
  have h3 : ∀ j p, ‖∑ q, φ (crd b R (m i j) p) * φ (crd b R (y j) q) *
      φ (algebraMap F R (b.repr (b p * b q) k))‖ ≤ d * (A * B * C) := fun j p =>
    (norm_sum_le_of_le _ fun q _ => hterm j p q).trans (by simp)
  have h2 : ∀ j, ‖∑ p, ∑ q, φ (crd b R (m i j) p) * φ (crd b R (y j) q) *
      φ (algebraMap F R (b.repr (b p * b q) k))‖ ≤ d * (d * (A * B * C)) := fun j =>
    (norm_sum_le_of_le _ fun p _ => h3 j p).trans (by simp)
  exact (norm_sum_le_of_le _ fun j _ => h2 j).trans (by simp)

theorem norm_crd_mulVec_le_one {R K : Type} [CommRing R] [Algebra F R] [NormedField K]
    [IsUltrametricDist K] (φ : R →+* K)
    {M : ℕ} (m : Matrix (Fin M) (Fin M) (R ⊗[F] E)) (y : Fin M → R ⊗[F] E)
    (hA : ∀ i j p, ‖φ (crd b R (m i j) p)‖ ≤ 1) (hB : ∀ j q, ‖φ (crd b R (y j) q)‖ ≤ 1)
    (hC : ∀ p q k, ‖φ (algebraMap F R (b.repr (b p * b q) k))‖ ≤ 1) (i : Fin M) (k : Fin d) :
    ‖φ (crd b R ((m.mulVec y) i) k)‖ ≤ 1 := by
  rw [crd_mulVec]
  simp only [map_sum, map_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun j _ => ?_
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun p _ => ?_
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun q _ => ?_
  rw [norm_mul, norm_mul]
  exact mul_le_one₀ (mul_le_one₀ (hA i j p) (norm_nonneg _) (hB j q)) (norm_nonneg _) (hC p q k)

theorem exists_bound_crd {R K : Type} [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] [NormedField K] (φ : R →+* K) (hφ : Continuous φ) {a M : ℕ}
    {S : Set (Fin a → Fin M → R ⊗[F] E)} (hS : IsCompact S) :
    ∃ B, 0 ≤ B ∧ ∀ Y ∈ S, ∀ i j k, ‖φ (crd b R (Y i j) k)‖ ≤ B := by
  have : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  have hc : ∀ i j k, Continuous fun Y : (Fin a → Fin M → R ⊗[F] E) => ‖φ (crd b R (Y i j) k)‖ := by
    intro i j k
    have hl : Continuous fun y : R ⊗[F] E => crd b R y k :=
      IsModuleTopology.continuous_of_linearMap
        ((Finsupp.lapply k).comp (Algebra.TensorProduct.basis R b).repr.toLinearMap)
    exact continuous_norm.comp (hφ.comp (hl.comp ((continuous_apply j).comp (continuous_apply i))))
  have hf : Continuous fun Y : (Fin a → Fin M → R ⊗[F] E) =>
      ∑ i, ∑ j, ∑ k, ‖φ (crd b R (Y i j) k)‖ :=
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      continuous_finsetSum _ fun k _ => hc i j k
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun Y hY i j k => ?_⟩
  have h1 : ‖φ (crd b R (Y i j) k)‖ ≤ ∑ i, ∑ j, ∑ k, ‖φ (crd b R (Y i j) k)‖ := by
    calc ‖φ (crd b R (Y i j) k)‖ ≤ ∑ k, ‖φ (crd b R (Y i j) k)‖ :=
          Finset.single_le_sum (f := fun k => ‖φ (crd b R (Y i j) k)‖)
            (fun _ _ => norm_nonneg _) (Finset.mem_univ k)
      _ ≤ ∑ j, ∑ k, ‖φ (crd b R (Y i j) k)‖ :=
          Finset.single_le_sum (f := fun j => ∑ k, ‖φ (crd b R (Y i j) k)‖)
            (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ j)
      _ ≤ _ :=
          Finset.single_le_sum (f := fun i => ∑ j, ∑ k, ‖φ (crd b R (Y i j) k)‖)
            (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
            (Finset.mem_univ i)
  have h2 := hC Y hY
  rw [Real.norm_eq_abs] at h2
  exact h1.trans ((le_abs_self _).trans (h2.trans (le_max_left _ _)))

end Bounds

section Places

variable (F : Type) [Field F] [NumberField F]

def piV (v : HeightOneSpectrum (𝓞 F)) : AF F →ₐ[F] Fv F v := (evalV F v).comp (sndA F)

def piW (w : InfinitePlace F) : AF F →ₐ[F] w.Completion :=
  (Pi.evalAlgHom F (fun w : InfinitePlace F => w.Completion) w).comp (fstA F)

theorem norm_le_one_iff_mem (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v) :
    ‖x‖ ≤ 1 ↔ x ∈ HeightOneSpectrum.adicCompletionIntegers F v := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  exact Valued.toNormedField.norm_le_one_iff

theorem eventually_piV_le_one (α : AF F) : ∀ᶠ v in Filter.cofinite, ‖piV F v α‖ ≤ 1 := by
  filter_upwards [α.2.2] with v hv
  exact (norm_le_one_iff_mem F v _).2 hv

theorem continuous_piW_inf (w : InfinitePlace F) :
    Continuous (Pi.evalAlgHom F (fun w : InfinitePlace F => w.Completion) w : Ainf F → w.Completion) :=
  continuous_apply w

theorem norm_piW_algebraMap (w : InfinitePlace F) (x : F) : ‖piW F w (algebraMap F (AF F) x)‖ = w x := by
  rw [AlgHom.commutes]
  exact InfinitePlace.Completion.norm_coe w _

theorem norm_piV_algebraMap (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    ‖piV F v (algebraMap F (AF F) x)‖ = ‖FinitePlace.embedding v x‖ := by
  rw [AlgHom.commutes]
  rfl

end Places

section Finite

variable {F : Type} [Field F] [NumberField F]

theorem norm_emb_le_one_iff (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    ‖FinitePlace.embedding v x‖ ≤ 1 ↔ v.valuation F x ≤ 1 := by
  rw [FinitePlace.embedding_apply, Valued.toNormedField.norm_le_one_iff,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

theorem finite_bdd (S : Finset (HeightOneSpectrum (𝓞 F))) (C : HeightOneSpectrum (𝓞 F) → ℝ)
    (Ci : InfinitePlace F → ℝ) :
    {x : F | (∀ v, ‖FinitePlace.embedding v x‖ ≤ C v) ∧
      (∀ v ∉ S, ‖FinitePlace.embedding v x‖ ≤ 1) ∧ ∀ w : InfinitePlace F, w x ≤ Ci w}.Finite := by
  classical
  set N : ℕ := ∏ v ∈ S, Ideal.absNorm v.asIdeal with hN
  have hNint : ∀ v : HeightOneSpectrum (𝓞 F), ‖FinitePlace.embedding v (N : F)‖ ≤ 1 := by
    intro v
    have := FinitePlace.norm_le_one F v (N : 𝓞 F)
    simpa using this
  have hNlt : ∀ v ∈ S, ‖FinitePlace.embedding v (N : F)‖ < 1 := by
    intro v hv
    have hmem : (N : 𝓞 F) ∈ v.asIdeal := by
      rw [hN, ← Finset.mul_prod_erase S (fun v => Ideal.absNorm v.asIdeal) hv, Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem v.asIdeal)
    have := (FinitePlace.norm_lt_one_iff_mem F v (N : 𝓞 F)).2 hmem
    simpa using this
  have hN0 : (N : F) ≠ 0 := by
    rw [Nat.cast_ne_zero, hN, Finset.prod_ne_zero_iff]
    intro v _
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have hk : ∀ v ∈ S, ∃ k : ℕ, ‖FinitePlace.embedding v (N : F)‖ ^ k * max (C v) 1 ≤ 1 := by
    intro v hv
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (one_div_pos.2 (lt_of_lt_of_le zero_lt_one
      (le_max_right (C v) 1))) (hNlt v hv)
    exact ⟨k, ((lt_div_iff₀ (lt_of_lt_of_le zero_lt_one (le_max_right (C v) 1))).1 hk).le⟩
  choose! kv hkv using hk
  set K := S.sup kv
  set D : F := (N : F) ^ K
  have hD0 : D ≠ 0 := pow_ne_zero _ hN0
  set Bi : ℝ := ∑ w : InfinitePlace F, w D * max (Ci w) 0
  refine ((Embeddings.finite_of_norm_le F ℂ Bi).preimage
    (mul_right_injective₀ hD0).injOn).subset ?_
  rintro x ⟨hC, hS, hI⟩
  refine ⟨?_, fun φ => ?_⟩
  · have hle : ∀ v : HeightOneSpectrum (𝓞 F), ‖FinitePlace.embedding v (D * x)‖ ≤ 1 := by
      intro v
      rw [map_mul, map_pow, norm_mul, norm_pow]
      by_cases hv : v ∈ S
      · calc ‖FinitePlace.embedding v (N : F)‖ ^ K * ‖FinitePlace.embedding v x‖
            ≤ ‖FinitePlace.embedding v (N : F)‖ ^ kv v * max (C v) 1 :=
              mul_le_mul (pow_le_pow_of_le_one (norm_nonneg _) (hNint v) (Finset.le_sup hv))
                ((hC v).trans (le_max_left _ _)) (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
          _ ≤ 1 := hkv v hv
      · exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) (hNint v)) (norm_nonneg _) (hS v hv)
    obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F (D * x)
      (fun v => (norm_emb_le_one_iff v _).1 (hle v))
    show IsIntegral ℤ (D * x)
    rw [← hy]
    exact RingOfIntegers.isIntegral_coe y
  · rw [map_mul, norm_mul, ← InfinitePlace.apply, ← InfinitePlace.apply]
    calc InfinitePlace.mk φ D * InfinitePlace.mk φ x
        ≤ InfinitePlace.mk φ D * max (Ci (InfinitePlace.mk φ)) 0 :=
          mul_le_mul_of_nonneg_left ((hI _).trans (le_max_left _ _)) (apply_nonneg _ _)
      _ ≤ Bi := Finset.single_le_sum (f := fun w : InfinitePlace F => w D * max (Ci w) 0)
          (fun w _ => mul_nonneg (apply_nonneg _ _) (le_max_right _ _)) (Finset.mem_univ _)

end Finite

section Main

theorem le_triple_sum_of_nonneg {ι κ ν : Type} [Fintype ι] [Fintype κ] [Fintype ν] (f : ι → κ → ν → ℝ)
    (hf : ∀ i j k, 0 ≤ f i j k) (i : ι) (j : κ) (k : ν) : f i j k ≤ ∑ i, ∑ j, ∑ k, f i j k := by
  calc f i j k ≤ ∑ k, f i j k :=
        Finset.single_le_sum (f := fun k => f i j k) (fun _ _ => hf _ _ _) (Finset.mem_univ k)
    _ ≤ ∑ j, ∑ k, f i j k :=
        Finset.single_le_sum (f := fun j => ∑ k, f i j k)
          (fun _ _ => Finset.sum_nonneg fun _ _ => hf _ _ _) (Finset.mem_univ j)
    _ ≤ _ :=
        Finset.single_le_sum (f := fun i => ∑ j, ∑ k, f i j k)
          (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hf _ _ _)
          (Finset.mem_univ i)

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem finite_of_adm {M a : ℕ} (Φ : (Fin a → Fin M → AF F ⊗[F] E) → ℂ) (hΦ : IsAdm F E Φ)
    (g : GL (Fin M) (AF F ⊗[F] E)) :
    {X : Fin a → Fin M → E | Φ (actTup (AF F) g (ratTup (AF F) X)) ≠ 0}.Finite := by
  classical
  obtain ⟨d, b, Φinf, Φf, Φv, _hcont, hcs, ⟨hSB, hae, hprod⟩, hIF⟩ := hΦ
  set m : Matrix (Fin M) (Fin M) (AF F ⊗[F] E) := ((g⁻¹ : GL (Fin M) (AF F ⊗[F] E)) :
    Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) with hm
  set gm : Matrix (Fin M) (Fin M) (AF F ⊗[F] E) := ((g : GL (Fin M) (AF F ⊗[F] E)) :
    Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) with hgm
  set Y : (Fin a → Fin M → E) → Fin a → Fin M → AF F ⊗[F] E :=
    fun X => actTup (AF F) g (ratTup (AF F) X) with hY
  set cst : Fin d → Fin d → Fin d → AF F := fun p q k => algebraMap F (AF F) (b.repr (b p * b q) k)
  have hback : ∀ X i, ratTup (AF F) X i = m.mulVec (Y X i) := by
    intro X i
    simp only [hY, actTup, Matrix.mulVec_mulVec, hm]
    rw [Units.inv_mul, Matrix.one_mulVec]
  have hx : ∀ X i j k, algebraMap F (AF F) (b.repr (X i j) k) = crd b (AF F) ((m.mulVec (Y X i)) j) k := by
    intro X i j k
    rw [← hback]
    exact (crd_incl b (AF F) (X i j) k).symm

  have hinfB : ∀ w : InfinitePlace F, ∃ B, 0 ≤ B ∧ ∀ Z ∈ tsupport Φinf, ∀ i j k,
      ‖(Pi.evalAlgHom F (fun w : InfinitePlace F => w.Completion) w).toRingHom (crd b (Ainf F) (Z i j) k)‖ ≤ B :=
    fun w => exists_bound_crd b _ (continuous_piW_inf F w) hcs
  choose Bw hBw0 hBw using hinfB

  have hfinB : ∀ v : HeightOneSpectrum (𝓞 F), ∃ B, 0 ≤ B ∧ ∀ Z ∈ tsupport (Φv v), ∀ i j k,
      ‖(RingHom.id (Fv F v)) (crd b (Fv F v) (Z i j) k)‖ ≤ B :=
    fun v => exists_bound_crd b _ continuous_id (hSB v).2
  choose Bv hBv0 hBv using hfinB

  have hgood : ∀ᶠ v in Filter.cofinite, Φv v = (latV b v).indicator 1 ∧
      (∀ i j p, ‖piV F v (crd b (AF F) (m i j) p)‖ ≤ 1) ∧ (∀ p q k, ‖piV F v (cst p q k)‖ ≤ 1) := by
    refine hae.and (Filter.Eventually.and ?_ ?_)
    · exact Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
        Filter.eventually_all.2 fun p => eventually_piV_le_one F _
    · exact Filter.eventually_all.2 fun p => Filter.eventually_all.2 fun q =>
        Filter.eventually_all.2 fun k => eventually_piV_le_one F _
  set S : Finset (HeightOneSpectrum (𝓞 F)) := (Filter.eventually_cofinite.1 hgood).toFinset

  have hcV : ∀ (Z : Fin a → Fin M → AF F ⊗[F] E) (v : HeightOneSpectrum (𝓞 F)) i j k,
      crd b (Fv F v) (projV v (projFin Z) i j) k = piV F v (crd b (AF F) (Z i j) k) := by
    intro Z v i j k
    show crd b (Fv F v) (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (Z i j))) k = _
    rw [crd_map, crd_map]
    rfl
  have hcI : ∀ (Z : Fin a → Fin M → AF F ⊗[F] E) (w : InfinitePlace F) i j k,
      (Pi.evalAlgHom F (fun w : InfinitePlace F => w.Completion) w).toRingHom
        (crd b (Ainf F) (projInf Z i j) k) = piW F w (crd b (AF F) (Z i j) k) := by
    intro Z w i j k
    show (Pi.evalAlgHom F (fun w : InfinitePlace F => w.Completion) w)
        (crd b (Ainf F) (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (Z i j)) k) = _
    rw [crd_map]
    rfl

  set Ci : InfinitePlace F → ℝ := fun w => M * (d * (d * (
    (∑ i, ∑ j, ∑ p, ‖piW F w (crd b (AF F) (m i j) p)‖) * Bw w *
    (∑ p, ∑ q, ∑ k, ‖piW F w (cst p q k)‖))))
  set Cv : HeightOneSpectrum (𝓞 F) → ℝ := fun v => M * (d * (d * (
    (∑ i, ∑ j, ∑ p, ‖piV F v (crd b (AF F) (m i j) p)‖) * Bv v *
    (∑ p, ∑ q, ∑ k, ‖piV F v (cst p q k)‖))))
  have hT := finite_bdd S Cv Ci
  set T := {x : F | (∀ v, ‖FinitePlace.embedding v x‖ ≤ Cv v) ∧
      (∀ v ∉ S, ‖FinitePlace.embedding v x‖ ≤ 1) ∧ ∀ w : InfinitePlace F, w x ≤ Ci w}
  have hT3 : (Set.pi Set.univ fun _ : Fin a => Set.pi Set.univ fun _ : Fin M =>
      Set.pi Set.univ fun _ : Fin d => T).Finite :=
    Set.Finite.pi fun _ => Set.Finite.pi fun _ => Set.Finite.pi fun _ => hT
  have hinj : Function.Injective fun (X : Fin a → Fin M → E) (i : Fin a) (j : Fin M) (k : Fin d) =>
      b.repr (X i j) k := by
    intro X X' h
    funext i j
    exact b.repr.injective (Finsupp.ext fun k => congrFun (congrFun (congrFun h i) j) k)
  refine (hT3.preimage hinj.injOn).subset ?_
  intro X hX
  simp only [Set.mem_ofPred_eq] at hX
  have hne : Φ (Y X) ≠ 0 := hX
  rw [hIF] at hne
  have hne_inf := left_ne_zero_of_mul hne
  have hne_fin := right_ne_zero_of_mul hne

  have hYint : ∀ᶠ v in Filter.cofinite, ∀ i j k, ‖piV F v (crd b (AF F) (Y X i j) k)‖ ≤ 1 := by
    have h1 : ∀ᶠ v in Filter.cofinite, (∀ i j p, ‖piV F v (crd b (AF F) (gm i j) p)‖ ≤ 1) ∧
        (∀ i j q, ‖piV F v (crd b (AF F) (ratTup (AF F) X i j) q)‖ ≤ 1) ∧
        (∀ p q k, ‖piV F v (cst p q k)‖ ≤ 1) := by
      refine Filter.Eventually.and ?_ (Filter.Eventually.and ?_ ?_)
      · exact Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
          Filter.eventually_all.2 fun p => eventually_piV_le_one F _
      · exact Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
          Filter.eventually_all.2 fun p => eventually_piV_le_one F _
      · exact Filter.eventually_all.2 fun p => Filter.eventually_all.2 fun q =>
          Filter.eventually_all.2 fun k => eventually_piV_le_one F _
    filter_upwards [h1] with v hv i j k
    exact norm_crd_mulVec_le_one b (piV F v).toRingHom gm (ratTup (AF F) X i) hv.1 (hv.2.1 i) hv.2.2 j k
  have hone : ∀ᶠ v in Filter.cofinite, Φv v (projV v (projFin (Y X))) = 1 := by
    filter_upwards [hYint, hae] with v hv hv'
    rw [hv']
    refine Set.indicator_of_mem ?_ _
    intro i j k
    rw [← norm_le_one_iff_mem]
    have := hv i j k
    rw [← hcV] at this
    exact this
  have hfin : (Function.mulSupport fun v => Φv v (projV v (projFin (Y X)))).Finite :=
    (Filter.eventually_cofinite.1 hone).subset fun v hv => hv
  have hall : ∀ v, Φv v (projV v (projFin (Y X))) ≠ 0 := by
    intro v
    rw [hprod, finprod_eq_prod _ hfin] at hne_fin
    by_cases hv : v ∈ hfin.toFinset
    · exact Finset.prod_ne_zero_iff.1 hne_fin v hv
    · rw [Set.Finite.mem_toFinset, Function.mem_mulSupport, not_not] at hv
      rw [hv]
      exact one_ne_zero
  intro i _ j _ k _
  refine ⟨?_, ?_, ?_⟩
  ·
    intro v
    rw [← norm_piV_algebraMap, hx]
    refine norm_crd_mulVec_le b (piV F v).toRingHom m (Y X i) (Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (hBv0 v)
      (fun i' j' p => le_triple_sum_of_nonneg (fun i' j' p => ‖piV F v (crd b (AF F) (m i' j') p)‖)
        (fun _ _ _ => norm_nonneg _) i' j' p)
      (fun j' q => ?_)
      (fun p q k' => le_triple_sum_of_nonneg (fun p q k' => ‖piV F v (cst p q k')‖) (fun _ _ _ => norm_nonneg _) p q k')
      j k
    have hmem := subset_tsupport _ (hall v)
    have := hBv v (projV v (projFin (Y X))) hmem i j' q
    rw [RingHom.id_apply, hcV] at this
    exact this
  ·
    intro v hv
    have hvS : v ∉ {v | ¬ (Φv v = (latV b v).indicator 1 ∧
        (∀ i j p, ‖piV F v (crd b (AF F) (m i j) p)‖ ≤ 1) ∧ (∀ p q k, ‖piV F v (cst p q k)‖ ≤ 1))} := by
      intro h
      exact hv ((Set.Finite.mem_toFinset _).2 h)
    simp only [Set.mem_ofPred_eq, not_not] at hvS
    obtain ⟨hΦv, hm1, hc1⟩ := hvS
    have hL : projV v (projFin (Y X)) ∈ latV b v := by
      by_contra hnot
      apply hall v
      rw [hΦv]
      exact Set.indicator_of_notMem hnot _
    rw [← norm_piV_algebraMap, hx]
    refine norm_crd_mulVec_le_one b (piV F v).toRingHom m (Y X i) hm1 (fun j' q => ?_) hc1 j k
    have := hL i j' q
    rw [← norm_le_one_iff_mem] at this
    show ‖piV F v (crd b (AF F) (Y X i j') q)‖ ≤ 1
    rw [← hcV]
    exact this
  ·
    intro w
    rw [← norm_piW_algebraMap, hx]
    refine norm_crd_mulVec_le b (piW F w).toRingHom m (Y X i) (Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (hBw0 w)
      (fun i' j' p => le_triple_sum_of_nonneg (fun i' j' p => ‖piW F w (crd b (AF F) (m i' j') p)‖)
        (fun _ _ _ => norm_nonneg _) i' j' p)
      (fun j' q => ?_)
      (fun p q k' => le_triple_sum_of_nonneg (fun p q k' => ‖piW F w (cst p q k')‖) (fun _ _ _ => norm_nonneg _) p q k')
      j k
    have hmem := subset_tsupport _ hne_inf
    have := hBw w (projInf (Y X)) hmem i j' q
    rw [hcI] at this
    exact this

end Main

end PI.VolStabSW.FiniteThetaCoordinates

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem finTheta_holds : FinTheta := by
  intro F E _ _ _ _ _ σ _ M J _ _ _ a _ _ X0 hT _ Φ hΦ h
  exact FiniteThetaCoordinates.finite_of_adm Φ hΦ _

end PI.VolStabSW
