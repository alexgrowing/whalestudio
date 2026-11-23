import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.MemPowSmul

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem ac_mul {G R : Type} [TopologicalSpace G] [CommRing R] {I : Ideal R} {f h : G → R}
    (hf : AdicCont I f) (hh : AdicCont I h) : AdicCont I fun g => f g * h g := fun N => by
  simp only [map_mul]; exact (hf N).mul (hh N)

private theorem ac_const {G R : Type} [TopologicalSpace G] [CommRing R] {I : Ideal R} (c : R) :
    AdicCont I fun _ : G => c := fun _ => IsLocallyConstant.const _

private theorem ac_sum {G R ι : Type} [TopologicalSpace G] [CommRing R] {I : Ideal R} (s : Finset ι)
    {f : ι → G → R} (hf : ∀ i, AdicCont I (f i)) : AdicCont I fun g => ∑ i ∈ s, f i g := by
  classical
  intro N
  simp only [map_sum]
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact IsLocallyConstant.const 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a N).add ih

private theorem mat_lc {G A R : Type} [TopologicalSpace G] [CommRing A] [CommRing R] [Algebra A R]
    {n : ℕ} (t : A) (f : G → Matrix (Fin n) (Fin n) R)
    (hf : ∀ i j, AdicCont (Ideal.span {algebraMap A R t}) fun g => f g i j) (N : ℕ) :
    IsLocallyConstant fun g =>
      (Ideal.span {t} ^ N • (⊤ : Submodule A (Matrix (Fin n) (Fin n) R))).mkQ (f g) := by
  classical
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hx : ∀ᶠ y in nhds x, ∀ i j, Ideal.Quotient.mk (Ideal.span {algebraMap A R t} ^ N) (f y i j)
      = Ideal.Quotient.mk (Ideal.span {algebraMap A R t} ^ N) (f x i j) :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => (hf i j N).eventually_eq x
  filter_upwards [hx] with y hy
  have hc : ∀ i j, ∃ c : R, c * algebraMap A R t ^ N = f y i j - f x i j := by
    intro i j
    have h := Ideal.Quotient.eq.1 (hy i j)
    rwa [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h
  choose c hc using hc
  simp only [Submodule.mkQ_apply]
  rw [Submodule.Quotient.eq]
  have hm : f y - f x = t ^ N • Matrix.of c := by
    ext i j
    simp [Algebra.smul_def, ← hc i j, mul_comm]
  rw [hm, Ideal.span_singleton_pow]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top

theorem UpperTheory.V.Pa.Det.matFg :
    ∀ (l : ℕ) [Fact l.Prime] {K G R : Type} [Field K] [Finite K] [CharP K l] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] [CommRing R] [Algebra (PowerSeries K) R] [Module.Free (PowerSeries K) R] [Module.Finite (PowerSeries K) R] {n : ℕ} (χ : G →* R) (r : G →* Matrix (Fin n) (Fin n) R) (Z : Submodule (PowerSeries K) (G → Matrix (Fin n) (Fin n) R)), PhiCond G l → AdicCont (Ideal.span {algebraMap (PowerSeries K) R PowerSeries.X}) χ → (∀ i j, AdicCont (Ideal.span {algebraMap (PowerSeries K) R PowerSeries.X}) fun g => r g i j) → (∀ z ∈ Z, (∀ i j, AdicCont (Ideal.span {algebraMap (PowerSeries K) R PowerSeries.X}) fun g => z g i j) ∧ TwCoc χ r Set.univ z) → Z.FG := by
  intro l _ K G R _ _ _ _ _ _ _ _ _ _ _ _ n χ r Z hφ hχ hr hZ
  let ρ : G →* Module.End (PowerSeries K) (Matrix (Fin n) (Fin n) R) :=
    { toFun := fun g =>
        { toFun := fun m => χ g • (r g * m * r g⁻¹)
          map_add' := by intro a b; simp [Matrix.mul_add, Matrix.add_mul]
          map_smul' := by
            intro c m
            simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]
            exact smul_comm _ _ _ }
      map_one' := by ext m : 1; simp
      map_mul' := by
        intro g h
        ext m : 1
        simp [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc, mul_comm] }
  have hinv : ∀ i j, AdicCont (Ideal.span {algebraMap (PowerSeries K) R PowerSeries.X}) fun g => r g⁻¹ i j :=
    fun i j N => (hr i j N).comp_continuous continuous_inv
  refine Det.z1Fg l ρ Z hφ ?_ ?_
  · intro N m
    refine mat_lc PowerSeries.X (fun g => χ g • (r g * m * r g⁻¹)) ?_ N
    intro i j
    have e : (fun g => (χ g • (r g * m * r g⁻¹)) i j)
        = fun g => χ g * ∑ q, (∑ k, r g i k * m k q) * r g⁻¹ q j := by
      funext g
      simp [Matrix.mul_apply]
    rw [e]
    exact ac_mul hχ (ac_sum _ fun q => ac_mul (ac_sum _ fun k => ac_mul (hr i k) (ac_const _)) (hinv q j))
  · intro z hz
    obtain ⟨hzc, hzt⟩ := hZ z hz
    exact ⟨fun N => mat_lc PowerSeries.X z hzc N, fun g h => hzt g trivial h trivial⟩
