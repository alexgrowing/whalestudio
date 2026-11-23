import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.FinAm

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem padic_hom_zero {l : ℕ} [Fact l.Prime] {M : Type} [AddCommGroup M] (hM : ∀ y : M, l • y = 0)
    (φ : ℤ_[l] →+ M) (h1 : φ 1 = 0) (c : ℤ_[l]) : φ c = 0 := by
  have hn : ∀ n : ℕ, φ (n : ℤ_[l]) = 0 := fun n => by
    rw [← nsmul_one, map_nsmul, h1, smul_zero]
  have hmem := PadicInt.sub_zmodRepr_mem c
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hmem
  obtain ⟨a, ha⟩ := hmem
  have hc : c = (c.zmodRepr : ℤ_[l]) + l • a := by
    rw [nsmul_eq_mul, mul_comm, ha]
    ring
  rw [hc, map_add, hn, map_nsmul, hM, add_zero]

private theorem free_hom_zero {l : ℕ} [Fact l.Prime] {M : Type} [AddCommGroup M] (hM : ∀ y : M, l • y = 0)
    {d : ℕ} (f : ((Fin d → ℤ_[l]) × ℤ_[l]) →+ M) (h1 : ∀ i, f (Pi.single i 1, 0) = 0) (h2 : f (0, 1) = 0)
    (v : (Fin d → ℤ_[l]) × ℤ_[l]) : f v = 0 := by
  have e1 : ∀ i c, f (Pi.single i c, 0) = 0 := fun i c =>
    padic_hom_zero hM (f.comp ((AddMonoidHom.inl _ _).comp (AddMonoidHom.single (fun _ : Fin d => ℤ_[l]) i)))
      (h1 i) c
  have e2 : ∀ c, f (0, c) = 0 := fun c =>
    padic_hom_zero hM (f.comp (AddMonoidHom.inr _ _)) h2 c
  obtain ⟨u, w⟩ := v
  have hs : ((u, w) : (Fin d → ℤ_[l]) × ℤ_[l]) = (∑ i, ((Pi.single i (u i), 0) : (Fin d → ℤ_[l]) × ℤ_[l])) + (0, w) := by
    ext j
    · simp [Prod.fst_sum, Finset.univ_sum_single]
    · simp [Prod.snd_sum]
  rw [hs, map_add, map_sum, e2, add_zero]
  exact Finset.sum_eq_zero fun i _ => e1 i (u i)

private theorem eq_zero_of_eq_self_add_self {M : Type} [AddCommGroup M] (a : M) (h : a = a + a) : a = 0 := by
  have := congrArg (fun x => x - a) h
  simpa using this.symm

private theorem char_zero {l : ℕ} [Fact l.Prime] {M : Type} [AddCommGroup M] [Finite M] (hM : ∀ y : M, l • y = 0)
    {D : Type} [Group D] [TopologicalSpace D] [IsTopologicalGroup D] {I : Subgroup D} {d : ℕ} (A : LocAb l D I d)
    (s : Fin d → D) (t : D) (hs : ∀ i, A.a (s i) = Multiplicative.ofAdd (Pi.single i 1, 0))
    (ht : A.a t = Multiplicative.ofAdd (0, 1))
    (z : D → M) (hz : IsLocallyConstant z) (hm : ∀ g h, z (g * h) = z g + z h) (hμ : ∀ g ∈ muG l D, z g = 0)
    (h1 : ∀ i, z (s i) = 0) (h2 : z t = 0) (g : D) : z g = 0 := by
  have hz1 : z 1 = 0 := by
    have := hm 1 1
    rw [one_mul] at this
    exact eq_zero_of_eq_self_add_self _ this
  let χ : D →* Multiplicative M :=
    { toFun := fun g => Multiplicative.ofAdd (z g)
      map_one' := by simp [hz1]
      map_mul' := fun g h => by simp [hm] }
  have hP : IsPGroup l (Multiplicative M) := fun g => ⟨1, by
    rw [pow_one]
    apply Multiplicative.toAdd.injective
    simp [toAdd_pow, hM]⟩
  have hχ : ∀ g, g ∈ χ.ker ↔ z g = 0 := fun g => by
    rw [MonoidHom.mem_ker]
    show Multiplicative.ofAdd (z g) = 1 ↔ _
    exact ofAdd_eq_one
  have hopen : IsOpen (χ.ker : Set D) := by
    have : (χ.ker : Set D) = z ⁻¹' {0} := by
      ext g
      exact hχ g
    rw [this]
    exact hz.isOpen_fiber 0
  have hmu : muG l D ≤ χ.ker := fun g hg => (hχ g).mpr (hμ g hg)
  have hker := A.univ (Multiplicative M) hP χ hopen hmu
  have dep : ∀ g g', A.a g = A.a g' → z g = z g' := by
    intro g g' h
    have hk : g⁻¹ * g' ∈ A.a.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
    have h0 := (hχ _).mp (hker hk)
    have := hm g (g⁻¹ * g')
    rw [mul_inv_cancel_left, h0, add_zero] at this
    exact this.symm
  let pre : (Fin d → ℤ_[l]) × ℤ_[l] → D := fun v => Classical.choose (A.surj (Multiplicative.ofAdd v))
  have hpre : ∀ v, A.a (pre v) = Multiplicative.ofAdd v := fun v => Classical.choose_spec (A.surj _)
  let φ : ((Fin d → ℤ_[l]) × ℤ_[l]) →+ M := AddMonoidHom.mk' (fun v => z (pre v)) (by
    intro v w
    rw [← hm]
    apply dep
    rw [map_mul, hpre, hpre, hpre]
    rfl)
  have hφ := free_hom_zero hM φ (fun i => by
      show z (pre _) = 0
      rw [dep _ (s i) (by rw [hpre, hs])]
      exact h1 i)
    (by
      show z (pre _) = 0
      rw [dep _ t (by rw [hpre, ht])]
      exact h2)
    (Multiplicative.toAdd (A.a g))
  have : φ (Multiplicative.toAdd (A.a g)) = z g := by
    show z (pre _) = z g
    apply dep
    rw [hpre]
    rfl
  rw [← this, hφ]

theorem UpperTheory.V.Pa.homCount :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (D : Type) [Group D] [TopologicalSpace D] [IsTopologicalGroup D] (I : Subgroup D) (d m : ℕ), LocAb l D I d → {z : D → x.Am m | IsLocallyConstant z ∧ (∀ g h, z (g * h) = z g + z h) ∧ ∀ g ∈ muG l D, z g = 0}.Finite ∧ {z : D → x.Am m | IsLocallyConstant z ∧ (∀ g h, z (g * h) = z g + z h) ∧ ∀ g ∈ muG l D, z g = 0}.ncard ≤ Nat.card x.K ^ (m * (d + 1)) := by
  intro l _ F n x D _ _ _ I d m A
  obtain ⟨hfin, hcard, -, hl, -⟩ := finAm l F n x m 0
  haveI := hfin
  have hs : ∀ i, A.a (Classical.choose (A.surj (Multiplicative.ofAdd ((Pi.single i 1, 0) : (Fin d → ℤ_[l]) × ℤ_[l])))) =
      Multiplicative.ofAdd ((Pi.single i 1, 0) : (Fin d → ℤ_[l]) × ℤ_[l]) :=
    fun i => Classical.choose_spec (A.surj _)
  have ht : A.a (Classical.choose (A.surj (Multiplicative.ofAdd ((0, 1) : (Fin d → ℤ_[l]) × ℤ_[l])))) =
      Multiplicative.ofAdd ((0, 1) : (Fin d → ℤ_[l]) × ℤ_[l]) :=
    Classical.choose_spec (A.surj _)
  set s : Fin d → D := fun i => Classical.choose (A.surj (Multiplicative.ofAdd ((Pi.single i 1, 0) : (Fin d → ℤ_[l]) × ℤ_[l]))) with hs_def
  set t : D := Classical.choose (A.surj (Multiplicative.ofAdd ((0, 1) : (Fin d → ℤ_[l]) × ℤ_[l]))) with ht_def
  set S := {z : D → x.Am m | IsLocallyConstant z ∧ (∀ g h, z (g * h) = z g + z h) ∧ ∀ g ∈ muG l D, z g = 0} with hS
  let ev : (D → x.Am m) → (Fin d → x.Am m) × x.Am m := fun z => (fun i => z (s i), z t)
  have hinj : Set.InjOn ev S := by
    intro z hz z' hz' he
    funext g
    have key := char_zero hl A s t hs ht (z - z') (hz.1.sub hz'.1)
      (fun g h => by
        simp only [Pi.sub_apply, hz.2.1, hz'.2.1]
        abel)
      (fun g hg => by simp [hz.2.2 g hg, hz'.2.2 g hg])
      (fun i => by
        simp only [Pi.sub_apply, sub_eq_zero]
        exact congrFun (congrArg Prod.fst he) i)
      (by
        simp only [Pi.sub_apply, sub_eq_zero]
        exact congrArg Prod.snd he) g
    exact sub_eq_zero.mp key
  refine ⟨Set.Finite.of_finite_image (Set.toFinite _) hinj, ?_⟩
  rw [← hinj.ncard_image]
  refine (Set.ncard_le_card _).trans (le_of_eq ?_)
  rw [Nat.card_prod, Nat.card_fun, Nat.card_fin, hcard, ← pow_succ, ← pow_mul]
