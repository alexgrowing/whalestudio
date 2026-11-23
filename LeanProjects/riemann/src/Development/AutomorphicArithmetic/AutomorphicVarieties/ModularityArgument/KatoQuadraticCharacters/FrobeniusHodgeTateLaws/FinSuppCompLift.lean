import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.ChiQuadAlt

open UpperTheory.V.Z.Kato.Joint

section

open Formalism.ConjugateSelfDual GlobalTheory.KZ GlobalTheory.KummerEisensteinGalois GlobalTheory.LambdaValuationPowers UpperTheory.V.HV

variable {l : ℕ} [Fact l.Prime]

private theorem finSupp_comp_fop (k : ℕ) (χ : ℕ → Qbar l) (T : Letter)
    (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l) (h : FinSupp lam) : FinSupp (lam ∘ₗ fop k l χ T) := by
  obtain ⟨S, hS⟩ := h
  cases T with
  | T q =>
    refine ⟨S.image (q * ·) ∪ S.image (· / q), fun f hf => ?_⟩
    rw [LinearMap.comp_apply]
    apply hS
    intro n hn
    show GlobalTheory.EisM.To k (χ q) q f n = 0
    have h1 : f (q * n) = 0 := hf _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨n, hn, rfl⟩))
    have h2 : f (n / q) = 0 := hf _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨n, hn, rfl⟩))
    simp [GlobalTheory.EisM.To, GlobalTheory.EisM.Vo, h1, h2]
  | U =>
    refine ⟨S.image (l * ·), fun f hf => ?_⟩
    rw [LinearMap.comp_apply]
    apply hS
    intro n hn
    show GlobalTheory.EisM.Uo l f n = 0
    exact hf _ (Finset.mem_image.mpr ⟨n, hn, rfl⟩)
  | D d =>
    refine ⟨S, fun f hf => ?_⟩
    rw [LinearMap.comp_apply]
    apply hS
    intro n hn
    show (χ d • f) n = 0
    simp [hf n hn]

private theorem finSupp_comp_lift (k : ℕ) (χ : ℕ → Qbar l) (P : FreeAlgebra (Qbar l) Letter) :
    ∀ lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l, FinSupp lam →
      FinSupp (lam ∘ₗ FreeAlgebra.lift (Qbar l) (fop k l χ) P) := by
  induction P using FreeAlgebra.induction with
  | grade0 r =>
    intro lam h
    rw [AlgHom.commutes]
    have hr : lam ∘ₗ algebraMap (Qbar l) (Module.End (Qbar l) (ℕ → Qbar l)) r = r • lam := by
      ext f
      simp [Module.algebraMap_end_apply]
    rw [hr]
    exact FinSupp.smul h r
  | grade1 x =>
    intro lam h
    rw [FreeAlgebra.lift_ι_apply]
    exact finSupp_comp_fop k χ x lam h
  | mul a b ha hb =>
    intro lam h
    rw [map_mul, Module.End.mul_eq_comp, ← LinearMap.comp_assoc]
    exact hb _ (ha lam h)
  | add a b ha hb =>
    intro lam h
    rw [map_add, LinearMap.comp_add]
    exact FinSupp.add (ha lam h) (hb lam h)

private theorem exists_pow_mul_le (x : Qbar l) : ∃ k : ℕ, ‖((l : ℕ) : Qbar l) ^ k * x‖ ≤ 1 := by
  obtain ⟨k, hk⟩ := exists_le_l_pow l ‖x‖
  refine ⟨k, ?_⟩
  rw [norm_mul, norm_l_pow]
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  calc ((l : ℝ))⁻¹ ^ k * ‖x‖ ≤ ((l : ℝ))⁻¹ ^ k * (l : ℝ) ^ k := by gcongr
    _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ hl.ne', one_pow]

end

open Formalism.ConjugateSelfDual GlobalTheory.KZ GlobalTheory.KummerEisensteinGalois GlobalTheory.LambdaValuationPowers UpperTheory.V.HV in
theorem UpperTheory.V.Z.Kato.Joint.finP :
    UpperTheory.V.Z.Kato.Joint.FinP := by
  classical
  intro hub l _ ι k N B cc χE c₀ P _
  let lam₀ : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l :=
    ∑ n ∈ Finset.range B, ι.symm (cc n) • LinearMap.proj n
  have hlam₀ : ∀ a : ℕ → Qbar l, lam₀ a = ι.symm (GlobalTheory.EisM.lam B cc fun i => ι (a i)) := by
    intro a
    simp [lam₀, GlobalTheory.EisM.lam, map_sum, map_mul, LinearMap.sum_apply]
  have hfs₀ : FinSupp lam₀ := by
    refine ⟨Finset.range B, fun f hf => ?_⟩
    rw [hlam₀, GlobalTheory.EisM.lam, Finset.sum_eq_zero, map_zero]
    intro n hn
    simp [hf n hn]
  let lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l := lam₀ ∘ₗ FreeAlgebra.lift (Qbar l) (fop k l χE) P
  have hfs : FinSupp lam := finSupp_comp_lift k χE P lam₀ hfs₀
  obtain ⟨S, hS⟩ := hfs
  choose e he using exists_pow_mul_le (l := l)
  let g : ℕ → Qbar l := fun i => ((l : ℕ) : Qbar l) ^ e (lam (Pi.single i 1)) * lam (Pi.single i 1)
  obtain ⟨c, hc₀, -, hcF⟩ := hub l c₀ c₀ (S.image g) (by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact he _)
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  refine ⟨lam₀, lam, c, hc₀, hfs₀, ⟨S, hS⟩, ?_, hlam₀, fun a => rfl⟩
  intro i σ hσ _
  by_cases hi : i ∈ S
  · have hy := hσ _ (hcF _ (Finset.mem_image_of_mem g hi))
    have hne : ((l : ℕ) : Qbar l) ^ e (lam (Pi.single i 1)) ≠ 0 := by
      intro h0
      have h1 := congrArg norm h0
      rw [norm_l_pow, norm_zero] at h1
      exact pow_ne_zero _ (inv_ne_zero hl.ne') h1
    simp only [g, map_mul, map_pow, map_natCast] at hy
    exact mul_left_cancel₀ hne hy
  · have h0 : lam (Pi.single i 1) = 0 :=
      hS _ (fun s hs => Pi.single_eq_of_ne (by rintro rfl; exact hi hs) 1)
    rw [h0, map_zero]
