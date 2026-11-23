import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.BilinearSmul.BSmulRight

open QuadraticAlgebra Matrix UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.One.fixg :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
        ∀ (c : K) (d m : EL Δ τ) (δ : U3 Δ) (ι : (Etau K τ)ˣ →* U3 Δ) (P : Sp Δ τ ≃ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ)), Models c d m δ ι P →
        ∀ g : U3 Δ, g⁻¹ * δ * theta Δ g ∈ KU O Δ →
        IsFix O c d m {x | ∀ i, IsInt O ((((g⁻¹ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ P x) i)} := by
  intro O K _ _ _ _ _ Δ τ hL c d m δ ι P hM g hg
  classical
  let M : Matrix (Fin 3) (Fin 3) (Lsq K Δ) := ((g⁻¹ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ))
  let G : Matrix (Fin 3) (Fin 3) (Lsq K Δ) := ((g : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ))
  have hMG : M * G = 1 := by
    have h : ((g⁻¹ * g : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) = 1 := by
      rw [inv_mul_cancel]; rfl
    exact h
  have hGM : G * M = 1 := by
    have h : ((g * g⁻¹ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) = 1 := by
      rw [mul_inv_cancel]; rfl
    exact h
  have hIsum : ∀ (f : Fin 3 → Lsq K Δ), (∀ i, IsInt O (f i)) → IsInt O (∑ i, f i) := by
    intro f hf
    exact IsIntegral.sum _ fun i _ => hf i
  have hImul : ∀ a b : Lsq K Δ, IsInt O a → IsInt O b → IsInt O (a * b) := fun a b ha hb => ha.mul hb
  have hIstar : ∀ a : Lsq K Δ, IsInt O a ↔ IsInt O (star a) := by
    intro a
    refine ⟨fun h => OE.int_star hL h, fun h => ?_⟩
    simpa using OE.int_star hL h
  have hU : ∀ (h : U3 Δ) (a b : Fin 3 → Lsq K Δ),
      ((h : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ a) ⬝ᵥ star ((h : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ b)
        = a ⬝ᵥ star b := by
    intro h a b
    have hu : (h : Matrix (Fin 3) (Fin 3) (Lsq K Δ))ᴴ * (h : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) = 1 :=
      Matrix.mem_unitaryGroup_iff'.mp h.2
    rw [Matrix.star_mulVec, dotProduct_comm, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hu,
      Matrix.one_mulVec, dotProduct_comm]
  have hsv : ∀ (N : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) (v : Fin 3 → Lsq K Δ),
      star (N *ᵥ v) = N.map star *ᵥ star v := by
    intro N v
    funext i
    simp [Matrix.mulVec, dotProduct, star_sum, star_mul']
  have hIvec : ∀ (N : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) (v : Fin 3 → Lsq K Δ),
      (∀ i j, IsInt O (N i j)) → (∀ j, IsInt O (v j)) → ∀ i, IsInt O ((N *ᵥ v) i) := by
    intro N v hN hv i
    exact hIsum _ fun j => hImul _ _ (hN i j) (hv j)
  have hsingle : ∀ (j : Fin 3) (u : Lsq K Δ), IsInt O u →
      ∀ i, IsInt O ((Pi.single j u : Fin 3 → Lsq K Δ) i) := by
    intro j u hu i
    by_cases hij : i = j
    · subst hij; simpa using hu
    · simpa [hij] using (isIntegral_zero : IsIntegral O (0 : Lsq K Δ))
  let Q : Sp Δ τ → Fin 3 → Lsq K Δ := fun x => M *ᵥ P x
  have hPQ : ∀ x, G *ᵥ Q x = P x := by
    intro x
    show G *ᵥ (M *ᵥ P x) = P x
    rw [Matrix.mulVec_mulVec, hGM, Matrix.one_mulVec]
  have hQS : ∀ v, Q (P.symm (G *ᵥ v)) = v := by
    intro v
    show M *ᵥ P (P.symm (G *ᵥ v)) = v
    rw [P.apply_symm_apply, Matrix.mulVec_mulVec, hMG, Matrix.one_mulVec]
  have hform : ∀ x y, herm c m x y = Q x ⬝ᵥ star (Q y) := by
    intro x y
    rw [hM.form]
    exact (hU g⁻¹ (P x) (P y)).symm
  let kU : U3 Δ := g⁻¹ * δ * theta Δ g
  let k : Matrix (Fin 3) (Fin 3) (Lsq K Δ) := (kU : Matrix (Fin 3) (Fin 3) (Lsq K Δ))
  let ki : Matrix (Fin 3) (Fin 3) (Lsq K Δ) := ((kU⁻¹ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ))
  have hkki : k * ki = 1 := by
    have h : ((kU * kU⁻¹ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) = 1 := by
      rw [mul_inv_cancel]; rfl
    exact h
  have hk : ∀ i j, IsInt O (k i j) := fun i j => (hg i j).1
  have hki : ∀ i j, IsInt O (ki i j) := fun i j => ((KU O Δ).inv_mem hg i j).1
  have hsemi : ∀ x, Q (semi d x) = k *ᵥ star (Q x) := by
    intro x
    show M *ᵥ P (semi d x) = k *ᵥ star (Q x)
    rw [hM.semi, ← hPQ x, hsv, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨u, s0, hs0, hΔ⟩ := hL.even
    have hs : Δ * s0⁻¹ ^ 2 = algebraMap O K (u : O) := by
      rw [hΔ]; field_simp
    have hdesc := descent O K Δ hL s0⁻¹ u hs
    let w : Lsq K Δ := ⟨0, s0⁻¹⟩
    have hw : IsInt O w := by
      refine (hdesc w).1.mpr ⟨⟨0, map_zero _⟩, 1, ?_⟩
      show s0⁻¹ = s0⁻¹ * algebraMap O K 1
      rw [map_one, mul_one]
    have hdec : ∀ z : Lsq K Δ, IsInt O z →
        ∃ a b : O, z = algebraMap O (Lsq K Δ) a + algebraMap O (Lsq K Δ) b * w := by
      intro z hz
      obtain ⟨⟨a, ha⟩, b, hb⟩ := (hdesc z).1.mp hz
      refine ⟨a, b, ?_⟩
      ext <;> simp [w, ← ha, hb, IsScalarTower.algebraMap_apply O K (Lsq K Δ)] <;> ring
    let R : Fin 3 → Lsq K Δ → Sp Δ τ := fun i v => P.symm (G *ᵥ Pi.single i v)
    let S : Finset (Sp Δ τ) := Finset.univ.image (fun i => R i 1) ∪ Finset.univ.image (fun i => R i w)
    refine ⟨S, ?_⟩
    ext x
    constructor
    · intro hx
      have hx' : ∀ i, IsInt O (Q x i) := hx
      have hxe : x = ∑ i, R i (Q x i) := by
        show x = ∑ i, P.symm (G *ᵥ Pi.single i (Q x i))
        rw [← map_sum, ← Matrix.mulVec_sum, Finset.univ_sum_single, hPQ, P.symm_apply_apply]
      rw [hxe]
      refine Submodule.sum_mem _ fun i _ => ?_
      obtain ⟨a, b, hab⟩ := hdec _ (hx' i)
      have h1S : R i 1 ∈ (S : Set (Sp Δ τ)) :=
        Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
      have hwS : R i w ∈ (S : Set (Sp Δ τ)) :=
        Finset.mem_coe.mpr (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
      have hsp : (Pi.single i (Q x i) : Fin 3 → Lsq K Δ)
          = algebraMap O (Lsq K Δ) a • Pi.single i 1 + algebraMap O (Lsq K Δ) b • Pi.single i w := by
        rw [hab]
        funext j
        by_cases hij : j = i
        · subst hij
          rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_same,
            Pi.single_eq_same, smul_eq_mul, smul_eq_mul, mul_one]
        · simp [hij]
      have hR : R i (Q x i) = a • R i 1 + b • R i w := by
        show P.symm (G *ᵥ Pi.single i (Q x i)) = a • R i 1 + b • R i w
        rw [hsp, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, map_add, map_smul, map_smul,
          ← algebra_compatible_smul, ← algebra_compatible_smul]
      rw [hR]
      exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span h1S))
        (Submodule.smul_mem _ _ (Submodule.subset_span hwS))
    · intro hx
      have hQR : ∀ i v, Q (R i v) = Pi.single i v := fun i v => hQS _
      show ∀ i, IsInt O (Q x i)
      induction hx using Submodule.span_induction with
      | mem z hz =>
        rcases Finset.mem_union.mp (Finset.mem_coe.mp hz) with hz | hz
        · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hz
          rw [hQR]
          exact hsingle j 1 isIntegral_one
        · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hz
          rw [hQR]
          exact hsingle j w hw
      | zero =>
        intro i
        show IsInt O ((M *ᵥ P 0) i)
        rw [map_zero, Matrix.mulVec_zero]
        exact isIntegral_zero
      | add z v _ _ hz hv =>
        intro i
        show IsInt O ((M *ᵥ P (z + v)) i)
        rw [map_add, Matrix.mulVec_add]
        exact (hz i).add (hv i)
      | smul a z _ hz =>
        intro i
        show IsInt O ((M *ᵥ P (a • z)) i)
        rw [algebra_compatible_smul (Lsq K Δ) a z, map_smul, Matrix.mulVec_smul]
        exact isIntegral_algebraMap.mul (hz i)
  · intro y
    constructor
    · intro hy x hx
      rw [hform]
      exact hIsum _ fun i => hImul _ _ (hx i) ((hIstar _).mp (hy i))
    · intro h i
      have he : P.symm (G *ᵥ Pi.single i 1) ∈
          {x : Sp Δ τ | ∀ i, IsInt O ((((g⁻¹ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ P x) i)} := by
        intro j
        show IsInt O (Q (P.symm (G *ᵥ Pi.single i 1)) j)
        rw [hQS]
        exact hsingle i 1 isIntegral_one j
      have h2 := h _ he
      rw [hform, hQS] at h2
      simp only [dotProduct, Pi.single_apply, Pi.star_apply, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
      exact (hIstar _).mpr h2
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩ i
      show IsInt O (Q (semi d x) i)
      rw [hsemi]
      exact hIvec k _ hk (fun j => (hIstar _).mp (hx j)) i
    · intro hy
      refine ⟨P.symm (G *ᵥ star (ki *ᵥ Q y)), ?_, ?_⟩
      · intro i
        show IsInt O (Q (P.symm (G *ᵥ star (ki *ᵥ Q y))) i)
        rw [hQS]
        exact (hIstar _).mp (hIvec ki _ hki hy i)
      · apply P.injective
        rw [← hPQ, ← hPQ, hsemi, hQS, star_star]
        rw [show k *ᵥ (ki *ᵥ Q y) = Q y by rw [Matrix.mulVec_mulVec, hkki, Matrix.one_mulVec]]
