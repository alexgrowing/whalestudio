import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CrDefs

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg UpperTheory.V.Pr UpperTheory.V

namespace UpperTheory.V.Pr

end UpperTheory.V.Pr

theorem UpperTheory.frame_criterion_residual :
    UpperTheory.V.Pr.CrResid := by
  intro l _ O _ _ _ F G n hn hk hg π hπ hs hc κ hκ hκe
  let χ : Fin n → G.G₀ →* (ResidueField O)ˣ := fun i =>
    { toFun := fun g => F.Ψ (π g : F.Γ) ^ Fr.w n i * W.pushCh (residue O) κ g
      map_one' := by simp
      map_mul' := by
        intro a b
        simp only [map_mul, Subgroup.coe_mul, mul_zpow]
        exact mul_mul_mul_comm _ _ _ _ }
  have hψ : IsOpen ((F.Ψ.comp (F.del.ker.subtype.comp π)).ker : Set G.G₀) := by
    rw [← MonoidHom.comap_ker, Subgroup.coe_comap]
    exact hk.preimage (continuous_subtype_val.comp hπ)
  have hκo : IsOpen ((W.pushCh (residue O) κ).ker : Set G.G₀) := by
    have h1 := (hκ 1).isOpen_fiber (Ideal.Quotient.mk (maximalIdeal O ^ 1) 1)
    convert h1 using 1
    ext g
    rw [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_setOf_eq, Ideal.Quotient.eq, pow_one, Units.ext_iff]
    show residue O (κ g : O) = 1 ↔ _
    rw [← map_one (residue O)]
    exact Ideal.Quotient.eq
  have hopen : ∀ i, IsOpen ((χ i).ker : Set G.G₀) := by
    intro i
    refine Subgroup.isOpen_mono (H₁ := (F.Ψ.comp (F.del.ker.subtype.comp π)).ker ⊓ (W.pushCh (residue O) κ).ker) ?_ (by rw [Subgroup.coe_inf]; exact hψ.inter hκo)
    intro g hg
    rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hg
    rw [MonoidHom.mem_ker]
    show F.Ψ (π g : F.Γ) ^ Fr.w n i * W.pushCh (residue O) κ g = 1
    rw [hg.2, mul_one]
    have : F.Ψ (π g : F.Γ) = 1 := hg.1
    rw [this, one_zpow]
  have hinj : Function.Injective χ := by
    intro i j hij
    obtain ⟨g, hg0⟩ := hs F.g0
    have h := DFunLike.congr_fun hij g
    change F.Ψ (π g : F.Γ) ^ Fr.w n i * _ = F.Ψ (π g : F.Γ) ^ Fr.w n j * _ at h
    rw [mul_right_cancel_iff, hg0] at h
    have key : F.Ψ (F.g0 : F.Γ) ^ (Fr.w n i - Fr.w n j) = 1 := by
      rw [zpow_sub, h, mul_inv_cancel]
    have hu2 : F.Ψ (F.g0 : F.Γ) ^ (2:ℤ) ≠ 1 := by exact_mod_cast hg
    have hu1 : F.Ψ (F.g0 : F.Γ) ≠ 1 := by
      intro h1
      apply hu2
      rw [h1, one_zpow]
    rcases hn with rfl | rfl <;> fin_cases i <;> fin_cases j <;> simp [Fr.w] at key ⊢
    all_goals first
      | exact hg key
      | exact hu1 key
      | exact hu2 key
      | exact hu1 (inv_eq_one.mp key)
      | exact hg (inv_eq_one.mp (by simpa [zpow_neg] using key))
  have hw : ∀ i : Fin n, Fr.w n (Fin.rev i) = - Fr.w n i := by
    intro i
    rcases hn with rfl | rfl <;> fin_cases i <;> simp [Fr.w] <;> decide
  have hΨc : ∀ g, F.Ψ (π (G.conj g) : F.Γ) = F.Ψ (π g : F.Γ) := by
    intro g
    rw [hc]
    simp [Fr.Frame.conj, MulAut.conjNormal_apply]
  have heps : ∀ g, Units.map (residue O : O →* ResidueField O) (G.eps O O g) = G.eps O (ResidueField O) g := by
    intro g
    ext
    simp [W.GFrame.eps, W.pushCh]
  have hκc : ∀ g, W.pushCh (residue O) κ (G.conj g) = (G.eps O (ResidueField O) g) ^ (1 - (n:ℤ)) * (W.pushCh (residue O) κ g)⁻¹ := by
    intro g
    have h1 : κ (G.conj g) = (G.eps O O g) ^ (1 - (n:ℤ)) * (κ g)⁻¹ := by
      rw [← hκe g, mul_comm (κ g) (κ (G.conj g)), mul_inv_cancel_right]
    show Units.map (residue O : O →* ResidueField O) (κ (G.conj g)) = _
    rw [h1, map_mul, map_inv, map_zpow, heps]
    rfl
  have hstar : ∀ i g, (G.eps O (ResidueField O) g) ^ (1 - (n:ℤ)) * (χ i (G.conj g))⁻¹ = χ (Fin.rev i) g := by
    intro i g
    show _ * (F.Ψ (π (G.conj g) : F.Γ) ^ Fr.w n i * W.pushCh (residue O) κ (G.conj g))⁻¹ = F.Ψ (π g : F.Γ) ^ Fr.w n (Fin.rev i) * W.pushCh (residue O) κ g
    rw [hΨc, hκc, hw, zpow_neg, mul_inv, mul_inv, inv_inv, mul_left_comm, mul_inv_cancel_left]
  have hpolar : G.IsPolar O (W.GDet.ofRep (W.diagRep χ)) := by
    intro B _ _ _ _ y
    let f : Fin n → G.G₀ →* B := fun i => (algebraMap (ResidueField O) B : ResidueField O →* B).comp ((Units.coeHom (ResidueField O)).comp (χ i))
    have hdiag : ∀ z : MonoidAlgebra B G.G₀, W.GDet.repAlg (W.diagRep χ) B z = Matrix.diagonal (fun i => MonoidAlgebra.lift B B G.G₀ (f i) z) := by
      intro z
      induction z using MonoidAlgebra.induction_linear with
      | zero => simp
      | add x y hx hy =>
        rw [map_add, hx, hy, Matrix.diagonal_add]
        congr 1
        ext i
        simp [map_add]
      | single g b =>
        ext i j
        simp [f, W.GDet.repAlg, W.diagRep, MonoidAlgebra.lift_single, Matrix.diagonal_apply]
    have hepsB : ∀ g, Units.map (algebraMap (ResidueField O) B : ResidueField O →* B) (G.eps O (ResidueField O) g) = G.eps O B g := by
      intro g
      ext
      simp [W.GFrame.eps, W.pushCh, IsScalarTower.algebraMap_apply O (ResidueField O) B]
    have hs1 : ∀ (g : G.G₀) (b : B), G.star O B n (MonoidAlgebra.single g b) = MonoidAlgebra.single (G.conj g)⁻¹ (b * ((G.eps O B g ^ (1 - (n:ℤ)) : Bˣ) : B)) := by
      intro g b
      simp [W.GFrame.star, W.GFrame.starOp, MonoidAlgebra.lift_single, MonoidAlgebra.smul_single']
    have hrev : ∀ i z, MonoidAlgebra.lift B B G.G₀ (f i) (G.star O B n z) = MonoidAlgebra.lift B B G.G₀ (f (Fin.rev i)) z := by
      intro i z
      induction z using MonoidAlgebra.induction_linear with
      | zero => simp [W.GFrame.star]
      | add x y hx hy =>
        have hadd : G.star O B n (x + y) = G.star O B n x + G.star O B n y := by simp [W.GFrame.star]
        rw [hadd, map_add, map_add, hx, hy]
      | single g b =>
        rw [hs1 g b, MonoidAlgebra.lift_single, MonoidAlgebra.lift_single, smul_eq_mul, smul_eq_mul, mul_assoc]
        congr 1
        rw [← hepsB g, ← map_zpow, Units.coe_map]
        show _ = algebraMap (ResidueField O) B ((χ (Fin.rev i) g : (ResidueField O)ˣ) : ResidueField O)
        rw [← hstar i g, Units.val_mul, map_mul]
        simp [f]
    show Matrix.det (W.GDet.repAlg (W.diagRep χ) B (G.star O B n y)) = Matrix.det (W.GDet.repAlg (W.diagRep χ) B y)
    rw [hdiag, hdiag, Matrix.det_diagonal, Matrix.det_diagonal]
    simp only [hrev]
    exact Fintype.prod_equiv Fin.revPerm _ _ (fun i => rfl)
  refine ⟨⟨χ, hopen, hinj, hpolar, fun v i => (χ i).comp (G.φ v), ?_, fun _ _ => 1, ?_⟩, ?_, ?_⟩
  · intro v i
    rw [← MonoidHom.comap_ker, Subgroup.coe_comap]
    exact (hopen i).preimage (G.φ_cont v)
  · intro v i g _
    rfl
  · intro i g
    rfl
  · intro v i g
    rfl
