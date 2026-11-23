import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CharacteristicPolynomialRoots.LeKerPt
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CharacteristicPolynomialRoots.MemRootsIffSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CharacteristicPolynomialRoots.ExistsSeparatingElement

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC Formalism.MainNotions.N ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private noncomputable def twHom {O Γ : Type} [CommRing O] [Group Γ] (η : Γ →* Oˣ) : Γ →* MonoidAlgebra O Γ where
  toFun g := MonoidAlgebra.single g (η g : O)
  map_one' := by simp [MonoidAlgebra.one_def]
  map_mul' g h := by simp [MonoidAlgebra.single_mul_single]

private theorem lift_tw {O Γ A : Type} [CommRing O] [Group Γ] [Ring A] [Algebra O A] (η : Γ →* Oˣ) (f f' : Γ →* A)
    (h : ∀ g, f' g = (η g : O) • f g) (y : MonoidAlgebra O Γ) :
    MonoidAlgebra.lift O A Γ f (MonoidAlgebra.lift O (MonoidAlgebra O Γ) Γ (twHom η) y) = MonoidAlgebra.lift O A Γ f' y := by
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single g a =>
    simp only [MonoidAlgebra.lift_single, h, map_smul, smul_smul]
    simp [twHom, MonoidAlgebra.lift_single, smul_smul]

private theorem mem_max {l : ℕ} [Fact l.Prime] (c : Coef l) (x : c.O) (hx : ‖(x : PadicAlgCl l)‖ < 1) : x ∈ maximalIdeal c.O := by
  haveI := c.fin
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rintro ⟨u, rfl⟩
  have hint : IsIntegral ℤ_[l] (((u⁻¹ : (c.O)ˣ) : c.O) : PadicAlgCl l) :=
    (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) ((u⁻¹ : (c.O)ˣ) : c.O)).map c.O.val
  have h1 := (GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).1 hint
  have h2 : ((u : c.O) : PadicAlgCl l) * (((u⁻¹ : (c.O)ˣ) : c.O) : PadicAlgCl l) = 1 := by
    rw [← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one]
  have h3 := congrArg norm h2
  rw [norm_mul, norm_one] at h3
  have h4 : ‖((u : c.O) : PadicAlgCl l)‖ * ‖(((u⁻¹ : (c.O)ˣ) : c.O) : PadicAlgCl l)‖ < 1 :=
    calc _ ≤ ‖((u : c.O) : PadicAlgCl l)‖ * 1 := by gcongr
      _ < 1 := by simpa using hx
  linarith

private theorem pushCh_zpow_neg_zero_eq_mul_zpow_neg_one {l : ℕ} [Fact l.Prime] (c : Coef l) {Γ : Type} [Group Γ] (ε : Γ →* c.Oˣ) (g : Γ) :
    ((((W.pushCh (algebraMap c.O (PadicAlgCl l)) ε) ^ (-((0 : ℕ) : ℤ))) g : (PadicAlgCl l)ˣ) : PadicAlgCl l) =
      algebraMap c.O (PadicAlgCl l) (ε g) *
        ((((W.pushCh (algebraMap c.O (PadicAlgCl l)) ε) ^ (-((1 : ℕ) : ℤ))) g : (PadicAlgCl l)ˣ) : PadicAlgCl l) := by
  have h := Units.mul_inv (Units.map (algebraMap c.O (PadicAlgCl l) : c.O →* PadicAlgCl l) (ε g))
  simp only [Nat.cast_zero, neg_zero, zpow_zero, MonoidHom.one_apply, Units.val_one, Nat.cast_one,
    zpow_neg, zpow_one, MonoidHom.inv_apply, W.pushCh, MonoidHom.comp_apply]
  rw [← h]
  rfl

theorem UpperTheory.V.Ws.Pu.mOne :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) {Γ : Type} [Group Γ] {n : ℕ} (ρ : Γ →* GL (Fin n) (PadicAlgCl l)) (χ : Fin n → Γ →* (ResidueField c.O)ˣ) (ε : Γ →* c.Oˣ) (ε' : Γ →* (PadicAlgCl l)ˣ),
      RedTo c ρ χ → ε' = W.pushCh (algebraMap c.O (PadicAlgCl l)) ε → (∀ i j, χ i ≠ χ j * W.pushCh (residue c.O) ε) →
      ∀ (a : ℕ) (d m : Fin a → ℕ) (ρ' : ∀ i, Γ →* GL (Fin (d i)) (PadicAlgCl l)), (∀ i, 1 ≤ d i ∧ 1 ≤ m i) →
        (∀ g, (W.mat ρ g).charpoly = ∏ i, ∏ j ∈ Finset.range (m i), (W.mat (Af.tw (ρ' i) (ε' ^ (-(j : ℤ)))) g).charpoly) → ∀ i, m i = 1 := by
  intro l _ c Γ _ n ρ χ ε ε' hR hε hne a d m ρ' hdm hcp i
  subst hε
  by_contra hmi
  have h2 : 2 ≤ m i := by have := (hdm i).2; omega
  obtain ⟨y, hy1, hy0⟩ := Pu.sepEl (O := c.O) χ (fun b => χ b * W.pushCh (residue c.O) ε) (fun a b => hne a b)
  let Y := MonoidAlgebra.lift c.O (MonoidAlgebra c.O Γ) Γ (twHom ε) y
  let t : Finset (Σ _ : Fin a, ℕ) := Finset.univ.sigma (fun k => Finset.range (m k))
  let dd : (Σ _ : Fin a, ℕ) → ℕ := fun p => d p.1
  let σ : (p : Σ _ : Fin a, ℕ) → Γ →* GL (Fin (dd p)) (PadicAlgCl l) :=
    fun p => Af.tw (ρ' p.1) ((W.pushCh (algebraMap c.O (PadicAlgCl l)) ε) ^ (-(p.2 : ℤ)))
  have hcp' : ∀ g, (W.mat ρ g).charpoly = ∏ p ∈ t, (W.mat (σ p) g).charpoly := by
    intro g
    rw [hcp g, Finset.prod_sigma]
  have hroot : ∀ (M : Matrix (Fin (d i)) (Fin (d i)) (PadicAlgCl l)), ∃ z, z ∈ M.charpoly.roots := by
    intro M
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root M.charpoly (by
      rw [Polynomial.degree_eq_natDegree M.charpoly_monic.ne_zero, Matrix.charpoly_natDegree_eq_dim]
      have := (hdm i).1
      simp only [Fintype.card_fin, ne_eq, Nat.cast_eq_zero]
      omega)
    exact ⟨z, (Polynomial.mem_roots M.charpoly_monic.ne_zero).2 hz⟩
  obtain ⟨z, hz⟩ := hroot (MonoidAlgebra.lift c.O _ Γ (W.mat (σ ⟨i, 0⟩)) y)
  have hM : MonoidAlgebra.lift c.O _ Γ (W.mat (σ ⟨i, 1⟩)) Y =
      MonoidAlgebra.lift c.O _ Γ (W.mat (σ ⟨i, 0⟩)) y := by
    apply lift_tw
    intro g
    simp only [σ, W.mat, MonoidHom.comp_apply, Units.coeHom_apply, Af.tw_val]
    rw [← IsScalarTower.algebraMap_smul (PadicAlgCl l) ((ε g : c.O)), smul_smul, ← pushCh_zpow_neg_zero_eq_mul_zpow_neg_one]
  have hz0 := Pu.cpAlg ρ t dd σ hcp' y ⟨i, 0⟩ (by simp [t]; omega) z hz
  have hz1 := Pu.cpAlg ρ t dd σ hcp' Y ⟨i, 1⟩ (by simp [t]; omega) z (by rw [hM]; exact hz)
  obtain ⟨j0, a0, ha0, hza0⟩ := hR y z hz0
  obtain ⟨j1, a1, ha1, hza1⟩ := hR Y z hz1
  rw [hy1] at ha0
  have hY0 : MonoidAlgebra.lift c.O (ResidueField c.O) Γ ((Units.coeHom (ResidueField c.O)).comp (χ j1)) Y = 0 := by
    rw [lift_tw ε _ ((Units.coeHom (ResidueField c.O)).comp (χ j1 * W.pushCh (residue c.O) ε)) _ y]
    · exact hy0 j1
    · intro g
      simp [Algebra.smul_def, W.pushCh, mul_comm]
  rw [hY0] at ha1
  have hm : a0 - a1 ∈ maximalIdeal c.O := mem_max c _ (by
    have e : ((a0 - a1 : c.O) : PadicAlgCl l) = (z - a1) + -(z - a0) := by push_cast; ring
    rw [e]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) ?_
    rw [norm_neg]
    exact max_lt hza1 hza0)
  have hr : residue c.O (a0 - a1) = 0 := (IsLocalRing.residue_eq_zero_iff _).2 hm
  rw [map_sub, ha0, ha1, sub_zero] at hr
  exact one_ne_zero hr
