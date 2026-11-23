import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PosExact
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Z1fMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrysOfInertia
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrystallineExtensionIffMemFiniteCocycles
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrystallineUpperTriangularIffMemFiniteCocycles
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiltByRestrictScalarsOfResidualCharacters
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

private theorem mem_ker_smul {B E : Type} [CommRing B] [CommRing E] (π : B →+* E) (u v : B) (hu : π u = 0)
    (hv : π v = 0) : ((u, v) : B × B) ∈ (RingHom.ker π) • (⊤ : Submodule B (B × B)) := by
  have h : ((u, v) : B × B) = u • ((1, 0) : B × B) + v • ((0, 1) : B × B) := by simp
  rw [h]
  exact Submodule.add_mem _ (Submodule.smul_mem_smul hu trivial) (Submodule.smul_mem_smul hv trivial)

private def triHom {G B : Type} [Group G] [CommRing B] (κ : Fin 3 → G →* Bˣ) (x y z : G → B)
    (hx : ∀ g h, x (g * h) = x g + ((κ 0 / κ 1) g : Bˣ) * x h)
    (hy : ∀ g h, y (g * h) = y g + ((κ 1 / κ 2) g : Bˣ) * y h)
    (hz : ∀ g h, z (g * h) = z g + (((κ 0 / κ 2) g : Bˣ) * z h + x g * ((κ 1 / κ 2) g : Bˣ) * y h)) :
    G →* Matrix (Fin 3) (Fin 3) B where
  toFun g := triM (fun i => κ i g) (x g) (y g) (z g)
  map_one' := by
    have h1 := hx 1 1
    have h2 := hy 1 1
    have h3 := hz 1 1
    simp only [mul_one, map_one, Units.val_one, one_mul, left_eq_add] at h1 h2
    simp only [mul_one, map_one, Units.val_one, one_mul, left_eq_add, h1, zero_mul, add_zero] at h3
    ext i j
    fin_cases i <;> fin_cases j <;> simp [triM, h1, h2, h3]
  map_mul' g h := by
    have e : ∀ i j, (κ i g : B) = (((κ i / κ j) g : Bˣ) : B) * κ j g := fun i j => by
      rw [← Units.val_mul, MonoidHom.div_apply, div_mul_cancel]
    have e1 := e 0 1
    have e2 := e 1 2
    have e3 := e 0 2
    have h1 := hx g h
    have h2 := hy g h
    have h3 := hz g h
    generalize (((κ 0 / κ 1) g : Bˣ) : B) = p at *
    generalize (((κ 1 / κ 2) g : Bˣ) : B) = q at *
    generalize (((κ 0 / κ 2) g : Bˣ) : B) = r at *
    ext i j
    fin_cases i <;> fin_cases j <;> simp [triM, h1, h2, h3, Matrix.mul_apply, Fin.sum_univ_three]
    · linear_combination (-(x h * κ 1 h)) * e1
    · linear_combination (-(z h * κ 2 h)) * e3 - (x g * y h * κ 2 h) * e2
    · linear_combination (-(y h * κ 2 h)) * e2

theorem UpperTheory.exists_crystalline_triangular_lift_of_mem_finiteCocycles :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) {e : ℕ} {ψ : G →* Eˣ} {κ : Fin 3 → G →* Bˣ}, Chars φ π e ψ κ → ∀ x ∈ UpperTheory.V.Loc.finiteCocycles φ (chRep (κ 0 / κ 1)), ∀ y ∈ UpperTheory.V.Loc.finiteCocycles φ (chRep (κ 1 / κ 2)), (∀ g, π (x g) = 0) → ∃ (z : G → B) (ρ : G →* GL (Fin 3) B), Continuous z ∧ (∀ g, (ρ g : Matrix (Fin 3) (Fin 3) B) = triM (fun i => κ i g) (x g) (y g) (z g)) ∧ IsCr φ (colRep ρ) := by
  intro hP l _ G _ _ _ φ hφ E _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ e ψ κ hκ x hx y hy hx0
  haveI : ContinuousConstSMul E B := contConstSMul_alg E
  haveI : Module.Finite E B := Module.Finite.of_restrictScalars_finite ℚ_[l] E B
  have hxc : Continuous x := hx.1.1
  have hyc : Continuous y := hy.1.1
  have hxm : ∀ g h, x (g * h) = x g + ((κ 0 / κ 1) g : Bˣ) * x h := hx.1.2
  have hym : ∀ g h, y (g * h) = y g + ((κ 1 / κ 2) g : Bˣ) * y h := hy.1.2
  have hab : (κ 0 / κ 2) / (κ 1 / κ 2) = κ 0 / κ 1 := div_div_div_cancel_right _ _ _
  have hxm' : ∀ g h, x (g * h) = x g + (((κ 0 / κ 2) / (κ 1 / κ 2)) g : Bˣ) * x h := by rw [hab]; exact hxm
  have hcr : ∀ i, IsCr φ (chRep (κ i)) := fun i =>
    crUnr φ hφ _ (contAction_chRep (hκ.cont i)) (e * wt1 i) fun g hg v => by
      rw [chRep_apply, hκ.ine g hg, smul_eq_mul]
  have hcd : ∀ i j, Continuous fun g => (((κ i / κ j) g : Bˣ) : B) := fun i j => cont_char_div (hκ.cont i) (hκ.cont j)
  have hcr' : ∀ i j, IsCr φ (chRep (κ i / κ j)) := fun i j =>
    crUnr φ hφ _ (contAction_chRep (hcd i j)) (e * wt1 i - e * wt1 j) fun g hg v => by
      rw [chRep_apply, MonoidHom.div_apply, hκ.ine g hg, hκ.ine g hg, smul_eq_mul, zpow_sub, div_eq_mul_inv]
  have hred : ∀ i j g, π (((κ i / κ j) g : Bˣ) : B) = ((ψ g ^ (wt1 i - wt1 j) : Eˣ) : E) := fun i j g => by
    have h1 : (((κ i / κ j) g : Bˣ) : B) * κ j g = κ i g := by
      rw [← Units.val_mul, MonoidHom.div_apply, div_mul_cancel]
    have h2 := congrArg π h1
    rw [map_mul, hκ.red, hκ.red] at h2
    rw [zpow_sub, Units.val_mul, ← h2, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  let T := ext2 (κ 0 / κ 2) (κ 1 / κ 2) x hxm'
  have hTc : ContAction T := contAction_charExtension_of_continuous_cocycle (hcd 0 2) (hcd 1 2) hxm' hxc
  have hTcr : IsCr φ T :=
    (UpperTheory.isCrystalline_extension_iff_mem_finiteCocycles φ hφ _ _ (hcd 0 2) (hcd 1 2) x hxm' hxc (hcr' 0 2) (hcr' 1 2)).2 (by rw [hab]; exact hx)
  have hTdr : IsDr φ (resCoef E T) := (isCrys_isDR_restrict_openSubgroup φ hφ T hTc).1 hTcr
  have hwt : ∀ n : ℕ, 1 ≤ n → ψ ^ n ∈ {κ : G →* Eˣ | ∃ w : ℤ, 1 ≤ w ∧ HasWeight φ κ w} := fun n hn =>
    ⟨((e * n : ℕ) : ℤ), by exact_mod_cast Nat.mul_pos hκ.e_pos hn, ⊤, by simp, fun g _ hg => by
      rw [MonoidHom.pow_apply, hκ.wt g hg, zpow_natCast, pow_mul]⟩
  have hTf : FiltBy (resCoef E T) {κ | ∃ w : ℤ, 1 ≤ w ∧ HasWeight φ κ w} := by
    refine UpperTheory.filtBy_restrictScalars_of_residual_characters π hπ T _ (ι := Fin 2) ![(1, 0), (0, 1)] ![ψ ^ 2, ψ ^ 1] ?_ ?_ ?_
    · rw [eq_top_iff]
      rintro ⟨u, v⟩ -
      have h : ((u, v) : B × B) = u • ((1, 0) : B × B) + v • ((0, 1) : B × B) := by simp
      rw [h]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
    · intro j
      fin_cases j
      · exact hwt 2 (by norm_num)
      · exact hwt 1 le_rfl
    · intro g j
      have a1 := hred 0 2 g
      have a2 := hred 1 2 g
      have w1 : wt1 0 - wt1 2 = ((2 : ℕ) : ℤ) := by decide
      have w2 : wt1 1 - wt1 2 = ((1 : ℕ) : ℤ) := by decide
      rw [w1, zpow_natCast] at a1
      rw [w2, zpow_natCast] at a2
      fin_cases j
      · refine mem_ker_smul (π : B →+* E) _ _ ?_ ?_
        · change π (((κ 0 / κ 2) g : Bˣ) * 1 + x g * ((κ 1 / κ 2) g : Bˣ) * 0 - ((ψ g ^ 2 : Eˣ) : E) • (1 : B)) = 0
          rw [mul_one, mul_zero, add_zero, map_sub, a1, map_smul, map_one, smul_eq_mul, mul_one, sub_self]
        · change π (((κ 1 / κ 2) g : Bˣ) * 0 - ((ψ g ^ 2 : Eˣ) : E) • (0 : B)) = 0
          rw [mul_zero, smul_zero, sub_zero, map_zero]
      · refine mem_ker_smul (π : B →+* E) _ _ ?_ ?_
        · change π (((κ 0 / κ 2) g : Bˣ) * 0 + x g * ((κ 1 / κ 2) g : Bˣ) * 1 - ((ψ g ^ 1 : Eˣ) : E) • (0 : B)) = 0
          rw [mul_one, mul_zero, zero_add, smul_zero, sub_zero, map_mul, hx0, zero_mul]
        · change π (((κ 1 / κ 2) g : Bˣ) * 1 - ((ψ g ^ 1 : Eˣ) : E) • (1 : B)) = 0
          rw [mul_one, map_sub, a2, map_smul, map_one, smul_eq_mul, mul_one, sub_self]
  obtain ⟨c, hc, hcy⟩ := (posExact hP φ hφ (resCoef E T) (resCoef E (chRep (κ 1 / κ 2))) hTc
    (contAction_chRep (hcd 1 2)) ⟨hTdr, hTf⟩ (LinearMap.snd E B B) (fun g v => rfl)).1 Prod.snd_surjective y hy
  have hcT : c ∈ UpperTheory.V.Loc.finiteCocycles φ T := hc
  have hc2 : ∀ g, (c g).2 = y g := fun g => congrFun hcy g
  have hzc : Continuous fun g => (c g).1 := hcT.1.1.fst
  have hzm : ∀ g h, (c (g * h)).1 =
      (c g).1 + (((κ 0 / κ 2) g : Bˣ) * (c h).1 + x g * ((κ 1 / κ 2) g : Bˣ) * y h) := fun g h => by
    rw [← hc2 h]
    exact congrArg Prod.fst (hcT.1.2 g h)
  let ρ := (triHom κ x y (fun g => (c g).1) hxm hym hzm).toHomUnits
  refine ⟨fun g => (c g).1, ρ, hzc, fun g => rfl, ?_⟩
  have h01 : IsCr φ (ext2 (κ 0) (κ 1) x hxm) :=
    (UpperTheory.isCrystalline_extension_iff_mem_finiteCocycles φ hφ _ _ (hκ.cont 0) (hκ.cont 1) x hxm hxc (hcr 0) (hcr 1)).2 hx
  refine (UpperTheory.isCrystalline_upperTriangular_iff_mem_finiteCocycles φ hφ κ hκ.cont x y _ ρ hxc hyc hzc (fun g => rfl) hxm h01 (hcr 2)).2 ?_
  have hT : twist (κ 2)⁻¹ (ext2 (κ 0) (κ 1) x hxm) = T := by
    refine MonoidHom.ext fun g => LinearMap.ext fun v => ?_
    rw [twist_apply, characterExtensionRep_apply, characterExtensionRep_apply]
    simp only [div_eq_mul_inv, MonoidHom.mul_apply, Units.val_mul, Prod.smul_mk, smul_eq_mul]
    ext <;> simp only [] <;> ring
  have hc' : (fun g => ((c g).1, y g)) = c := funext fun g => by rw [← hc2 g]
  rw [hT, hc']
  exact hcT
