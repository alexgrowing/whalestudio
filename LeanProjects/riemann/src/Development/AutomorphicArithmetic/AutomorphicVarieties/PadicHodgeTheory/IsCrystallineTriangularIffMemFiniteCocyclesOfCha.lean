import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PosExact
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Z1fMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrysOfInertia
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrystallineExtensionIffMemFiniteCocycles
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrystallineUpperTriangularIffMemFiniteCocycles
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiltByRestrictScalarsOfResidualCharacters
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

private theorem coc {G B : Type} [Group G] [CommRing B] {κ : Fin 3 → G →* Bˣ} {x y z : G → B}
    {ρ : G →* GL (Fin 3) B}
    (h : ∀ g, (ρ g : Matrix (Fin 3) (Fin 3) B) = triM (fun i => κ i g) (x g) (y g) (z g)) :
    (∀ g g', x (g * g') = x g + ((κ 0 / κ 1) g : Bˣ) * x g') ∧
    ∀ g g', z (g * g') = z g + ((κ 0 / κ 2) g : Bˣ) * z g' + x g * ((κ 1 / κ 2) g : Bˣ) * y g' := by
  have e : ∀ (i j : Fin 3) g, (((κ i / κ j) g : Bˣ) : B) * κ j g = κ i g := fun i j g => by
    rw [← Units.val_mul, MonoidHom.div_apply, div_mul_cancel]
  have m : ∀ g g', triM (fun i => κ i (g * g')) (x (g * g')) (y (g * g')) (z (g * g')) =
      triM (fun i => κ i g) (x g) (y g) (z g) * triM (fun i => κ i g') (x g') (y g') (z g') := fun g g' => by
    rw [← h, ← h, ← h, map_mul, Units.val_mul]
  refine ⟨fun g g' => ?_, fun g g' => ?_⟩
  · have h1 := congrFun (congrFun (m g g') 0) 1
    simp only [triM, Matrix.mul_apply, Fin.sum_univ_three, map_mul, Units.val_mul] at h1
    simp at h1
    apply (κ 1 g * κ 1 g').isUnit.mul_right_cancel
    rw [Units.val_mul, h1, ← e 0 1 g]
    ring
  · have h1 := congrFun (congrFun (m g g') 0) 2
    simp only [triM, Matrix.mul_apply, Fin.sum_univ_three, map_mul, Units.val_mul] at h1
    simp at h1
    apply (κ 2 g * κ 2 g').isUnit.mul_right_cancel
    rw [Units.val_mul, h1, ← e 0 2 g, ← e 1 2 g]
    ring

private theorem mem_ker_smul {E B V : Type} [Field E] [CommRing B] [Algebra E B] [AddCommGroup V] [Module B V]
    (π : B →ₐ[E] E) {a : B} (ha : π a = 0) (v : V) :
    a • v ∈ (RingHom.ker (π : B →+* E)) • (⊤ : Submodule B V) :=
  Submodule.smul_mem_smul (by simpa using ha) trivial

theorem UpperTheory.isCrystalline_triangular_iff_mem_finiteCocycles_of_charData :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) {e : ℕ} {ψ : G →* Eˣ} {κ : Fin 3 → G →* Bˣ}, Chars φ π e ψ κ → ∀ (x y z : G → B) (ρ : G →* GL (Fin 3) B), Continuous x → Continuous y → Continuous z → (∀ g, (ρ g : Matrix (Fin 3) (Fin 3) B) = triM (fun i => κ i g) (x g) (y g) (z g)) → (∀ g, π (x g) = 0) → IsCr φ (colRep ρ) → ∀ (z' : G → B) (ρ' : G →* GL (Fin 3) B), Continuous z' → (∀ g, (ρ' g : Matrix (Fin 3) (Fin 3) B) = triM (fun i => κ i g) (x g) (y g) (z' g)) → z' - z ∈ Z1 (chRep (κ 0 / κ 2)) ∧ (IsCr φ (colRep ρ') ↔ z' - z ∈ UpperTheory.V.Loc.finiteCocycles φ (chRep (κ 0 / κ 2))) := by
  intro hP l _ G _ _ _ φ hφ E _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ e ψ κ hκ x y z ρ hxc hyc hzc hρ hx0 hcr z' ρ' hzc' hρ'
  obtain ⟨hx, hz⟩ := coc hρ
  obtain ⟨-, hz'⟩ := coc hρ'
  have : Module.Finite E B := Module.Finite.of_restrictScalars_finite ℚ_[l] E B
  have := contConstSMul_alg (B := B) E
  have hZ : z' - z ∈ Z1 (chRep (κ 0 / κ 2)) := by
    refine ⟨hzc'.sub hzc, fun g h => ?_⟩
    simp only [Pi.sub_apply, hz, hz', chRep_apply]
    ring
  refine ⟨hZ, ?_⟩
  have w0 : wt1 0 = 1 := rfl
  have w1 : wt1 1 = 0 := rfl
  have w2 : wt1 2 = -1 := rfl
  have cd : ∀ i j, Continuous fun g => (((κ i / κ j) g : Bˣ) : B) := fun i j => cont_char_div (hκ.cont i) (hκ.cont j)
  have crk : ∀ i, IsCr φ (chRep (κ i)) := fun i =>
    crUnr φ hφ _ (contAction_chRep (hκ.cont i)) (e * wt1 i) fun g hg v => by
      rw [chRep_apply, hκ.ine g hg, smul_eq_mul]
  have crd : ∀ i j, IsCr φ (chRep (κ i / κ j)) := fun i j =>
    crUnr φ hφ _ (contAction_chRep (cd i j)) (e * wt1 i - e * wt1 j) fun g hg v => by
      rw [chRep_apply, MonoidHom.div_apply, hκ.ine g hg, hκ.ine g hg, zpow_sub, div_eq_mul_inv, smul_eq_mul]
  have red : ∀ i j g, π (((κ i / κ j) g : Bˣ) : B) = (((ψ ^ (wt1 i - wt1 j)) g : Eˣ) : E) := fun i j g => by
    have e1 : (((κ i / κ j) g : Bˣ) : B) * κ j g = κ i g := by
      rw [← Units.val_mul, MonoidHom.div_apply, div_mul_cancel]
    have e2 := congrArg π e1
    rw [map_mul, hκ.red, hκ.red] at e2
    apply (ψ g ^ wt1 j).isUnit.mul_right_cancel
    rw [e2, ← Units.val_mul, MonoidHom.zpow_apply, ← zpow_add, sub_add_cancel]
  have hw : ∀ n : ℤ, 1 ≤ n → (ψ ^ n) ∈ {κ : G →* Eˣ | ∃ w : ℤ, 1 ≤ w ∧ HasWeight φ κ w} := fun n hn => by
    have := hκ.e_pos
    refine ⟨e * n, by nlinarith, ⊤, by simp, fun g _ hg => ?_⟩
    rw [MonoidHom.zpow_apply, hκ.wt g hg, zpow_mul, zpow_natCast]
  have cρ : ContAction (colRep ρ) := contAction_colRep (by
    simp only [hρ]
    exact continuous_triM hκ.cont hxc hyc hzc)
  have c2 := contAction_charExtension_of_continuous_cocycle (hκ.cont 0) (hκ.cont 1) hx hxc
  have cr2 : IsCr φ (ext2 (κ 0) (κ 1) x hx) := by
    let f : B × B →ₗ[ℚ_[l]] (Fin 3 → B) :=
      { toFun := fun v => ![v.1, v.2, 0]
        map_add' := fun v w => by ext i; fin_cases i <;> simp
        map_smul' := fun c v => by ext i; fin_cases i <;> simp }
    refine ((isCrys_isDR_sub_quot φ hφ _ _ c2 cρ f fun g v => ?_).1 fun v w h => ?_).1 hcr
    · ext i
      fin_cases i <;> simp [f, characterExtensionRep_apply, colRep_apply, hρ, triM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    · exact Prod.ext (congrFun h 0) (congrFun h 1)
  have hxf := (UpperTheory.isCrystalline_extension_iff_mem_finiteCocycles φ hφ _ _ (hκ.cont 0) (hκ.cont 1) x hx hxc (crk 0) (crk 1)).1 cr2
  have ed : (κ 0 / κ 2) / (κ 1 / κ 2) = κ 0 / κ 1 := div_div_div_cancel_right _ _ _
  have hx' : ∀ g h, x (g * h) = x g + (((κ 0 / κ 2) / (κ 1 / κ 2)) g : Bˣ) * x h := by rw [ed]; exact hx
  have eM : twist (κ 2)⁻¹ (ext2 (κ 0) (κ 1) x hx) = ext2 (κ 0 / κ 2) (κ 1 / κ 2) x hx' := by
    refine MonoidHom.ext fun g => LinearMap.ext fun v => ?_
    simp only [twist_apply, characterExtensionRep_apply, div_eq_mul_inv, MonoidHom.mul_apply, Units.val_mul, Prod.smul_mk, smul_eq_mul]
    ext <;> simp only [] <;> ring
  have k1 := (UpperTheory.isCrystalline_upperTriangular_iff_mem_finiteCocycles φ hφ κ hκ.cont x y z ρ hxc hyc hzc hρ hx cr2 (crk 2)).1 hcr
  have k2 := UpperTheory.isCrystalline_upperTriangular_iff_mem_finiteCocycles φ hφ κ hκ.cont x y z' ρ' hxc hyc hzc' hρ' hx cr2 (crk 2)
  rw [eM] at k1 k2
  set M := ext2 (κ 0 / κ 2) (κ 1 / κ 2) x hx' with hM
  have cM : ContAction M := contAction_charExtension_of_continuous_cocycle (cd 0 2) (cd 1 2) hx' hxc
  have crM : IsCr φ M :=
    (UpperTheory.isCrystalline_extension_iff_mem_finiteCocycles φ hφ _ _ (cd 0 2) (cd 1 2) x hx' hxc (crd 0 2) (crd 1 2)).2 (by rw [ed]; exact hxf)
  have cχ := contAction_chRep (cd 0 2)
  have inl : ∀ g v, LinearMap.inl E B B (chRep (κ 0 / κ 2) g v) = M g (LinearMap.inl E B B v) := fun g v => by
    simp [hM, characterExtensionRep_apply, chRep_apply]
  have pχ : Positive φ (resCoef E (chRep (κ 0 / κ 2))) := by
    refine ⟨(isCrys_isDR_restrict_openSubgroup φ hφ _ cχ).1 (crd 0 2), UpperTheory.filtBy_restrictScalars_of_residual_characters π hπ _ _ (fun _ : Unit => (1 : B))
      (fun _ => ψ ^ (wt1 0 - wt1 2)) (by simp) (fun _ => hw _ (by decide)) fun g _ => ?_⟩
    have := mem_ker_smul π (a := ((κ 0 / κ 2) g : Bˣ) - algebraMap E B ((ψ ^ (wt1 0 - wt1 2)) g : Eˣ))
      (by rw [map_sub, red, AlgHom.commutes]; simp) (1 : B)
    rwa [sub_smul, algebraMap_smul] at this
  have pM : Positive φ (resCoef E M) := by
    refine ⟨(isCrys_isDR_restrict_openSubgroup φ hφ _ cM).1 crM, UpperTheory.filtBy_restrictScalars_of_residual_characters π hπ _ _ (![(1, 0), (0, 1)] : Fin 2 → B × B)
      ![ψ ^ (wt1 0 - wt1 2), ψ ^ (wt1 1 - wt1 2)] ?_ (fun j => ?_) fun g j => ?_⟩
    · refine eq_top_iff.2 fun v _ => ?_
      have : v = v.1 • ((1, 0) : B × B) + v.2 • ((0, 1) : B × B) := by simp
      rw [this]
      exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
    · fin_cases j
      · exact hw _ (by decide)
      · exact hw _ (by decide)
    · have t : ∀ i (v : B × B), _ := fun i v =>
        mem_ker_smul π (a := ((κ i / κ 2) g : Bˣ) - algebraMap E B ((ψ ^ (wt1 i - wt1 2)) g : Eˣ))
          (by rw [map_sub, red, AlgHom.commutes]; simp) v
      fin_cases j
      · convert t 0 (1, 0) using 1
        rw [sub_smul, algebraMap_smul]
        simp [hM, characterExtensionRep_apply]
      · convert add_mem (t 1 (0, 1)) (mem_ker_smul π (a := x g * ((κ 1 / κ 2) g : Bˣ))
          (by rw [map_mul, hx0, zero_mul]) ((1, 0) : B × B)) using 1
        rw [sub_smul, algebraMap_smul]
        simp [hM, characterExtensionRep_apply]
  have dif : (fun g => (z' g, y g)) - (fun g => (z g, y g)) = fun g => LinearMap.inl E B B ((z' - z) g) := by
    funext g
    simp
  rw [k2]
  constructor
  · intro h
    have h1 := sub_mem h k1
    rw [dif] at h1
    have h2 := (z1fMap φ M (resCoef E M)).2 LinearMap.id (fun _ _ => rfl) _ h1
    have h3 := (posExact hP φ hφ (resCoef E (chRep (κ 0 / κ 2))) (resCoef E M) cχ cM pχ (LinearMap.inl E B B) inl).2 LinearMap.inl_injective pM _ hZ h2
    exact (z1fMap φ (resCoef E (chRep (κ 0 / κ 2))) (chRep (κ 0 / κ 2))).2 LinearMap.id (fun _ _ => rfl) _ h3
  · intro h
    have h1 := (z1fMap φ _ M).2 ((LinearMap.inl E B B).restrictScalars ℚ_[l]) inl _ h
    have h2 := add_mem h1 k1
    convert h2 using 1
    funext g
    simp
