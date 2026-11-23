import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Counterexamples.AbelianLawCounterexamples.MulGenNegRight

noncomputable section

namespace GlobalTheory.LamBiext

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

section Nest

variable {X W Y Z : Scheme.{0}} (L : LB X) {I K : Type} [Fintype I] [Fintype K]
  (φ : I → (W ⟶ X)) (δ : I → ℤ) (ψ : K → (Y ⟶ W)) (ε : K → ℤ)

abbrev flatφ : K × I → (Y ⟶ X) := fun p => ψ p.1 ≫ φ p.2

abbrev flatε : K × I → ℤ := fun p => ε p.1 * δ p.2

theorem nest_le (j : K → I → L.ι) :
    LB.wchart (LB.LinComb L φ δ) ψ j ≤ LB.wchart L (flatφ φ ψ) (fun p => j p.1 p.2) :=
  fun _ hy => Set.mem_iInter.2 fun p => Set.mem_iInter.1 (Set.mem_iInter.1 hy p.1) p.2

def nest (t : LB.Gen (LB.LinComb L (flatφ φ ψ) (flatε δ ε))) :
    LB.Gen (LB.LinComb (LB.LinComb L φ δ) ψ ε) :=
  ⟨fun j => res (nest_le L φ δ ψ j) (t.s fun p => j p.1 p.2)⟩

theorem trF_flat (r : Z ⟶ Y) (z : Z) (j j' : K → I → L.ι) :
    trF (L := L) (flatφ φ ψ) (flatε δ ε) r z (fun p => j p.1 p.2) (fun p => j' p.1 p.2) =
      ∏ k, trF (L := L) φ δ (r ≫ ψ k) z (j k) (j' k) ^ ε k := by
  rw [trF, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [trF, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun i _ => ?_
  show gm (r ≫ ψ k ≫ φ i) z _ (L.g (j k i) (j' k i)) ^ (ε k * δ i) = _
  rw [mul_comm (ε k), zpow_mul, Category.assoc]

variable {L φ δ ψ ε}

theorem nest_isGen {t : LB.Gen (LB.LinComb L (flatφ φ ψ) (flatε δ ε))} (ht : t.IsGen) :
    (nest L φ δ ψ ε t).IsGen := fun j j' => unit_ext fun y hy => by
  have hj : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart (LB.LinComb L φ δ) ψ j := hy.1
  have hj' : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart (LB.LinComb L φ δ) ψ j' := hy.2
  refine (gm_res _ y _ hy _).trans ((gm_res _ y _ hj _).trans ?_)
  refine (gen_trans ht (𝟙 Y) y (nest_le L φ δ ψ j hj) (nest_le L φ δ ψ j' hj')).trans ?_
  refine Eq.trans ?_ (map_mul _ _ _).symm
  refine congrArg₂ (· * ·) ?_ ((gm_res _ y _ hj' _).symm.trans (gm_res _ y _ hy _).symm)
  refine (trF_flat L φ δ ψ ε (𝟙 Y) y j j').trans (Eq.symm ?_)
  refine (gm_linComb _ ψ ε (𝟙 Y) y j j' hj hj').trans (Finset.prod_congr rfl fun k _ => ?_)
  exact congrArg (· ^ ε k) (gm_linComb L φ δ (𝟙 Y ≫ ψ k) y (j k) (j' k) (Set.mem_iInter.1 hj k)
    (Set.mem_iInter.1 hj' k))

def adj (φ : I → (W ⟶ X)) (δ : I → ℤ) (z : Z) (JP : (Z ⟶ W) → I → L.ι) (J : (Z ⟶ X) → L.ι) (χ : Z ⟶ W) :
    (Z.presheaf.stalk z)ˣ :=
  trF (L := L) φ δ χ z (JP χ) (fun i => J (χ ≫ φ i))

theorem val_nest {t : LB.Gen (LB.LinComb L (flatφ φ ψ) (flatε δ ε))} (ht : t.IsGen) (r : Z ⟶ Y) {z : Z}
    {JP : (Z ⟶ W) → I → L.ι} (hJP : Good (LB.LinComb L φ δ) z JP) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    val (L := LB.LinComb L φ δ) (nest L φ δ ψ ε t) r z JP =
      (∏ k, adj φ δ z JP J (r ≫ ψ k) ^ ε k) * val (L := L) t r z J := by
  have hm := hJP.mem ψ r
  have e₁ : val (L := LB.LinComb L φ δ) (nest L φ δ ψ ε t) r z JP =
      gm r z (LB.wchart L (flatφ φ ψ) fun p => JP (r ≫ ψ p.1) p.2) (t.s fun p => JP (r ≫ ψ p.1) p.2) :=
    gm_res r z _ hm _
  have e₂ := val_of t r z J (fun p => J ((r ≫ ψ p.1) ≫ φ p.2)) (fun p => by rw [Category.assoc])
  have m₂ : r z ∈ LB.wchart L (flatφ φ ψ) (fun p => J ((r ≫ ψ p.1) ≫ φ p.2)) := by
    have := hJ.mem (flatφ φ ψ) r
    simpa only [Category.assoc] using this
  rw [e₂]
  refine e₁.trans ((gen_trans ht r z (nest_le L φ δ ψ _ hm) m₂).trans ?_)
  exact congrArg (· * _) (trF_flat L φ δ ψ ε r z (fun k => JP (r ≫ ψ k)) (fun k i => J ((r ≫ ψ k) ≫ φ i)))

end Nest

section Group

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

variable (G) in

abbrev lamφ : ULift.{0} (Finset (Fin 2)) → ((G2 G).left ⟶ G.left) := fun I => (psum G (x2 G) I.down).left

abbrev lamε : ULift.{0} (Finset (Fin 2)) → ℤ := fun I => (-1) ^ (2 - I.down.card)

theorem prod_lam {T : Over S} (x y : T ⟶ G) {U : Type} [CommGroup U] (h : (T.left ⟶ G.left) → U) :
    ∏ I, h ((lift x y).left ≫ lamφ G I) ^ lamε I =
      h (x * y).left * (h x.left)⁻¹ * (h y.left)⁻¹ * h (1 : T ⟶ G).left := by
  have e : ∀ I : ULift.{0} (Finset (Fin 2)), (lift x y).left ≫ lamφ G I = (psum G ![x, y] I.down).left := fun I =>
    congrArg (fun q => q.left) ((psum_hom (preHom (lift x y)) (x2 G) I.down).trans
      (congrArg (fun q => psum G q I.down) (funext fun i => by fin_cases i <;> simp [preHom, x2])))
  refine (Fintype.prod_equiv (Equiv.ulift : ULift.{0} (Finset (Fin 2)) ≃ Finset (Fin 2)) _
    (fun I => h (psum G ![x, y] I).left ^ ((-1 : ℤ) ^ (2 - I.card)))
    (fun I => congrArg (fun q => h q ^ lamε I) (e I))).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  have p₀ : psum G ![x, y] ∅ = 1 := rfl
  have p₁ : psum G ![x, y] {0} = x := _root_.mul_one x
  have p₂ : psum G ![x, y] {1} = y := _root_.mul_one y
  have p₃ : psum G ![x, y] {0, 1} = x * y := congrArg (x * ·) (_root_.mul_one y)
  rw [p₀, p₁, p₂, p₃]
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : ∀ i : Fin 2, (-1 : ℤ) ^ (2 - ({i} : Finset (Fin 2)).card) = -1 := by decide
  have q₃ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [q₀, q₁, q₁, q₃]
  simp only [zpow_neg, zpow_one]
  ac_rfl

theorem prod_law₁ {T : Over S} (a b c : T ⟶ G) {U : Type} [CommGroup U] (h : (T.left ⟶ (G2 G).left) → U) :
    ∏ k, h ((lift a (lift b c)).left ≫ law1φ G (x3 G 0) (x3 G 1) (x3 G 2) k) ^ lawε k =
      h (lift (a * b) c).left * (h (lift a c).left)⁻¹ * (h (lift b c).left)⁻¹ := by
  have r₀ : lift a (lift b c) ≫ x3 G 0 = a := by simp [x3]
  have r₁ : lift a (lift b c) ≫ x3 G 1 = b := by simp [x3]
  have r₂ : lift a (lift b c) ≫ x3 G 2 = c := by simp [x3]
  have s : lift a (lift b c) ≫ padd G (x3 G 0) (x3 G 1) = a * b := (MonObj.comp_mul _ _ _).trans (by rw [r₀, r₁])
  refine (Fintype.prod_equiv Equiv.ulift _ (fun i : Fin 3 => h ((lift a (lift b c)).left ≫
    law1φ G (x3 G 0) (x3 G 1) (x3 G 2) ⟨i⟩) ^ lawε ⟨i⟩) (fun _ => rfl)).trans ?_
  rw [Fin.prod_univ_three]
  show h (lift a (lift b c) ≫ lift (padd G (x3 G 0) (x3 G 1)) (x3 G 2)).left ^ (1 : ℤ) *
    h (lift a (lift b c) ≫ lift (x3 G 0) (x3 G 2)).left ^ (-1 : ℤ) *
    h (lift a (lift b c) ≫ lift (x3 G 1) (x3 G 2)).left ^ (-1 : ℤ) = _
  rw [comp_lift, comp_lift, comp_lift, s, r₀, r₁, r₂]
  simp only [zpow_neg, zpow_one]

theorem prod_law₂ {T : Over S} (a b c : T ⟶ G) {U : Type} [CommGroup U] (h : (T.left ⟶ (G2 G).left) → U) :
    ∏ k, h ((lift a (lift b c)).left ≫ law2φ G (x3 G 0) (x3 G 1) (x3 G 2) k) ^ lawε k =
      h (lift a (b * c)).left * (h (lift a b).left)⁻¹ * (h (lift a c).left)⁻¹ := by
  have r₀ : lift a (lift b c) ≫ x3 G 0 = a := by simp [x3]
  have r₁ : lift a (lift b c) ≫ x3 G 1 = b := by simp [x3]
  have r₂ : lift a (lift b c) ≫ x3 G 2 = c := by simp [x3]
  have s : lift a (lift b c) ≫ padd G (x3 G 1) (x3 G 2) = b * c := (MonObj.comp_mul _ _ _).trans (by rw [r₁, r₂])
  refine (Fintype.prod_equiv Equiv.ulift _ (fun i : Fin 3 => h ((lift a (lift b c)).left ≫
    law2φ G (x3 G 0) (x3 G 1) (x3 G 2) ⟨i⟩) ^ lawε ⟨i⟩) (fun _ => rfl)).trans ?_
  rw [Fin.prod_univ_three]
  show h (lift a (lift b c) ≫ lift (x3 G 0) (padd G (x3 G 1) (x3 G 2))).left ^ (1 : ℤ) *
    h (lift a (lift b c) ≫ lift (x3 G 0) (x3 G 1)).left ^ (-1 : ℤ) *
    h (lift a (lift b c) ≫ lift (x3 G 0) (x3 G 2)).left ^ (-1 : ℤ) = _
  rw [comp_lift, comp_lift, comp_lift, s, r₀, r₁, r₂]
  simp only [zpow_neg, zpow_one]

theorem id₃ : lift (x3 G 0) (lift (x3 G 1) (x3 G 2)) = 𝟙 (G3 G) := by
  ext <;> simp [x3]

theorem prod_flat {Y W X : Scheme.{0}} {K I : Type} [Fintype K] [Fintype I] (ψ : K → (Y ⟶ W)) (ε : K → ℤ)
    (φ : I → (W ⟶ X)) (δ : I → ℤ) {U : Type} [CommGroup U] (h : (Y ⟶ X) → U) :
    ∏ p, h (flatφ φ ψ p) ^ flatε δ ε p = ∏ k, (∏ i, h (ψ k ≫ φ i) ^ δ i) ^ ε k := by
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun i _ => ?_
  show h (ψ k ≫ φ i) ^ (ε k * δ i) = _
  rw [mul_comm (ε k), zpow_mul]

theorem formEq₁ : FormEq (thφ G (x3 G)) thε
    (flatφ (lamφ G) (law1φ G (x3 G 0) (x3 G 1) (x3 G 2))) (flatε lamε lawε) := fun U _ h => by
  have a := prod_cub (x3 G 0) (x3 G 1) (x3 G 2) h
  rw [id₃] at a
  simp only [Over.id_left, Category.id_comp] at a
  have b := prod_law₁ (x3 G 0) (x3 G 1) (x3 G 2) (fun χ => ∏ i, h (χ ≫ lamφ G i) ^ lamε i)
  rw [id₃] at b
  simp only [Over.id_left, Category.id_comp, prod_lam] at b
  rw [a, prod_flat, b]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem formEq₂ : FormEq (thφ G (x3 G)) thε
    (flatφ (lamφ G) (law2φ G (x3 G 0) (x3 G 1) (x3 G 2))) (flatε lamε lawε) := fun U _ h => by
  have a := prod_cub (x3 G 0) (x3 G 1) (x3 G 2) h
  rw [id₃] at a
  simp only [Over.id_left, Category.id_comp] at a
  have b := prod_law₂ (x3 G 0) (x3 G 1) (x3 G 2) (fun χ => ∏ i, h (χ ≫ lamφ G i) ^ lamε i)
  rw [id₃] at b
  simp only [Over.id_left, Category.id_comp, prod_lam] at b
  rw [a, prod_flat, b, _root_.mul_assoc (x3 G 0)]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

abbrev lamLB (L : RigLB G) : LB (G2 G).left := LB.LinComb L.L (lamφ G) lamε

theorem nest_isCube (L : RigLB G) (c : CubicalStr G L) (ψ : ULift.{0} (Fin 3) → ((G3 G).left ⟶ (G2 G).left))
    (t : LB.Gen (LB.LinComb L.L (flatφ (lamφ G) ψ) (flatε lamε lawε)))
    (v : LB.Gen.Corr L.L _ _ (thφ G (x3 G)) thε t c.t) :
    GlobalTheory.BiextSignTwist.LawIsCube G L c ψ (nest L.L (lamφ G) lamε ψ lawε t) := fun J j h₁ h₂ h₃ =>
  unit_ext fun y hy => by
    have e := v (fun p => J p.1 p.2) j (fun a b q => h₁ _ _ _ _ q) h₂ (fun a b q => h₃ _ _ _ q)
    have hm := nest_le L.L (lamφ G) lamε ψ J hy.1
    have hy' : (𝟙 _ : (G3 G).left ⟶ _) y ∈ LB.wchart L.L (flatφ (lamφ G) ψ) (fun p => J p.1 p.2) ⊓
        LB.wchart L.L (thφ G (x3 G)) j := ⟨hm, hy.2⟩
    refine (gm_res _ y _ hy _).trans ((gm_res _ y _ hy.1 _).trans ?_)
    refine Eq.trans ?_ (gm_res _ y _ hy _).symm
    exact (gm_res _ y _ hy' _).symm.trans ((congrArg (gm _ y _) e).trans (gm_res _ y _ hy' _))

theorem exists_laws (L : RigLB G) (c : CubicalStr G L) :
    ∃ (l₁ : LB.Gen (LB.LinComb (lamLB L) (law1φ G (x3 G 0) (x3 G 1) (x3 G 2)) lawε))
      (l₂ : LB.Gen (LB.LinComb (lamLB L) (law2φ G (x3 G 0) (x3 G 1) (x3 G 2)) lawε)), l₁.IsGen ∧ l₂.IsGen ∧
      GlobalTheory.BiextSignTwist.LawIsCube G L c _ l₁ ∧ GlobalTheory.BiextSignTwist.LawIsCube G L c _ l₂ ∧
      ∀ {T : Over S} (y : T.left) (JP : (T.left ⟶ (G2 G).left) → ULift.{0} (Finset (Fin 2)) → L.L.ι)
        (_ : Good (lamLB L) y JP) (J : (T.left ⟶ G.left) → L.L.ι) (_ : Good L.L y J),
        (∀ a b d : T ⟶ G, val (L := lamLB L) l₁ (lift a (lift b d)).left y JP =
          adj (lamφ G) lamε y JP J (lift (a * b) d).left * (adj (lamφ G) lamε y JP J (lift a d).left)⁻¹ *
            (adj (lamφ G) lamε y JP J (lift b d).left)⁻¹ * cubV c y J a b d) ∧
        (∀ a b d : T ⟶ G, val (L := lamLB L) l₂ (lift a (lift b d)).left y JP =
          adj (lamφ G) lamε y JP J (lift a (b * d)).left * (adj (lamφ G) lamε y JP J (lift a b).left)⁻¹ *
            (adj (lamφ G) lamε y JP J (lift a d).left)⁻¹ * cubV c y J a b d) := by
  obtain ⟨t₁, g₁, v₁⟩ := exists_gen L.isLB (φ := thφ G (x3 G)) (ε := thε) formEq₁ c.t c.isGen
  obtain ⟨t₂, g₂, v₂⟩ := exists_gen L.isLB (φ := thφ G (x3 G)) (ε := thε) formEq₂ c.t c.isGen
  refine ⟨nest L.L _ _ _ _ t₁, nest L.L _ _ _ _ t₂, nest_isGen g₁, nest_isGen g₂,
    nest_isCube L c _ t₁ (corr_of_val L.isLB fun y J hJ => v₁ _ _ y J hJ),
    nest_isCube L c _ t₂ (corr_of_val L.isLB fun y J hJ => v₂ _ _ y J hJ),
    fun y JP hJP J hJ => ⟨fun a b d => ?_, fun a b d => ?_⟩⟩
  · rw [val_nest g₁ _ hJP hJ, prod_law₁ a b d (adj (lamφ G) lamε y JP J), v₁ _ _ y J hJ]
    rfl
  · rw [val_nest g₂ _ hJP hJ, prod_law₂ a b d (adj (lamφ G) lamε y JP J), v₂ _ _ y J hJ]
    rfl

end Group

end GlobalTheory.LamBiext
