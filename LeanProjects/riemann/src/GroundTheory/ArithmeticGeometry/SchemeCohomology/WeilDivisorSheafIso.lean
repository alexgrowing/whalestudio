import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.WeilDivisorSheaf

namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

variable {X : Scheme.{u}}

section Mul

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]

lemma mul_mem_divisorSections {D E : WeilDivisor X} (c : (X.functionField)ˣ)
    (hc : ∀ Z : PrimeDivisor X, D Z - E Z ≤ Z.ord (c : X.functionField)) {V : X.Opens}
    {f : V → X.functionField} (hf : f ∈ divisorSections D V) :
    (fun y => f y * (c : X.functionField)) ∈ divisorSections E V := by
  refine ⟨fun y => ?_, fun y hy => ?_⟩
  · obtain ⟨W, hyW, h⟩ := hf.1 y
    exact ⟨W, hyW, fun z hz => by simp only [h z hz]⟩
  · set Z := PrimeDivisor.ofPoint y.1 hy
    by_cases hfy : f y = 0
    · simp [hfy]
    · have h1 := hf.2 y hy
      change Z.valuation (f y) ≤ WithZero.exp (D Z) at h1
      change Z.valuation (f y * c) ≤ WithZero.exp (E Z)
      rw [Z.valuation_le_exp_iff hfy] at h1
      rw [Z.valuation_le_exp_iff (mul_ne_zero hfy (Units.ne_zero c)),
        Z.ord_mul hfy (Units.ne_zero c)]
      have := hc Z
      omega

noncomputable def divisorMulPresheaf {D E : WeilDivisor X} (c : (X.functionField)ˣ)
    (hc : ∀ Z : PrimeDivisor X, D Z - E Z ≤ Z.ord (c : X.functionField)) :
    divisorPresheaf D ⟶ divisorPresheaf E where
  app _ := AddCommGrpCat.ofHom
    { toFun := fun f => ⟨fun y => f.1 y * c, mul_mem_divisorSections c hc f.2⟩
      map_zero' := Subtype.ext (funext fun _ => zero_mul _)
      map_add' := fun _ _ => Subtype.ext (funext fun _ => add_mul _ _ _) }
  naturality _ _ _ := rfl

noncomputable def divisorMul {D E : WeilDivisor X} (c : (X.functionField)ˣ)
    (hc : ∀ Z : PrimeDivisor X, D Z - E Z ≤ Z.ord (c : X.functionField)) :
    divisorSheaf D ⟶ divisorSheaf E :=
  ⟨PresheafOfModules.homMk (divisorMulPresheaf c hc) (fun _ _ _ =>
    Subtype.ext (funext fun _ => mul_assoc _ _ _))⟩

end Mul

section MulIso

variable [IsIntegral X] [IsNoetherian X] [IsNormalScheme X]

noncomputable def divisorMulIso {D E : WeilDivisor X} (c : (X.functionField)ˣ)
    (hc : D - E = principalDivisor (Additive.ofMul c)) : divisorSheaf D ≅ divisorSheaf E where
  hom := divisorMul c (fun Z => by
    have := congrArg (fun F : WeilDivisor X => F Z) hc
    simp only [Finsupp.coe_sub, Pi.sub_apply, principalDivisor_apply] at this
    omega)
  inv := divisorMul c⁻¹ (fun Z => by
    have := congrArg (fun F : WeilDivisor X => F Z) hc
    simp only [Finsupp.coe_sub, Pi.sub_apply, principalDivisor_apply] at this
    have h := Z.ord_mul (Units.ne_zero c) (Units.ne_zero c⁻¹)
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, PrimeDivisor.ord_one] at h
    omega)
  hom_inv_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    ext f
    apply Subtype.ext
    funext y
    change f.1 y * c * ((c⁻¹ : (X.functionField)ˣ) : X.functionField) = f.1 y
    rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    ext f
    apply Subtype.ext
    funext y
    change f.1 y * ((c⁻¹ : (X.functionField)ˣ) : X.functionField) * c = f.1 y
    rw [mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]

end MulIso

section Basis

variable [IsIntegral X] [IsNoetherian X] [IsLocallyFactorial X]

noncomputable def localBasis (D : WeilDivisor X) (U : X.Opens) (g : (X.functionField)ˣ)
    (hg : ∀ Z : PrimeDivisor X, Z.point ∈ U → Z.ord (g : X.functionField) = D Z) :
    divisorSections D U :=
  ⟨fun _ => ((g⁻¹ : (X.functionField)ˣ) : X.functionField), by
    refine ⟨fun y => ⟨⊤, trivial, fun _ _ => rfl⟩, fun y hy => ?_⟩
    rw [PrimeDivisor.valuation_le_exp_iff _ (Units.ne_zero _)]
    have h1 := PrimeDivisor.ord_mul (PrimeDivisor.ofPoint y.1 hy) (Units.ne_zero g)
      (Units.ne_zero g⁻¹)
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, PrimeDivisor.ord_one,
      hg (PrimeDivisor.ofPoint y.1 hy) y.2] at h1
    dsimp only
    omega⟩

theorem localBasis_bijective (D : WeilDivisor X) (U : X.Opens) (g : (X.functionField)ˣ)
    (hg : ∀ Z : PrimeDivisor X, Z.point ∈ U → Z.ord (g : X.functionField) = D Z)
    (V : X.Opens) (hVU : V ≤ U) :
    Function.Bijective (fun r : Γ(X, V) => r • divisorSectionsRes D hVU (localBasis D U g hg)) := by
  by_cases hne : Nonempty V
  · constructor
    · intro r₁ r₂ h12
      obtain ⟨y⟩ := hne
      have : Nonempty V := ⟨y⟩
      have := congrArg (fun t : divisorSections D V => t.1 y) h12
      have h := mul_right_cancel₀ (Units.ne_zero g⁻¹) this
      rw [sectionValue_eq V y r₁, sectionValue_eq V y r₂] at h
      exact Scheme.germToFunctionField_injective X V h
    · intro t
      obtain ⟨y0⟩ := hne
      have : Nonempty V := ⟨y0⟩
      set c := t.1 y0
      have hord : ∀ Z : PrimeDivisor X, Z.point ∈ V →
          0 ≤ Z.ord (c * (g : X.functionField)) := by
        intro Z hZ
        by_cases hc : c = 0
        · rw [hc, zero_mul, PrimeDivisor.ord_zero]
        · rw [PrimeDivisor.ord_mul Z hc (Units.ne_zero g), hg Z (hVU hZ)]
          have ht := t.2.2 ⟨Z.point, hZ⟩ Z.2
          have hcZ : t.1 ⟨Z.point, hZ⟩ = c := divisorSections_apply_eq D t _ y0
          rw [hcZ] at ht
          have := (PrimeDivisor.valuation_le_exp_iff Z hc (D Z)).mp ht
          omega
      obtain ⟨r, hr⟩ := exists_section_of_ord_nonneg V _ hord
      refine ⟨r, Subtype.ext (funext fun y => ?_)⟩
      rw [divisorSections_smul_apply, sectionValue_eq, hr, divisorSections_apply_eq D t y y0]
      change c * (g : X.functionField) * ((g⁻¹ : (X.functionField)ˣ) : X.functionField) = c
      rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  · have hV : V = ⊥ := by
      ext y
      simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hy => hne ⟨⟨y, hy⟩⟩
    have : Subsingleton Γ(X, V) :=
      CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hV)
    refine ⟨fun _ _ _ => Subsingleton.elim _ _, fun t => ⟨0, Subtype.ext (funext fun y => ?_)⟩⟩
    exact (hne ⟨y⟩).elim

noncomputable def divisorSectionsOne (V : X.Opens) : divisorSections (0 : WeilDivisor X) V :=
  divisorSectionsRes 0 le_top (localBasis 0 ⊤ 1 (fun Z _ => by simp [PrimeDivisor.ord_one]))

noncomputable def unitToDivisorZero (V : (Opens X)ᵒᵖ) :
    (X.ringCatSheaf.obj.obj V) →ₗ[X.ringCatSheaf.obj.obj V]
      ((divisorPresheaf (0 : WeilDivisor X)).obj V) :=
  LinearMap.toSpanSingleton _ _ (divisorSectionsOne V.unop)

lemma unitToDivisorZero_bijective (V : (Opens X)ᵒᵖ) :
    Function.Bijective (unitToDivisorZero (X := X) V) :=
  localBasis_bijective 0 ⊤ 1 (fun Z _ => by simp [PrimeDivisor.ord_one]) V.unop le_top

noncomputable def divisorSheafZeroIso :
    SheafOfModules.unit X.ringCatSheaf ≅ divisorSheaf (0 : WeilDivisor X) :=
  (SheafOfModules.fullyFaithfulForget X.ringCatSheaf).preimageIso
    (PresheafOfModules.isoMk
      (fun V => (LinearEquiv.ofBijective (unitToDivisorZero V)
        (unitToDivisorZero_bijective V)).toModuleIso)
      (fun V W i => by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro r
        apply Subtype.ext
        funext y
        change sectionValue W.unop y (X.presheaf.map i r) * 1 =
          sectionValue V.unop ⟨y.1, i.unop.le y.2⟩ r * 1
        exact congrArg (· * 1) (sectionValue_res i.unop.le y (show Γ(X, V.unop) from r))))

end Basis

section Hom

variable [IsIntegral X] [IsNoetherian X] [IsLocallyFactorial X]

theorem divisorSheaf_hom_eq_mul {D E : WeilDivisor X} (φ : divisorSheaf D ⟶ divisorSheaf E) :
    ∃ c : X.functionField, ∀ (V : (Opens X)ᵒᵖ) (f : divisorSections D V.unop) (y : V.unop),
      ((φ.val.app V).hom f : divisorSections E V.unop).1 y = f.1 y * c := by
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨U, g, hxU, hg⟩ := WeilDivisor.exists_local_equation D x
  have hg' : ∀ Z : PrimeDivisor X, Z.point ∈ U → Z.ord (g : X.functionField) = D Z :=
    fun Z hZ => (principalDivisor_apply g Z).symm.trans (hg Z hZ)
  set s := localBasis D U g hg'
  set t : divisorSections E U := (φ.val.app (op U)).hom s
  refine ⟨t.1 ⟨x, hxU⟩ * g, fun V f y => ?_⟩
  obtain ⟨w, hwV, hwU⟩ := nonempty_preirreducible_inter V.unop.isOpen U.isOpen ⟨y.1, y.2⟩ ⟨x, hxU⟩
  set W : X.Opens := V.unop ⊓ U
  have hWU : W ≤ U := inf_le_right
  have hWV : W ≤ V.unop := inf_le_left
  obtain ⟨r, hr⟩ := (localBasis_bijective D U g hg' W hWU).2
    (divisorSectionsRes D hWV f)
  have hnat := PresheafOfModules.naturality_apply φ.val (homOfLE hWV).op f
  have hnat' := PresheafOfModules.naturality_apply φ.val (homOfLE hWU).op s
  have hw : w ∈ W := ⟨hwV, hwU⟩
  have key : ((φ.val.app V).hom f : divisorSections E V.unop).1 ⟨w, hwV⟩ =
      f.1 ⟨w, hwV⟩ * (t.1 ⟨x, hxU⟩ * g) := by
    have e1 := congrArg (fun m : divisorSections E W => m.1 ⟨w, hw⟩) hnat
    have e2 := congrArg (fun m : divisorSections D W => m.1 ⟨w, hw⟩) hr
    change ((φ.val.app (op W)).hom (divisorSectionsRes D hWV f)).1 ⟨w, hw⟩ =
      ((φ.val.app V).hom f).1 ⟨w, hwV⟩ at e1
    change sectionValue W ⟨w, hw⟩ r * ((g⁻¹ : (X.functionField)ˣ) : X.functionField) =
      f.1 ⟨w, hwV⟩ at e2
    have e3 := congrArg (fun m : divisorSections E W => m.1 ⟨w, hw⟩) hnat'
    change ((φ.val.app (op W)).hom (divisorSectionsRes D hWU s)).1 ⟨w, hw⟩ = t.1 ⟨w, hwU⟩ at e3
    have hr' : r • divisorSectionsRes D hWU s = divisorSectionsRes D hWV f := hr
    let ψ : divisorSections D W → divisorSections E W := fun m => (φ.val.app (op W)).hom m
    have hlin : ψ (r • divisorSectionsRes D hWU s) = r • ψ (divisorSectionsRes D hWU s) :=
      (φ.val.app (op W)).hom.map_smul r _
    have hg0 : (g : X.functionField) ≠ 0 := g.ne_zero
    calc ((φ.val.app V).hom f : divisorSections E V.unop).1 ⟨w, hwV⟩
        = ((φ.val.app (op W)).hom (divisorSectionsRes D hWV f) : divisorSections E W).1
            ⟨w, hw⟩ := e1.symm
      _ = (ψ (r • divisorSectionsRes D hWU s)).1 ⟨w, hw⟩ := by rw [hr']
      _ = (r • ψ (divisorSectionsRes D hWU s)).1 ⟨w, hw⟩ := by rw [hlin]
      _ = sectionValue W ⟨w, hw⟩ r * t.1 ⟨w, hwU⟩ := by
            rw [divisorSections_smul_apply, e3]
      _ = sectionValue W ⟨w, hw⟩ r * t.1 ⟨x, hxU⟩ := by
            rw [divisorSections_apply_eq E t ⟨w, hwU⟩ ⟨x, hxU⟩]
      _ = f.1 ⟨w, hwV⟩ * (t.1 ⟨x, hxU⟩ * g) := by
            rw [← e2, Units.val_inv_eq_inv_val]
            field_simp
  have h1 := divisorSections_apply_eq E ((φ.val.app V).hom f : divisorSections E V.unop) y
    ⟨w, hwV⟩
  rw [h1, key, divisorSections_apply_eq D f ⟨w, hwV⟩ y]

end Hom

section Iso

variable [IsIntegral X] [IsNoetherian X] [IsLocallyFactorial X]

lemma neg_le_ord_of_mem (D : WeilDivisor X) {U : X.Opens} (m : divisorSections D U)
    (Z : PrimeDivisor X) (hZ : Z.point ∈ U) (hm : m.1 ⟨Z.point, hZ⟩ ≠ 0) :
    -D Z ≤ Z.ord (m.1 ⟨Z.point, hZ⟩) :=
  (Z.valuation_le_exp_iff hm (D Z)).mp (m.2.2 ⟨Z.point, hZ⟩ Z.2)

lemma ord_inv_units (Z : PrimeDivisor X) (g : (X.functionField)ˣ) :
    Z.ord ((g⁻¹ : (X.functionField)ˣ) : X.functionField) = - Z.ord (g : X.functionField) := by
  have h := Z.ord_mul (Units.ne_zero g) (Units.ne_zero g⁻¹)
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one, PrimeDivisor.ord_one] at h
  omega

lemma sub_le_ord_of_hom {D E : WeilDivisor X} (φ : divisorSheaf D ⟶ divisorSheaf E)
    {c : X.functionField} (hc0 : c ≠ 0)
    (hc : ∀ (V : (Opens X)ᵒᵖ) (f : divisorSections D V.unop) (y : V.unop),
      ((φ.val.app V).hom f : divisorSections E V.unop).1 y = f.1 y * c)
    (Z : PrimeDivisor X) : D Z - E Z ≤ Z.ord c := by
  obtain ⟨U, g, hZU, hg⟩ := WeilDivisor.exists_local_equation D Z.point
  have hg' : ∀ Z : PrimeDivisor X, Z.point ∈ U → Z.ord (g : X.functionField) = D Z :=
    fun Z hZ => (principalDivisor_apply g Z).symm.trans (hg Z hZ)
  set s := localBasis D U g hg'
  let m : divisorSections E U := (φ.val.app (op U)).hom s
  have hval : m.1 ⟨Z.point, hZU⟩ = s.1 ⟨Z.point, hZU⟩ * c := hc (op U) s ⟨Z.point, hZU⟩
  have hs0 : s.1 ⟨Z.point, hZU⟩ ≠ 0 := Units.ne_zero g⁻¹
  have hne : m.1 ⟨Z.point, hZU⟩ ≠ 0 := by
    rw [hval]
    exact mul_ne_zero hs0 hc0
  have h := neg_le_ord_of_mem E m Z hZU hne
  rw [hval] at h
  change -E Z ≤ Z.ord (((g⁻¹ : (X.functionField)ˣ) : X.functionField) * c) at h
  rw [Z.ord_mul (Units.ne_zero _) hc0, ord_inv_units, hg' Z hZU] at h
  omega

theorem exists_principal_of_iso {D E : WeilDivisor X} (e : divisorSheaf D ≅ divisorSheaf E) :
    ∃ c : (X.functionField)ˣ, D - E = principalDivisor (Additive.ofMul c) := by
  obtain ⟨c, hc⟩ := divisorSheaf_hom_eq_mul e.hom
  obtain ⟨c', hc'⟩ := divisorSheaf_hom_eq_mul e.inv
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨U, g, hxU, hg⟩ := WeilDivisor.exists_local_equation D x
  have hg' : ∀ Z : PrimeDivisor X, Z.point ∈ U → Z.ord (g : X.functionField) = D Z :=
    fun Z hZ => (principalDivisor_apply g Z).symm.trans (hg Z hZ)
  set s := localBasis D U g hg'
  have hid := congrArg (fun φ : divisorSheaf D ⟶ divisorSheaf D =>
    ((φ.val.app (op U)).hom s : divisorSections D U).1 ⟨x, hxU⟩) e.hom_inv_id
  have e1 := hc' (op U) ((e.hom.val.app (op U)).hom s) ⟨x, hxU⟩
  have e2 := hc (op U) s ⟨x, hxU⟩
  have hid' : s.1 ⟨x, hxU⟩ * c * c' = s.1 ⟨x, hxU⟩ := by
    rw [← e2]
    exact e1.symm.trans hid
  have hcc' : c * c' = 1 := by
    have hs0 : s.1 ⟨x, hxU⟩ ≠ 0 := Units.ne_zero g⁻¹
    rw [mul_assoc] at hid'
    exact (mul_right_eq_self₀.mp hid').resolve_right hs0
  have hc0 : c ≠ 0 := left_ne_zero_of_mul_eq_one hcc'
  have hc'0 : c' ≠ 0 := right_ne_zero_of_mul_eq_one hcc'
  refine ⟨Units.mk c c' hcc' (by rw [mul_comm]; exact hcc'), ?_⟩
  ext Z
  simp only [Finsupp.coe_sub, Pi.sub_apply, principalDivisor_apply]
  have h1 := sub_le_ord_of_hom e.hom hc0 hc Z
  have h2 := sub_le_ord_of_hom e.inv hc'0 hc' Z
  have h3 := Z.ord_mul hc0 hc'0
  rw [hcc', PrimeDivisor.ord_one] at h3
  omega

theorem nonempty_divisorSheaf_iso_iff (D E : WeilDivisor X) :
    Nonempty (divisorSheaf D ≅ divisorSheaf E) ↔ D - E ∈ principalDivisors X := by
  constructor
  · rintro ⟨e⟩
    obtain ⟨c, hc⟩ := exists_principal_of_iso e
    exact ⟨Additive.ofMul c, hc.symm⟩
  · rintro ⟨a, ha⟩
    exact ⟨divisorMulIso (Additive.toMul a) ha.symm⟩

end Iso

end GroundTheory.Arith.SchemeCoh
