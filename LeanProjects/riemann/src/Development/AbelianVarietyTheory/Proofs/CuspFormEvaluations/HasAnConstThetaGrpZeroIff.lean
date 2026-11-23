import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsUniqueSecIsFnAt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertTrivialOfNowhereVanishing

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.ThetaFn

open CubeValues SymmetricSemicharacter AppellHumbertTrivial

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
  {T : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ T)

theorem exAt_mem_twist_chart_iff {m : T ⊗ A ⟶ A} {z w : Fin g → ℂ}
    (hw : exAt u p z ≫ m.left = (u.ex w).left) (j : Fin 2 → L.ι) :
    ⊤ ≤ exAt u p z ⁻¹ᵁ LB.wchart L ![(snd T A).left, m.left] j ↔
      ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j 0) ∧ ⊤ ≤ (u.ex w).left ⁻¹ᵁ L.U (j 1) := by
  have h0 : exAt u p z ≫ (snd T A).left = (u.ex z).left := by
    unfold exAt
    rw [← Over.comp_left, lift_snd]
  rw [← h0, ← hw]
  constructor
  · intro h
    refine ⟨fun a _ => ?_, fun a _ => ?_⟩
    · have ha := Set.mem_iInter.1 (h (show a ∈ (⊤ : (Sp ℂ).Opens) from trivial)) 0
      simpa using ha
    · have ha := Set.mem_iInter.1 (h (show a ∈ (⊤ : (Sp ℂ).Opens) from trivial)) 1
      simpa using ha
  · rintro ⟨h0', h1'⟩ a _
    refine Set.mem_iInter.2 (fun k => ?_)
    fin_cases k
    · simpa using h0' (show a ∈ (⊤ : (Sp ℂ).Opens) from trivial)
    · simpa using h1' (show a ∈ (⊤ : (Sp ℂ).Opens) from trivial)

private theorem exists_algChart_mem_source (hL : L.IsLB) (f : Sp ℂ ⟶ A.left) : ∃ i, ⊤ ≤ f ⁻¹ᵁ L.U i := by
  obtain ⟨cover, -, -⟩ := hL
  obtain ⟨a0⟩ : Nonempty (PrimeSpectrum ℂ) := inferInstance
  have hmem : f.base a0 ∈ (⨆ i, L.U i) := by
    rw [cover]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hmem
  refine ⟨i, fun a _ => ?_⟩
  have hsub : a = a0 := Subsingleton.elim (α := PrimeSpectrum ℂ) a a0
  rw [hsub]
  exact hi

private theorem valAt'_unit_ne_zero_cusp_form_evaluations {X : Scheme.{0}} (y : Sp ℂ ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ y ⁻¹ᵁ U) (f : Γ(X, U)ˣ) : valAt' y U f.val ≠ 0 := by
  unfold valAt'
  rw [dif_pos h]
  unfold valAt
  exact (Units.map ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (y.appLE U ⊤ h).hom).toMonoidHom f).ne_zero

private theorem valAt'_mul_of_top_le_preimage_open {X : Scheme.{0}} (y : Sp ℂ ⟶ X) (U : X.Opens) (a b : Γ(X, U)) :
    valAt' y U (a * b) = valAt' y U a * valAt' y U b := by
  unfold valAt'
  split_ifs with h
  · unfold valAt
    simp only [map_mul]
  · simp

private theorem valAt'_resG {X : Scheme.{0}} (y : Sp ℂ ⟶ X) {U V : X.Opens} (hVU : V ≤ U)
    (h : ⊤ ≤ y ⁻¹ᵁ V) (f : Γ(X, U)) :
    valAt' y V (X.presheaf.map (homOfLE hVU).op f) = valAt' y U f := by
  have h' : ⊤ ≤ y ⁻¹ᵁ U := fun a ha => hVU (h ha)
  unfold valAt'
  rw [dif_pos h, dif_pos h']
  unfold valAt
  exact congrArg (fun F => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (F.hom f))
    (Scheme.Hom.map_appLE y h (homOfLE hVU).op)

private theorem valAt'_app_eq_valAt'_comp {X Y : Scheme.{0}} (y : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens)
    (f : Γ(Y, U)) : valAt' y (φ ⁻¹ᵁ U) (φ.app U f) = valAt' (y ≫ φ) U f := by
  unfold valAt'
  by_cases h : ⊤ ≤ (y ≫ φ) ⁻¹ᵁ U
  · have h' : ⊤ ≤ y ⁻¹ᵁ (φ ⁻¹ᵁ U) := h
    rw [dif_pos h, dif_pos h']
    unfold valAt
    rw [Scheme.Hom.comp_appLE]
    rfl
  · have h' : ¬ ⊤ ≤ y ⁻¹ᵁ (φ ⁻¹ᵁ U) := h
    rw [dif_neg h, dif_neg h']

private theorem exAt_eq_ex_comp_lift (z : Fin g → ℂ) :
    exAt u p z = (u.ex z).left ≫ (lift (toUnit A ≫ p) (𝟙 A)).left := by
  unfold exAt
  rw [← Over.comp_left, comp_lift, Category.comp_id, ← Category.assoc,
    toUnit_unique (u.ex z ≫ toUnit A) (𝟙 _), Category.id_comp]

private theorem exists_ringHom_eq_valAt' {X : Scheme.{0}} (y : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U) :
    ∃ φ : Γ(X, U) →+* ℂ, ∀ f, φ f = valAt' y U f :=
  ⟨(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (y.appLE U ⊤ h).hom, fun f => by
    unfold valAt'
    rw [dif_pos h]
    rfl⟩

private theorem preimage_inf_eq_univ {X : Scheme.{0}} (y : Sp ℂ ⟶ X) {U V : X.Opens}
    (h1 : ⊤ ≤ y ⁻¹ᵁ U) (h2 : ⊤ ≤ y ⁻¹ᵁ V) : ⊤ ≤ y ⁻¹ᵁ (U ⊓ V) := by
  intro a ha
  have h1' := h1 ha
  have h2' := h2 ha
  exact ⟨h1', h2'⟩

private theorem mul_zpow_div_zpow_eq_of_factor {v v' G0 G1 f0 f1 f0' f1' : ℂ} (a b : ℤ) (hG0 : G0 ≠ 0) (hG1 : G1 ≠ 0)
    (hf0' : f0' ≠ 0) (hv : v = G0 ^ a * G1 ^ (-b) * v') (h0 : f0 = G0 * f0') (h1 : f1 = G1 * f1') :
    v * f1 ^ b / f0 ^ a = v' * f1' ^ b / f0' ^ a := by
  subst hv h0 h1
  have hinv : G1 ^ (-b) * G1 ^ b = 1 := by
    rw [zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ hG1)]
  rw [div_eq_div_iff (zpow_ne_zero _ (mul_ne_zero hG0 hf0')) (zpow_ne_zero _ hf0'), mul_zpow, mul_zpow]
  linear_combination (G0 ^ a * v' * f1' ^ b * f0' ^ a) * hinv

private theorem ringHom_prod_units_zpow {R : Type} [CommRing R] (φ : R →+* ℂ) {n : ℕ} (v : Fin n → Rˣ)
    (e : Fin n → ℤ) : φ ((∏ k, v k ^ e k : Rˣ) : R) = ∏ k, (φ (v k : R)) ^ e k := by
  have h1 : φ ((∏ k, v k ^ e k : Rˣ) : R) = ((Units.map φ.toMonoidHom (∏ k, v k ^ e k) : ℂˣ) : ℂ) := rfl
  rw [h1, map_prod, Units.coe_prod]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  rw [map_zpow, Units.val_zpow_eq_zpow_val]
  rfl

private theorem valAt'_res_pullU_eq_valAt'_comp {X Y : Scheme.{0}} (y : Sp ℂ ⟶ Y) (ψ : Y ⟶ X) (V : X.Opens)
    {W : Y.Opens} (h : W ≤ ψ ⁻¹ᵁ V) (hy : ⊤ ≤ y ⁻¹ᵁ W) (f : Γ(X, V)ˣ) :
    valAt' y W (res h (pullU ψ V f)).val = valAt' (y ≫ ψ) V f.val := by
  unfold res pullU
  simp only [Units.coe_map]
  erw [valAt'_resG _ h hy, valAt'_app_eq_valAt'_comp]

private theorem valAt'_res_eq {X : Scheme.{0}} (y : Sp ℂ ⟶ X) {U V : X.Opens} (h : V ≤ U)
    (hy : ⊤ ≤ y ⁻¹ᵁ V) (f : Γ(X, U)ˣ) : valAt' y V (res h f).val = valAt' y U f.val := by
  unfold res
  exact valAt'_resG _ h hy _

private theorem valAt'_linComb_g_eq_prod_zpow {X Y : Scheme.{0}} (L : LB X) (F : Fin 2 → (Y ⟶ X)) (ε : Fin 2 → ℤ)
    (i j : (LB.LinComb L F ε).ι) (y : Sp ℂ ⟶ Y)
    (hy : ⊤ ≤ y ⁻¹ᵁ ((LB.LinComb L F ε).U i ⊓ (LB.LinComb L F ε).U j)) :
    valAt' y ((LB.LinComb L F ε).U i ⊓ (LB.LinComb L F ε).U j) ((LB.LinComb L F ε).g i j).val =
      ∏ k, valAt' (y ≫ F k) (L.U (i k) ⊓ L.U (j k)) (L.g (i k) (j k)).val ^ ε k := by
  have hle : ∀ k, (LB.LinComb L F ε).U i ⊓ (LB.LinComb L F ε).U j ≤ F k ⁻¹ᵁ (L.U (i k) ⊓ L.U (j k)) :=
    fun k x hx => ⟨Set.mem_iInter.1 hx.1 k, Set.mem_iInter.1 hx.2 k⟩
  have hg : (LB.LinComb L F ε).g i j = ∏ k, res (hle k) (pullU (F k) _ (L.g (i k) (j k))) ^ ε k := rfl
  obtain ⟨φ, hφ⟩ := exists_ringHom_eq_valAt' y _ hy
  rw [← hφ, hg, ringHom_prod_units_zpow]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  rw [hφ, valAt'_res_pullU_eq_valAt'_comp _ _ _ _ hy]

private theorem div_zpow_eq_mul_zpow_neg (x y : ℂ) (a : ℤ) : x / y ^ a = x * y ^ (-a) := by
  rw [zpow_neg, div_eq_mul_inv]

theorem exists_entire_twist (hL : L.IsLB) {m : T ⊗ A ⟶ A} {a b : ℤ}
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])) (hα : α.IsGen)
    {w : (Fin g → ℂ) → Fin g → ℂ} (hwd : Differentiable ℂ w)
    (hw : ∀ z, exAt u p z ≫ m.left = (u.ex (w z)).left) :
    ∃ r : (Fin g → ℂ) → ℂ, Differentiable ℂ r ∧ (∀ z, r z ≠ 0) ∧
      ∀ (j : Fin 2 → L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j 0) →
        ⊤ ≤ (u.ex (w z)).left ⁻¹ᵁ L.U (j 1) →
        valAt' (exAt u p z) (LB.wchart L ![(snd T A).left, m.left] j) (α.s j).val *
          u.fr (j 1) (w z) ^ b = r z * u.fr (j 0) z ^ a := by
  have hsnd : ∀ z, exAt u p z ≫ (snd T A).left = (u.ex z).left := by
    intro z
    unfold exAt
    rw [← Over.comp_left, lift_snd]
  unfold LB.Gen.IsGen at hα
  obtain ⟨Q, hQ⟩ : ∃ Q : (Fin 2 → L.ι) → (Fin g → ℂ) → ℂ, ∀ j z, Q j z =
      valAt' (exAt u p z) (LB.wchart L ![(snd T A).left, m.left] j) (α.s j).val *
        u.fr (j 1) (w z) ^ b / u.fr (j 0) z ^ a := ⟨_, fun _ _ => rfl⟩
  have compat : ∀ (j j' : Fin 2 → L.ι) z,
      ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j 0) → ⊤ ≤ (u.ex (w z)).left ⁻¹ᵁ L.U (j 1) →
      ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j' 0) → ⊤ ≤ (u.ex (w z)).left ⁻¹ᵁ L.U (j' 1) →
      Q j z = Q j' z := by
    intro j j' z h0 h1 h0' h1'
    have hc := (exAt_mem_twist_chart_iff u p (hw z) j).2 ⟨h0, h1⟩
    have hc' := (exAt_mem_twist_chart_iff u p (hw z) j').2 ⟨h0', h1'⟩
    have hW := preimage_inf_eq_univ _ hc hc'
    have hW2 : ⊤ ≤ exAt u p z ⁻¹ᵁ ((LB.LinComb L ![(snd T A).left, m.left] ![a, -b]).U j ⊓
        (LB.LinComb L ![(snd T A).left, m.left] ![a, -b]).U j') := hW
    obtain ⟨φ, hφ⟩ := exists_ringHom_eq_valAt' (exAt u p z) _ hW2
    have E := (congrArg (fun v => φ v.val) (hα j j')).trans
      ((congrArg φ (Units.val_mul _ _)).trans (map_mul φ _ _))
    beta_reduce at E
    have Vj := (hφ _).trans (valAt'_res_eq (exAt u p z) inf_le_left hW2 (α.s j))
    have Vj' := (hφ _).trans (valAt'_res_eq (exAt u p z) inf_le_right hW2 (α.s j'))
    have Gv := (hφ _).trans ((valAt'_linComb_g_eq_prod_zpow L _ _ j j' _ hW2).trans (Fin.prod_univ_two _))
    rw [Vj, Vj', Gv] at E
    have hG0eq : valAt' (exAt u p z ≫ ![(snd T A).left, m.left] 0) (L.U (j 0) ⊓ L.U (j' 0))
        (L.g (j 0) (j' 0)).val = valAt' (u.ex z).left (L.U (j 0) ⊓ L.U (j' 0)) (L.g (j 0) (j' 0)).val := by
      rw [Matrix.cons_val_zero, hsnd]
    have hG1eq : valAt' (exAt u p z ≫ ![(snd T A).left, m.left] 1) (L.U (j 1) ⊓ L.U (j' 1))
        (L.g (j 1) (j' 1)).val =
        valAt' (u.ex (w z)).left (L.U (j 1) ⊓ L.U (j' 1)) (L.g (j 1) (j' 1)).val := by
      rw [Matrix.cons_val_one, Matrix.cons_val_zero, hw]
    rw [hG0eq, hG1eq] at E
    have f0 := u.fr_compat (j 0) (j' 0) z (preimage_inf_eq_univ _ h0 h0')
    have f1 := u.fr_compat (j 1) (j' 1) (w z) (preimage_inf_eq_univ _ h1 h1')
    have hG0 := valAt'_unit_ne_zero_cusp_form_evaluations _ _ (preimage_inf_eq_univ _ h0 h0') (L.g (j 0) (j' 0))
    have hG1 := valAt'_unit_ne_zero_cusp_form_evaluations _ _ (preimage_inf_eq_univ _ h1 h1') (L.g (j 1) (j' 1))
    rw [hQ, hQ]
    exact mul_zpow_div_zpow_eq_of_factor a b hG0 hG1 (u.fr_ne _ _ h0') E f0 f1
  have hex : ∀ z, ∃ j : Fin 2 → L.ι,
      ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j 0) ∧ ⊤ ≤ (u.ex (w z)).left ⁻¹ᵁ L.U (j 1) := by
    intro z
    obtain ⟨i0, hi0⟩ := exists_algChart_mem_source hL (u.ex z).left
    obtain ⟨i1, hi1⟩ := exists_algChart_mem_source hL (u.ex (w z)).left
    exact ⟨![i0, i1], hi0, hi1⟩
  choose J hJ0 hJ1 using hex
  refine ⟨fun z => Q (J z) z, ?_, fun z => ?_, fun j z h0 h1 => ?_⟩
  · refine fun z0 => ?_
    have hO : IsOpen {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (J z0 0) ∧
        ⊤ ≤ (u.ex (w z)).left ⁻¹ᵁ L.U (J z0 1)} :=
      (u.hol (L.U (J z0 0)) 0).1.inter ((u.hol (L.U (J z0 1)) 0).1.preimage hwd.continuous)
    have hz0 : z0 ∈ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (J z0 0) ∧
        ⊤ ≤ (u.ex (w z)).left ⁻¹ᵁ L.U (J z0 1)} := ⟨hJ0 z0, hJ1 z0⟩
    have hval : DifferentiableOn ℂ (fun z => valAt' (exAt u p z)
        (LB.wchart L ![(snd T A).left, m.left] (J z0)) (α.s (J z0)).val)
        {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (J z0 0) ∧ ⊤ ≤ (u.ex (w z)).left ⁻¹ᵁ L.U (J z0 1)} := by
      have hfac : ∀ z, valAt' (exAt u p z) (LB.wchart L ![(snd T A).left, m.left] (J z0))
          (α.s (J z0)).val = valAt' (u.ex z).left
            ((lift (toUnit A ≫ p) (𝟙 A)).left ⁻¹ᵁ LB.wchart L ![(snd T A).left, m.left] (J z0))
            ((lift (toUnit A ≫ p) (𝟙 A)).left.app _ (α.s (J z0)).val) := by
        intro z
        rw [exAt_eq_ex_comp_lift u p z]
        exact (valAt'_app_eq_valAt'_comp _ _ _ _).symm
      simp only [hfac]
      refine (u.hol _ _).2.mono (fun z hz => ?_)
      have hc := (exAt_mem_twist_chart_iff u p (hw z) (J z0)).2 hz
      rw [exAt_eq_ex_comp_lift u p z] at hc
      exact hc
    have hf1 : DifferentiableOn ℂ (fun z => u.fr (J z0 1) (w z) ^ b)
        {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (J z0 0) ∧ ⊤ ≤ (u.ex (w z)).left ⁻¹ᵁ L.U (J z0 1)} :=
      DifferentiableOn.zpow ((u.fr_hol (J z0 1)).comp hwd.differentiableOn (fun z hz => hz.2))
        (Or.inl (fun z hz => u.fr_ne _ _ hz.2))
    have hf0 : DifferentiableOn ℂ (fun z => u.fr (J z0 0) z ^ a)
        {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (J z0 0) ∧ ⊤ ≤ (u.ex (w z)).left ⁻¹ᵁ L.U (J z0 1)} :=
      DifferentiableOn.zpow ((u.fr_hol (J z0 0)).mono (fun z hz => hz.1))
        (Or.inl (fun z hz => u.fr_ne _ _ hz.1))
    have hQd : DifferentiableOn ℂ (Q (J z0))
        {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (J z0 0) ∧ ⊤ ≤ (u.ex (w z)).left ⁻¹ᵁ L.U (J z0 1)} := by
      have hf0' : DifferentiableOn ℂ (fun z => u.fr (J z0 0) z ^ (-a))
          {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (J z0 0) ∧ ⊤ ≤ (u.ex (w z)).left ⁻¹ᵁ L.U (J z0 1)} :=
        DifferentiableOn.zpow ((u.fr_hol (J z0 0)).mono (fun z hz => hz.1))
          (Or.inl (fun z hz => u.fr_ne _ _ hz.1))
      have hd := (hval.mul hf1).mul hf0'
      refine hd.congr (fun z _ => ?_)
      rw [hQ]
      exact div_zpow_eq_mul_zpow_neg _ _ _
    refine (hQd.differentiableAt (hO.mem_nhds hz0)).congr_of_eventuallyEq ?_
    filter_upwards [hO.mem_nhds hz0] with z hz
    exact compat (J z) (J z0) z (hJ0 z) (hJ1 z) hz.1 hz.2
  · show Q (J z) z ≠ 0
    rw [hQ]
    exact div_ne_zero (mul_ne_zero (valAt'_unit_ne_zero_cusp_form_evaluations _ _
      ((exAt_mem_twist_chart_iff u p (hw z) (J z)).2 ⟨hJ0 z, hJ1 z⟩) _)
      (zpow_ne_zero _ (u.fr_ne _ _ (hJ1 z)))) (zpow_ne_zero _ (u.fr_ne _ _ (hJ0 z)))
  · show _ = Q (J z) z * _
    rw [← compat j (J z) z h0 h1 (hJ0 z) (hJ1 z), hQ,
      div_mul_cancel₀ _ (zpow_ne_zero _ (u.fr_ne _ _ h0))]

variable {p} in

theorem exAt_translPt {y : T ⟶ A} {x : Fin g → ℂ} (hy : p ≫ y = u.ex x) (z : Fin g → ℂ) :
    exAt u p z ≫ (translPt A y).left = (u.ex (z + x)).left := by
  have h : lift p (u.ex z) ≫ translPt A y = u.ex (z + x) := by
    unfold translPt
    rw [← Category.assoc, comp_lift, lift_fst_assoc, lift_snd, hy, ← Hom.mul_def, ← u.ex_add, add_comm]
  unfold exAt
  rw [← Over.comp_left, h]

variable {p} in

theorem exAt_translT {y : T ⟶ A} {x : Fin g → ℂ} (hy : p ≫ y = u.ex x) (z : Fin g → ℂ) :
    exAt u p z ≫ (translT A y).left = exAt u p (z + x) := by
  have h : lift p (u.ex z) ≫ translPt A y = u.ex (z + x) := by
    unfold translPt
    rw [← Category.assoc, comp_lift, lift_fst_assoc, lift_snd, hy, ← Hom.mul_def, ← u.ex_add, add_comm]
  have h' : lift p (u.ex z) ≫ translT A y = lift p (u.ex (z + x)) := by
    unfold translT
    rw [comp_lift, lift_fst, h]
  unfold exAt
  rw [← Over.comp_left, h']

def fockFactor (Hm : Matrix (Fin g) (Fin g) ℂ) (k : ℤ) (x z : Fin g → ℂ) : ℂ :=
  Complex.exp (-(k * Real.pi * hermForm Hm z x) - k * Real.pi * hermForm Hm x x / 2)

theorem fockFactor_ne_zero (Hm : Matrix (Fin g) (Fin g) ℂ) (k : ℤ) (x z : Fin g → ℂ) :
    fockFactor Hm k x z ≠ 0 := by
  unfold fockFactor
  exact Complex.exp_ne_zero _

def HasAnConst (Hm : Matrix (Fin g) (Fin g) ℂ) {k : ℤ} (Θ : ThetaGrp A L k T) (x : Fin g → ℂ)
    (c : ℂ) : Prop :=
  p ≫ Θ.pt = u.ex x ∧
    ∀ (j : Fin 2 → L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j 0) →
      ⊤ ≤ (u.ex (z + x)).left ⁻¹ᵁ L.U (j 1) →
      valAt' (exAt u p z) (LB.wchart L ![(snd T A).left, (translPt A Θ.pt).left] j) (Θ.φ.s j).val *
        u.fr (j 1) (z + x) ^ k = c * fockFactor Hm k x z * u.fr (j 0) z ^ k

variable {u p} {Hm : Matrix (Fin g) (Fin g) ℂ} {k : ℤ} {Θ : ThetaGrp A L k T} {x : Fin g → ℂ}

theorem HasAnConst.unique (hL : L.IsLB) {c c' : ℂ} (h : HasAnConst u p Hm Θ x c)
    (h' : HasAnConst u p Hm Θ x c') : c = c' := by
  obtain ⟨i0, hi0⟩ := exists_algChart_mem_source hL (u.ex 0).left
  obtain ⟨i1, hi1⟩ := exists_algChart_mem_source hL (u.ex (0 + x)).left
  have e := h.2 ![i0, i1] 0 hi0 hi1
  have e' := h'.2 ![i0, i1] 0 hi0 hi1
  rw [e] at e'
  have hF := fockFactor_ne_zero Hm k x 0
  have hfr : u.fr (![i0, i1] 0) 0 ^ k ≠ 0 := zpow_ne_zero _ (u.fr_ne _ _ hi0)
  exact mul_right_cancel₀ hF (mul_right_cancel₀ hfr e')

theorem HasAnConst.ne_zero (hL : L.IsLB) {c : ℂ} (h : HasAnConst u p Hm Θ x c) : c ≠ 0 := by
  obtain ⟨i0, hi0⟩ := exists_algChart_mem_source hL (u.ex 0).left
  obtain ⟨i1, hi1⟩ := exists_algChart_mem_source hL (u.ex (0 + x)).left
  have e := h.2 ![i0, i1] 0 hi0 hi1
  intro hc
  rw [hc, zero_mul, zero_mul] at e
  have hch := (exAt_mem_twist_chart_iff u p (exAt_translPt u h.1 0) ![i0, i1]).2 ⟨hi0, hi1⟩
  have hv := valAt'_unit_ne_zero_cusp_form_evaluations (exAt u p 0) _ hch (Θ.φ.s ![i0, i1])
  exact mul_ne_zero hv (zpow_ne_zero k (u.fr_ne _ _ hi1)) e

private theorem exAt_preimage_wchart_eq_univ (z : Fin g → ℂ) (i : L.ι)
    (h : ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i) :
    ⊤ ≤ exAt u p z ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => i) := by
  have h0 : exAt u p z ≫ (snd T A).left = (u.ex z).left := by
    unfold exAt
    rw [← Over.comp_left, lift_snd]
  rw [← h0] at h
  intro a ha
  refine Set.mem_iInter.2 (fun _ => ?_)
  simpa using h ha

theorem HasAnConst.act (hL : L.IsLB) {c : ℂ} (h : HasAnConst u p Hm Θ x c)
    {s s' : LB.Sec (LPow A L k T)} (hs : IsActOf A L k Θ s s') {θ θ' : (Fin g → ℂ) → ℂ}
    (hθ : IsFnAt u p k s θ) (hθ' : IsFnAt u p k s' θ') (z : Fin g → ℂ) :
    θ' z = c * fockFactor Hm k x z * θ (z + x) := by
  obtain ⟨i0, hi0⟩ := exists_algChart_mem_source hL (u.ex z).left
  obtain ⟨i1, hi1⟩ := exists_algChart_mem_source hL (u.ex (z + x)).left
  have hch := (exAt_mem_twist_chart_iff u p (exAt_translPt u h.1 z) ![i0, i1]).2 ⟨hi0, hi1⟩
  have e : valAt' (exAt u p z) (LB.wchart L ![(snd T A).left, (translPt A Θ.pt).left] ![i0, i1])
      (Θ.φ.s ![i0, i1]).val * u.fr i1 (z + x) ^ k = c * fockFactor Hm k x z * u.fr i0 z ^ k :=
    h.2 ![i0, i1] z hi0 hi1
  unfold IsActOf IsTwistPull at hs
  have hs1 := congrArg (valAt' (exAt u p z) _) (hs ![i0, i1])
  erw [valAt'_mul_of_top_le_preimage_open, valAt'_resG _ _ hch, valAt'_resG _ _ hch, valAt'_app_eq_valAt'_comp,
    exAt_translT u h.1 z] at hs1
  have A1 : valAt' (exAt u p z) ((LPow A L k T).U fun _ => i0) (s'.f fun _ => i0) = θ' z * u.fr i0 z ^ k :=
    hθ' (fun _ => i0) z (exAt_preimage_wchart_eq_univ z i0 hi0)
  have A2 : valAt' (exAt u p (z + x)) ((LPow A L k T).U fun _ => i1) (s.f fun _ => i1) =
      θ (z + x) * u.fr i1 (z + x) ^ k :=
    hθ (fun _ => i1) (z + x) (exAt_preimage_wchart_eq_univ (z + x) i1 hi1)
  have key : θ' z * u.fr i0 z ^ k = valAt' (exAt u p z)
      (LB.wchart L ![(snd T A).left, (translPt A Θ.pt).left] ![i0, i1]) (Θ.φ.s ![i0, i1]).val *
      (θ (z + x) * u.fr i1 (z + x) ^ k) := by
    rw [← A1, ← A2]
    exact hs1
  have hfr0 : u.fr i0 z ^ k ≠ 0 := zpow_ne_zero _ (u.fr_ne _ _ hi0)
  apply mul_right_cancel₀ hfr0
  linear_combination key + θ (z + x) * e

theorem exists_int_of_exp_eq_one {t : ℝ}
    (h : Complex.exp (-(2 * Real.pi * Complex.I * t)) = 1) : ∃ n : ℤ, t = n := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h
  refine ⟨-n, ?_⟩
  have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have ht : (t : ℂ) = ((-n : ℤ) : ℂ) := by
    apply mul_right_cancel₀ hc
    push_cast
    linear_combination -hn
  exact_mod_cast ht

private theorem mul_zpow_eq_of_two_zpow_relations {V r r' q a0 f0 f1 W : ℂ} (k : ℤ) (hq : q ≠ 0) (ha : a0 ≠ 0)
    (hf : f0 ≠ 0) (e1 : V * (q * (a0 * W) * f1) ^ k = r * (q * a0 * f0) ^ k)
    (e2 : V * f1 ^ k = r' * f0 ^ k) : r' * W ^ k = r := by
  simp only [mul_zpow] at e1
  have hne : q ^ k * a0 ^ k * f0 ^ k ≠ 0 :=
    mul_ne_zero (mul_ne_zero (zpow_ne_zero _ hq) (zpow_ne_zero _ ha)) (zpow_ne_zero _ hf)
  apply mul_right_cancel₀ hne
  linear_combination e1 - (q ^ k * a0 ^ k * W ^ k) * e2

private theorem complex_star_eq_sub_two_I_mul_im (w : ℂ) : star w = w - 2 * Complex.I * (w.im : ℂ) := by
  apply Complex.ext <;> simp <;> ring

theorem exists_hasAnConst (hL : L.IsLB) {χ : u.Λ → ℂ} (hAH : u.IsAH Hm χ)
    (hx : p ≫ Θ.pt = u.ex x) :
    (∀ l ∈ u.Λ, ∃ n : ℤ, k * (hermForm Hm x l).im = n) ∧ ∃ c, HasAnConst u p Hm Θ x c := by
  obtain ⟨r, hrd, hr0, hr⟩ := exists_entire_twist u p hL (m := translPt A Θ.pt) (a := k) (b := k)
    Θ.φ Θ.isGen (w := fun z => z + x) (differentiable_id.add_const x) (fun z => exAt_translPt u hx z)
  have hr' : ∀ (j : Fin 2 → L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j 0) →
      ⊤ ≤ (u.ex (z + x)).left ⁻¹ᵁ L.U (j 1) →
      valAt' (exAt u p z) (LB.wchart L ![(snd T A).left, (translPt A Θ.pt).left] j) (Θ.φ.s j).val *
        u.fr (j 1) (z + x) ^ k = r z * u.fr (j 0) z ^ k :=
    fun j z h0 h1 => hr j z h0 h1
  have hper : ∀ (l : u.Λ) z, u.ex (z + l) = u.ex z := by
    intro l z
    rw [u.ex_add, (u.ker _).2 l.2, _root_.mul_one]
  have R1 : ∀ (l : u.Λ) z,
      r (z + l) * Complex.exp (Real.pi * (x ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))) ^ k = r z := by
    intro l z
    obtain ⟨i0, hi0⟩ := exists_algChart_mem_source hL (u.ex z).left
    obtain ⟨i1, hi1⟩ := exists_algChart_mem_source hL (u.ex (z + x)).left
    have hi0' : ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ L.U i0 := by
      rw [hper]
      exact hi0
    have hi1' : ⊤ ≤ (u.ex (z + l + x)).left ⁻¹ᵁ L.U i1 := by
      rw [add_right_comm, hper]
      exact hi1
    have hexAt : exAt u p (z + l) = exAt u p z := by
      unfold exAt
      rw [hper]
    have e1 : valAt' (exAt u p z) (LB.wchart L ![(snd T A).left, (translPt A Θ.pt).left] ![i0, i1])
        (Θ.φ.s ![i0, i1]).val * u.fr i1 (z + x) ^ k = r z * u.fr i0 z ^ k := hr' ![i0, i1] z hi0 hi1
    have e2 : valAt' (exAt u p z) (LB.wchart L ![(snd T A).left, (translPt A Θ.pt).left] ![i0, i1])
        (Θ.φ.s ![i0, i1]).val * u.fr i1 (z + x + l) ^ k = r (z + l) * u.fr i0 (z + l) ^ k := by
      have h2 := hr' ![i0, i1] (z + l) hi0' hi1'
      rw [hexAt, add_right_comm] at h2
      exact h2
    have a0 := hAH.2.2.2 l i0 z hi0
    have a1 := hAH.2.2.2 l i1 (z + x) hi1
    have hE : Complex.exp (Real.pi * ((z + x) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
        Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))) =
        Complex.exp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
          Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))) *
        Complex.exp (Real.pi * (x ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))) := by
      rw [add_dotProduct, ← Complex.exp_add]
      congr 1
      ring
    rw [a0, a1, hE] at e1
    have hχ : χ l ≠ 0 := by
      intro h0
      have := hAH.2.2.1 l
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    exact mul_zpow_eq_of_two_zpow_relations k hχ (Complex.exp_ne_zero _) (u.fr_ne _ _ hi0') e1 e2
  obtain ⟨ρ, hρ⟩ : ∃ ρ : (Fin g → ℂ) → ℂ, ∀ z, ρ z = r z *
      Complex.exp (k * Real.pi * hermForm Hm z x + k * Real.pi * hermForm Hm x x / 2) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨cf, hcf⟩ : ∃ cf : u.Λ → ℂ, ∀ l, cf l =
      Complex.exp (-(2 * Real.pi * Complex.I * (((k : ℝ) * (hermForm Hm x l).im : ℝ) : ℂ))) :=
    ⟨_, fun _ => rfl⟩
  have hB := hAH.1
  have R2 : ∀ (l : u.Λ) z, ρ (z + l) = cf l * ρ z := by
    intro l z
    have hr1 : r (z + l) = r z * Complex.exp (-(k * Real.pi * hermForm Hm x l)) := by
      rw [← R1 l z, ← Complex.exp_int_mul, _root_.mul_assoc, ← Complex.exp_add]
      have h0 : (k : ℂ) * (Real.pi * (x ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))) +
          -(k * Real.pi * hermForm Hm x l) = 0 := by
        unfold hermForm
        ring
      rw [h0, Complex.exp_zero, _root_.mul_one]
    rw [hρ, hρ, hr1, hcf, _root_.mul_assoc, ← Complex.exp_add, _root_.mul_left_comm, ← Complex.exp_add]
    congr 2
    rw [hermForm_add_left, hermForm_swap hB x (l : Fin g → ℂ), complex_star_eq_sub_two_I_mul_im]
    push_cast
    ring
  have hρd : Differentiable ℂ ρ := by
    have hfun : ρ = fun z => r z *
        Complex.exp (k * Real.pi * hermForm Hm z x + k * Real.pi * hermForm Hm x x / 2) := funext hρ
    rw [hfun]
    simp only [hermForm, dotProduct]
    fun_prop
  have hρ0 : ∀ z, ρ z ≠ 0 := fun z => by
    rw [hρ]
    exact mul_ne_zero (hr0 z) (Complex.exp_ne_zero _)
  have hcn : ∀ l, ‖cf l‖ = 1 := by
    intro l
    rw [hcf, Complex.norm_exp]
    simp
  have := u.discrete
  obtain ⟨-, hc1, hconst⟩ := appellHumbert_trivial_of_nowhere_vanishing g u.Λ u.full 0 cf ρ
    Matrix.isHermitian_zero hcn hρd hρ0 (fun l z => by
      rw [R2 l z]
      simp [hermForm])
  refine ⟨fun l hl => exists_int_of_exp_eq_one (by have h1 := hc1 ⟨l, hl⟩; rw [hcf] at h1; exact h1), ρ 0, hx,
    fun j z h0 h1 => ?_⟩
  rw [hr' j z h0 h1, ← hconst z, hρ]
  have hEF : Complex.exp (k * Real.pi * hermForm Hm z x + k * Real.pi * hermForm Hm x x / 2) *
      fockFactor Hm k x z = 1 := by
    unfold fockFactor
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 2
    ring
  linear_combination (-(r z * u.fr (j 0) z ^ k)) * hEF

variable (L) in

def thetaGrpZero (y : T ⟶ A) : ThetaGrp A L 0 T where
  pt := y
  φ := ⟨fun _ => 1⟩
  isGen j j' := by
    have : (thetaLB A L 0 y).g j j' = 1 := by
      unfold thetaLB LB.LinComb
      dsimp only
      exact Finset.prod_eq_one fun i _ => by fin_cases i <;> exact zpow_zero _
    rw [this, _root_.one_mul]
    exact (map_one _).trans (map_one _).symm

end GlobalTheory.ThetaFn
