import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SemicharacterSqEqOneOfSymmetric

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.ThetaFn

open CubeValues SymmetricSemicharacter

section Values

variable {X Y : Scheme.{0}} (x : Sp ℂ ⟶ X)

def valHom (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* ℂ :=
  (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (x.appLE U ⊤ h).hom

theorem valAt'_eq_valHom {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    valAt' x U f = valHom x U h f := by
  rw [valAt', dif_pos h]; rfl

theorem valAt'_mul {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f f' : Γ(X, U)) :
    valAt' x U (f * f') = valAt' x U f * valAt' x U f' := by
  simp only [valAt'_eq_valHom x h, map_mul]

theorem valAt'_add {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f f' : Γ(X, U)) :
    valAt' x U (f + f') = valAt' x U f + valAt' x U f' := by
  simp only [valAt'_eq_valHom x h, map_add]

theorem valAt'_sum {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) {I : Type*} (t : Finset I) (f : I → Γ(X, U)) :
    valAt' x U (∑ i ∈ t, f i) = ∑ i ∈ t, valAt' x U (f i) := by
  simp only [valAt'_eq_valHom x h, map_sum]

theorem valAt'_unit_zpow {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)ˣ) (k : ℤ) :
    valAt' x U (f ^ k).val = valAt' x U f.val ^ k := by
  simp only [valAt'_eq_valHom x h]
  have h1 : ∀ v : Γ(X, U)ˣ, valHom x U h v.val =
      ((Units.coeHom ℂ).comp (Units.map (valHom x U h).toMonoidHom)) v := fun v => rfl
  simp only [h1, map_zpow]

theorem valAt'_res {U V : X.Opens} (h : V ≤ U) (hV : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, U)) :
    valAt' x V ((X.presheaf.map (homOfLE h).op).hom f) = valAt' x U f :=
  (valueRules X x).2.2.1 U V h f hV

theorem valAt'_app (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)) :
    valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f :=
  (valueRules X x).2.2.2.1 Y φ U f

theorem valAt'_appLE' (φ : X ⟶ Y) {U : Y.Opens} {V : X.Opens} (e : V ≤ φ ⁻¹ᵁ U)
    (hV : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(Y, U)) :
    valAt' x V ((φ.appLE U V e).hom f) = valAt' (x ≫ φ) U f :=
  (valAt'_res x e hV _).trans (valAt'_app x φ U f)

theorem valAt'_sec {M : LB X} (s : M.Sec) (i j : M.ι) (hi : ⊤ ≤ x ⁻¹ᵁ M.U i)
    (hj : ⊤ ≤ x ⁻¹ᵁ M.U j) :
    valAt' x (M.U i) (s.f i) =
      valAt' x (M.U i ⊓ M.U j) (M.g i j).val * valAt' x (M.U j) (s.f j) := by
  have hij := (le_preimage_inf x _ _).2 ⟨hi, hj⟩
  rw [← valAt'_res x inf_le_left hij (s.f i), s.compat i j, valAt'_mul x hij,
    valAt'_res x inf_le_right hij]

theorem valAt'_id_top (r : Γ(Sp ℂ, ⊤)) :
    valAt' (𝟙 (Sp ℂ)) ⊤ r = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom r := by
  have e : ∀ k, Scheme.Hom.appLE (𝟙 (Sp ℂ)) ⊤ ⊤ k = 𝟙 _ := fun k => by
    rw [← Scheme.Hom.id_app]
    exact (Scheme.Hom.app_eq_appLE (𝟙 (Sp ℂ)) (U := ⊤)).symm
  rw [valAt', dif_pos (show ⊤ ≤ 𝟙 (Sp ℂ) ⁻¹ᵁ ⊤ from fun _ _ => trivial), valAt, e]
  rfl

theorem ext_of_valAt'_of_isIso [IsIso x] {U : X.Opens} {f f' : Γ(X, U)}
    (h : ⊤ ≤ x ⁻¹ᵁ U → valAt' x U f = valAt' x U f') : f = f' := by
  by_cases hU : ⊤ ≤ x ⁻¹ᵁ U
  · have h1 := h hU
    rw [valAt', valAt', dif_pos hU, dif_pos hU] at h1
    have h2 := (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).1 h1
    have hinj : Function.Injective (x.appLE U ⊤ hU).hom := by
      rw [Scheme.Hom.appLE_congr x hU rfl (top_unique hU).symm
        (fun φ => Function.Injective φ.hom), Scheme.Hom.appLE_eq_app]
      exact (ConcreteCategory.bijective_of_isIso (x.app U)).1
    exact hinj h2
  · have hb : U = ⊥ := by
      refine bot_unique fun y hy => hU ?_
      obtain ⟨q, rfl⟩ := x.surjective y
      intro q' _
      obtain rfl : q' = q := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
      exact hy
    subst hb
    exact Subsingleton.elim _ _

end Values

section Transport

variable {X Y Z : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K'] [Unique K]
  [Unique K']

theorem res_appLE (h : Z ⟶ Y) {U U' : Y.Opens} {V V' : Z.Opens} (hU : U' ≤ U) (hV : V' ≤ V)
    (e : V ≤ h ⁻¹ᵁ U) (e' : V' ≤ h ⁻¹ᵁ U') (f : Γ(Y, U)) :
    (Z.presheaf.map (homOfLE hV).op).hom ((h.appLE U V e).hom f) =
      (h.appLE U' V' e').hom ((Y.presheaf.map (homOfLE hU).op).hom f) :=
  congrArg (fun t : Γ(Y, U) ⟶ Γ(Z, V') => t.hom f)
    ((Scheme.Hom.appLE_map h e (homOfLE hV).op).trans
      (Scheme.Hom.map_appLE h e' (homOfLE hU).op).symm)

omit [Unique K] in

theorem wchart_le_of_comp {φ : Y ⟶ X} {ψ : Z ⟶ X} {h : Z ⟶ Y} (e : h ≫ φ = ψ) (j : K' → L.ι) :
    LB.wchart L (fun _ : K' => ψ) j ≤
      h ⁻¹ᵁ LB.wchart L (fun _ : K => φ) (fun _ => j default) := by
  subst e
  exact fun _ hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy default

theorem le_wchart_unique {W : Scheme.{0}} (x : W ⟶ Y) (φ : Y ⟶ X) (j : K → L.ι) :
    ⊤ ≤ x ⁻¹ᵁ LB.wchart L (fun _ : K => φ) j ↔ ⊤ ≤ (x ≫ φ) ⁻¹ᵁ L.U (j default) :=
  ⟨fun h _ hy => Set.mem_iInter.1 (h hy) default, fun h _ hy => Set.mem_iInter.2 fun k => by
    rw [Subsingleton.elim k default]; exact h hy⟩

def pullPow {φ : Y ⟶ X} {ψ : Z ⟶ X} (h : Z ⟶ Y) (e : h ≫ φ = ψ) (a : ℤ)
    (s : LB.Sec (LB.LinComb L (fun _ : K => φ) (fun _ => a))) :
    LB.Sec (LB.LinComb L (fun _ : K' => ψ) (fun _ => a)) where
  f j := (h.appLE _ _ (wchart_le_of_comp L (K := K) e j)).hom (s.f (fun _ => j default))
  compat i j := by
    have hij : LB.wchart L (fun _ : K' => ψ) i ⊓ LB.wchart L (fun _ : K' => ψ) j ≤
        h ⁻¹ᵁ (LB.wchart L (fun _ : K => φ) (fun _ => i default) ⊓
          LB.wchart L (fun _ : K => φ) (fun _ => j default)) :=
      le_inf (inf_le_left.trans (wchart_le_of_comp L e i))
        (inf_le_right.trans (wchart_le_of_comp L e j))
    have hc := congrArg (h.appLE _ _ hij).hom (s.compat (fun _ => i default) (fun _ => j default))
    replace hc := hc.trans (map_mul (h.appLE _ _ hij).hom _ _)
    have hg : (h.appLE _ _ hij).hom ((LB.LinComb L (fun _ : K => φ) (fun _ => a)).g
        (fun _ => i default) (fun _ => j default)).val =
        ((LB.LinComb L (fun _ : K' => ψ) (fun _ => a)).g i j).val := by
      subst e
      change (Units.map (h.appLE _ _ hij).hom.toMonoidHom _).val = _
      congr 1
      simp only [LB.LinComb, Fintype.prod_unique, map_zpow]
      congr 1
      ext1
      exact congrArg (fun t => t.hom (L.g (i default) (j default)).val)
        (Scheme.Hom.appLE_comp_appLE h φ _ _ _ _ hij)
    refine Eq.trans ?_ (hc.trans (congrArg₂ (· * ·) hg ?_))
    · exact res_appLE h _ _ _ hij _
    · exact (res_appLE h _ _ _ hij _).symm

theorem valAt'_pullPow {φ : Y ⟶ X} {ψ : Z ⟶ X} (h : Z ⟶ Y) (e : h ≫ φ = ψ) (a : ℤ)
    (s : LB.Sec (LB.LinComb L (fun _ : K => φ) (fun _ => a))) (x : Sp ℂ ⟶ Z) (j : K' → L.ι)
    (hj : ⊤ ≤ x ⁻¹ᵁ LB.wchart L (fun _ : K' => ψ) j) :
    valAt' x (LB.wchart L (fun _ : K' => ψ) j) ((pullPow L (K' := K') h e a s).f j) =
      valAt' (x ≫ h) (LB.wchart L (fun _ : K => φ) (fun _ => j default))
        (s.f (fun _ => j default)) :=
  valAt'_appLE' x h _ hj _

theorem pullPow_pullPow {φ : Y ⟶ X} {ψ : Z ⟶ X} (h : Z ⟶ Y) (e : h ≫ φ = ψ) (h' : Y ⟶ Z)
    (e' : h' ≫ ψ = φ) (hh : h' ≫ h = 𝟙 Y) (a : ℤ)
    (s : LB.Sec (LB.LinComb L (fun _ : K => φ) (fun _ => a))) :
    pullPow L (K' := K) h' e' a (pullPow L (K' := K') h e a s) = s := by
  have key : ∀ (t : Y ⟶ Y) (_ : t = 𝟙 Y) (U : Y.Opens) (l : U ≤ t ⁻¹ᵁ U),
      t.appLE U U l = 𝟙 _ := by
    rintro _ rfl U l
    rw [← Scheme.Hom.id_app]
    exact (Scheme.Hom.app_eq_appLE (𝟙 Y) (U := U)).symm
  have hf : (pullPow L (K' := K) h' e' a (pullPow L (K' := K') h e a s)).f = s.f := by
    funext j
    obtain ⟨i, rfl⟩ : ∃ i, j = fun _ => i :=
      ⟨j default, funext fun k => congrArg j (Subsingleton.elim _ _)⟩
    exact congrArg (fun t => t.hom (s.f fun _ => i))
      ((Scheme.Hom.appLE_comp_appLE h' h _ _ _ _ _).trans (key _ hh _ _))
  cases s
  exact (LB.Sec.mk.injEq _ _ _ _).mpr hf

end Transport

section Fibre

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
  {T : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ T)

variable (A) in

def fibreIncl : A ⟶ T ⊗ A := lift (toUnit A ≫ p) (𝟙 A)

omit [GrpObj A] in

theorem fibreIncl_snd : (fibreIncl A p).left ≫ (snd T A).left = 𝟙 A.left := by
  rw [← Over.comp_left, fibreIncl, lift_snd, Over.id_left]

omit [GrpObj A] in

theorem snd_fibreIncl [IsIso p] : (snd T A).left ≫ (fibreIncl A p).left = 𝟙 (T ⊗ A).left := by
  rw [← Over.comp_left, ← Over.id_left]
  congr 1
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
  · rw [← cancel_mono (inv p)]
    exact toUnit_unique _ _
  · rw [Category.assoc, fibreIncl, lift_snd, Category.comp_id, Category.id_comp]

omit [GrpObj A] in

theorem isIso_snd_left [IsIso p] : IsIso (snd T A).left :=
  ⟨⟨(fibreIncl A p).left, snd_fibreIncl p, fibreIncl_snd p⟩⟩

def exAt (z : Fin g → ℂ) : Sp ℂ ⟶ (T ⊗ A).left := (lift p (u.ex z)).left

theorem exAt_snd (z : Fin g → ℂ) : exAt u p z ≫ (snd T A).left = (u.ex z).left :=
  (Over.comp_left _ _ _ _ _).symm.trans (congrArg CommaMorphism.left (lift_snd p (u.ex z)))

theorem exAt_fst (z : Fin g → ℂ) : exAt u p z ≫ (fst T A).left = p.left :=
  (Over.comp_left _ _ _ _ _).symm.trans (congrArg CommaMorphism.left (lift_fst p (u.ex z)))

theorem ex_fibreIncl (z : Fin g → ℂ) : (u.ex z).left ≫ (fibreIncl A p).left = exAt u p z := by
  rw [← Over.comp_left, fibreIncl, comp_lift, Category.comp_id, ← Category.assoc,
    toUnit_unique (u.ex z ≫ toUnit A) (𝟙 _), Category.id_comp]
  rfl

theorem exAt_add_period (z l : Fin g → ℂ) (hl : l ∈ u.Λ) : exAt u p (z + l) = exAt u p z := by
  rw [exAt, exAt, ex_add_period u z l hl]

theorem comp_ptSecT {x : T ⟶ A} {z : Fin g → ℂ} (hx : p ≫ x = u.ex z) :
    p.left ≫ (ptSecT A x).left = exAt u p z := by
  rw [← Over.comp_left, ptSecT, comp_lift, Category.comp_id, hx]
  rfl

theorem exAt_mem_chart_iff (k : ℤ) (j : Fin 1 → L.ι) (z : Fin g → ℂ) :
    ⊤ ≤ exAt u p z ⁻¹ᵁ (LPow A L k T).U j ↔ ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j 0) := by
  refine (le_wchart_unique L (exAt u p z) (snd T A).left j).trans ?_
  rw [exAt_snd]
  rfl

theorem exAt_hol (U : (T ⊗ A).left.Opens) (f : Γ((T ⊗ A).left, U)) :
    IsOpen {z | ⊤ ≤ exAt u p z ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun z => valAt' (exAt u p z) U f) {z | ⊤ ≤ exAt u p z ⁻¹ᵁ U} := by
  have h := u.hol ((fibreIncl A p).left ⁻¹ᵁ U) (((fibreIncl A p).left.app U).hom f)
  simp only [← ex_fibreIncl]
  refine ⟨h.1, h.2.congr fun z _ => ?_⟩
  exact (valAt'_app (u.ex z).left (fibreIncl A p).left U f).symm

theorem valAt'_liftFun {W : (T ⊗ A).left.Opens} {z : Fin g → ℂ} (hW : ⊤ ≤ exAt u p z ⁻¹ᵁ W)
    (r : Γ(T.left, ⊤)) : valAt' (exAt u p z) W (liftFun A W r) = valAt' p.left ⊤ r := by
  refine (valAt'_res (exAt u p z) (U := (fst T A).left ⁻¹ᵁ ⊤) le_top hW _).trans ?_
  refine (valAt'_app (exAt u p z) (fst T A).left ⊤ r).trans ?_
  rw [exAt_fst]

theorem valAt'_LPow_g (k : ℤ) (j j' : Fin 1 → L.ι) (z : Fin g → ℂ)
    (hj : ⊤ ≤ exAt u p z ⁻¹ᵁ (LPow A L k T).U j) (hj' : ⊤ ≤ exAt u p z ⁻¹ᵁ (LPow A L k T).U j') :
    valAt' (exAt u p z) ((LPow A L k T).U j ⊓ (LPow A L k T).U j') ((LPow A L k T).g j j').val =
      valAt' (u.ex z).left (L.U (j 0) ⊓ L.U (j' 0)) (L.g (j 0) (j' 0)).val ^ k := by
  refine (val_linComb (exAt u p z) valueRules L _ _ j j' hj hj').trans ?_
  rw [Fin.prod_univ_one, exAt_snd]

def IsFnAt (k : ℤ) (s : LB.Sec (LPow A L k T)) (θ : (Fin g → ℂ) → ℂ) : Prop :=
  ∀ (j : Fin 1 → L.ι) z, ⊤ ≤ exAt u p z ⁻¹ᵁ (LPow A L k T).U j →
    valAt' (exAt u p z) ((LPow A L k T).U j) (s.f j) = θ z * u.fr (j 0) z ^ k

theorem exists_chart_exAt (hL : L.IsLB) (k : ℤ) (z : Fin g → ℂ) :
    ∃ j : Fin 1 → L.ι, ⊤ ≤ exAt u p z ⁻¹ᵁ (LPow A L k T).U j := by
  obtain ⟨i, hi⟩ := exists_chart u valueRules hL z
  exact ⟨fun _ => i, (exAt_mem_chart_iff u p k _ z).2 hi⟩

theorem fr_zpow_ne_zero {k : ℤ} {j : Fin 1 → L.ι} {z : Fin g → ℂ}
    (hj : ⊤ ≤ exAt u p z ⁻¹ᵁ (LPow A L k T).U j) (m : ℤ) : u.fr (j 0) z ^ m ≠ 0 :=
  zpow_ne_zero m (u.fr_ne _ z ((exAt_mem_chart_iff u p k j z).1 hj))

variable {u p} in

theorem IsFnAt.eq_div {k : ℤ} {s : LB.Sec (LPow A L k T)} {θ : (Fin g → ℂ) → ℂ}
    (h : IsFnAt u p k s θ) {j : Fin 1 → L.ι} {z : Fin g → ℂ}
    (hj : ⊤ ≤ exAt u p z ⁻¹ᵁ (LPow A L k T).U j) :
    θ z = valAt' (exAt u p z) ((LPow A L k T).U j) (s.f j) / u.fr (j 0) z ^ k := by
  rw [h j z hj, mul_div_cancel_right₀ _ (fr_zpow_ne_zero u p hj k)]

theorem isFnAt_of_exists_chart {k : ℤ} {s : LB.Sec (LPow A L k T)} {θ : (Fin g → ℂ) → ℂ}
    (h : ∀ z, ∃ j : Fin 1 → L.ι, ⊤ ≤ exAt u p z ⁻¹ᵁ (LPow A L k T).U j ∧
      valAt' (exAt u p z) ((LPow A L k T).U j) (s.f j) = θ z * u.fr (j 0) z ^ k) :
    IsFnAt u p k s θ := by
  intro j z hj
  obtain ⟨j', hj', e⟩ := h z
  have hc := u.fr_compat (j 0) (j' 0) z ((le_preimage_inf _ _ _).2
    ⟨(exAt_mem_chart_iff u p k j z).1 hj, (exAt_mem_chart_iff u p k j' z).1 hj'⟩)
  rw [valAt'_sec _ s j j' hj hj', valAt'_LPow_g u p k j j' z hj hj', e, hc, mul_zpow]
  ring

variable {u p} in

theorem IsFnAt.unique (hL : L.IsLB) {k : ℤ} {s : LB.Sec (LPow A L k T)}
    {θ θ' : (Fin g → ℂ) → ℂ} (h : IsFnAt u p k s θ) (h' : IsFnAt u p k s θ') : θ = θ' := by
  funext z
  obtain ⟨j, hj⟩ := exists_chart_exAt u p hL k z
  rw [h.eq_div hj, h'.eq_div hj]

theorem existsUnique_isFnAt (hL : L.IsLB) (k : ℤ) (s : LB.Sec (LPow A L k T)) :
    ∃! θ, IsFnAt u p k s θ := by
  choose c hc using exists_chart_exAt u p hL k
  have h : IsFnAt u p k s fun z =>
      valAt' (exAt u p z) ((LPow A L k T).U (c z)) (s.f (c z)) / u.fr (c z 0) z ^ k :=
    isFnAt_of_exists_chart u p fun z =>
      ⟨c z, hc z, (div_mul_cancel₀ _ (fr_zpow_ne_zero u p (hc z) k)).symm⟩
  exact ⟨_, h, fun θ hθ => hθ.unique hL h⟩

def fnAt (hL : L.IsLB) (k : ℤ) (s : LB.Sec (LPow A L k T)) : (Fin g → ℂ) → ℂ :=
  (existsUnique_isFnAt u p hL k s).exists.choose

theorem isFnAt_fnAt (hL : L.IsLB) (k : ℤ) (s : LB.Sec (LPow A L k T)) :
    IsFnAt u p k s (fnAt u p hL k s) :=
  (existsUnique_isFnAt u p hL k s).exists.choose_spec

theorem isFnAt_iff_eq_fnAt (hL : L.IsLB) {k : ℤ} {s : LB.Sec (LPow A L k T)}
    {θ : (Fin g → ℂ) → ℂ} : IsFnAt u p k s θ ↔ θ = fnAt u p hL k s :=
  ⟨fun h => h.unique hL (isFnAt_fnAt u p hL k s), fun h => h ▸ isFnAt_fnAt u p hL k s⟩

variable {u p}

theorem IsFnAt.differentiable (hL : L.IsLB) {k : ℤ} {s : LB.Sec (LPow A L k T)}
    {θ : (Fin g → ℂ) → ℂ} (h : IsFnAt u p k s θ) : Differentiable ℂ θ := by
  intro z
  obtain ⟨j, hj⟩ := exists_chart_exAt u p hL k z
  obtain ⟨ho, hd⟩ := exAt_hol u p _ (s.f j)
  have hn := ho.mem_nhds hj
  have hd2 : DifferentiableOn ℂ (u.fr (j 0)) {w | ⊤ ≤ exAt u p w ⁻¹ᵁ (LPow A L k T).U j} :=
    (u.fr_hol _).mono fun w hw => (exAt_mem_chart_iff u p k j w).1 hw
  have hq := (hd.differentiableAt hn).mul ((hd2.differentiableAt hn).zpow (m := -k)
    (Or.inl (u.fr_ne _ z ((exAt_mem_chart_iff u p k j z).1 hj))))
  refine hq.congr_of_eventuallyEq ?_
  filter_upwards [hn] with w hw
  rw [h.eq_div hw, div_eq_mul_inv, ← zpow_neg]
  rfl

theorem IsFnAt.add_period (hL : L.IsLB) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    (hAH : u.IsAH Hm χ) {k : ℤ} {s : LB.Sec (LPow A L k T)} {θ : (Fin g → ℂ) → ℂ}
    (h : IsFnAt u p k s θ) (l : u.Λ) (z : Fin g → ℂ) :
    θ (z + l) =
      (χ l * Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l)) ^ k * θ z := by
  obtain ⟨j, hj⟩ := exists_chart_exAt u p hL k z
  have hj' : ⊤ ≤ exAt u p (z + l) ⁻¹ᵁ (LPow A L k T).U j := by
    rw [exAt_add_period u p z l l.2]; exact hj
  have h2 := h j (z + l) hj'
  rw [exAt_add_period u p z l l.2, h j z hj,
    hAH.2.2.2 l _ z ((exAt_mem_chart_iff u p k j z).1 hj), mul_zpow, ← _root_.mul_assoc] at h2
  rw [← mul_right_cancel₀ (fr_zpow_ne_zero u p hj' k) h2, _root_.mul_comm]
  rfl

theorem IsFnAt.isThetaFn (hL : L.IsLB) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    (hAH : u.IsAH Hm χ) {n : ℕ} {s : LB.Sec (LPow A L n T)} {θ : (Fin g → ℂ) → ℂ}
    (h : IsFnAt u p n s θ) : u.IsThetaFn Hm χ n θ :=
  ⟨h.differentiable hL, fun l z => by rw [h.add_period hL hAH l z, zpow_natCast]⟩

theorem IsFnAt.add {k : ℤ} {s s' t : LB.Sec (LPow A L k T)} {θ θ' : (Fin g → ℂ) → ℂ}
    (h : IsFnAt u p k s θ) (h' : IsFnAt u p k s' θ') (ht : ∀ j, t.f j = s.f j + s'.f j) :
    IsFnAt u p k t (θ + θ') := fun j z hj => by
  rw [ht j, valAt'_add _ hj, h j z hj, h' j z hj, Pi.add_apply, add_mul]

theorem IsFnAt.liftFun_mul {k : ℤ} {s t : LB.Sec (LPow A L k T)} {θ : (Fin g → ℂ) → ℂ}
    (h : IsFnAt u p k s θ) (r : Γ(T.left, ⊤)) (ht : ∀ j, t.f j = liftFun A _ r * s.f j) :
    IsFnAt u p k t (valAt' p.left ⊤ r • θ) := fun j z hj => by
  rw [ht j, valAt'_mul _ hj, valAt'_liftFun u p hj, h j z hj, Pi.smul_apply, smul_eq_mul,
    _root_.mul_assoc]

theorem IsFnAt.sum_liftFun_mul {k : ℤ} {I : Type*} (F : Finset I) {s : I → LB.Sec (LPow A L k T)}
    {t : LB.Sec (LPow A L k T)} {θ : I → (Fin g → ℂ) → ℂ} (h : ∀ i ∈ F, IsFnAt u p k (s i) (θ i))
    (r : I → Γ(T.left, ⊤)) (ht : ∀ j, t.f j = ∑ i ∈ F, liftFun A _ (r i) * (s i).f j) :
    IsFnAt u p k t (∑ i ∈ F, valAt' p.left ⊤ (r i) • θ i) := fun j z hj => by
  rw [ht j, valAt'_sum _ hj, Finset.sum_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [valAt'_mul _ hj, valAt'_liftFun u p hj, h i hi j z hj, Pi.smul_apply, smul_eq_mul,
    _root_.mul_assoc]

variable (u p)

theorem isFnAt_zero (k : ℤ) : IsFnAt u p k (H1.SectionArithmetic.secZero (LPow A L k T)) 0 := fun j z hj => by
  rw [Pi.zero_apply, zero_mul, valAt'_eq_valHom _ hj]
  exact map_zero _

def fnAtHom (hL : L.IsLB) (k : ℤ) :
    SecM A L k T →ₛₗ[valHom p.left ⊤ (fun _ _ => trivial)] ((Fin g → ℂ) → ℂ) where
  toFun s := fnAt u p hL k (SecM.toSec A s)
  map_add' s s' := ((isFnAt_iff_eq_fnAt u p hL).1
    ((isFnAt_fnAt u p hL k (SecM.toSec A s)).add (isFnAt_fnAt u p hL k (SecM.toSec A s'))
      (t := SecM.toSec A (s + s')) fun _ => rfl)).symm
  map_smul' r s := by
    refine Eq.trans ((isFnAt_iff_eq_fnAt u p hL).1
      ((isFnAt_fnAt u p hL k (SecM.toSec A s)).liftFun_mul r
        (t := SecM.toSec A (r • s)) fun _ => rfl)).symm ?_
    exact congrArg (· • fnAt u p hL k (SecM.toSec A s)) (valAt'_eq_valHom p.left _ r)

theorem fnAtHom_apply (hL : L.IsLB) (k : ℤ) (s : SecM A L k T) :
    fnAtHom u p hL k s = fnAt u p hL k (SecM.toSec A s) := rfl

variable (A L) in

def secOfFun (r : Γ(T.left, ⊤)) : LB.Sec (LPow A L 0 T) where
  f j := liftFun A _ r
  compat j j' := by
    have : (LPow A L 0 T).g j j' = 1 := by
      unfold LPow LB.LinComb
      dsimp only
      exact Finset.prod_eq_one fun _ _ => zpow_zero _
    rw [this, Units.val_one, _root_.one_mul]
    exact (res_liftHom A _ r).trans (res_liftHom A _ r).symm

theorem isFnAt_secOfFun (r : Γ(T.left, ⊤)) :
    IsFnAt u p 0 (secOfFun A L r) (fun _ => valAt' p.left ⊤ r) := fun j z hj => by
  rw [zpow_zero, _root_.mul_one]
  exact valAt'_liftFun u p hj r

variable (L) in

def toFibre (n : ℕ) (s : LB.Sec (LPow A L n T)) : (lbPow L n).Sec :=
  pullPow L (K := Fin 1) (K' := PUnit) (fibreIncl A p).left (fibreIncl_snd p) n s

variable (A L T) in

def ofFibre (n : ℕ) (s : (lbPow L n).Sec) : LB.Sec (LPow A L n T) :=
  pullPow L (K := PUnit) (K' := Fin 1) (snd T A).left (Category.comp_id _) n s

omit [GrpObj A] in

theorem toFibre_ofFibre (n : ℕ) (s : (lbPow L n).Sec) : toFibre L p n (ofFibre A L T n s) = s :=
  pullPow_pullPow L _ _ _ _ (fibreIncl_snd p) _ s

omit [GrpObj A] in

theorem ofFibre_toFibre [IsIso p] (n : ℕ) (s : LB.Sec (LPow A L n T)) :
    ofFibre A L T n (toFibre L p n s) = s :=
  pullPow_pullPow L _ _ _ _ (snd_fibreIncl p) _ s

variable (L) in

def fibreEquiv [IsIso p] (n : ℕ) : LB.Sec (LPow A L n T) ≃ (lbPow L n).Sec where
  toFun := toFibre L p n
  invFun := ofFibre A L T n
  left_inv := ofFibre_toFibre p n
  right_inv := toFibre_ofFibre p n

theorem isFnAt_iff_isFnPow (n : ℕ) (s : LB.Sec (LPow A L n T)) (θ : (Fin g → ℂ) → ℂ) :
    IsFnAt u p n s θ ↔ u.IsFnPow n (toFibre L p n s) θ := by
  have hm : ∀ (i : L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow L n).U (fun _ => i) ↔
      ⊤ ≤ exAt u p z ⁻¹ᵁ (LPow A L n T).U (fun _ => i) := fun i z =>
    (le_wchart_unique L (K := PUnit) (u.ex z).left (𝟙 _) (fun _ => i)).trans
      (exAt_mem_chart_iff u p n (fun _ => i) z).symm
  have hv : ∀ (i : L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow L n).U (fun _ => i) →
      valAt' (u.ex z).left ((lbPow L n).U fun _ => i) ((toFibre L p n s).f fun _ => i) =
        valAt' (exAt u p z) ((LPow A L n T).U fun _ => i) (s.f fun _ => i) := fun i z hz => by
    rw [← ex_fibreIncl]
    exact valAt'_pullPow L _ _ _ s _ (fun _ : PUnit => i) hz
  constructor
  · intro h j z hj
    exact (hv (j PUnit.unit) z hj).trans
      ((h (fun _ => j PUnit.unit) z ((hm _ z).1 hj)).trans (by rw [zpow_natCast]))
  · intro h j z hj
    obtain ⟨i, rfl⟩ : ∃ i, j = fun _ => i :=
      ⟨j 0, funext fun k => congrArg j (Subsingleton.elim _ _)⟩
    have hj' := (hm i z).2 hj
    exact (hv i z hj').symm.trans ((h _ z hj').trans (by rw [zpow_natCast]))

theorem isFnAt_ofFibre_iff (n : ℕ) (s : (lbPow L n).Sec) (θ : (Fin g → ℂ) → ℂ) :
    IsFnAt u p n (ofFibre A L T n s) θ ↔ u.IsFnPow n s θ := by
  rw [isFnAt_iff_isFnPow, toFibre_ofFibre]

theorem existsUnique_sec_isFnAt [IsIso p] {n : ℕ} {θ : (Fin g → ℂ) → ℂ}
    (h : ∃! s, u.IsFnPow n s θ) : ∃! s : LB.Sec (LPow A L n T), IsFnAt u p n s θ := by
  obtain ⟨s, hs, huniq⟩ := h
  refine ⟨ofFibre A L T n s, (isFnAt_ofFibre_iff u p n s θ).2 hs, fun s' hs' => ?_⟩
  rw [← huniq _ ((isFnAt_iff_isFnPow u p n s' θ).1 hs'), ofFibre_toFibre]

variable {u p}

theorem mem_ptChart_iff {x : T ⟶ A} {z : Fin g → ℂ} (hx : p ≫ x = u.ex z) (j : Fin 1 → L.ι) :
    ⊤ ≤ p.left ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => x.left) j ↔ ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j 0) := by
  refine (le_wchart_unique L p.left x.left j).trans ?_
  rw [← Over.comp_left, hx]
  rfl

theorem IsFnAt.valAt'_ptSecT {k : ℤ} {s : LB.Sec (LPow A L k T)} {θ : (Fin g → ℂ) → ℂ}
    (h : IsFnAt u p k s θ) {x : T ⟶ A} {z : Fin g → ℂ} (hx : p ≫ x = u.ex z) (j : Fin 1 → L.ι)
    (hj : ⊤ ≤ p.left ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => x.left) j) :
    valAt' p.left (LB.wchart L (fun _ : Fin 1 => x.left) j)
      ((T.left.presheaf.map (homOfLE (val_le A L x j)).op).hom
        (((ptSecT A x).left.app _).hom (s.f j))) = θ z * u.fr (j 0) z ^ k := by
  refine (valAt'_appLE' p.left (ptSecT A x).left (val_le A L x j) hj _).trans ?_
  rw [comp_ptSecT u p hx]
  exact h j z ((exAt_mem_chart_iff u p k j z).2 ((mem_ptChart_iff hx j).1 hj))

theorem IsFnAt.value_mul_frame {k : ℤ} {s : LB.Sec (LPow A L k T)} {θ : (Fin g → ℂ) → ℂ}
    (h : IsFnAt u p k s θ) {x : T ⟶ A} {z : Fin g → ℂ} (hx : p ≫ x = u.ex z)
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => k))}
    {v : Γ(T.left, ⊤)} (hv : IsValueAt A L k s x τ v) (j : Fin 1 → L.ι)
    (hj : ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j 0)) :
    valAt' p.left ⊤ v * valAt' p.left (LB.wchart L (fun _ : Fin 1 => x.left) j) (τ.s j).val =
      θ z * u.fr (j 0) z ^ k := by
  have hj' := (mem_ptChart_iff hx j).2 hj
  rw [← h.valAt'_ptSecT hx j hj', hv j, valAt'_mul _ hj', valAt'_res _ _ hj']

theorem IsFnAt.isValueAt_of_isIso [IsIso p] {k : ℤ} {s : LB.Sec (LPow A L k T)}
    {θ : (Fin g → ℂ) → ℂ} (h : IsFnAt u p k s θ) {x : T ⟶ A} {z : Fin g → ℂ}
    (hx : p ≫ x = u.ex z)
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => k))}
    {v : Γ(T.left, ⊤)} (hv : ∀ j : Fin 1 → L.ι, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j 0) →
      valAt' p.left ⊤ v * valAt' p.left (LB.wchart L (fun _ : Fin 1 => x.left) j) (τ.s j).val =
        θ z * u.fr (j 0) z ^ k) : IsValueAt A L k s x τ v := by
  intro j
  have : IsIso (show Sp ℂ ⟶ T.left from p.left) :=
    inferInstanceAs (IsIso ((Over.forget _).map p))
  refine ext_of_valAt'_of_isIso (show Sp ℂ ⟶ T.left from p.left) fun hj => ?_
  refine (h.valAt'_ptSecT hx j hj).trans ((hv j ((mem_ptChart_iff hx j).1 hj)).symm.trans ?_)
  exact ((valAt'_mul p.left hj _ _).trans (congrArg (· * _) (valAt'_res p.left _ hj v))).symm

variable (u p) in

theorem comp_one_eq_ex_zero : p ≫ (1 : T ⟶ A) = u.ex 0 := by
  rw [ex_zero, MonObj.comp_one]

variable (p) in

theorem valAt'_rigT {rig : LB.Gen (L.pull (eSec A))} (hrig : u.IsRig rig) (k : ℤ)
    (j : Fin 1 → L.ι) (hj : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ L.U (j 0)) :
    valAt' p.left (LB.wchart L (fun _ : Fin 1 => (1 : T ⟶ A).left) j)
      ((rigT A L rig T k).s j).val = u.fr (j 0) 0 ^ k := by
  have hj' := (mem_ptChart_iff (comp_one_eq_ex_zero u p) j).2 hj
  have hp : p.left ≫ T.hom = 𝟙 (Sp ℂ) := Over.w p
  have h0 : ⊤ ≤ (L.pull (eSec A)).U (fun _ => j 0) := by
    rw [ex_zero] at hj
    exact fun _ hy => Set.mem_iInter.2 fun _ => hj hy
  refine (valAt'_unit_zpow p.left hj' _ k).trans (congrArg (· ^ k) ?_)
  refine (valAt'_appLE' p.left T.hom (rigT_le A L j) hj' _).trans ?_
  rw [hp]
  exact (hrig (fun _ => j 0) h0).symm

theorem IsFnAt.value_origin (hL : L.IsLB) {rig : LB.Gen (L.pull (eSec A))} (hrig : u.IsRig rig)
    {k : ℤ} {s : LB.Sec (LPow A L k T)} {θ : (Fin g → ℂ) → ℂ} (h : IsFnAt u p k s θ)
    {v : Γ(T.left, ⊤)} (hv : IsValueAt A L k s 1 (rigT A L rig T k) v) :
    valAt' p.left ⊤ v = θ 0 := by
  obtain ⟨i, hi⟩ := exists_chart u valueRules hL 0
  have h1 := h.value_mul_frame (comp_one_eq_ex_zero u p) hv (fun _ => i) hi
  rw [valAt'_rigT p hrig k (fun _ => i) hi] at h1
  exact mul_right_cancel₀ (zpow_ne_zero k (u.fr_ne i 0 hi)) h1

theorem IsFnAt.isValueAt_origin_iff [IsIso p] (hL : L.IsLB) {rig : LB.Gen (L.pull (eSec A))}
    (hrig : u.IsRig rig) {k : ℤ} {s : LB.Sec (LPow A L k T)} {θ : (Fin g → ℂ) → ℂ}
    (h : IsFnAt u p k s θ) (v : Γ(T.left, ⊤)) :
    IsValueAt A L k s 1 (rigT A L rig T k) v ↔ valAt' p.left ⊤ v = θ 0 :=
  ⟨h.value_origin hL hrig, fun hv => h.isValueAt_of_isIso (comp_one_eq_ex_zero u p) fun j hj => by
    rw [valAt'_rigT p hrig k j hj, hv]⟩

theorem IsFnAt.twistPull {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A} {hm : ψ ≫ snd T A = m} {a b : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])}
    {s : LB.Sec (LPow A L b T)} {s' : LB.Sec (LPow A L a T)} {θ θ' : (Fin g → ℂ) → ℂ}
    (h : IsFnAt u p b s θ) (h' : IsFnAt u p a s' θ') (ht : IsTwistPull A L ψ m hm a b α s s')
    {z w : Fin g → ℂ} (hw : exAt u p z ≫ ψ.left = exAt u p w) (j : Fin 2 → L.ι)
    (hj : ⊤ ≤ exAt u p z ⁻¹ᵁ LB.wchart L ![(snd T A).left, m.left] j) :
    θ' z * u.fr (j 0) z ^ a =
      valAt' (exAt u p z) (LB.wchart L ![(snd T A).left, m.left] j) (α.s j).val *
        (θ w * u.fr (j 1) w ^ b) := by
  have h0 : ⊤ ≤ exAt u p z ⁻¹ᵁ (LPow A L a T).U (fun _ => j 0) :=
    fun _ hy => chart_le_zero A L m j (hj hy)
  have h1 : ⊤ ≤ exAt u p w ⁻¹ᵁ (LPow A L b T).U (fun _ => j 1) := by
    rw [← hw]
    exact fun _ hy => chart_le_pull A L ψ m hm j (hj hy)
  refine (h' _ z h0).symm.trans ((valAt'_res _ (chart_le_zero A L m j) hj _).symm.trans ?_)
  refine (congrArg _ (ht j)).trans ((valAt'_mul _ hj _ _).trans (congrArg (_ * ·) ?_))
  refine (valAt'_appLE' _ ψ.left (chart_le_pull A L ψ m hm j) hj _).trans ?_
  rw [hw]
  exact h _ w h1

theorem isFnAt_iff_of_isPullSec {T' : Over (Sp ℂ)} {p' : 𝟙_ (Over (Sp ℂ)) ⟶ T'}
    {h : T' ⊗ A ⟶ T ⊗ A} {hh : h ≫ snd T A = snd T' A} {k : ℤ} {s : LB.Sec (LPow A L k T)}
    {s' : LB.Sec (LPow A L k T')} (hs : IsPullSec A L k h hh s s')
    (hp : ∀ z, exAt u p' z ≫ h.left = exAt u p z) (θ : (Fin g → ℂ) → ℂ) :
    IsFnAt u p' k s' θ ↔ IsFnAt u p k s θ := by
  refine forall_congr' fun j => forall_congr' fun z => ?_
  rw [exAt_mem_chart_iff u p k j z, ← exAt_mem_chart_iff u p' k j z]
  refine imp_congr_right fun hj => ?_
  rw [hs j, ← hp z]
  exact Eq.congr_left (valAt'_appLE' _ h.left (chart_le_res A L h hh k j) hj _)

end Fibre

section Base

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

def basePt : 𝟙_ (Over (Sp ℂ)) ⟶ baseOver (Sp ℂ) := Over.homMk (𝟙 (Sp ℂ)) (Category.id_comp _)

theorem basePt_left : basePt.left = 𝟙 (Sp ℂ) := rfl

instance isIso_basePt : IsIso basePt := inferInstanceAs (IsIso (𝟙 (𝟙_ (Over (Sp ℂ)))))

abbrev exT (z : Fin g → ℂ) : Sp ℂ ⟶ (baseOver (Sp ℂ) ⊗ A).left := exAt u basePt z

abbrev IsFnT (k : ℤ) (s : LB.Sec (LPow A L k (baseOver (Sp ℂ)))) (θ : (Fin g → ℂ) → ℂ) : Prop :=
  IsFnAt u basePt k s θ

theorem isFnT_iff (k : ℤ) (s : LB.Sec (LPow A L k (baseOver (Sp ℂ)))) (θ : (Fin g → ℂ) → ℂ) :
    IsFnT u k s θ ↔ ∀ (j : Fin 1 → L.ι) z, ⊤ ≤ exT u z ⁻¹ᵁ (LPow A L k (baseOver (Sp ℂ))).U j →
      valAt' (exT u z) ((LPow A L k (baseOver (Sp ℂ))).U j) (s.f j) = θ z * u.fr (j 0) z ^ k :=
  Iff.rfl

abbrev exUnit (z : Fin g → ℂ) : Sp ℂ ⟶ (𝟙_ (Over (Sp ℂ)) ⊗ A).left := exAt u (𝟙 _) z

abbrev IsFnUnit (k : ℤ) (s : LB.Sec (LPow A L k (𝟙_ (Over (Sp ℂ))))) (θ : (Fin g → ℂ) → ℂ) : Prop :=
  IsFnAt u (𝟙 _) k s θ

theorem exUnit_eq_exT (z : Fin g → ℂ) : exUnit u z = exT u z := rfl

theorem isFnUnit_iff_isFnT (k : ℤ) (s : LB.Sec (LPow A L k (𝟙_ (Over (Sp ℂ)))))
    (θ : (Fin g → ℂ) → ℂ) : IsFnUnit u k s θ ↔ IsFnT u k s θ := Iff.rfl

theorem exT_snd (z : Fin g → ℂ) : exT u z ≫ (snd (baseOver (Sp ℂ)) A).left = (u.ex z).left :=
  exAt_snd u basePt z

theorem eq_exT_of_snd {z : Fin g → ℂ} {y : Sp ℂ ⟶ (baseOver (Sp ℂ) ⊗ A).left}
    (hy : y ≫ (snd (baseOver (Sp ℂ)) A).left = (u.ex z).left) : y = exT u z := by
  have := isIso_snd_left (A := A) basePt
  rw [← cancel_mono (snd (baseOver (Sp ℂ)) A).left, hy, exT_snd]

abbrev constT (a : ℂ) : Γ((baseOver (Sp ℂ)).left, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a

abbrev numT (r : Γ((baseOver (Sp ℂ)).left, ⊤)) : ℂ :=
  (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom r

theorem numT_constT (a : ℂ) : numT (constT a) = a :=
  (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv_hom_id_apply a

theorem constT_numT (r : Γ((baseOver (Sp ℂ)).left, ⊤)) : constT (numT r) = r :=
  (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom_inv_id_apply r

theorem valAt'_basePt (r : Γ((baseOver (Sp ℂ)).left, ⊤)) : valAt' basePt.left ⊤ r = numT r :=
  valAt'_id_top r

theorem existsUnique_isFnT (hL : L.IsLB) (k : ℤ) (s : LB.Sec (LPow A L k (baseOver (Sp ℂ)))) :
    ∃! θ, IsFnT u k s θ := existsUnique_isFnAt u basePt hL k s

variable {u}

theorem IsFnT.differentiable (hL : L.IsLB) {k : ℤ} {s : LB.Sec (LPow A L k (baseOver (Sp ℂ)))}
    {θ : (Fin g → ℂ) → ℂ} (h : IsFnT u k s θ) : Differentiable ℂ θ :=
  IsFnAt.differentiable hL h

theorem IsFnT.add_period (hL : L.IsLB) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    (hAH : u.IsAH Hm χ) {k : ℤ} {s : LB.Sec (LPow A L k (baseOver (Sp ℂ)))}
    {θ : (Fin g → ℂ) → ℂ} (h : IsFnT u k s θ) (l : u.Λ) (z : Fin g → ℂ) :
    θ (z + l) =
      (χ l * Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l)) ^ k * θ z :=
  IsFnAt.add_period hL hAH h l z

theorem IsFnT.isThetaFn (hL : L.IsLB) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    (hAH : u.IsAH Hm χ) {n : ℕ} {s : LB.Sec (LPow A L n (baseOver (Sp ℂ)))}
    {θ : (Fin g → ℂ) → ℂ} (h : IsFnT u n s θ) : u.IsThetaFn Hm χ n θ :=
  IsFnAt.isThetaFn hL hAH h

theorem IsFnT.add {k : ℤ} {s s' t : LB.Sec (LPow A L k (baseOver (Sp ℂ)))}
    {θ θ' : (Fin g → ℂ) → ℂ} (h : IsFnT u k s θ) (h' : IsFnT u k s' θ')
    (ht : ∀ j, t.f j = s.f j + s'.f j) : IsFnT u k t (θ + θ') :=
  IsFnAt.add h h' ht

theorem IsFnT.liftFun_mul {k : ℤ} {s t : LB.Sec (LPow A L k (baseOver (Sp ℂ)))}
    {θ : (Fin g → ℂ) → ℂ} (h : IsFnT u k s θ) (r : Γ((baseOver (Sp ℂ)).left, ⊤))
    (ht : ∀ j, t.f j = liftFun A _ r * s.f j) : IsFnT u k t (numT r • θ) :=
  valAt'_basePt r ▸ IsFnAt.liftFun_mul h r ht

theorem IsFnT.sum_liftFun_mul {k : ℤ} {I : Type*} (F : Finset I)
    {s : I → LB.Sec (LPow A L k (baseOver (Sp ℂ)))} {t : LB.Sec (LPow A L k (baseOver (Sp ℂ)))}
    {θ : I → (Fin g → ℂ) → ℂ} (h : ∀ i ∈ F, IsFnT u k (s i) (θ i))
    (r : I → Γ((baseOver (Sp ℂ)).left, ⊤))
    (ht : ∀ j, t.f j = ∑ i ∈ F, liftFun A _ (r i) * (s i).f j) :
    IsFnT u k t (∑ i ∈ F, numT (r i) • θ i) := by
  simpa only [valAt'_basePt] using IsFnAt.sum_liftFun_mul F h r ht

theorem IsFnT.isValueAt_origin_iff (hL : L.IsLB) {rig : LB.Gen (L.pull (eSec A))}
    (hrig : u.IsRig rig) {k : ℤ} {s : LB.Sec (LPow A L k (baseOver (Sp ℂ)))}
    {θ : (Fin g → ℂ) → ℂ} (h : IsFnT u k s θ) (v : Γ((baseOver (Sp ℂ)).left, ⊤)) :
    IsValueAt A L k s 1 (rigT A L rig (baseOver (Sp ℂ)) k) v ↔ numT v = θ 0 :=
  valAt'_basePt v ▸ IsFnAt.isValueAt_origin_iff hL hrig h v

theorem IsFnT.isValueAt_origin (hL : L.IsLB) {rig : LB.Gen (L.pull (eSec A))}
    (hrig : u.IsRig rig) {k : ℤ} {s : LB.Sec (LPow A L k (baseOver (Sp ℂ)))}
    {θ : (Fin g → ℂ) → ℂ} (h : IsFnT u k s θ) :
    IsValueAt A L k s 1 (rigT A L rig (baseOver (Sp ℂ)) k) (constT (θ 0)) :=
  (h.isValueAt_origin_iff hL hrig _).2 (numT_constT _)

variable (u)

theorem isFnT_iff_isFnPow (n : ℕ) (s : LB.Sec (LPow A L n (baseOver (Sp ℂ))))
    (θ : (Fin g → ℂ) → ℂ) : IsFnT u n s θ ↔ u.IsFnPow n (fibreEquiv L basePt n s) θ :=
  isFnAt_iff_isFnPow u basePt n s θ

theorem existsUnique_sec_isFnT {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} {n : ℕ}
    (hsec : ∀ θ, u.IsThetaFn Hm χ n θ → ∃! s, u.IsFnPow n s θ) {θ : (Fin g → ℂ) → ℂ}
    (hθ : u.IsThetaFn Hm χ n θ) :
    ∃! s : LB.Sec (LPow A L n (baseOver (Sp ℂ))), IsFnT u n s θ :=
  existsUnique_sec_isFnAt u basePt (hsec θ hθ)

theorem IsFnT.sec_eq (hL : L.IsLB) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    (hAH : u.IsAH Hm χ) {n : ℕ} (hsec : ∀ θ, u.IsThetaFn Hm χ n θ → ∃! s, u.IsFnPow n s θ)
    {s s' : LB.Sec (LPow A L n (baseOver (Sp ℂ)))} {θ : (Fin g → ℂ) → ℂ} (h : IsFnT u n s θ)
    (h' : IsFnT u n s' θ) : s = s' :=
  (existsUnique_sec_isFnT u hsec (h.isThetaFn hL hAH)).unique h h'

theorem isFnT_zero (k : ℤ) :
    IsFnT u k (H1.SectionArithmetic.secZero (LPow A L k (baseOver (Sp ℂ)))) 0 := isFnAt_zero u basePt k

theorem isFnT_const (a : ℂ) : IsFnT u 0 (secOfFun A L (constT a)) (fun _ => a) := by
  have h := isFnAt_secOfFun u basePt (constT a)
  rwa [valAt'_basePt, numT_constT] at h

end Base

def zeroUnif : HolUnif (Inh.zeroPolAV (Sp ℂ)).A (Inh.zeroPolAV (Sp ℂ)).L 0 where
  ex _ := 1
  ex_add _ _ := (_root_.mul_one _).symm
  ex_onto x := ⟨0, toUnit_unique _ _⟩
  Λ := ⊤
  ker _ := ⟨fun _ => trivial, fun _ => rfl⟩
  discrete := inferInstance
  full := by simp
  hol _ _ := ⟨isOpen_discrete _, differentiableOn_const _⟩
  fr _ _ := 1
  fr_hol _ := differentiableOn_const _
  fr_ne _ _ _ := one_ne_zero
  fr_compat _ _ _ h := by
    rw [valAt'_eq_valHom _ h, _root_.mul_one]
    exact (map_one _).symm

theorem zeroUnif_isAH : zeroUnif.IsAH 0 (fun _ => 1) :=
  ⟨Matrix.isHermitian_zero, fun z hz => (hz (Subsingleton.elim _ _)).elim, fun _ => norm_one,
    fun l i z _ => by simp [zeroUnif]⟩

example (P : PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (a b : ℂ) :
    IsFnT u 0 (secOfFun P.A P.L (constT a)) (fun _ => b) ↔ a = b :=
  ⟨fun h => congrFun ((isFnT_const u a).unique P.isLB h) 0, fun h => h ▸ isFnT_const u a⟩

example (P : PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (k : ℤ) (θ : (Fin P.g → ℂ) → ℂ) :
    IsFnT u k (H1.SectionArithmetic.secZero (LPow P.A P.L k (baseOver (Sp ℂ)))) θ ↔ θ = 0 :=
  ⟨fun h => h.unique P.isLB (isFnT_zero u k), fun h => h ▸ isFnT_zero u k⟩

example : IsFnT zeroUnif 0 (secOfFun _ _ (constT 2)) (fun _ => 2) ∧
    ¬ IsFnT zeroUnif 0 (secOfFun _ _ (constT 2)) (fun _ => 3) :=
  ⟨isFnT_const _ 2, fun h => by
    have := congrFun ((isFnT_const zeroUnif 2).unique (Inh.zeroPolAV (Sp ℂ)).isLB h) 0
    norm_num at this⟩

theorem exists_unif_isFnT (h : ThetaUnifAV) (P : PolAV (Sp ℂ))
    (rig : LB.Gen (P.L.pull (eSec P.A))) (hrig : rig.IsGen) :
    ∃ (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ),
      u.IsAH Hm χ ∧ u.IsRig rig ∧ ∀ n : ℕ,
        (∀ s : LB.Sec (LPow P.A P.L n (baseOver (Sp ℂ))),
          ∃! θ, u.IsThetaFn Hm χ n θ ∧ IsFnT u n s θ) ∧
        ∀ θ, u.IsThetaFn Hm χ n θ →
          ∃! s : LB.Sec (LPow P.A P.L n (baseOver (Sp ℂ))), IsFnT u n s θ := by
  obtain ⟨u, Hm, χ, -, hAH, hr, -, -, -, hsec, -⟩ := h P rig hrig
  refine ⟨u, Hm, χ, hAH, hr, fun n => ⟨fun s => ?_, fun θ hθ =>
    existsUnique_sec_isFnT u (hsec n).2 hθ⟩⟩
  simpa only [isFnT_iff_isFnPow] using (hsec n).1 (fibreEquiv P.L basePt n s)

end GlobalTheory.ThetaFn
