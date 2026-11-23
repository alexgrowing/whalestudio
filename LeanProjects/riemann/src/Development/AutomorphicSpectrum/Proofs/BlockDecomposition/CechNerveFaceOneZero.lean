import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open CategoryTheory.ComposableArrows

namespace GlobalTheory.CompanionTheory.Dict

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

def L0 : Cn F 0 →ₗ[R] C0 F where
  toFun f T := f (mk₀ T)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def L1 : Cn F 1 →ₗ[R] C1 F where
  toFun f _ _ φ := f (mk₁ φ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def L2 : Cn F 2 →ₗ[R] C2 F where
  toFun f _ _ _ φ ψ := f (mk₂ φ ψ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def L3 : Cn F 3 →ₗ[R] C3 F where
  toFun f _ _ _ _ φ ψ χ := f (mk₃ φ ψ χ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem L0_bijective_cochain : Function.Bijective (L0 F) := by
  refine ⟨fun f g h => funext fun c => ?_, fun e => ⟨fun c => e (c.obj (Fin.last 0)), rfl⟩⟩
  obtain ⟨X, rfl⟩ := ComposableArrows.mk₀_surjective c
  exact congr_fun h X

theorem L1_bijective_cochain : Function.Bijective (L1 F) := by
  refine ⟨fun f g h => funext fun c => ?_, fun e => ⟨fun c => e (c.obj 0) (c.obj (Fin.last 1))
    (c.map (homOfLE (Fin.zero_le _))), rfl⟩⟩
  obtain ⟨X₀, X₁, φ, rfl⟩ := ComposableArrows.mk₁_surjective c
  exact congr_fun (congr_fun (congr_fun h X₀) X₁) φ

theorem L2_bijective_cochain : Function.Bijective (L2 F) := by
  refine ⟨fun f g h => funext fun c => ?_, fun e => ⟨fun c => e (c.obj 0) (c.obj 1) (c.obj (Fin.last 2))
    (c.map (homOfLE (show (0 : Fin 3) ≤ 1 by decide)))
    (c.map (homOfLE (show (1 : Fin 3) ≤ Fin.last 2 by decide))), rfl⟩⟩
  obtain ⟨X₀, X₁, X₂, φ, ψ, rfl⟩ := ComposableArrows.mk₂_surjective c
  exact congr_fun (congr_fun (congr_fun (congr_fun (congr_fun h X₀) X₁) X₂) φ) ψ

theorem L3_bijective_cochain : Function.Bijective (L3 F) := by
  refine ⟨fun f g h => funext fun c => ?_, fun e => ⟨fun c => e (c.obj 0) (c.obj 1) (c.obj 2)
    (c.obj (Fin.last 3)) (c.map (homOfLE (show (0 : Fin 4) ≤ 1 by decide)))
    (c.map (homOfLE (show (1 : Fin 4) ≤ 2 by decide)))
    (c.map (homOfLE (show (2 : Fin 4) ≤ Fin.last 3 by decide))), rfl⟩⟩
  obtain ⟨X₀, X₁, X₂, X₃, φ, ψ, χ, rfl⟩ := ComposableArrows.mk₃_surjective c
  exact congr_fun (congr_fun (congr_fun (congr_fun (congr_fun (congr_fun (congr_fun h X₀) X₁) X₂) X₃) φ) ψ) χ

theorem cof_eq {n : ℕ} (i : Fin (n + 2)) (c : Fin (n + 2) ⥤ C) (c' : Fin (n + 1) ⥤ C)
    (h : face i c = c') (u : c'.obj (Fin.last n) ⟶ c.obj (Fin.last (n + 1)))
    (hu : HEq (c.map (homOfLE (Fin.le_last (i.succAbove (Fin.last n))))) u) (f : Cn F n) :
    cof F n i f c = mp F u (f c') := by
  subst h
  obtain rfl := eq_of_heq hu
  rfl

theorem dn0 (f : Cn F 0) (c : Fin 2 ⥤ C) : dn F 0 f c = cof F 0 0 f c - cof F 0 1 f c := by
  simp [dn, Fin.sum_univ_two, sub_eq_add_neg]

theorem dn1 (f : Cn F 1) (c : Fin 3 ⥤ C) :
    dn F 1 f c = cof F 1 0 f c - cof F 1 1 f c + cof F 1 2 f c := by
  simp [dn, Fin.sum_univ_three, pow_succ, sub_eq_add_neg]

theorem dn2 (f : Cn F 2) (c : Fin 4 ⥤ C) :
    dn F 2 f c = cof F 2 0 f c - cof F 2 1 f c + cof F 2 2 f c - cof F 2 3 f c := by
  simp [dn, Fin.sum_univ_four, pow_succ, sub_eq_add_neg]

theorem eq_mk₁ (c : ComposableArrows C 1) (x : c.left ⟶ c.right) (h : c.hom = x) : c = mk₁ x := by
  obtain ⟨X₀, X₁, g, rfl⟩ := ComposableArrows.mk₁_surjective c
  subst h
  rfl

theorem eq_mk₂ (c : ComposableArrows C 2) (x : c.obj' 0 ⟶ c.obj' 1) (y : c.obj' 1 ⟶ c.obj' 2)
    (hx : map' c 0 1 = x) (hy : map' c 1 2 = y) : c = mk₂ x y := by
  obtain ⟨X₀, X₁, X₂, g₀, g₁, rfl⟩ := ComposableArrows.mk₂_surjective c
  subst hx hy
  rfl

section Faces

variable {T T' T'' T''' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') (χ : T'' ⟶ T''')

theorem cech_nerve_face_one_zero : face 0 (mk₁ φ) = mk₀ T' := by
  exact ComposableArrows.ext₀ rfl
theorem cech_nerve_face_one_one : face 1 (mk₁ φ) = mk₀ T := by
  exact ComposableArrows.ext₀ rfl
theorem cech_nerve_face_two_zero : face 0 (mk₂ φ ψ) = mk₁ ψ := by
  exact eq_mk₁ (face 0 (mk₂ φ ψ)) ψ rfl
theorem cech_nerve_face_two_one : face 1 (mk₂ φ ψ) = mk₁ (φ ≫ ψ) := by
  exact eq_mk₁ (face 1 (mk₂ φ ψ)) (φ ≫ ψ) rfl
theorem cech_nerve_face_two_two : face 2 (mk₂ φ ψ) = mk₁ φ := by
  exact eq_mk₁ (face 2 (mk₂ φ ψ)) φ rfl
theorem face_zero_mk3 : face 0 (mk₃ φ ψ χ) = mk₂ ψ χ := by
  exact eq_mk₂ (face 0 (mk₃ φ ψ χ)) ψ χ rfl rfl
theorem face_one_mk3 : face 1 (mk₃ φ ψ χ) = mk₂ (φ ≫ ψ) χ := by
  exact eq_mk₂ (face 1 (mk₃ φ ψ χ)) (φ ≫ ψ) χ rfl rfl
theorem face_two_mk3 : face 2 (mk₃ φ ψ χ) = mk₂ φ (ψ ≫ χ) := by
  exact eq_mk₂ (face 2 (mk₃ φ ψ χ)) φ (ψ ≫ χ) rfl rfl
theorem face_three_mk3 : face 3 (mk₃ φ ψ χ) = mk₂ φ ψ := by
  exact eq_mk₂ (face 3 (mk₃ φ ψ χ)) φ ψ rfl rfl

end Faces

private theorem mp_id_apply (X : C) (x : F.obj X) : mp F (𝟙 X) x = x := by
  rw [mp, CategoryTheory.Functor.map_id]
  rfl

theorem L1_dn_zero_eq_d0_L0 (f : Cn F 0) : L1 F (dn F 0 f) = d0 F (L0 F f) := by
  funext T T' φ
  show dn F 0 f (mk₁ φ) = L0 F f T' - mp F φ (L0 F f T)
  rw [dn0, cof_eq F (n := 0) 0 (mk₁ φ) (mk₀ T') (cech_nerve_face_one_zero φ) (𝟙 T') HEq.rfl f,
    cof_eq F (n := 0) 1 (mk₁ φ) (mk₀ T) (cech_nerve_face_one_one φ) φ HEq.rfl f]
  show mp F (𝟙 T') (f (mk₀ T')) - mp F φ (f (mk₀ T)) = _
  rw [mp_id_apply F T' (f (mk₀ T'))]
  rfl

theorem L2_dn_one_eq_d1_L1 (f : Cn F 1) : L2 F (dn F 1 f) = d1 F (L1 F f) := by
  funext T T' T'' φ ψ
  show dn F 1 f (mk₂ φ ψ) = mp F ψ (L1 F f T T' φ) - L1 F f T T'' (φ ≫ ψ) + L1 F f T' T'' ψ
  rw [dn1, cof_eq F (n := 1) 0 (mk₂ φ ψ) (mk₁ ψ) (cech_nerve_face_two_zero φ ψ) (𝟙 T'') HEq.rfl f,
    cof_eq F (n := 1) 1 (mk₂ φ ψ) (mk₁ (φ ≫ ψ)) (cech_nerve_face_two_one φ ψ) (𝟙 T'') HEq.rfl f,
    cof_eq F (n := 1) 2 (mk₂ φ ψ) (mk₁ φ) (cech_nerve_face_two_two φ ψ) ψ HEq.rfl f]
  conv_lhs => rw [sub_add_comm]
  show mp F ψ (f (mk₁ φ)) - mp F (𝟙 T'') (f (mk₁ (φ ≫ ψ))) + mp F (𝟙 T'') (f (mk₁ ψ)) = _
  rw [mp_id_apply F T'' (f (mk₁ (φ ≫ ψ))), mp_id_apply F T'' (f (mk₁ ψ))]
  rfl

theorem L3_dn_two_eq_d2_L2 (f : Cn F 2) : L3 F (dn F 2 f) = d2 F (L2 F f) := by
  funext T T' T'' T''' φ ψ χ
  show dn F 2 f (mk₃ φ ψ χ) = L2 F f T' T'' T''' ψ χ - L2 F f T T'' T''' (φ ≫ ψ) χ +
    L2 F f T T' T''' φ (ψ ≫ χ) - mp F χ (L2 F f T T' T'' φ ψ)
  rw [dn2, cof_eq F (n := 2) 0 (mk₃ φ ψ χ) (mk₂ ψ χ) (face_zero_mk3 φ ψ χ) (𝟙 T''') HEq.rfl f,
    cof_eq F (n := 2) 1 (mk₃ φ ψ χ) (mk₂ (φ ≫ ψ) χ) (face_one_mk3 φ ψ χ) (𝟙 T''') HEq.rfl f,
    cof_eq F (n := 2) 2 (mk₃ φ ψ χ) (mk₂ φ (ψ ≫ χ)) (face_two_mk3 φ ψ χ) (𝟙 T''') HEq.rfl f,
    cof_eq F (n := 2) 3 (mk₃ φ ψ χ) (mk₂ φ ψ) (face_three_mk3 φ ψ χ) χ HEq.rfl f]
  show mp F (𝟙 T''') (f (mk₂ ψ χ)) - mp F (𝟙 T''') (f (mk₂ (φ ≫ ψ) χ)) +
    mp F (𝟙 T''') (f (mk₂ φ (ψ ≫ χ))) - mp F χ (f (mk₂ φ ψ)) = _
  rw [mp_id_apply F T''' (f (mk₂ ψ χ)), mp_id_apply F T''' (f (mk₂ (φ ≫ ψ) χ)),
    mp_id_apply F T''' (f (mk₂ φ (ψ ≫ χ)))]
  rfl

theorem dictSt : DictSt := by
  intro R _ C _ F
  refine ⟨LinearEquiv.ofBijective (L0 F) (L0_bijective_cochain F), LinearEquiv.ofBijective (L1 F) (L1_bijective_cochain F),
    LinearEquiv.ofBijective (L2 F) (L2_bijective_cochain F), LinearEquiv.ofBijective (L3 F) (L3_bijective_cochain F),
    fun _ _ => ?_, fun _ _ _ _ => ?_, fun _ _ _ _ _ _ => ?_, fun _ _ _ _ _ _ _ _ => ?_,
    fun f => ?_, fun f => ?_, fun f => ?_⟩ <;> simp only [LinearEquiv.ofBijective_apply]
  · rfl
  · rfl
  · rfl
  · rfl
  · exact L1_dn_zero_eq_d0_L0 F f
  · exact L2_dn_one_eq_d1_L1 F f
  · exact L3_dn_two_eq_d2_L2 F f

end GlobalTheory.CompanionTheory.Dict
