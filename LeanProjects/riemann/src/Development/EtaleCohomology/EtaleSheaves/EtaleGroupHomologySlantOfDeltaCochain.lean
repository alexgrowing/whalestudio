import Development.EtaleCohomology.EtaleSheaves.EtaleChapterDThree

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.t_D3Cut

abbrev BX (Γ : Type) [Group Γ] (X : Scheme.{0}) : Spc := cst (SingleObj Γ) ⨯ sch.obj X

def slantHom (R : Type) [CommRing R] {Γ : Type} [Group Γ] (X : Scheme.{0}) {m : ℕ} (c : (Fin m → Γ) →₀ R) :
    (free R).obj (yoneda.obj X) ⟶ (free R).obj ((BX Γ X).obj (op (SimplexCategory.mk m))) :=
  c.sum fun g r => (ULift.up r : ULift.{1} R) • (free R).map (grpPt X g)

def slantV (R : Type) [CommRing R] {Γ : Type} [Group Γ] (X : Scheme.{0}) {m : ℕ} (c : (Fin m → Γ) →₀ R) :
    ((chains R).obj (sch.obj X)).X 0 ⟶ ((chains R).obj (BX Γ X)).X (-(m : ℤ)) :=
  (((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).obj
      (((SimplicialObject.whiskering _ _).obj (free R)).obj (sch.obj X))).extendXIso
      ComplexShape.embeddingDownNat (i := 0) (i' := 0) (by simp)).hom ≫ slantHom R X c ≫
    (((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).obj
      (((SimplicialObject.whiskering _ _).obj (free R)).obj (BX Γ X))).extendXIso
      ComplexShape.embeddingDownNat (i := m) (i' := -(m : ℤ)) (by simp)).inv

def slantCo (R : Type) [CommRing R] {Γ : Type} [Group Γ] (X : Scheme.{0}) {m : ℕ} (c : (Fin m → Γ) →₀ R) :
    Cochain ((chains R).obj (sch.obj X)) ((chains R).obj (BX Γ X)) (-(m : ℤ)) :=
  Cochain.single (slantV R X c) (-(m : ℤ))

abbrev bd (R : Type) [CommRing R] {Γ : Type} [Group Γ] {m : ℕ} (b : (Fin (m + 1) → Γ) →₀ R) : (Fin m → Γ) →₀ R :=
  groupHomology.inhomogeneousChains.d (Rep.trivial R Γ R) m b

def Faces : Prop := ∀ (Γ : Type) [Group Γ] (X : Scheme.{0}) (m : ℕ) (g : Fin (m + 1) → Γ),
  grpPt X g ≫ (BX Γ X).δ 0 = grpPt X (fun i => g i.succ) ∧
  ∀ j : Fin (m + 1), grpPt X g ≫ (BX Γ X).δ j.succ = grpPt X (j.contractNth (· * ·) g)

def HomD : Prop := ∀ (R : Type) [CommRing R] (Γ : Type) [Group Γ] (X : Scheme.{0}) (m : ℕ) (b : (Fin (m + 1) → Γ) →₀ R),
  slantHom R X b ≫ ((chainsN R).obj (BX Γ X)).d (m + 1) m = slantHom R X (bd R b)

def DeltaCo : Prop := ∀ (R : Type) [CommRing R] (Γ : Type) [Group Γ] (X : Scheme.{0}),
  (∀ c : (Fin 0 → Γ) →₀ R, δ (-((0 : ℕ) : ℤ)) (-((0 : ℕ) : ℤ) + 1) (slantCo R X c) = 0) ∧
  ∀ (m : ℕ) (b : (Fin (m + 1) → Γ) →₀ R), δ (-((m + 1 : ℕ) : ℤ)) (-(m : ℤ)) (slantCo R X b) = slantCo R X (bd R b)

section
variable (R : Type) [CommRing R] {Γ : Type} [Group Γ] (X : Scheme.{0}) {m : ℕ}

theorem slantHom_zero : slantHom R X (0 : (Fin m → Γ) →₀ R) = 0 := Finsupp.sum_zero_index

theorem slantHom_single (g : Fin m → Γ) (r : R) :
    slantHom R X (Finsupp.single g r) = (ULift.up r : ULift.{1} R) • (free R).map (grpPt X g) :=
  Finsupp.sum_single_index (zero_smul (ULift.{1} R) _)

theorem slantHom_add (c c' : (Fin m → Γ) →₀ R) : slantHom R X (c + c') = slantHom R X c + slantHom R X c' :=
  Finsupp.sum_add_index' (fun _ => zero_smul (ULift.{1} R) _)
    (fun _ r s => add_smul (ULift.up r : ULift.{1} R) (ULift.up s) _)

theorem slantV_add (c c' : (Fin m → Γ) →₀ R) : slantV R X (c + c') = slantV R X c + slantV R X c' := by
  unfold slantV
  rw [slantHom_add]
  erw [Preadditive.add_comp, Preadditive.comp_add]

theorem slantCo_v (c : (Fin m → Γ) →₀ R) : (slantCo R X c).v 0 (-(m : ℤ)) (zero_add _) = slantV R X c :=
  Cochain.single_v _ _ _

theorem slantCo_v_ne (c : (Fin m → Γ) →₀ R) (p p' : ℤ) (h : p + -(m : ℤ) = p') (hp : p ≠ 0) :
    (slantCo R X c).v p p' h = 0 := Cochain.single_v_eq_zero _ _ _ _ _ hp

theorem slantCo_add (c c' : (Fin m → Γ) →₀ R) : slantCo R X (c + c') = slantCo R X c + slantCo R X c' := by
  ext p p' h : 1
  by_cases hp : p = 0
  · subst hp
    obtain rfl : p' = -(m : ℤ) := by omega
    rw [Cochain.add_v, slantCo_v, slantCo_v, slantCo_v, slantV_add]
  · rw [Cochain.add_v, slantCo_v_ne _ _ _ _ _ _ hp, slantCo_v_ne _ _ _ _ _ _ hp, slantCo_v_ne _ _ _ _ _ _ hp, add_zero]

theorem slantCo_zero : slantCo R X (0 : (Fin m → Γ) →₀ R) = 0 := by
  have h := slantCo_add R X (0 : (Fin m → Γ) →₀ R) 0
  rw [add_zero] at h
  exact left_eq_add.1 h

theorem isSlant_iff (c : (Fin m → Γ) →₀ R) (z) : IsSlant R X c z ↔ z.1 = slantCo R X c := by
  constructor
  · rintro ⟨h1, h2⟩
    ext p p' h : 1
    by_cases hp : p = 0
    · subst hp
      obtain rfl : p' = -(m : ℤ) := by omega
      rw [slantCo_v]; exact h2
    · rw [slantCo_v_ne _ _ _ _ _ _ hp]; exact h1 p p' h hp
  · intro h
    refine ⟨fun p p' hh hp => ?_, ?_⟩
    · rw [h]; exact slantCo_v_ne _ _ _ _ _ _ hp
    · rw [h]; exact slantCo_v _ _ _

end

theorem closed (h : DeltaCo) (R : Type) [CommRing R] (Γ : Type) [Group Γ] (X : Scheme.{0}) (m : ℕ)
    (c : groupHomology.cycles (Rep.trivial R Γ R) m) :
    δ (-(m : ℤ)) (-(m : ℤ) + 1) (slantCo R X (groupHomology.iCycles (Rep.trivial R Γ R) m c)) = 0 := by
  cases m with
  | zero => exact (h R Γ X).1 _
  | succ m =>
    have h1 := (h R Γ X).2 m (groupHomology.iCycles (Rep.trivial R Γ R) (m + 1) c)
    have h2 : bd R (groupHomology.iCycles (Rep.trivial R Γ R) (m + 1) c) = 0 := by
      have h3 := ConcreteCategory.congr_hom
        ((groupHomology.inhomogeneousChains (Rep.trivial R Γ R)).iCycles_d (m + 1) m) c
      rw [groupHomology.inhomogeneousChains.d_def] at h3
      exact h3
    rw [h2, slantCo_zero] at h1
    have h4 : ∀ k : ℤ, k = -(m : ℤ) →
        δ (-((m + 1 : ℕ) : ℤ)) k (slantCo R X (groupHomology.iCycles (Rep.trivial R Γ R) (m + 1) c)) = 0 := by
      rintro _ rfl; exact h1
    exact h4 _ (by omega)

theorem exists_bd (R : Type) [CommRing R] (Γ : Type) [Group Γ] (m : ℕ)
    (c : groupHomology.cycles (Rep.trivial R Γ R) m) (hc : groupHomology.π (Rep.trivial R Γ R) m c = 0) :
    ∃ b, bd R b = groupHomology.iCycles (Rep.trivial R Γ R) m c := by
  have e : (ShortComplex.mk _ _ ((groupHomology.inhomogeneousChains (Rep.trivial R Γ R)).toCycles_comp_homologyπ (m + 1) m)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _
      ((groupHomology.inhomogeneousChains (Rep.trivial R Γ R)).homologyIsCokernel (m + 1) m (by simp))
  obtain ⟨b, hb⟩ := (ShortComplex.moduleCat_exact_iff _).1 e c hc
  refine ⟨b, ?_⟩
  have h3 := ConcreteCategory.congr_hom
    ((groupHomology.inhomogeneousChains (Rep.trivial R Γ R)).toCycles_i (m + 1) m) b
  rw [groupHomology.inhomogeneousChains.d_def] at h3
  rw [← hb]
  exact h3.symm

theorem cpre_add {C : Type*} [Category C] [Preadditive C] {K L : CochainComplex C ℤ} {m : ℤ} (a a' : Cocycle K L m)
    (M : CochainComplex C ℤ) (n k : ℤ) (h : m + n = k) : cpre (a + a') M n k h = cpre a M n k h + cpre a' M n k h := by
  ext x
  obtain ⟨x, rfl⟩ := x.mk_surjective
  rw [AddMonoidHom.add_apply, cpre_mk, cpre_mk, cpre_mk, ← CohomologyClass.mk_add]
  congr 1
  exact Cocycle.ext (Cochain.add_comp _ _ _ h)

theorem cpre_eq_zero {C : Type*} [Category C] [Preadditive C] {K L : CochainComplex C ℤ} {m m' : ℤ} (a : Cocycle K L m)
    (hm : m' + 1 = m) (w : Cochain K L m') (hw : δ m' m w = a.1)
    (M : CochainComplex C ℤ) (n k : ℤ) (h : m + n = k) : cpre a M n k h = 0 := by
  ext x
  obtain ⟨x, rfl⟩ := x.mk_surjective
  have h1 : cpost K x m k h (CohomologyClass.mk a) = 0 := by
    rw [(CohomologyClass.mk_eq_zero_iff a).2 ⟨m', hm, w, hw⟩, map_zero]
  exact h1

theorem etale_group_homology_slant_of_delta_cochain (h : DeltaCo) : D3 := by
  intro R _ Γ _ X m
  let z : groupHomology.cycles (Rep.trivial R Γ R) m → Cocycle ((chains R).obj (sch.obj X)) ((chains R).obj (BX Γ X)) (-(m : ℤ)) :=
    fun c => Cocycle.mk _ _ rfl (closed h R Γ X m c)
  refine ⟨fun c => ⟨z c, (isSlant_iff R X _ _).2 rfl⟩, fun F n => ?_⟩
  have hex : ∃ S, IsSlantMap R Γ X F m n S := by
    let T : groupHomology.cycles (Rep.trivial R Γ R) m →+ H R (BX Γ X) F (m + n) →+ H R (sch.obj X) F n :=
      AddMonoidHom.mk' (fun c => HK.pre R (z c) F (m + n) n (by ring)) (fun c c' => by
        have : z (c + c') = z c + z c' := Cocycle.ext (by
          change slantCo R X (groupHomology.iCycles (Rep.trivial R Γ R) m (c + c')) = slantCo R X _ + slantCo R X _
          rw [map_add]; exact slantCo_add R X _ _)
        rw [this]; exact cpre_add _ _ _ _ _ _)
    have hs : Function.Surjective (groupHomology.π (Rep.trivial R Γ R) m).hom.toAddMonoidHom :=
      (ModuleCat.epi_iff_surjective (groupHomology.π (Rep.trivial R Γ R) m)).1
        (inferInstanceAs (Epi ((groupHomology.inhomogeneousChains (Rep.trivial R Γ R)).homologyπ m)))
    have hk : (groupHomology.π (Rep.trivial R Γ R) m).hom.toAddMonoidHom.ker ≤ T.ker := by
      intro c hc
      obtain ⟨b, hb⟩ := exists_bd R Γ m c hc
      refine cpre_eq_zero (z c) (m' := -((m + 1 : ℕ) : ℤ)) (by omega) (slantCo R X b) ?_ _ _ _ _
      rw [(h R Γ X).2 m b, hb]; rfl
    refine ⟨AddMonoidHom.liftOfSurjective _ hs ⟨T, hk⟩, fun c z' hz' => ?_⟩
    have e : z' = z c := Cocycle.ext ((isSlant_iff R X _ _).1 hz')
    rw [e]
    exact AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨T, hk⟩ c
  unfold slantR
  rw [dif_pos hex]
  exact hex.choose_spec

theorem goal_of (h : DeltaCo) : LateralTheory.E.EtaleChapterDThree :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => etale_group_homology_slant_of_delta_cochain h

end LateralTheory.E.t_D3Cut
