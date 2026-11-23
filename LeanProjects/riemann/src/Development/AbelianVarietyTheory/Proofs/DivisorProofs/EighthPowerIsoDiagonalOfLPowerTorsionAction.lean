import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinitePointsOfIsOpenImmersion

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowerDiagonal

section General

variable {C : Type*} [Category C] [CartesianMonoidalCategory C]

theorem isMonHom_of_points {X Y : C} [MonObj X] [MonObj Y] (f : X ⟶ Y)
    (h1 : ∀ T : C, (1 : T ⟶ X) ≫ f = 1)
    (hm : ∀ (T : C) (x y : T ⟶ X), (x * y) ≫ f = (x ≫ f) * (y ≫ f)) : IsMonHom f where
  one_hom := by
    rw [MonObj.one_eq_one X, MonObj.one_eq_one Y]
    exact h1 _
  mul_hom := by
    rw [MonObj.mul_eq_mul X, MonObj.mul_eq_mul Y, hm, MonObj.comp_mul]
    simp

theorem exists_sections {G H : C} [MonObj G] [MonObj H] {n : Type} [DecidableEq n]
    (p : n → (G ⟶ H)) (hp : ∀ a, IsMonHom (p a))
    (hu : ∀ (T : C) (y : n → (T ⟶ H)), ∃! x : T ⟶ G, ∀ a, x ≫ p a = y a) :
    ∃ j : n → (H ⟶ G), (∀ b, IsMonHom (j b)) ∧ (∀ b, j b ≫ p b = 𝟙 H) ∧
      ∀ b c, c ≠ b → j b ≫ p c = 1 := by
  classical
  have hex := fun b => (hu H (fun c => if c = b then 𝟙 H else 1)).exists
  choose j hj using hex
  have key : ∀ {T : C} (x : T ⟶ H) (b c : n), x ≫ j b ≫ p c = if c = b then x else 1 := by
    intro T x b c
    rw [hj b c]
    split_ifs <;> simp
  have ext : ∀ {T : C} (x y : T ⟶ G), (∀ a, x ≫ p a = y ≫ p a) → x = y := fun {T} x y h =>
    (hu T fun a => y ≫ p a).unique h (fun _ => rfl)
  refine ⟨j, fun b => ?_, fun b => by simpa using key (𝟙 H) b b,
    fun b c hcb => by simpa [hcb] using key (𝟙 H) b c⟩
  apply isMonHom_of_points
  · intro T
    apply ext
    intro a
    haveI := hp a
    rw [Category.assoc, key, MonObj.one_comp]
    split_ifs <;> rfl
  · intro T x y
    apply ext
    intro a
    haveI := hp a
    simp only [Category.assoc, key, MonObj.mul_comp]
    split_ifs <;> simp

theorem hom_ext_sections {G H H' : C} [MonObj G] [MonObj H] [MonObj H']
    {n : Type} [Finite n] [DecidableEq n]
    (p : n → (G ⟶ H)) (hp : ∀ a, IsMonHom (p a))
    (hu : ∀ (T : C) (y : n → (T ⟶ H)), ∃! x : T ⟶ G, ∀ a, x ≫ p a = y a)
    (j : n → (H ⟶ G)) (h1 : ∀ b, j b ≫ p b = 𝟙 H) (h2 : ∀ b c, c ≠ b → j b ≫ p c = 1)
    (f g : G ⟶ H') [IsMonHom f] [IsMonHom g] (h : ∀ b, j b ≫ f = j b ≫ g) : f = g := by
  classical
  haveI := Fintype.ofFinite n
  have ext : ∀ {T : C} (x y : T ⟶ G), (∀ a, x ≫ p a = y ≫ p a) → x = y := fun {T} x y h =>
    (hu T fun a => y ≫ p a).unique h (fun _ => rfl)
  have hcomp : ∀ {K : C} [MonObj K] (k : G ⟶ K) [IsMonHom k] (l : List n),
      (l.map fun b => p b ≫ j b).prod ≫ k = (l.map fun b => p b ≫ j b ≫ k).prod := by
    intro K _ k _ l
    induction l with
    | nil => simp
    | cons b l ih => simp [MonObj.mul_comp, ih]
  have hlist : ∀ (c : n) (l : List n), l.Nodup →
      (l.map fun b => p b ≫ j b ≫ p c).prod = if c ∈ l then p c else 1 := by
    intro c l hl
    induction l with
    | nil => simp
    | cons b l ih =>
      rw [List.map_cons, List.prod_cons, ih (List.nodup_cons.mp hl).2]
      by_cases hbc : b = c
      · subst hbc
        have hnot : b ∉ l := (List.nodup_cons.mp hl).1
        simp [h1, hnot]
      · simp [h2 b c (Ne.symm hbc), Ne.symm hbc]
  have hs : (Finset.univ.toList.map fun b => p b ≫ j b).prod = 𝟙 G := by
    apply ext
    intro c
    haveI := hp c
    rw [hcomp (p c), hlist c _ (Finset.nodup_toList _)]
    simp
  calc f = (Finset.univ.toList.map fun b => p b ≫ j b).prod ≫ f := by rw [hs, Category.id_comp]
    _ = (Finset.univ.toList.map fun b => p b ≫ j b ≫ f).prod := hcomp f _
    _ = (Finset.univ.toList.map fun b => p b ≫ j b ≫ g).prod := by simp only [h]
    _ = (Finset.univ.toList.map fun b => p b ≫ j b).prod ≫ g := (hcomp g _).symm
    _ = g := by rw [hs, Category.id_comp]

end General

theorem exists_diagonal : ∀ (K : Type) [Field K] [IsAlgClosed K] (G₀ G₁ H₀ H₁ : Over (Sp K)) [GrpObj G₀] [GrpObj G₁] [GrpObj H₀] [GrpObj H₁] [IsCommMonObj H₀] [IsCommMonObj H₁], IsSemiAbelian H₀ → IsSemiAbelian H₁ → ∀ (l : ℕ), l.Prime → (l : K) ≠ 0 → ∀ (p₀ : Fin 8 → (G₀ ⟶ H₀)) (p₁ : Fin 8 → (G₁ ⟶ H₁)), (∀ a, IsMonHom (p₀ a)) → (∀ a, IsMonHom (p₁ a)) → (∀ (T : Over (Sp K)) (y : Fin 8 → (T ⟶ H₀)), ∃! x : T ⟶ G₀, ∀ a, x ≫ p₀ a = y a) → (∀ (T : Over (Sp K)) (y : Fin 8 → (T ⟶ H₁)), ∃! x : T ⟶ G₁, ∀ a, x ≫ p₁ a = y a) → ∀ (F : G₀ ⟶ G₁), IsMonHom F → IsIso F → (∀ (z z' : 𝟙_ (Over (Sp K)) ⟶ G₀), (∃ k : ℕ, z ^ (l ^ k) = 1) → (∃ k : ℕ, z' ^ (l ^ k) = 1) → ∀ a a', z ≫ p₀ a = z' ≫ p₀ a' → z ≫ F ≫ p₁ a = z' ≫ F ≫ p₁ a') → ∃ f₁ : H₀ ⟶ H₁, IsMonHom f₁ ∧ IsIso f₁ ∧ ∀ a, F ≫ p₁ a = p₀ a ≫ f₁ := by
  intro K _ _ G₀ G₁ H₀ H₁ _ _ _ _ _ _ hH₀ hH₁ l hl hlK p₀ p₁ hp₀ hp₁ hu₀ hu₁ F hF hFi htor
  classical
  obtain ⟨j₀, hj₀m, hj₀1, hj₀2⟩ := exists_sections p₀ hp₀ hu₀
  obtain ⟨j₁, hj₁m, hj₁1, hj₁2⟩ := exists_sections p₁ hp₁ hu₁
  haveI := hF
  haveI := hFi
  haveI := fun a => hp₀ a
  haveI := fun a => hp₁ a
  haveI := fun b => hj₀m b
  have hpj : ∀ b a : Fin 8, j₀ b ≫ p₀ a = if a = b then 𝟙 H₀ else 1 := by
    intro b a
    split_ifs with h
    · subst h; exact hj₀1 a
    · exact hj₀2 b a h
  have hpj₁ : ∀ b a : Fin 8, j₁ b ≫ p₁ a = if a = b then 𝟙 H₁ else 1 := by
    intro b a
    split_ifs with h
    · subst h; exact hj₁1 a
    · exact hj₁2 b a h

  have htors : ∀ (b : Fin 8) (y : 𝟙_ (Over (Sp K)) ⟶ H₀) (k : ℕ), y ^ (l ^ k) = 1 →
      ∃ k : ℕ, (y ≫ j₀ b) ^ (l ^ k) = 1 := by
    intro b y k hy
    haveI := hj₀m b
    exact ⟨k, by rw [← MonObj.pow_comp, hy, MonObj.one_comp]⟩

  have hoff : ∀ b a : Fin 8, a ≠ b → j₀ b ≫ F ≫ p₁ a = 1 := by
    intro b a hab
    haveI := hj₀m b
    haveI := hp₁ a
    refine GlobalTheory.TorsionDense.eq_one_of_torsion_comp_eq_one K H₀ H₁ hH₀ hH₁ l hl hlK _ inferInstance
      (fun _ _ y k hy => ?_)
    have := htor (y ≫ j₀ b) 1 (htors b y k hy) ⟨0, _root_.one_pow _⟩ a a
      (by rw [Category.assoc, hpj, if_neg hab, MonObj.comp_one, MonObj.one_comp])
    rw [MonObj.one_comp (F ≫ p₁ a)] at this
    simpa [Category.assoc] using this

  have hdiag : ∀ a : Fin 8, j₀ a ≫ F ≫ p₁ a = j₀ 0 ≫ F ≫ p₁ 0 := by
    intro a
    haveI := hj₀m a
    haveI := hj₀m 0
    haveI := hp₁ a
    haveI := hp₁ 0
    have hpt : ∀ (T : Over (Sp K)) (x : T ⟶ H₀),
        x ≫ ((j₀ a ≫ F ≫ p₁ a) * (j₀ 0 ≫ F ≫ p₁ 0)⁻¹) =
          (x ≫ j₀ a ≫ F ≫ p₁ a) * (x ≫ j₀ 0 ≫ F ≫ p₁ 0)⁻¹ := by
      intro T x
      rw [MonObj.comp_mul, GrpObj.comp_inv]
    have hmon : IsMonHom ((j₀ a ≫ F ≫ p₁ a) * (j₀ 0 ≫ F ≫ p₁ 0)⁻¹) := by
      apply isMonHom_of_points
      · intro T
        rw [hpt, MonObj.one_comp, MonObj.one_comp, _root_.inv_one, _root_.mul_one]
      · intro T x y
        rw [hpt, hpt, hpt, MonObj.mul_comp, MonObj.mul_comp, _root_.mul_inv, _root_.mul_mul_mul_comm]
    have h1 := GlobalTheory.TorsionDense.eq_one_of_torsion_comp_eq_one K H₀ H₁ hH₀ hH₁ l hl hlK _ hmon
      (fun _ _ y k hy => by
        have := htor (y ≫ j₀ a) (y ≫ j₀ 0) (htors a y k hy) (htors 0 y k hy) a 0
          (by rw [Category.assoc, Category.assoc, hpj, hpj, if_pos rfl, if_pos rfl])
        rw [hpt, _root_.mul_inv_eq_one]
        simpa [Category.assoc] using this)
    exact _root_.mul_inv_eq_one.mp h1
  let f₁ : H₀ ⟶ H₁ := j₀ 0 ≫ F ≫ p₁ 0
  haveI : IsMonHom f₁ := by
    haveI := hj₀m 0
    haveI := hp₁ 0
    dsimp [f₁]
    infer_instance
  have hcomm : ∀ a, F ≫ p₁ a = p₀ a ≫ f₁ := by
    intro a
    haveI := hp₁ a
    haveI := hp₀ a
    refine hom_ext_sections p₀ hp₀ hu₀ j₀ hj₀1 hj₀2 _ _ (fun b => ?_)
    rw [← Category.assoc (j₀ b) (p₀ a), hpj]
    split_ifs with hab
    · subst hab
      rw [Category.id_comp, hdiag]
    · rw [hoff b a hab, MonObj.one_comp]
  have hsec : j₀ 0 ≫ F = f₁ ≫ j₁ 0 := by
    refine (hu₁ H₀ fun a => (f₁ ≫ j₁ 0) ≫ p₁ a).unique (fun a => ?_) (fun _ => rfl)
    rw [Category.assoc, hcomm, ← Category.assoc, hpj, Category.assoc, hpj₁]
    split_ifs
    · simp
    · rw [MonObj.one_comp, MonObj.comp_one]
  refine ⟨f₁, inferInstance, ⟨⟨j₁ 0 ≫ inv F ≫ p₀ 0, ?_, ?_⟩⟩, hcomm⟩
  · rw [← Category.assoc, ← hsec, Category.assoc, IsIso.hom_inv_id_assoc, hj₀1]
  · rw [Category.assoc, Category.assoc, ← hcomm, IsIso.inv_hom_id_assoc, hj₁1]

end GlobalTheory.PowerDiagonal
