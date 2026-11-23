import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverCompImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyUnramifiedAdjointRingActionScheme
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

noncomputable section

namespace GlobalTheory.UPel.HT

theorem zRel_of_pullback : ∀ (h h' M : ℕ) (B : Type) [CommRing B] (ζ : B) (O : Type) [Ring O] (e : O) (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin h' ⊕ Fin h' → ℤ)) (n : ℕ) (o : Fin n → O) (κ : Fin n → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (S₁ S₂ : Scheme.{0}) (s₁ : S₁ ⟶ Sp B) (s₂ : S₂ ⟶ Sp B) (y : S₂ ⟶ S₁) (c₁ : SiegPre h M ζ s₁) (w₁ : SiegPre h' M ζ s₁) (act₁ : O → (w₁.A ⟶ w₁.A)) (c₂ : SiegPre h M ζ s₂) (w₂ : SiegPre h' M ζ s₂) (act₂ : O → (w₂.A ⟶ w₂.A)), ActPB w₂ act₂ w₁ act₁ y → SiegPB c₂ c₁ y → ZRel e jl o κ c₁ w₁ act₁ → ZRel e jl o κ c₂ w₂ act₂ := by
  intro h h' M B _ ζ O _ e jl n o κ S₁ S₂ s₁ s₂ y c₁ w₁ act₁ c₂ w₂ act₂ hA hS hZ
  obtain ⟨ψ, ψ₂, hψ, sqψ, hwP, hwl, hact⟩ := hA
  obtain ⟨φ, φ₂, hφ, sqφ, hcP, hcl⟩ := hS
  obtain ⟨inc₁, pr₁, mi₁, mp₁, ip₁, pi₁, hP₁, hl₁, hz₁⟩ := hZ
  haveI := mi₁
  haveI := mp₁
  have wi : (φ ≫ inc₁.left) ≫ w₁.A.hom = c₂.A.hom ≫ y := by
    rw [Category.assoc, Over.w inc₁]; exact hφ.1.w
  let inc₂ : c₂.A ⟶ w₂.A := Over.homMk (hψ.1.lift (φ ≫ inc₁.left) c₂.A.hom wi) (hψ.1.lift_snd _ _ _)
  have inc₂_l : inc₂.left ≫ ψ = φ ≫ inc₁.left := hψ.1.lift_fst _ _ _
  have wp : (ψ ≫ pr₁.left) ≫ c₁.A.hom = w₂.A.hom ≫ y := by
    rw [Category.assoc, Over.w pr₁]; exact hψ.1.w
  let pr₂ : w₂.A ⟶ c₂.A := Over.homMk (hφ.1.lift (ψ ≫ pr₁.left) w₂.A.hom wp) (hφ.1.lift_snd _ _ _)
  have pr₂_l : pr₂.left ≫ φ = ψ ≫ pr₁.left := hφ.1.lift_fst _ _ _
  have extW : ∀ {T : Over S₂} (a b : T ⟶ w₂.A), a.left ≫ ψ = b.left ≫ ψ → a = b := fun a b hab =>
    Over.OverMorphism.ext (hψ.1.hom_ext hab (by rw [Over.w, Over.w]))
  have extC : ∀ {T : Over S₂} (a b : T ⟶ c₂.A), a.left ≫ φ = b.left ≫ φ → a = b := fun a b hab =>
    Over.OverMorphism.ext (hφ.1.hom_ext hab (by rw [Over.w, Over.w]))
  have pI : ∀ (T : Over S₂) (x : T ⟶ c₂.A), pushHom hψ T (x ≫ inc₂) = pushHom hφ T x ≫ inc₁ := fun T x =>
    Over.OverMorphism.ext (by
      show (x ≫ inc₂).left ≫ ψ = (x.left ≫ φ) ≫ inc₁.left
      rw [Over.comp_left, Category.assoc, inc₂_l, Category.assoc])
  have pP : ∀ (T : Over S₂) (x : T ⟶ w₂.A), pushHom hφ T (x ≫ pr₂) = pushHom hψ T x ≫ pr₁ := fun T x =>
    Over.OverMorphism.ext (by
      show (x ≫ pr₂).left ≫ φ = (x.left ≫ ψ) ≫ pr₁.left
      rw [Over.comp_left, Category.assoc, pr₂_l, Category.assoc])
  have mI : IsMonHom inc₂ := isMonHom_of_mul _ fun T x z => extW _ _ (congrArg (fun q => q.left)
    (calc pushHom hψ T ((x * z) ≫ inc₂) = pushHom hφ T (x * z) ≫ inc₁ := pI _ _
      _ = (pushHom hφ T x * pushHom hφ T z) ≫ inc₁ := by rw [map_mul]
      _ = (pushHom hφ T x ≫ inc₁) * (pushHom hφ T z ≫ inc₁) := MonObj.mul_comp _ _ _
      _ = pushHom hψ T (x ≫ inc₂) * pushHom hψ T (z ≫ inc₂) := by rw [pI, pI]
      _ = pushHom hψ T ((x ≫ inc₂) * (z ≫ inc₂)) := (map_mul _ _ _).symm))
  have mP : IsMonHom pr₂ := isMonHom_of_mul _ fun T x z => extC _ _ (congrArg (fun q => q.left)
    (calc pushHom hφ T ((x * z) ≫ pr₂) = pushHom hψ T (x * z) ≫ pr₁ := pP _ _
      _ = (pushHom hψ T x * pushHom hψ T z) ≫ pr₁ := by rw [map_mul]
      _ = (pushHom hψ T x ≫ pr₁) * (pushHom hψ T z ≫ pr₁) := MonObj.mul_comp _ _ _
      _ = pushHom hφ T (x ≫ pr₂) * pushHom hφ T (z ≫ pr₂) := by rw [pP, pP]
      _ = pushHom hφ T ((x ≫ pr₂) * (z ≫ pr₂)) := (map_mul _ _ _).symm))
  have h1 : inc₂ ≫ pr₂ = 𝟙 c₂.A := extC _ _ (by
    rw [Over.comp_left, Over.id_left, Category.assoc, pr₂_l, ← Category.assoc, inc₂_l, Category.assoc,
      ← Over.comp_left, ip₁, Over.id_left, Category.comp_id, Category.id_comp])
  have h2 : pr₂ ≫ inc₂ = act₂ e := extW _ _ (by
    rw [Over.comp_left, Category.assoc, inc₂_l, ← Category.assoc, pr₂_l, Category.assoc, ← Over.comp_left, pi₁,
      hact])
  have eι : (inc₂ ⊗ₘ inc₂).left ≫ ψ₂ = φ₂ ≫ (inc₁ ⊗ₘ inc₁).left := by
    apply ActUnr.left_hom_ext
    · rw [Category.assoc, sqψ.1, ← Category.assoc, ← Over.comp_left, tensorHom_fst, Category.assoc, ← Over.comp_left,
        tensorHom_fst, Over.comp_left, Over.comp_left, Category.assoc, inc₂_l, ← Category.assoc, ← sqφ.1,
        Category.assoc]
    · rw [Category.assoc, sqψ.2, ← Category.assoc, ← Over.comp_left, tensorHom_snd, Category.assoc, ← Over.comp_left,
        tensorHom_snd, Over.comp_left, Over.comp_left, Category.assoc, inc₂_l, ← Category.assoc, ← sqφ.2,
        Category.assoc]
  have P1 : LBIso (c₁.P.pull φ₂) (w₁.P.pull (φ₂ ≫ (inc₁ ⊗ₘ inc₁).left)) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull c₁.P φ₂ φ₂ rfl)
      (chartPullSame w₁.P _ (fun _ => (inc₁ ⊗ₘ inc₁).left) _ φ₂ fun _ => rfl) hP₁
  have P2 : LBIso (w₂.P.pull (inc₂ ⊗ₘ inc₂).left) (w₁.P.pull (φ₂ ≫ (inc₁ ⊗ₘ inc₁).left)) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull w₂.P (inc₂ ⊗ₘ inc₂).left (inc₂ ⊗ₘ inc₂).left rfl)
      (chartPullSame w₁.P _ (fun _ => ψ₂) _ (inc₂ ⊗ₘ inc₂).left fun _ => eι.symm) hwP
  have hP₂ : LBIso c₂.P (w₂.P.pull (inc₂ ⊗ₘ inc₂).left) :=
    LBIso.trans c₂.isLB (pull_isLB c₁.isLB _) (pull_isLB w₂.isLB _) hcP
      (LBIso.trans (pull_isLB c₁.isLB _) (pull_isLB w₁.isLB _) (pull_isLB w₂.isLB _) P1 P2.symm)
  have lv : ∀ a, c₂.lev a ≫ inc₂ = w₂.lev (jl a) := fun a => extW _ _ (by
    rw [Over.comp_left, Category.assoc, inc₂_l, ← Category.assoc, hcl, Category.assoc, ← Over.comp_left, hl₁, hwl])
  let T₀ : Over S₂ := 𝟙_ (Over S₂)
  let u : Over.mk (T₀.hom ≫ y) ⟶ 𝟙_ (Over S₁) := toUnit _
  have hu : u.left = y := by
    simp [u, T₀]
  have pL : ∀ a, pushHom hψ T₀ (w₂.lev a) = u ≫ w₁.lev a := fun a => Over.OverMorphism.ext (by
    show (w₂.lev a).left ≫ ψ = u.left ≫ (w₁.lev a).left
    rw [hu, hwl])
  have pT : ∀ (b : Fin h ⊕ Fin h → ℤ) (r : O), pushHom hψ T₀ (c₂.lev b ≫ inc₂ ≫ act₂ r) =
      u ≫ (c₁.lev b ≫ inc₁ ≫ act₁ r) := fun b r => Over.OverMorphism.ext (by
    show (c₂.lev b ≫ inc₂ ≫ act₂ r).left ≫ ψ = u.left ≫ (c₁.lev b ≫ inc₁ ≫ act₁ r).left
    simp only [Over.comp_left, Category.assoc]
    rw [hact, reassoc_of% inc₂_l, reassoc_of% (hcl b), hu])
  have lz : ∀ a, w₂.lev a = (List.ofFn fun k => c₂.lev (κ k a) ≫ inc₂ ≫ act₂ (o k)).prod := fun a =>
    extW _ _ (congrArg (fun q => q.left)
      (calc pushHom hψ T₀ (w₂.lev a) = u ≫ w₁.lev a := pL a
        _ = preHom (G := w₁.A) u (List.ofFn fun k => c₁.lev (κ k a) ≫ inc₁ ≫ act₁ (o k)).prod := by
          rw [hz₁ a]; rfl
        _ = (List.ofFn fun k => u ≫ (c₁.lev (κ k a) ≫ inc₁ ≫ act₁ (o k))).prod := by
          rw [map_list_prod, List.map_ofFn]; rfl
        _ = (List.ofFn fun k => pushHom hψ T₀ (c₂.lev (κ k a) ≫ inc₂ ≫ act₂ (o k))).prod := by
          simp only [pT]
        _ = pushHom hψ T₀ (List.ofFn fun k => c₂.lev (κ k a) ≫ inc₂ ≫ act₂ (o k)).prod := by
          rw [map_list_prod, List.map_ofFn]; rfl))
  exact ⟨inc₂, pr₂, mI, mP, h1, h2, hP₂, lv, lz⟩

end GlobalTheory.UPel.HT
