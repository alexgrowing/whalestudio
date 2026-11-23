import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.ZM.SiegPull

variable {S S' : Scheme.{0}} {f : S' ⟶ S}

theorem lbIso_pull_comp {X Y Y' : Scheme.{0}} {L : LB X} {A : LB Y} {F : Y ⟶ X} (H : LBIso A (L.pull F))
    (h : Y' ⟶ Y) : LBIso (A.pull h) (L.pull (h ≫ F)) := by
  refine LBIso.chartPull (chartPullPull A h h rfl) ⟨id, fun J x hx => ?_, fun y J J' hJ hJ' => ?_⟩ H
  · have hx' := (mem_pull (F := h ≫ F)).1 hx
    exact (mem_pull (F := F)).2 hx'
  · have a1 := (mem_pull (F := h ≫ F)).1 hJ
    have a2 := (mem_pull (F := h ≫ F)).1 hJ'
    rw [gm_pull_g L (h ≫ F) (𝟙 Y') y J J' hJ hJ', Category.id_comp]
    exact (gm_pull_g L F h y J J' ((mem_pull (F := F)).2 a1) ((mem_pull (F := F)).2 a2)).symm

theorem exists_isSquare {G : Over S} {G' : Over S'} {φ : G'.left ⟶ G.left} (w : φ ≫ G.hom = G'.hom ≫ f) :
    ∃ φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left, IsSquare φ φ₂ := by
  let T : Over S := Over.mk ((G' ⊗ G').hom ≫ f)
  have w₁ : ((fst G' G').left ≫ φ) ≫ G.hom = T.hom := by
    rw [Category.assoc, w, ← Category.assoc, Over.w (fst G' G')]
    rfl
  have w₂ : ((snd G' G').left ≫ φ) ≫ G.hom = T.hom := by
    rw [Category.assoc, w, ← Category.assoc, Over.w (snd G' G')]
    rfl
  let x : T ⟶ G := Over.homMk ((fst G' G').left ≫ φ) w₁
  let y : T ⟶ G := Over.homMk ((snd G' G').left ≫ φ) w₂
  refine ⟨(lift x y).left, ?_, ?_⟩
  · rw [← Over.comp_left, lift_fst]
    rfl
  · rw [← Over.comp_left, lift_snd]
    rfl

theorem isSquare_tensor {G G' : Over S} (φ : G' ⟶ G) : IsSquare φ.left (φ ⊗ₘ φ).left := by
  constructor
  · rw [← Over.comp_left, tensorHom_fst, Over.comp_left]
  · rw [← Over.comp_left, tensorHom_snd, Over.comp_left]

theorem isSquare_comp {S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} {φ : G'.left ⟶ G.left}
    {ψ : G''.left ⟶ G'.left} {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} {ψ₂ : (G'' ⊗ G'').left ⟶ (G' ⊗ G').left}
    (h' : IsSquare ψ ψ₂) (h : IsSquare φ φ₂) : IsSquare (ψ ≫ φ) (ψ₂ ≫ φ₂) := by
  constructor
  · rw [Category.assoc, h.1, ← Category.assoc, h'.1, Category.assoc]
  · rw [Category.assoc, h.2, ← Category.assoc, h'.2, Category.assoc]

theorem isSquare_unique {G : Over S} {G' : Over S'} {φ φ' : G'.left ⟶ G.left}
    {φ₂ φ₂' : (G' ⊗ G').left ⟶ (G ⊗ G).left} (h : IsSquare φ φ₂) (h' : IsSquare φ' φ₂') (e : φ = φ') : φ₂ = φ₂' := by
  subst e
  have w : φ₂' ≫ (G ⊗ G).hom = φ₂ ≫ (G ⊗ G).hom := by
    rw [← Over.w (fst G G), ← Category.assoc, h'.1, ← Category.assoc, h.1]
  let a : Over.mk (φ₂ ≫ (G ⊗ G).hom) ⟶ G ⊗ G := Over.homMk φ₂ rfl
  let b : Over.mk (φ₂ ≫ (G ⊗ G).hom) ⟶ G ⊗ G := Over.homMk φ₂' w
  have hab : a = b := by
    apply CartesianMonoidalCategory.hom_ext
    · apply Over.OverMorphism.ext
      change φ₂ ≫ (fst G G).left = φ₂' ≫ (fst G G).left
      rw [h.1, h'.1]
    · apply Over.OverMorphism.ext
      change φ₂ ≫ (snd G G).left = φ₂' ≫ (snd G G).left
      rw [h.2, h'.2]
  exact congrArg (fun m => m.left) hab

theorem lbIso_lam_pull {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
    {φ : G'.left ⟶ G.left} {L : LB G.left} {L' : LB G'.left} (h : IsGrpPullback G' G f φ)
    (hw : LBIso L' (L.pull φ)) {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} (hs : IsSquare φ φ₂) :
    LBIso (abelian₂ G' L') ((abelian₂ G L).pull φ₂) := by
  obtain ⟨w, hw'⟩ := hw
  have hP : PGen w := by
    unfold PGen gw
    intro Y g y j j' k k' h1 h2 h3 h4
    have m1 : g y ∈ (L.pull φ).U (fun _ => j) := (mem_pull (F := φ)).2 h1
    have m2 : g y ∈ (L.pull φ).U (fun _ => j') := (mem_pull (F := φ)).2 h2
    have hV : g y ∈ (L.pull φ).U (fun _ => j) ⊓ L'.U k ⊓ ((L.pull φ).U (fun _ => j') ⊓ L'.U k') :=
      ⟨⟨m1, h3⟩, ⟨m2, h4⟩⟩
    have e := congrArg (gm g y _) (hw' (fun _ => j, k) (fun _ => j', k'))
    unfold LB.div at e
    simp only [map_mul, map_inv] at e
    simp only [gm_res g y _ hV] at e
    rw [gm_pull_g L φ g y (fun _ => j) (fun _ => j') m1 m2] at e
    exact e
  have e : ∀ I : ULift (Finset (Fin 2)),
      (psum G' (x2 G') I.down).left ≫ φ = φ₂ ≫ (psum G (x2 G) I.down).left := by
    let T : Over S' := G' ⊗ G'
    have hj : φ₂ ≫ (G ⊗ G).hom = T.hom ≫ f := by
      rw [← Over.w (fst G G), ← Category.assoc, hs.1, Category.assoc, h.1.w, ← Category.assoc,
        Over.w (fst G' G')]
    let U : Over S := Over.mk (T.hom ≫ f)
    let j : U ⟶ G ⊗ G := Over.homMk φ₂ hj
    have hΦ : ∀ u : T ⟶ G', (u.left ≫ φ) ≫ G.hom = U.hom := fun u => by
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w u]
      rfl
    let Φ : (T ⟶ G') → (U ⟶ G) := fun u => Over.homMk (u.left ≫ φ) (hΦ u)
    have Φmul : ∀ x y, Φ (x * y) = Φ x * Φ y := fun x y =>
      Over.OverMorphism.ext (h.2 T x y (Φ x) (Φ y) rfl rfl).symm
    let Φh : (T ⟶ G') →* (U ⟶ G) := MonoidHom.mk' Φ Φmul
    have key : ∀ (u : T ⟶ G') (v : G ⊗ G ⟶ G), Φ u = j ≫ v → u.left ≫ φ = φ₂ ≫ v.left :=
      fun u v hh => congrArg (fun m => m.left) hh
    have key' : ∀ (u : T ⟶ G') (v : G ⊗ G ⟶ G), u.left ≫ φ = φ₂ ≫ v.left → Φ u = j ≫ v :=
      fun u v hh => Over.OverMorphism.ext (by exact hh)
    have base : ∀ k : Fin 2, Φ (x2 G' k) = j ≫ x2 G k := by
      intro k
      fin_cases k
      · exact key' _ _ hs.1.symm
      · exact key' _ _ hs.2.symm
    have fold : ∀ l : List (Fin 2),
        Φ (List.foldr (fun k acc => padd G' (x2 G' k) acc) (pzero G' (G2 G')) l) =
          j ≫ List.foldr (fun k acc => padd G (x2 G k) acc) (pzero G (G2 G)) l := by
      intro l
      induction l with
      | nil =>
        change Φh 1 = j ≫ 1
        rw [map_one, comp_one]
      | cons k l ih =>
        change Φ (x2 G' k * _) = j ≫ (x2 G k * _)
        rw [Φmul, comp_mul, base k, ih]
    intro I
    exact key _ _ (fold _)
  exact LBIso.chartPull (chartPullId _) (chartPullOut L _ _ φ₂ _ e) (iso_linComb hP _ _)

theorem lev_comm_of_basis {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    {χ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f χ) {n : ℕ} {M : Type} [AddCommGroup M] (e : (Fin n → ℤ) ≃ₗ[ℤ] M)
    (l : M → (𝟙_ (Over S) ⟶ G)) (l' : M → (𝟙_ (Over S') ⟶ G')) (hl : ∀ a b, l (a + b) = l a * l b)
    (hl' : ∀ a b, l' (a + b) = l' a * l' b)
    (H : ∀ i, (l' (e (Pi.single i 1))).left ≫ χ = f ≫ (l (e (Pi.single i 1))).left) (a : M) :
    (l' a).left ≫ χ = f ≫ (l a).left := by
  let U : Over S := Over.mk ((𝟙_ (Over S')).hom ≫ f)
  have hΦ : ∀ x : 𝟙_ (Over S') ⟶ G', (x.left ≫ χ) ≫ G.hom = U.hom := fun x => by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w x]
    rfl
  let Φ : (𝟙_ (Over S') ⟶ G') → (U ⟶ G) := fun x => Over.homMk (x.left ≫ χ) (hΦ x)
  have Φmul : ∀ x y, Φ (x * y) = Φ x * Φ y := fun x y =>
    Over.OverMorphism.ext (h.2 _ x y (Φ x) (Φ y) rfl rfl).symm
  let Ψ : (𝟙_ (Over S) ⟶ G) → (U ⟶ G) := fun y => toUnit U ≫ y
  have Ψmul : ∀ x y, Ψ (x * y) = Ψ x * Ψ y := fun x y => comp_mul _ _ _
  have hT : (toUnit U).left = f := by
    simp [U]
  let F₁ : (Fin n → ℤ) →+ Additive (U ⟶ G) :=
    AddMonoidHom.mk' (fun v => Additive.ofMul (Φ (l' (e v)))) (fun v w => by
      simp only [map_add, hl', Φmul]
      rfl)
  let F₂ : (Fin n → ℤ) →+ Additive (U ⟶ G) :=
    AddMonoidHom.mk' (fun v => Additive.ofMul (Ψ (l (e v)))) (fun v w => by
      simp only [map_add, hl, Ψmul]
      rfl)
  have hF : F₁ = F₂ := by
    ext i
    change (l' (e (Pi.single i 1))).left ≫ χ = (toUnit U).left ≫ (l (e (Pi.single i 1))).left
    rw [hT, H i]
  have key := congrArg (fun F : (Fin n → ℤ) →+ Additive (U ⟶ G) => (Additive.toMul (F (e.symm a))).left) hF
  change (l' (e (e.symm a))).left ≫ χ = (toUnit U).left ≫ (l (e (e.symm a))).left at key
  rw [LinearEquiv.apply_symm_apply, hT] at key
  exact key

end GlobalTheory.ZM.SiegPull

open GlobalTheory.ZM.SiegPull in

theorem GlobalTheory.ZM.siegPB_iff_tSieg : ∀ (g k : ℕ) (J La : Type) [AddCommGroup La] (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] La) (bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] La) (o B : Type) [CommRing o] [CommRing B] (b : TBase o k) (ζ : B) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s₁ : S ⟶ Sp B) (s' : S' ⟶ Sp o) (s₁' : S' ⟶ Sp B) (t : TObj g k J b s) (c : SiegPre g k ζ s₁) (t' : TObj g k J b s') (c' : SiegPre g k ζ s₁') (f : S' ⟶ S), TSieg bas bas' t c → TMap t' t f → (SiegPB c' c f ↔ TSieg bas bas' t' c') := by
  intro g k J La _ bas bas' o B _ _ b ζ S S' s s₁ s' s₁' t c t' c' f hc ht
  let _ := t.ab.comm
  let _ := t'.ab.comm
  obtain ⟨ψ, hψm, hψL, hψp⟩ := hc
  obtain ⟨χ, hχ, hχL, hχp, -⟩ := ht
  obtain ⟨χ₂, hχ₂⟩ := exists_isSquare (G := t.A) (G' := t'.A) (f := f) hχ.1.w
  have hLam : LBIso (abelian₂ t'.A t'.L) ((abelian₂ t.A t.L).pull χ₂) := lbIso_lam_pull hχ hχL hχ₂
  have hLt : (abelian₂ t.A t.L).IsLB := DVR.linComb_isLB _ t.isLB _ _
  have hLt' : (abelian₂ t'.A t'.L).IsLB := DVR.linComb_isLB _ t'.isLB _ _
  have hhi : ψ.hom.left ≫ ψ.inv.left = 𝟙 _ := by
    rw [← Over.comp_left, ψ.hom_inv_id, Over.id_left]
  have hih : ψ.inv.left ≫ ψ.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, ψ.inv_hom_id, Over.id_left]
  constructor
  · rintro ⟨φ, φ₂, hφ, hsq, hP, hlev⟩
    have hψg : IsGrpPullback c.A t.A (𝟙 S) ψ.hom.left := isGrpPullback_of_iso ψ
    have h1 : IsGrpPullback c'.A t.A f (φ ≫ ψ.hom.left) :=
      (IsGrpPullback.comp hφ hψg).congr (Category.comp_id f) rfl
    obtain ⟨e, hem, heχ⟩ := grpPullback_iso h1 hχ
    have sq1 := isSquare_comp (isSquare_tensor e.hom) hχ₂
    have sq2 := isSquare_comp hsq (isSquare_tensor ψ.hom)
    have heq : (e.hom ⊗ₘ e.hom).left ≫ χ₂ = φ₂ ≫ (ψ.hom ⊗ₘ ψ.hom).left := isSquare_unique sq1 sq2 heχ
    refine ⟨e, hem, ?_, fun i => ?_⟩
    · have x1 := lbIso_pull_comp hψL φ₂
      have x2 := lbIso_pull_comp hLam (e.hom ⊗ₘ e.hom).left
      rw [heq] at x2
      exact LBIso.trans c'.isLB (pull_isLB c.isLB φ₂) (pull_isLB hLt' _) hP
        (LBIso.trans (pull_isLB c.isLB φ₂) (pull_isLB hLt _) (pull_isLB hLt' _) x1 x2.symm)
    · apply hχ.1.hom_ext
      · rw [Over.comp_left, Category.assoc, heχ, ← Category.assoc, hlev, Category.assoc, ← Over.comp_left,
          hψp i, hχp i]
      · rw [Over.w, Over.w]
        rfl
  · rintro ⟨ψ', hψ'm, hψ'L, hψ'p⟩
    have hψg : IsGrpPullback c.A t.A (𝟙 S) ψ.hom.left := isGrpPullback_of_iso ψ
    have hn : IsGrpPullback c'.A t.A (f ≫ 𝟙 S) ((ψ'.hom.left ≫ χ ≫ ψ.inv.left) ≫ ψ.hom.left) :=
      (IsGrpPullback.comp (isGrpPullback_of_iso ψ') hχ).congr (by rw [Category.id_comp, Category.comp_id])
        (by rw [Category.assoc, Category.assoc, hih, Category.comp_id])
    have hφ : IsGrpPullback c'.A c.A f (ψ'.hom.left ≫ χ ≫ ψ.inv.left) := by
      refine IsGrpPullback.cancel hψg hn ?_
      rw [Category.assoc, Category.assoc, Over.w ψ.inv, hχ.1.w, ← Category.assoc, Over.w ψ'.hom]
    obtain ⟨φ₂, hsq⟩ := exists_isSquare hφ.1.w
    have sq1 := isSquare_comp (isSquare_tensor ψ'.hom) hχ₂
    have sq2 := isSquare_comp hsq (isSquare_tensor ψ.hom)
    have heq : (ψ'.hom ⊗ₘ ψ'.hom).left ≫ χ₂ = φ₂ ≫ (ψ.hom ⊗ₘ ψ.hom).left :=
      isSquare_unique sq1 sq2 (by rw [Category.assoc, Category.assoc, hih, Category.comp_id])
    refine ⟨_, φ₂, hφ, hsq, ?_, ?_⟩
    · have x1 := lbIso_pull_comp hψL φ₂
      have x2 := lbIso_pull_comp hLam (ψ'.hom ⊗ₘ ψ'.hom).left
      rw [heq] at x2
      exact LBIso.trans c'.isLB (pull_isLB hLt' _) (pull_isLB c.isLB φ₂) hψ'L
        (LBIso.trans (pull_isLB hLt' _) (pull_isLB hLt _) (pull_isLB c.isLB φ₂) x2 x1.symm)
    · intro a
      refine lev_comm_of_basis hφ (bas.trans bas'.symm) c.lev c'.lev c.lev_add c'.lev_add (fun i => ?_) a
      change (c'.lev (bas'.symm (bas (Pi.single i 1)))).left ≫ ψ'.hom.left ≫ χ ≫ ψ.inv.left =
        f ≫ (c.lev (bas'.symm (bas (Pi.single i 1)))).left
      rw [← Category.assoc, ← Over.comp_left, hψ'p i, ← Category.assoc, hχp i, Category.assoc, ← hψp i,
        Over.comp_left, Category.assoc, hhi, Category.comp_id]

end
