import Development.EtaleCohomology.EtaleSheaves.FiltPf

noncomputable section
open CategoryTheory Limits Category Pretriangulated GlobalTheory.EtC LateralTheory.E.TruncationPieces LateralTheory.E.FiltPf

namespace LateralTheory.E.TowerFinPf

abbrev Q (R : Type) [CommRing R] := HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)

section RelYLemmas
variable (R : Type) [CommRing R] (F : Shv R) (n : ℤ)

theorem relY_of_iso {A B A' B' : HomotopyCategory (Shv R) (ComplexShape.up ℤ)} (g : A ⟶ B) (g' : A' ⟶ B')
    (e₁ : A' ≅ A) (e₂ : B' ≅ B) (w : g' ≫ e₂.hom = e₁.hom ≫ g) (h : Tri.RelY (Yres R F) n g) :
    Tri.RelY (Yres R F) n g' := by
  have w' : g ≫ e₂.inv = e₁.inv ≫ g' := by
    rw [Iso.eq_inv_comp, ← assoc, ← w, assoc, Iso.hom_inv_id, comp_id]
  refine ⟨fun y => ?_, fun x₁ x₂ hx => ?_⟩
  · obtain ⟨x, hx⟩ := h.1 (e₁.inv ≫ y)
    refine ⟨e₂.hom ≫ x, ?_⟩
    simp only at hx ⊢
    rw [← assoc, w, assoc, hx, Iso.hom_inv_id_assoc]
  · simp only at hx
    have : e₂.inv ≫ x₁ = e₂.inv ≫ x₂ := h.2 (by
      simp only
      rw [← assoc, w', assoc, hx, ← assoc, ← w', assoc])
    simpa using congrArg (e₂.hom ≫ ·) this

theorem relY_zero {A B : HomotopyCategory (Shv R) (ComplexShape.up ℤ)} (g : A ⟶ B) (hA : IsZero A) (hB : IsZero B) :
    Tri.RelY (Yres R F) n g :=
  ⟨fun y => ⟨0, hA.eq_of_src _ _⟩, fun _ _ _ => hB.eq_of_src _ _⟩

theorem isZero_cx {K : Cx R} (h : ∀ i, IsZero (K.X i)) : IsZero K := by
  rw [IsZero.iff_id_eq_zero]
  ext i : 1
  exact (h i).eq_of_src _ _

theorem relK_zero {K L : Cx R} (f : K ⟶ L) (hK : ∀ i, IsZero (K.X i)) (hL : ∀ i, IsZero (L.X i)) :
    RelK R F n f :=
  (relK_iff R f F n).2 (relY_zero R F n _ ((Q R).map_isZero (isZero_cx R hK)) ((Q R).map_isZero (isZero_cx R hL)))

theorem relK_piece_zero {K L : Cx R} (f : K ⟶ L) (p : ℕ) (hK : IsZero (K.X (-(p : ℤ)))) (hL : IsZero (L.X (-(p : ℤ)))) :
    RelK R F n (pieceC R f p) :=
  (relK_iff R _ F n).2 (relY_zero R F n _
    ((Q R).map_isZero ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) _).map_isZero hK))
    ((Q R).map_isZero ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) _).map_isZero hL)))

theorem relK_piece_iso {K L K' L' : Cx R} (f : K ⟶ L) (g : K' ⟶ L') (p : ℕ)
    (α : K'.X (-(p : ℤ)) ≅ K.X (-(p : ℤ))) (β : L'.X (-(p : ℤ)) ≅ L.X (-(p : ℤ)))
    (w : g.f (-(p : ℤ)) ≫ β.hom = α.hom ≫ f.f (-(p : ℤ))) (h : RelK R F n (pieceC R f p)) :
    RelK R F n (pieceC R g p) := by
  rw [relK_iff] at h ⊢
  refine relY_of_iso R F n _ _ ((Q R).mapIso ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) _).mapIso α))
    ((Q R).mapIso ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) _).mapIso β)) ?_ h
  simp only [Functor.mapIso_hom, pieceC, ← Functor.map_comp, w]

end RelYLemmas

theorem inv_nat {C : Type*} [Category C] {X₁ X₂ Y₁ Y₂ : C} (g₁ : X₁ ⟶ Y₁) (g₂ : X₂ ⟶ Y₂) [IsIso g₁] [IsIso g₂]
    (t₂ : X₁ ⟶ X₂) (t₃ : Y₁ ⟶ Y₂) (h : g₁ ≫ t₃ = t₂ ≫ g₂) : t₃ ≫ inv g₂ = inv g₁ ≫ t₂ := by
  rw [IsIso.comp_inv_eq, assoc, IsIso.eq_inv_comp, h]

theorem aux {C : Type*} [Category C] {A₃ A₂ B₂ B₁ A₃' A₂' B₂' B₁' : C} (s₁ : A₃ ⟶ A₂) (d₁ : A₂ ⟶ B₂)
    (r₁ : B₂ ⟶ B₁) (t₁ : B₁ ⟶ B₁') (t₃ : A₃ ⟶ A₃') (s₂ : A₃' ⟶ A₂') (d₂ : A₂' ⟶ B₂') (r₂ : B₂' ⟶ B₁')
    (ta : A₂ ⟶ A₂') (tb : B₂ ⟶ B₂') (hs : t₃ ≫ s₂ = s₁ ≫ ta) (hc : ta ≫ d₂ = d₁ ≫ tb) (hr : tb ≫ r₂ = r₁ ≫ t₁) :
    (s₁ ≫ d₁ ≫ r₁) ≫ t₁ = t₃ ≫ s₂ ≫ d₂ ≫ r₂ := by
  rw [reassoc_of% hs, reassoc_of% hc, hr]; simp only [assoc]

theorem hom_nat {C : Type*} [Category C] [Preadditive C] {S₁ S₂ : ShortComplex (CochainComplex C ℤ)} (φ : S₁ ⟶ S₂)
    (σ₁ : ∀ n, (S₁.map (HomologicalComplex.eval C _ n)).Splitting)
    (σ₂ : ∀ n, (S₂.map (HomologicalComplex.eval C _ n)).Splitting)
    (hs : ∀ n, φ.τ₃.f n ≫ (σ₂ n).s = (σ₁ n).s ≫ φ.τ₂.f n)
    (hr : ∀ n, φ.τ₂.f n ≫ (σ₂ n).r = (σ₁ n).r ≫ φ.τ₁.f n) :
    CochainComplex.homOfDegreewiseSplit S₁ σ₁ ≫ (CategoryTheory.shiftFunctor _ (1 : ℤ)).map φ.τ₁ =
      φ.τ₃ ≫ CochainComplex.homOfDegreewiseSplit S₂ σ₂ := by
  ext n
  simp [CochainComplex.cocycleOfDegreewiseSplit, CochainComplex.shiftFunctor_map_f']
  exact aux _ _ _ _ _ _ _ _ _ _ (hs n) (φ.τ₂.comm n (n + 1)) (hr (n + 1))

section Step
variable {R : Type} [CommRing R]

def qK (K : Cx R) (a : ℤ) (hK : ∀ i, i < a → IsZero (K.X i)) :
    K ⟶ (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) a).obj (K.X a) :=
  HomologicalComplex.mkHomToSingle (𝟙 _) (fun j hj => (hK j (by simp at hj; omega)).eq_of_src _ _)

theorem qK_iso (K : Cx R) (a : ℤ) (hK : ∀ i, i < a → IsZero (K.X i)) : IsIso ((qK K a hK).f a) := by
  rw [qK, HomologicalComplex.mkHomToSingle_f]; infer_instance

theorem qK_zero (K : Cx R) (a : ℤ) (hK : ∀ i, i < a → IsZero (K.X i)) (m : ℤ) (hm : m ≠ a) : (qK K a hK).f m = 0 :=
  (HomologicalComplex.isZero_single_obj_X _ _ _ _ hm).eq_of_tgt _ _

def lim (K : Cx R) (a : ℤ) (hK : ∀ i, i < a → IsZero (K.X i)) (m : ℤ) :=
  KernelFork.mapIsLimit _ (kernelIsKernel (qK K a hK)) (HomologicalComplex.eval (Shv R) (ComplexShape.up ℤ) m)

theorem ι_iso (K : Cx R) (a : ℤ) (hK : ∀ i, i < a → IsZero (K.X i)) (m : ℤ) (hm : m ≠ a) :
    IsIso ((kernel.ι (qK K a hK)).f m) :=
  isIso_limit_cone_parallelPair_of_eq (by exact qK_zero K a hK m hm) (lim K a hK m)

theorem ker_zero (K : Cx R) (a : ℤ) (hK : ∀ i, i < a → IsZero (K.X i)) :
    IsZero ((kernel (qK K a hK)).X a) := by
  have := qK_iso K a hK
  rw [IsZero.iff_id_eq_zero]
  refine Fork.IsLimit.hom_ext (lim K a hK a) ?_
  have h0 : (kernel.ι (qK K a hK)).f a = 0 := by
    rw [← cancel_mono ((qK K a hK).f a), ← HomologicalComplex.comp_f, kernel.condition]; simp
  change 𝟙 _ ≫ (kernel.ι (qK K a hK)).f a = 0 ≫ (kernel.ι (qK K a hK)).f a
  rw [h0, comp_zero, zero_comp]

theorem inv_nat' {C : Type*} [Category C] {X₁ X₂ Y₁ Y₂ : C} (g₁ : X₁ ⟶ Y₁) (g₂ : X₂ ⟶ Y₂) [IsIso g₁] [IsIso g₂]
    (t₂ : X₁ ⟶ X₂) (t₃ : Y₁ ⟶ Y₂) (h : g₁ ≫ t₃ = t₂ ≫ g₂) : t₃ ≫ inv g₂ = inv g₁ ≫ t₂ := inv_nat g₁ g₂ t₂ t₃ h

abbrev MainNotions (K : Cx R) (a : ℤ) (hK : ∀ i, i < a → IsZero (K.X i)) : ShortComplex (Cx R) :=
  ShortComplex.mk (kernel.ι (qK K a hK)) (qK K a hK) (kernel.condition _)

def spl (K : Cx R) (a : ℤ) (hK : ∀ i, i < a → IsZero (K.X i)) (m : ℤ) :
    ((MainNotions K a hK).map (HomologicalComplex.eval (Shv R) (ComplexShape.up ℤ) m)).Splitting :=
  if h : m = a then
    ShortComplex.Splitting.ofIsZeroOfIsIso _ (by subst h; exact ker_zero K m hK) (by subst h; exact qK_iso K m hK)
  else ShortComplex.Splitting.ofIsIsoOfIsZero _ (ι_iso K a hK m h) (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) a (K.X a) m h)

theorem dist (K : Cx R) (a : ℤ) (hK : ∀ i, i < a → IsZero (K.X i)) :
    CochainComplex.trianglehOfDegreewiseSplit (MainNotions K a hK) (spl K a hK) ∈ distTriang _ :=
  (HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit _).2 ⟨_, _, ⟨Iso.refl _⟩⟩

variable {K L : Cx R} (f : K ⟶ L) (a : ℤ) (hK : ∀ i, i < a → IsZero (K.X i)) (hL : ∀ i, i < a → IsZero (L.X i))

abbrev pc : (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) a).obj (K.X a) ⟶
    (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) a).obj (L.X a) :=
  (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) a).map (f.f a)

theorem hqf : qK K a hK ≫ pc f a = f ≫ qK L a hL := by
  apply HomologicalComplex.to_single_hom_ext
  simp [qK, pc, HomologicalComplex.single_map_f_self]

def sf : kernel (qK K a hK) ⟶ kernel (qK L a hL) := kernel.map _ _ f (pc f a) (hqf f a hK hL)

theorem hι : sf f a hK hL ≫ kernel.ι (qK L a hL) = kernel.ι (qK K a hK) ≫ f := by
  simp [sf]

def phiS : MainNotions K a hK ⟶ MainNotions L a hL where
  τ₁ := sf f a hK hL
  τ₂ := f
  τ₃ := pc f a
  comm₁₂ := hι f a hK hL
  comm₂₃ := (hqf f a hK hL).symm

theorem hs (m : ℤ) : (phiS f a hK hL).τ₃.f m ≫ (spl L a hL m).s = (spl K a hK m).s ≫ (phiS f a hK hL).τ₂.f m := by
  unfold spl
  split_ifs with h
  · subst h
    exact @inv_nat' _ _ _ _ _ _ _ _ (qK_iso K m hK) (qK_iso L m hL) _ _ (HomologicalComplex.congr_hom (phiS f m hK hL).comm₂₃ m).symm
  · simp only [ShortComplex.Splitting.ofIsIsoOfIsZero]
    erw [comp_zero, zero_comp]
    rfl

theorem hr (m : ℤ) : (phiS f a hK hL).τ₂.f m ≫ (spl L a hL m).r = (spl K a hK m).r ≫ (phiS f a hK hL).τ₁.f m := by
  unfold spl
  split_ifs with h
  · simp only [ShortComplex.Splitting.ofIsZeroOfIsIso]
    erw [comp_zero, zero_comp]
    rfl
  · exact @inv_nat' _ _ _ _ _ _ _ _ (ι_iso K a hK m h) (ι_iso L a hL m h) _ _ (HomologicalComplex.congr_hom (phiS f a hK hL).comm₁₂ m).symm

def triMap : CochainComplex.triangleOfDegreewiseSplit (MainNotions K a hK) (spl K a hK) ⟶
    CochainComplex.triangleOfDegreewiseSplit (MainNotions L a hL) (spl L a hL) :=
  Triangle.homMk _ _ (sf f a hK hL) f (pc f a) (hι f a hK hL).symm (hqf f a hK hL)
    (hom_nat (phiS f a hK hL) _ _ (hs f a hK hL) (hr f a hK hL))

end Step

section Main
variable (R : Type) [CommRing R] (F : Shv R) (n : ℤ)

theorem claim : ∀ (N : ℕ) {K L : Cx R} (f : K ⟶ L),
    (∀ i : ℤ, (0 < i ∨ i < -(N : ℤ) + 1) → IsZero (K.X i) ∧ IsZero (L.X i)) →
    (∀ p : ℕ, RelK R F n (pieceC R f p)) → RelK R F n f
  | 0, K, L, f, hz, _ => relK_zero R F n f (fun i => (hz i (by omega)).1) (fun i => (hz i (by omega)).2)
  | N + 1, K, L, f, hz, hp => by
    have hK : ∀ i, i < -(N : ℤ) → IsZero (K.X i) := fun i hi => (hz i (by push_cast; omega)).1
    have hL : ∀ i, i < -(N : ℤ) → IsZero (L.X i) := fun i hi => (hz i (by push_cast; omega)).2
    have ih := claim N (sf f (-(N : ℤ)) hK hL) (fun i hi => ?_) (fun p => ?_)
    · have h3 := hp N
      rw [relK_iff] at ih h3 ⊢
      exact Tri.relY_mid _ _ (dist K _ hK) (dist L _ hL) ((Q R).mapTriangle.map (triMap f _ hK hL))
        (Yres R F) (yresIso R F) n ih h3
    · by_cases hia : i = -(N : ℤ)
      · subst hia; exact ⟨ker_zero K _ hK, ker_zero L _ hL⟩
      · have h1 := ι_iso K _ hK i hia
        have h2 := ι_iso L _ hL i hia
        have hz' := hz i (by push_cast; omega)
        exact ⟨hz'.1.of_iso (asIso ((kernel.ι (qK K _ hK)).f i)), hz'.2.of_iso (asIso ((kernel.ι (qK L _ hL)).f i))⟩
    · by_cases hpa : -(p : ℤ) = -(N : ℤ)
      · exact relK_piece_zero R F n _ p (by rw [hpa]; exact ker_zero K _ hK) (by rw [hpa]; exact ker_zero L _ hL)
      · exact relK_piece_iso R F n f _ p (@asIso _ _ _ _ ((kernel.ι (qK K _ hK)).f _) (ι_iso K _ hK _ hpa))
          (@asIso _ _ _ _ ((kernel.ι (qK L _ hL)).f _) (ι_iso L _ hL _ hpa))
          (HomologicalComplex.congr_hom (hι f _ hK hL) _) (hp p)

end Main

end LateralTheory.E.TowerFinPf

theorem LateralTheory.E.FiltPf.TowerFin_of : LateralTheory.E.FiltPf.TowerFin := by
  intro R _ F K L f n P hz hp
  exact LateralTheory.E.TowerFinPf.claim R F n (P + 1) f (fun i hi => hz i (by push_cast at hi; omega)) hp
