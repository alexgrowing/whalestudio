import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsAtExpLeB
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.MumCmp.SamePolIso
variable {R : Type} [CommRing R] [IsDomain R]

theorem grp_iso {B Q : Over (Sp R)} [GrpObj B] [GrpObj Q] {β : B.left ⟶ Q.left}
    (h : IsGrpPullback B Q (spMap (RingHom.id R)) β) : ∃ f : B ≅ Q, f.hom.left = β ∧ IsMonHom f.hom := by
  have hs : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _
  have h1 := h.1
  rw [hs] at h1
  have : IsIso β := h1.isIso_fst_of_isIso
  let f : B ⟶ Q := Over.homMk β (by simpa using h1.w)
  have : IsIso ((Over.forget (Sp R)).map f) := (inferInstance : IsIso β)
  have : IsIso f := isIso_of_reflects_iso f (Over.forget _)
  refine ⟨asIso f, rfl, isMonHom_of_mul _ fun T x y => ?_⟩
  let ρ : Over.mk (T.hom ≫ spMap (RingHom.id R)) ⟶ T := Over.homMk (𝟙 T.left) (by simp [hs])
  have e := h.2 T x y (ρ ≫ x ≫ f) (ρ ≫ y ≫ f) (by simp [ρ, f]) (by simp [ρ, f])
  apply Over.OverMorphism.ext
  rw [← MonObj.comp_mul] at e
  simpa [ρ, f] using e.symm

theorem gw_congr {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F))
    {f f' : Y ⟶ X'} (hf : f = f') (y : Y) {j j' : L.ι} (hj : j = j') {k k' : L'.ι} (hk : k = k') :
    gw w f y j k = gw w f' y j' k' := by
  subst hf hj hk; rfl

theorem exists_iso : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ D : DegPre R), SamePol D₀ D →
  ∃ (β : D₀.P.A ≅ D.P.A) (xe : D₀.X ≃+ D.X), IsMonHom β.hom ∧ (∀ χ, D₀.c χ ≫ β.hom = D.c (xe χ)) ∧
    ∃ wΛ : LB.Iso (abelian₂ D₀.P.A D₀.P.L)
        ((abelian₂ D.P.A D.P.L).pull (lift (fst D₀.P.A D₀.P.A ≫ β.hom) (snd D₀.P.A D₀.P.A ≫ β.hom) : G2 D₀.P.A ⟶ G2 D.P.A).left),
      wΛ.IsGen ∧
      ∀ (a a' : D₀.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι)
        (J' : ((TK R).left ⟶ D₀.P.A.left) → D₀.P.L.ι), Good D.P.L z J → Good D₀.P.L z J' →
        val (D₀.tau a a') (𝟙 _) z J' =
          GlobalTheory.PolDeg.lamVal wΛ (lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left z J J' *
            val (D.tau (xe a) (xe a')) (𝟙 _) z J := by
  intro R _ _ D₀ D h
  obtain ⟨Q, e₀, e, ⟨β₀, β₂₀, w₀, p₀, s₀, g₀, c₀, t₀⟩, ⟨β₁, β₂₁, w₁, p₁, s₁, g₁, c₁, t₁⟩⟩ := h
  have hs : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _
  obtain ⟨f₀, hf₀, m₀⟩ := grp_iso p₀
  obtain ⟨f₁, hf₁, m₁⟩ := grp_iso p₁
  have cc₀ : ∀ a, D₀.c a ≫ f₀.hom = Q.c (e₀ a) := fun a => Over.OverMorphism.ext (by
    rw [Over.comp_left, hf₀, c₀ a, hs, Category.id_comp])
  have cc₁ : ∀ a, D.c a ≫ f₁.hom = Q.c (e a) := fun a => Over.OverMorphism.ext (by
    rw [Over.comp_left, hf₁, c₁ a, hs, Category.id_comp])
  have ea : ∀ x, e ((e₀.trans e.symm) x) = e₀ x := fun x => by simp
  have hcβ : ∀ χ, D₀.c χ ≫ (f₀ ≪≫ f₁.symm).hom = D.c ((e₀.trans e.symm) χ) := fun χ => by
    rw [Iso.trans_hom, Iso.symm_hom, ← Category.assoc, cc₀, Iso.comp_inv_eq, cc₁, ea]
  have hF : (lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) :
      G2 D₀.P.A ⟶ G2 D.P.A).left ≫ β₂₁ = β₂₀ := by
    apply pullback.hom_ext
    · change _ ≫ β₂₁ ≫ (fst Q.B Q.B).left = β₂₀ ≫ (fst Q.B Q.B).left
      rw [s₁.1, s₀.1, ← Category.assoc, ← Over.comp_left, lift_fst, ← hf₁, ← hf₀, ← Over.comp_left, ← Over.comp_left]
      simp
    · change _ ≫ β₂₁ ≫ (snd Q.B Q.B).left = β₂₀ ≫ (snd Q.B Q.B).left
      rw [s₁.2, s₀.2, ← Category.assoc, ← Over.comp_left, lift_snd, ← hf₁, ← hf₀, ← Over.comp_left, ← Over.comp_left]
      simp

  subst hF
  have hLQ : (abelian₂ Q.B Q.M.L).IsLB := DVR.linComb_isLB _ Q.M.isLB _ _
  have hLD : (abelian₂ D.P.A D.P.L).IsLB := DVR.linComb_isLB _ D.P.isLB _ _
  have hLD₀ : (abelian₂ D₀.P.A D₀.P.L).IsLB := DVR.linComb_isLB _ D₀.P.isLB _ _
  obtain ⟨wΛ, T⟩ := exists_cancel hLQ w₁ w₀ ((isGen_iff _).1 g₁) ((isGen_iff _).1 g₀) hLD hLD₀
  refine ⟨f₀ ≪≫ f₁.symm, e₀.trans e.symm, ?_, hcβ, wΛ,
    (isGen_iff _).2 (T.pgen_cancel hLQ ((isGen_iff _).1 g₁) ((isGen_iff _).1 g₀)), ?_⟩
  · show IsMonHom (f₀.hom ≫ f₁.inv)
    infer_instance
  intro a a' z J J' hJ hJ'
  choose d hd using fun χ : (TK R).left ⟶ Q.B.left => exists_chart Q.M.isLB (χ z)
  have hκ : 𝟙 (TK R).left ≫ jK R = jK R ≫ spMap (RingHom.id R) := by rw [hs]; simp
  have A₀ := t₀ (𝟙 _) hκ a a' z d J' hd hJ'
  have A₁ := t₁ (𝟙 _) hκ ((e₀.trans e.symm) a) ((e₀.trans e.symm) a') z d J hd hJ
  rw [ea, ea] at A₁
  have hP : (lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left ≫ (lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left = (lift (toUnit (TK R) ≫ D.c ((e₀.trans e.symm) a)) (toUnit (TK R) ≫ D.c ((e₀.trans e.symm) a'))).left := by
    rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, Category.assoc, Category.assoc, hcβ, hcβ]
  have m₁ : β₂₁ ((lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left z)) ∈ (abelian₂ Q.B Q.M.L).U
      (fun I => d ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left ≫ ((lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left ≫ β₂₁) ≫ (psum Q.B (x2 Q.B) I.down).left)) := by
    have := Good.mem (L := Q.M.L) hd (fun I : ULift (Finset (Fin 2)) => (psum Q.B (x2 Q.B) I.down).left) ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left ≫ (lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left ≫ β₂₁)
    simp only [Category.assoc] at this ⊢
    exact this
  have m₂ : (lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left z) ∈ (abelian₂ D.P.A D.P.L).U (fun I => J ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left ≫ (lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left ≫ (psum D.P.A (x2 D.P.A) I.down).left)) := by
    have := Good.mem (L := D.P.L) hJ (fun I : ULift (Finset (Fin 2)) => (psum D.P.A (x2 D.P.A) I.down).left) ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left ≫ (lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left)
    simp only [Category.assoc] at this
    exact this
  have m₃ : (lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left z ∈ (abelian₂ D₀.P.A D₀.P.L).U (fun I => J' ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left ≫ (psum D₀.P.A (x2 D₀.P.A) I.down).left)) :=
    Good.mem (L := D₀.P.L) hJ' (fun I : ULift (Finset (Fin 2)) => (psum D₀.P.A (x2 D₀.P.A) I.down).left) (lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left
  have key := T _ (lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left z _ _ _ m₁ m₂ m₃
  have k₁ : gw w₁ ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left ≫ (lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left) z (fun I => d ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left ≫ ((lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left ≫ β₂₁) ≫ (psum Q.B (x2 Q.B) I.down).left))
      (fun I => J ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left ≫ (lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left ≫ (psum D.P.A (x2 D.P.A) I.down).left)) =
      GlobalTheory.PolDeg.lamVal w₁ (lift (toUnit (TK R) ≫ D.c ((e₀.trans e.symm) a))
        (toUnit (TK R) ≫ D.c ((e₀.trans e.symm) a'))).left z d J :=
    gw_congr w₁ hP z (funext fun I => by rw [← hP]; simp only [Category.assoc])
      (funext fun I => by rw [← hP]; simp only [Category.assoc])
  rw [k₁] at key
  rw [A₀, A₁]
  change gw w₀ (lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left z _ _ * _ = gw wΛ (lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left z _ _ * _
  rw [key, _root_.mul_assoc, _root_.mul_left_comm]
end GlobalTheory.MumCmp.SamePolIso
