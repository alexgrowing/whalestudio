import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Desc.UAgree

theorem ext_of_schDom {W X Y Z : Scheme.{0}} {f g : X ⟶ Y} (s : Y ⟶ Z) [IsSeparated s] (h : f ≫ s = g ≫ s)
    (d : W ⟶ X) [IsSchemeTheoreticallyDominant d] (hU : d ≫ f = d ≫ g) : f = g := by
  let X' : Over Z := Over.mk (f ≫ s)
  let Y' : Over Z := Over.mk s
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g h.symm
  haveI : IsSeparated Y'.hom := ‹IsSeparated s›
  let U' : Over Z := Over.mk (d ≫ f ≫ s)
  let d' : U' ⟶ X' := Over.homMk d
  have e : d' ≫ f' = d' ≫ g' := by
    ext1
    exact hU
  let l := equalizer.lift d' e
  have hd : d = l.left ≫ (equalizer.ι f' g').left := by
    rw [← Over.comp_left, equalizer.lift_ι]; rfl
  have hker : (equalizer.ι f' g').left.ker = ⊥ := by
    apply le_bot_iff.1
    calc _ ≤ (l.left ≫ (equalizer.ι f' g').left).ker := Scheme.Hom.le_ker_comp _ _
      _ = ⊥ := by rw [← hd]; exact d.ker_eq_bot
  haveI : IsIso (equalizer.ι f' g').left := IsClosedImmersion.isIso_iff_ker_eq_bot.2 hker
  have h0 : IsIso ((Over.forget Z).map (equalizer.ι f' g')) := (inferInstance : IsIso (equalizer.ι f' g').left)
  have : IsIso (equalizer.ι f' g') := isIso_of_reflects_iso _ (Over.forget Z)
  have hfg : f' = g' := (cancel_epi (equalizer.ι f' g')).1 (equalizer.condition f' g')
  exact congrArg CommaMorphism.left hfg

theorem schDom_away {R : Type} [CommRing R] [IsDomain R] {f : R} (hf : f ≠ 0) {T : Scheme.{0}} (q : T ⟶ Sp R)
    [Flat q] : IsSchemeTheoreticallyDominant (pullback.fst q (awayMap f)) := by
  have hinj : Function.Injective (algebraMap R (Localization.Away f)) :=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  have : IsDominant (awayMap f) :=
    ⟨PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _ |>.2 (by
      exact ((RingHom.injective_iff_ker_eq_bot _).1 hinj).le.trans bot_le)⟩
  have : IsSchemeTheoreticallyDominant (awayMap f) := .of_isDominant _
  infer_instance

theorem ext_generic {R : Type} [CommRing R] [IsDomain R] {f : R} (hf : f ≠ 0) {T P : Scheme.{0}}
    (q : T ⟶ Sp R) [Flat q] (p : P ⟶ Sp R) [IsSeparated p] (u v : T ⟶ P) (hu : u ≫ p = q) (hv : v ≫ p = q)
    (h : pullback.fst q (awayMap f) ≫ u = pullback.fst q (awayMap f) ≫ v) : u = v := by
  haveI := schDom_away hf q
  exact ext_of_schDom p (hu.trans hv.symm) _ h

theorem flat_of_openIn {S S₁ P Y : Scheme.{0}} {h : Y ⟶ P} {q : Y ⟶ S₁} {p : P ⟶ S} {s : S₁ ⟶ S}
    (ho : OpenIn h q p s) [Flat s] : Flat h := by
  obtain ⟨w, hw⟩ := ho
  haveI := hw
  rw [← pullback.lift_fst h q w]
  infer_instance

variable {σ : Setup} (E : Emb σ)

def toA {T : Scheme.{0}} (x : T ⟶ E.P) (k : T ⟶ Sp (Localization.Away σ.f)) (w : x ≫ E.p = k ≫ awayMap σ.f) :
    Over.mk k ⟶ σ.A :=
  Over.homMk (E.cartA.lift x k w) (E.cartA.lift_snd _ _ _)

theorem toA_left {T : Scheme.{0}} (x : T ⟶ E.P) (k : T ⟶ Sp (Localization.Away σ.f))
    (w : x ≫ E.p = k ≫ awayMap σ.f) : (toA E x k w).left ≫ E.ιA = x :=
  E.cartA.lift_fst _ _ _

theorem gen_mul {S₁ S₂ : Scheme.{0}} {s₁ : S₁ ⟶ Sp σ.R} (H₁ : Over S₁) [GrpObj H₁] (H₂ : Over S₂) [GrpObj H₂]
    (h₁ : H₁.left ⟶ E.P) (h₂ : H₂.left ⟶ E.P) (w₁ : h₁ ≫ E.p = H₁.hom ≫ s₁)
    (m₁ : MulAgree H₁ σ.A h₁ E.ιA) (m₂ : MulAgree H₂ σ.A h₂ E.ιA) {T : Scheme.{0}} (t : T ⟶ S₁) (t' : T ⟶ S₂)
    (k : T ⟶ Sp (Localization.Away σ.f)) (hk : t ≫ s₁ = k ≫ awayMap σ.f) (a b : Over.mk t ⟶ H₁)
    (a' b' : Over.mk t' ⟶ H₂) (ha : a.left ≫ h₁ = a'.left ≫ h₂) (hb : b.left ≫ h₁ = b'.left ≫ h₂) :
    (a * b).left ≫ h₁ = (a' * b').left ≫ h₂ := by
  have pa : (a.left ≫ h₁) ≫ E.p = k ≫ awayMap σ.f := by
    rw [Category.assoc, w₁, ← Category.assoc, Over.w a]; exact hk
  have pb : (b.left ≫ h₁) ≫ E.p = k ≫ awayMap σ.f := by
    rw [Category.assoc, w₁, ← Category.assoc, Over.w b]; exact hk
  exact (m₁ T t k a b (toA E _ k pa) (toA E _ k pb) (toA_left E _ _ _).symm (toA_left E _ _ _).symm).trans
    (m₂ T t' k a' b' (toA E _ k pa) (toA E _ k pb) ((toA_left E _ _ _).trans ha).symm
      ((toA_left E _ _ _).trans hb).symm).symm

theorem gen_one {S : Scheme.{0}} {s : S ⟶ Sp σ.R} (H : Over S) [GrpObj H] (h : H.left ⟶ E.P)
    (w : h ≫ E.p = H.hom ≫ s) (m : MulAgree H σ.A h E.ιA) {T : Scheme.{0}} (t : T ⟶ S)
    (k : T ⟶ Sp (Localization.Away σ.f)) (hk : t ≫ s = k ≫ awayMap σ.f) :
    (1 : Over.mk t ⟶ H).left ≫ h = (1 : Over.mk k ⟶ σ.A).left ≫ E.ιA := by
  have pe : ((1 : Over.mk t ⟶ H).left ≫ h) ≫ E.p = k ≫ awayMap σ.f := by
    rw [Category.assoc, w, ← Category.assoc, Over.w]; exact hk
  have hm := m T t k 1 1 (toA E _ k pe) (toA E _ k pe) (toA_left E _ _ _).symm (toA_left E _ _ _).symm
  rw [_root_.mul_one] at hm
  have hee : toA E _ k pe * toA E _ k pe = toA E _ k pe := by
    apply Over.OverMorphism.ext
    apply E.cartA.hom_ext
    · rw [← hm, toA_left]
    · exact (Over.w _).trans (Over.w _).symm
  have h1 : toA E _ k pe = 1 := mul_eq_left.1 hee
  rw [← h1, toA_left]

theorem mul_agree {S₁ S₂ : Scheme.{0}} (s₁ : S₁ ⟶ Sp σ.R) (s₂ : S₂ ⟶ Sp σ.R)
    (H₁ : Over S₁) [GrpObj H₁] (H₂ : Over S₂) [GrpObj H₂] (h₁ : H₁.left ⟶ E.P) (h₂ : H₂.left ⟶ E.P)
    [Flat s₁] [Flat H₁.hom] [Flat h₂] (w₁ : h₁ ≫ E.p = H₁.hom ≫ s₁) (w₂ : h₂ ≫ E.p = H₂.hom ≫ s₂)
    [IsOpenImmersion (pullback.lift h₂ H₂.hom w₂)]
    (m₁ : MulAgree H₁ σ.A h₁ E.ιA) (m₂ : MulAgree H₂ σ.A h₂ E.ιA) : MulAgree H₁ H₂ h₁ h₂ := by
  haveI := E.sep
  obtain ⟨X₁, fa, fb, hX, _⟩ : ∃ (X₁ : Scheme.{0}) (fa fb : X₁ ⟶ H₁.left),
      IsPullback fa fb H₁.hom H₁.hom ∧ Flat fa :=
    ⟨_, _, _, IsPullback.of_hasPullback _ _, inferInstance⟩
  obtain ⟨Y, ya, ya', hY, _⟩ : ∃ (Y : Scheme.{0}) (ya : Y ⟶ X₁) (ya' : Y ⟶ H₂.left),
      IsPullback ya ya' (fa ≫ h₁) h₂ ∧ Flat ya :=
    ⟨_, _, _, IsPullback.of_hasPullback _ _, inferInstance⟩
  have cX : fa ≫ H₁.hom = fb ≫ H₁.hom := hX.w
  have cY : ya ≫ fa ≫ h₁ = ya' ≫ h₂ := hY.w
  have wY : (ya ≫ fb ≫ h₁) ≫ E.p = (ya' ≫ H₂.hom) ≫ s₂ := by
    simp only [Category.assoc]
    rw [w₁, ← reassoc_of% cX, ← w₁, reassoc_of% cY, w₂]
  obtain ⟨Tu, π, ρ, hT, _⟩ : ∃ (Tu : Scheme.{0}) (π : Tu ⟶ Y) (ρ : Tu ⟶ H₂.left),
      IsPullback π ρ (pullback.lift (ya ≫ fb ≫ h₁) (ya' ≫ H₂.hom) wY) (pullback.lift h₂ H₂.hom w₂) ∧ Flat π :=
    ⟨_, _, _, IsPullback.of_hasPullback _ _, inferInstance⟩
  have eT₁ : π ≫ ya ≫ fb ≫ h₁ = ρ ≫ h₂ := by
    have := hT.w =≫ pullback.fst E.p s₂
    simp only [Category.assoc] at this
    rw [pullback.lift_fst, pullback.lift_fst] at this
    exact this
  have eT₂ : π ≫ ya' ≫ H₂.hom = ρ ≫ H₂.hom := by
    have := hT.w =≫ pullback.snd E.p s₂
    simp only [Category.assoc] at this
    rw [pullback.lift_snd, pullback.lift_snd] at this
    simpa only [Category.assoc] using this
  let Au : Over.mk (π ≫ ya ≫ fa ≫ H₁.hom) ⟶ H₁ := Over.homMk (π ≫ ya ≫ fa) (by simp)
  let Bu : Over.mk (π ≫ ya ≫ fa ≫ H₁.hom) ⟶ H₁ := Over.homMk (π ≫ ya ≫ fb) (by simp [cX])
  let A'u : Over.mk (π ≫ ya' ≫ H₂.hom) ⟶ H₂ := Over.homMk (π ≫ ya') (by simp)
  let B'u : Over.mk (π ≫ ya' ≫ H₂.hom) ⟶ H₂ := Over.homMk ρ (by simp [eT₂])
  have key : (Au * Bu).left ≫ h₁ = (A'u * B'u).left ≫ h₂ := by
    haveI : Flat (π ≫ ya ≫ fa ≫ H₁.hom ≫ s₁) := inferInstance
    refine ext_generic σ.hf (π ≫ ya ≫ fa ≫ H₁.hom ≫ s₁) E.p _ _ ?_ ?_ ?_
    · rw [Category.assoc, w₁, ← Category.assoc, Over.w (Au * Bu)]; simp
    · rw [Category.assoc, w₂, ← Category.assoc, Over.w (A'u * B'u)]
      simp only [Over.mk_hom, Category.assoc]
      rw [← w₂, ← reassoc_of% cY, w₁]
    · have hk : (pullback.fst (π ≫ ya ≫ fa ≫ H₁.hom ≫ s₁) (awayMap σ.f) ≫ π ≫ ya ≫ fa ≫ H₁.hom) ≫ s₁ =
          pullback.snd (π ≫ ya ≫ fa ≫ H₁.hom ≫ s₁) (awayMap σ.f) ≫ awayMap σ.f := by
        simp only [Category.assoc]; exact pullback.condition
      let J₁ : Over.mk (pullback.fst (π ≫ ya ≫ fa ≫ H₁.hom ≫ s₁) (awayMap σ.f) ≫ π ≫ ya ≫ fa ≫ H₁.hom) ⟶
          Over.mk (π ≫ ya ≫ fa ≫ H₁.hom) := Over.homMk (pullback.fst _ _) (by simp)
      let J₂ : Over.mk (pullback.fst (π ≫ ya ≫ fa ≫ H₁.hom ≫ s₁) (awayMap σ.f) ≫ π ≫ ya' ≫ H₂.hom) ⟶
          Over.mk (π ≫ ya' ≫ H₂.hom) := Over.homMk (pullback.fst _ _) (by simp)
      have e1 : pullback.fst (π ≫ ya ≫ fa ≫ H₁.hom ≫ s₁) (awayMap σ.f) ≫ (Au * Bu).left =
          ((J₁ ≫ Au) * (J₁ ≫ Bu)).left := by
        rw [← MonObj.comp_mul, Over.comp_left]; rfl
      have e2 : pullback.fst (π ≫ ya ≫ fa ≫ H₁.hom ≫ s₁) (awayMap σ.f) ≫ (A'u * B'u).left =
          ((J₂ ≫ A'u) * (J₂ ≫ B'u)).left := by
        rw [← MonObj.comp_mul, Over.comp_left]; rfl
      have ha : (J₁ ≫ Au).left ≫ h₁ = (J₂ ≫ A'u).left ≫ h₂ := by
        simp [J₁, J₂, Au, A'u, cY]
      have hb : (J₁ ≫ Bu).left ≫ h₁ = (J₂ ≫ B'u).left ≫ h₂ := by
        simp [J₁, J₂, Bu, B'u, eT₁]
      calc _ = ((J₁ ≫ Au) * (J₁ ≫ Bu)).left ≫ h₁ := by rw [← e1, Category.assoc]
        _ = ((J₂ ≫ A'u) * (J₂ ≫ B'u)).left ≫ h₂ := gen_mul E H₁ H₂ h₁ h₂ w₁ m₁ m₂ _ _ _ hk _ _ _ _ ha hb
        _ = _ := by rw [← e2, Category.assoc]
  intro T t₁ t₂ a b a' b' ha hb
  obtain ⟨x, hx1, hx2⟩ : ∃ x, x ≫ fa = a.left ∧ x ≫ fb = b.left :=
    ⟨hX.lift a.left b.left ((Over.w a).trans (Over.w b).symm), hX.lift_fst _ _ _, hX.lift_snd _ _ _⟩
  have gY : x ≫ fa ≫ h₁ = a'.left ≫ h₂ := by rw [reassoc_of% hx1]; exact ha
  obtain ⟨y, hy1, hy2⟩ : ∃ y, y ≫ ya = x ∧ y ≫ ya' = a'.left :=
    ⟨hY.lift x a'.left gY, hY.lift_fst _ _ _, hY.lift_snd _ _ _⟩
  have gT : y ≫ pullback.lift (ya ≫ fb ≫ h₁) (ya' ≫ H₂.hom) wY = b'.left ≫ pullback.lift h₂ H₂.hom w₂ := by
    apply pullback.hom_ext <;> simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd]
    · rw [reassoc_of% hy1, reassoc_of% hx2]; exact hb
    · rw [reassoc_of% hy2]; exact (Over.w a').trans (Over.w b').symm
  obtain ⟨g, hg1, hg2⟩ : ∃ g, g ≫ π = y ∧ g ≫ ρ = b'.left :=
    ⟨hT.lift y b'.left gT, hT.lift_fst _ _ _, hT.lift_snd _ _ _⟩
  let G : Over.mk t₁ ⟶ Over.mk (π ≫ ya ≫ fa ≫ H₁.hom) := Over.homMk g (by
    simp only [Over.mk_hom]; rw [reassoc_of% hg1, reassoc_of% hy1, reassoc_of% hx1]; exact Over.w a)
  let G' : Over.mk t₂ ⟶ Over.mk (π ≫ ya' ≫ H₂.hom) := Over.homMk g (by
    simp only [Over.mk_hom]; rw [reassoc_of% hg1, reassoc_of% hy2]; exact Over.w a')
  have hA : G ≫ Au = a := Over.OverMorphism.ext (by
    simp only [G, Au, Over.comp_left, Over.homMk_left]; rw [reassoc_of% hg1, reassoc_of% hy1, hx1])
  have hB : G ≫ Bu = b := Over.OverMorphism.ext (by
    simp only [G, Bu, Over.comp_left, Over.homMk_left]; rw [reassoc_of% hg1, reassoc_of% hy1, hx2])
  have hA' : G' ≫ A'u = a' := Over.OverMorphism.ext (by
    simp only [G', A'u, Over.comp_left, Over.homMk_left]; rw [reassoc_of% hg1, hy2])
  have hB' : G' ≫ B'u = b' := Over.OverMorphism.ext (by
    simp only [G', B'u, Over.comp_left, Over.homMk_left]; exact hg2)
  calc (a * b).left ≫ h₁ = g ≫ (Au * Bu).left ≫ h₁ := by
        rw [← hA, ← hB, ← MonObj.comp_mul, Over.comp_left, Category.assoc]; rfl
    _ = g ≫ (A'u * B'u).left ≫ h₂ := by rw [key]
    _ = (a' * b').left ≫ h₂ := by
        rw [← hA', ← hB', ← MonObj.comp_mul, Over.comp_left, Category.assoc]; rfl

theorem one_agree {S₁ S₂ : Scheme.{0}} (s₁ : S₁ ⟶ Sp σ.R) (s₂ : S₂ ⟶ Sp σ.R)
    (H₁ : Over S₁) [GrpObj H₁] (H₂ : Over S₂) [GrpObj H₂] (h₁ : H₁.left ⟶ E.P) (h₂ : H₂.left ⟶ E.P)
    [Flat s₁] [Flat s₂] (w₁ : h₁ ≫ E.p = H₁.hom ≫ s₁) (w₂ : h₂ ≫ E.p = H₂.hom ≫ s₂)
    (m₁ : MulAgree H₁ σ.A h₁ E.ιA) (m₂ : MulAgree H₂ σ.A h₂ E.ιA) : OneAgree s₁ s₂ H₁ H₂ h₁ h₂ := by
  haveI := E.sep
  obtain ⟨Z, u₁, u₂, hP, _⟩ : ∃ (Z : Scheme.{0}) (u₁ : Z ⟶ S₁) (u₂ : Z ⟶ S₂), IsPullback u₁ u₂ s₁ s₂ ∧ Flat u₁ :=
    ⟨_, _, _, IsPullback.of_hasPullback _ _, inferInstance⟩
  have key : (1 : Over.mk u₁ ⟶ H₁).left ≫ h₁ = (1 : Over.mk u₂ ⟶ H₂).left ≫ h₂ := by
    haveI : Flat (u₁ ≫ s₁) := inferInstance
    refine ext_generic σ.hf (u₁ ≫ s₁) E.p _ _ ?_ ?_ ?_
    · rw [Category.assoc, w₁, ← Category.assoc, Over.w]; rfl
    · rw [Category.assoc, w₂, ← Category.assoc, Over.w]; exact hP.w.symm
    · have hk : (pullback.fst (u₁ ≫ s₁) (awayMap σ.f) ≫ u₁) ≫ s₁ =
          pullback.snd (u₁ ≫ s₁) (awayMap σ.f) ≫ awayMap σ.f := by
        rw [Category.assoc]; exact pullback.condition
      have hk' : (pullback.fst (u₁ ≫ s₁) (awayMap σ.f) ≫ u₂) ≫ s₂ =
          pullback.snd (u₁ ≫ s₁) (awayMap σ.f) ≫ awayMap σ.f := by
        rw [Category.assoc, ← hP.w]; exact pullback.condition
      let J₁ : Over.mk (pullback.fst (u₁ ≫ s₁) (awayMap σ.f) ≫ u₁) ⟶ Over.mk u₁ :=
        Over.homMk (pullback.fst _ _) rfl
      let J₂ : Over.mk (pullback.fst (u₁ ≫ s₁) (awayMap σ.f) ≫ u₂) ⟶ Over.mk u₂ :=
        Over.homMk (pullback.fst _ _) rfl
      calc pullback.fst (u₁ ≫ s₁) (awayMap σ.f) ≫ (1 : Over.mk u₁ ⟶ H₁).left ≫ h₁
            = (J₁ ≫ (1 : Over.mk u₁ ⟶ H₁)).left ≫ h₁ := by rw [Over.comp_left, Category.assoc]; rfl
        _ = (1 : Over.mk (pullback.fst (u₁ ≫ s₁) (awayMap σ.f) ≫ u₁) ⟶ H₁).left ≫ h₁ := by
            rw [MonObj.comp_one]
        _ = (1 : Over.mk (pullback.snd (u₁ ≫ s₁) (awayMap σ.f)) ⟶ σ.A).left ≫ E.ιA :=
            gen_one E H₁ h₁ w₁ m₁ _ _ hk
        _ = (1 : Over.mk (pullback.fst (u₁ ≫ s₁) (awayMap σ.f) ≫ u₂) ⟶ H₂).left ≫ h₂ :=
            (gen_one E H₂ h₂ w₂ m₂ _ _ hk').symm
        _ = (J₂ ≫ (1 : Over.mk u₂ ⟶ H₂)).left ≫ h₂ := by rw [MonObj.comp_one]
        _ = pullback.fst (u₁ ≫ s₁) (awayMap σ.f) ≫ (1 : Over.mk u₂ ⟶ H₂).left ≫ h₂ := by
            rw [Over.comp_left, Category.assoc]; rfl
  intro T t₁ t₂ hw
  obtain ⟨g, hg1, hg2⟩ : ∃ g, g ≫ u₁ = t₁ ∧ g ≫ u₂ = t₂ :=
    ⟨hP.lift t₁ t₂ hw, hP.lift_fst _ _ _, hP.lift_snd _ _ _⟩
  let G : Over.mk t₁ ⟶ Over.mk u₁ := Over.homMk g hg1
  let G' : Over.mk t₂ ⟶ Over.mk u₂ := Over.homMk g hg2
  calc (1 : Over.mk t₁ ⟶ H₁).left ≫ h₁ = (G ≫ (1 : Over.mk u₁ ⟶ H₁)).left ≫ h₁ := by rw [MonObj.comp_one]
    _ = g ≫ (1 : Over.mk u₁ ⟶ H₁).left ≫ h₁ := by rw [Over.comp_left, Category.assoc]; rfl
    _ = g ≫ (1 : Over.mk u₂ ⟶ H₂).left ≫ h₂ := by rw [key]
    _ = (G' ≫ (1 : Over.mk u₂ ⟶ H₂)).left ≫ h₂ := by rw [Over.comp_left, Category.assoc]; rfl
    _ = (1 : Over.mk t₂ ⟶ H₂).left ≫ h₂ := by rw [MonObj.comp_one]

end GlobalTheory.Desc.UAgree

open GlobalTheory.Desc.UAgree in

theorem GlobalTheory.Desc.mulAgree_oneAgree_of_openIn : ∀ (σ : Setup) (E : Emb σ) (S₁ S₂ : Scheme.{0}) (s₁ : S₁ ⟶ Sp σ.R) (s₂ : S₂ ⟶ Sp σ.R) (H₁ : Over S₁) [GrpObj H₁] (H₂ : Over S₂) [GrpObj H₂] (h₁ : H₁.left ⟶ E.P) (h₂ : H₂.left ⟶ E.P), Flat s₁ → Flat s₂ → Flat H₁.hom → Flat H₂.hom → OpenIn h₁ H₁.hom E.p s₁ → OpenIn h₂ H₂.hom E.p s₂ → MulAgree H₁ σ.A h₁ E.ιA → MulAgree H₂ σ.A h₂ E.ιA → MulAgree H₁ H₂ h₁ h₂ ∧ OneAgree s₁ s₂ H₁ H₂ h₁ h₂ := by
  intro σ E S₁ S₂ s₁ s₂ H₁ _ H₂ _ h₁ h₂ fs₁ fs₂ fH₁ fH₂ o₁ o₂ m₁ m₂
  haveI := fs₁; haveI := fs₂; haveI := fH₁; haveI := fH₂
  haveI : Flat h₂ := flat_of_openIn o₂
  obtain ⟨w₁, -⟩ := o₁
  obtain ⟨w₂, hw₂⟩ := o₂
  haveI := hw₂
  exact ⟨mul_agree E s₁ s₂ H₁ H₂ h₁ h₂ w₁ w₂ m₁ m₂, one_agree E s₁ s₂ H₁ H₂ h₁ h₂ w₁ w₂ m₁ m₂⟩
