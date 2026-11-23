import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.BlowOfBl
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.PresBC
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.CoordBC

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.Onto TopologicalSpace

namespace UpperTheory.Gal.KunnethLefschetz.G

variable {W Z Y W' Z' Y' : Scheme.{0}}

private lemma range_pb {i : W ⟶ Z} {i' : W' ⟶ Z'} {a : Z' ⟶ Z} {b : W' ⟶ W} (h : IsPullback b i' i a) :
    Set.range i' = a ⁻¹' Set.range i := by
  rw [← Scheme.Pullback.range_fst a i]
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨h.flip.isoPullback.hom w, by rw [← Scheme.Hom.comp_apply, h.flip.isoPullback_hom_fst]⟩
  · rintro ⟨y, rfl⟩
    exact ⟨h.flip.isoPullback.inv y, by rw [← Scheme.Hom.comp_apply, h.flip.isoPullback_inv_fst]⟩

private lemma iso_pb {π : Y ⟶ Z} {π' : Y' ⟶ Z'} {a : Z' ⟶ Z} {c : Y' ⟶ Y} (h : IsPullback c π' π a) (U : Z.Opens)
    (hi : IsIso (π ∣_ U)) : IsIso (π' ∣_ (a ⁻¹ᵁ U)) := by
  have R1 := isPullback_morphismRestrict π' (a ⁻¹ᵁ U)
  have R2 := (isPullback_morphismRestrict π U).flip
  have Rect := R1.flip.paste_horiz h
  rw [← morphismRestrict_ι a U] at Rect
  have comm : ((π' ⁻¹ᵁ (a ⁻¹ᵁ U)).ι ≫ c) ≫ π = (π' ∣_ (a ⁻¹ᵁ U) ≫ a ∣_ U) ≫ U.ι := by
    simpa only [Category.assoc] using Rect.w
  have sq := IsPullback.of_right (h₁₁ := R2.lift _ _ comm) (v₁₂ := π ∣_ U)
    (by rw [R2.lift_fst]; exact Rect) (R2.lift_snd _ _ comm) R2
  exact sq.isIso_snd_of_isIso

private def secPb (D : E.LineData Y) (c : Y' ⟶ Y) (C : Y.Opens) (σ : (C : Scheme.{0}) ⟶ D.Y) (hσ : σ ≫ D.f = C.ι) :
    ((c ⁻¹ᵁ C : Y'.Opens) : Scheme.{0}) ⟶ (D.pb c).Y :=
  pullback.lift (f := D.f) (g := c) ((c ∣_ C) ≫ σ) (c ⁻¹ᵁ C).ι (by rw [Category.assoc, hσ, morphismRestrict_ι])

private lemma secPb_f (D : E.LineData Y) (c : Y' ⟶ Y) (C : Y.Opens) (σ : (C : Scheme.{0}) ⟶ D.Y) (hσ : σ ≫ D.f = C.ι) :
    secPb D c C σ hσ ≫ (D.pb c).f = (c ⁻¹ᵁ C).ι := pullback.lift_snd _ _ _

private lemma secPb_fst (D : E.LineData Y) (c : Y' ⟶ Y) (C : Y.Opens) (σ : (C : Scheme.{0}) ⟶ D.Y) (hσ : σ ≫ D.f = C.ι) :
    (show _ ⟶ pullback D.f c from secPb D c C σ hσ) ≫ pullback.fst D.f c = (c ∣_ C) ≫ σ := pullback.lift_fst _ _ _

private lemma loc_pb (D : E.LineData Y) (c : Y' ⟶ Y) (h : sSup (Pb.𝒱D D) = ⊤) : sSup (Pb.𝒱D (D.pb c)) = ⊤ := by
  rw [eq_top_iff]
  intro y _
  have hy : c y ∈ sSup (Pb.𝒱D D) := by rw [h]; trivial
  obtain ⟨C, ⟨σ, hσ⟩, hC⟩ := Opens.mem_sSup.1 hy
  exact Opens.mem_sSup.2 ⟨c ⁻¹ᵁ C, ⟨secPb D c C σ hσ, secPb_f D c C σ hσ⟩, hC⟩

private lemma topIso_nat (c : Y' ⟶ Y) (C : Y.Opens) :
    c.app C ≫ (c ⁻¹ᵁ C).topIso.inv = C.topIso.inv ≫ (c ∣_ C).appTop := by
  simp [Scheme.Hom.appTop, morphismRestrict_app, Scheme.Opens.topIso_inv]
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]

private lemma eqn_pb {π : Y ⟶ Z} {π' : Y' ⟶ Z'} {a : Z' ⟶ Z} {c : Y' ⟶ Y} (h : IsPullback c π' π a) (V : Z.Opens)
    (C : Y.Opens) (hC : C ≤ π ⁻¹ᵁ V) (hC' : c ⁻¹ᵁ C ≤ π' ⁻¹ᵁ (a ⁻¹ᵁ V)) (t : Γ(Z, V)) :
    (c ∣_ C).appTop.hom (C.topIso.inv.hom ((π.appLE V C hC).hom t)) =
      (c ⁻¹ᵁ C).topIso.inv.hom ((π'.appLE (a ⁻¹ᵁ V) (c ⁻¹ᵁ C) hC').hom ((a.app V).hom t)) := by
  have e : π.appLE V C hC ≫ c.app C = a.app V ≫ π'.appLE (a ⁻¹ᵁ V) (c ⁻¹ᵁ C) hC' := by
    rw [Scheme.Hom.app_eq_appLE c, Scheme.Hom.appLE_comp_appLE, ← Scheme.Hom.comp_appLE]
    simp only [h.w]
  have e2 := congr($(e) ≫ (c ⁻¹ᵁ C).topIso.inv)
  rw [Category.assoc, Category.assoc, topIso_nat] at e2
  exact congr($(e2).hom t)

private lemma mem_C {A : Type} [CommRing A] (T : Set A) (x : A) :
    MvPolynomial.C x ∈ Ideal.span ((MvPolynomial.C : A →+* MvPolynomial Empty A) '' T) ↔ x ∈ Ideal.span T := by
  constructor
  · intro h
    let g : MvPolynomial Empty A →+* A := MvPolynomial.eval₂Hom (RingHom.id A) Empty.elim
    have hg : ∀ y, g (MvPolynomial.C y) = y := fun y => MvPolynomial.eval₂Hom_C _ _ _
    have := Ideal.mem_map_of_mem g h
    rw [Ideal.map_span, Set.image_image] at this
    simpa only [hg, Set.image_id'] using this
  · intro h
    have := Ideal.mem_map_of_mem (MvPolynomial.C : A →+* MvPolynomial Empty A) h
    rwa [Ideal.map_span] at this

private lemma app_zero (g : W' ⟶ Z') (U : Z'.Opens) (O : W'.Opens) (e : O = g ⁻¹ᵁ U) (h : O ≤ g ⁻¹ᵁ U) (x : Γ(Z', U)) :
    (g.appLE U O h).hom x = 0 ↔ (g.app U).hom x = 0 := by
  subst e
  rw [Scheme.Hom.app_eq_appLE]

private lemma ker_pb {i : W ⟶ Z} {i' : W' ⟶ Z'} {a : Z' ⟶ Z} {b : W' ⟶ W} (h : IsPullback b i' i a) [IsClosedImmersion i]
    (V : Z.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen (a ⁻¹ᵁ V)) (T : Set Γ(Z, V))
    (hk : RingHom.ker (i.app V).hom = Ideal.span T) :
    RingHom.ker (i'.app (a ⁻¹ᵁ V)).hom = Ideal.span ((a.app V).hom '' T) := by
  have e : b ⁻¹ᵁ (i ⁻¹ᵁ V) = i' ⁻¹ᵁ (a ⁻¹ᵁ V) := by
    change (b ≫ i) ⁻¹ᵁ V = (i' ≫ a) ⁻¹ᵁ V
    rw [h.w]
  have ev : ∀ (x : Γ(Z, V)) (u : Empty → Γ(W, i ⁻¹ᵁ V)),
      MvPolynomial.eval₂Hom (i.appLE V (i ⁻¹ᵁ V) le_rfl).hom u (MvPolynomial.C x) = (i.app V).hom x := by
    intro x u
    rw [MvPolynomial.eval₂Hom_C, Scheme.Hom.app_eq_appLE]
  have P := presBC i i' a b h V (i ⁻¹ᵁ V) le_rfl hV (hV.preimage i) hV' e.le Empty Empty.elim
    ((MvPolynomial.C : Γ(Z, V) →+* _) '' T) ?_ ?_
  · ext x
    have hs : MvPolynomial.map (a.app V).hom '' ((MvPolynomial.C : Γ(Z, V) →+* _) '' T) =
        (MvPolynomial.C : Γ(Z', a ⁻¹ᵁ V) →+* MvPolynomial Empty Γ(Z', a ⁻¹ᵁ V)) '' ((a.app V).hom '' T) := by
      simp [Set.image_image, MvPolynomial.map_C]
    rw [RingHom.mem_ker, ← app_zero i' _ _ e e.le, ← mem_C, ← hs, ← P.2.2, RingHom.mem_ker, MvPolynomial.eval₂Hom_C]
  · intro y
    obtain ⟨x, rfl⟩ := i.app_surjective V hV y
    exact ⟨MvPolynomial.C x, ev x _⟩
  · ext p
    obtain ⟨x, rfl⟩ := MvPolynomial.C_surjective Empty p
    rw [RingHom.mem_ker, ev, mem_C, ← hk, RingHom.mem_ker]

private lemma rel_pb {A B : Type} [CommRing A] [CommRing B] (g : A →+* B) {d : ℕ} (t : Fin d → A) (k : Fin d) :
    MvPolynomial.map g '' (insert (MvPolynomial.X k - 1)
      (Set.range fun j => MvPolynomial.C (t j) - MvPolynomial.C (t k) * MvPolynomial.X j) : Set (MvPolynomial (Fin d) A)) =
    insert (MvPolynomial.X k - 1) (Set.range fun j => MvPolynomial.C (g (t j)) - MvPolynomial.C (g (t k)) * MvPolynomial.X j) := by
  rw [Set.image_insert_eq, ← Set.range_comp]
  simp [Function.comp_def]

private lemma hE_pb {K K' : Type} [CommRing K] [CommRing K'] (φ : K →+* K') {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z}
    {π : Y ⟶ Z} {d : ℕ} {q' : Z' ⟶ Spec (CommRingCat.of K')} {a : Z' ⟶ Z}
    (hq : IsPullback a q' q (Spec.map (CommRingCat.ofHom φ))) {V : Z.Opens} (B : CrystallineSemistableComparison.Onto.BChart q i π d V) :
    IsAffineOpen (a ⁻¹ᵁ V) ∧ (MvPolynomial.eval₂Hom (Pb.strV q' (a ⁻¹ᵁ V)) fun s => (a.app V).hom (Sum.elim B.x B.t s)).Etale :=
  coordBC K K' φ q q' a hq V B.affine _ _ B.etale

private lemma hle_pb {π : Y ⟶ Z} {π' : Y' ⟶ Z'} {a : Z' ⟶ Z} {c : Y' ⟶ Y} (hc : IsPullback c π' π a) {V : Z.Opens}
    {C : Y.Opens} (h : C ≤ π ⁻¹ᵁ V) : c ⁻¹ᵁ C ≤ π' ⁻¹ᵁ (a ⁻¹ᵁ V) := fun y hy => by
  have h1 : π (c y) ∈ V := h hy
  have h2 : a (π' y) = π (c y) := by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hc.w]
  change a (π' y) ∈ V
  rw [h2]
  exact h1

private def chartPb {K K' : Type} [CommRing K] [CommRing K'] (φ : K →+* K') {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z}
    {π : Y ⟶ Z} {d : ℕ} {q' : Z' ⟶ Spec (CommRingCat.of K')} {i' : W' ⟶ Z'} {π' : Y' ⟶ Z'} {a : Z' ⟶ Z} {b : W' ⟶ W}
    {c : Y' ⟶ Y} (hq : IsPullback a q' q (Spec.map (CommRingCat.ofHom φ))) (hb : IsPullback b i' i a)
    (hc : IsPullback c π' π a) (hi : IsClosedImmersion i) {V : Z.Opens} (B : CrystallineSemistableComparison.Onto.BChart q i π d V) :
    CrystallineSemistableComparison.Onto.BChart q' i' π' d (a ⁻¹ᵁ V) where
  affine := (hE_pb φ hq B).1
  n := B.n
  x := fun s => (a.app V).hom (B.x s)
  t := fun s => (a.app V).hom (B.t s)
  etale := by
    convert (hE_pb φ hq B).2 using 2
    ext s
    cases s <;> rfl
  ker := by
    rw [ker_pb hb V B.affine (hE_pb φ hq B).1 _ B.ker, ← Set.range_comp]
    rfl
  C := fun k => c ⁻¹ᵁ B.C k
  C_aff := fun k => (presBC π π' a c hc V (B.C k) (B.C_le k) B.affine (B.C_aff k) (hE_pb φ hq B).1 (hle_pb hc (B.C_le k))
    (Fin d) (B.u k) _ (B.surj k) (B.rel k)).1
  C_le := fun k => hle_pb hc (B.C_le k)
  C_cover := fun y hy => by
    have h2 : a (π' y) = π (c y) := by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hc.w]
    have h1 : c y ∈ π ⁻¹ᵁ V := by
      change π (c y) ∈ V
      rw [← h2]
      exact hy
    obtain ⟨k, h3⟩ := Opens.mem_iSup.1 (B.C_cover h1)
    exact Opens.mem_iSup.2 ⟨k, h3⟩
  u := fun k j => (c.app (B.C k)).hom (B.u k j)
  surj := fun k => (presBC π π' a c hc V (B.C k) (B.C_le k) B.affine (B.C_aff k) (hE_pb φ hq B).1 (hle_pb hc (B.C_le k))
    (Fin d) (B.u k) _ (B.surj k) (B.rel k)).2.1
  rel := fun k => by
    rw [(presBC π π' a c hc V (B.C k) (B.C_le k) B.affine (B.C_aff k) (hE_pb φ hq B).1 (hle_pb hc (B.C_le k))
      (Fin d) (B.u k) _ (B.surj k) (B.rel k)).2.2, rel_pb]
  inter := fun k j => by
    rw [← Scheme.Hom.preimage_basicOpen, ← B.inter]
    rfl

theorem blowBC : BlowBC := by
  intro K K' _ _ φ W Z Y W' Z' Y' q i π D d q' i' π' a b c hq hb hc ⟨B⟩
  have hcl : IsClosedImmersion i := B.closed
  refine ⟨{
    closed := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hb hcl
    f := fun {V} e => B.f ((show V ⟶ pullback D.f c from e) ≫ pullback.fst D.f c)
    f_nat := fun g e => by
      rw [← B.f_nat]
      simp only [Category.assoc]
    f_u := fun e e' h => B.f_u _ _ _
    U := a ⁻¹ᵁ B.U
    U_eq := by
      rw [range_pb hb]
      change a ⁻¹' (B.U : Set Z) = _
      rw [B.U_eq, Set.preimage_compl]
    iso := iso_pb hc B.U B.iso
    unit := fun {V} e he => by
      apply B.unit
      have : ((show V ⟶ pullback D.f c from e) ≫ pullback.fst D.f c) ≫ D.f ≫ π = (e ≫ (D.pb c).f ≫ π') ≫ a := by
        have h1 : pullback.fst D.f c ≫ D.f = pullback.snd D.f c ≫ c := pullback.condition
        simp only [Category.assoc]
        rw [reassoc_of% h1, hc.w]
        rfl
      rw [this]
      exact he
    loc := loc_pb D c B.loc
    ι := B.ι
    fin := B.fin
    V := fun α => a ⁻¹ᵁ B.V α
    cover := by
      intro w _
      have h1 : b w ∈ i ⁻¹ᵁ (⨆ α, B.V α) := B.cover trivial
      obtain ⟨α, h2⟩ := Opens.mem_iSup.1 h1
      have h3 : a (i' w) = i (b w) := by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hb.w]
      refine Opens.mem_iSup.2 ⟨α, ?_⟩
      change a (i' w) ∈ B.V α
      rw [h3]
      exact h2
    c := fun α => chartPb φ hq hb hc hcl (B.c α)
    σ := fun α k => secPb D c ((B.c α).C k) (B.σ α k) (B.σ_f α k)
    σ_f := fun α k => secPb_f D c _ _ _
    f_σ := fun α k => by
      refine (congrArg B.f (secPb_fst D c _ _ _)).trans ?_
      rw [B.f_nat, B.f_σ]
      exact eqn_pb hc _ _ _ _ _ }⟩

end UpperTheory.Gal.KunnethLefschetz.G
