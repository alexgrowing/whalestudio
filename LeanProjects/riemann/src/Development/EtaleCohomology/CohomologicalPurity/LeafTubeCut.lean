import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCutHoc

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut

def Good {d : ℕ} (P : SP d) (V : P.X.affineOpens) : Prop :=
  (P.ι.ker.ideal V).FG ∧ Chart d Γ(P.X, V.1) (P.ι.ker.ideal V)

structure Sys {d : ℕ} (P : SP d) where
  J : Type
  [ord : Preorder J]
  V : J → P.X.affineOpens
  mono : ∀ {j k}, j ≤ k → V j ≤ V k
  good : ∀ j, Good P (V j)
  cov : ∀ x : P.X, ∃ j, x ∈ (V j).1
  dir : ∀ (x : P.X) j k, x ∈ (V j).1 → x ∈ (V k).1 → ∃ l, l ≤ j ∧ l ≤ k ∧ x ∈ (V l).1

attribute [instance] Sys.ord

def Sys.all (hC : LeafChart) {d : ℕ} (P : SP d) : Sys P where
  J := {V : P.X.affineOpens // Good P V}
  V j := j.1
  mono h := h
  good j := j.2
  cov x := by
    obtain ⟨V, h, -, g⟩ := hC d P x ⊤ trivial
    exact ⟨⟨V, g⟩, h⟩
  dir x j k hj hk := by
    obtain ⟨V, h, l, g⟩ := hC d P x (j.1.1 ⊓ k.1.1) ⟨hj, hk⟩
    exact ⟨⟨V, g⟩, l.trans inf_le_left, l.trans inf_le_right, h⟩

variable {d : ℕ}

abbrev eta (H : Hens) (P : SP d) (V : P.X.affineOpens) : Γ(P.X, V.1) →+* H.obj Γ(P.X, V.1) (P.ι.ker.ideal V) := H.η _ _

abbrev hensTo (H : Hens) (P : SP d) (V : P.X.affineOpens) : Spec (H.obj Γ(P.X, V.1) (P.ι.ker.ideal V)) ⟶ P.X :=
  Spec.map (CommRingCat.ofHom (eta H P V)) ≫ V.2.fromSpec

def Sys.aff {P : SP d} (S : Sys P) : S.J ⥤ Scheme.{0} where
  obj j := Spec Γ(P.X, (S.V j).1)
  map f := Spec.map (P.X.presheaf.map (homOfLE (S.mono f.le)).op)
  map_id j := by rw [← Spec.map_id, ← P.X.presheaf.map_id]; rfl
  map_comp f g := by rw [← Spec.map_comp, ← P.X.presheaf.map_comp]; rfl

def Sys.hen {P : SP d} (S : Sys P) (H : Hens) : S.J ⥤ Scheme.{0} where
  obj j := Spec (H.obj Γ(P.X, (S.V j).1) (P.ι.ker.ideal (S.V j)))
  map f := Spec.map (CommRingCat.ofHom (H.map _ (P.ι.ker.ideal_le_comap_ideal (S.mono f.le))))
  map_id j := by
    have e : (P.X.presheaf.map (homOfLE (le_refl (S.V j).1)).op).hom = RingHom.id Γ(P.X, (S.V j).1) :=
      (congrArg CommRingCat.Hom.hom (P.X.presheaf.map_id (op (S.V j).1))).trans (CommRingCat.hom_id)
    have k : ∀ φ h, φ = RingHom.id _ → H.map (I := P.ι.ker.ideal (S.V j)) (J := P.ι.ker.ideal (S.V j)) φ h = RingHom.id _ := by
      rintro _ h rfl; exact H.map_id _ _ h
    exact (congrArg (fun φ => Spec.map (CommRingCat.ofHom φ)) (k _ _ e)).trans (Spec.map_id _)
  map_comp {i j k} f g := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← H.map_comp _ _ _ _ (fun x hx =>
      P.ι.ker.ideal_le_comap_ideal (S.mono f.le) (P.ι.ker.ideal_le_comap_ideal (S.mono g.le) hx))]
    congr 3
    rw [← CommRingCat.hom_comp, ← P.X.presheaf.map_comp]; rfl

def Sys.toAff {P : SP d} (S : Sys P) (H : Hens) : S.hen H ⟶ S.aff where
  app j := Spec.map (CommRingCat.ofHom (eta H P (S.V j)))
  naturality j k f := by
    dsimp only [Sys.hen, Sys.aff]
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, H.map_η]; rfl

theorem Sys.cocAff {P : SP d} (S : Sys P) : Coc (S.aff ⋙ yoneda) fun j => yoneda.map (S.V j).2.fromSpec := fun j k f =>
  (yoneda.map_comp _ _).symm.trans (congrArg yoneda.map ((S.V k).2.map_fromSpec (S.V j).2 (homOfLE (S.mono f.le)).op))

theorem Sys.cocHen {P : SP d} (S : Sys P) (H : Hens) :
    Coc (S.hen H ⋙ yoneda) fun j => yoneda.map (hensTo H P (S.V j)) := fun j k f =>
  (yoneda.map_comp _ _).symm.trans (congrArg yoneda.map (by
    have h := (S.toAff H).naturality f
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (S.V k).2.fromSpec) h).trans ((Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) ((S.V k).2.map_fromSpec (S.V j).2 (homOfLE (S.mono f.le)).op))))))

abbrev Sys.E {P : SP d} (S : Sys P) (H : Hens) : Spc := hoc (S.hen H ⋙ yoneda)

abbrev Sys.π {P : SP d} (S : Sys P) (H : Hens) : S.E H ⟶ sch.obj P.X := aug _ (S.cocHen H)

def LeafQuot : Prop := ∀ (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A), IndNbhd φ I →
  Function.Bijective (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map)

def LeafZ : Prop := ∀ (X Z : Scheme.{0}) (ι : Z ⟶ X) [IsClosedImmersion ι] (V : X.affineOpens) (B : Type) [CommRing B]
  (φ : Γ(X, V.1) →+* B),
  (∃ z, IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((ι.ker.ideal V).map φ)))) z
    (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) ι) ∧
  ∀ U : X.Opens, (U : Set X) = (Set.range ι)ᶜ →
    off B ((ι.ker.ideal V).map φ) = (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) ⁻¹ᵁ U

def LeafAbv : Prop := ∀ (Y X : Scheme.{0}) (w : Y ⟶ X) (U' : Y.Opens) (U : X.Opens) (h : U' = w ⁻¹ᵁ U),
  ∃ e : opn U' ≅ abv U (sch.map w), e.hom.right = 𝟙 (sch.obj Y) ∧ e.hom ≫ abvMap U (sch.map w) = opnMap w U' U h.le

def LeafLocFst : Prop := E1 → ∀ (H : Hens) (d : ℕ) (P : SP d) (V : P.X.affineOpens) (q : ℕ), IsUnit (q : Γ(P.X, ⊤)) → ∀ i,
  Eqv _ (pullback.fst (sch.map (hensTo H P V)) (sch.map P.ι)) (tw q i)

def LeafLocIso : Prop := ∀ (H : Hens) (d : ℕ) (P : SP d) (V : P.X.affineOpens) h,
  IsIso (pbRel (sch.map P.ι) (sch.map (Spec.map (CommRingCat.ofHom (eta H P V)))) (sch.map (hensTo H P V))
    (sch.map V.2.fromSpec) h)

def LeafLocHen : Prop := Hyp → ∀ (H : Hens) (d : ℕ) (P : SP d) (V : P.X.affineOpens) (q : ℕ), IsUnit (q : Γ(P.X, ⊤)) →
  (P.ι.ker.ideal V).FG → ∀ h, Exc q (abvRel P.U (sch.map (Spec.map (CommRingCat.ofHom (eta H P V)))) (sch.map (hensTo H P V))
    (sch.map V.2.fromSpec) h)

def LeafPrdAff : Prop := Hyp → ∀ (d q : ℕ) [NeZero q] (R B C : Type) [CommRing R] [CommRing B] [CommRing C]
  (ψ : MvPolynomial (Fin d) R →+* B) (η : B →+* C), IsUnit (q : R) →
  Nbhd ψ (Ideal.span (Set.range MvPolynomial.X)) → ∀ (I : Ideal B) (K : Ideal C), IndNbhd η I → K = I.map η → HenselianRing C K →
  ∀ (_ : Ideal.span (Set.range fun j => ψ (MvPolynomial.X j)) = I) hy (n i : ℤ),
  Function.Bijective fun a : Ht q (sp C) n i =>
    Hs.act q (P := opn (off C K)) a (thom d q C K (fun j => η (ψ (MvPolynomial.X j))) hy)

def LeafPrdRing : Prop := Hyp → ∀ (H : Hens) (d q : ℕ) [NeZero q] (A : Type) [CommRing A] (I : Ideal A), IsUnit (q : A) → I.FG →
  Chart d A I → ∀ c : Hs q (opn (off A I)) (2 * d) d,
  (∀ (B : Type) [CommRing B] (φ : A →+* B) (x : Fin d → B) hx h, φ.Etale →
    Hs.pull q (opnMap (Spec.map (CommRingCat.ofHom φ)) (off B (I.map φ)) (off A I) h) _ _ c = thom d q B (I.map φ) x hx) →
  ∀ h (n i : ℤ), Function.Bijective fun a : Ht q (sp (H.obj A I)) n i =>
    Hs.act q (P := opn (off (H.obj A I) (I.map (H.η A I)))) a
      (Hs.pull q (opnMap (Spec.map (CommRingCat.ofHom (H.η A I))) (off _ (I.map (H.η A I))) (off A I) h) _ _ c)

def LeafLocPrd : Prop := Hyp → ∀ (H : Hens) (d : ℕ) (P : SP d) (V : P.X.affineOpens) (q : ℕ) [NeZero q],
  IsUnit (q : Γ(P.X, ⊤)) → Good P V → Prd q P.U (sch.map (hensTo H P V)) (fcl d q P)

def LeafRefine : Prop := ∀ (hC : LeafChart) (H : Hens) (d : ℕ) (P' P : SP d) (φ : P'.Hom P),
  ∃ (S' : Sys P') (a : S'.E H ⟶ (Sys.all hC P').E H) (b : S'.E H ⟶ (Sys.all hC P).E H),
    a ≫ (Sys.all hC P').π H = S'.π H ∧ b ≫ (Sys.all hC P).π H = S'.π H ≫ sch.map φ.f

theorem hs_pull_comp (q : ℕ) {P'' P' P : Arrow Spc} (φ : P'' ⟶ P') (ψ : P' ⟶ P) (n i : ℤ) (x : Hs q P n i) :
    Hs.pull q (φ ≫ ψ) n i x = Hs.pull q φ n i (Hs.pull q ψ n i x) := by
  have e : dbl.map (φ ≫ ψ) = dbl.map φ ≫ dbl.map ψ := by
    exact (pushout.map_comp φ.left ψ.left _ _ _ _ (Arrow.w φ).symm (Arrow.w φ).symm (Arrow.w ψ).symm (Arrow.w ψ).symm).symm
  apply Subtype.ext
  change pull _ (dbl.map (φ ≫ ψ)) _ _ x.1 = pull _ (dbl.map φ) _ _ (pull _ (dbl.map ψ) _ _ x.1)
  rw [e, pull_comp]

theorem exc_comp (q : ℕ) {P'' P' P : Arrow Spc} {φ : P'' ⟶ P'} {ψ : P' ⟶ P} (h : Exc q φ) (h' : Exc q ψ) : Exc q (φ ≫ ψ) :=
  fun n i => by
    have e : ⇑(Hs.pull q (φ ≫ ψ) n i) = Hs.pull q φ n i ∘ Hs.pull q ψ n i := funext (hs_pull_comp q φ ψ n i)
    rw [e]; exact (h n i).comp (h' n i)

theorem eqv_comp {R : Type} [CommRing R] {E'' E' E : Spc} {f : E'' ⟶ E'} {g : E' ⟶ E} {F : Shv R} (h : Eqv R f F)
    (h' : Eqv R g F) : Eqv R (f ≫ g) F := fun n => by
  have e : ⇑(pull R (f ≫ g) F n) = pull R f F n ∘ pull R g F n := funext (pull_comp R f g F n)
  rw [e]; exact (h n).comp (h' n)

theorem eqv_iso {R : Type} [CommRing R] {E' E : Spc} (f : E' ⟶ E) [IsIso f] (F : Shv R) : Eqv R f F := fun n =>
  Function.bijective_iff_has_inverse.2 ⟨pull R (inv f) F n,
    fun x => by rw [← pull_comp, IsIso.inv_hom_id, pull_id], fun x => by rw [← pull_comp, IsIso.hom_inv_id, pull_id]⟩

theorem abvRel_abvMap {X : Scheme.{0}} (U : X.Opens) {E' E : Spc} (a : E' ⟶ E) (π' : E' ⟶ sch.obj X) (π : E ⟶ sch.obj X)
    (h : a ≫ π = π') : abvRel U a π' π h ≫ abvMap U π = abvMap U π' :=
  Arrow.hom_ext _ _ ((pullback.lift_snd _ _ _).trans (Category.comp_id _)) h

theorem goal_of (hH : LeafHens) (hC : LeafChart) (fst : LeafFstHoc) (rel : LeafRelHoc) (exc : LeafExcHoc) (prd : LeafPrdHoc)
    (loc : LeafLoc) (locExc : LeafLocExc) (lf : LeafLocFst) (li : LeafLocIso) (lh : LeafLocHen) (lp : LeafLocPrd)
    (ref : LeafRefine) : LeafTube := by
  intro hyp d
  obtain ⟨H⟩ := hH
  have hyp' := hyp
  obtain ⟨a1, -, a3, -, -, -, -, -, -, -, -, e1⟩ := hyp'
  have ok : ∀ (P : SP d) (S : Sys P) (q : ℕ) [NeZero q], IsUnit (q : Γ(P.X, ⊤)) →
      (∀ i, Eqv _ (pullback.fst (S.π H) (sch.map P.ι)) (tw q i)) ∧ (∀ i, Eqv _ (pullback.snd (S.π H) (sch.map P.ι)) (tw q i)) ∧
      Exc q (abvMap P.U (S.π H)) ∧ Prd q P.U (S.π H) (fcl d q P) := by
    intro P S q _ hq
    have L : Loc (aug _ S.cocAff) := loc S.J S.aff P.X (fun j => (S.V j).2.fromSpec) (fun j => (S.V j).2.isOpenImmersion_fromSpec)
      (fun x => by
        obtain ⟨j, h⟩ := S.cov x
        exact ⟨j, (S.V j).2.range_fromSpec.ge h⟩)
      (fun x j k hj hk => by
        obtain ⟨l, h, h', h''⟩ := S.dir x j k ((S.V j).2.range_fromSpec.le hj) ((S.V k).2.range_fromSpec.le hk)
        exact ⟨l, h, h', (S.V l).2.range_fromSpec.ge h''⟩) S.cocAff
    have hj : ∀ j, (Functor.whiskerRight (S.toAff H) yoneda).app j ≫ yoneda.map (S.V j).2.fromSpec =
        yoneda.map (hensTo H P (S.V j)) := fun j => (yoneda.map_comp _ _).symm
    have hj' := fun j => (disc.map_comp _ _).symm.trans (congrArg disc.map (hj j))
    have hg := map_aug _ _ _ (S.cocHen H) S.cocAff hj
    refine ⟨fun i => fst a3 _ _ _ _ _ _ (yoneda.map P.ι) _ (S.cocHen H) fun j => lf e1 H d P (S.V j) q hq i, fun i => ?_, ?_,
      prd hyp q _ _ _ P.U _ (S.cocHen H) _ _ _ fun j => lp hyp H d P (S.V j) q hq (S.good j)⟩
    · have e : pullback.snd (S.π H) (sch.map P.ι) =
          pbRel (sch.map P.ι) _ _ _ hg ≫ pullback.snd (aug _ S.cocAff) (sch.map P.ι) :=
        ((pullback.lift_snd _ _ _).trans (Category.comp_id _)).symm
      rw [e]
      refine eqv_comp (rel a3 _ _ _ _ _ _ _ _ (yoneda.map P.ι) _ _ (S.cocHen H) S.cocAff hj' hg fun j => ?_) fun n => ?_
      · exact @eqv_iso _ _ _ _ _ (li H d P (S.V j) (hj' j)) _
      · exact @a1 _ _ _ _ _ (L _ _ P.ι) _ n
    · rw [← abvRel_abvMap P.U _ _ _ hg]
      exact exc_comp q (exc a3 q _ _ _ _ _ P.U _ _ (S.cocHen H) S.cocAff hj' hg
        fun j => lh hyp H d P (S.V j) q hq (S.good j).1 (hj' j)) (locExc a1 q _ _ _ _ L)
  refine ⟨fun P => ⟨_, (Sys.all hC P).π H, ok P _⟩, fun P' P φ => ?_⟩
  obtain ⟨S', a, b, ha, hb⟩ := ref hC H d P' P φ
  exact ⟨⟨_, S'.π H, ok P' S'⟩, a, b, ha, hb⟩

end LateralTheory.CohomologicalPurity.TubeCut
