import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpOfIsCocycle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepOfFactoringCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueCommaOfBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLocOAff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictPull1InjectiveOfSepGlue
open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

noncomputable section

open GlobalTheory.CatCoh GlobalTheory.CechDR Opposite

namespace GlobalTheory.CechCmp

abbrev PairCov {Z Y : Scheme.{0}} {J : Type} (W : J → Z.Opens) (ι : Y ⟶ Z) : Type :=
  {p : Pair ι // ∃ i, p.1.2.1 ≤ W i}

abbrev pairCovIncl {Z Y : Scheme.{0}} {J : Type} (W : J → Z.Opens) (ι : Y ⟶ Z) :
    (PairCov W ι)ᵒᵖ ⥤ (Pair ι)ᵒᵖ :=
  (Monotone.functor (f := (Subtype.val : PairCov W ι → Pair ι)) fun _ _ h ↦ h).op

abbrev pairCovSnd {Z Y : Scheme.{0}} {J : Type} (W : J → Z.Opens) (ι : Y ⟶ Z) :
    (PairCov W ι)ᵒᵖ ⥤ (Bas W)ᵒᵖ :=
  (Monotone.functor (f := fun p : PairCov W ι ↦ (⟨p.1.1.2, p.2⟩ : Bas W))
    fun _ _ h ↦ Pair.le_snd (φ := ι) h).op

def pairCovPull {R R' : Type} [CommRing R] [CommRing R'] {Z Y : Scheme.{0}} {J : Type}
    (W : J → Z.Opens) {ι : Y ⟶ Z} {s : Z ⟶ Sp R} {s' : Y ⟶ Sp R'} {σ : R →+* R'}
    (w : ι ≫ s = s' ≫ spMap σ) :
    CoefMap σ (incl W ⋙ OAff s) (pairCovIncl W ι ⋙ OPair ι s') where
  G := pairCovSnd W ι
  α p := GlobalTheory.CechDR.secPull s s' p.unop.1
  naturality {p q} a b := (GlobalTheory.CechDR.pairPull w).naturality ((pairCovIncl W ι).map a) b
  smul p := semiHom_secPull w p.unop.1

theorem pairCov_pull1_eq {R R' : Type} [CommRing R] [CommRing R'] {Z Y : Scheme.{0}} {J : Type}
    (W : J → Z.Opens) {ι : Y ⟶ Z} {s : Z ⟶ Sp R} {s' : Y ⟶ Sp R'} {σ : R →+* R'}
    (w : ι ≫ s = s' ≫ spMap σ) (x : HO1 s) :
    (CoefMap.restrict (OPair ι s') (pairCovIncl W ι)).pull1 ((GlobalTheory.CechDR.pairPull w).pull1 x) =
      (pairCovPull W w).pull1 ((CoefMap.restrict (OAff s) (incl W)).pull1 x) := by
  rw [← CoefMap.pullCohomologyOne_comp, ← CoefMap.pullCohomologyOne_comp]
  exact CoefMap.pullCohomologyOne_eq_of_natTrans _ _ (𝟙 _) (fun T b ↦ by rw [NatTrans.id_app, mp_id]) x

theorem pairCov_restrict_injective {R' : Type} [CommRing R'] {Z Y : Scheme.{0}} [Z.IsSeparated]
    {J : Type} (W : J → Z.Opens) (hW : ⨆ i, W i = ⊤) (hWa : ∀ i, IsAffineOpen (W i)) (ι : Y ⟶ Z)
    (s' : Y ⟶ Sp R') :
    Function.Injective (CoefMap.restrict (OAff s') (pairCovIncl W ι ⋙ pairFst ι)).pull1 := by
  let G : (PairCov W ι)ᵒᵖ ⥤ AffOp Y := pairCovIncl W ι ⋙ pairFst ι
  have hcov : ∀ T : AffOp Y, ∃ (n : ℕ) (b : Fin n → (OAff s').obj T),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp Y) (u : T ⟶ S),
        IsUnit (mp (OAff s') u (b i)) →
          ∃ (t : (PairCov W ι)ᵒᵖ) (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u := by
    intro T
    have hT : IsAffineOpen T.unop.1 := T.unop.2
    let Gs : Set Γ(Y, T.unop.1) := {f | ∃ j, Y.basicOpen f ≤ ι ⁻¹ᵁ W j}
    have hG : Ideal.span Gs = ⊤ := by
      rw [← hT.self_le_iSup_basicOpen_iff]
      intro x hx
      have hxU : ι.base x ∈ ⨆ i, W i := by rw [hW]; trivial
      obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hxU
      obtain ⟨f, hf, hxf⟩ := hT.exists_basicOpen_le (V := ι ⁻¹ᵁ W j) ⟨x, hj⟩ hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, ⟨j, hf⟩⟩, hxf⟩
    obtain ⟨F, hFG, hF⟩ := (Ideal.span_eq_top_iff_finite Gs).1 hG
    refine ⟨F.card, fun i ↦ (F.equivFin.symm i).1, ?_, ?_⟩
    · have hR : Set.range (fun i : Fin F.card ↦ (F.equivFin.symm i).1) =
          (F : Set Γ(Y, T.unop.1)) := by
        ext f
        constructor
        · rintro ⟨i, rfl⟩; exact (F.equivFin.symm i).2
        · intro hf; exact ⟨F.equivFin ⟨f, hf⟩, by simp⟩
      exact hR ▸ hF
    · intro i S u hu
      obtain ⟨j, hj⟩ := hFG (F.equivFin.symm i).2
      set f : Γ(Y, T.unop.1) := (F.equivFin.symm i).1
      have hB : IsAffineOpen (Y.basicOpen f) := hT.basicOpen f
      have hBT : Y.basicOpen f ≤ T.unop.1 := Y.basicOpen_le f
      have hSB : S.unop.1 ≤ Y.basicOpen f := by
        have h1 : Y.basicOpen (Y.presheaf.map (homOfLE (leOfHom u.unop)).op f) = S.unop.1 :=
          Y.basicOpen_of_isUnit hu
        rw [Scheme.basicOpen_res] at h1
        rw [← h1]; exact inf_le_right
      let p : Pair ι := ⟨(⟨_, hB⟩, ⟨W j, hWa j⟩), hj⟩
      let t : PairCov W ι := ⟨p, j, le_rfl⟩
      refine ⟨op t, (homOfLE (show (⟨_, hB⟩ : Y.affineOpens) ≤ T.unop from hBT)).op,
        (homOfLE (show S.unop ≤ (⟨_, hB⟩ : Y.affineOpens) from hSB)).op, ?_⟩
      exact Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  have hdir : ∀ (t₁ t₂ : (PairCov W ι)ᵒᵖ) (S : AffOp Y), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) →
      ∃ (n : ℕ) (b : Fin n → (OAff s').obj S), Ideal.span (Set.range b) = ⊤ ∧
        ∀ (i : Fin n) (S' : AffOp Y) (u : S ⟶ S'), IsUnit (mp (OAff s') u (b i)) →
          ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S') := by
    intro t₁ t₂ S h₁ h₂
    refine ⟨1, fun _ ↦ 1, ?_, fun _ S' u _ ↦ ?_⟩
    · rw [Ideal.span_eq_top_iff_finite]
      exact ⟨{1}, by simp, by simp⟩
    · obtain ⟨j, hj⟩ := t₁.unop.2
      have hS'S : S'.unop.1 ≤ S.unop.1 := leOfHom u.unop
      have hS1 : S.unop.1 ≤ t₁.unop.1.1.1.1 := leOfHom h₁.unop
      have hS2 : S.unop.1 ≤ t₂.unop.1.1.1.1 := leOfHom h₂.unop
      let A : Z.affineOpens := ⟨t₁.unop.1.1.2.1 ⊓ t₂.unop.1.1.2.1,
        IsAffineOpen.inf t₁.unop.1.1.2.2 t₂.unop.1.1.2.2⟩
      have hA : S'.unop.1 ≤ ι ⁻¹ᵁ A.1 := fun y hy ↦
        ⟨t₁.unop.1.2 (hS1 (hS'S hy)), t₂.unop.1.2 (hS2 (hS'S hy))⟩
      let p₃ : Pair ι := ⟨(S'.unop, A), hA⟩
      let t₃ : PairCov W ι := ⟨p₃, j, inf_le_left.trans hj⟩
      refine ⟨op t₃, ⟨(homOfLE ?_).op⟩, ⟨(homOfLE ?_).op⟩, ⟨𝟙 _⟩⟩
      · exact ⟨hS'S.trans hS1, (inf_le_left : A.1 ≤ t₁.unop.1.1.2.1)⟩
      · exact ⟨hS'S.trans hS2, (inf_le_right : A.1 ≤ t₂.unop.1.1.2.1)⟩
  have H := _root_.GlobalTheory.CechDR.hasLoc_OAff s'
  have hs := _root_.GlobalTheory.sep_of_factoring_cover (OAff s') G H hcov
  have hg := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s') G H hcov hdir
  exact _root_.GlobalTheory.CatCoh.CoefMap.restrict_pull1_injective_of_sep_glue _ _ hs hg

end GlobalTheory.CechCmp

namespace GlobalTheory.CechCmp

theorem appLE_resG_eq {Z Y : Scheme.{0}} (ι : Y ⟶ Z) {A V : Z.Opens} {T B : Y.Opens} (hV : V ≤ A)
    (e : T ≤ ι ⁻¹ᵁ V) (e' : B ≤ ι ⁻¹ᵁ A) (hT : T ≤ B) (x : Γ(Z, A)) :
    (ι.appLE V T e).hom (resG Z hV x) = resG Y hT ((ι.appLE A B e').hom x) := by
  simp only [resG, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

theorem pullHO1_cmp_eq_zero_of_coboundary : ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) [Z.IsSeparated]
    (s : Z ⟶ Sp R) (J : Type) (W : J → Z.Opens) (hW : ⨆ i, W i = ⊤), (∀ i, IsAffineOpen (W i)) →
    ∀ (R' : Type) [CommRing R'] (σ : R →+* R') (Y : Scheme.{0}) (s' : Y ⟶ Sp R') (ι : Y ⟶ Z)
    (w : ι ≫ s = s' ≫ spMap σ) (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')), GlobalTheory.CechCmp.IsCocycle W c →
    (∃ h' : ∀ i, Γ(Y, ι ⁻¹ᵁ W i), ∀ i i', (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i')
      (fun _ hx => hx)).hom (c i i') = resG Y inf_le_left (h' i) - resG Y inf_le_right (h' i')) →
    GlobalTheory.CechDR.pullHO1 w (GlobalTheory.CechCmp.cmp s W hW c) = 0 := by
  intro R _ Z _ s J W hW hWa R' _ σ Y s' ι w c hc ⟨h', hh'⟩
  set y := GlobalTheory.CechDR.pullHO1 w (cmp s W hW c)
  have e1 : (GlobalTheory.CechDR.pairPull w).pull1 (cmp s W hW c) = (pairRes ι s').pull1 y :=
    isPullO_pullHO1 w _
  apply pairCov_restrict_injective W hW hWa ι s'
  rw [map_zero]
  have e2 : (CoefMap.restrict (OAff s') (pairCovIncl W ι ⋙ pairFst ι)).pull1 y =
      (CoefMap.restrict (OPair ι s') (pairCovIncl W ι)).pull1 ((pairRes ι s').pull1 y) := by
    rw [← CoefMap.pullCohomologyOne_comp]
    exact CoefMap.pullCohomologyOne_eq_of_natTrans _ _ (𝟙 _) (fun T b ↦ by rw [NatTrans.id_app, mp_id]) y
  rw [e2, ← e1, pairCov_pull1_eq, restrict_cmp s W hW hc, CoefMap.pullCohomologyOne_class, H1.mk_eq_zero]
  let ix : PairCov W ι → J := fun p ↦ idx (⟨p.1.1.2, p.2⟩ : Bas W)
  have hix : ∀ p : PairCov W ι, p.1.1.1.1 ≤ ι ⁻¹ᵁ W (ix p) := fun p y hy ↦
    le_idx (⟨p.1.1.2, p.2⟩ : Bas W) (p.1.2 hy)
  refine ⟨fun p ↦ -resG Y (hix p.unop) (h' (ix p.unop)), ?_⟩
  funext p q a
  have hqp : q.unop.1.1.1.1 ≤ p.unop.1.1.1.1 := Pair.le_fst (leOfHom a.unop)
  change -resG Y (hix q.unop) (h' (ix q.unop)) - resG Y hqp (-resG Y (hix p.unop) (h' (ix p.unop))) =
    (ι.appLE _ _ _).hom (resG Z _ (c (ix p.unop) (ix q.unop)))
  rw [map_neg, resG_resG']
  have hT : q.unop.1.1.1.1 ≤ ι ⁻¹ᵁ W (ix p.unop) ⊓ ι ⁻¹ᵁ W (ix q.unop) :=
    le_inf (hqp.trans (hix p.unop)) (hix q.unop)
  have hV : q.unop.1.1.2.1 ≤ W (ix p.unop) ⊓ W (ix q.unop) :=
    le_inf ((show q.unop.1.1.2.1 ≤ p.unop.1.1.2.1 from Pair.le_snd (leOfHom a.unop)).trans (le_idx (⟨p.unop.1.1.2, p.unop.2⟩ : Bas W)))
      (le_idx (⟨q.unop.1.1.2, q.unop.2⟩ : Bas W))
  have k := appLE_resG_eq ι (A := W (ix p.unop) ⊓ W (ix q.unop))
    (B := ι ⁻¹ᵁ W (ix p.unop) ⊓ ι ⁻¹ᵁ W (ix q.unop)) hV q.unop.1.2 (fun _ hx => hx) hT
    (c (ix p.unop) (ix q.unop))
  refine Eq.trans ?_ k.symm
  rw [hh', map_sub, resG_resG', resG_resG']
  ring

end GlobalTheory.CechCmp
