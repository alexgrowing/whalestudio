import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechTripleRestrictCompositeInjectiveSecond
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj KaehlerDifferential
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.GroupLaw

section Bas

variable {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) {C : Type} [Category.{0} C]

def Bas (G : C ⥤ AffOp X) : Prop :=
  (∀ T : AffOp X, ∃ (n : ℕ) (b : Fin n → (OAff s).obj T),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X) (u : T ⟶ S),
        IsUnit (mp (OAff s) u (b i)) →
          ∃ (t : C) (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) ∧
    ∀ (t₁ t₂ : C) (S : AffOp X), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) →
      ∃ (n : ℕ) (b : Fin n → (OAff s).obj S), Ideal.span (Set.range b) = ⊤ ∧
        ∀ (i : Fin n) (S' : AffOp X) (u : S ⟶ S'), IsUnit (mp (OAff s) u (b i)) →
          ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')

variable {s} {G : C ⥤ AffOp X}

theorem Bas.sep (h : Bas s G) (T : AffOp X) (x : (OAff s).obj T)
    (hx : ∀ t (u : T ⟶ G.obj t), mp (OAff s) u x = 0) : x = 0 :=
  _root_.GlobalTheory.sep_of_factoring_cover (OAff s) G (_root_.GlobalTheory.CechDR.hasLoc_OAff s) h.1 T x hx

theorem Bas.pull1 [Quiver.IsThin C] (h : Bas s G) :
    Function.Bijective (CoefMap.restrict (OAff s) G).pull1 := by
  have H := _root_.GlobalTheory.CechDR.hasLoc_OAff s
  have hs := _root_.GlobalTheory.sep_of_factoring_cover (OAff s) G H h.1
  have hg := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s) G H h.1 h.2
  have hv := _root_.GlobalTheory.CatCoh.Desc.Basis.oneCocycle_vanishing_comma_of_basis (OAff s) G H h.1 h.2
  exact ⟨_root_.GlobalTheory.CatCoh.CoefMap.restrict_pull1_injective_of_sep_glue _ _ hs hg,
    _root_.GlobalTheory.CatCoh.pull1_restrict_surjective_of_comma _ _ hs hg hv⟩

theorem Bas.glob [Quiver.IsThin C] (h : Bas s G) :
    Function.Bijective (pullGlob1 (CoefMap.restrict (OAff s) G)) :=
  _root_.GlobalTheory.restrict_glob1_bijective _ _ (_root_.GlobalTheory.CechDR.form_eq_zero_of_basis_cover s G h.1)
    (_root_.GlobalTheory.CechDR.FormExt.glue_one_forms s G h.1 h.2)

theorem Bas.hyp [Quiver.IsThin C] (h : Bas s G) :
    Function.Bijective (pullHyp1 (CoefMap.restrict (OAff s) G)) :=
  restrict_bijective_one_of_basis s G h.1 h.2

theorem Bas.extend [Quiver.IsThin C] (h : Bas s G) (g' : ∀ t, (OAff s).obj (G.obj t))
    (hg' : ∀ ⦃t t' : C⦄ (a : t ⟶ t'), g' t' = mp (OAff s) (G.map a) (g' t)) :
    ∃ g : C0 (OAff s), (∀ ⦃T T' : AffOp X⦄ (φ : T ⟶ T'), g T' = mp (OAff s) φ (g T)) ∧
      ∀ t, g (G.obj t) = g' t := by
  have H := _root_.GlobalTheory.CechDR.hasLoc_OAff s
  exact _root_.GlobalTheory.compat_family_extend _ G (_root_.GlobalTheory.sep_of_factoring_cover (OAff s) G H h.1)
    (_root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s) G H h.1 h.2) g' hg'

theorem stein_const {D : Type} [Category.{0} D] {F : D ⥤ CommAlgCat.{0} R} (h : Stein F) (g : C0 F)
    (hg : ∀ ⦃T T' : D⦄ (φ : T ⟶ T'), g T' = mp F φ (g T)) : ∃ r : R, ∀ T, g T = algebraMap R _ r := by
  have h0 : d0 F g = 0 := by
    funext T T' φ
    rw [amitsur_d0_apply, hg φ, sub_self]; rfl
  obtain ⟨r, hr⟩ := (h.1 g).1 h0
  exact ⟨r, fun T ↦ (congrFun hr T).symm⟩

theorem Bas.stein [Quiver.IsThin C] (h : Bas s G) (hF : Stein (OAff s)) : Stein (G ⋙ OAff s) := by
  refine ⟨fun x ↦ ⟨fun hx ↦ ?_, ?_⟩, fun r r' e ↦ hF.2 ?_⟩
  · have hc : ∀ ⦃t t' : C⦄ (a : t ⟶ t'), x t' = mp (OAff s) (G.map a) (x t) := fun t t' a ↦
      sub_eq_zero.1 (congrFun (congrFun (congrFun hx t) t') a)
    obtain ⟨g, hg, hgx⟩ := h.extend x hc
    obtain ⟨r, hr⟩ := stein_const hF g hg
    exact ⟨r, funext fun t ↦ ((hr _).symm.trans (hgx t))⟩
  · rintro ⟨r, rfl⟩
    funext T T' φ
    have := (mp (G ⋙ OAff s) φ).commutes r
    rw [amitsur_d0_apply]
    exact sub_eq_zero.2 this.symm
  · funext T
    refine sub_eq_zero.1 (h.sep T _ fun t u ↦ ?_)
    have k : ∀ r : R, mp (OAff s) u (algebraMap R (C0 (OAff s)) r T) =
        algebraMap R (C0 (G ⋙ OAff s)) r t := fun r ↦ (mp (OAff s) u).commutes r
    rw [map_sub, sub_eq_zero, k, k]
    exact congrFun e t

theorem Bas.par [Quiver.IsThin C] (h : Bas s G) (hF : Par (OAff s)) : Par (G ⋙ OAff s) := by
  intro T
  let e : Glob1 (OAff s) ≃ₗ[R] Glob1 (G ⋙ OAff s) :=
    LinearEquiv.ofBijective (pullGlob1 (CoefMap.restrict (OAff s) G)) h.glob
  refine IsBaseChange.of_equiv ((e.symm.baseChange R ((G ⋙ OAff s).obj T) _ _).trans
    (hF (G.obj T)).equiv) fun x ↦ ?_
  obtain ⟨y, rfl⟩ := e.surjective x
  have k : (hF (G.obj T)).equiv ((1 : (G ⋙ OAff s).obj T) ⊗ₜ[R] y) = evForm (OAff s) (G.obj T) y := by
    rw [IsBaseChange.equiv_tmul, one_smul]
  simp only [LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul, LinearEquiv.symm_apply_apply]
  exact k.trans (cechDeRhamCoefMapOneForms_restrictAlongFunctor (OAff s) G T _).symm

end Bas

section Fam

variable {X Y : Scheme.{0}} {J : Type} (φ : J → (Y ⟶ X))

abbrev Fam : Type :=
  {q : Y.affineOpens × (J → X.affineOpens) // ∀ i, q.1.1 ≤ φ i ⁻¹ᵁ (q.2 i).1}

variable {φ}

theorem Fam.le_fst {p q : Fam φ} (h : p ≤ q) : p.1.1 ≤ q.1.1 :=
  (Prod.le_def.1 (Subtype.coe_le_coe.2 h)).1

theorem Fam.le_snd {p q : Fam φ} (h : p ≤ q) (i : J) : p.1.2 i ≤ q.1.2 i :=
  (Prod.le_def.1 (Subtype.coe_le_coe.2 h)).2 i

def Fam.pr (q : Fam φ) (i : J) : Pair (φ i) := ⟨(q.1.1, q.1.2 i), q.2 i⟩

variable (φ)

def famFst : (Fam φ)ᵒᵖ ⥤ AffOp Y :=
  (Monotone.functor (f := fun p : Fam φ ↦ p.1.1) fun _ _ h ↦ Fam.le_fst h).op

def famPair (i : J) : (Fam φ)ᵒᵖ ⥤ (Pair (φ i))ᵒᵖ :=
  (Monotone.functor (f := fun p : Fam φ ↦ p.pr i) fun _ _ h ↦
    Subtype.coe_le_coe.1 (Prod.le_def.2 ⟨Fam.le_fst h, Fam.le_snd h i⟩)).op

theorem bas_fam [Finite J] {R : Type} [CommRing R] (t : Y ⟶ Sp R) : Bas t (famFst φ) := by
  refine ⟨fun T ↦ ?_, fun t₁ t₂ S h₁ h₂ ↦ ?_⟩
  · have hT : IsAffineOpen T.unop.1 := T.unop.2
    let B : Set Γ(Y, T.unop.1) := {f | ∃ V : J → X.affineOpens, ∀ i, Y.basicOpen f ≤ φ i ⁻¹ᵁ (V i).1}
    have hB : Ideal.span B = ⊤ := by
      rw [← hT.self_le_iSup_basicOpen_iff]
      intro x hx
      have hV : ∀ i, ∃ V : X.affineOpens, (φ i).base x ∈ V.1 := fun i ↦ by
        obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := (φ i).base x)
          (U := (⊤ : X.Opens)) trivial
        exact ⟨⟨V, hV⟩, hxV⟩
      choose V hxV using hV
      let O : Y.Opens := ⟨⋂ i, (φ i ⁻¹ᵁ (V i).1 : Set Y),
        isOpen_iInter_of_finite fun i ↦ (φ i ⁻¹ᵁ (V i).1).2⟩
      have hxO : x ∈ O := Set.mem_iInter.2 fun i ↦ hxV i
      obtain ⟨f, hf, hxf⟩ := hT.exists_basicOpen_le (V := O) ⟨x, hxO⟩ hx
      exact TopologicalSpace.Opens.mem_iSup.2
        ⟨⟨f, ⟨V, fun i y hy ↦ Set.mem_iInter.1 (hf hy) i⟩⟩, hxf⟩
    obtain ⟨F, hFB, hF⟩ := (Ideal.span_eq_top_iff_finite B).1 hB
    refine ⟨F.card, fun i ↦ (F.equivFin.symm i).1, ?_, fun i S u hu ↦ ?_⟩
    · have hR : Set.range (fun i : Fin F.card ↦ (F.equivFin.symm i).1) = (F : Set Γ(Y, T.unop.1)) := by
        ext f
        constructor
        · rintro ⟨i, rfl⟩; exact (F.equivFin.symm i).2
        · intro hf; exact ⟨F.equivFin ⟨f, hf⟩, by simp⟩
      exact hR ▸ hF
    · obtain ⟨V, hV⟩ := hFB (F.equivFin.symm i).2
      set f : Γ(Y, T.unop.1) := (F.equivFin.symm i).1
      have hW : IsAffineOpen (Y.basicOpen f) := hT.basicOpen f
      have hWT : Y.basicOpen f ≤ T.unop.1 := Y.basicOpen_le f
      let q : Fam φ := ⟨(⟨_, hW⟩, V), hV⟩
      have hSW : S.unop.1 ≤ Y.basicOpen f := by
        have h1 : Y.basicOpen (Y.presheaf.map (homOfLE (leOfHom u.unop)).op f) = S.unop.1 :=
          Y.basicOpen_of_isUnit hu
        rw [Scheme.basicOpen_res] at h1
        rw [← h1]; exact inf_le_right
      refine ⟨Opposite.op q, (homOfLE (show (⟨_, hW⟩ : Y.affineOpens) ≤ T.unop from hWT)).op,
        (homOfLE (show S.unop ≤ (⟨_, hW⟩ : Y.affineOpens) from hSW)).op, ?_⟩
      exact Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  · have hS₁ : S.unop.1 ≤ t₁.unop.1.1.1 := leOfHom h₁.unop
    have hS₂ : S.unop.1 ≤ t₂.unop.1.1.1 := leOfHom h₂.unop
    let B : Set Γ(Y, S.unop.1) := {g | ∃ W : J → X.affineOpens,
      (∀ i, (W i).1 ≤ (t₁.unop.1.2 i).1) ∧ (∀ i, (W i).1 ≤ (t₂.unop.1.2 i).1) ∧
        ∀ i, Y.basicOpen g ≤ φ i ⁻¹ᵁ (W i).1}
    have hB : Ideal.span B = ⊤ := by
      refine (S.unop.2.self_le_iSup_basicOpen_iff).1 fun x hx ↦ ?_
      have hW : ∀ i, ∃ W : X.affineOpens, (φ i).base x ∈ W.1 ∧ W.1 ≤ (t₁.unop.1.2 i).1 ∧
          W.1 ≤ (t₂.unop.1.2 i).1 := fun i ↦ by
        obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset (x := (φ i).base x)
          (U := (t₁.unop.1.2 i).1 ⊓ (t₂.unop.1.2 i).1) ⟨t₁.unop.2 i (hS₁ hx), t₂.unop.2 i (hS₂ hx)⟩
        exact ⟨⟨W, hW⟩, hxW, fun y hy ↦ (hWV hy).1, fun y hy ↦ (hWV hy).2⟩
      choose W hxW hW₁ hW₂ using hW
      let O : Y.Opens := ⟨⋂ i, (φ i ⁻¹ᵁ (W i).1 : Set Y),
        isOpen_iInter_of_finite fun i ↦ (φ i ⁻¹ᵁ (W i).1).2⟩
      have hxO : x ∈ O := Set.mem_iInter.2 fun i ↦ hxW i
      obtain ⟨f, hf, hxf⟩ := S.unop.2.exists_basicOpen_le (V := O) ⟨x, hxO⟩ hx
      exact TopologicalSpace.Opens.mem_iSup.2
        ⟨⟨f, ⟨W, hW₁, hW₂, fun i y hy ↦ Set.mem_iInter.1 (hf hy) i⟩⟩, hxf⟩
    obtain ⟨s0, hs0, hspan⟩ := (Ideal.span_eq_top_iff_finite B).1 hB
    refine ⟨s0.card, fun i ↦ (s0.equivFin.symm i).1, ?_, fun i S' u hu ↦ ?_⟩
    · have hsp : Ideal.span (Set.range fun i ↦ ((s0.equivFin.symm i).1 : Γ(Y, S.unop.1))) = ⊤ := by
        rw [eq_top_iff, ← hspan]
        exact Ideal.span_mono fun x hx ↦ ⟨s0.equivFin ⟨x, hx⟩, by simp⟩
      exact hsp
    · obtain ⟨W, hW₁, hW₂, hg⟩ := hs0 (s0.equivFin.symm i).2
      set g : Γ(Y, S.unop.1) := (s0.equivFin.symm i).1
      change IsUnit (Y.presheaf.map (homOfLE (show S'.unop.1 ≤ S.unop.1 from leOfHom u.unop)).op g) at hu
      have hS' : S'.unop.1 ≤ Y.basicOpen g := by
        have := Scheme.basicOpen_of_isUnit Y hu
        rw [Scheme.basicOpen_res] at this
        rw [← this]; exact inf_le_right
      let t₃ : Fam φ := ⟨(⟨Y.basicOpen g, S.unop.2.basicOpen g⟩, W), hg⟩
      refine ⟨Opposite.op t₃, ⟨(homOfLE ?_).op⟩, ⟨(homOfLE ?_).op⟩, ⟨(homOfLE ?_).op⟩⟩
      · exact Subtype.coe_le_coe.1 (Prod.le_def.2 ⟨(Y.basicOpen_le g).trans hS₁, fun i ↦ hW₁ i⟩)
      · exact Subtype.coe_le_coe.1 (Prod.le_def.2 ⟨(Y.basicOpen_le g).trans hS₂, fun i ↦ hW₂ i⟩)
      · exact hS'

variable {φ}
variable {R : Type} [CommRing R] {s : X ⟶ Sp R} {t : Y ⟶ Sp R}

def famPull (h : ∀ i, φ i ≫ s = t ≫ spMap (RingHom.id R)) (i : J) :
    CoefMap (RingHom.id R) (OAff s) (famFst φ ⋙ OAff t) where
  G := famPair φ i ⋙ pairSnd (φ i)
  α T := (pairPull (h i)).α ((famPair φ i).obj T)
  naturality a b := (pairPull (h i)).naturality ((famPair φ i).map a) b
  smul T := (pairPull (h i)).smul ((famPair φ i).obj T)

def famRes (t : Y ⟶ Sp R) (i : J) : CoefMap (RingHom.id R) (OPair (φ i) t) (famFst φ ⋙ OAff t) where
  G := famPair φ i
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

variable (h : ∀ i, φ i ≫ s = t ≫ spMap (RingHom.id R))

theorem famPull_pull1 (i : J) (x : HO1 s) :
    (famPull h i).pull1 x = (CoefMap.restrict (OAff t) (famFst φ)).pull1 (pullHO1 (h i) x) := by
  have e1 : (famPull h i).pull1 x = (famRes t i).pull1 ((pairPull (h i)).pull1 x) := by
    rw [← CoefMap.pullCohomologyOne_comp]
    exact CoefMap.pullCohomologyOne_eq_of_natTrans _ ((pairPull (h i)).comp (famRes t i)) { app U := 𝟙 _ }
      (fun U b ↦ by erw [mp_id]) x
  have e2 : ∀ y : HO1 t, (CoefMap.restrict (OAff t) (famFst φ)).pull1 y =
      (famRes t i).pull1 ((pairRes (φ i) t).pull1 y) := fun y ↦ by
    rw [← CoefMap.pullCohomologyOne_comp]
    exact CoefMap.pullCohomologyOne_eq_of_natTrans _ ((pairRes (φ i) t).comp (famRes t i)) { app U := 𝟙 _ }
      (fun U b ↦ by erw [mp_id]; rfl) y
  rw [e1, e2]
  exact congrArg _ (isPullO_pullHO1 (h i) x)

theorem famPull_hyp (i : J) (x : HH1 s) :
    pullHyp1 (famPull h i) x = pullHyp1 (CoefMap.restrict (OAff t) (famFst φ)) (pullHH1 (h i) x) := by
  have e1 : pullHyp1 (famPull h i) x = pullHyp1 (famRes t i) (pullHyp1 (pairPull (h i)) x) := by
    rw [← pullHyp1_comp]
    exact pullHyp1_eq_of_natTrans _ ((pairPull (h i)).comp (famRes t i)) { app U := 𝟙 _ }
      (fun U b ↦ by erw [mp_id]) x
  have e2 : ∀ y : HH1 t, pullHyp1 (CoefMap.restrict (OAff t) (famFst φ)) y =
      pullHyp1 (famRes t i) (pullHyp1 (pairRes (φ i) t) y) := fun y ↦ by
    rw [← pullHyp1_comp]
    exact pullHyp1_eq_of_natTrans _ ((pairRes (φ i) t).comp (famRes t i)) { app U := 𝟙 _ }
      (fun U b ↦ by erw [mp_id]; rfl) y
  rw [e1, e2]
  exact congrArg _ (isPull1_pullHH1 (h i) x)

theorem famPull_glob (i : J) (x : GlobForm s) :
    pullGlob1 (famPull h i) x =
      pullGlob1 (CoefMap.restrict (OAff t) (famFst φ)) (pullForm (h i) x) := by
  refine Subtype.ext (funext fun T ↦ ?_)
  have k := isPullForm_iff.1 (isPullForm_pullForm (h i) x) (T.unop.pr i)
  exact k.trans (cechDeRhamCoefMapOneForms_restrictAlongFunctor (OAff t) (famFst φ) T _).symm

end Fam

section Comp

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {X X' X'' : Scheme.{0}}
  {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R →+* R'} {τ : R' →+* R''}
  {φ : X' ⟶ X} {ψ : X'' ⟶ X'}

theorem bas_pair (φ : X' ⟶ X) (s' : X' ⟶ Sp R') : Bas s' (pairFst φ) :=
  ⟨pair_cover_affine φ s', exists_pair_below_two φ s'⟩

theorem bas_triple (ψ : X'' ⟶ X') (φ : X' ⟶ X) (s'' : X'' ⟶ Sp R'') :
    Bas s'' (cechTripleProjFirstThird ψ φ ⋙ pairFst (ψ ≫ φ)) :=
  ⟨triple_cover_affine ψ φ s'', exists_triple_below_two ψ φ s''⟩

theorem cechTripleRestrictComposite_comp_pairRestrict (s'' : X'' ⟶ Sp R'') (c : HO1 s'') :
    (cechTripleRestrictComposite ψ φ s'').pull1 ((pairRes (ψ ≫ φ) s'').pull1 c) =
      (CoefMap.restrict (OAff s'') (cechTripleProjFirstThird ψ φ ⋙ pairFst (ψ ≫ φ))).pull1 c := by
  rw [← CoefMap.pullCohomologyOne_comp]
  exact CoefMap.pullCohomologyOne_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ mp_id (OAff s'') _ b) c

theorem cechTripleRestrictComposite_injective_cohomology_forms (s'' : X'' ⟶ Sp R'') : Function.Injective (cechTripleRestrictComposite ψ φ s'').pull1 := by
  intro x y e
  obtain ⟨x0, rfl⟩ := (pairRes_bijective (ψ ≫ φ) s'').1.2 x
  obtain ⟨y0, rfl⟩ := (pairRes_bijective (ψ ≫ φ) s'').1.2 y
  rw [cechTripleRestrictComposite_comp_pairRestrict, cechTripleRestrictComposite_comp_pairRestrict] at e
  rw [(bas_triple ψ φ s'').pull1.1 e]

theorem tri_pull_pullO (h : φ ≫ s = s' ≫ spMap σ) (h' : ψ ≫ s' = s'' ≫ spMap τ)
    (h'' : (ψ ≫ φ) ≫ s = s'' ≫ spMap (τ.comp σ)) (a : HO1 s) :
    (cechTripleRestrictComposite ψ φ s'').pull1 ((pairPull h'').pull1 a) =
      (cechTriplePullbackSecond h').pull1 ((pairPull h).pull1 a) := by
  rw [← CoefMap.pullCohomologyOne_comp, ← CoefMap.pullCohomologyOne_comp]
  exact CoefMap.pullCohomologyOne_eq_of_natTrans ((pairPull h'').comp (cechTripleRestrictComposite ψ φ s''))
    ((pairPull h).comp (cechTriplePullbackSecond h')) { app U := 𝟙 _ } (fun U b ↦ by
      erw [mp_id]
      exact congrArg (fun q ↦ q.hom b) (Scheme.Hom.appLE_comp_appLE ψ φ U.unop.1.2.2.1 U.unop.1.2.1.1
        U.unop.1.1.1 U.unop.2.2 U.unop.2.1)) a

theorem tri_res_pullO (h' : ψ ≫ s' = s'' ≫ spMap τ) (a : HO1 s') :
    (cechTriplePullbackSecond (φ := φ) h').pull1 ((pairRes φ s').pull1 a) =
      (cechTripleRestrictFirst ψ φ s'').pull1 ((pairPull h').pull1 a) := by
  rw [← CoefMap.pullCohomologyOne_comp, ← CoefMap.pullCohomologyOne_comp]
  exact CoefMap.pullCohomologyOne_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ by erw [mp_id]) a

theorem tri_res_resO (a : HO1 s'') :
    (cechTripleRestrictFirst ψ φ s'').pull1 ((pairRes ψ s'').pull1 a) =
      (cechTripleRestrictComposite ψ φ s'').pull1 ((pairRes (ψ ≫ φ) s'').pull1 a) := by
  rw [← CoefMap.pullCohomologyOne_comp, ← CoefMap.pullCohomologyOne_comp]
  exact CoefMap.pullCohomologyOne_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ mp_id (OAff s'') _ b) a

theorem isPullO_comp (h : φ ≫ s = s' ≫ spMap σ) (h' : ψ ≫ s' = s'' ≫ spMap τ)
    (h'' : (ψ ≫ φ) ≫ s = s'' ≫ spMap (τ.comp σ)) {a : HO1 s} {a' : HO1 s'} {a'' : HO1 s''}
    (p : IsPullO h a a') (p' : IsPullO h' a' a'') : IsPullO h'' a a'' := by
  refine cechTripleRestrictComposite_injective_cohomology_forms s'' ?_
  have p0 : (pairPull h).pull1 a = (pairRes φ s').pull1 a' := p
  have p1 : (pairPull h').pull1 a' = (pairRes ψ s'').pull1 a'' := p'
  rw [tri_pull_pullO h h' h'', p0, tri_res_pullO, p1, tri_res_resO]

theorem glob_restrict {C C' : Type} [Category.{0} C] [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R)
    (G : C' ⥤ C) (ω : Glob1 F) (T : C') :
    (pullGlob1 (CoefMap.restrict F G) ω).1 T = ω.1 (G.obj T) := cechDeRhamCoefMapOneForms_restrictAlongFunctor F G T _

theorem triRes_apply (s'' : X'' ⟶ Sp R'') (c : Glob1 (OPair (ψ ≫ φ) s'')) (t : (Triple ψ φ)ᵒᵖ) :
    (pullGlob1 (cechTripleRestrictComposite ψ φ s'') c).1 t = c.1 ((cechTripleProjFirstThird ψ φ).obj t) :=
  glob_restrict (OPair (ψ ≫ φ) s'') (cechTripleProjFirstThird ψ φ) c t

theorem triple_restriction_forms_injective (s'' : X'' ⟶ Sp R'') :
    Function.Injective (pullGlob1 (cechTripleRestrictComposite ψ φ s'')) := by
  have key : ∀ c : GlobForm s'', pullGlob1 (cechTripleRestrictComposite ψ φ s'') (pullGlob1 (pairRes (ψ ≫ φ) s'') c) =
      pullGlob1 (CoefMap.restrict (OAff s'') (cechTripleProjFirstThird ψ φ ⋙ pairFst (ψ ≫ φ))) c := fun c ↦
    Subtype.ext (funext fun t ↦ (triRes_apply s'' _ t).trans
      ((glob_restrict (OAff s'') (pairFst (ψ ≫ φ)) c _).trans
        (glob_restrict (OAff s'') (cechTripleProjFirstThird ψ φ ⋙ pairFst (ψ ≫ φ)) c t).symm))
  intro x y e
  obtain ⟨x0, rfl⟩ := (pairRes_bijective (ψ ≫ φ) s'').2.1.2 x
  obtain ⟨y0, rfl⟩ := (pairRes_bijective (ψ ≫ φ) s'').2.1.2 y
  rw [key, key] at e
  rw [(bas_triple ψ φ s'').glob.1 e]

theorem isPullForm_comp (h : φ ≫ s = s' ≫ spMap σ) (h' : ψ ≫ s' = s'' ≫ spMap τ)
    (h'' : (ψ ≫ φ) ≫ s = s'' ≫ spMap (τ.comp σ)) {a : GlobForm s} {a' : GlobForm s'}
    {a'' : GlobForm s''} (p : IsPullForm h a a') (p' : IsPullForm h' a' a'') :
    IsPullForm h'' a a'' := by
  refine triple_restriction_forms_injective s'' (Subtype.ext (funext fun t ↦ ?_))
  have k := isPullForm_iff.1 p t.unop.p23
  have k' := isPullForm_iff.1 p' t.unop.p12
  have e : (semiHom_secPull h' t.unop.p12).m1 ((semiHom_secPull h t.unop.p23).m1 (a.1 (op t.unop.1.2.2))) =
      (semiHom_secPull h'' t.unop.p13).m1 (a.1 (op t.unop.1.2.2)) :=
    SemiHom.oneFormMap_comp_oneFormMap _ _ _ (fun b ↦ congrArg (fun q ↦ q.hom b)
      (Scheme.Hom.appLE_comp_appLE ψ φ t.unop.1.2.2.1 t.unop.1.2.1.1 t.unop.1.1.1 t.unop.2.2 t.unop.2.1)) _
  have L : (pullGlob1 (pairPull h'') a).1 ((cechTripleProjFirstThird ψ φ).obj t) =
      (semiHom_secPull h'' t.unop.p13).m1 (a.1 (op t.unop.1.2.2)) := rfl
  have Rr : (pullGlob1 (pairRes (ψ ≫ φ) s'') a'').1 ((cechTripleProjFirstThird ψ φ).obj t) = a''.1 (op t.unop.1.1) :=
    glob_restrict (OAff s'') (pairFst (ψ ≫ φ)) a'' _
  have k1 : (semiHom_secPull h t.unop.p23).m1 (a.1 (op t.unop.1.2.2)) = a'.1 (op t.unop.1.2.1) := k
  have k2 : (semiHom_secPull h' t.unop.p12).m1 (a'.1 (op t.unop.1.2.1)) = a''.1 (op t.unop.1.1) := k'
  exact (triRes_apply s'' _ t).trans (L.trans (e.symm.trans ((congrArg _ k1).trans
    (k2.trans (Rr.symm.trans (triRes_apply s'' _ t).symm)))))

theorem isPull1_comp (h : φ ≫ s = s' ≫ spMap σ) (h' : ψ ≫ s' = s'' ≫ spMap τ)
    (h'' : (ψ ≫ φ) ≫ s = s'' ≫ spMap (τ.comp σ)) {a : HH1 s} {a' : HH1 s'} {a'' : HH1 s''}
    (p : IsPull1 h a a') (p' : IsPull1 h' a' a'') : IsPull1 h'' a a'' := by
  refine cechTripleRestrictComposite_injective_first ψ φ s'' ?_
  have p0 : pullHyp1 (pairPull h) a = pullHyp1 (pairRes φ s') a' := p
  have p1 : pullHyp1 (pairPull h') a' = pullHyp1 (pairRes ψ s'') a'' := p'
  rw [tri_pull_pull1 h h' h'', p0, tri_res_pull1, p1, cechTriple_restrict_restrict_first]

theorem isPullO_id (h : 𝟙 X ≫ s = s ≫ spMap (RingHom.id R)) (c : HO1 s) : IsPullO h c c :=
  CoefMap.pullCohomologyOne_eq_of_natTrans (pairPull h) (pairRes _ s) (pairIdTrans X) (fun _ _ ↦ rfl) c

theorem isPullForm_id (h : 𝟙 X ≫ s = s ≫ spMap (RingHom.id R)) (c : GlobForm s) :
    IsPullForm h c c := by
  refine isPullForm_iff.2 fun p ↦ ?_
  have e : (p.1.1 : X.affineOpens) ≤ p.1.2 := p.2
  exact (c.2 (homOfLE e).op).symm

end Comp

section Base

variable {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) [IsIso s]

omit [IsIso s] in
theorem base_affine (s : X ⟶ Sp R) [IsIso s] : IsAffine X := IsAffine.of_isIso s

def topAff : AffOp X :=
  haveI := base_affine s
  op ⟨⊤, isAffineOpen_top X⟩

def topInitial : Limits.IsInitial (topAff s) :=
  Limits.IsInitial.ofUniqueHom (fun U ↦ (homOfLE (show U.unop ≤ (topAff s).unop from
    le_top (a := U.unop.1))).op) fun _ _ ↦ Subsingleton.elim _ _

theorem base_first_cohomology_zero (c : HO1 s) : c = 0 := H1.eq_zero_of_isInitial (OAff s) (topInitial s) c

theorem base_surj : Function.Surjective (algebraMap R ((OAff s).obj (topAff s))) := by
  have e : s.appLE ⊤ ⊤ le_top = s.appTop := by
    simp only [Scheme.Hom.appLE]
    exact (congrArg _ ((X.presheaf.map_id _))).trans (Category.comp_id _)
  haveI : IsIso s.appTop := inferInstanceAs (IsIso (Scheme.Hom.app _ ⊤))
  have h : IsIso (secMap s ⊤) := by
    have h1 : IsIso (s.appLE ⊤ ⊤ le_top) := by
      rw [e]
      infer_instance
    exact IsIso.comp_isIso' (f := (Scheme.ΓSpecIso (CommRingCat.of R)).inv) inferInstance h1
  exact (ConcreteCategory.bijective_of_isIso (secMap s ⊤)).2

theorem base_form (c : GlobForm s) : c = 0 := by
  haveI : Subsingleton Ω[(OAff s).obj (topAff s)⁄R] :=
    KaehlerDifferential.subsingleton_of_surjective R _ (base_surj s)
  refine Subtype.ext (funext fun T ↦ ?_)
  rw [c.2 ((topInitial s).to T), Subsingleton.elim (c.1 (topAff s)) 0, map_zero]
  rfl

theorem base_hyp (c : HH1 s) : c = 0 := by
  have h : c ∈ CechHodgeFiltration s := LinearMap.mem_ker.2 (base_first_cohomology_zero s _)
  rw [cechHodgeFiltration_eq_range] at h
  obtain ⟨ω, rfl⟩ := h
  have : ω = 0 := Subtype.ext (base_form s ω.1)
  rw [this, map_zero]

end Base

section Over

variable {R : Type} [CommRing R]

abbrev PO {Y Z : Over (Sp R)} (f : Y ⟶ Z) : HO1 Z.hom →ₗ[R] HO1 Y.hom := pullHO1 (wOver f)

abbrev PF {Y Z : Over (Sp R)} (f : Y ⟶ Z) : GlobForm Z.hom →ₗ[R] GlobForm Y.hom := pullForm (wOver f)

abbrev PH {Y Z : Over (Sp R)} (f : Y ⟶ Z) : HH1 Z.hom →ₗ[R] HH1 Y.hom := pullHH1 (wOver f)

variable {Y Z W : Over (Sp R)}

theorem PO_comp (f : Y ⟶ Z) (g : Z ⟶ W) (c : HO1 W.hom) : PO (f ≫ g) c = PO f (PO g c) :=
  (IsPullO.eq_pullHO1 (wOver (f ≫ g)) (isPullO_comp (wOver g) (wOver f) (wOver (f ≫ g))
    (isPullO_pullHO1 _ c) (isPullO_pullHO1 _ _))).symm

theorem PF_comp (f : Y ⟶ Z) (g : Z ⟶ W) (c : GlobForm W.hom) : PF (f ≫ g) c = PF f (PF g c) :=
  (IsPullForm.eq_pullForm (wOver (f ≫ g)) (isPullForm_comp (wOver g) (wOver f) (wOver (f ≫ g))
    (isPullForm_pullForm _ c) (isPullForm_pullForm _ _))).symm

theorem PH_comp (f : Y ⟶ Z) (g : Z ⟶ W) (c : HH1 W.hom) : PH (f ≫ g) c = PH f (PH g c) :=
  (IsPull1.eq_pullHH1 (wOver (f ≫ g)) (isPull1_comp (wOver g) (wOver f) (wOver (f ≫ g))
    (isPull1_pullHH1 _ c) (isPull1_pullHH1 _ _))).symm

theorem PO_id (c : HO1 Y.hom) : PO (𝟙 Y) c = c :=
  (IsPullO.eq_pullHO1 (wOver (𝟙 Y)) (isPullO_id _ c)).symm

theorem PF_id (c : GlobForm Y.hom) : PF (𝟙 Y) c = c :=
  (IsPullForm.eq_pullForm (wOver (𝟙 Y)) (isPullForm_id _ c)).symm

theorem PH_id (c : HH1 Y.hom) : PH (𝟙 Y) c = c :=
  (IsPull1.eq_pullHH1 (wOver (𝟙 Y)) (isPull1_id _ c)).symm

instance : IsIso (𝟙_ (Over (Sp R))).hom := inferInstanceAs (IsIso (𝟙 (Sp R)))

theorem PO_one {A : Over (Sp R)} [GrpObj A] (c : HO1 A.hom) : PO (1 : Y ⟶ A) c = 0 := by
  rw [Hom.one_def, PO_comp, base_first_cohomology_zero _ (PO η[A] c), map_zero]

theorem PF_one {A : Over (Sp R)} [GrpObj A] (c : GlobForm A.hom) : PF (1 : Y ⟶ A) c = 0 := by
  rw [Hom.one_def, PF_comp, base_form _ (PF η[A] c), map_zero]

theorem PH_one {A : Over (Sp R)} [GrpObj A] (c : HH1 A.hom) : PH (1 : Y ⟶ A) c = 0 := by
  rw [Hom.one_def, PH_comp, base_hyp _ (PH η[A] c), map_zero]

end Over

section Abstract

variable {R M N : Type} [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
  (a b : M →ₗ[R] N) (u v : N →ₗ[R] M)

theorem sum_bijective (ua : ∀ x, u (a x) = x) (ub : ∀ x, u (b x) = 0) (va : ∀ x, v (a x) = 0)
    (vb : ∀ x, v (b x) = x) (hz : ∀ c, u c = 0 → v c = 0 → c = 0) :
    Function.Bijective fun x : M × M ↦ a x.1 + b x.2 := by
  refine ⟨fun x y e ↦ ?_, fun c ↦ ⟨(u c, v c), ?_⟩⟩
  · have e' : a x.1 + b x.2 = a y.1 + b y.2 := e
    have e1 := congrArg u e'
    have e2 := congrArg v e'
    simp only [map_add, ua, ub, va, vb, add_zero, zero_add] at e1 e2
    exact Prod.ext e1 e2
  · refine sub_eq_zero.1 (hz _ ?_ ?_) <;> simp [ua, ub, va, vb]

theorem sum_primitive (m : M →ₗ[R] N) (ua : ∀ x, u (a x) = x) (ub : ∀ x, u (b x) = 0)
    (va : ∀ x, v (a x) = 0) (vb : ∀ x, v (b x) = x) (um : ∀ x, u (m x) = x) (vm : ∀ x, v (m x) = x)
    (hz : ∀ c, u c = 0 → v c = 0 → c = 0) (x : M) : m x = a x + b x := by
  refine sub_eq_zero.1 (hz _ ?_ ?_) <;> simp [ua, ub, va, vb, um, vm]

end Abstract

section Main

variable {R : Type} [CommRing R]

theorem isPullForm_zero {Y Z : Over (Sp R)} (f : Y ⟶ Z) (sY : Stein (OAff Y.hom))
    (β : ClosedForm Z.hom) (e : PH f (clForm _ β) = 0) : IsPullForm (wOver f) β.1 0 := by
  have k : IsPull1 (wOver f) (clForm _ β) 0 := by
    have := isPull1_pullHH1 (wOver f) (clForm _ β)
    rwa [show pullHH1 (wOver f) (clForm _ β) = 0 from e] at this
  have k2 : ofForm (OPair f.left Y.hom) (pullClosed1 (pairPull (wOver f)) β) = 0 := by
    rw [← pullHyp1_ofForm]
    exact k.trans (map_zero _)
  obtain ⟨g, hg, hD⟩ := ofForm_eq_zero.1 k2
  obtain ⟨r, hr⟩ := stein_const ((bas_pair f.left Y.hom).stein sY) g hg
  refine Eq.trans ?_ (map_zero _).symm
  refine Subtype.ext (funext fun T ↦ ?_)
  refine (hD T).symm.trans ?_
  rw [hr T]
  exact (D R _).map_algebraMap r

variable (A : Over (Sp R)) [GrpObj A]

abbrev ax₁ : A ⟶ A ⊗ A := lift (𝟙 A) 1

abbrev ax₂ : A ⟶ A ⊗ A := lift 1 (𝟙 A)

theorem ax₁_mul : ax₁ A ≫ (μ : A ⊗ A ⟶ A) = 𝟙 A := by
  rw [← Hom.mul_def, _root_.mul_one]

theorem ax₂_mul : ax₂ A ≫ (μ : A ⊗ A ⟶ A) = 𝟙 A := by
  rw [← Hom.mul_def, _root_.one_mul]

theorem hyp_primitive (sA : Stein (OAff A.hom))
    (aO : ∀ c : HO1 (A ⊗ A).hom, IsPullO (wOver (ax₁ A)) c 0 → IsPullO (wOver (ax₂ A)) c 0 → c = 0)
    (aF : ∀ c : GlobForm (A ⊗ A).hom, IsPullForm (wOver (ax₁ A)) c 0 →
      IsPullForm (wOver (ax₂ A)) c 0 → c = 0) (c : HH1 A.hom) :
    PH (μ : A ⊗ A ⟶ A) c = PH (fst A A) c + PH (snd A A) c := by
  set d : HH1 (A ⊗ A).hom := PH (μ : A ⊗ A ⟶ A) c - (PH (fst A A) c + PH (snd A A) c) with hd
  have d1 : PH (ax₁ A) d = 0 := by
    simp only [hd, map_sub, map_add, ← PH_comp, ax₁_mul, lift_fst, lift_snd, PH_id, PH_one]
    simp
  have d2 : PH (ax₂ A) d = 0 := by
    simp only [hd, map_sub, map_add, ← PH_comp, ax₂_mul, lift_fst, lift_snd, PH_id, PH_one]
    simp
  have toO0 : ∀ f : A ⟶ A ⊗ A, PH f d = 0 → IsPullO (wOver f) (toHO1 _ d) 0 := fun f e ↦ by
    have := IsPull1.toO (isPull1_pullHH1 (wOver f) d)
    rwa [show pullHH1 (wOver f) d = 0 from e, map_zero] at this
  have hF : d ∈ CechHodgeFiltration (A ⊗ A).hom := LinearMap.mem_ker.2 (aO _ (toO0 _ d1) (toO0 _ d2))
  rw [cechHodgeFiltration_eq_range] at hF
  obtain ⟨β, hβ⟩ := hF
  have hβ0 : β = 0 := Subtype.ext (aF β.1 (isPullForm_zero _ sA β (by rw [hβ]; exact d1))
    (isPullForm_zero _ sA β (by rw [hβ]; exact d2)))
  have : d = 0 := by rw [← hβ, hβ0, map_zero]
  exact sub_eq_zero.1 this

variable {A}

theorem bi_of_fam {Y : Over (Sp R)} {J : Type} [Finite J] (f : J → (Y ⟶ A)) (m p q : J)
    (sY : Stein (OAff Y.hom)) (pY : Par (OAff Y.hom))
    (hO : Function.Bijective fun x : HO1 A.hom × HO1 A.hom ↦ PO (f p) x.1 + PO (f q) x.2)
    (hF : Function.Bijective fun x : GlobForm A.hom × GlobForm A.hom ↦ PF (f p) x.1 + PF (f q) x.2)
    (mO : ∀ c, PO (f m) c = PO (f p) c + PO (f q) c) (mF : ∀ c, PF (f m) c = PF (f p) c + PF (f q) c)
    (mH : ∀ c, PH (f m) c = PH (f p) c + PH (f q) c) : Bi (OAff A.hom) := by
  let φ : J → (Y.left ⟶ A.left) := fun i ↦ (f i).left
  have h : ∀ i, φ i ≫ A.hom = Y.hom ≫ spMap (RingHom.id R) := fun i ↦ wOver (f i)
  have hb : Bas Y.hom (famFst φ) := bas_fam φ Y.hom
  have eO : ∀ i x, (famPull h i).pull1 x =
      (CoefMap.restrict (OAff Y.hom) (famFst φ)).pull1 (PO (f i) x) := famPull_pull1 h
  have eF : ∀ i x, pullGlob1 (famPull h i) x =
      pullGlob1 (CoefMap.restrict (OAff Y.hom) (famFst φ)) (PF (f i) x) := famPull_glob h
  have eH : ∀ i x, pullHyp1 (famPull h i) x =
      pullHyp1 (CoefMap.restrict (OAff Y.hom) (famFst φ)) (PH (f i) x) := famPull_hyp h
  refine ⟨(Fam φ)ᵒᵖ, inferInstance, famFst φ ⋙ OAff Y.hom, famPull h m, famPull h p, famPull h q,
    hb.stein sY, hb.par pY, ?_, ?_, fun c ↦ ?_, fun c ↦ ?_, fun c ↦ ?_⟩
  · convert hb.pull1.comp hO using 1
    funext x
    simp only [Function.comp_apply, map_add, eO]
  · convert hb.glob.comp hF using 1
    funext x
    simp only [Function.comp_apply, map_add, eF]
  · rw [eO, eO, eO, ← map_add, mO]
  · rw [eF, eF, eF, ← map_add, mF]
  · rw [eH, eH, eH, ← map_add, mH]

theorem bi_of_pull {Y : Over (Sp R)} (m p q : Y ⟶ A) (sY : Stein (OAff Y.hom)) (pY : Par (OAff Y.hom))
    (hO : Function.Bijective fun x : HO1 A.hom × HO1 A.hom ↦ PO p x.1 + PO q x.2)
    (hF : Function.Bijective fun x : GlobForm A.hom × GlobForm A.hom ↦ PF p x.1 + PF q x.2)
    (mO : ∀ c, PO m c = PO p c + PO q c) (mF : ∀ c, PF m c = PF p c + PF q c)
    (mH : ∀ c, PH m c = PH p c + PH q c) : Bi (OAff A.hom) :=
  bi_of_fam ![m, p, q] 0 1 2 sY pY hO hF mO mF mH

end Main

theorem biSt_of : SteinSt → ParSt → AxOSt → AxFormSt → BiSt := by
  intro hS hP hO hF R _ A _ g hA hg
  have hAA := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have hgg := GlobalTheory.AbDual.smooth_prod hg hg
  have sA : Stein (OAff A.hom) := hS R A g hA hg
  have sAA : Stein (OAff (A ⊗ A).hom) := hS R (A ⊗ A) (g + g) hAA hgg
  have pAA : Par (OAff (A ⊗ A).hom) := (hP R (A ⊗ A) (g + g) hAA hgg).1
  have aO := hO R A g hA hg
  have aF := hF R A g hA hg
  have zO : ∀ c : HO1 (A ⊗ A).hom, PO (ax₁ A) c = 0 → PO (ax₂ A) c = 0 → c = 0 := fun c e₁ e₂ ↦ by
    have k₁ := isPullO_pullHO1 (wOver (ax₁ A)) c
    have k₂ := isPullO_pullHO1 (wOver (ax₂ A)) c
    rw [show pullHO1 (wOver (ax₁ A)) c = 0 from e₁] at k₁
    rw [show pullHO1 (wOver (ax₂ A)) c = 0 from e₂] at k₂
    exact aO c k₁ k₂
  have zF : ∀ c : GlobForm (A ⊗ A).hom, PF (ax₁ A) c = 0 → PF (ax₂ A) c = 0 → c = 0 := fun c e₁ e₂ ↦ by
    have k₁ := isPullForm_pullForm (wOver (ax₁ A)) c
    have k₂ := isPullForm_pullForm (wOver (ax₂ A)) c
    rw [show pullForm (wOver (ax₁ A)) c = 0 from e₁] at k₁
    rw [show pullForm (wOver (ax₂ A)) c = 0 from e₂] at k₂
    exact aF c k₁ k₂
  have o1 : ∀ x, PO (ax₁ A) (PO (fst A A) x) = x := fun x ↦ by rw [← PO_comp, lift_fst, PO_id]
  have o2 : ∀ x, PO (ax₁ A) (PO (snd A A) x) = 0 := fun x ↦ by rw [← PO_comp, lift_snd, PO_one]
  have o3 : ∀ x, PO (ax₂ A) (PO (fst A A) x) = 0 := fun x ↦ by rw [← PO_comp, lift_fst, PO_one]
  have o4 : ∀ x, PO (ax₂ A) (PO (snd A A) x) = x := fun x ↦ by rw [← PO_comp, lift_snd, PO_id]
  have o5 : ∀ x, PO (ax₁ A) (PO (μ : A ⊗ A ⟶ A) x) = x := fun x ↦ by
    rw [← PO_comp, ax₁_mul, PO_id]
  have o6 : ∀ x, PO (ax₂ A) (PO (μ : A ⊗ A ⟶ A) x) = x := fun x ↦ by
    rw [← PO_comp, ax₂_mul, PO_id]
  have f1 : ∀ x, PF (ax₁ A) (PF (fst A A) x) = x := fun x ↦ by rw [← PF_comp, lift_fst, PF_id]
  have f2 : ∀ x, PF (ax₁ A) (PF (snd A A) x) = 0 := fun x ↦ by rw [← PF_comp, lift_snd, PF_one]
  have f3 : ∀ x, PF (ax₂ A) (PF (fst A A) x) = 0 := fun x ↦ by rw [← PF_comp, lift_fst, PF_one]
  have f4 : ∀ x, PF (ax₂ A) (PF (snd A A) x) = x := fun x ↦ by rw [← PF_comp, lift_snd, PF_id]
  have f5 : ∀ x, PF (ax₁ A) (PF (μ : A ⊗ A ⟶ A) x) = x := fun x ↦ by
    rw [← PF_comp, ax₁_mul, PF_id]
  have f6 : ∀ x, PF (ax₂ A) (PF (μ : A ⊗ A ⟶ A) x) = x := fun x ↦ by
    rw [← PF_comp, ax₂_mul, PF_id]
  exact bi_of_pull (μ : A ⊗ A ⟶ A) (fst A A) (snd A A) sAA pAA
    (sum_bijective _ _ (PO (ax₁ A)) (PO (ax₂ A)) o1 o2 o3 o4 zO)
    (sum_bijective _ _ (PF (ax₁ A)) (PF (ax₂ A)) f1 f2 f3 f4 zF)
    (sum_primitive _ _ (PO (ax₁ A)) (PO (ax₂ A)) _ o1 o2 o3 o4 o5 o6 zO)
    (sum_primitive _ _ (PF (ax₁ A)) (PF (ax₂ A)) _ f1 f2 f3 f4 f5 f6 zF)
    (hyp_primitive A sA aO aF)

theorem bilinear_statement_with_descent_hypotheses : DescentSt → LowSt → SteinSt → ParSt → AxOSt → AxFormSt → BiSt :=
  fun _ _ ↦ biSt_of

end GlobalTheory.CompanionTheory.GroupLaw
