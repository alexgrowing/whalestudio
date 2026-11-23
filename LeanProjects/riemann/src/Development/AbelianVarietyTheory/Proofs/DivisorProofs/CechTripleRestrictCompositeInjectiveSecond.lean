import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairResBijectiveTwo

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry KaehlerDifferential Opposite GlobalTheory.CatCoh
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
namespace GlobalTheory.CechDR
open FormExt FormExtJ
attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler

theorem restrict_bijective_one_of_basis {R' : Type} [CommRing R'] {X' : Scheme.{0}} (s' : X' ⟶ Sp R')
    {C' : Type} [Category.{0} C'] [Quiver.IsThin C'] (G : C' ⥤ AffOp X')
    (hcov : ∀ T : AffOp X', ∃ (n : ℕ) (b : Fin n → (OAff s').obj T),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X') (u : T ⟶ S),
        IsUnit (mp (OAff s') u (b i)) →
          ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u)
    (hdir : ∀ (t₁ t₂ : C') (S : AffOp X'), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) →
      ∃ (n : ℕ) (b : Fin n → (OAff s').obj S), Ideal.span (Set.range b) = ⊤ ∧
        ∀ (i : Fin n) (S' : AffOp X') (u : S ⟶ S'), IsUnit (mp (OAff s') u (b i)) →
          ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) :
    Function.Bijective (pullHyp1 (CoefMap.restrict (OAff s') G)) := by
  have H := _root_.GlobalTheory.CechDR.hasLoc_OAff s'
  have hs := _root_.GlobalTheory.sep_of_factoring_cover (OAff s') G H hcov
  have hg := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s') G H hcov hdir
  have hv := _root_.GlobalTheory.CatCoh.Desc.Basis.oneCocycle_vanishing_comma_of_basis (OAff s') G H hcov hdir
  have hs1 := _root_.GlobalTheory.CechDR.form_eq_zero_of_basis_cover s' G hcov
  have hg1 := _root_.GlobalTheory.CechDR.FormExt.glue_one_forms s' G hcov hdir
  have hs2 := _root_.GlobalTheory.CechDR.twoForm_sep_of_basis s' G hcov
  have b1 : Function.Bijective (CoefMap.restrict (OAff s') G).pull1 :=
    ⟨_root_.GlobalTheory.CatCoh.CoefMap.restrict_pull1_injective_of_sep_glue _ _ hs hg,
      _root_.GlobalTheory.CatCoh.pull1_restrict_surjective_of_comma _ _ hs hg hv⟩
  have bg := _root_.GlobalTheory.restrict_glob1_bijective _ _ hs1 hg1
  exact ⟨_root_.GlobalTheory.CechDR.pullHyp1_restrict_injective _ _ b1.1 (_root_.GlobalTheory.compat_family_extend _ _ hs hg) bg.1,
    _root_.GlobalTheory.CechDR.pullHyp1_restrict_surjective _ _ b1.2 (_root_.GlobalTheory.cocycle_one_forms_coboundary_of_restrict _ _ hs1 hg1) bg.2 hs2⟩

theorem restrict_bijective_two_of_basis {R' : Type} [CommRing R'] {X' : Scheme.{0}} (s' : X' ⟶ Sp R')
    {C' : Type} [Category.{0} C'] [Quiver.IsThin C'] (G : C' ⥤ AffOp X')
    (hcov : ∀ T : AffOp X', ∃ (n : ℕ) (b : Fin n → (OAff s').obj T),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X') (u : T ⟶ S),
        IsUnit (mp (OAff s') u (b i)) →
          ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u)
    (hdir : ∀ (t₁ t₂ : C') (S : AffOp X'), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) →
      ∃ (n : ℕ) (b : Fin n → (OAff s').obj S), Ideal.span (Set.range b) = ⊤ ∧
        ∀ (i : Fin n) (S' : AffOp X') (u : S ⟶ S'), IsUnit (mp (OAff s') u (b i)) →
          ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) :
    Function.Bijective (pullHyp2 (CoefMap.restrict (OAff s') G)) := by
  have H := _root_.GlobalTheory.CechDR.hasLoc_OAff s'
  have hs := _root_.GlobalTheory.sep_of_factoring_cover (OAff s') G H hcov
  have hg := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s') G H hcov hdir
  have hv := _root_.GlobalTheory.CatCoh.Desc.Basis.oneCocycle_vanishing_comma_of_basis (OAff s') G H hcov hdir
  have hv2 := GlobalTheory.T.twoCocycle_coboundary_of_basisFunctor (OAff s') G H hcov hdir
  have hs1 := _root_.GlobalTheory.CechDR.form_eq_zero_of_basis_cover s' G hcov
  have hg1 := _root_.GlobalTheory.CechDR.FormExt.glue_one_forms s' G hcov hdir
  have hs2 := _root_.GlobalTheory.CechDR.twoForm_sep_of_basis s' G hcov
  have b1 : Function.Bijective (CoefMap.restrict (OAff s') G).pull1 :=
    ⟨_root_.GlobalTheory.CatCoh.CoefMap.restrict_pull1_injective_of_sep_glue _ _ hs hg,
      _root_.GlobalTheory.CatCoh.pull1_restrict_surjective_of_comma _ _ hs hg hv⟩
  have bg := _root_.GlobalTheory.restrict_glob1_bijective _ _ hs1 hg1
  have unitE : ∀ {S S' : AffOp X'} (u : S ⟶ S') (b : (OAff s').obj S),
      IsUnit (mp (omExt (OAff s')) u (TrivSqZeroExt.inl b)) → IsUnit (mp (OAff s') u b) :=
    fun u b h ↦ ((isUnit_mp_omExt_iff (OAff s') u _).1 h)
  have HE := hasLoc_omExt (OAff s') H
  have hcovE : ∀ T : AffOp X', ∃ (n : ℕ) (b : Fin n → (omExt (OAff s')).obj T),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X') (u : T ⟶ S),
        IsUnit (mp (omExt (OAff s')) u (b i)) →
          ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u :=
    fun T ↦ by
      obtain ⟨n, b, hb, h⟩ := hcov T
      exact ⟨n, fun i ↦ TrivSqZeroExt.inl (b i), span_inl_eq_top (OAff s') hb,
        fun i S u hu ↦ h i S u (unitE u _ hu)⟩
  have hdirE : ∀ (t₁ t₂ : C') (S : AffOp X'), (G.obj t₁ ⟶ S) →
      (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → (omExt (OAff s')).obj S),
        Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : AffOp X') (u : S ⟶ S'),
          IsUnit (mp (omExt (OAff s')) u (b i)) →
            ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S') :=
    fun t₁ t₂ S a₁ a₂ ↦ by
      obtain ⟨n, b, hb, h⟩ := hdir t₁ t₂ S a₁ a₂
      exact ⟨n, fun i ↦ TrivSqZeroExt.inl (b i), span_inl_eq_top (OAff s') hb,
        fun i S' u hu ↦ h i S' u (unitE u _ hu)⟩
  have hsE := _root_.GlobalTheory.sep_of_factoring_cover (omExt (OAff s')) G HE hcovE
  have hgE := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (omExt (OAff s')) G HE hcovE hdirE
  have hvE := _root_.GlobalTheory.CatCoh.Desc.Basis.oneCocycle_vanishing_comma_of_basis (omExt (OAff s')) G HE hcovE hdirE
  have hcovJ : ∀ j : ℕ, ∀ T : AffOp X', ∃ (n : ℕ) (b : Fin n → (omjExt (OAff s') j).obj T),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X') (u : T ⟶ S),
        IsUnit (mp (omjExt (OAff s') j) u (b i)) →
          ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u :=
    fun j T ↦ by
      obtain ⟨n, b, hb, h⟩ := hcov T
      exact ⟨n, fun i ↦ TrivSqZeroExt.inl (b i), span_inlJ_eq_top (OAff s') j hb,
        fun i S u hu ↦ h i S u ((isUnit_mp_omjExt_iff (OAff s') j u _).1 hu)⟩
  have hdirJ : ∀ j : ℕ, ∀ (t₁ t₂ : C') (S : AffOp X'), (G.obj t₁ ⟶ S) →
      (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → (omjExt (OAff s') j).obj S),
        Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : AffOp X') (u : S ⟶ S'),
          IsUnit (mp (omjExt (OAff s') j) u (b i)) →
            ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S') :=
    fun j t₁ t₂ S a₁ a₂ ↦ by
      obtain ⟨n, b, hb, h⟩ := hdir t₁ t₂ S a₁ a₂
      exact ⟨n, fun i ↦ TrivSqZeroExt.inl (b i), span_inlJ_eq_top (OAff s') j hb,
        fun i S' u hu ↦ h i S' u ((isUnit_mp_omjExt_iff (OAff s') j u _).1 hu)⟩
  have hsJ := fun j ↦ _root_.GlobalTheory.sep_of_factoring_cover (omjExt (OAff s') j) G
    (GlobalTheory.T.hasLocalisationAtElements_trivSqZeroExtForms (OAff s') j H) (hcovJ j)
  have hgJ := fun j ↦ _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (omjExt (OAff s') j) G
    (GlobalTheory.T.hasLocalisationAtElements_trivSqZeroExtForms (OAff s') j H) (hcovJ j) (hdirJ j)
  have hs3 : ∀ (T : AffOp X') (x : Om R' ((OAff s').obj T) 3),
      (∀ t (u : T ⟶ G.obj t), pOm (OAff s') 3 u x = 0) → x = 0 := by
    intro T x hx
    have h0 : (TrivSqZeroExt.inr x : (omjExt (OAff s') 3).obj T) = 0 :=
      hsJ 3 T _ fun t u ↦ (mp_omjExt_inr (OAff s') 3 u x).trans (by rw [hx t u]; exact TrivSqZeroExt.inr_zero _)
    simpa using congrArg TrivSqZeroExt.snd h0
  exact ⟨GlobalTheory.T.comma_first_order_cocycle_lift _ _ (GlobalTheory.T.comma_descent_injective _ _ hs hg hv) b1.2
      (_root_.GlobalTheory.cocycle_one_forms_coboundary_of_restrict _ _ hs1 hg1) bg.2 hs2,
    GlobalTheory.T.comma_second_order_cocycle_lift _ _ (GlobalTheory.T.comma_descent_restriction_equiv _ _ hs hg hv hv2)
      (GlobalTheory.T.oneForms_twoCocycle_coboundary_of_restrict _ _ (GlobalTheory.T.comma_descent_injective _ _ hsE hgE hvE))
      (GlobalTheory.T.exists_oneForms_cocycle_restrict_sub_coboundary _ _ (_root_.GlobalTheory.CatCoh.pull1_restrict_surjective_of_comma _ _ hsE hgE hvE))
      (GlobalTheory.T.higherForms_oneCocycle_coboundary_of_restrict _ _ 2 (_root_.GlobalTheory.CatCoh.CoefMap.restrict_pull1_injective_of_sep_glue _ _ (hsJ 2) (hgJ 2)))
      (GlobalTheory.T.compatible_higherForms_extend_along_functor _ _ 2 (hsJ 2) (hgJ 2)) hs3⟩

section Triple

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {X X' X'' : Scheme.{0}}

abbrev Triple (ψ : X'' ⟶ X') (φ : X' ⟶ X) : Type :=
  {q : X''.affineOpens × X'.affineOpens × X.affineOpens //
    q.1.1 ≤ ψ ⁻¹ᵁ q.2.1.1 ∧ q.2.1.1 ≤ φ ⁻¹ᵁ q.2.2.1}

variable {ψ : X'' ⟶ X'} {φ : X' ⟶ X}

theorem Triple.le_one {p q : Triple ψ φ} (h : p ≤ q) : p.1.1 ≤ q.1.1 :=
  (Prod.le_def.1 (Subtype.coe_le_coe.2 h)).1

theorem Triple.le_two {p q : Triple ψ φ} (h : p ≤ q) : p.1.2.1 ≤ q.1.2.1 :=
  (Prod.le_def.1 (Prod.le_def.1 (Subtype.coe_le_coe.2 h)).2).1

theorem Triple.le_three {p q : Triple ψ φ} (h : p ≤ q) : p.1.2.2 ≤ q.1.2.2 :=
  (Prod.le_def.1 (Prod.le_def.1 (Subtype.coe_le_coe.2 h)).2).2

def Triple.p12 (q : Triple ψ φ) : Pair ψ := ⟨(q.1.1, q.1.2.1), q.2.1⟩

def Triple.p23 (q : Triple ψ φ) : Pair φ := ⟨(q.1.2.1, q.1.2.2), q.2.2⟩

def Triple.p13 (q : Triple ψ φ) : Pair (ψ ≫ φ) :=
  ⟨(q.1.1, q.1.2.2), fun _ hx ↦ q.2.2 (q.2.1 hx)⟩

theorem Triple.pairFirstThirdComp_monotone : Monotone (Triple.p13 (ψ := ψ) (φ := φ)) := fun _ _ h ↦
  Subtype.coe_le_coe.1 (Prod.le_def.2 ⟨Triple.le_one h, Triple.le_three h⟩)

variable (ψ φ)

def cechTripleProjFirstSecond : (Triple ψ φ)ᵒᵖ ⥤ (Pair ψ)ᵒᵖ :=
  (Monotone.functor (f := Triple.p12) fun _ _ h ↦
    Subtype.coe_le_coe.1 (Prod.le_def.2 ⟨Triple.le_one h, Triple.le_two h⟩)).op

def cechTripleProjSecondThird : (Triple ψ φ)ᵒᵖ ⥤ (Pair φ)ᵒᵖ :=
  (Monotone.functor (f := Triple.p23) fun _ _ h ↦
    Subtype.coe_le_coe.1 (Prod.le_def.2 ⟨Triple.le_two h, Triple.le_three h⟩)).op

def cechTripleProjFirstThird : (Triple ψ φ)ᵒᵖ ⥤ (Pair (ψ ≫ φ))ᵒᵖ :=
  (Monotone.functor (Triple.pairFirstThirdComp_monotone (ψ := ψ) (φ := φ))).op

abbrev OTriple (s'' : X'' ⟶ Sp R'') : (Triple ψ φ)ᵒᵖ ⥤ CommAlgCat.{0} R'' :=
  cechTripleProjFirstThird ψ φ ⋙ OPair (ψ ≫ φ) s''

def cechTripleRestrictComposite (s'' : X'' ⟶ Sp R'') : CoefMap (RingHom.id R'') (OPair (ψ ≫ φ) s'') (OTriple ψ φ s'') :=
  CoefMap.restrict _ _

def cechTripleRestrictFirst (s'' : X'' ⟶ Sp R'') : CoefMap (RingHom.id R'') (OPair ψ s'') (OTriple ψ φ s'') where
  G := cechTripleProjFirstSecond ψ φ
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

variable {ψ φ}

def cechTriplePullbackSecond {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {τ : R' →+* R''}
    (h' : ψ ≫ s' = s'' ≫ spMap τ) : CoefMap τ (OPair φ s') (OTriple ψ φ s'') where
  G := cechTripleProjSecondThird ψ φ
  α t := (pairPull h').α ((cechTripleProjFirstSecond ψ φ).obj t)
  naturality a b := (pairPull h').naturality ((cechTripleProjFirstSecond ψ φ).map a) b
  smul t := (pairPull h').smul ((cechTripleProjFirstSecond ψ φ).obj t)

variable (ψ φ)

theorem triple_cover_affine (s'' : X'' ⟶ Sp R'') : ∀ T : AffOp X'', ∃ (n : ℕ) (b : Fin n → (OAff s'').obj T),
    Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X'') (u : T ⟶ S),
      IsUnit (mp (OAff s'') u (b i)) →
        ∃ (t : (Triple ψ φ)ᵒᵖ) (v : T ⟶ (cechTripleProjFirstThird ψ φ ⋙ pairFst (ψ ≫ φ)).obj t)
          (w : (cechTripleProjFirstThird ψ φ ⋙ pairFst (ψ ≫ φ)).obj t ⟶ S), v ≫ w = u := by
  intro T
  have hT : IsAffineOpen T.unop.1 := T.unop.2
  let G : Set Γ(X'', T.unop.1) :=
    {f | ∃ (V' : X'.affineOpens) (V : X.affineOpens), V'.1 ≤ φ ⁻¹ᵁ V.1 ∧
      X''.basicOpen f ≤ ψ ⁻¹ᵁ V'.1}
  have hG : Ideal.span G = ⊤ := by
    rw [← hT.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := φ.base (ψ.base x))
      (U := (⊤ : X.Opens)) trivial
    obtain ⟨V', hV', hxV', hV'V⟩ := exists_isAffineOpen_mem_and_subset (x := ψ.base x)
      (U := φ ⁻¹ᵁ V) hxV
    obtain ⟨f, hf, hxf⟩ := hT.exists_basicOpen_le (V := ψ ⁻¹ᵁ V') ⟨x, hxV'⟩ hx
    exact TopologicalSpace.Opens.mem_iSup.2
      ⟨⟨f, ⟨⟨V', hV'⟩, ⟨V, hV⟩, fun y hy ↦ hV'V hy, hf⟩⟩, hxf⟩
  obtain ⟨F, hFG, hF⟩ := (Ideal.span_eq_top_iff_finite G).1 hG
  refine ⟨F.card, fun i ↦ (F.equivFin.symm i).1, ?_, ?_⟩
  · have hR : Set.range (fun i : Fin F.card ↦ (F.equivFin.symm i).1) = (F : Set Γ(X'', T.unop.1)) := by
      ext f
      constructor
      · rintro ⟨i, rfl⟩; exact (F.equivFin.symm i).2
      · intro hf; exact ⟨F.equivFin ⟨f, hf⟩, by simp⟩
    exact hR ▸ hF
  · intro i S u hu
    obtain ⟨V', V, hV'V, hV⟩ := hFG (F.equivFin.symm i).2
    set f : Γ(X'', T.unop.1) := (F.equivFin.symm i).1
    have hW : IsAffineOpen (X''.basicOpen f) := hT.basicOpen f
    have hWT : X''.basicOpen f ≤ T.unop.1 := X''.basicOpen_le f
    let t : Triple ψ φ := ⟨(⟨_, hW⟩, V', V), hV, hV'V⟩
    have hSW : S.unop.1 ≤ X''.basicOpen f := by
      have h1 : X''.basicOpen (X''.presheaf.map (homOfLE (leOfHom u.unop)).op f) = S.unop.1 :=
        X''.basicOpen_of_isUnit hu
      rw [Scheme.basicOpen_res] at h1
      rw [← h1]; exact inf_le_right
    refine ⟨Opposite.op t, (homOfLE (show (⟨_, hW⟩ : X''.affineOpens) ≤ T.unop from hWT)).op,
      (homOfLE (show S.unop ≤ (⟨_, hW⟩ : X''.affineOpens) from hSW)).op, ?_⟩
    exact Quiver.Hom.unop_inj (Subsingleton.elim _ _)

theorem exists_triple_below_two (s'' : X'' ⟶ Sp R'') : ∀ (t₁ t₂ : (Triple ψ φ)ᵒᵖ) (S : AffOp X''),
    ((cechTripleProjFirstThird ψ φ ⋙ pairFst (ψ ≫ φ)).obj t₁ ⟶ S) → ((cechTripleProjFirstThird ψ φ ⋙ pairFst (ψ ≫ φ)).obj t₂ ⟶ S) →
      ∃ (n : ℕ) (b : Fin n → (OAff s'').obj S), Ideal.span (Set.range b) = ⊤ ∧
        ∀ (i : Fin n) (S' : AffOp X'') (u : S ⟶ S'), IsUnit (mp (OAff s'') u (b i)) →
          ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧
            Nonempty ((cechTripleProjFirstThird ψ φ ⋙ pairFst (ψ ≫ φ)).obj t₃ ⟶ S') := by
  intro t₁ t₂ S h₁ h₂
  have hS₁ : S.unop.1 ≤ t₁.unop.1.1.1 := leOfHom h₁.unop
  have hS₂ : S.unop.1 ≤ t₂.unop.1.1.1 := leOfHom h₂.unop
  let B : Set Γ(X'', S.unop.1) := {g | ∃ (W' : X'.affineOpens) (W : X.affineOpens),
    W.1 ≤ t₁.unop.1.2.2.1 ∧ W.1 ≤ t₂.unop.1.2.2.1 ∧ W'.1 ≤ t₁.unop.1.2.1.1 ∧
      W'.1 ≤ t₂.unop.1.2.1.1 ∧ W'.1 ≤ φ ⁻¹ᵁ W.1 ∧ X''.basicOpen g ≤ ψ ⁻¹ᵁ W'.1}
  have hB : Ideal.span B = ⊤ := by
    refine (S.unop.2.self_le_iSup_basicOpen_iff).1 fun x hx ↦ ?_
    have hy₁ : ψ.base x ∈ t₁.unop.1.2.1.1 := t₁.unop.2.1 (hS₁ hx)
    have hy₂ : ψ.base x ∈ t₂.unop.1.2.1.1 := t₂.unop.2.1 (hS₂ hx)
    have hz₁ : φ.base (ψ.base x) ∈ t₁.unop.1.2.2.1 := t₁.unop.2.2 hy₁
    have hz₂ : φ.base (ψ.base x) ∈ t₂.unop.1.2.2.1 := t₂.unop.2.2 hy₂
    obtain ⟨W, hW, hzW, hWV⟩ := exists_isAffineOpen_mem_and_subset (x := φ.base (ψ.base x))
      (U := t₁.unop.1.2.2.1 ⊓ t₂.unop.1.2.2.1) ⟨hz₁, hz₂⟩
    obtain ⟨W', hW', hyW', hW'V⟩ := exists_isAffineOpen_mem_and_subset (x := ψ.base x)
      (U := t₁.unop.1.2.1.1 ⊓ t₂.unop.1.2.1.1 ⊓ φ ⁻¹ᵁ W) ⟨⟨hy₁, hy₂⟩, hzW⟩
    obtain ⟨f, hf, hxf⟩ := S.unop.2.exists_basicOpen_le (V := S.unop.1 ⊓ ψ ⁻¹ᵁ W')
      ⟨x, hx, hyW'⟩ hx
    have hfB : f ∈ B := ⟨⟨W', hW'⟩, ⟨W, hW⟩, fun y hy ↦ (hWV hy).1, fun y hy ↦ (hWV hy).2,
      fun y hy ↦ (hW'V hy).1.1, fun y hy ↦ (hW'V hy).1.2, fun y hy ↦ (hW'V hy).2,
      hf.trans inf_le_right⟩
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, hfB⟩, hxf⟩
  obtain ⟨s0, hs0, hspan⟩ := (Ideal.span_eq_top_iff_finite B).1 hB
  refine ⟨s0.card, fun i ↦ (s0.equivFin.symm i).1, ?_, fun i S' u hu ↦ ?_⟩
  · have hsp : Ideal.span (Set.range fun i ↦ ((s0.equivFin.symm i).1 : Γ(X'', S.unop.1))) = ⊤ := by
      rw [eq_top_iff, ← hspan]
      exact Ideal.span_mono fun x hx ↦ ⟨s0.equivFin ⟨x, hx⟩, by simp⟩
    exact hsp
  · have hbB : (s0.equivFin.symm i).1 ∈ B := hs0 (s0.equivFin.symm i).2
    obtain ⟨W', W, hW₁, hW₂, hW'₁, hW'₂, hW'W, hg⟩ := hbB
    set g : Γ(X'', S.unop.1) := (s0.equivFin.symm i).1
    change IsUnit (X''.presheaf.map (homOfLE (show S'.unop.1 ≤ S.unop.1 from leOfHom u.unop)).op g) at hu
    have hS' : S'.unop.1 ≤ X''.basicOpen g := by
      have := Scheme.basicOpen_of_isUnit X'' hu
      rw [Scheme.basicOpen_res] at this
      rw [← this]; exact inf_le_right
    let t₃ : Triple ψ φ := ⟨(⟨X''.basicOpen g, S.unop.2.basicOpen g⟩, W', W), hg, hW'W⟩
    refine ⟨Opposite.op t₃, ⟨(homOfLE ?_).op⟩, ⟨(homOfLE ?_).op⟩, ⟨(homOfLE ?_).op⟩⟩
    · exact ⟨(X''.basicOpen_le g).trans hS₁, hW'₁, hW₁⟩
    · exact ⟨(X''.basicOpen_le g).trans hS₂, hW'₂, hW₂⟩
    · exact hS'

theorem cechTripleRestrictComposite_pairRes_first (s'' : X'' ⟶ Sp R'') (c : HH1 s'') :
    pullHyp1 (cechTripleRestrictComposite ψ φ s'') (pullHyp1 (pairRes (ψ ≫ φ) s'') c) =
      pullHyp1 (CoefMap.restrict (OAff s'') (cechTripleProjFirstThird ψ φ ⋙ pairFst (ψ ≫ φ))) c := by
  rw [← pullHyp1_comp]
  exact pullHyp1_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ mp_id (OAff s'') _ b) c

theorem cechTripleRestrictComposite_pairRes_second (s'' : X'' ⟶ Sp R'') (c : HH2 s'') :
    pullHyp2 (cechTripleRestrictComposite ψ φ s'') (pullHyp2 (pairRes (ψ ≫ φ) s'') c) =
      pullHyp2 (CoefMap.restrict (OAff s'') (cechTripleProjFirstThird ψ φ ⋙ pairFst (ψ ≫ φ))) c := by
  rw [← pullHyp2_comp]
  exact pullHyp2_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ mp_id (OAff s'') _ b) c

theorem cechTripleRestrictComposite_injective_first (s'' : X'' ⟶ Sp R'') : Function.Injective (pullHyp1 (cechTripleRestrictComposite ψ φ s'')) := by
  intro x y e
  obtain ⟨x0, rfl⟩ := (pairRes_bijective (ψ ≫ φ) s'').2.2.2 x
  obtain ⟨y0, rfl⟩ := (pairRes_bijective (ψ ≫ φ) s'').2.2.2 y
  rw [cechTripleRestrictComposite_pairRes_first, cechTripleRestrictComposite_pairRes_first] at e
  rw [(restrict_bijective_one_of_basis s'' _ (triple_cover_affine ψ φ s'')
    (exists_triple_below_two ψ φ s'')).1 e]

theorem cechTripleRestrictComposite_injective_second (s'' : X'' ⟶ Sp R'') : Function.Injective (pullHyp2 (cechTripleRestrictComposite ψ φ s'')) := by
  intro x y e
  obtain ⟨x0, rfl⟩ := (pairRes_bijective_two (ψ ≫ φ) s'').2 x
  obtain ⟨y0, rfl⟩ := (pairRes_bijective_two (ψ ≫ φ) s'').2 y
  rw [cechTripleRestrictComposite_pairRes_second, cechTripleRestrictComposite_pairRes_second] at e
  rw [(restrict_bijective_two_of_basis s'' _ (triple_cover_affine ψ φ s'')
    (exists_triple_below_two ψ φ s'')).1 e]

end Triple

section Comp

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {X X' X'' : Scheme.{0}}
  {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R →+* R'} {τ : R' →+* R''}
  {φ : X' ⟶ X} {ψ : X'' ⟶ X'}

theorem tri_pull_pull1 (h : φ ≫ s = s' ≫ spMap σ) (h' : ψ ≫ s' = s'' ≫ spMap τ)
    (h'' : (ψ ≫ φ) ≫ s = s'' ≫ spMap (τ.comp σ)) (a : HH1 s) :
    pullHyp1 (cechTripleRestrictComposite ψ φ s'') (pullHyp1 (pairPull h'') a) =
      pullHyp1 (cechTriplePullbackSecond h') (pullHyp1 (pairPull h) a) := by
  rw [← pullHyp1_comp, ← pullHyp1_comp]
  exact pullHyp1_eq_of_natTrans ((pairPull h'').comp (cechTripleRestrictComposite ψ φ s''))
    ((pairPull h).comp (cechTriplePullbackSecond h')) { app U := 𝟙 _ } (fun U b ↦ by
      erw [mp_id]
      exact congrArg (fun q ↦ q.hom b) (Scheme.Hom.appLE_comp_appLE ψ φ U.unop.1.2.2.1 U.unop.1.2.1.1
        U.unop.1.1.1 U.unop.2.2 U.unop.2.1)) a

theorem tri_pull_pull2 (h : φ ≫ s = s' ≫ spMap σ) (h' : ψ ≫ s' = s'' ≫ spMap τ)
    (h'' : (ψ ≫ φ) ≫ s = s'' ≫ spMap (τ.comp σ)) (a : HH2 s) :
    pullHyp2 (cechTripleRestrictComposite ψ φ s'') (pullHyp2 (pairPull h'') a) =
      pullHyp2 (cechTriplePullbackSecond h') (pullHyp2 (pairPull h) a) := by
  rw [← pullHyp2_comp, ← pullHyp2_comp]
  exact pullHyp2_eq_of_natTrans ((pairPull h'').comp (cechTripleRestrictComposite ψ φ s''))
    ((pairPull h).comp (cechTriplePullbackSecond h')) { app U := 𝟙 _ } (fun U b ↦ by
      erw [mp_id]
      exact congrArg (fun q ↦ q.hom b) (Scheme.Hom.appLE_comp_appLE ψ φ U.unop.1.2.2.1 U.unop.1.2.1.1
        U.unop.1.1.1 U.unop.2.2 U.unop.2.1)) a

theorem tri_res_pull1 (h' : ψ ≫ s' = s'' ≫ spMap τ) (a : HH1 s') :
    pullHyp1 (cechTriplePullbackSecond (φ := φ) h') (pullHyp1 (pairRes φ s') a) =
      pullHyp1 (cechTripleRestrictFirst ψ φ s'') (pullHyp1 (pairPull h') a) := by
  rw [← pullHyp1_comp, ← pullHyp1_comp]
  exact pullHyp1_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ by erw [mp_id]) a

theorem tri_res_pull2 (h' : ψ ≫ s' = s'' ≫ spMap τ) (a : HH2 s') :
    pullHyp2 (cechTriplePullbackSecond (φ := φ) h') (pullHyp2 (pairRes φ s') a) =
      pullHyp2 (cechTripleRestrictFirst ψ φ s'') (pullHyp2 (pairPull h') a) := by
  rw [← pullHyp2_comp, ← pullHyp2_comp]
  exact pullHyp2_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ by erw [mp_id]) a

theorem cechTriple_restrict_restrict_first (a : HH1 s'') :
    pullHyp1 (cechTripleRestrictFirst ψ φ s'') (pullHyp1 (pairRes ψ s'') a) =
      pullHyp1 (cechTripleRestrictComposite ψ φ s'') (pullHyp1 (pairRes (ψ ≫ φ) s'') a) := by
  rw [← pullHyp1_comp, ← pullHyp1_comp]
  exact pullHyp1_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ mp_id (OAff s'') _ b) a

theorem cechTriple_restrict_restrict_second (a : HH2 s'') :
    pullHyp2 (cechTripleRestrictFirst ψ φ s'') (pullHyp2 (pairRes ψ s'') a) =
      pullHyp2 (cechTripleRestrictComposite ψ φ s'') (pullHyp2 (pairRes (ψ ≫ φ) s'') a) := by
  rw [← pullHyp2_comp, ← pullHyp2_comp]
  exact pullHyp2_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ mp_id (OAff s'') _ b) a

theorem isPull_comp (h : φ ≫ s = s' ≫ spMap σ) (h' : ψ ≫ s' = s'' ≫ spMap τ)
    (h'' : (ψ ≫ φ) ≫ s = s'' ≫ spMap (τ.comp σ)) :
    (∀ a a' a'', IsPull1 h a a' → IsPull1 h' a' a'' → IsPull1 h'' a a'') ∧
      (∀ a a' a'', IsPull2 h a a' → IsPull2 h' a' a'' → IsPull2 h'' a a'') := by
  refine ⟨fun a a' a'' p p' ↦ cechTripleRestrictComposite_injective_first ψ φ s'' ?_,
    fun a a' a'' p p' ↦ cechTripleRestrictComposite_injective_second ψ φ s'' ?_⟩
  · have p0 : pullHyp1 (pairPull h) a = pullHyp1 (pairRes φ s') a' := p
    have p1 : pullHyp1 (pairPull h') a' = pullHyp1 (pairRes ψ s'') a'' := p'
    rw [tri_pull_pull1 h h' h'', p0, tri_res_pull1, p1, cechTriple_restrict_restrict_first]
  · have p0 : pullHyp2 (pairPull h) a = pullHyp2 (pairRes φ s') a' := p
    have p1 : pullHyp2 (pairPull h') a' = pullHyp2 (pairRes ψ s'') a'' := p'
    rw [tri_pull_pull2 h h' h'', p0, tri_res_pull2, p1, cechTriple_restrict_restrict_second]

end Comp

end GlobalTheory.CechDR
