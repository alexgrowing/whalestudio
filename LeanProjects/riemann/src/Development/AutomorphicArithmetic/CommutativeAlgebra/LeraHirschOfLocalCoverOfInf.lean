import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
import Development.AutomorphicArithmetic.BlowupCategories.AffC
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsIsoOfBijectiveOnSimplices
import Development.AutomorphicArithmetic.CommutativeAlgebra.MonoOfInjectiveOnSimplices
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsPullbackOfUniqueSimplicesPullback
import Development.AutomorphicArithmetic.CommutativeAlgebra.SimplicesPullbackExistsUniqueOfMapEq
import Development.AutomorphicArithmetic.CommutativeAlgebra.MayerVietorisCoverOfMonoOfZariskiLocal
import Development.AutomorphicArithmetic.CommutativeAlgebra.LocallyExistsIsUnitOfSpanRangeEqTop
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsIsoStackProductMapOfBijective
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsIsoStackProductPairOfBijective
import Development.AutomorphicArithmetic.CommutativeAlgebra.StackProductIsPullbackOfActionPullback
import Development.AutomorphicArithmetic.CommutativeAlgebra.LerayHirschOfIsoSquare
import Development.AutomorphicArithmetic.CommutativeAlgebra.LerayHirschOneIffTwistEquiv
import Development.AutomorphicArithmetic.CommutativeAlgebra.AffineLineActionFstTwistEquiv
import Development.AutomorphicArithmetic.CommutativeAlgebra.MayerVietorisStackProductOfInjectiveOfLocallyCov
import Development.AutomorphicArithmetic.CommutativeAlgebra.PullCupPowEqCupPowPull
import Development.AutomorphicArithmetic.CommutativeAlgebra.LerayHirschOfMayerVietorisCover

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

namespace UpperTheory.Glue

private theorem map_incl (E : Spc) {a : Act} {Q R : Pred a} (h : Q.Le R) :
    Sp.map E (inclLe h) ≫ Sp.map E (incl R) = Sp.map E (incl Q) := by
  rfl

private theorem map_inclLe (E : Spc) {a : Act} {Q R S : Pred a} (h : Q.Le R) (h' : R.Le S) (h'' : Q.Le S) :
    Sp.map E (inclLe h) ≫ Sp.map E (inclLe h') = Sp.map E (inclLe h'') := by
  rfl

private theorem comap_le {c a : Act} (π : Act.Hom c a) {Q' Q : Pred a} (h : Q'.Le Q) : (Q'.comap π).Le (Q.comap π) :=
  fun A _ hx => h A _ hx

private theorem sq (E : Spc) {c a : Act} (π : Act.Hom c a) {Q' Q : Pred a} (h : Q'.Le Q) :
    IsPullback (Sp.map E (inclLe (comap_le π h))) (Sp.map E (π.sub Q')) (Sp.map E (π.sub Q)) (Sp.map E (inclLe h)) := by
  refine UpperTheory.stackProduct_isPullback_of_actionPullback E _ _ _ _ (fun _ _ => rfl) (fun _ _ => rfl) ?_ ?_
  · intro A x y hxy
    have e : π.d.app A x.1 = y.1 := congrArg Subtype.val hxy
    have hx : Q'.P A (π.d.app A x.1) := by
      rw [e]
      exact y.2
    refine ⟨⟨x.1, hx⟩, ⟨rfl, Subtype.ext e⟩, ?_⟩
    rintro z ⟨h1, -⟩
    have e1 : z.1 = x.1 := congrArg Subtype.val h1
    exact Subtype.ext e1
  · intro A g g' hg
    exact ⟨g, ⟨rfl, hg⟩, fun z hz => hz.1⟩

private theorem sq_inf (E : Spc) {a : Act} {Q Q₁ Q₂ : Pred a} (h₁ : Q₁.Le Q) (h₂ : Q₂.Le Q) :
    IsPullback (Sp.map E (inclLe (show (Q₁.inf Q₂).Le Q₁ from fun _ _ h => h.1)))
      (Sp.map E (inclLe (show (Q₁.inf Q₂).Le Q₂ from fun _ _ h => h.2)))
      (Sp.map E (inclLe h₁)) (Sp.map E (inclLe h₂)) := by
  refine UpperTheory.stackProduct_isPullback_of_actionPullback E _ _ _ _ (fun A z => rfl) (fun A z => rfl) ?_ ?_
  · intro A x y hxy
    have hv : x.1 = y.1 := congrArg Subtype.val hxy
    refine ⟨⟨x.1, x.2, ?_⟩, ⟨rfl, ?_⟩, ?_⟩
    · rw [hv]
      exact y.2
    · apply Subtype.ext
      exact hv
    · rintro z ⟨hz, -⟩
      have hz' : z.1 = x.1 := congrArg Subtype.val hz
      apply Subtype.ext
      exact hz'
  · intro A g k hgk
    exact ⟨g, ⟨rfl, hgk⟩, fun z hz => hz.1⟩

private theorem cover_tr {R : Type} [CommRing R] {U U' V V' E : Spc} (u : U ⟶ E) (v : V ⟶ E) (u' : U' ⟶ E) (v' : V' ⟶ E)
    (e : U ⟶ U') (e' : V ⟶ V') [IsIso e] [IsIso e'] (hu : e ≫ u' = u) (hv : e' ≫ v' = v) (h : Cover2 R u v) :
    Cover2 R u' v' := by
  subst hu hv
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, fun n => ?_⟩
  · have : u' = inv e ≫ e ≫ u' := by simp
    rw [this]
    infer_instance
  · have : v' = inv e' ≫ e' ≫ v' := by simp
    rw [this]
    infer_instance
  · have h4 := h3 n
    have : biprod.desc ((free R).map ((e ≫ u').app n)) ((free R).map ((e' ≫ v').app n)) =
        biprod.map ((free R).map (e.app n)) ((free R).map (e'.app n)) ≫
          biprod.desc ((free R).map (u'.app n)) ((free R).map (v'.app n)) := by
      apply biprod.hom_ext' <;> simp
    rw [this] at h4
    exact epi_of_epi (biprod.map ((free R).map (e.app n)) ((free R).map (e'.app n))) _

private theorem cov (R : Type) [CommRing R] (E : Spc) {a : Act} {Q Q₁ Q₂ : Pred a} (h₁ : Q₁.Le Q) (h₂ : Q₂.Le Q)
    (hloc : ∀ (T : Scheme.{0}) (x : a.D.obj Γ(T, ⊤)), Q.P _ x →
      Loc T fun V g => Q₁.P _ (a.D.map g.appTop x) ∨ Q₂.P _ (a.D.map g.appTop x)) :
    Cover2 R (Sp.map E (inclLe h₁)) (Sp.map E (inclLe h₂)) := by
  refine UpperTheory.mayerVietoris_stackProduct_of_injective_of_locally_covered R E _ _ ?_ ?_ (fun _ => Function.bijective_id) (fun _ => Function.bijective_id) ?_
  · intro A x y h
    have e := congrArg (fun w : {z // Q.P A z} => w.1) h
    exact Subtype.ext e
  · intro A x y h
    have e := congrArg (fun w : {z // Q.P A z} => w.1) h
    exact Subtype.ext e
  · intro T x
    obtain ⟨S, hS, hP⟩ := hloc T x.1 x.2
    refine ⟨S, hS, fun V g hg => ?_⟩
    rcases hP V g hg with h | h
    · exact Or.inl ⟨⟨_, h⟩, rfl⟩
    · exact Or.inr ⟨⟨_, h⟩, rfl⟩

private theorem tr (q : ℕ) [NeZero q] (E : Spc) {c a : Act} (π : Act.Hom c a) {m : ℕ} (d e : Fin m → ℤ)
    (cl : ∀ j, Ht q (Sp E c) (d j) (e j)) {Q' Q : Pred a} (h : Q'.Le Q) {P B' : Spc}
    (fs : P ⟶ Sp E (c.sub (Q.comap π))) (sn : P ⟶ B') (u : P ⟶ Sp E (c.sub (Q'.comap π))) (b : B' ⟶ Sp E (a.sub Q'))
    [IsIso u] [IsIso b] (hu : u ≫ Sp.map E (inclLe (comap_le π h)) = fs) (hb : u ≫ Sp.map E (π.sub Q') = sn ≫ b)
    (L : LHQ q E π d e cl Q') :
    LH q sn d e (fun j => pull _ fs _ _ (pull _ (Sp.map E (incl (Q.comap π))) _ _ (cl j))) := by
  have h1 := UpperTheory.lerayHirsch_of_iso_square q (Sp.map E (π.sub Q')) sn u b hb d e _ L
  have h2 : (fun j => pull _ fs _ _ (pull _ (Sp.map E (incl (Q.comap π))) _ _ (cl j))) =
      fun j => pull _ u _ _ (pull _ (Sp.map E (incl (Q'.comap π))) _ _ (cl j)) := by
    funext j
    rw [← pull_comp, ← pull_comp, ← hu, Category.assoc, map_incl]
  rw [h2]
  exact h1

end UpperTheory.Glue

theorem UpperTheory.leraHirsch_of_local_cover_of_inf :
    ∀ (q : ℕ) [NeZero q] (E : Spc), Inv q E → ∀ {c a : Act} (π : Act.Hom c a) {m : ℕ} (d e : Fin m → ℤ) (cl : ∀ j, Ht q (Sp E c) (d j) (e j))
        (Q Q₁ Q₂ : Pred a) (_ : Q₁.Le Q) (_ : Q₂.Le Q),
        (∀ (T : Scheme.{0}) (x : a.D.obj Γ(T, ⊤)), Q.P _ x → Loc T fun V g => Q₁.P _ (a.D.map g.appTop x) ∨ Q₂.P _ (a.D.map g.appTop x)) →
        LHQ q E π d e cl Q₁ → LHQ q E π d e cl Q₂ → LHQ q E π d e cl (Q₁.inf Q₂) → LHQ q E π d e cl Q := by
  intro q _ E _ c a π m d e cl Q Q₁ Q₂ h₁ h₂ hloc L₁ L₂ L₁₂
  have hinf : (Q₁.inf Q₂).Le Q := fun A x hx => h₁ A x hx.1
  have sq1 := UpperTheory.Glue.sq E π h₁
  have sq2 := UpperTheory.Glue.sq E π h₂
  have sqi := UpperTheory.Glue.sq_inf E h₁ h₂
  have hloc' : ∀ (T : Scheme.{0}) (x : c.D.obj Γ(T, ⊤)), (Q.comap π).P _ x →
      Loc T fun V g => (Q₁.comap π).P _ (c.D.map g.appTop x) ∨ (Q₂.comap π).P _ (c.D.map g.appTop x) := by
    intro T x hx
    obtain ⟨S, hS, hP⟩ := hloc T _ hx
    refine ⟨S, hS, fun V g hg => ?_⟩
    show Q₁.P _ _ ∨ Q₂.P _ _
    rw [FunctorToTypes.naturality]
    exact hP V g hg
  have sq' : IsPullback (Sp.map E (inclLe (UpperTheory.Glue.comap_le π hinf)))
      (Sp.map E (π.sub (Q₁.inf Q₂)) ≫ sqi.isoPullback.hom) (Sp.map E (π.sub Q))
      (pullback.fst (Sp.map E (inclLe h₁)) (Sp.map E (inclLe h₂)) ≫ Sp.map E (inclLe h₁)) := by
    refine (UpperTheory.Glue.sq E π hinf).of_iso (Iso.refl _) (Iso.refl _) sqi.isoPullback (Iso.refl _)
      (by simp) (by simp) (by simp) ?_
    rw [Iso.refl_hom, Category.comp_id, ← Category.assoc, IsPullback.isoPullback_hom_fst,
      UpperTheory.Glue.map_inclLe]
  refine UpperTheory.lerayHirsch_of_mayerVietoris_cover q (Sp.map E (inclLe h₁)) (Sp.map E (inclLe h₂)) (Sp.map E (π.sub Q)) d e _
    (UpperTheory.Glue.cov _ E h₁ h₂ hloc) ?_ ?_ ?_ ?_
  · exact UpperTheory.Glue.cover_tr (Sp.map E (inclLe (UpperTheory.Glue.comap_le π h₁)))
      (Sp.map E (inclLe (UpperTheory.Glue.comap_le π h₂))) _ _ sq1.isoPullback.hom sq2.isoPullback.hom
      sq1.isoPullback_hom_fst sq2.isoPullback_hom_fst
      (UpperTheory.Glue.cov _ E (UpperTheory.Glue.comap_le π h₁) (UpperTheory.Glue.comap_le π h₂) hloc')
  · exact UpperTheory.Glue.tr q E π d e cl h₁ _ _ sq1.isoPullback.inv (𝟙 _) sq1.isoPullback_inv_fst
      (by rw [sq1.isoPullback_inv_snd, Category.comp_id]) L₁
  · exact UpperTheory.Glue.tr q E π d e cl h₂ _ _ sq2.isoPullback.inv (𝟙 _) sq2.isoPullback_inv_fst
      (by rw [sq2.isoPullback_inv_snd, Category.comp_id]) L₂
  · exact UpperTheory.Glue.tr q E π d e cl hinf _ _ sq'.isoPullback.inv sqi.isoPullback.inv
      sq'.isoPullback_inv_fst
      (by rw [← sq'.isoPullback_inv_snd, Category.assoc, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]) L₁₂
