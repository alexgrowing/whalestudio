import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointTorusPartEqOfEquivSameLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfPresentationsSamePolarisationLevelStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

theorem GlobalTheory.TInj.low_eq_of_match : ∀ {o : Type} [CommRing o] {ζ : o} {n : ℕ} (L : LowBase ζ n), 3 ≤ n → IsUnit ζ → IsUnit (n : o) → ∀ {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin L.T.r → ℤ)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D₁ D₂ : DegPre V) (ω₁ : L.W →+* V) (s₁ : I → V) (e₁ : D₁.X ≃+ (Fin L.T.r → ℤ)) (β₁ : D₁.P.A.left ⟶ L.T.B.left) (ββ₁ : (G2 D₁.P.A).left ⟶ (G2 L.T.B).left) (w₁ : LB.Iso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ L.T.B L.T.M.L).pull ββ₁)) (ω₂ : L.W →+* V) (s₂ : I → V) (e₂ : D₂.X ≃+ (Fin L.T.r → ℤ)) (β₂ : D₂.P.A.left ⟶ L.T.B.left) (ββ₂ : (G2 D₂.P.A).left ⟶ (G2 L.T.B).left) (w₂ : LB.Iso (abelian₂ D₂.P.A D₂.P.L) ((abelian₂ L.T.B L.T.M.L).pull ββ₂)) (b : D₁.P.A ⟶ D₂.P.A) (φ : D₁.X ≃+ D₂.X) (F : Type) [Field F] [Algebra (FractionRing V) F], D₁.TauBimult → D₂.TauBimult → From L.T ω₁ s₁ ε n D₁ e₁ β₁ ββ₁ w₁ → From L.T ω₂ s₂ ε n D₂ e₂ β₂ ββ₂ w₂ → ω₁.comp L.T.b = ω₂.comp L.T.b → Match D₁ D₂ b φ F → (∀ y, e₂ (φ y) = e₁ y) → (∀ a : Fin L.T.r → ℤ, ∃ (p₁ : QkPt D₁ F n) (p₂ : QkPt D₂ F n), p₁.y = e₁.symm a ∧ TautPt L.T ω₁ s₁ ε n D₁ e₁ β₁ ββ₁ w₁ F a p₁.g ∧ p₂.y = e₂.symm a ∧ TautPt L.T ω₂ s₂ ε n D₂ e₂ β₂ ββ₂ w₂ F a p₂.g ∧ QImg b φ p₁ p₂) → (∀ l : Fin L.h ⊕ Fin L.h → ℤ, ∃ (p₁ : QkPt D₁ F n) (p₂ : QkPt D₂ F n), p₁.y = 0 ∧ p₁.g.b.left ≫ β₁ ≫ L.β = (TF (R := V) F).hom ≫ spMap ω₁ ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom ≫ (L.F.univ.lev l).left ∧ p₂.y = 0 ∧ p₂.g.b.left ≫ β₂ ≫ L.β = (TF (R := V) F).hom ≫ spMap ω₂ ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom ≫ (L.F.univ.lev l).left ∧ QImg b φ p₁ p₂) → spMap ω₁ ≫ L.u = spMap ω₂ ≫ L.u ∧ (ω₁ = ω₂ → b.left ≫ β₂ = β₁) := by
  intro o _ ζ n L hn hζ hnu I _ ε V _ _ _ D₁ D₂ ω₁ s₁ e₁ β₁ ββ₁ w₁ ω₂ s₂ e₂ β₂ ββ₂ w₂ b φ F _ _ hτ₁ hτ₂ hF₁ hF₂ hω hM he
    hco hlev
  have himg : ∀ (p₁ : QkPt D₁ F n) (p₂ : QkPt D₂ F n), QImg b φ p₁ p₂ → p₂.y = φ p₁.y →
      p₂.g.b.left = p₁.g.b.left ≫ b.left := by
    rintro p₁ p₂ ⟨p', hp'y, hact, heqv⟩ hy
    have hg : p'.g = p₂.g := GlobalTheory.T.torsionPoint_torusPart_eq_of_equiv_same_lattice V D₂ hτ₂ F n (by omega) p' p₂ (hp'y.trans hy.symm) heqv
    rw [← hg, hact.1, Over.comp_left]
  haveI := hM.2.1
  haveI : IsMonHom (asIso b).hom := hM.1
  set t₁ : Sp V ⟶ L.F.X := spMap ω₁ ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom with ht₁
  set t₂ : Sp V ⟶ L.F.X := spMap ω₂ ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom with ht₂
  let a₁ : D₁.P.A.left ⟶ L.F.univ.A.left := β₁ ≫ L.β
  let a₂ : D₁.P.A.left ⟶ L.F.univ.A.left := b.left ≫ β₂ ≫ L.β
  let bb : (G2 D₁.P.A).left ⟶ (G2 D₂.P.A).left :=
    (lift (fst D₁.P.A D₁.P.A ≫ b) (snd D₁.P.A D₁.P.A ≫ b) : G2 D₁.P.A ⟶ G2 D₂.P.A).left
  let aa₁ : (G2 D₁.P.A).left ⟶ (G2 L.F.univ.A).left := ββ₁ ≫ L.β₂
  let aa₂ : (G2 D₁.P.A).left ⟶ (G2 L.F.univ.A).left := bb ≫ ββ₂ ≫ L.β₂
  have hpb₁ : IsGrpPullback D₁.P.A L.F.univ.A t₁ a₁ := IsGrpPullback.comp hF₁.1 L.cart
  have hpb₂ : IsGrpPullback D₁.P.A L.F.univ.A t₂ a₂ :=
    (IsGrpPullback.comp (ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_of_iso (asIso b))
      (IsGrpPullback.comp hF₂.1 L.cart)).congr (Category.id_comp _) rfl
  have hbsq : IsSquare b.left bb :=
    ⟨by rw [← Over.comp_left, lift_fst, Over.comp_left], by rw [← Over.comp_left, lift_snd, Over.comp_left]⟩
  have hsq₁ : IsSquare a₁ aa₁ := GlobalTheory.PolDeg.isSquare_comp hF₁.2.1 L.sq
  have hsq₂ : IsSquare a₂ aa₂ := GlobalTheory.PolDeg.isSquare_comp hbsq (GlobalTheory.PolDeg.isSquare_comp hF₂.2.1 L.sq)
  have hLam : ∀ D : DegPre V, (abelian₂ D.P.A D.P.L).IsLB := fun D => LB.isLB_linComb D.P.isLB _ _
  have hLamT : (abelian₂ L.T.B L.T.M.L).IsLB := LB.isLB_linComb L.T.M.isLB _ _
  have hU := L.F.univ.isLB
  have hA₁ : LBIso (abelian₂ D₁.P.A D₁.P.L) (L.F.univ.P.pull aa₁) :=
    LBIso.trans (hLam D₁) (pull_isLB hLamT ββ₁) (pull_isLB hU _) ⟨w₁, hF₁.2.2.1⟩
      (GlobalTheory.PolDeg.lbIso_pull_comp L.lb ββ₁ rfl)
  have hA₂' : LBIso (abelian₂ D₂.P.A D₂.P.L) (L.F.univ.P.pull (ββ₂ ≫ L.β₂)) :=
    LBIso.trans (hLam D₂) (pull_isLB hLamT ββ₂) (pull_isLB hU _) ⟨w₂, hF₂.2.2.1⟩
      (GlobalTheory.PolDeg.lbIso_pull_comp L.lb ββ₂ rfl)
  have hA₂ : LBIso (abelian₂ D₁.P.A D₁.P.L) (L.F.univ.P.pull aa₂) :=
    LBIso.trans (hLam D₁) (pull_isLB (hLam D₂) bb) (pull_isLB hU _) hM.2.2.1
      (GlobalTheory.PolDeg.lbIso_pull_comp hA₂' bb rfl)
  have hP : LBIso (L.F.univ.P.pull aa₁) (L.F.univ.P.pull aa₂) :=
    LBIso.trans (pull_isLB hU _) (hLam D₁) (pull_isLB hU _) hA₁.symm hA₂
  have hs : t₁ ≫ L.F.s = t₂ ≫ L.F.s := by
    have hb : spMap ω₁ ≫ spMap L.T.b = spMap ω₂ ≫ spMap L.T.b := by
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hω]
    have e : ∀ ω : L.W →+* V, (spMap ω ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom) ≫ L.F.s = spMap ω ≫ spMap L.T.b := by
      intro ω
      rw [Category.assoc, Category.assoc, ← L.u_base]
      rfl
    rw [ht₁, ht₂, e, e, hb]
  have hlev' : ∀ l, ∃ x : TF (R := V) F ⟶ D₁.P.A,
      x.left ≫ a₁ = (TF (R := V) F).hom ≫ t₁ ≫ (L.F.univ.lev l).left ∧
      x.left ≫ a₂ = (TF (R := V) F).hom ≫ t₂ ≫ (L.F.univ.lev l).left := by
    intro l
    obtain ⟨p₁, p₂, hy₁, hb₁, hy₂, hb₂, hQ⟩ := hlev l
    have h21 := himg p₁ p₂ hQ (by rw [hy₂, hy₁, map_zero])
    refine ⟨p₁.g.b, ?_, ?_⟩
    · simpa only [a₁, ht₁, Category.assoc] using hb₁
    · have : p₁.g.b.left ≫ a₂ = p₂.g.b.left ≫ β₂ ≫ L.β := by
        simp only [a₂, h21, Category.assoc]
      rw [this, hb₂]
      simp only [ht₂, Category.assoc]
  obtain ⟨ht, ha⟩ := GlobalTheory.T.eq_of_presentations_same_polarisation_level L.F hn hζ hnu V D₁.P.A t₁ t₂ a₁ a₂ aa₁ aa₂ hpb₁ hpb₂ hsq₁ hsq₂ hP hs F hlev'
  have hcoordEq : ∀ i, (spMap ω₁ ≫ L.u) ≫ (GlobalTheory.LowChart.coord L.F i).left =
      (spMap ω₂ ≫ L.u) ≫ (GlobalTheory.LowChart.coord L.F i).left := by
    intro i
    obtain ⟨p₁, p₂, hy₁, hT₁, hy₂, hT₂, hQ⟩ := hco (Pi.single i 1)
    have hφ : p₂.y = φ p₁.y := by
      rw [hy₂, hy₁]
      apply e₂.injective
      rw [he, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    have h21 := himg p₁ p₂ hQ hφ
    have c1 : (TF (R := V) F).hom ≫ (spMap ω₁ ≫ L.u) ≫ (GlobalTheory.LowChart.coord L.F i).left = p₁.g.b.left ≫ a₁ := by
      simp only [a₁, Category.assoc, ← L.coord i]
      rw [← Category.assoc p₁.g.b.left, hT₁.1]
      simp only [Category.assoc]
    have c2 : (TF (R := V) F).hom ≫ (spMap ω₂ ≫ L.u) ≫ (GlobalTheory.LowChart.coord L.F i).left = p₁.g.b.left ≫ a₂ := by
      simp only [a₂, Category.assoc, ← L.coord i]
      rw [← Category.assoc p₁.g.b.left, ← h21, ← Category.assoc p₂.g.b.left, hT₂.1]
      simp only [Category.assoc]
    have hgen : (TF (R := V) F).hom ≫ (spMap ω₁ ≫ L.u) ≫ (GlobalTheory.LowChart.coord L.F i).left =
        (TF (R := V) F).hom ≫ (spMap ω₂ ≫ L.u) ≫ (GlobalTheory.LowChart.coord L.F i).left := by
      rw [c1, c2, ha]
    have : IsProper L.F.univ.A.hom := L.F.univ.ab.proper
    haveI : IsDominant (TF (R := V) F).hom := ReciprocityTheory.ChartRestriction.G.DVR.GC.isDominant_jFR (V := V) F
    refine ext_of_isDominant_of_isSeparated L.F.univ.A.hom ?_ (TF (R := V) F).hom hgen
    simp only [Category.assoc, Over.w]
    exact ht
  refine ⟨GlobalTheory.LowChart.hom_ext _ _ (by simpa only [Category.assoc] using ht) hcoordEq, ?_⟩
  rintro rfl
  apply L.cart.1.hom_ext
  · simpa only [a₁, a₂, Category.assoc] using ha.symm
  · rw [Category.assoc, hF₂.1.1.w, ← Category.assoc, Over.w b, hF₁.1.1.w]
