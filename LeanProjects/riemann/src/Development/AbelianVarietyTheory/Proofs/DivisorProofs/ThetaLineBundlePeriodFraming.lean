import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.SymChart
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (transl per IsBundleIso mulPullFactor)

section
open MonObj CartesianMonoidalCategory

theorem ex_neg {k : Type} [CommRing k] {S : Scheme.{0}} {p : S ⟶ Sp k} {σ : k →+* ℂ} {A : Over S}
    [GrpObj A] {g : ℕ} {h : VMetric p (omega A) g} {c : AlgChart p σ 1}
    {τ : V 1 → Matrix (Fin g) (Fin g) ℂ} {ex : Pt (V 1) g → CxPts (A.hom ≫ p) σ}
    (H : IsPeriodChart h c τ ex) {v : V 1} (hv : v ∈ c.e.target) (z : Fin g → ℂ) :
    (ex (v, -z)).1 = (ex (v, z)).1 ≫ (ι[A]).left := by
  obtain ⟨h₁, h₂, -, h₄, -⟩ := H.2.2 v hv
  let e (w : Fin g → ℂ) : Over.mk (c.e.symm v).1 ⟶ A := Over.homMk (ex (v, w)).1 (h₁ w)
  have h0 : (ex (v, 0)).1 = (c.e.symm v).1 ≫ GlobalTheory.LieVB.unitSec A :=
    (h₄ 0).2 ⟨0, zero_mem _, by ext i; simp [per, Matrix.vecMul, dotProduct]⟩
  have hm : e z * e (-z) = 1 := by
    refine Over.OverMorphism.ext ?_
    rw [h₂ z (-z) _ _ rfl rfl, add_neg_cancel, h0]
    rfl
  have hi : e (-z) = (e z)⁻¹ := eq_inv_of_mul_eq_one_right hm
  exact congrArg (·.left) hi
end

section Lift
variable {k : Type} [CommRing k] {X : Scheme.{0}} {q : X ⟶ Sp k} {σ : k →+* ℂ}

theorem range_sub (O : X.Opens) {y : Sp ℂ ⟶ X} (hy : ⊤ ≤ y ⁻¹ᵁ O) :
    Set.range y.base ⊆ Set.range O.ι.base := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨z, rfl⟩
  exact hy (show z ∈ (⊤ : (Sp ℂ).Opens) from trivial)

def liftPt (O : X.Opens) (y : CxPts q σ) (h : y ∈ ptsIn q σ O) : CxPts (O.ι ≫ q) σ :=
  ⟨IsOpenImmersion.lift O.ι y.1 (range_sub O h), by
    rw [← Category.assoc, IsOpenImmersion.lift_fac]; exact y.2⟩

theorem liftPt_fac (O : X.Opens) (y : CxPts q σ) (h : y ∈ ptsIn q σ O) :
    (liftPt O y h).1 ≫ O.ι = y.1 := IsOpenImmersion.lift_fac _ _ _

theorem valR_eqToHom {C : Type} [CommRing C] {Y : Scheme.{0}} (x : Sp C ⟶ Y) {U U' : Y.Opens}
    (e : U = U') (f : Γ(Y, U')) :
    valR x U ((Y.presheaf.map (eqToHom e).op).hom f) = valR x U' f := by
  subst e
  simp

theorem mem_ptsIn_liftPt (O : X.Opens) (y : CxPts q σ) (h : y ∈ ptsIn q σ O) (W : O.toScheme.Opens) :
    liftPt O y h ∈ ptsIn (O.ι ≫ q) σ W ↔ y ∈ ptsIn q σ (O.ι ''ᵁ W) := by
  have e : y.1 = (liftPt O y h).1 ≫ O.ι := (liftPt_fac O y h).symm
  change ⊤ ≤ (liftPt O y h).1 ⁻¹ᵁ W ↔ ⊤ ≤ y.1 ⁻¹ᵁ (O.ι ''ᵁ W)
  rw [e, Scheme.Hom.comp_preimage, O.ι.preimage_image_eq]

theorem ev_liftPt (O : X.Opens) (y : CxPts q σ) (h : y ∈ ptsIn q σ O) (W : O.toScheme.Opens)
    (s : Γ(O.toScheme, W)) :
    ev (O.ι ≫ q) σ W s (liftPt O y h) = ev q σ (O.ι ''ᵁ W) ((O.ι.appIso W).inv s) y := by
  have e : s = (O.ι.appIso W).hom ((O.ι.appIso W).inv s) := by simp; rfl
  change valR _ W s = valR y.1 _ _
  conv_lhs => rw [e, Scheme.Hom.appIso_hom]
  rw [CommRingCat.comp_apply, valR_eqToHom, ← GlobalTheory.Points.valR_comp, liftPt_fac]

end Lift

section Gen
variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ}

theorem ev_gen_rel {B : LB Y} {t : LB.Gen B} (ht : t.IsGen) {i j : B.ι} {y : CxPts p σ}
    (hi : y ∈ ptsIn p σ (B.U i)) (hj : y ∈ ptsIn p σ (B.U j)) :
    ev p σ _ (t.s i).val y = gv p σ B i j y * ev p σ _ (t.s j).val y := by
  have hy : y ∈ ptsIn p σ (B.U i ⊓ B.U j) := mem_ptsIn_inf.2 ⟨hi, hj⟩
  have e := congrArg (fun u : Γ(Y, B.U i ⊓ B.U j)ˣ => ev p σ _ u.val y) (ht i j)
  exact (ev_res _ hy _).symm.trans (e.trans ((ev_mul _ _ y).trans
    (congrArg₂ (· * ·) rfl (ev_res _ hy _))))

theorem ev_gen_ne_zero {B : LB Y} (t : LB.Gen B) {i : B.ι} {y : CxPts p σ}
    (hi : y ∈ ptsIn p σ (B.U i)) : ev p σ _ (t.s i).val y ≠ 0 :=
  ev_ne_zero hi (t.s i).isUnit

variable {k' : Type} [CommRing k'] {Y' : Scheme.{0}} {p' : Y' ⟶ Sp k'} {σ' : k' →+* ℂ}
  {κ : Type} [Fintype κ] {f : κ → (Y' ⟶ Y)} {z : CxPts p' σ'} {m : κ → CxPts p σ}

theorem mem_linComb_of_mem (hm : ∀ a, (m a).1 = z.1 ≫ f a) {B : LB Y} (ε : κ → ℤ) {j : κ → B.ι}
    (h : ∀ a, m a ∈ ptsIn p σ (B.U (j a))) : z ∈ ptsIn p' σ' ((LB.LinComb B f ε).U j) := by
  intro x hx
  refine Set.mem_iInter.2 fun a => ?_
  have := h a hx
  rw [hm a] at this
  exact this
end Gen

section Hol
variable {k : Type} [CommRing k] {X : Scheme.{0}} {q : X ⟶ Sp k} {σ : k →+* ℂ}

open Classical in

def evLift (O : X.Opens) (W : O.toScheme.Opens) (s : Γ(O.toScheme, W)) (y : CxPts q σ) : ℂ :=
  if h : y ∈ ptsIn q σ O then ev (O.ι ≫ q) σ W s (liftPt O y h) else 0

theorem evLift_of_mem (O : X.Opens) (W : O.toScheme.Opens) (s : Γ(O.toScheme, W)) {y : CxPts q σ}
    (h : y ∈ ptsIn q σ O) : evLift O W s y = ev (O.ι ≫ q) σ W s (liftPt O y h) := dif_pos h

theorem differentiableAt_evLift {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {T : Set E}
    {ex : E → CxPts q σ} (hex : IsHolTo T (fun b => (ex b).1)) (O : X.Opens) (W : O.toScheme.Opens)
    (s : Γ(O.toScheme, W)) {P : E} (hP : P ∈ T) (hO : ex P ∈ ptsIn q σ O)
    (hW : liftPt O (ex P) hO ∈ ptsIn (O.ι ≫ q) σ W) :
    DifferentiableAt ℂ (fun Q => evLift O W s (ex Q)) P := by
  obtain ⟨ho, hd⟩ := hex (O.ι ''ᵁ W) ((O.ι.appIso W).inv s)
  have hPN : P ∈ {b ∈ T | ⊤ ≤ (ex b).1 ⁻¹ᵁ (O.ι ''ᵁ W)} :=
    ⟨hP, (mem_ptsIn_liftPt O _ hO W).1 hW⟩
  have hsub : O.ι ''ᵁ W ≤ O := Scheme.Opens.ι_image_le O W
  refine (hd.differentiableAt (ho.mem_nhds hPN)).congr_of_eventuallyEq ?_
  filter_upwards [ho.mem_nhds hPN] with Q hQ
  have hQO : ex Q ∈ ptsIn q σ O := ptsIn_mono hsub hQ.2
  rw [evLift_of_mem O W s hQO, ev_liftPt]
  rfl
end Hol

section SymLB
open MonObj

abbrev symLB {S : Scheme.{0}} (A : Over S) [GrpObj A] (U : S.Opens) (L : LB A.left) :
    LB (A.hom ⁻¹ᵁ U).toScheme :=
  LB.LinComb L (K := Fin 2) ![(A.hom ⁻¹ᵁ U).ι ≫ (ι[A]).left, (A.hom ⁻¹ᵁ U).ι] ![1, -1]
end SymLB

section Core
open MonObj
variable {k : Type} [CommRing k] {S : Scheme.{0}} {p : S ⟶ Sp k} {σ : k →+* ℂ} {A : Over S}
  [GrpObj A] {g : ℕ} {h : VMetric p (omega A) g} {c : AlgChart p σ 1}
  {τ : V 1 → Matrix (Fin g) (Fin g) ℂ} {ex : Pt (V 1) g → CxPts (A.hom ≫ p) σ}

theorem mulN_neg_one (Q : Pt (V 1) g) : IndefiniteRowSideFullHecke.SiegelReframe.mulN (-1) Q = (Q.1, -Q.2) := by
  simp [IndefiniteRowSideFullHecke.SiegelReframe.mulN]

theorem per_neg (T : Matrix (Fin g) (Fin g) ℂ) (x : Fl g) : per T (-x) = -per T x := by
  ext i
  simp [per, Matrix.vecMul, dotProduct, Finset.sum_neg_distrib]
  ring

theorem mem_O (H : IsPeriodChart h c τ ex) {U : S.Opens} {P : Pt (V 1) g}
    (hP : P ∈ cov (c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ U) g) :
    ex P ∈ ptsIn (A.hom ≫ p) σ (A.hom ⁻¹ᵁ U) := by
  have h₁ := (H.2.2 P.1 hP.1.1).1 P.2
  have hU : ⊤ ≤ (c.e.symm P.1).1 ⁻¹ᵁ U := hP.1.2
  rw [← h₁] at hU
  exact hU

theorem exists_isBundleIso_of_gen (H : IsPeriodChart h c τ ex) (L : HermLB (A.hom ≫ p))
    {j : Fl g → Pt (V 1) g → ℂ} {m : Pt (V 1) g → ℝ} (hF : IsFramed L c.e.target τ ex j m)
    (U : S.Opens)
    (t : LB.Gen (symLB A U L.B)) (ht : t.IsGen) :
    ∃ φ, IsBundleIso (c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ U) τ (stdLat g)
      (mulPullFactor (-1) j) j φ := by
  obtain ⟨fr, hfr⟩ := hF
  set B' := c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ U with hB'
  have hLB := L.isLB
  let tv (jj : Fin 2 → L.B.ι) (y : CxPts (A.hom ≫ p) σ) : ℂ := evLift (A.hom ⁻¹ᵁ U) ((symLB A U L.B).U jj) (t.s jj).val y
  let a0 (P : Pt (V 1) g) : L.B.ι := pick hLB (ex P)
  let b0 (P : Pt (V 1) g) : L.B.ι := pick hLB (ex (IndefiniteRowSideFullHecke.SiegelReframe.mulN (-1) P))
  let F (P : Pt (V 1) g) : ℂ :=
    fr (b0 P) (IndefiniteRowSideFullHecke.SiegelReframe.mulN (-1) P) / (tv ![b0 P, a0 P] (ex P) * fr (a0 P) P)
  have hcov : ∀ P ∈ cov B' g, P ∈ cov c.e.target g := fun P hP => ⟨hP.1.1, trivial⟩
  have hcovN : ∀ P ∈ cov B' g, IndefiniteRowSideFullHecke.SiegelReframe.mulN (-1) P ∈ cov B' g := fun P hP => ⟨hP.1, trivial⟩
  have hinv : ∀ P ∈ cov B' g, (ex (IndefiniteRowSideFullHecke.SiegelReframe.mulN (-1) P)).1 = (ex P).1 ≫ (ι[A]).left := by
    intro P hP
    rw [mulN_neg_one]
    exact ex_neg H hP.1.1 P.2

  have hmem : ∀ P (hP : P ∈ cov B' g) (a b : L.B.ι), ex P ∈ ptsIn _ σ (L.B.U a) →
      ex (IndefiniteRowSideFullHecke.SiegelReframe.mulN (-1) P) ∈ ptsIn _ σ (L.B.U b) →
      liftPt (A.hom ⁻¹ᵁ U) (ex P) (mem_O H hP) ∈ ptsIn ((A.hom ⁻¹ᵁ U).ι ≫ A.hom ≫ p) σ ((symLB A U L.B).U ![b, a]) := by
    intro P hP a b ha hb
    refine mem_linComb_of_mem (m := ![ex (IndefiniteRowSideFullHecke.SiegelReframe.mulN (-1) P), ex P]) ?_ _ ?_
    · intro i
      fin_cases i
      · change (ex (IndefiniteRowSideFullHecke.SiegelReframe.mulN (-1) P)).1 = _ ≫ (A.hom ⁻¹ᵁ U).ι ≫ _
        rw [← Category.assoc, liftPt_fac, hinv P hP]
      · change (ex P).1 = _ ≫ (A.hom ⁻¹ᵁ U).ι
        rw [liftPt_fac]
    · intro i
      fin_cases i
      · exact hb
      · exact ha

  have hm : ∀ P (hP : P ∈ cov B' g) (i : Fin 2),
      (![ex (IndefiniteRowSideFullHecke.SiegelReframe.mulN (-1) P), ex P] i).1 = (liftPt (A.hom ⁻¹ᵁ U) (ex P) (mem_O H hP)).1 ≫ ![(A.hom ⁻¹ᵁ U).ι ≫ (ι[A]).left, (A.hom ⁻¹ᵁ U).ι] i := by
    intro P hP i
    fin_cases i
    · change (ex (IndefiniteRowSideFullHecke.SiegelReframe.mulN (-1) P)).1 = _ ≫ (A.hom ⁻¹ᵁ U).ι ≫ _
      rw [← Category.assoc, liftPt_fac, hinv P hP]
    · change (ex P).1 = _ ≫ (A.hom ⁻¹ᵁ U).ι
      rw [liftPt_fac]
  have hgv : ∀ P (hP : P ∈ cov B' g) (a b a' b' : L.B.ι), ex P ∈ ptsIn _ σ (L.B.U a) →
      ex (IndefiniteRowSideFullHecke.SiegelReframe.mulN (-1) P) ∈ ptsIn _ σ (L.B.U b) → ex P ∈ ptsIn _ σ (L.B.U a') →
      ex (IndefiniteRowSideFullHecke.SiegelReframe.mulN (-1) P) ∈ ptsIn _ σ (L.B.U b') →
      tv ![b', a'] (ex P) = gv _ σ L.B b' b (ex (IndefiniteRowSideFullHecke.SiegelReframe.mulN (-1) P)) *
        (gv _ σ L.B a' a (ex P))⁻¹ * tv ![b, a] (ex P) := by
    intro P hP a b a' b' ha hb ha' hb'
    simp only [tv]
    rw [evLift_of_mem _ _ _ (mem_O H hP), evLift_of_mem _ _ _ (mem_O H hP),
      ev_gen_rel ht (hmem P hP a' b' ha' hb') (hmem P hP a b ha hb),
      gv_linComb (hm P hP) (hmem P hP a' b' ha' hb') (hmem P hP a b ha hb)]
    simp [Fin.prod_univ_two]
  have htv0 : ∀ P (hP : P ∈ cov B' g) (a b : L.B.ι), ex P ∈ ptsIn _ σ (L.B.U a) →
      ex (IndefiniteRowSideFullHecke.SiegelReframe.mulN (-1) P) ∈ ptsIn _ σ (L.B.U b) → tv ![b, a] (ex P) ≠ 0 := by
    intro P hP a b ha hb
    simp only [tv]
    rw [evLift_of_mem _ _ _ (mem_O H hP)]
    exact ev_gen_ne_zero t (hmem P hP a b ha hb)
  have LF : ∀ P (hP : P ∈ cov B' g) (a b : L.B.ι), ex P ∈ ptsIn _ σ (L.B.U a) →
      ex (IndefiniteRowSideFullHecke.SiegelReframe.mulN (-1) P) ∈ ptsIn _ σ (L.B.U b) →
      F P = fr b (IndefiniteRowSideFullHecke.SiegelReframe.mulN (-1) P) / (tv ![b, a] (ex P) * fr a P) := by
    intro P hP a b ha hb
    have ha0 := mem_pick hLB (ex P)
    have hb0 := mem_pick hLB (ex (IndefiniteRowSideFullHecke.SiegelReframe.mulN (-1) P))
    have e1 : fr (a0 P) P = gv _ σ L.B (a0 P) a (ex P) * fr a P :=
      ((hfr (a0 P)).2 P (hcov P hP) ha0).2.1 a ha
    have e2 : fr (b0 P) (IndefiniteRowSideFullHecke.SiegelReframe.mulN (-1) P) = gv _ σ L.B (b0 P) b (ex (IndefiniteRowSideFullHecke.SiegelReframe.mulN (-1) P)) * fr b (IndefiniteRowSideFullHecke.SiegelReframe.mulN (-1) P) :=
      ((hfr (b0 P)).2 _ (hcov _ (hcovN P hP)) hb0).2.1 b hb
    have e3 := hgv P hP a b (a0 P) (b0 P) ha hb ha0 hb0
    have n1 := gv_ne_zero ha0 ha
    have n2 := gv_ne_zero hb0 hb
    have n3 := htv0 P hP a b ha hb
    have n4 := ((hfr a).2 P (hcov P hP) ha).1
    simp only [F]
    rw [e1, e2, e3]
    rw [div_eq_div_iff (mul_ne_zero (mul_ne_zero (mul_ne_zero n2 (inv_ne_zero n1)) n3) (mul_ne_zero n1 n4)) (mul_ne_zero n3 n4)]
    field_simp
    ring

  have hmeq : (IndefiniteRowSideFullHecke.SiegelReframe.mulN (-1) : Pt (V 1) g → Pt (V 1) g) = fun Q => (Q.1, -Q.2) := funext mulN_neg_one
  have hmd : Differentiable ℂ (IndefiniteRowSideFullHecke.SiegelReframe.mulN (-1) : Pt (V 1) g → Pt (V 1) g) := by
    rw [hmeq]; exact differentiable_fst.prodMk differentiable_snd.neg
  have hopen : ∀ i, IsOpen (cov c.e.target g ∩ ex ⁻¹' ptsIn _ σ (L.B.U i)) := fun i =>
    (H.2.1 (L.B.U i) 0).1
  have hN : IsOpen (cov B' g) := (c.e.isOpen_inter_preimage_symm (isOpen_ptsIn U)).prod isOpen_univ
  refine ⟨F, ?_, ?_, ?_⟩
  · intro P hP
    refine DifferentiableAt.differentiableWithinAt ?_
    have ha : ex P ∈ ptsIn _ σ (L.B.U (a0 P)) := mem_pick hLB _
    have hb : ex (IndefiniteRowSideFullHecke.SiegelReframe.mulN (-1) P) ∈ ptsIn _ σ (L.B.U (b0 P)) := mem_pick hLB _
    have hNb : IsOpen (cov B' g ∩ (cov c.e.target g ∩ ex ⁻¹' ptsIn _ σ (L.B.U (a0 P))) ∩
        IndefiniteRowSideFullHecke.SiegelReframe.mulN (-1) ⁻¹' (cov c.e.target g ∩ ex ⁻¹' ptsIn _ σ (L.B.U (b0 P)))) :=
      (hN.inter (hopen _)).inter ((hopen _).preimage hmd.continuous)
    have hPN : P ∈ cov B' g ∩ (cov c.e.target g ∩ ex ⁻¹' ptsIn _ σ (L.B.U (a0 P))) ∩
        IndefiniteRowSideFullHecke.SiegelReframe.mulN (-1) ⁻¹' (cov c.e.target g ∩ ex ⁻¹' ptsIn _ σ (L.B.U (b0 P))) :=
      ⟨⟨hP, hcov P hP, ha⟩, hcov _ (hcovN P hP), hb⟩
    have heq : F =ᶠ[𝓝 P] fun Q => fr (b0 P) (IndefiniteRowSideFullHecke.SiegelReframe.mulN (-1) Q) /
        (tv ![b0 P, a0 P] (ex Q) * fr (a0 P) Q) := by
      filter_upwards [hNb.mem_nhds hPN] with Q hQ
      exact LF Q hQ.1.1 _ _ hQ.1.2.2 hQ.2.2
    have d1 : DifferentiableAt ℂ (fun Q => fr (b0 P) (IndefiniteRowSideFullHecke.SiegelReframe.mulN (-1) Q)) P :=
      ((hfr (b0 P)).1.differentiableAt
        ((hopen _).mem_nhds ⟨hcov _ (hcovN P hP), hb⟩)).comp P (hmd P)
    have d2 : DifferentiableAt ℂ (fun Q => tv ![b0 P, a0 P] (ex Q)) P :=
      differentiableAt_evLift H.2.1 (A.hom ⁻¹ᵁ U) _ _ (hcov P hP) (mem_O H hP)
        (hmem P hP _ _ ha hb)
    have d3 : DifferentiableAt ℂ (fr (a0 P)) P :=
      (hfr _).1.differentiableAt ((hopen _).mem_nhds ⟨hcov P hP, ha⟩)
    have d4 : DifferentiableAt ℂ (fun Q => tv ![b0 P, a0 P] (ex Q) * fr (a0 P) Q) P := d2.mul d3
    have d5 : DifferentiableAt ℂ (fun Q => fr (b0 P) (IndefiniteRowSideFullHecke.SiegelReframe.mulN (-1) Q) *
        (tv ![b0 P, a0 P] (ex Q) * fr (a0 P) Q)⁻¹) P :=
      d1.mul (d4.inv (mul_ne_zero (htv0 P hP _ _ ha hb) ((hfr _).2 P (hcov P hP) ha).1))
    exact d5.congr_of_eventuallyEq (heq.trans (Eventually.of_forall fun Q => div_eq_mul_inv _ _))
  · intro P hP
    have ha : ex P ∈ ptsIn _ σ (L.B.U (a0 P)) := mem_pick hLB _
    have hb : ex (IndefiniteRowSideFullHecke.SiegelReframe.mulN (-1) P) ∈ ptsIn _ σ (L.B.U (b0 P)) := mem_pick hLB _
    exact div_ne_zero ((hfr _).2 _ (hcov _ (hcovN P hP)) hb).1
      (mul_ne_zero (htv0 P hP _ _ ha hb) ((hfr _).2 P (hcov P hP) ha).1)
  · intro l hl P hP
    have ha : ex P ∈ ptsIn _ σ (L.B.U (a0 P)) := mem_pick hLB _
    have hb : ex (IndefiniteRowSideFullHecke.SiegelReframe.mulN (-1) P) ∈ ptsIn _ σ (L.B.U (b0 P)) := mem_pick hLB _
    have hl' : (-1 : ℤ) • l = -l := by simp
    have hP' : transl τ l P ∈ cov B' g := ⟨hP.1, trivial⟩
    have hexP' : ex (transl τ l P) = ex P :=
      ((H.isUnifChart.2.2 P.1 hP.1.1).2.2 _ _).2 ⟨l, hl, rfl⟩
    have hmP' : IndefiniteRowSideFullHecke.SiegelReframe.mulN (-1) (transl τ l P) = transl τ (-l) (IndefiniteRowSideFullHecke.SiegelReframe.mulN (-1) P) := by
      rw [mulN_neg_one, mulN_neg_one]
      simp only [transl, per_neg, neg_add]
    have hexmP' : ex (IndefiniteRowSideFullHecke.SiegelReframe.mulN (-1) (transl τ l P)) = ex (IndefiniteRowSideFullHecke.SiegelReframe.mulN (-1) P) := by
      rw [hmP']
      exact ((H.isUnifChart.2.2 P.1 hP.1.1).2.2 _ _).2 ⟨-l, neg_mem hl, rfl⟩
    have ha' : ex (transl τ l P) ∈ ptsIn _ σ (L.B.U (a0 P)) := hexP' ▸ ha
    have hb' : ex (IndefiniteRowSideFullHecke.SiegelReframe.mulN (-1) (transl τ l P)) ∈ ptsIn _ σ (L.B.U (b0 P)) := hexmP' ▸ hb
    have e1 := LF _ hP' _ _ ha' hb'
    have f1 : fr (a0 P) P = j l P * fr (a0 P) (transl τ l P) :=
      ((hfr _).2 P (hcov P hP) ha).2.2.2 l hl
    have f2 : fr (b0 P) (IndefiniteRowSideFullHecke.SiegelReframe.mulN (-1) P) =
        j (-l) (IndefiniteRowSideFullHecke.SiegelReframe.mulN (-1) P) * fr (b0 P) (IndefiniteRowSideFullHecke.SiegelReframe.mulN (-1) (transl τ l P)) := by
      rw [hmP']
      exact ((hfr _).2 _ (hcov _ (hcovN P hP)) hb).2.2.2 (-l) (neg_mem hl)
    have n0 := ((hfr _).2 P (hcov P hP) ha).1
    have n0' := ((hfr _).2 _ (hcov _ (hcovN P hP)) hb).1
    have n1 : fr (a0 P) (transl τ l P) ≠ 0 := ((hfr _).2 _ (hcov _ hP') ha').1
    have n2 := htv0 P hP _ _ ha hb
    have n3 : j l P ≠ 0 := left_ne_zero_of_mul (f1 ▸ n0)
    have n4 : j (-l) (IndefiniteRowSideFullHecke.SiegelReframe.mulN (-1) P) ≠ 0 := left_ne_zero_of_mul (f2 ▸ n0')
    simp only [mulPullFactor]
    rw [hl', e1, hexP']
    show _ = j l P * (fr (b0 P) (IndefiniteRowSideFullHecke.SiegelReframe.mulN (-1) P) / (tv ![b0 P, a0 P] (ex P) * fr (a0 P) P))
    rw [f1, f2]
    field_simp
end Core

theorem exists_isBundleIso_neg : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k), IsRegSurf p → ∀ (P : PPAS S), IsArithVar (P.A.hom ≫ p) (P.g + 1) → ∀ (h : VMetric p (omega P.A) P.g) (L : HermLB (P.A.hom ≫ p)), IsTheta P L.B → ∀ (σ : k →+* ℂ) (c : AlgChart p σ 1) (τ : V 1 → Matrix (Fin P.g) (Fin P.g) ℂ) (ex : Pt (V 1) P.g → CxPts (P.A.hom ≫ p) σ) (j : Fl P.g → Pt (V 1) P.g → ℂ) (m : Pt (V 1) P.g → ℝ), IsPeriodChart h c τ ex → IsFramed L c.e.target τ ex j m → IsDatum c.e.target τ (stdLat P.g) j m → ∀ v ∈ c.e.target, ∃ B' ⊆ c.e.target, IsOpen B' ∧ v ∈ B' ∧ ∃ ι, GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.IsBundleIso B' τ (stdLat P.g) (GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.mulPullFactor (-1) j) j ι := by
  intro k _ S p _ P _ h L hθ σ c τ ex j m H hF _ v hv
  obtain ⟨-, -, hSym, -⟩ := hθ
  obtain ⟨U, hsU, t, ht⟩ := hSym ((c.e.symm v).1 (IsLocalRing.closedPoint ℂ))
  obtain ⟨φ, hφ⟩ := exists_isBundleIso_of_gen H L hF U t ht
  exact ⟨_, inter_subset_left, c.e.isOpen_inter_preimage_symm (isOpen_ptsIn U),
    ⟨hv, mem_ptsIn.2 hsU⟩, φ, hφ⟩

end GlobalTheory.SymChart
