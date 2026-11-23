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
import Development.AutomorphicArithmetic.CommutativeAlgebra.ProjBundleFormulaIffPglForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernClassTateTwistCocycleUniqueNaturalAddiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistUnitClassRootClassSpecStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupProductGradedCommStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupUnitAndPrimitiveRootClassesStatement
import Development.AutomorphicArithmetic.CommutativeAlgebra.FirstChernClassEqZeroOfIsTrivialized
import Development.AutomorphicArithmetic.CommutativeAlgebra.ProjectiveBundleFormulaRankOneOfHomotopyInvarian
import Development.AutomorphicArithmetic.CommutativeAlgebra.ProjectiveBundleFormulaRankTwo

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

private noncomputable def sg {N : ℕ} {A : Type} [CommRing A] (i : Fin N) (x : Um N A × Um 2 A) (h : IsUnit (x.1.1 i)) : Um 2 A :=
  Um.scale ![h.unit, 1] x.2

private theorem sg_map {N : ℕ} {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (i : Fin N) (x : Um N A × Um 2 A)
    (h : IsUnit (x.1.1 i)) (h' : IsUnit (((Um.map N f).obj x.1).1 i)) :
    sg i ((Um.map N f).obj x.1, (Um.map 2 f).obj x.2) h' = (Um.map 2 f).obj (sg i x h) := by
  apply Subtype.ext
  funext j
  fin_cases j <;> simp [sg, Um.scale, Um.map]

private theorem sg_act {N : ℕ} {A : Type} [CommRing A] (i : Fin N) (u : Aˣ × Aˣ) (x : Um N A × Um 2 A)
    (h : IsUnit (x.1.1 i)) (h' : IsUnit ((bAct u x).1.1 i)) :
    sg i (bAct u x) h' = Um.scale (fun _ => u.2) (sg i x h) := by
  apply Subtype.ext
  funext j
  fin_cases j
  · simp [sg, Um.scale, bAct]
    linear_combination ((u.2 : A) * (x.1.1 i) * (x.2.1 0)) * (Units.mul_inv u.1)
  · simp [sg, Um.scale, bAct]

private noncomputable def sig {N : ℕ} (i : Fin N) (Q : Pred (XC N)) (hQ : Q.Le (unitAt i)) :
    Act.Hom ((BC N).sub (Q.comap (pC N))) (XC 2) where
  d :=
    { app := fun A => TypeCat.ofHom fun x => sg (A := A) i x.1 (hQ A _ x.2)
      naturality := fun A B f => by
        ext x
        exact sg_map f.hom i x.1 (hQ A _ x.2) _ }
  g := (βC N).g
  eq A u x := sg_act (A := A) i u x.1 (hQ A _ x.2) _

private theorem etC_inv_of_hom {q : ℕ} {X Y : Spc} (f : X ⟶ Y) (h : GlobalTheory.EtC.Inv q Y) : GlobalTheory.EtC.Inv q X :=
  fun U hU => h U (hU.elim fun x => ⟨Sx.map f x⟩)

private theorem um_scale_scale_eq_of_mul_eq_one {A : Type} [CommRing A] (c d : Fin 2 → Aˣ) (h : ∀ j, c j * d j = 1)
    (w : Um 2 A) : Um.scale c (Um.scale d w) = w := by
  rw [← Um.scale_mul]
  simp only [h]
  exact Um.scale_one w

theorem UpperTheory.leraHirsch_chernPowers_on_unitChart :
    ∀ (q : ℕ) [NeZero q] (N : ℕ) (E : Spc) (i : Fin N) (Q : Pred (XC N)), Q.Le (unitAt i) → Inv q E →
        LHQ q E (pC N) (fun j : Fin 2 => 2 * (((j : ℕ) : ℤ))) (fun j : Fin 2 => ((j : ℕ) : ℤ)) (fun j => cpow q (c1 q (Sp.line E (chiB N))) j) Q := by
  intro q _ N E i Q hQ hE
  have hiso : IsIso (Sp.pair E ((pC N).sub Q) (sig i Q hQ)) := by
    apply UpperTheory.isIso_stackProductPair_of_bijective
    · intro A
      constructor
      · rintro ⟨⟨x1, x2⟩, hx⟩ ⟨⟨y1, y2⟩, hy⟩ e
        have e1 : x1 = y1 := congrArg (fun p => p.1.1) e
        have e2 : Um.scale ![(hQ A _ hx).unit, 1] x2 = Um.scale ![(hQ A _ hy).unit, 1] y2 :=
          congrArg Prod.snd e
        subst e1
        have e3 := congrArg (Um.scale ![(hQ A _ hx).unit⁻¹, 1]) e2
        rw [um_scale_scale_eq_of_mul_eq_one _ _ (by intro j; fin_cases j <;> simp <;> exact inv_mul_cancel _),
          um_scale_scale_eq_of_mul_eq_one _ _ (by intro j; fin_cases j <;> simp <;> exact inv_mul_cancel _)] at e3
        subst e3
        rfl
      · rintro ⟨⟨y1, hy1⟩, w⟩
        refine ⟨⟨(y1, Um.scale ![(hQ A _ hy1).unit⁻¹, 1] w), hy1⟩, ?_⟩
        refine Prod.ext rfl ?_
        change Um.scale ![(hQ A _ hy1).unit, 1] (Um.scale ![(hQ A _ hy1).unit⁻¹, 1] w) = w
        exact um_scale_scale_eq_of_mul_eq_one _ _ (by intro j; fin_cases j <;> simp) w
    · intro A
      constructor
      · intro g h e
        exact Prod.ext (congrArg Prod.fst e) (congrArg Prod.snd e)
      · intro p
        exact ⟨(p.1, p.2), rfl⟩
  have hS : GlobalTheory.EtC.Inv q (Sp E ((XC N).sub Q)) := etC_inv_of_hom (Sp.fst E _) hE
  have hP : Pbf q (Sp E ((XC N).sub Q)) 2 :=
    (UpperTheory.projBundleFormula_iff_pglForm q _ 2 hS).mp (UpperTheory.projectiveBundleFormula_rank_two q _ hS)
  have hX : GlobalTheory.EtC.Inv q (Sp (Sp E ((XC N).sub Q)) (XC 2)) := etC_inv_of_hom (Sp.fst _ _) hS
  have hB : GlobalTheory.EtC.Inv q (Sp E (BC N)) := etC_inv_of_hom (Sp.fst E _) hE
  have hcomm : Sp.pair E ((pC N).sub Q) (sig i Q hQ) ≫ Sp.fst (Sp E ((XC N).sub Q)) (XC 2) =
      Sp.map E ((pC N).sub Q) ≫ 𝟙 (Sp E ((XC N).sub Q)) := rfl
  have h1 := UpperTheory.lerayHirsch_of_iso_square q (Sp.fst (Sp E ((XC N).sub Q)) (XC 2)) (Sp.map E ((pC N).sub Q))
    (Sp.pair E ((pC N).sub Q) (sig i Q hQ)) (𝟙 _) hcomm _ _ _ hP
  have hline : Sp.pair E ((pC N).sub Q) (sig i Q hQ) ≫ Sp.line (Sp E ((XC N).sub Q)) (chiX 2) =
      Sp.map E (incl (Q.comap (pC N))) ≫ Sp.line E (chiB N) := rfl
  have key : ∀ j : Fin 2,
      (pull (ZMod q) (Sp.pair E ((pC N).sub Q) (sig i Q hQ)) (tw q ((j : ℕ) : ℤ)) (2 * ((j : ℕ) : ℤ)))
        (cpow q (c1 q (Sp.line (Sp E ((XC N).sub Q)) (chiX 2))) (j : ℕ)) =
      (pull (ZMod q) (Sp.map E (incl (Q.comap (pC N)))) (tw q ((j : ℕ) : ℤ)) (2 * ((j : ℕ) : ℤ)))
        (cpow q (c1 q (Sp.line E (chiB N))) (j : ℕ)) := by
    intro j
    rw [UpperTheory.pull_cupPow_eq_cupPow_pull q _ _ _ hX, UpperTheory.pull_cupPow_eq_cupPow_pull q _ _ _ hB, (GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive q).2.1 _ _ hX,
      (GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive q).2.1 _ _ hB, hline]
  show LH q (Sp.map E ((pC N).sub Q)) _ _ _
  convert h1 using 2
  exact (key _).symm
