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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceBasicPropertiesStatement

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

namespace UpperTheory.BlowEqv

private theorem s_unit {N : ℕ} {A : Type} [CommRing A] (x : Um N A × Um 2 A)
    (h : Ideal.span ((Um.join x).1 '' Set.range Fin.castSucc) = ⊤) : IsUnit (x.2.1 0) := by
  have key : ∀ i : Fin N, (Um.join x).1 (Fin.castSucc i) = x.2.1 0 * x.1.1 i := by
    intro i
    simp [Um.join, Fin.snoc_castSucc]
  rw [← Ideal.span_singleton_eq_top]
  refine eq_top_iff.2 (le_trans (le_of_eq h.symm) ?_)
  rw [Ideal.span_le]
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  rw [key]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

private def vec1 {A : Type} [CommRing A] (s : A) (h : IsUnit s) : Um 1 A :=
  ⟨fun _ => s, by
    rw [Set.range_const]
    exact Ideal.span_singleton_eq_top.2 h⟩

private theorem unimodularRow_one_isUnit {A : Type} [CommRing A] (c : Um 1 A) : IsUnit (c.1 0) := by
  have h := c.2
  rw [Set.range_unique] at h
  exact Ideal.span_singleton_eq_top.1 h

private theorem join_inj {N : ℕ} {A : Type} [CommRing A] {x y : Um N A × Um 2 A} (hs : x.2.1 0 = y.2.1 0)
    (hu : IsUnit (x.2.1 0)) (h : Um.join x = Um.join y) : x = y := by
  have h1 := congrArg Subtype.val h
  have hl : x.2.1 1 = y.2.1 1 := by
    have := congrFun h1 (Fin.last N)
    simpa [Um.join] using this
  have hi : ∀ i, x.1.1 i = y.1.1 i := by
    intro i
    have := congrFun h1 (Fin.castSucc i)
    simp only [Um.join, Fin.snoc_castSucc] at this
    rw [← hs] at this
    exact hu.mul_left_cancel this
  refine Prod.ext (Subtype.ext (funext hi)) (Subtype.ext (funext fun j => ?_))
  refine Fin.cases hs (fun k => ?_) j
  rw [Fin.fin_one_eq_zero k]
  exact hl

private theorem join_surj {N : ℕ} {A : Type} [CommRing A] (w : Um (N + 1) A)
    (hw : Ideal.span (w.1 '' Set.range Fin.castSucc) = ⊤) (u : Aˣ) :
    ∃ x : Um N A × Um 2 A, x.2.1 0 = u ∧ Um.join x = w := by
  refine ⟨(⟨fun i => (↑u⁻¹ : A) * w.1 (Fin.castSucc i), ?_⟩, ⟨![(u : A), w.1 (Fin.last N)], ?_⟩), rfl, ?_⟩
  · refine eq_top_iff.2 (le_trans (le_of_eq hw.symm) ?_)
    rw [Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    have e : w.1 (Fin.castSucc i) = (u : A) * ((↑u⁻¹ : A) * w.1 (Fin.castSucc i)) := by
      simp
    rw [e]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩) u.isUnit
  · apply Subtype.ext
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [Um.join]
    · simp [Um.join, Fin.snoc_castSucc]

private def ratioG : gm2F ⟶ gmF where
  app A := GrpCat.ofHom
    { toFun := fun g => (show Aˣ × Aˣ from g).2 * (show Aˣ × Aˣ from g).1⁻¹
      map_one' := by
        change (1 : Aˣ) * (1 : Aˣ)⁻¹ = 1
        simp
      map_mul' := fun g h => by
        change ((show Aˣ × Aˣ from g).2 * (show Aˣ × Aˣ from h).2) * ((show Aˣ × Aˣ from g).1 * (show Aˣ × Aˣ from h).1)⁻¹ =
          ((show Aˣ × Aˣ from g).2 * (show Aˣ × Aˣ from g).1⁻¹) * ((show Aˣ × Aˣ from h).2 * (show Aˣ × Aˣ from h).1⁻¹)
        rw [mul_inv]
        exact mul_mul_mul_comm _ _ _ _ }
  naturality A B f := by
    refine GrpCat.hom_ext (MonoidHom.ext fun g => ?_)
    change (Units.map f.hom.toMonoidHom (show Aˣ × Aˣ from g).2) * (Units.map f.hom.toMonoidHom (show Aˣ × Aˣ from g).1)⁻¹ =
      Units.map f.hom.toMonoidHom ((show Aˣ × Aˣ from g).2 * (show Aˣ × Aˣ from g).1⁻¹)
    rw [map_mul, map_inv]

private def sig (N : ℕ) (Q : Pred (XC (N + 1))) (hQ : Q.Le (Q2 N)) :
    Act.Hom ((BC N).sub (Q.comap (βC N))) (XC 1) where
  d :=
    { app := fun A => TypeCat.ofHom fun x =>
        vec1 ((show Um N A × Um 2 A from x.1).2.1 0) (s_unit _ (hQ A _ x.2))
      naturality := fun A B f => by
        ext x
        exact Subtype.ext rfl }
  g := ratioG
  eq A u x := Subtype.ext (funext fun _ => rfl)

private theorem pts_bij (N : ℕ) (Q : Pred (XC (N + 1))) (hQ : Q.Le (Q2 N)) (A : CommRingCat.{0}) :
    Function.Bijective (fun x : ((BC N).sub (Q.comap (βC N))).D.obj A =>
      ((((βC N).sub Q).d.app A x, (sig N Q hQ).d.app A x) :
        ((XC (N + 1)).sub Q).D.obj A × (XC 1).D.obj A)) := by
  constructor
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have e1 : Um.join x = Um.join y := congrArg Subtype.val h1
    have e2 : x.2.1 0 = y.2.1 0 := congrArg (fun c : Um 1 A => c.1 0) h2
    exact Subtype.ext (join_inj e2 (s_unit x (hQ A _ hx)) e1)
  · rintro ⟨⟨w, hw⟩, c⟩
    obtain ⟨x, hx0, hxw⟩ := join_surj w (hQ A w hw) (unimodularRow_one_isUnit c).unit
    refine ⟨⟨x, ?_⟩, ?_⟩
    · show Q.P A (Um.join x)
      rw [hxw]
      exact hw
    · refine Prod.ext (Subtype.ext hxw) (Subtype.ext (funext fun i => ?_))
      obtain rfl : i = 0 := Subsingleton.elim _ _
      exact hx0.trans (unimodularRow_one_isUnit c).unit_spec

private theorem mul_ringHom_units_ratio {G : Type} [CommGroup G] (m c : G) : m * (m * c⁻¹)⁻¹ = c := by
  rw [mul_inv_rev, inv_inv, mul_comm c, mul_inv_cancel_left]

private theorem grp_bij (N : ℕ) (Q : Pred (XC (N + 1))) (hQ : Q.Le (Q2 N)) (A : CommRingCat.{0}) :
    Function.Bijective (fun g : ((BC N).sub (Q.comap (βC N))).G.obj A =>
      ((((βC N).sub Q).g.app A g, (sig N Q hQ).g.app A g) :
        ((XC (N + 1)).sub Q).G.obj A × (XC 1).G.obj A)) := by
  constructor
  · rintro ⟨a, b⟩ ⟨a', b'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    change b = b' at h1
    change b * a⁻¹ = b' * a'⁻¹ at h2
    subst h1
    have e : a⁻¹ = a'⁻¹ := mul_left_cancel h2
    exact Prod.ext (inv_injective e) rfl
  · rintro ⟨m, c⟩
    let m' : (↑A : Type)ˣ := m
    let c' : (↑A : Type)ˣ := c
    refine ⟨(show (↑A : Type)ˣ × (↑A : Type)ˣ from (m' * c'⁻¹, m')), ?_⟩
    refine Prod.ext rfl ?_
    exact mul_ringHom_units_ratio m' c'

private theorem lh_norm {q : ℕ} {X E : Spc} (π : X ⟶ E) {d e : Fin 1 → ℤ} (c : ∀ j, Ht q X (d j) (e j))
    (hd : ∀ j, d j = 0) (he : ∀ j, e j = 0) (hc : ∀ j, c j = (one q X).cast (hd j).symm (he j).symm)
    (h : LH q π d e c) : LH q π (fun _ : Fin 1 => (0 : ℤ)) (fun _ : Fin 1 => (0 : ℤ)) (fun _ => one q X) := by
  obtain rfl : d = fun _ => 0 := funext hd
  obtain rfl : e = fun _ => 0 := funext he
  have hc' : c = fun _ => one q X := funext fun j => by
    rw [hc j]
    rfl
  subst hc'
  exact h

end UpperTheory.BlowEqv

open UpperTheory.BlowEqv in
theorem UpperTheory.eqv_twist_blowupRestriction :
    ∀ (q : ℕ) [NeZero q] (N : ℕ) (E : Spc) (Q : Pred (XC (N + 1))) (i : ℤ), Q.Le (Q2 N) → Inv q E →
        Eqv _ (Sp.map E ((βC N).sub Q)) (tw q i) := by
  intro q _ N E Q i hQ hE
  have invS : ∀ {X : Spc} (Z : Spc), Inv q X → Inv q (mulS X Z) := fun Z hX U ⟨x⟩ => hX U ⟨x.1⟩
  have hF : Inv q (Sp E ((XC (N + 1)).sub Q)) := invS _ hE
  have hX : Inv q (Sp (Sp E ((XC (N + 1)).sub Q)) (XC 1)) := invS _ hF
  have hP : Pbf q (Sp E ((XC (N + 1)).sub Q)) 1 := (UpperTheory.projBundleFormula_iff_pglForm q _ 1 hF).1 (UpperTheory.projectiveBundleFormula_rank_one_of_homotopyInvariant q _ hF)
  unfold Pbf at hP
  have hL := lh_norm _ _ (fun j => by obtain rfl : j = 0 := Subsingleton.elim _ _; simp)
    (fun j => by obtain rfl : j = 0 := Subsingleton.elim _ _; simp)
    (fun j => by obtain rfl : j = 0 := Subsingleton.elim _ _; exact cpow_zero q _) hP
  have hfst : ∀ i, Eqv (ZMod q) (Sp.fst (Sp E ((XC (N + 1)).sub Q)) (XC 1)) (tw q i) :=
    (UpperTheory.lerayHirsch_one_iff_twist_equiv q _ hX).1 hL
  have hiso := UpperTheory.isIso_stackProductPair_of_bijective E ((βC N).sub Q) (sig N Q hQ) (pts_bij N Q hQ) (grp_bij N Q hQ)
  have hcomp : Sp.pair E ((βC N).sub Q) (sig N Q hQ) ≫ Sp.fst _ (XC 1) = Sp.map E ((βC N).sub Q) := by
    rfl
  rw [← hcomp]
  obtain ⟨hiso', hcmp, -, -⟩ := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties (ZMod q) (tw q i)
  exact (hcmp _ _ _ _ _).1 (hiso' _ _ _ hiso) (hfst i)
