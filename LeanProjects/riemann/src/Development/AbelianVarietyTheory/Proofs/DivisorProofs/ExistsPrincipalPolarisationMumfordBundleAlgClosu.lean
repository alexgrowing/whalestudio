import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullGeneratorFactorPairingGenericMumfordBundle
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RelAmpleOfAmpleOnClosedSubschemeLocalBase
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSquareUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.PrincipalBaseChange

variable {S S' : Scheme.{0}} {A : Over S} [GrpObj A] {f : S' ⟶ S}

theorem lift_comp_sq (w : pullback.fst A.hom f ≫ A.hom = ((Over.pullback f).obj A).hom ≫ f)
    {X : Over S'} (a b : X ⟶ (Over.pullback f).obj A) :
    (lift a b).left ≫ (lift (pushPt w (fst ((Over.pullback f).obj A) ((Over.pullback f).obj A)))
        (pushPt w (snd ((Over.pullback f).obj A) ((Over.pullback f).obj A)))).left =
      (lift (pushPt w a) (pushPt w b)).left := by
  apply pullback.hom_ext
  · change _ ≫ _ ≫ (fst A A).left = _ ≫ (fst A A).left
    rw [← Over.comp_left, lift_fst, ← Over.comp_left, lift_fst]
    show (lift a b).left ≫ ((fst ((Over.pullback f).obj A) ((Over.pullback f).obj A)).left ≫ pullback.fst A.hom f) = a.left ≫ pullback.fst A.hom f
    rw [← Category.assoc, ← Over.comp_left, lift_fst]
  · change _ ≫ _ ≫ (snd A A).left = _ ≫ (snd A A).left
    rw [← Over.comp_left, lift_snd, ← Over.comp_left, lift_snd]
    show (lift a b).left ≫ ((snd ((Over.pullback f).obj A) ((Over.pullback f).obj A)).left ≫ pullback.fst A.hom f) = b.left ≫ pullback.fst A.hom f
    rw [← Category.assoc, ← Over.comp_left, lift_snd]

theorem lift_comp_sq' (w : pullback.fst A.hom f ≫ A.hom = ((Over.pullback f).obj A).hom ≫ f)
    {X : Over S'} {Y : Over S} (U : Over.mk (X.hom ≫ f) ⟶ Y) (a b : X ⟶ (Over.pullback f).obj A) (c d : Y ⟶ A)
    (ha : pushPt w a = U ≫ c) (hb : pushPt w b = U ≫ d) :
    (lift a b).left ≫ (lift (pushPt w (fst ((Over.pullback f).obj A) ((Over.pullback f).obj A)))
        (pushPt w (snd ((Over.pullback f).obj A) ((Over.pullback f).obj A)))).left =
      U.left ≫ (lift c d).left := by
  rw [lift_comp_sq, ← Over.comp_left, comp_lift, ha, hb]

end GlobalTheory.PrincipalBaseChange

namespace GlobalTheory.PrincipalBaseChange

theorem exists_principal_algClosure : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ PP : LB (G2 A).left, PP.IsLB → (∃ u : LB.Gen (LB.LinComb PP (K := Fin 2) ![(lift (snd A A) (fst A A) : G2 A ⟶ G2 A).left, 𝟙 (G2 A).left] ![1, -1]), u.IsGen) → (∃ u : LB.Gen (LB.LinComb PP (K := Fin 3) ![(lift (fst A (A ⊗ A) * (snd A (A ⊗ A) ≫ fst A A)) (snd A (A ⊗ A) ≫ snd A A) : A ⊗ (A ⊗ A) ⟶ G2 A).left, (lift (fst A (A ⊗ A)) (snd A (A ⊗ A) ≫ snd A A) : A ⊗ (A ⊗ A) ⟶ G2 A).left, (snd A (A ⊗ A) : A ⊗ (A ⊗ A) ⟶ G2 A).left] ![1, -1, -1]), u.IsGen) → Out.RelAmple A (PP.pull (lift (𝟙 A) (𝟙 A) : A ⟶ G2 A).left) → (∀ (T : Over (Sp K)) (x : T ⟶ A), (∃ t : LB.Gen (PP.pull (lift (snd A T ≫ x) (fst A T) : A ⊗ T ⟶ G2 A).left), t.IsGen) → x = toUnit T ≫ η[A]) → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] (κ : (G2 ((Over.pullback (spMap (algebraMap K Ω))).obj A)).left ⟶ (G2 A).left), Geo.Tor.IsSquare (pullback.fst A.hom (spMap (algebraMap K Ω))) κ → ∃ L : LB ((Over.pullback (spMap (algebraMap K Ω))).obj A).left, L.IsLB ∧ Out.Sym ((Over.pullback (spMap (algebraMap K Ω))).obj A) L ∧ LBIso (abelian₂ ((Over.pullback (spMap (algebraMap K Ω))).obj A) L) (PP.pull κ) ∧ Out.RelAmple ((Over.pullback (spMap (algebraMap K Ω))).obj A) L ∧ Out.KTriv ((Over.pullback (spMap (algebraMap K Ω))).obj A) L := by
  intro K _ _ A _ _ hA PP hP hs hb ha hk Ω _ _ _ κ hκ
  set f := spMap (algebraMap K Ω) with hf
  set AΩ := (Over.pullback f).obj A with hAΩ
  have h := isGrpPullback_pullback A f
  have w := h.1.w
  obtain rfl := GlobalTheory.LamPull.isSquare_unique hκ (GlobalTheory.LamPull.exists_isSquare w)
  have hAΩab : IsAbelianScheme AΩ := GlobalTheory.isAbelianScheme_pullback_obj f A hA
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  have hP' := pull_isLB hP (lift (pushPt w (fst AΩ AΩ)) (pushPt w (snd AΩ AΩ))).left
  have pmul : ∀ {T : Over (Sp Ω)} (x y : T ⟶ AΩ), pushPt w (x * y) = pushPt w x * pushPt w y :=
    fun x y => map_mul (pushHom h _) x y
  refine GlobalTheory.PrincipalOfPairing.exists_principal Ω AΩ hAΩab _ hP' ?_ ?_ ?_ ?_
  · obtain ⟨u, hu⟩ := hs
    refine gen_chartPull (chartPullLinComb PP _ _ _ _ (lift (pushPt w (fst AΩ AΩ)) (pushPt w (snd AΩ AΩ))).left fun k => ?_) u hu
    fin_cases k
    · exact lift_comp_sq' w _ (snd AΩ AΩ) (fst AΩ AΩ) (snd A A) (fst A A) (lift_snd _ _).symm (lift_fst _ _).symm
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · obtain ⟨u, hu⟩ := hb
    let U3 : Over.mk ((AΩ ⊗ (AΩ ⊗ AΩ)).hom ≫ f) ⟶ A ⊗ (A ⊗ A) :=
      lift (pushPt w (fst AΩ (AΩ ⊗ AΩ)))
        (lift (pushPt w (snd AΩ (AΩ ⊗ AΩ) ≫ fst AΩ AΩ)) (pushPt w (snd AΩ (AΩ ⊗ AΩ) ≫ snd AΩ AΩ)))
    refine gen_chartPull (chartPullLinComb PP _ _ _ _ U3.left fun k => ?_) u hu
    fin_cases k
    · refine lift_comp_sq' w U3 _ _ _ _ ?_ (by simp [U3])
      rw [comp_mul, pmul]
      simp [U3]
    · exact lift_comp_sq' w U3 _ _ _ _ (by simp [U3]) (by simp [U3])
    · have e1 : snd AΩ (AΩ ⊗ AΩ) = lift (snd AΩ (AΩ ⊗ AΩ) ≫ fst AΩ AΩ) (snd AΩ (AΩ ⊗ AΩ) ≫ snd AΩ AΩ) := by simp
      have e2 : snd A (A ⊗ A) = lift (snd A (A ⊗ A) ≫ fst A A) (snd A (A ⊗ A) ≫ snd A A) := by simp
      show (snd AΩ (AΩ ⊗ AΩ)).left ≫ _ = U3.left ≫ (snd A (A ⊗ A)).left
      rw [e1, e2]
      exact lift_comp_sq' w U3 _ _ _ _ (by simp [U3]) (by simp [U3])
  · have e : (lift (𝟙 AΩ) (𝟙 AΩ)).left ≫ (lift (pushPt w (fst AΩ AΩ)) (pushPt w (snd AΩ AΩ))).left =
        pullback.fst A.hom f ≫ (lift (𝟙 A) (𝟙 A)).left := by
      rw [lift_comp_sq' w (pushPt w (𝟙 AΩ)) _ _ (𝟙 A) (𝟙 A) (by simp) (by simp)]
      simp [pushPt]
    refine GlobalTheory.AmpleLocalBase.relAmple_baseChange h.1 (pull_isLB hP _) (pull_isLB hP' _) ?_ ha
    refine LBIso.trans (pull_isLB hP' _) (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _)
      (GlobalTheory.Mum.lbIso_pull_pull_comp hP _ _) ?_
    rw [e]
    exact (GlobalTheory.Mum.lbIso_pull_pull_comp hP _ _).symm
  · intro T x ⟨t, ht⟩
    let T₀ : Over (Sp K) := Over.mk (T.hom ≫ f)
    let x₀ : T₀ ⟶ A := pushPt w x
    let sT : Over.mk ((AΩ ⊗ T).hom ≫ f) ⟶ T₀ := Over.homMk (snd AΩ T).left (by
      show (snd AΩ T).left ≫ T.hom ≫ f = (AΩ ⊗ T).hom ≫ f
      rw [← Category.assoc, Over.w (snd AΩ T)])
    let V0 : Over.mk ((AΩ ⊗ T).hom ≫ f) ⟶ A ⊗ T₀ := lift (pushPt w (fst AΩ T)) sT
    have e : (lift (snd AΩ T ≫ x) (fst AΩ T)).left ≫ (lift (pushPt w (fst AΩ AΩ)) (pushPt w (snd AΩ AΩ))).left =
        V0.left ≫ (lift (snd A T₀ ≫ x₀) (fst A T₀)).left := by
      refine lift_comp_sq' w V0 _ _ _ _ ?_ (by simp [V0])
      rw [lift_snd_assoc]
      exact Over.OverMorphism.ext (by simp [pushPt, sT, x₀])
    have hV : IsIso V0.left := by
      have e3 : V0.left = (pullbackLeftPullbackSndIso A.hom f T.hom).hom := by
        apply pullback.hom_ext
        · change V0.left ≫ pullback.fst A.hom (T.hom ≫ f) =
            (pullbackLeftPullbackSndIso A.hom f T.hom).hom ≫ pullback.fst A.hom (T.hom ≫ f)
          rw [pullbackLeftPullbackSndIso_hom_fst]
          change V0.left ≫ (fst A T₀).left = _
          rw [← Over.comp_left, lift_fst]
          rfl
        · change V0.left ≫ pullback.snd A.hom (T.hom ≫ f) =
            (pullbackLeftPullbackSndIso A.hom f T.hom).hom ≫ pullback.snd A.hom (T.hom ≫ f)
          rw [pullbackLeftPullbackSndIso_hom_snd]
          change V0.left ≫ (snd A T₀).left = _
          rw [← Over.comp_left, lift_snd]
          rfl
      rw [e3]
      infer_instance
    have g1 := (exists_gen_pull_pull_iff hP _ _).1 ⟨t, ht⟩
    rw [e] at g1
    obtain ⟨t1, ht1⟩ := g1
    obtain ⟨t2, ht2⟩ := gen_chartPull (chartPullPull (PP.pull (V0.left ≫ (lift (snd A T₀ ≫ x₀) (fst A T₀)).left))
      (inv V0.left)) t1 ht1
    have g3 := (exists_gen_pull_pull_iff hP _ (inv V0.left)).1 ⟨t2, ht2⟩
    rw [IsIso.inv_hom_id_assoc] at g3
    have hx0 : x₀ = toUnit T₀ ≫ η[A] := hk T₀ x₀ g3
    have e1 : pushPt w (toUnit T ≫ η[AΩ]) = toUnit T₀ ≫ η[A] := by
      rw [← Hom.one_def, ← Hom.one_def]
      exact map_one (pushHom h T)
    apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · change x₀.left = (pushPt w (toUnit T ≫ η[AΩ])).left
      rw [hx0, e1]
    · rw [Over.w x, Over.w (toUnit T ≫ η[AΩ])]

end GlobalTheory.PrincipalBaseChange
