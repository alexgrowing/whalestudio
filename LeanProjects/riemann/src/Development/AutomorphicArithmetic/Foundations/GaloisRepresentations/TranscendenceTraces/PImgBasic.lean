import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCochainEvEqOfNaturalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexDifferentialValuesStatement

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

namespace UpperTheory.Gal.TranscendenceTraces

private noncomputable def toOf {Z S : Scheme.{0}} {p : Z ⟶ S} (A : Sq p) : A.To (Sq.of p A.u) :=
  ⟨𝟙 _, pullback.lift A.v A.r A.pb.w, Category.id_comp _, pullback.lift_fst _ _ _,
    (pullback.lift_snd _ _ _).trans (Category.comp_id _).symm⟩

private noncomputable def ofTo {Z S V U : Scheme.{0}} (p : Z ⟶ S) (g : V ⟶ U) (u : U ⟶ S) :
    (Sq.of p (g ≫ u)).To (Sq.of p u) :=
  ⟨g, pullback.lift (pullback.fst p (g ≫ u)) (pullback.snd p (g ≫ u) ≫ g)
      (pullback.condition.trans (Category.assoc _ _ _).symm),
    rfl, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

private noncomputable def imgVal {Z S : Scheme.{0}} {p : Z ⟶ S} {R' R : Type} [CommRing R'] [CommRing R] {I : Cx R'} {J : Cx R}
    (τ : Fam p I J) {n : ℤ} (α : Cochain ((chains R').obj (sch.obj Z)) I n) (k : ℕ) (s : ℤ) (h : -(k : ℤ) + n = s)
    (U : Scheme.{0}) (u : U ⟶ S) : Sec (J.X s) U :=
  (τ.deg s).app (Sq.of p u) (ev α k s h (pullback p u) (pullback.fst p u))

end UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.imgBasic_of :
    ImgBasic := by
  intro Z S p R' R _ _ I J τ n
  have evZ := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R' (E := sch.obj Z) (I := I) (n := n)
  have ev_ext := (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj S) (I := J) (n := n)).2.2.1
  refine ⟨fun α => ?_, fun m hm α β hαβ => ?_⟩
  · have hnat : ∀ (k : ℕ) (s : ℤ) (h : -(k : ℤ) + n = s) (V U : Scheme) (g : V ⟶ U) (u : Sx (sch.obj S) k U),
        Sec.res g (imgVal τ α k s h U u) = imgVal τ α k s h V (Sx.res g u) := by
      intro k s h V U g u
      have e1 : Sec.res g ((τ.deg s).app (Sq.of p u) (ev α k s h (pullback p u) (pullback.fst p u))) =
          (τ.deg s).app (Sq.of p (g ≫ u)) (Sec.res (ofTo p g u).k (ev α k s h (pullback p u) (pullback.fst p u))) :=
        (τ.deg s).nat (ofTo p g u) _
      have e2 : Sec.res (ofTo p g u).k (ev α k s h (pullback p u) (pullback.fst p u)) =
          ev α k s h (pullback p (g ≫ u)) (pullback.fst p (g ≫ u)) := by
        refine (evZ.2.1 α k s h _ _ (ofTo p g u).k (pullback.fst p u)).trans ?_
        congr 1
        show (ofTo p g u).k ≫ pullback.fst p u = pullback.fst p (g ≫ u)
        exact pullback.lift_fst _ _ _
      exact e1.trans (congrArg _ e2)
    obtain ⟨β, hβ⟩ := GlobalTheory.T.exists_cochain_ev_eq_of_natural' R (E := sch.obj S) (I := J) (n := n)
      (fun k s h U u => imgVal τ α k s h U u) hnat
    have hIm : τ.IsImage α β := by
      intro k s h A
      have e1 : Sec.res (toOf A).g ((τ.deg s).app (Sq.of p A.u) (ev α k s h (pullback p A.u) (pullback.fst p A.u))) =
          (τ.deg s).app A (Sec.res (toOf A).k (ev α k s h (pullback p A.u) (pullback.fst p A.u))) :=
        (τ.deg s).nat (toOf A) _
      have e2 : Sec.res (toOf A).k (ev α k s h (pullback p A.u) (pullback.fst p A.u)) = ev α k s h A.V A.v := by
        refine (evZ.2.1 α k s h _ _ (toOf A).k (pullback.fst p A.u)).trans ?_
        congr 1
        show (toOf A).k ≫ pullback.fst p A.u = A.v
        exact pullback.lift_fst _ _ _
      exact (hβ k s h A.U A.u).trans (((res_id _).symm.trans e1).trans (congrArg _ e2))
    refine ⟨β, hIm, fun β' h' => ev_ext β' β (fun k s h U u => ?_)⟩
    exact (h' k s h (Sq.of p u)).trans (hIm k s h (Sq.of p u)).symm
  · intro k s h A
    cases k with
    | zero =>
      have hs : s = m := by simpa using h.symm
      subst hs
      have eβ := (GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values R (E := sch.obj S) (I := J) hm β A.U).1 A.u
      have eα := (GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values R' (E := sch.obj Z) (I := I) hm α A.V).1 A.v
      refine eβ.trans ?_
      refine Eq.trans ?_ (congrArg _ eα.symm)
      refine (congrArg _ (hαβ 0 n (by simp) A)).trans ?_
      exact τ.comm A n s _
    | succ q =>
      have eβ := (GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values R (E := sch.obj S) (I := J) hm β A.U).2 q (-((q + 1 : ℕ) : ℤ) + n) s rfl h A.u
      have eα := (GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values R' (E := sch.obj Z) (I := I) hm α A.V).2 q (-((q + 1 : ℕ) : ℤ) + n) s rfl h A.v
      refine eβ.trans ?_
      refine Eq.trans ?_ (congrArg _ eα.symm)
      rw [map_add]
      congr 1
      · exact (congrArg _ (hαβ _ _ rfl A)).trans (τ.comm A _ s _)
      · rw [Units.smul_def, Units.smul_def, map_zsmul, map_sum]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_zsmul]
        congr 1
        exact hαβ q s _ A
