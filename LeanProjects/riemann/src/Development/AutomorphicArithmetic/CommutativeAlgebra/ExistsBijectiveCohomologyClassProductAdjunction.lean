import Development.AutomorphicArithmetic.CommutativeAlgebra.BconeDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCochainEvEqOfNaturalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexDifferentialValuesStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

namespace UpperTheory.Adj

section Gen
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C]

private theorem classes {K L K' L' : CochainComplex C ℤ}
    (e : ∀ n, Cochain K L n ≃+ Cochain K' L' n)
    (he : ∀ (n m : ℤ) (_ : n + 1 = m) (α : Cochain K L n), δ n m (e n α) = e m (δ n m α)) (n : ℤ) :
    ∃ Θ : CohomologyClass K L n →+ CohomologyClass K' L' n, Function.Bijective Θ ∧
      ∀ γ : Cocycle K L n, ∃ β : Cocycle K' L' n,
        Θ (CohomologyClass.mk γ) = CohomologyClass.mk β ∧ β.1 = e n γ.1 := by
  have hc : ∀ γ : Cocycle K L n, δ n (n + 1) (e n γ.1) = 0 := fun γ => by
    rw [he n _ rfl, (Cocycle.mem_iff n (n + 1) rfl γ.1).1 γ.2, map_zero]
  let f : Cocycle K L n → Cocycle K' L' n := fun γ => Cocycle.mk (e n γ.1) (n + 1) rfl (hc γ)
  let Θ : CohomologyClass K L n →+ CohomologyClass K' L' n :=
    CohomologyClass.descAddMonoidHom
      (AddMonoidHom.mk' (fun γ => CohomologyClass.mk (f γ)) (fun a b => by
        rw [← CohomologyClass.mk_add]
        congr 1
        exact Cocycle.ext (map_add (e n) a.1 b.1)))
      (by
        rintro ⟨b, hb⟩ ⟨n', hn', β, rfl⟩
        change CohomologyClass.mk _ = 0
        rw [CohomologyClass.mk_eq_zero_iff]
        exact ⟨n', hn', e n' β, he n' n hn' β⟩)
  have hΘ : ∀ γ, Θ (CohomologyClass.mk γ) = CohomologyClass.mk (f γ) := fun γ =>
    CohomologyClass.descAddMonoidHom_cohomologyClass _ _ γ
  refine ⟨Θ, ⟨?_, ?_⟩, fun γ => ⟨f γ, hΘ γ, rfl⟩⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨γ, rfl⟩ := x.mk_surjective
    rw [hΘ, CohomologyClass.mk_eq_zero_iff] at hx
    obtain ⟨n', hn', β, hβ⟩ := hx
    rw [CohomologyClass.mk_eq_zero_iff]
    refine ⟨n', hn', (e n').symm β, (e n).injective ?_⟩
    rw [← he n' n hn', AddEquiv.apply_symm_apply]
    exact hβ
  · intro x
    obtain ⟨β, rfl⟩ := x.mk_surjective
    have h0 : δ n (n + 1) ((e n).symm β.1) = 0 := by
      apply (e (n + 1)).injective
      rw [← he n _ rfl, AddEquiv.apply_symm_apply, (Cocycle.mem_iff n (n + 1) rfl β.1).1 β.2, map_zero]
    refine ⟨CohomologyClass.mk (Cocycle.mk _ (n + 1) rfl h0), ?_⟩
    rw [hΘ]
    congr 1
    exact Cocycle.ext (AddEquiv.apply_symm_apply (e n) β.1)

end Gen

private theorem map_res {A B : Spc} (f : A ⟶ B) {p : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx A p U) :
    (x.res g).map f = (x.map f).res g :=
  FunctorToTypes.naturality (f.app (op (SimplexCategory.mk p))) g.op x

private theorem map_face {A B : Spc} (f : A ⟶ B) {p : ℕ} {U : Scheme.{0}} (x : Sx A (p + 1) U) (i : Fin (p + 2)) :
    (x.face i).map f = (x.map f).face i :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (f.naturality (SimplexCategory.δ i).op) (op U)) x

private def evF (p : ℕ) (T : Scheme.{0}) : Spc ⥤ Type :=
  (evaluation SimplexCategoryᵒᵖ PSh).obj (op (SimplexCategory.mk p)) ⋙ (evaluation Scheme.{0}ᵒᵖ Type).obj (op T)

private theorem pair_bij (A B : Spc) (p : ℕ) (T : Scheme.{0}) :
    Function.Bijective (fun y : Sx (A ⨯ B) p T => ((y.map prod.fst : Sx A p T), (y.map prod.snd : Sx B p T))) := by
  haveI : PreservesLimit (pair A B) (evF p T) := by unfold evF; infer_instance
  let e := PreservesLimitPair.iso (evF p T) A B ≪≫ Types.binaryProductIso _ _
  have h : (fun y : Sx (A ⨯ B) p T => ((y.map prod.fst : Sx A p T), (y.map prod.snd : Sx B p T))) = e.hom := by
    funext y
    refine Prod.ext ?_ ?_
    · exact (ConcreteCategory.congr_hom (prodComparison_fst (evF p T) A B) y).symm
    · exact (ConcreteCategory.congr_hom (prodComparison_snd (evF p T) A B) y).symm
  rw [h]
  exact (isIso_iff_bijective _).1 inferInstance

end UpperTheory.Adj

noncomputable section
namespace UpperTheory.Adj

variable {R : Type} [CommRing R] {W : Scheme.{0}} {E : Spc}

private def fstW {p : ℕ} {T : Scheme.{0}} (y : Sx (sch.obj W ⨯ E) p T) : T ⟶ W := y.map prod.fst

private def sndE {p : ℕ} {T : Scheme.{0}} (y : Sx (sch.obj W ⨯ E) p T) : Sx E p T := y.map prod.snd

private theorem pair_ext {p : ℕ} {T : Scheme.{0}} {y y' : Sx (sch.obj W ⨯ E) p T}
    (h1 : fstW y = fstW y') (h2 : sndE y = sndE y') : y = y' :=
  (pair_bij (sch.obj W) E p T).1 (Prod.ext h1 h2)

private theorem exists_fst_eq_and_snd_eq {p : ℕ} {T : Scheme.{0}} (g : T ⟶ W) (x : Sx E p T) :
    ∃ y : Sx (sch.obj W ⨯ E) p T, fstW y = g ∧ sndE y = x := by
  obtain ⟨y, hy⟩ := (pair_bij (sch.obj W) E p T).2 (show Sx (sch.obj W) p T × Sx E p T from (g, x))
  exact ⟨y, congrArg Prod.fst hy, congrArg Prod.snd hy⟩

private def mkP {p : ℕ} {T : Scheme.{0}} (g : T ⟶ W) (x : Sx E p T) : Sx (sch.obj W ⨯ E) p T :=
  (exists_fst_eq_and_snd_eq g x).choose

private theorem fst_mkP {p : ℕ} {T : Scheme.{0}} (g : T ⟶ W) (x : Sx E p T) : fstW (mkP g x) = g :=
  (exists_fst_eq_and_snd_eq g x).choose_spec.1

private theorem snd_mkP {p : ℕ} {T : Scheme.{0}} (g : T ⟶ W) (x : Sx E p T) : sndE (mkP g x) = x :=
  (exists_fst_eq_and_snd_eq g x).choose_spec.2

private theorem fst_res {p : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (y : Sx (sch.obj W ⨯ E) p U) :
    fstW (y.res g) = g ≫ fstW y := map_res prod.fst g y

private theorem snd_res {p : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (y : Sx (sch.obj W ⨯ E) p U) :
    sndE (y.res g) = (sndE y).res g := map_res prod.snd g y

private theorem fst_face {p : ℕ} {U : Scheme.{0}} (y : Sx (sch.obj W ⨯ E) (p + 1) U) (i : Fin (p + 2)) :
    fstW (y.face i) = fstW y := map_face prod.fst y i

private theorem snd_face {p : ℕ} {U : Scheme.{0}} (y : Sx (sch.obj W ⨯ E) (p + 1) U) (i : Fin (p + 2)) :
    sndE (y.face i) = (sndE y).face i := map_face prod.snd y i

private theorem sx_res_res {A : Spc} {p : ℕ} {X Y Z : Scheme.{0}} (a : X ⟶ Y) (b : Y ⟶ Z) (x : Sx A p Z) :
    (x.res b).res a = x.res (a ≫ b) := by
  simp [Sx.res]

private theorem sx_res_id {A : Spc} {p : ℕ} {X : Scheme.{0}} (x : Sx A p X) : x.res (𝟙 X) = x := by
  simp [Sx.res]

private theorem res_res {F : Shv R} {X Y Z : Scheme.{0}} (a : X ⟶ Y) (b : Y ⟶ Z) (x : Sec F Z) :
    Sec.res a (Sec.res b x) = Sec.res (a ≫ b) x := by
  rw [Sec.res, Sec.res, Sec.res, op_comp, F.obj.map_comp]
  rfl

private theorem res_id {F : Shv R} {X : Scheme.{0}} (x : Sec F X) : Sec.res (𝟙 X) x = x := by
  rw [Sec.res, op_id, F.obj.map_id]
  rfl

private theorem map_sec_res {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec F U) :
    Sec.map φ (Sec.res g a) = Sec.res g (Sec.map φ a) := by
  have := φ.hom.naturality g.op
  exact congrArg (fun f => f.hom a) this

private def upL (I : Cx R) {T : Scheme.{0}} (g : T ⟶ W) (s : ℤ) : Sec ((Bc W I).X s) T →+ Sec (I.X s) T where
  toFun a := Sec.res (prod.lift g (𝟙 T)) (show Sec (I.X s) (W ⨯ T) from a)
  map_zero' := map_zero ((I.X s).obj.map (prod.lift g (𝟙 T)).op).hom
  map_add' a b := map_add ((I.X s).obj.map (prod.lift g (𝟙 T)).op).hom a b

private theorem upL_nat (I : Cx R) {V U : Scheme.{0}} (g : V ⟶ U) (h : U ⟶ W) (s : ℤ) (a : Sec ((Bc W I).X s) U) :
    Sec.res g (upL I h s a) = upL I (g ≫ h) s (Sec.res g a) := by
  change Sec.res g (Sec.res (prod.lift h (𝟙 U)) (show Sec (I.X s) (W ⨯ U) from a)) =
    Sec.res (prod.lift (g ≫ h) (𝟙 V)) (Sec.res (Limits.prod.map (𝟙 W) g) (show Sec (I.X s) (W ⨯ U) from a))
  have e : g ≫ prod.lift h (𝟙 U) = prod.lift (g ≫ h) (𝟙 V) ≫ Limits.prod.map (𝟙 W) g := by
    apply Limits.prod.hom_ext <;> simp
  rw [res_res, res_res, e]

private theorem upL_res (I : Cx R) {T : Scheme.{0}} (s : ℤ) (a : Sec ((Bc W I).X s) T) :
    upL I (prod.fst : W ⨯ T ⟶ W) s (Sec.res (prod.snd : W ⨯ T ⟶ T) a) = a := by
  change Sec.res (prod.lift (prod.fst : W ⨯ T ⟶ W) (𝟙 (W ⨯ T)))
    (Sec.res (Limits.prod.map (𝟙 W) (prod.snd : W ⨯ T ⟶ T)) (show Sec (I.X s) (W ⨯ T) from a)) = a
  rw [res_res]
  have : prod.lift (prod.fst : W ⨯ T ⟶ W) (𝟙 (W ⨯ T)) ≫ Limits.prod.map (𝟙 W) (prod.snd : W ⨯ T ⟶ T) = 𝟙 _ := by
    apply Limits.prod.hom_ext <;> simp
  rw [this, res_id]

private theorem upL_d (I : Cx R) {T : Scheme.{0}} (g : T ⟶ W) (s t : ℤ) (a : Sec ((Bc W I).X s) T) :
    Sec.map (I.d s t) (upL I g s a) = upL I g t (Sec.map ((Bc W I).d s t) a) :=
  map_sec_res (I.d s t) (prod.lift g (𝟙 T)) (show Sec (I.X s) (W ⨯ T) from a)

private theorem ev_nat' {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E p U) :
    Sec.res g (ev α p s h U x) = ev α p s h V (x.res g) :=
  (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).2.1 α p s h V U g x

private theorem ev_ext' {E : Spc} {I : Cx R} {n : ℤ} {α β : Cochain ((chains R).obj E) I n}
    (h : ∀ p s h U x, ev α p s h U x = ev β p s h U x) : α = β :=
  (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).2.2.1 α β h

private theorem up_ex {I : Cx R} {n : ℤ} (γ : Cochain ((chains R).obj E) (Bc W I) n) :
    ∃ β : Cochain ((chains R).obj (sch.obj W ⨯ E)) I n,
      ∀ p s h T y, ev β p s h T y = upL I (fstW y) s (ev γ p s h T (sndE y)) :=
  GlobalTheory.T.exists_cochain_ev_eq_of_natural' R (fun p s h T y => upL I (fstW y) s (ev γ p s h T (sndE y))) (by
    intro p s h V U g y
    rw [upL_nat, ev_nat', fst_res, snd_res])

private theorem down_ex {I : Cx R} {n : ℤ} (β : Cochain ((chains R).obj (sch.obj W ⨯ E)) I n) :
    ∃ γ : Cochain ((chains R).obj E) (Bc W I) n, ∀ p s h T x, ev γ p s h T x =
      (show Sec ((Bc W I).X s) T from ev β p s h (W ⨯ T) (mkP prod.fst (x.res prod.snd))) :=
  GlobalTheory.T.exists_cochain_ev_eq_of_natural' R (fun p s h T x =>
               (show Sec ((Bc W I).X s) T from ev β p s h (W ⨯ T) (mkP prod.fst (x.res prod.snd)))) (by
    intro p s h V U g x
    change Sec.res (Limits.prod.map (𝟙 W) g) (ev β p s h (W ⨯ U) (mkP prod.fst (x.res prod.snd))) =
      ev β p s h (W ⨯ V) (mkP prod.fst ((x.res g).res prod.snd))
    rw [ev_nat']
    congr 1
    apply pair_ext
    · rw [fst_res, fst_mkP, fst_mkP]
      simp
    · rw [snd_res, snd_mkP, snd_mkP, sx_res_res, sx_res_res]
      simp)

private def up {I : Cx R} {n : ℤ} (γ : Cochain ((chains R).obj E) (Bc W I) n) :
    Cochain ((chains R).obj (sch.obj W ⨯ E)) I n := (up_ex γ).choose

private theorem ev_up {I : Cx R} {n : ℤ} (γ : Cochain ((chains R).obj E) (Bc W I) n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) (T : Scheme.{0}) (y : Sx (sch.obj W ⨯ E) p T) :
    ev (up γ) p s h T y = upL I (fstW y) s (ev γ p s h T (sndE y)) :=
  (up_ex γ).choose_spec p s h T y

private def down {I : Cx R} {n : ℤ} (β : Cochain ((chains R).obj (sch.obj W ⨯ E)) I n) :
    Cochain ((chains R).obj E) (Bc W I) n := (down_ex β).choose

private theorem ev_down {I : Cx R} {n : ℤ} (β : Cochain ((chains R).obj (sch.obj W ⨯ E)) I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) (T : Scheme.{0}) (x : Sx E p T) :
    ev (down β) p s h T x =
      (show Sec ((Bc W I).X s) T from ev β p s h (W ⨯ T) (mkP prod.fst (x.res prod.snd))) :=
  (down_ex β).choose_spec p s h T x

private theorem up_down {I : Cx R} {n : ℤ} (β : Cochain ((chains R).obj (sch.obj W ⨯ E)) I n) :
    up (down β) = β := by
  apply ev_ext'
  intro p s h T y
  rw [ev_up, ev_down]
  change Sec.res (prod.lift (fstW y) (𝟙 T)) (ev β p s h (W ⨯ T) (mkP prod.fst ((sndE y).res prod.snd))) = _
  rw [ev_nat']
  congr 1
  apply pair_ext
  · rw [fst_res, fst_mkP]
    exact prod.lift_fst _ _
  · rw [snd_res, snd_mkP, sx_res_res, prod.lift_snd, sx_res_id]

private theorem down_up {I : Cx R} {n : ℤ} (γ : Cochain ((chains R).obj E) (Bc W I) n) :
    down (up γ) = γ := by
  apply ev_ext'
  intro p s h T x
  rw [ev_down]
  change ev (up γ) p s h (W ⨯ T) (mkP prod.fst (x.res prod.snd)) = _
  rw [ev_up, fst_mkP, snd_mkP, ← ev_nat']
  exact upL_res I s _

private theorem up_add {I : Cx R} {n : ℤ} (a b : Cochain ((chains R).obj E) (Bc W I) n) :
    up (a + b) = up a + up b := by
  apply ev_ext'
  intro p s h T y
  rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).1 (up a) (up b) p s h T y |>.1, ev_up, ev_up, ev_up,
    ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).1 a b p s h T (sndE y)).1, map_add]

private def upE (W : Scheme.{0}) (I : Cx R) (E : Spc) (n : ℤ) :
    Cochain ((chains R).obj E) (Bc W I) n ≃+ Cochain ((chains R).obj (sch.obj W ⨯ E)) I n where
  toFun := up
  invFun := down
  left_inv := down_up
  right_inv := up_down
  map_add' := up_add

private theorem up_δ {I : Cx R} {n m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj E) (Bc W I) n) :
    δ n m (up α) = up (δ n m α) := by
  apply ev_ext'
  intro p t ht T y
  rw [ev_up]
  cases p with
  | zero =>
    obtain rfl : m = t := by simpa using ht
    refine ((GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values R hm (up α) T).1 y).trans ?_
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values R hm α T).1 (sndE y), ev_up, upL_d]
  | succ p =>
    have hs : -((p + 1 : ℕ) : ℤ) + n = t - 1 := by omega
    refine ((GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values R hm (up α) T).2 p (t - 1) t hs ht y).trans ?_
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values R hm α T).2 p (t - 1) t hs ht (sndE y), map_add, ev_up, upL_d]
    congr 1
    simp only [Units.smul_def, map_zsmul, map_sum, ev_up, fst_face, snd_face]

end UpperTheory.Adj
end

theorem UpperTheory.exists_bijective_cohomologyClass_product_adjunction :
    ∀ (R : Type) [CommRing R] (W : Scheme.{0}) (I : Cx R) (E : Spc) (n : ℤ),
        ∃ Θ : CohomologyClass ((chains R).obj E) (Bc W I) n →+ CohomologyClass ((chains R).obj (sch.obj W ⨯ E)) I n,
          Function.Bijective Θ ∧ ∀ γ : Cocycle ((chains R).obj E) (Bc W I) n,
            ∃ β : Cocycle ((chains R).obj (sch.obj W ⨯ E)) I n, Θ (CohomologyClass.mk γ) = CohomologyClass.mk β ∧
              ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (T : Scheme.{0}) (y : Sx (sch.obj W ⨯ E) p T),
                ev β.1 p s h T y = Sec.res (prod.lift (show T ⟶ W from y.map prod.fst) (𝟙 T))
                  (show Sec (I.X s) (W ⨯ T) from ev γ.1 p s h T (y.map prod.snd)) := by
  intro R _ W I E n
  obtain ⟨Θ, hb, h⟩ := UpperTheory.Adj.classes (fun n => UpperTheory.Adj.upE W I E n)
    (fun n m hm α => UpperTheory.Adj.up_δ hm α) n
  refine ⟨Θ, hb, fun γ => ?_⟩
  obtain ⟨β, h1, h2⟩ := h γ
  refine ⟨β, h1, fun p s hs T y => ?_⟩
  rw [h2]
  exact UpperTheory.Adj.ev_up γ.1 p s hs T y
