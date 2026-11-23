import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaOfUnitOnEtalePoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivV
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotDComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec

noncomputable section
namespace GlobalTheory.EtC.GlueDisc

def pe (k : ℕ) (V : Scheme.{0}) : Spc ⥤ Type :=
  (evaluation _ _).obj (op (SimplexCategory.mk k)) ⋙ (evaluation _ _).obj (op V)

instance (k : ℕ) (V : Scheme.{0}) : PreservesLimitsOfShape (Discrete WalkingPair) (pe k V) := by
  unfold pe; infer_instance

def pairE (A B : Spc) (k : ℕ) (V : Scheme.{0}) : Sx (A ⨯ B) k V ≃ Sx A k V × Sx B k V :=
  ((PreservesLimitPair.iso (pe k V) A B) ≪≫ Types.binaryProductIso _ _).toEquiv

theorem pairE_apply (A B : Spc) (k : ℕ) (V : Scheme.{0}) (z : Sx (A ⨯ B) k V) :
    pairE A B k V z = (Sx.map prod.fst z, Sx.map prod.snd z) := by
  apply Prod.ext
  · change ((Types.binaryProductIso _ _).hom ((prodComparison (pe k V) A B) z)).1 = _
    rw [Types.binaryProductIso_hom_comp_fst_apply]
    exact ConcreteCategory.congr_hom (prodComparison_fst (pe k V) A B) z
  · change ((Types.binaryProductIso _ _).hom ((prodComparison (pe k V) A B) z)).2 = _
    rw [Types.binaryProductIso_hom_comp_snd_apply]
    exact ConcreteCategory.congr_hom (prodComparison_snd (pe k V) A B) z

theorem prod_ext {A B : Spc} {k : ℕ} {V : Scheme.{0}} (z z' : Sx (A ⨯ B) k V)
    (h₁ : Sx.map prod.fst z = Sx.map prod.fst z') (h₂ : Sx.map prod.snd z = Sx.map prod.snd z') : z = z' :=
  (pairE A B k V).injective (by rw [pairE_apply, pairE_apply, h₁, h₂])

def mk {A B : Spc} {k : ℕ} {V : Scheme.{0}} (a : Sx A k V) (b : Sx B k V) : Sx (A ⨯ B) k V :=
  (pairE A B k V).symm (a, b)

theorem mk_fst {A B : Spc} {k : ℕ} {V : Scheme.{0}} (a : Sx A k V) (b : Sx B k V) : Sx.map prod.fst (mk a b) = a := by
  have h := (pairE A B k V).apply_symm_apply (a, b)
  rw [pairE_apply] at h
  exact congrArg Prod.fst h

theorem mk_snd {A B : Spc} {k : ℕ} {V : Scheme.{0}} (a : Sx A k V) (b : Sx B k V) : Sx.map prod.snd (mk a b) = b := by
  have h := (pairE A B k V).apply_symm_apply (a, b)
  rw [pairE_apply] at h
  exact congrArg Prod.snd h

theorem map_res {E E' : Spc} (f : E ⟶ E') {V W : Scheme.{0}} (h : W ⟶ V) {k : ℕ} (a : Sx E k V) :
    Sx.map f (Sx.res h a) = Sx.res h (Sx.map f a) :=
  ConcreteCategory.congr_hom ((f.app (op (SimplexCategory.mk k))).naturality h.op) a

theorem map_prodMap_fst {A A' B B' : Spc} (f : A ⟶ A') (g : B ⟶ B') {k : ℕ} {V : Scheme.{0}} (z : Sx (A ⨯ B) k V) :
    Sx.map prod.fst (Sx.map (prod.map f g) z) = Sx.map f (Sx.map prod.fst z) := by
  change Sx.map (prod.map f g ≫ prod.fst) z = Sx.map (prod.fst ≫ f) z
  rw [prod.map_fst]

theorem map_prodMap_snd {A A' B B' : Spc} (f : A ⟶ A') (g : B ⟶ B') {k : ℕ} {V : Scheme.{0}} (z : Sx (A ⨯ B) k V) :
    Sx.map prod.snd (Sx.map (prod.map f g) z) = Sx.map g (Sx.map prod.snd z) := by
  change Sx.map (prod.map f g ≫ prod.snd) z = Sx.map (prod.snd ≫ g) z
  rw [prod.map_snd]

variable {F : PSh} {B : Spc}

def lift {k : ℕ} {V : Scheme.{0}} (z : Sx (disc.obj F ⨯ B) k V) : Sx (sch.obj V ⨯ B) k V :=
  mk (show Sx (sch.obj V) k V from 𝟙 V) (Sx.map prod.snd z)

theorem lift_spec {k : ℕ} {V : Scheme.{0}} (z : Sx (disc.obj F ⨯ B) k V) :
    Sx.map (E := sch.obj V ⨯ B) (prod.map (disc.map (yonedaEquiv.symm (Sx.map prod.fst z))) (𝟙 B)) (lift z) = z := by
  apply prod_ext
  · have h := map_prodMap_fst (A := sch.obj V)
      (show sch.obj V ⟶ disc.obj F from disc.map (yonedaEquiv.symm (Sx.map prod.fst z))) (𝟙 B) (lift z)
    rw [lift, mk_fst] at h
    refine h.trans ?_
    change F.map (𝟙 V).op (Sx.map prod.fst z) = _
    rw [op_id, FunctorToTypes.map_id_apply]
    rfl
  · have h := map_prodMap_snd (A := sch.obj V)
      (show sch.obj V ⟶ disc.obj F from disc.map (yonedaEquiv.symm (Sx.map prod.fst z))) (𝟙 B) (lift z)
    rw [lift, mk_snd] at h
    exact h

theorem lift_res {k : ℕ} {V W : Scheme.{0}} (g : W ⟶ V) (z : Sx (disc.obj F ⨯ B) k V) :
    Sx.res g (lift z) = Sx.map (prod.map (sch.map g) (𝟙 B)) (lift (Sx.res g z)) := by
  apply prod_ext
  · rw [map_prodMap_fst, map_res, lift, lift, mk_fst, mk_fst]
    change g ≫ 𝟙 V = 𝟙 W ≫ g
    rw [Category.comp_id, Category.id_comp]
  · rw [map_prodMap_snd, map_res, lift, lift, mk_snd, mk_snd, map_res]
    rfl

theorem fst_pull {k : ℕ} {U W : Scheme.{0}} (x : F.obj (op U)) (y : Sx (sch.obj U ⨯ B) k W) :
    Sx.map prod.fst (Sx.map (E := sch.obj U ⨯ B) (prod.map (disc.map (yonedaEquiv.symm x)) (𝟙 B)) y) =
      F.map (Quiver.Hom.op (Sx.map prod.fst y : W ⟶ U)) x :=
  map_prodMap_fst (A := sch.obj U)
    (show sch.obj U ⟶ disc.obj F from disc.map (yonedaEquiv.symm x)) (𝟙 B) y

theorem lift_pull {k : ℕ} {U W : Scheme.{0}} (x : F.obj (op U)) (y : Sx (sch.obj U ⨯ B) k W) :
    Sx.map (prod.map (sch.map (Sx.map prod.fst y : W ⟶ U)) (𝟙 B))
      (lift (Sx.map (E := sch.obj U ⨯ B) (prod.map (disc.map (yonedaEquiv.symm x)) (𝟙 B)) y)) = y := by
  apply prod_ext
  · rw [map_prodMap_fst, lift, mk_fst]
    exact Category.id_comp (Sx.map prod.fst y : W ⟶ U)
  · rw [map_prodMap_snd, lift, mk_snd]
    exact map_prodMap_snd (A := sch.obj U)
      (show sch.obj U ⟶ disc.obj F from disc.map (yonedaEquiv.symm x)) (𝟙 B) y

end GlobalTheory.EtC.GlueDisc

namespace GlobalTheory.EtC
open GlueDisc

theorem cochain_disc_glue (R : Type) [CommRing R] (q N : ℕ) (I : Cx R) (F : PSh) (n : ℤ)
    (c : ∀ U : Scheme.{0}, F.obj (op U) → Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n)
    (hc : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : F.obj (op U)),
      c V (F.map g.op x) = (Cochain.ofHom ((chains R).map (prod.map (sch.map g) (𝟙 (fibQ q N))))).comp (c U x) (zero_add n)) :
    ∃! γ : Cochain ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n, ∀ (U : Scheme.{0}) (x : F.obj (op U)),
      (Cochain.ofHom ((chains R).map (prod.map (disc.map (yonedaEquiv.symm x)) (𝟙 (fibQ q N))))).comp γ (zero_add n) =
        c U x := by
  obtain ⟨γ, hγ⟩ := ev_exists (R := R) (E := disc.obj F ⨯ fibQ q N) (I := I) (n := n)
    (fun p s h V z => ev (c V (Sx.map prod.fst z)) p s h V (lift z)) (by
      intro p s h V U g z
      rw [ev_res, lift_res, map_res]
      refine (ev_pull (prod.map (sch.map g) (𝟙 (fibQ q N))) (c U (Sx.map prod.fst z)) p s h V
        (lift (Sx.res g z))).symm.trans ?_
      rw [← hc]
      rfl)
  refine ⟨γ, fun U x => ev_ext (E := sch.obj U ⨯ fibQ q N) _ _ fun p s h W y => ?_, fun γ' hγ' => ev_ext _ _ fun p s h V z => ?_⟩
  · refine (ev_pull (E' := sch.obj U ⨯ fibQ q N) (prod.map (disc.map (yonedaEquiv.symm x)) (𝟙 (fibQ q N))) γ
      p s h W y).trans ?_
    rw [hγ, fst_pull]
    refine (congrArg (fun α => ev α p s h W _) (hc W U (Sx.map prod.fst y : W ⟶ U) x)).trans ?_
    rw [ev_pull, lift_pull]
  · rw [hγ, ← hγ' V (Sx.map prod.fst z)]
    refine (congrArg (ev γ' p s h V) (lift_spec z)).symm.trans ?_
    exact (ev_pull (E' := sch.obj V ⨯ fibQ q N) _ γ' p s h V (lift z)).symm

end GlobalTheory.EtC
