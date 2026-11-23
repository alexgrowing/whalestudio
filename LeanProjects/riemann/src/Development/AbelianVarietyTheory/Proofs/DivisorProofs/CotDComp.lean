import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaOfUnitOnEtalePoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivV
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC

def invP (q : ℕ) : PSh where
  obj U := PLift (IsUnit (q : Γ(U.unop, ⊤)))
  map f := TypeCat.ofHom fun h => ⟨by simpa using h.down.map f.unop.appTop.hom⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def fibQ (q N : ℕ) : Spc := pullback (trivV N (disc.obj (invP q))) (PGL.pr N)

def lineQ (q N : ℕ) : fibQ q N ⟶ ofCat (glCat 1) := pullback.snd _ _ ≫ PGL.line N

variable (R : Type) [CommRing R]

def cotPre (q N : ℕ) (I : Cx R) (n : ℤ) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj U := ModuleCat.of (ULift.{1} R) (Cochain ((chains R).obj (sch.obj U.unop ⨯ fibQ q N)) I n)
  map f := ModuleCat.ofHom
    { toFun := fun α => (Cochain.ofHom ((chains R).map (prod.map (sch.map f.unop) (𝟙 (fibQ q N))))).comp α (zero_add n)
      map_add' := fun α β => Cochain.comp_add _ _ _ _
      map_smul' := fun r α => Cochain.comp_smul _ _ _ _ }
  map_id U := by
    ext α : 2
    simp
  map_comp f g := by
    ext α : 2
    change (Cochain.ofHom ((chains R).map (prod.map (sch.map (g.unop ≫ f.unop)) (𝟙 (fibQ q N))))).comp α (zero_add n) =
      (Cochain.ofHom ((chains R).map (prod.map (sch.map g.unop) (𝟙 (fibQ q N))))).comp
        ((Cochain.ofHom ((chains R).map (prod.map (sch.map f.unop) (𝟙 (fibQ q N))))).comp α (zero_add n)) (zero_add n)
    rw [show prod.map (sch.map (g.unop ≫ f.unop)) (𝟙 (fibQ q N)) =
      prod.map (sch.map g.unop) (𝟙 (fibQ q N)) ≫ prod.map (sch.map f.unop) (𝟙 (fibQ q N)) by simp,
      Functor.map_comp, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

def cotD (q N : ℕ) (I : Cx R) (n : ℤ) : cotPre R q N I n ⟶ cotPre R q N I (n + 1) where
  app U := ModuleCat.ofHom
    { toFun := fun α => δ n (n + 1) α
      map_add' := fun α β => δ_add _ _ _ _
      map_smul' := fun r α => δ_smul _ _ _ _ }
  naturality U U' f := by
    ext α : 2
    revert α
    intro (α : Cochain ((chains R).obj (sch.obj U.unop ⨯ fibQ q N)) I n)
    change δ n (n + 1) ((Cochain.ofHom ((chains R).map (prod.map (sch.map f.unop) (𝟙 (fibQ q N))))).comp α (zero_add n)) =
      (Cochain.ofHom ((chains R).map (prod.map (sch.map f.unop) (𝟙 (fibQ q N))))).comp (δ n (n + 1) α) (zero_add (n + 1))
    rw [δ_zero_cochain_comp _ _ _ rfl, δ_ofHom, Cochain.zero_comp, smul_zero, add_zero]

theorem cotD_comp (q N : ℕ) (I : Cx R) (n : ℤ) : cotD R q N I n ≫ cotD R q N I (n + 1) = 0 := by
  ext U : 2
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro α
  change δ (n + 1) (n + 1 + 1) (δ n (n + 1) α) = 0
  exact δ_δ _ _ _ _

def Jcx (q N : ℕ) (I : Cx R) : Cx R :=
  CochainComplex.of (fun n => (presheafToSheaf Scheme.etaleTopology.{0} _).obj (cotPre R q N I n))
    (fun n => (presheafToSheaf Scheme.etaleTopology.{0} _).map (cotD R q N I n))
    (fun n => by rw [← Functor.map_comp, cotD_comp, Functor.map_zero])

variable {R}

def Jsec {q N : ℕ} {I : Cx R} {n : ℤ} {U : Scheme.{0}} (c : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n) :
    Sec ((Jcx R q N I).X n) U :=
  ((toSheafify Scheme.etaleTopology.{0} (cotPre R q N I n)).app (op U)).hom c

def twCast {q : ℕ} {i i' : ℤ} (h : i = i') {s : ℤ} {V : Scheme.{0}} (x : Sec ((res (ZMod q) (tw q i)).X s) V) :
    Sec ((res (ZMod q) (tw q i')).X s) V := h ▸ x

end GlobalTheory.EtC

end
