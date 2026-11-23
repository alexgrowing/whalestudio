import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.CechAugRow
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.MapUgAlgebraMap
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TensorProduct GroundTheory.PAdicHodge

universe w v u v' u'

namespace CrystallineSemistableComparison.D

def DesJ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {T : Type u'} [Category.{v'} T] (j : T ⥤ C)
    (F : C ⥤ ModuleCat.{w} R) (s : R) : Prop :=
  ∀ A : C, (CH.cx (CH.elF (CH.pts j A) (j ⋙ F))).ResUpTo s (CH.ptsAug j F A)

abbrev PfC (p : ℕ) (R : Type) [CommRing R] : Type 1 := ObjectProperty.FullSubcategory fun A : CommAlgCat.{0} R => Pf p A

def tensF (p : ℕ) (R : Type) [CommRing R] (N : Type) [AddCommGroup N] [Module R N] : PfC p R ⥤ ModuleCat.{0} R where
  obj A := ModuleCat.of R (N ⊗[R] A.obj)
  map f := ModuleCat.ofHom (f.hom.hom.toLinearMap.lTensor N)
  map_id A := ModuleCat.hom_ext (TensorProduct.ext' fun _ _ => rfl)
  map_comp f g := ModuleCat.hom_ext (TensorProduct.ext' fun _ _ => rfl)

variable (l : ℕ) [Fact l.Prime]

def toPf : PAlg l ⥤ PfC l (Ob l) where
  obj A := ⟨CommAlgCat.of (Ob l) A.A, A.natCast_l, A.perf.bijective_frobenius⟩
  map f := ObjectProperty.homMk (CommAlgCat.ofHom ⟨PAlg.Hom.f f, fun c => RingHom.congr_fun (PAlg.Hom.comm f) c⟩)
  map_id _ := rfl
  map_comp _ _ := rfl

def rt (k : ℕ) : Ob l := (iterateFrobeniusEquiv (Ob l) l k).symm (pFlat l)

def rtW (k : ℕ) : Ainf l := WittVector.teichmuller l (rt l k)

def InWm (s : Ainf l) : Prop := ∀ i, ¬ IsUnit (s.coeff i)

variable {l} in

abbrev Des {R : Type} [CommRing R] (F : PAlg l ⥤ ModuleCat.{0} R) (s : R) : Prop := DesJ (testι l) F s

def ObFacts : Prop :=
  ∃ _ : IsDomain (Ob l), ValuationRing (Ob l) ∧ (∀ a : Ob l, a ≠ 0 → ∃ M : ℕ, a ∣ pFlat l ^ M) ∧
    ∀ a : Ob l, ¬ IsUnit a → ∃ k, rt l k ∣ a

def RAcr1 : Prop :=
  ∃ (N : Type) (_ : AddCommGroup N) (_ : Module (Ob l) N) (M : ℕ) (τ : ∀ A : PAlg l, N ⊗[Ob l] A.A ≃+ A.Acr 1),
    (∀ x : N, pFlat l ^ M • x = 0) ∧
    (∀ (A : PAlg l) (a : Ainf l) (x : N ⊗[Ob l] A.A), τ A (a.coeff 0 • x) = algebraMap (Ainf l) (A.Acr 1) a * τ A x) ∧
    ∀ (A B : PAlg l) (f : A ⟶ B) (x : N ⊗[Ob l] A.A),
      τ B (((toPf l ⋙ tensF l (Ob l) N).map f).hom x) = PAlg.mapAcr f 1 (τ A x)

def RAcrSeq : Prop :=
  ∀ n : ℕ, ∃ α : ∀ A : PAlg l, A.Acr 1 →+ A.Acr (n + 1),
    (∀ (A : PAlg l) (y : A.Acr0), α A (A.mkAcr 1 y) = A.mkAcr (n + 1) ((l : A.Acr0) ^ n * y)) ∧
    ∀ A : PAlg l, Function.Injective (α A) ∧ Function.Exact (α A) (A.red n.le_succ)

def RU : Prop :=
  ∀ A : PAlg l, (l : A.U) ∈ nonZeroDivisors A.U ∧
    ∀ x : A.W, A.th x ∈ Ideal.span {(l : A.U)} ↔ x.coeff 0 ∈ Ideal.span {A.pi}

def RGr : Prop :=
  ∀ (A : PAlg l) (n r : ℕ), (∀ z ∈ A.Fil n r, ∃ x : A.W, z - A.toAcr n x * A.dxi n r ∈ A.Fil n (r + 1)) ∧
    ∀ x : A.W, A.toAcr n x * A.dxi n r ∈ A.Fil n (r + 1) ↔ A.th x ∈ Ideal.span {(l : A.U) ^ n}

def RIn : Prop := ObFacts l ∧ RAcr1 l ∧ RAcrSeq l ∧ RU l ∧ RGr l

def Out : Prop :=
  ∀ s : Ainf l, InWm l s → ∀ n : ℕ, Des (UnF l n) s ∧ Des (AcrF l n) (algebraMap (Ainf l) (Acris l) s) ∧
    ∀ r : ℕ, Des (FilF l n r) (algebraMap (Ainf l) (Acris l) s)

end CrystallineSemistableComparison.D
