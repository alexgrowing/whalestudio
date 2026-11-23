import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafDescendAlongLocallyBijectiveStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.TensFam

variable {R : Type} [CommRing R]

theorem tensRes_id (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Tens.res (I := I) (J := J) (𝟙 U) w = LinearMap.id := by
  classical
  apply DirectSum.linearMap_ext
  intro p
  apply TensorProduct.ext'
  intro a b
  simp [Tens.res, DirectSum.lmap_lof]

theorem tensRes_comp (I J : Cx R) {W V U : Scheme.{0}} (f : W ⟶ V) (g : V ⟶ U) (w : ℤ) :
    Tens.res (I := I) (J := J) (f ≫ g) w = (Tens.res f w).comp (Tens.res g w) := by
  classical
  apply DirectSum.linearMap_ext
  intro p
  apply TensorProduct.ext'
  intro a b
  simp [Tens.res, DirectSum.lmap_lof]

theorem lift_resL {I J K : Cx R} (τ : Pair I J K) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) :
    (τ.lift V w).comp (Tens.res g w) = ((K.X w).obj.map g.op).hom.comp (τ.lift U w) := by
  classical
  apply DirectSum.linearMap_ext
  intro p
  apply TensorProduct.ext'
  intro a b
  have := τ.nat g p.1.1 p.1.2 w p.2 a b
  simp [Tens.res, Pair.lift, DirectSum.lmap_lof] at this ⊢
  exact this.symm

def tensP (I J : Cx R) (w : ℤ) : Scheme.{0}ᵒᵖ ⥤ AddCommGrpCat.{1} where
  obj U := AddCommGrpCat.of (Tens I J U.unop w)
  map g := AddCommGrpCat.ofHom (Tens.res g.unop w).toAddMonoidHom
  map_id U := by
    apply AddCommGrpCat.ext; intro x
    change Tens.res (I := I) (J := J) (𝟙 U.unop) w x = x
    rw [tensRes_id]; rfl
  map_comp f g := by
    apply AddCommGrpCat.ext; intro x
    change Tens.res (I := I) (J := J) (g.unop ≫ f.unop) w x = Tens.res g.unop w (Tens.res f.unop w x)
    rw [tensRes_comp]; rfl

def secP (F : Shv R) : Scheme.{0}ᵒᵖ ⥤ AddCommGrpCat.{1} := F.obj ⋙ forget₂ _ AddCommGrpCat

def liftP {I J K : Cx R} (τ : Pair I J K) (w : ℤ) : tensP I J w ⟶ secP (K.X w) where
  app U := AddCommGrpCat.ofHom (τ.lift U.unop w).toAddMonoidHom
  naturality V U g := by
    apply AddCommGrpCat.ext; intro x
    exact LinearMap.congr_fun (lift_resL τ g.unop w) x

end GlobalTheory.EtC.TensFam

open GlobalTheory.EtC.TensFam in

theorem GlobalTheory.EtC.tens_fam : ∀ (R S : Type) [CommRing R] [CommRing S] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor → ∀ (w : ℤ) (M : Shv S) (b : ∀ U : Scheme.{0}, Tens I J U w →+ Sec M U), (∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (b U x) = b V (Tens.res g w x)) → ∃ φ : ∀ U : Scheme.{0}, Sec (K.X w) U →+ Sec M U, (∀ (V U : Scheme.{0}) (g : V ⟶ U) y, Sec.res g (φ U y) = φ V (Sec.res g y)) ∧ ∀ U x, φ U (τ.lift U w x) = b U x := by
  intro R S _ _ I J K τ hτ w M b hb
  exact GlobalTheory.T.etaleSheaf_descend_along_locallyBijective S (tensP I J w) (secP (K.X w)) (liftP τ w)
    (fun U y => hτ.1 U w y) (fun U x hx => hτ.2 U w x hx) M b hb
