import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.Divisors.AltPullApply
import Development.AbelianVarietyTheory.Definitions.Divisors.CircleAsphGNontrivial

noncomputable section

namespace GlobalTheory.KS

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.EtC GlobalTheory.UPel.HT
open scoped TensorProduct

variable {S : Scheme.{0}} {O : Type} [Ring O]

abbrev pow (A : Over S) (m : ℕ) : Over S := ∏ᶜ fun _ : Fin m => A

abbrev pr (A : Over S) {m : ℕ} (i : Fin m) : pow A m ⟶ A := Pi.π (fun _ : Fin m => A) i

def matEnd {A : Over S} [GrpObj A] (act : OActN O A) {m : ℕ} (M : Matrix (Fin m) (Fin m) O) : pow A m ⟶ pow A m :=
  Pi.lift fun i => (List.ofFn fun j => pr A j ≫ act.act (M i j)).prod

def powMap {S' : Scheme.{0}} {A' : Over S'} {A : Over S} (f : S' ⟶ S) (φ : A'.left ⟶ A.left) (h : φ ≫ A.hom = A'.hom ≫ f)
    (m : ℕ) : (pow A' m).left ⟶ (pow A m).left :=
  (Pi.lift (fun i => Over.homMk ((pr A' i).left ≫ φ) (by
    rw [Category.assoc, h, ← Category.assoc, Over.w]; rfl)) : Over.mk ((pow A' m).hom ≫ f) ⟶ pow A m).left

variable {B B' : Scheme.{0}}

abbrev ksBC (A : Over S) (m : ℕ) (p : S ⟶ B) (b : B' ⟶ B) : Scheme.{0} := pullback ((pow A m).hom ≫ p) b

def matBC {A : Over S} [GrpObj A] (act : OActN O A) {m : ℕ} (p : S ⟶ B) (b : B' ⟶ B) (M : Matrix (Fin m) (Fin m) O) :
    ksBC A m p b ⟶ ksBC A m p b :=
  pullback.map _ _ _ _ (matEnd act M).left (𝟙 _) (𝟙 _) (by rw [Category.comp_id, ← Category.assoc, Over.w]) (by simp)

variable (l : ℕ) [Fact l.Prime] (E : Type) [CommRing E] [Algebra ℚ_[l] E]

abbrev HE (Y : Scheme.{0}) (n : ℤ) : Type 1 := E ⊗[ℚ_[l]] HQ l (sch.obj Y) n 0

def pullE {Y Y' : Scheme.{0}} (u : Y ⟶ Y') (n : ℤ) : HE l E Y' n →ₗ[E] HE l E Y n :=
  (pullHQ l (sch.map u) n 0).baseChange E

variable {E}

def op {A : Over S} [GrpObj A] (act : OActN O A) {m : ℕ} (p : S ⟶ B) (b : B' ⟶ B) (ε : Matrix (Fin m) (Fin m) O →₀ E)
    (n : ℤ) : Module.End E (HE l E (ksBC A m p b) n) :=
  ε.sum fun M c => c • pullE l E (matBC act p b M) n

def Hxi {A : Over S} [GrpObj A] (act : OActN O A) {m : ℕ} (p : S ⟶ B) (b : B' ⟶ B) (ε : Matrix (Fin m) (Fin m) O →₀ E)
    (k : ℕ) (i : ℤ) : Submodule E (HE l E (ksBC A m p b) (i + k)) :=
  LinearMap.range (op l act p b ε (i + k))

def galE (E : Type) [CommRing E] [Algebra ℚ_[l] E] {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {Y : Scheme.{0}}
    (q : Y ⟶ Spec (CommRingCat.of k)) (n : ℤ) (σ : Ω ≃ₐ[k] Ω) : Module.End E (HE l E (GlobalTheory.Et.geom Ω q) n) :=
  pullE l E (GlobalTheory.Et.galMap Ω q σ) n

variable (E) in

abbrev HEt (Y : Scheme.{0}) (n t : ℤ) : Type 1 := E ⊗[ℚ_[l]] HQ l (sch.obj Y) n t

variable (E) in

def pullEt {Y Y' : Scheme.{0}} (u : Y ⟶ Y') (n t : ℤ) : HEt l E Y' n t →ₗ[E] HEt l E Y n t :=
  (pullHQ l (sch.map u) n t).baseChange E

def opT {A : Over S} [GrpObj A] (act : OActN O A) {m : ℕ} (p : S ⟶ B) (b : B' ⟶ B) (ε : Matrix (Fin m) (Fin m) O →₀ E)
    (n t : ℤ) : Module.End E (HEt l E (ksBC A m p b) n t) :=
  ε.sum fun M c => c • pullEt l E (matBC act p b M) n t

def HxiT {A : Over S} [GrpObj A] (act : OActN O A) {m : ℕ} (p : S ⟶ B) (b : B' ⟶ B) (ε : Matrix (Fin m) (Fin m) O →₀ E)
    (k : ℕ) (t i : ℤ) : Submodule E (HEt l E (ksBC A m p b) (i + k) t) :=
  LinearMap.range (opT l act p b ε (i + k) t)

def galEt (E : Type) [CommRing E] [Algebra ℚ_[l] E] {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {Y : Scheme.{0}}
    (q : Y ⟶ Spec (CommRingCat.of k)) (n t : ℤ) (σ : Ω ≃ₐ[k] Ω) : Module.End E (HEt l E (GlobalTheory.Et.geom Ω q) n t) :=
  pullEt l E (GlobalTheory.Et.galMap Ω q σ) n t

variable (E) in
theorem pullEt_zero {Y Y' : Scheme.{0}} (u : Y ⟶ Y') (n : ℤ) : pullEt l E u n 0 = pullE l E u n := rfl

theorem opT_zero {A : Over S} [GrpObj A] (act : OActN O A) {m : ℕ} (p : S ⟶ B) (b : B' ⟶ B)
    (ε : Matrix (Fin m) (Fin m) O →₀ E) (n : ℤ) : opT l act p b ε n 0 = op l act p b ε n := rfl

theorem HxiT_zero {A : Over S} [GrpObj A] (act : OActN O A) {m : ℕ} (p : S ⟶ B) (b : B' ⟶ B)
    (ε : Matrix (Fin m) (Fin m) O →₀ E) (k : ℕ) (i : ℤ) : HxiT l act p b ε k 0 i = Hxi l act p b ε k i := rfl

theorem galEt_zero (E : Type) [CommRing E] [Algebra ℚ_[l] E] {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω]
    {Y : Scheme.{0}} (q : Y ⟶ Spec (CommRingCat.of k)) (n : ℤ) (σ : Ω ≃ₐ[k] Ω) :
    galEt l E Ω q n 0 σ = galE l E Ω q n σ := rfl

example (Y : Scheme.{0}) (n : ℤ) : HEt l E Y n 0 = HE l E Y n := rfl

@[simp] theorem opT_zero_comb {A : Over S} [GrpObj A] (act : OActN O A) {m : ℕ} (p : S ⟶ B) (b : B' ⟶ B) (n t : ℤ) :
    opT l act p b (0 : Matrix (Fin m) (Fin m) O →₀ E) n t = 0 := by
  simp [opT]

theorem HxiT_zero_comb {A : Over S} [GrpObj A] (act : OActN O A) {m : ℕ} (p : S ⟶ B) (b : B' ⟶ B) (k : ℕ) (t i : ℤ) :
    HxiT l act p b (0 : Matrix (Fin m) (Fin m) O →₀ E) k t i = ⊥ := by
  rw [HxiT, opT_zero_comb, LinearMap.range_zero]

theorem opT_add {A : Over S} [GrpObj A] (act : OActN O A) {m : ℕ} (p : S ⟶ B) (b : B' ⟶ B)
    (ε ε' : Matrix (Fin m) (Fin m) O →₀ E) (n t : ℤ) : opT l act p b (ε + ε') n t = opT l act p b ε n t + opT l act p b ε' n t := by
  unfold opT
  exact Finsupp.sum_add_index' (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)

abbrev latRep {p : ℕ} [Fact p.Prime] (D : Datum p) : D.O →+* Module.End ℤ D.La := Module.toModuleEnd ℤ D.La

example {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (A : Over S) (m : ℕ) (p : S ⟶ Spec (CommRingCat.of k)) :
    ksBC A m p (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) = GlobalTheory.Et.geom Ω ((pow A m).hom ≫ p) := rfl

def ArtinQE (E : Type) [Field E] [Algebra ℚ_[l] E] : Prop :=
  ∃ e : ∀ (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of ℂ)) [LocallyOfFiniteType p] [QuasiCompact p] [IsSeparated p] (n : ℕ),
      HE l E X n ≃ₗ[E] SH E (GlobalTheory.CxPts p (RingHom.id ℂ)) n,
    ∀ (X Y : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of ℂ)) [LocallyOfFiniteType p] [QuasiCompact p] [IsSeparated p]
      (q : Y ⟶ Spec (CommRingCat.of ℂ)) [LocallyOfFiniteType q] [QuasiCompact q] [IsSeparated q]
      (u : X ⟶ Y) (g : C(GlobalTheory.CxPts p (RingHom.id ℂ), GlobalTheory.CxPts q (RingHom.id ℂ))), u ≫ q = p → (∀ x, (g x).1 = x.1 ≫ u) →
      ∀ (n : ℕ) (y : HE l E Y n), e X p n (pullE l E u n y) = shMap E g n (e Y q n y)

def trivMap (E : Type) [Field E] {G G' : Type} [Group G] [Group G'] (α : G' →* G) :
    Rep.res α (Rep.trivial E G E) ⟶ Rep.trivial E G' E :=
  Rep.ofHom { toLinearMap := LinearMap.id, isIntertwining' := fun _ => rfl }

end GlobalTheory.KS
