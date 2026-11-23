import Mathlib
import Formalism.LocalRingCardinality.DataLevelD
import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ClassesDoubleCosets

open NumberField IsDedekindDomain Formalism.UG Formalism.BasicNotions Formalism.L2.Herm
open scoped TensorProduct

def CosetMass {G : Type} [Group G] (Γ K : Subgroup G) (m : ℝ) : Prop :=
  Finite (ClassSet Γ K) ∧
  (∀ y : G, Finite (stabAt Γ K y)) ∧
  ∀ [Fintype (ClassSet Γ K)] (s : ClassSet Γ K → G), (∀ c, DoubleCoset.mk Γ K (s c) = c) →
    ∑ c, ((Nat.card (stabAt Γ K (s c)) : ℕ) : ℝ)⁻¹ = m

def stabHat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) (W : HSpace E) (N : Submodule (𝓞 E) W.V) : Subgroup (UAf hc W) :=
  (stabGL (hatL (F := F) (crdLat W N))).subgroupOf (UAf hc W)

def General : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) (W : HSpace E), W.SigOK → W.IsPosDef →
    ∀ N : Submodule (𝓞 E) W.V, Submodule.IsLattice E N → Formalism.HermitianLatticesTheory.IsUnimodular W.hT N →
      CosetMass (UFin hc W) (stabHat hc W N) (Formalism.HermitianLatticesTheory.mass W.hT N)

def DefiniteSpaceClassStatement (D : D7) (_Lv : LevelData D) (_u : D.what₂.Word) : Prop :=
  letI := D.host.cmStar
  ∀ N : Submodule (𝓞 D.host.E) (D.sp.X 0).V, Submodule.IsLattice D.host.E N →
    Formalism.HermitianLatticesTheory.IsUnimodular (D.sp.X 0).hT N →
    CosetMass
      ((ratPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F)).subgroupOf
        (UPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
      ((levelAfL D.sp.cm.sig D.sp.gram0 (D.sp.crdLat0 N)).subgroupOf
        (UPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
      (Formalism.HermitianLatticesTheory.mass (D.sp.X 0).hT N)

def ClassesAsDoubleCosets : Prop :=
  General ∧ ∀ (D : D7) (Lv : LevelData D) (u : D.what₂.Word), DefiniteSpaceClassStatement D Lv u

theorem CosetMass.unique {G : Type} [Group G] {Γ K : Subgroup G} {m m' : ℝ}
    (h : CosetMass Γ K m) (h' : CosetMass Γ K m') : m = m' := by
  haveI := h.1
  letI := Fintype.ofFinite (ClassSet Γ K)
  have hs : ∀ c : ClassSet Γ K, DoubleCoset.mk Γ K (Quotient.out c) = c := fun c => Quotient.out_eq' c
  rw [← h.2.2 _ hs, ← h'.2.2 _ hs]

example {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) (W : HSpace E) (N : Submodule (𝓞 E) W.V) :
    stabHat hc W N = (levelAfL hc.sig W.gram (crdLat W N)).subgroupOf (UAf hc W) := by
  ext x
  simp only [stabHat, Subgroup.mem_subgroupOf, levelAfL, level, Subgroup.mem_inf]
  exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩

end GlobalTheory.IndefiniteRowSideFullHecke.ClassesDoubleCosets

end
