import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.BijectiveToPushforwardComp
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.TwistingSheafQuasicoherentLocallyFree

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
noncomputable section
namespace GlobalTheory.AbLaw
open GlobalTheory.LB
variable {X X' : Scheme.{0}}

abbrev lbSheaf (M : LB X) : X.Modules := toMod M

namespace lbSheaf

variable {M M' : LB X} {V W : X.Opens}

variable (M V) in

def sectionsEquiv : Γ(lbSheaf M, V) ≃ₗ[Γ(X, V)] SecOn M V := LinearEquiv.refl _ _

@[simp] theorem sectionsEquiv_apply (s : Γ(lbSheaf M, V)) : sectionsEquiv M V s = s := rfl

def chartIso (hM : M.IsLB) (i : M.ι) :
    unitMod (M.U i).toScheme ≅ (lbSheaf M).restrict (M.U i).ι :=
  GlobalTheory.LB.chartIso hM i

theorem isQuasicoherent (hM : M.IsLB) : (lbSheaf M).IsQuasicoherent := isQuasicoherent_toMod hM

theorem exists_restrict_iso (hM : M.IsLB) (x : X) :
    ∃ (U : X.Opens) (_ : x ∈ U), Nonempty (unitMod U.toScheme ≅ (lbSheaf M).restrict U.ι) := by
  have hx : x ∈ ⨆ i, M.U i := by rw [hM.cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  exact ⟨M.U i, hi, ⟨GlobalTheory.LB.chartIso hM i⟩⟩

def isoOfGen (hM : M.IsLB) (hM' : M'.IsLB) (w : LB.Gen (LB.div M' M)) (hw : w.IsGen) :
    lbSheaf M ≅ lbSheaf M' := GlobalTheory.LB.isoOfGen hM hM' w hw

theorem existsUnique_gen (hM : M.IsLB) (hM' : M'.IsLB) (φ : lbSheaf M ≅ lbSheaf M') :
    ∃! w : LB.Gen (LB.div M' M), ∃ hw : w.IsGen, isoOfGen hM hM' w hw = φ :=
  existsUnique_gen_of_iso hM hM' φ

def genEquivIso (hM : M.IsLB) (hM' : M'.IsLB) :
    {w : LB.Gen (LB.div M' M) // w.IsGen} ≃ (lbSheaf M ≅ lbSheaf M') :=
  Equiv.ofBijective (fun w => isoOfGen hM hM' w.1 w.2)
    ⟨fun w w' h => Subtype.ext ((existsUnique_gen hM hM' _).unique ⟨w.2, h⟩ ⟨w'.2, rfl⟩),
      fun φ => let ⟨w, ⟨hw, h⟩, _⟩ := existsUnique_gen hM hM' φ; ⟨⟨w, hw⟩, h⟩⟩

@[simp] theorem genEquivIso_apply (hM : M.IsLB) (hM' : M'.IsLB)
    (w : {w : LB.Gen (LB.div M' M) // w.IsGen}) :
    genEquivIso hM hM' w = isoOfGen hM hM' w.1 w.2 := rfl

def secEquivHom (hM : M.IsLB) (hM' : M'.IsLB) :
    LB.Sec (LB.div M' M) ≃ (lbSheaf M ⟶ lbSheaf M') := homEquiv hM hM'

theorem triv_div_iff (hM : M.IsLB) (hM' : M'.IsLB) :
    Triv (LB.div M' M) ↔ Nonempty (lbSheaf M ≅ lbSheaf M') := lbIso_iff_nonempty_iso hM hM'

def unitIso (hM : M.IsLB) (t : LB.Gen M) (ht : t.IsGen) :
    unitMod X ≅ lbSheaf M := GlobalTheory.LB.unitIso hM t ht

theorem triv_iff (hM : M.IsLB) :
    Triv M ↔ Nonempty (lbSheaf M ≅ unitMod X) :=
  (exists_isGen_iff_nonempty_iso hM).trans ⟨fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ => ⟨e.symm⟩⟩

def pullbackIso (hM : M.IsLB) (π : X' ⟶ X) :
    (Scheme.Modules.pullback π).obj (lbSheaf M) ≅ lbSheaf (M.pull π) := GlobalTheory.LB.pullbackIso hM π

theorem triv_pull_iff (hM : M.IsLB) (π : X' ⟶ X) :
    Triv (M.pull π) ↔
      Nonempty ((Scheme.Modules.pullback π).obj (lbSheaf M) ≅ unitMod X') :=
  (triv_iff (LB.isLB_pull hM π)).trans
    ⟨fun ⟨e⟩ => ⟨pullbackIso hM π ≪≫ e⟩, fun ⟨e⟩ => ⟨(pullbackIso hM π).symm ≪≫ e⟩⟩

theorem exists_iso_iff (F : X.Modules) :
    (∃ M : LB X, M.IsLB ∧ Nonempty (lbSheaf M ≅ F)) ↔
      ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U), Nonempty (unitMod U.toScheme ≅ F.restrict U.ι) := by
  refine ⟨?_, exists_toMod_iso_of_restrict_iso F⟩
  rintro ⟨M, hM, ⟨φ⟩⟩ x
  obtain ⟨U, hx, ⟨e⟩⟩ := exists_restrict_iso hM x
  exact ⟨U, hx, ⟨e ≪≫ (Scheme.Modules.restrictFunctor U.ι).mapIso φ⟩⟩

end lbSheaf

example (X : Scheme.{0}) : Nonempty (lbSheaf (Inh.trivLB X) ≅ unitMod X) :=
  (lbSheaf.triv_iff (Inh.trivLB_isLB X)).1 (triv_trivLB X)

example : Nontrivial Γ(lbSheaf (Inh.trivLB (Spec (CommRingCat.of ℚ))), ⊤) :=
  (secOnRTrivEquiv (𝟙 (Spec (CommRingCat.of ℚ))) rfl).toEquiv.symm.nontrivial

example {U₀ U₁ : X.Opens} (h : U₀ ⊔ U₁ = ⊤) (a : Γ(X, U₀)ˣ) :
    ∃ e : unitMod X ≅ lbSheaf (twoChart U₀ U₁ (res inf_le_left a)),
      coord (e.hom.app ⊤ (1 : Γ(X, ⊤))) true = rs X (inf_le_right : ⊤ ⊓ U₀ ≤ U₀) a.val :=
  ⟨lbSheaf.unitIso (twoChart_isLB h _) _ (twoChart_isGen _ a 1 (by rw [map_one, _root_.mul_one])),
    (congrArg (· * rs X (inf_le_right : ⊤ ⊓ U₀ ≤ U₀) a.val)
      (map_one (rs X (inf_le_left : ⊤ ⊓ U₀ ≤ ⊤)))).trans (_root_.one_mul _)⟩

example (R : Type) [CommRing R] [Nontrivial (CommRing.Pic R)] :
    ∃ M : LB (Spec (CommRingCat.of R)), M.IsLB ∧ IsEmpty (lbSheaf M ≅ unitMod _) := by
  by_contra! h
  exact not_subsingleton (CommRing.Pic R)
    ((subsingleton_pic_iff R).2 fun M hM => (lbSheaf.triv_iff hM).2 (h M hM))

example : (∀ x, ∃ (U : (Geo.Tor.PSpace ℤ 1).Opens) (_ : x ∈ U),
      Nonempty (unitMod U.toScheme ≅ (lbSheaf (GlobalTheory.ProjSpace.O1 ℤ 1)).restrict U.ι)) ∧
    ¬ Nonempty (lbSheaf (GlobalTheory.ProjSpace.O1 ℤ 1) ≅ unitMod _) :=
  ⟨lbSheaf.exists_restrict_iso (GlobalTheory.ProjSpace.O1_isLB ℤ 1), fun h =>
    SheafModel.not_exists_gen ℤ ((lbSheaf.triv_iff (GlobalTheory.ProjSpace.O1_isLB ℤ 1)).2 h)⟩

end GlobalTheory.AbLaw
