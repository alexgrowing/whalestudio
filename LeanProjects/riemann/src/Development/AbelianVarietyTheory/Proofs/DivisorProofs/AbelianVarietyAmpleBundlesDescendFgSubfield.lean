import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolAVDescendsToCountableSubfield
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LbIsoDescendsToSubfieldContainingFinset
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RigidifiedSymmetricKernelTrivialDescendFieldExt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfFieldExtensionBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfAmpleGeometricFibresAbelianScheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefIntersectionNumberNonnegSubscheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlueRigidifiedLineBundlesCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.AbFGSpread

theorem sym_transfer {X Y : Scheme.{0}} {L : LB X} {N : LB Y} (hL : L.IsLB) (hN : N.IsLB) (jX : X ⟶ X)
    (jj : Y ⟶ Y) (φ : Y ⟶ X) (e : jj ≫ φ = φ ≫ jX) (hw : LBIso N (L.pull φ)) (hs : LBIso (N.pull jj) N) :
    LBIso ((L.pull jX).pull φ) (L.pull φ) := by
  have h1 : LBIso ((L.pull jX).pull φ) (L.pull (jj ≫ φ)) := by
    rw [e]; exact (FibreNef.lbIso_pull_comp hL jX φ).symm
  have h2 : LBIso (L.pull (jj ≫ φ)) ((L.pull φ).pull jj) := FibreNef.lbIso_pull_comp hL φ jj
  have h3 : LBIso ((L.pull φ).pull jj) (N.pull jj) := RigidBundleGlue.LBIso.pull hw.symm jj
  have p := fun (f : Y ⟶ X) => pull_isLB hL f
  refine LBIso.trans (pull_isLB (pull_isLB hL jX) φ) (p _) (p φ) h1 ?_
  refine LBIso.trans (p _) (pull_isLB (p φ) _) (p φ) h2 ?_
  refine LBIso.trans (pull_isLB (p φ) _) (pull_isLB hN _) (p φ) h3 ?_
  exact LBIso.trans (pull_isLB hN _) hN (p φ) hs hw

theorem sym_of_pull {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (jX : X ⟶ X) (jj : Y ⟶ Y) (φ : Y ⟶ X)
    (e : jj ≫ φ = φ ≫ jX) (hs : LBIso ((L.pull jX).pull φ) (L.pull φ)) :
    LBIso ((L.pull φ).pull jj) (L.pull φ) := by
  have p := fun {Z : Scheme.{0}} (f : Z ⟶ X) => pull_isLB hL f
  have h1 : LBIso ((L.pull φ).pull jj) (L.pull (jj ≫ φ)) := (FibreNef.lbIso_pull_comp hL φ jj).symm
  have h2 : LBIso (L.pull (jj ≫ φ)) ((L.pull jX).pull φ) := by
    rw [e]; exact FibreNef.lbIso_pull_comp hL jX φ
  refine LBIso.trans (pull_isLB (p φ) _) (p _) (p φ) h1 ?_
  exact LBIso.trans (p _) (pull_isLB (p jX) _) (p φ) h2 hs

theorem spread_to_fg_subfield : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (L M : LB A.left), L.IsLB → M.IsLB → RelAmple A L → RelAmple A M → LBIso (L.pull (GrpObj.inv : A ⟶ A).left) L → LBIso (M.pull (GrpObj.inv : A ⟶ A).left) M → ∃ (k₀ : IntermediateField ℚ K) (A₀ : Over (Sp k₀)) (_ : GrpObj A₀) (π : A.left ⟶ A₀.left) (L₀ M₀ : LB A₀.left), k₀.FG ∧ IsAbelianScheme A₀ ∧ IsGrpPullback A A₀ (spMap (algebraMap k₀ K)) π ∧ L₀.IsLB ∧ M₀.IsLB ∧ RelAmple A₀ L₀ ∧ RelAmple A₀ M₀ ∧ LBIso (L₀.pull (GrpObj.inv : A₀ ⟶ A₀).left) L₀ ∧ LBIso (M₀.pull (GrpObj.inv : A₀ ⟶ A₀).left) M₀ ∧ LBIso L (L₀.pull π) ∧ LBIso M (M₀.pull π) := by
  intro K _ _ A _ hA L M hL hM hLa hMa hLs hMs
  classical
  obtain ⟨s₀, H₀⟩ := GlobalTheory.exists_finset_isProjOver_descends K ⊥ A.left A.hom
    (GlobalTheory.ProjSpace.isProjOver_of_relAmple hLa)
  let K₀ : Subfield K := Subfield.closure (s₀ : Set K)
  obtain ⟨X₀, p₀, φ, hp₀, sq⟩ := H₀ K₀ bot_le Subfield.subset_closure
  have : IsProper p₀ := by
    obtain ⟨N, i, hi, rfl⟩ := hp₀
    have := isProper_str K₀ N
    infer_instance
  have : LocallyOfFinitePresentation p₀ := inferInstance
  have : QuasiCompact (Over.mk p₀).hom := inferInstanceAs (QuasiCompact p₀)
  have : QuasiSeparated (Over.mk p₀).hom := inferInstanceAs (QuasiSeparated p₀)
  have : LocallyOfFinitePresentation (Over.mk p₀).hom := inferInstanceAs (LocallyOfFinitePresentation p₀)
  obtain ⟨s₁, H₁⟩ := GlobalTheory.grpObj_descends_to_large_subfield K K₀ (Over.mk p₀) A φ sq
  obtain ⟨s₂, H₂⟩ := GlobalTheory.LBDescent.exists_lb_subfield K K₀ X₀ A.left p₀ A.hom φ L hL sq
  obtain ⟨s₃, H₃⟩ := GlobalTheory.LBDescent.exists_lb_subfield K K₀ X₀ A.left p₀ A.hom φ M hM sq
  let s : Finset K := s₀ ∪ s₁ ∪ s₂ ∪ s₃
  let K₁ : Subfield K := Subfield.closure (s : Set K)
  have sub : ∀ t : Finset K, t ⊆ s → (t : Set K) ⊆ K₁ := fun t ht =>
    PolCountableDescent.subset_closure_of_subset ht
  have h : K₀ ≤ K₁ := Subfield.closure_mono (Finset.coe_subset.2 (fun y hy => by simp [s, hy]))
  let inc := spMap (Subfield.inclusion h)
  let A₁ : Over (Sp K₁) := Over.mk (pullback.snd p₀ inc)
  let φ₁ : A₁.left ⟶ X₀ := pullback.fst p₀ inc
  have sq₁ : IsPullback φ₁ A₁.hom p₀ inc := IsPullback.of_hasPullback p₀ inc
  let ψ : A.left ⟶ A₁.left := sq₁.lift φ (A.hom ≫ spMap K₁.subtype)
    (by rw [Category.assoc, PolCountableDescent.spMap_subtype_comp h, sq.w])
  have hψ₁ : ψ ≫ φ₁ = φ := sq₁.lift_fst _ _ _
  have hψ₂ : ψ ≫ A₁.hom = A.hom ≫ spMap K₁.subtype := sq₁.lift_snd _ _ _
  obtain ⟨gr₁, hG⟩ := H₁ K₁ h (sub s₁ (fun y hy => by simp [s, hy])) A₁ φ₁ ψ sq₁ hψ₁ hψ₂
  obtain ⟨L₁, hL₁, hLL⟩ := H₂ K₁ h (sub s₂ (fun y hy => by simp [s, hy])) A₁.left A₁.hom φ₁ ψ sq₁ hψ₁ hψ₂
  obtain ⟨M₁, hM₁, hMM⟩ := H₃ K₁ h (sub s₃ (fun y hy => by simp [s, hy])) A₁.left A₁.hom φ₁ ψ sq₁ hψ₁ hψ₂
  obtain ⟨hab₁, -⟩ := GlobalTheory.FieldDescentAb.isAbelianScheme_and_relDim_descend K₁ K K₁.subtype A₁ A ψ hG hA
  have : IsProper A₁.hom := hab₁.proper
  have e₁ := PolDescent.inv_left_comp hG
  have symL := sym_transfer hL₁ hL _ _ ψ e₁ hLL hLs
  have symM := sym_transfer hM₁ hM _ _ ψ e₁ hMM hMs
  obtain ⟨s₄, H₄⟩ := lbIso_descends_to_subfield_containing_finset K₁ K K₁.subtype A₁ A ψ _ L₁ hG.1
    inferInstance inferInstance (pull_isLB hL₁ _) hL₁ symL
  obtain ⟨s₅, H₅⟩ := lbIso_descends_to_subfield_containing_finset K₁ K K₁.subtype A₁ A ψ _ M₁ hG.1
    inferInstance inferInstance (pull_isLB hM₁ _) hM₁ symM
  let t : Finset K := s ∪ s₄ ∪ s₅
  let k₀ : IntermediateField ℚ K := IntermediateField.adjoin ℚ (t : Set K)
  let K₂ : Subfield K := k₀.toSubfield
  have mem₂ : ∀ y ∈ t, y ∈ K₂ := fun y hy => IntermediateField.subset_adjoin ℚ (t : Set K) hy
  have h₁₂ : K₁ ≤ K₂ := Subfield.closure_le.2 (fun y hy => mem₂ y (by simp [t, Finset.mem_coe.1 hy]))
  have rng : ∀ u : Finset K, u ⊆ t → (u : Set K) ⊆ Set.range K₂.subtype := fun u hu y hy =>
    ⟨⟨y, mem₂ y (hu hy)⟩, rfl⟩
  let inc₂ := spMap (Subfield.inclusion h₁₂)
  let A₂ : Over (Sp K₂) := (Over.pullback inc₂).obj A₁
  have hP : IsGrpPullback A₂ A₁ inc₂ (pullback.fst A₁.hom inc₂) := isGrpPullback_pullback A₁ inc₂
  let χ : A₂.left ⟶ A₁.left := pullback.fst A₁.hom inc₂
  let π : A.left ⟶ A₂.left := pullback.lift ψ (A.hom ≫ spMap K₂.subtype)
    (by rw [hψ₂, Category.assoc, PolCountableDescent.spMap_subtype_comp h₁₂])
  have hπ₁ : π ≫ χ = ψ := pullback.lift_fst _ _ _
  have hπ₂ : π ≫ A₂.hom = A.hom ≫ spMap K₂.subtype := pullback.lift_snd _ _ _
  have hG₂ : IsGrpPullback A A₂ (spMap K₂.subtype) π :=
    IsGrpPullback.cancel hP (by rw [PolCountableDescent.spMap_subtype_comp h₁₂, hπ₁]; exact hG) hπ₂
  obtain ⟨hab₂, -⟩ := GlobalTheory.FieldDescentAb.isAbelianScheme_and_relDim_descend K₂ K K₂.subtype A₂ A π hG₂ hA
  have e₂ := PolDescent.inv_left_comp hP
  have symL₂ := H₄ K₂ (Subfield.inclusion h₁₂) K₂.subtype rfl (rng s₄ (fun y hy => by simp [t, hy]))
    A₂ χ hP.1
  have symM₂ := H₅ K₂ (Subfield.inclusion h₁₂) K₂.subtype rfl (rng s₅ (fun y hy => by simp [t, hy]))
    A₂ χ hP.1
  have isoL : LBIso L ((L₁.pull χ).pull π) := by
    refine LBIso.trans hL (pull_isLB hL₁ _) (pull_isLB (pull_isLB hL₁ _) _) hLL ?_
    rw [← hπ₁]; exact FibreNef.lbIso_pull_comp hL₁ χ π
  have isoM : LBIso M ((M₁.pull χ).pull π) := by
    refine LBIso.trans hM (pull_isLB hM₁ _) (pull_isLB (pull_isLB hM₁ _) _) hMM ?_
    rw [← hπ₁]; exact FibreNef.lbIso_pull_comp hM₁ χ π
  refine ⟨k₀, A₂, inferInstance, π, L₁.pull χ, M₁.pull χ, ⟨t, rfl⟩, hab₂, hG₂, pull_isLB hL₁ _,
    pull_isLB hM₁ _, ?_, ?_, sym_of_pull hL₁ _ _ χ e₂ symL₂, sym_of_pull hM₁ _ _ χ e₂ symM₂, isoL, isoM⟩
  · exact AmpleDescent.relAmple_of_fieldExtension K₂ K K₂.subtype A₂ A π _ L hab₂ hG₂ (pull_isLB hL₁ _) hL isoL hLa
  · exact AmpleDescent.relAmple_of_fieldExtension K₂ K K₂.subtype A₂ A π _ M hab₂ hG₂ (pull_isLB hM₁ _) hM isoM hMa

end GlobalTheory.AbFGSpread
