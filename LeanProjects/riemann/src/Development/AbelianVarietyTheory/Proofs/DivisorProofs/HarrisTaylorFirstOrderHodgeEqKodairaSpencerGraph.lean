import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrysActApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFiltrationLiftDeterminesModFil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerUniqueValueAbelianSchemeField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorFirstOrderDeformationSkewStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieConditionHodgeSubspaceConstantLiftMemFilStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section
namespace GlobalTheory.HTNecessary

variable {k : Type} [Field k] {A₀ : Over (Sp k)} [GrpObj A₀] {A' : Over (Sp (DualNumber k))} [GrpObj A']
  {i : A₀.left ⟶ A'.left} {h : IsGrpPullback A₀ A' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) i}

theorem isFilLift_add {x y x' y' : HdR A₀} (e : IsFilLift h x y) (e' : IsFilLift h x' y') :
    IsFilLift h (x + x') (y + y') := by
  obtain ⟨d, hd, e⟩ := e
  obtain ⟨d', hd', e'⟩ := e'
  refine ⟨d + d', add_mem hd hd', fun c ↦ ?_⟩
  rw [LinearMap.add_apply, e, e']
  ext <;> simp

theorem isFilLift_smul {x y : HdR A₀} (e : IsFilLift h x y) (r : k) :
    IsFilLift h (r • x) (r • y) := by
  obtain ⟨d, hd, e⟩ := e
  refine ⟨algebraMap k (DualNumber k) r • d, Submodule.smul_mem _ _ hd, fun c ↦ ?_⟩
  rw [LinearMap.smul_apply, e]
  ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem isFilLift_zero : IsFilLift h (0 : HdR A₀) 0 :=
  ⟨0, zero_mem _, fun c ↦ by
    simp only [LinearMap.zero_apply, TrivSqZeroExt.inl_zero, TrivSqZeroExt.inr_zero, add_zero]⟩

theorem isFilLift_push (f₀ : A₀ ⟶ A₀) (f : A' ⟶ A') [IsMonHom f₀] [IsMonHom f] (e : i ≫ f.left = f₀.left ≫ i)
    {x y : HdR A₀} (hxy : IsFilLift h x y) :
    IsFilLift h (push (dp0 k) (𝟙 _) f₀ x) (push (dp0 k) (𝟙 _) f₀ y) := by
  obtain ⟨d, hd, e'⟩ := hxy
  have hmem := push_mem_liftFil (epsDP k) h h f₀ f e hd
  refine ⟨_, hmem, fun c ↦ ?_⟩
  have k1 := (homMor (dp0 k) (𝟙 _) f₀).comp (constMor A₀)
  have e1 := GrpMor.pull_pull (constMor A₀) (homMor (epsDP k) _ f₀) k1 (fun _ ↦ rfl) (by simp) c
  have e2 := GrpMor.pull_pull (homMor (dp0 k) (𝟙 _) f₀) (constMor A₀) k1 (fun _ ↦ rfl) rfl c
  rw [push_apply]
  show d (primPull _ _ f₀ _) = _
  erw [primPull, e1, ← e2, e']
  rfl

theorem exists_isFilLift (hA' : IsAbelianScheme A') {x : HdR A₀} (hx : x ∈ Fil A₀) : ∃ y, IsFilLift h x y := by
  obtain ⟨g, hg⟩ := GlobalTheory.KSGraph.exists_dim A' hA'
  obtain ⟨v, ⟨y, hy, -⟩, -⟩ := GlobalTheory.DeRham.ksRegular_of_isAbelianScheme GlobalTheory.T.abelianScheme_firstDeRham_structure h hA' hg x hx
  exact ⟨y, hy⟩

theorem main : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∃ g : HdR o₀.A →ₗ[k] HdR o₀.A, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) g ∧ ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (g x) := by
  intro p _ D R _ b N _ _ k _ _ t o₀ β hβ φ hφ o' m'
  have hab₀ := o₀.ab
  have hab' := o'.ab
  have hL1 : ∀ x ∈ Fil o₀.A, ∃ y, IsFilLift m'.cart x y := fun x hx ↦ exists_isFilLift hab' hx
  have hG := GlobalTheory.KSGraph.isFilLift_iff_sub_mem k o₀.A o'.A m'.φ m'.cart hab'
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (Fil o₀.A)
  let bs := Module.Basis.ofVectorSpace k (Fil o₀.A)
  let f : Fil o₀.A →ₗ[k] HdR o₀.A := bs.constr k fun j ↦ (hL1 _ (bs j).2).choose
  have hf : ∀ x : Fil o₀.A, IsFilLift m'.cart x.1 (f x) := by
    intro x
    have hx : x ∈ Submodule.span k (Set.range bs) := by rw [bs.span_eq]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rw [Module.Basis.constr_basis]
      exact (hL1 _ (bs j).2).choose_spec
    | zero => simpa using isFilLift_zero
    | add x y _ _ hx hy => simpa using isFilLift_add hx hy
    | smul r x _ hx => simpa using isFilLift_smul hx r
  let g : HdR o₀.A →ₗ[k] HdR o₀.A := f ∘ₗ Submodule.linearProjOfIsCompl _ _ hC
  have hg : ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (g x) := fun x hx ↦ by
    have : Submodule.linearProjOfIsCompl _ _ hC x = ⟨x, hx⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hC ⟨x, hx⟩
    simpa [g, this] using hf ⟨x, hx⟩
  refine ⟨g, ⟨fun a x hx ↦ ?_, fun z hz ↦ ?_, fun x hx y hy ↦ ?_⟩, hg⟩
  · haveI := o₀.act.hom a
    haveI := o'.act.hom a
    have hax : GlobalTheory.HTCount.crysAct o₀ a x ∈ Fil o₀.A := by
      rw [GlobalTheory.HTCount.crysAct_apply]; exact push_mem_Fil _ hx
    have e1 : IsFilLift m'.cart (GlobalTheory.HTCount.crysAct o₀ a x) (GlobalTheory.HTCount.crysAct o₀ a (g x)) := by
      rw [GlobalTheory.HTCount.crysAct_apply]
      exact isFilLift_push (o₀.act.act a) (o'.act.act a) (m'.act a).symm (hg x hx)
    exact (hG _ hax _ _ e1).1 (hg _ hax)
  · obtain ⟨hz₀, hz⟩ := GlobalTheory.T.lieConditionHodgeSubspace_constant_lift_mem_fil p D R b N k t o₀ β hβ o' m' z hz
    simpa using (hG _ hz₀ _ _ hz).1 (hg _ hz₀)
  · exact GlobalTheory.T.harrisTaylor_firstOrder_deformation_skew p D R b N k t o₀ φ hφ o' m' x hx y hy _ _ (hg x hx) (hg y hy)

end GlobalTheory.HTNecessary
