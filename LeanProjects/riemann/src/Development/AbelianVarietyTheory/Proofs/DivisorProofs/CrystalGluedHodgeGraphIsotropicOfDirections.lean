import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArtinianRingTsze
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationIffReductionGluedFilHtObject
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPairingSkewHodgeLagrangian
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HTGlueIso

open GlobalTheory.AbDual

variable {k : Type} [Field k]

theorem fil_isotropic_of_isCorrForm (A : Over (Sp k)) [GrpObj A] (hA : IsAbelianScheme A) (P : LB (A ⊗ A).left)
    (hP : P.IsLB) (φ : HdR A →ₗ[k] HdR A →ₗ[k] k) (hφ : IsCorrForm (dp0 k) (𝟙 _) A A P φ) :
    ∀ x ∈ Fil A, ∀ y ∈ Fil A, φ x y = 0 := by
  have H := GlobalTheory.abelianDeRham
  obtain ⟨g, hg⟩ := GlobalTheory.AbVarRelDim.exists_relDim k A hA
  have hAB := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have gAB := smooth_prod hg hg
  obtain ⟨ψ, hψ, e⟩ := hφ.isPolForm
  obtain ⟨iso, -⟩ := H.2.2.2.2 k _ _ hAB gAB P hP ψ hψ
  intro x hx y hy
  have a₁ : push (dp0 k) (𝟙 _) (fst A A) (push (dp0 k) (𝟙 _) (inl A A) x) = x := by
    rw [push_push _ _ _ (lift_fst _ _), push_id]; rfl
  have a₂ : push (dp0 k) (𝟙 _) (snd A A) (push (dp0 k) (𝟙 _) (inl A A) x) = 0 := by
    rw [push_push _ _ _ (lift_snd _ _), push_one]; rfl
  have b₁ : push (dp0 k) (𝟙 _) (fst A A) (push (dp0 k) (𝟙 _) (inr A A) y) = 0 := by
    rw [push_push _ _ _ (lift_fst _ _), push_one]; rfl
  have b₂ : push (dp0 k) (𝟙 _) (snd A A) (push (dp0 k) (𝟙 _) (inr A A) y) = y := by
    rw [push_push _ _ _ (lift_snd _ _), push_id]; rfl
  have key : φ x y = ψ (push (dp0 k) (𝟙 _) (inl A A) x) (push (dp0 k) (𝟙 _) (inr A A) y) := by
    rw [e, a₁, a₂, b₁, b₂]; simp
  rw [key]
  exact iso _ (push_mem_Fil _ hx) _ (push_mem_Fil _ hy)

variable {d : ℕ}

def proj (j : Fin d) : TrivSqZeroExt k (Fin d → k) →+* TrivSqZeroExt k k :=
  (TrivSqZeroExt.map (LinearMap.proj (R := k) (φ := fun _ : Fin d => k) j)).toRingHom

@[simp] theorem fst_proj (j : Fin d) (a : TrivSqZeroExt k (Fin d → k)) : (proj j a).fst = a.fst := by
  simp [proj]

@[simp] theorem snd_proj (j : Fin d) (a : TrivSqZeroExt k (Fin d → k)) : (proj j a).snd = a.snd j := by
  simp [proj]

theorem projMor (A₀ : Over (Sp k)) [GrpObj A₀] (j : Fin d) :
    GrpMor (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀
      (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀ (proj j) (𝟙 _)
      (Over.Hom.left (𝟙 A₀)) :=
  GrpMor.of_hom (isDPMorphism_sqDP _ _ _ fun a ha => by
      rw [RingHom.mem_ker] at ha ⊢
      change (proj j a).fst = 0
      rw [fst_proj]; exact ha)
    (by
      rw [← GlobalTheory.Cris.spMap_comp]
      congr 1
      ext a <;> simp) (𝟙 A₀)

theorem eq_of_liftSemi_surj' {K C C' : Type} [Field K] [CommRing C] [CommRing C'] [Algebra K C] {M M' M'' : Type*}
    [AddCommGroup M] [Module K M] [AddCommGroup M'] [Module C M'] [AddCommGroup M''] [Module C' M'']
    (P : M →ₛₗ[algebraMap K C] M') (hP : Function.Surjective (liftSemi P)) (σ : C →+* C')
    (Q : M' →ₛₗ[σ] M'') (P' : M → M'') (hQ : ∀ c, Q (P c) = P' c) (x : M' →ₗ[C] C) (x' : M'' →ₗ[C'] C')
    (h : ∀ c, x' (P' c) = σ (x (P c))) (c : M') : x' (Q c) = σ (x c) := by
  obtain ⟨u, rfl⟩ := hP c
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => rw [map_add, map_add, map_add, map_add, map_add, hu, hv]
  | tmul r c =>
    rw [liftSemi_tmul, LinearMap.map_smulₛₗ, map_smul, map_smul, hQ, h, smul_eq_mul, smul_eq_mul, map_mul]

theorem projMor_corr (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀) (j : Fin d)
    (x : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀)
    (x' : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀)
    (h : ∀ c, x' ((GlobalTheory.FODef.constMorV k k A₀).pull c) = proj j (x ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c))) :
    (projMor A₀ j).Corr x x' :=
  eq_of_liftSemi_surj' _ (GlobalTheory.SqZeroCrys.isBC_trivSqZeroExt k (Fin d → k) A₀ hA (GlobalTheory.FODef.sqZero k (Fin d → k))
    (GlobalTheory.FODef.constMorV k (Fin d → k) A₀)).2 (proj j) (projMor A₀ j).pull _
    (fun c => GrpMor.pull_pull (GlobalTheory.FODef.constMorV k (Fin d → k) A₀) (projMor A₀ j) (GlobalTheory.FODef.constMorV k k A₀)
      (fun r => by ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]) (by simp) c) x x' h

theorem exists_red_form (A₀ : Over (Sp k)) [GrpObj A₀] (P : LB (A₀ ⊗ A₀).left) (hP : P.IsLB)
    (φ : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀ →ₗ[TrivSqZeroExt k (Fin d → k)]
      Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀ →ₗ[TrivSqZeroExt k (Fin d → k)]
        TrivSqZeroExt k (Fin d → k))
    (hφ : IsCorrForm (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom)
      A₀ A₀ P φ) :
    ∃ φ₀ : HdR A₀ →ₗ[k] HdR A₀ →ₗ[k] k, IsCorrForm (dp0 k) (𝟙 _) A₀ A₀ P φ₀ ∧
      ∀ x x' y y', (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) rfl A₀).Corr x x' →
        (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) rfl A₀).Corr y y' →
        φ₀ x' y' = (φ x y).fst :=
  hφ.pull hP (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) rfl A₀)
    (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) rfl A₀)
    (h := 𝟙 _) ((Category.id_comp _).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (Category.comp_id _).symm) hP (GlobalTheory.lbIso_pull_id hP)

theorem exists_proj_form (A₀ : Over (Sp k)) [GrpObj A₀] (P : LB (A₀ ⊗ A₀).left) (hP : P.IsLB) (j : Fin d)
    (φ : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀ →ₗ[TrivSqZeroExt k (Fin d → k)]
      Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀ →ₗ[TrivSqZeroExt k (Fin d → k)]
        TrivSqZeroExt k (Fin d → k))
    (hφ : IsCorrForm (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom)
      A₀ A₀ P φ) :
    ∃ φ' : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀ →ₗ[TrivSqZeroExt k k]
        Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀ →ₗ[TrivSqZeroExt k k]
          TrivSqZeroExt k k,
      IsCorrForm (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀ A₀ P φ' ∧
      ∀ x x' y y', (projMor A₀ j).Corr x x' → (projMor A₀ j).Corr y y' → φ' x' y' = proj j (φ x y) :=
  hφ.pull hP (projMor A₀ j) (projMor A₀ j) (h := 𝟙 _) ((Category.id_comp _).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (Category.comp_id _).symm) hP (GlobalTheory.lbIso_pull_id hP)

theorem exists_mem_of_fil (A₀ : Over (Sp k)) [GrpObj A₀] (g : HdR A₀ →ₗ[k] HdR A₀)
    (E : Submodule (TrivSqZeroExt k k)
      (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀))
    (hE : ∀ x ∈ Fil A₀, ∃ e ∈ E, ∀ c, e ((GlobalTheory.FODef.constMorV k k A₀).pull c) =
      TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (g x c))
    {x z : HdR A₀} (hx : x ∈ Fil A₀) (hz : z ∈ Fil A₀) :
    ∃ e ∈ E, ∀ c, e ((GlobalTheory.FODef.constMorV k k A₀).pull c) =
      TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr ((g x + z) c) := by
  obtain ⟨e₁, h₁, he₁⟩ := hE x hx
  obtain ⟨e₂, h₂, he₂⟩ := hE z hz
  refine ⟨e₁ + (TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) • e₂, add_mem h₁ (E.smul_mem _ h₂), fun c => ?_⟩
  rw [LinearMap.add_apply, LinearMap.smul_apply, he₁, he₂, smul_eq_mul]
  ext <;> simp

theorem glueFil_isotropic : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] [IsAlgClosed k] (tk : R →+* k) (s : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s), s = spMap tk → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), ∀ (E' : Fin d → Submodule (TrivSqZeroExt k k) (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A)), (∀ j, ∃ M : Submodule (TrivSqZeroExt k k) (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A), IsCompl (E' j) M) → (∀ j, ∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ e ∈ E' j, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k k)) rfl o₀.A).Corr e y) → (∀ j, ∀ x ∈ Fil o₀.A, ∃ e ∈ E' j, ∀ c, e ((GlobalTheory.FODef.constMorV k k o₀.A).pull c) = TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (f j x c)) → (∀ j (c : D.O), ∀ e ∈ E' j, (haveI := o₀.act.hom (c); push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (o₀.act.act (c)) (e)) ∈ E' j) → (∀ j, ∀ φ : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A →ₗ[TrivSqZeroExt k k] Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A →ₗ[TrivSqZeroExt k k] TrivSqZeroExt k k, GlobalTheory.AbDual.IsCorrForm (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A o₀.A o₀.P φ → ∀ x ∈ E' j, ∀ y ∈ E' j, φ x y = 0) → ∀ φ : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A →ₗ[TrivSqZeroExt k (Fin d → k)] Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A →ₗ[TrivSqZeroExt k (Fin d → k)] TrivSqZeroExt k (Fin d → k), GlobalTheory.AbDual.IsCorrForm (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A o₀.A o₀.P φ → ∀ x ∈ GlobalTheory.HTGlue.glueFil o₀.A f, ∀ y ∈ GlobalTheory.HTGlue.glueFil o₀.A f, φ x y = 0 := by
  intro p _ D R _ b N k _ _ tk s o₀ _ d f E' _ _ h3 _ h5 φ hφ x hx y hy
  obtain ⟨x₀, hx₀, zx, hzx, hxc⟩ := hx
  obtain ⟨y₀, hy₀, zy, hzy, hyc⟩ := hy
  have t₀ := exists_red_form (k := k) (d := d) o₀.A o₀.P o₀.isLB φ hφ
  obtain ⟨φ₀, hφ₀, e₀⟩ := t₀
  have hfst : (φ x y).fst = 0 := by
    have cx := GlobalTheory.HTGlue.corr_of_fst o₀.A o₀.ab x x₀ fun c => by rw [hxc c]; simp
    have cy := GlobalTheory.HTGlue.corr_of_fst o₀.A o₀.ab y y₀ fun c => by rw [hyc c]; simp
    rw [← e₀ x x₀ y y₀ cx cy]
    exact fil_isotropic_of_isCorrForm o₀.A o₀.ab o₀.P o₀.isLB φ₀ hφ₀ x₀ hx₀ y₀ hy₀
  have hsnd : ∀ j, (φ x y).snd j = 0 := by
    intro j
    have t₁ := exists_proj_form (k := k) (d := d) o₀.A o₀.P o₀.isLB j φ hφ
    obtain ⟨φ', hφ', e'⟩ := t₁
    have t₂ := exists_mem_of_fil o₀.A (f j) (E' j) (h3 j) hx₀ (hzx j)
    obtain ⟨x', hx', hx'c⟩ := t₂
    have t₃ := exists_mem_of_fil o₀.A (f j) (E' j) (h3 j) hy₀ (hzy j)
    obtain ⟨y', hy', hy'c⟩ := t₃
    have cx := projMor_corr o₀.A o₀.ab j x x' fun c => by
      rw [hx'c c, hxc c]; ext <;> simp
    have cy := projMor_corr o₀.A o₀.ab j y y' fun c => by
      rw [hy'c c, hyc c]; ext <;> simp
    have e := e' x x' y y' cx cy
    have h0 : φ' x' y' = 0 := h5 j φ' hφ' x' hx' y' hy'
    have e2 : proj j (φ x y) = 0 := e.symm.trans h0
    have e3 : (proj j (φ x y)).snd = (0 : TrivSqZeroExt k k).snd := congrArg TrivSqZeroExt.snd e2
    rw [snd_proj] at e3
    exact e3
  exact TrivSqZeroExt.ext hfst (funext hsnd)

end GlobalTheory.HTGlueIso
