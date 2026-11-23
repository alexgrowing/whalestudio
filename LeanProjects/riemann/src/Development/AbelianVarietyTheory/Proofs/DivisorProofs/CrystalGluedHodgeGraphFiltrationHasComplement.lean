import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrysActApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArtinianRingTsze
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.HTGlue

variable {k : Type} [Field k] {d : ℕ}

theorem crys_ext (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀)
    {e e' : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀}
    (h : ∀ c, e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c) =
      e' ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c)) : e = e' := by
  have hm := GlobalTheory.SqZeroCrys.isBC_trivSqZeroExt k (Fin d → k) A₀ hA (GlobalTheory.FODef.sqZero k (Fin d → k))
    (GlobalTheory.FODef.constMorV k (Fin d → k) A₀)
  let eqv := LinearEquiv.ofBijective _ hm
  have h1 : ∀ c, (GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c = eqv (1 ⊗ₜ c) := fun c =>
    (one_smul (TrivSqZeroExt k (Fin d → k)) ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c)).symm
  have key : e ∘ₗ eqv.toLinearMap = e' ∘ₗ eqv.toLinearMap := by
    refine TensorProduct.AlgebraTensorModule.ext fun r c => ?_
    have hr : (r ⊗ₜ c : TrivSqZeroExt k (Fin d → k) ⊗[k] primDR A₀) = r • (1 ⊗ₜ c) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hr, map_smul, ← h1, h c]
  refine LinearMap.ext fun y => ?_
  obtain ⟨t, rfl⟩ := eqv.surjective y
  exact LinearMap.congr_fun key t

theorem crys_pull_smul (A₀ : Over (Sp k)) [GrpObj A₀]
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀)
    (a : k) (c : primDR A₀) :
    e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull (a • c)) =
      TrivSqZeroExt.inl a * e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c) := by
  rw [LinearMap.map_smulₛₗ]
  exact e.map_smul (algebraMap k (TrivSqZeroExt k (Fin d → k)) a) ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c)

theorem crys_pull_add (A₀ : Over (Sp k)) [GrpObj A₀]
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀)
    (a b : primDR A₀) :
    e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull (a + b)) =
      e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull a) + e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull b) := by
  rw [LinearMap.map_add]
  exact e.map_add _ _

def fstVal (A₀ : Over (Sp k)) [GrpObj A₀]
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀) :
    HdR A₀ where
  toFun c := (e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c)).fst
  map_add' a b := by
    rw [crys_pull_add]
    rfl
  map_smul' a c := by
    rw [crys_pull_smul]
    simp

def sndVal (A₀ : Over (Sp k)) [GrpObj A₀]
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀)
    (j : Fin d) : HdR A₀ where
  toFun c := (e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c)).snd j
  map_add' a b := by
    rw [crys_pull_add]
    rfl
  map_smul' a c := by
    rw [crys_pull_smul]
    simp

def constSub (A₀ : Over (Sp k)) [GrpObj A₀] (S : Submodule k (HdR A₀)) :
    Submodule (TrivSqZeroExt k (Fin d → k))
      (Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀) where
  carrier := {e | ∃ x ∈ S, ∃ z : Fin d → HdR A₀, (∀ j, z j ∈ S) ∧
      ∀ c : primDR A₀, e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c) =
        TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (fun j => z j c)}
  add_mem' := by
    rintro e e' ⟨x, hx, z, hz, he⟩ ⟨x', hx', z', hz', he'⟩
    refine ⟨x + x', add_mem hx hx', z + z', fun j => add_mem (hz j) (hz' j), fun c => ?_⟩
    rw [LinearMap.add_apply, he c, he' c]
    ext
    · simp
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, Pi.add_apply,
        LinearMap.add_apply, zero_add, add_zero, Pi.zero_apply]
  zero_mem' := ⟨0, zero_mem _, 0, fun _ => zero_mem _, fun c => by rw [LinearMap.zero_apply]; ext <;> simp⟩
  smul_mem' := by
    rintro r e ⟨x, hx, z, hz, he⟩
    refine ⟨r.fst • x, Submodule.smul_mem _ _ hx, fun j => r.fst • z j + r.snd j • x,
      fun j => add_mem (Submodule.smul_mem _ _ (hz j)) (Submodule.smul_mem _ _ hx), fun c => ?_⟩
    rw [LinearMap.smul_apply, he c, smul_eq_mul]
    ext
    · simp
    · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
        TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, Pi.add_apply, Pi.smul_apply,
        LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, add_zero, zero_add,
        MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, Pi.zero_apply]

set_option maxHeartbeats 1000000 in

theorem mem_sup_of_coords (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀)
    (f : Fin d → (HdR A₀ →ₗ[k] HdR A₀)) (M₀ : Submodule k (HdR A₀))
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀)
    (x₁ m : HdR A₀) (hx₁ : x₁ ∈ Fil A₀) (hm : m ∈ M₀) (hxm : ∀ c, x₁ c + m c = (e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c)).fst)
    (z w : Fin d → HdR A₀) (hz : ∀ j, z j ∈ Fil A₀) (hw : ∀ j, w j ∈ M₀)
    (hzw : ∀ j c, z j c + w j c = (e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c)).snd j - f j x₁ c) :
    e ∈ glueFil A₀ f ⊔ constSub A₀ M₀ := by
  obtain ⟨g, hg⟩ := exists_coords (Fin d → k) A₀ hA
    ((Algebra.linearMap k (TrivSqZeroExt k (Fin d → k))) ∘ₗ x₁ + (TrivSqZeroExt.inrHom k (Fin d → k)) ∘ₗ
      LinearMap.pi fun j => f j x₁ + z j)
  have hgv : ∀ c, g ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c) =
      TrivSqZeroExt.inl (x₁ c) + TrivSqZeroExt.inr (fun j => (f j x₁ + z j) c) := fun c => by
    rw [hg c]; ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have hgm : g ∈ glueFil A₀ f := ⟨x₁, hx₁, z, hz, hgv⟩
  obtain ⟨h, hh⟩ := exists_coords (Fin d → k) A₀ hA
    ((Algebra.linearMap k (TrivSqZeroExt k (Fin d → k))) ∘ₗ m + (TrivSqZeroExt.inrHom k (Fin d → k)) ∘ₗ
      LinearMap.pi fun j => w j)
  have hhv : ∀ c, h ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c) =
      TrivSqZeroExt.inl (m c) + TrivSqZeroExt.inr (fun j => w j c) := fun c => by
    rw [hh c]; ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have hhm : h ∈ constSub A₀ M₀ := ⟨m, hm, w, hw, hhv⟩
  refine Submodule.mem_sup.2 ⟨g, hgm, h, hhm, crys_ext A₀ hA fun c => ?_⟩
  rw [LinearMap.add_apply, hgv c, hhv c]
  ext
  · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, hxm c]
  · rename_i j
    simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr,
      Pi.add_apply, zero_add, LinearMap.add_apply]
    linear_combination (hzw j c)

theorem isCompl_glueFil (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀)
    (f : Fin d → (HdR A₀ →ₗ[k] HdR A₀)) (M₀ : Submodule k (HdR A₀)) (hM : IsCompl (Fil A₀) M₀) :
    IsCompl (glueFil A₀ f) (constSub (d := d) A₀ M₀) := by
  constructor
  · rw [Submodule.disjoint_def]
    rintro e ⟨x, hx, z, hz, he⟩ ⟨m, hm, w, hw, he'⟩
    have hxm : x = m := LinearMap.ext fun c => by
      have := congrArg TrivSqZeroExt.fst ((he c).symm.trans (he' c))
      simpa using this
    have hx0 : x = 0 := by
      rw [← Submodule.mem_bot k, ← hM.inf_eq_bot]
      exact ⟨hx, hxm ▸ hm⟩
    have hzw : ∀ j, z j = w j := fun j => LinearMap.ext fun c => by
      have := congrFun (congrArg TrivSqZeroExt.snd ((he c).symm.trans (he' c))) j
      simpa [hx0] using this
    have hz0 : ∀ j, z j = 0 := fun j => by
      rw [← Submodule.mem_bot k, ← hM.inf_eq_bot]
      exact ⟨hz j, (hzw j) ▸ hw j⟩
    refine crys_ext A₀ hA fun c => ?_
    rw [he c, LinearMap.zero_apply]
    ext <;> simp [hx0, hz0]
  · rw [codisjoint_iff, eq_top_iff]
    rintro e -
    have hdec : ∀ u : HdR A₀, ∃ a ∈ Fil A₀, ∃ b ∈ M₀, a + b = u := fun u => by
      have hu : u ∈ Fil A₀ ⊔ M₀ := by rw [hM.sup_eq_top]; trivial
      rw [Submodule.mem_sup] at hu
      exact hu
    choose pa hpa pb hpb hpab using hdec
    exact mem_sup_of_coords A₀ hA f M₀ e _ _ (hpa _) (hpb _) (fun c => LinearMap.congr_fun (hpab (fstVal A₀ e)) c)
      (fun j => pa (sndVal A₀ e j - f j (pa (fstVal A₀ e))))
      (fun j => pb (sndVal A₀ e j - f j (pa (fstVal A₀ e)))) (fun _ => hpa _) (fun _ => hpb _)
      (fun j c => LinearMap.congr_fun (hpab (sndVal A₀ e j - f j (pa (fstVal A₀ e)))) c)

end GlobalTheory.HTGlue

open GlobalTheory.HTGlue in

theorem GlobalTheory.HTGlue.glueFil_hasCompl : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), (∀ j, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) (f j)) → (∃ M : Submodule (TrivSqZeroExt k (Fin d → k)) (Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A), IsCompl (GlobalTheory.HTGlue.glueFil o₀.A f) M) := by
  intro p _ D R _ b N _ _ k _ _ t o₀ β _ φ _ d f _
  obtain ⟨M₀, hM⟩ := Submodule.exists_isCompl (Fil o₀.A)
  exact ⟨_, isCompl_glueFil o₀.A o₀.ab f M₀ hM⟩
