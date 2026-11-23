import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArtinianRingTsze
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTGlueOStab

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V]

theorem coord_ext (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀)
    {e e' : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀}
    (h : ∀ c, e ((GlobalTheory.FODef.constMorV k V A₀).pull c) = e' ((GlobalTheory.FODef.constMorV k V A₀).pull c)) :
    e = e' := by
  refine LinearMap.ext fun c' => ?_
  obtain ⟨u, rfl⟩ := (GlobalTheory.SqZeroCrys.isBC_trivSqZeroExt k V A₀ hA (GlobalTheory.FODef.sqZero k V)
    (GlobalTheory.FODef.constMorV k V A₀)).2 c'
  induction u using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul r c => rw [liftSemi_tmul, map_smul, map_smul, h]

theorem push_coord (A₀ : Over (Sp k)) [GrpObj A₀] (f : A₀ ⟶ A₀) [IsMonHom f]
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀)
    (c : primDR A₀) :
    push (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) f e
        ((GlobalTheory.FODef.constMorV k V A₀).pull c) =
      e ((GlobalTheory.FODef.constMorV k V A₀).pull (primPull (dp0 k) (𝟙 _) f c)) := by
  rw [push_apply]
  congr 1
  have m := (homMor (dp0 k) (𝟙 _) f).comp (GlobalTheory.FODef.constMorV k V A₀)
  exact (GrpMor.pull_pull (GlobalTheory.FODef.constMorV k V A₀) (homMor _ _ f) m (fun _ => rfl) (by simp) c).trans
    (GrpMor.pull_pull (homMor (dp0 k) (𝟙 _) f) (GlobalTheory.FODef.constMorV k V A₀) m (fun _ => rfl) rfl c).symm

theorem red_pull (A₀ : Over (Sp k)) [GrpObj A₀] (c : prim (dp0 k) (𝟙 _) A₀) :
    (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k V)) rfl A₀).pull
      ((GlobalTheory.FODef.constMorV k V A₀).pull c) = c := by
  rw [GrpMor.pull_pull _ _ (homMor (dp0 k) (𝟙 _) (𝟙 A₀)) (fun r => rfl) (by simp)]
  exact Subtype.ext (IsMor.pullCohomologyOne_id _ c.1)

theorem eq_of_surj {K C : Type} [Field K] [CommRing C] [Algebra K C] {M M' : Type*} [AddCommGroup M]
    [Module K M] [AddCommGroup M'] [Module C M'] (P : M →ₛₗ[algebraMap K C] M')
    (hP : Function.Surjective (liftSemi P)) (π : C →+* K)
    (Q : M' →ₛₗ[π] M) (e : M' →ₗ[C] C) (y : M →ₗ[K] K) (hQ : ∀ c, Q (P c) = c)
    (he : ∀ c, π (e (P c)) = y c) (c' : M') : y (Q c') = π (e c') := by
  obtain ⟨u, rfl⟩ := hP c'
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => rw [map_add, map_add, map_add, map_add, map_add, hu, hv]
  | tmul r c =>
    rw [liftSemi_tmul, LinearMap.map_smulₛₗ, hQ, map_smul, map_smul, smul_eq_mul, smul_eq_mul, map_mul, he]

theorem corr_of_fst (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀)
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀)
    (y : HdR A₀) (hc : ∀ c, (TrivSqZeroExt.fstHom k k V).toRingHom
      (e ((GlobalTheory.FODef.constMorV k V A₀).pull c)) = y c) :
    (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k V)) rfl A₀).Corr e y :=
  eq_of_surj _ (GlobalTheory.SqZeroCrys.isBC_trivSqZeroExt k V A₀ hA (GlobalTheory.FODef.sqZero k V)
    (GlobalTheory.FODef.constMorV k V A₀)).2 _ _ e y (red_pull A₀) hc

theorem eps_smul_eq {k : Type} [Field k] (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀) (y : HdR A₀)
    (w e₃ : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀)
    (hw : ∀ c, w ((GlobalTheory.FODef.constMorV k k A₀).pull c) = (Algebra.linearMap k (TrivSqZeroExt k k) ∘ₗ y) c)
    (hy : ∀ c, e₃ ((GlobalTheory.FODef.constMorV k k A₀).pull c) = TrivSqZeroExt.inr (y c)) :
    (TrivSqZeroExt.inr 1 : TrivSqZeroExt k k) • w = e₃ := by
  refine coord_ext A₀ hA fun c => ?_
  have e1 : ((TrivSqZeroExt.inr 1 : TrivSqZeroExt k k) • w) ((GlobalTheory.FODef.constMorV k k A₀).pull c) =
      (TrivSqZeroExt.inr 1 : TrivSqZeroExt k k) * (w ((GlobalTheory.FODef.constMorV k k A₀).pull c)) := rfl
  rw [e1, hw c, hy c]
  ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem exists_smul_eq_of_isCompl {C X : Type*} [CommRing C] [AddCommGroup X] [Module C X] {E M : Submodule C X}
    (hEM : IsCompl E M) (ε : C) {w e₃ : X} (h1 : ε • w = e₃) (he₃ : e₃ ∈ E) : ∃ a ∈ E, ε • a = e₃ := by
  have hw : w ∈ E ⊔ M := by rw [hEM.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨a, ha, m, hm, rfl⟩ := Submodule.mem_sup.1 hw
  have h4 : ε • m = e₃ - ε • a := by rw [← h1, smul_add]; abel
  have hmE : ε • m ∈ E := h4 ▸ E.sub_mem he₃ (E.smul_mem ε ha)
  have h2 : ε • m = 0 := (Submodule.disjoint_def.1 hEM.disjoint) _ hmE (M.smul_mem ε hm)
  exact ⟨a, ha, by rw [← h1, smul_add, h2, add_zero]⟩

theorem fil_of_eps (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀)
    (E M : Submodule (TrivSqZeroExt k k)
      (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀))
    (hEM : IsCompl E M)
    (hred : ∀ y : HdR A₀, y ∈ Fil A₀ ↔
      ∃ e ∈ E, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k k)) rfl A₀).Corr e y)
    {e₃ : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀}
    (he₃ : e₃ ∈ E) (y : HdR A₀)
    (hy : ∀ c, e₃ ((GlobalTheory.FODef.constMorV k k A₀).pull c) = TrivSqZeroExt.inr (y c)) : y ∈ Fil A₀ := by
  obtain ⟨w, hw⟩ := GlobalTheory.HTGlue.exists_coords k A₀ hA (Algebra.linearMap k (TrivSqZeroExt k k) ∘ₗ y)
  obtain ⟨a, ha, h1⟩ := exists_smul_eq_of_isCompl hEM _ (eps_smul_eq A₀ hA y w e₃ hw hy) he₃
  refine (hred y).2 ⟨a, ha, corr_of_fst A₀ hA a y fun c => ?_⟩
  have h3 := congrArg (fun u => (u ((GlobalTheory.FODef.constMorV k k A₀).pull c)).snd) h1
  have e1 : ((TrivSqZeroExt.inr 1 : TrivSqZeroExt k k) • a) ((GlobalTheory.FODef.constMorV k k A₀).pull c) =
      (TrivSqZeroExt.inr 1 : TrivSqZeroExt k k) * (a ((GlobalTheory.FODef.constMorV k k A₀).pull c)) := rfl
  simp only [e1, hy c] at h3
  simpa using h3

theorem glueFil_stable : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] [IsAlgClosed k] (tk : R →+* k) (s : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s), s = spMap tk → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), ∀ (E' : Fin d → Submodule (TrivSqZeroExt k k) (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A)), (∀ j, ∃ M : Submodule (TrivSqZeroExt k k) (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A), IsCompl (E' j) M) → (∀ j, ∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ e ∈ E' j, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k k)) rfl o₀.A).Corr e y) → (∀ j, ∀ x ∈ Fil o₀.A, ∃ e ∈ E' j, ∀ c, e ((GlobalTheory.FODef.constMorV k k o₀.A).pull c) = TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (f j x c)) → (∀ j (c : D.O), ∀ e ∈ E' j, (haveI := o₀.act.hom (c); push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (o₀.act.act (c)) (e)) ∈ E' j) → ∀ (c : D.O), ∀ e ∈ GlobalTheory.HTGlue.glueFil o₀.A f, (haveI := o₀.act.hom (c); push (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) (o₀.act.act (c)) (e)) ∈ GlobalTheory.HTGlue.glueFil o₀.A f := by
  intro p _ D R _ b N k _ _ tk s o₀ _ d f E' hcompl hred hlift hstab c e he
  obtain ⟨x, hx, z, hz, hze⟩ := he
  haveI := o₀.act.hom c
  have key : ∀ j, ∀ x ∈ Fil o₀.A, push (dp0 k) (𝟙 _) (o₀.act.act c) (f j x) -
      f j (push (dp0 k) (𝟙 _) (o₀.act.act c) x) ∈ Fil o₀.A := by
    intro j x hx
    obtain ⟨M, hM⟩ := hcompl j
    obtain ⟨e1, he1, hc1⟩ := hlift j x hx
    obtain ⟨e2, he2, hc2⟩ := hlift j _ (push_mem_Fil (o₀.act.act c) hx)
    refine fil_of_eps o₀.A o₀.ab (E' j) M hM (hred j) (sub_mem (hstab j c e1 he1) he2) _ fun c' => ?_
    rw [LinearMap.sub_apply, push_coord, hc1, hc2]
    ext <;> simp [push_apply]
  refine ⟨_, push_mem_Fil (o₀.act.act c) hx, fun j => push (dp0 k) (𝟙 _) (o₀.act.act c) (f j x) -
      f j (push (dp0 k) (𝟙 _) (o₀.act.act c) x) + push (dp0 k) (𝟙 _) (o₀.act.act c) (z j),
    fun j => add_mem (key j x hx) (push_mem_Fil _ (hz j)), fun c' => ?_⟩
  rw [push_coord, hze]
  ext
  · simp [push_apply]
  · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, Pi.add_apply,
      LinearMap.add_apply, LinearMap.sub_apply, push_apply]
    ring

end GlobalTheory.HTGlueOStab
