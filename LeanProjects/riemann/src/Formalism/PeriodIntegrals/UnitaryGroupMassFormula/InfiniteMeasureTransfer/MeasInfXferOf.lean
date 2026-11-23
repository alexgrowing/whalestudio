import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.MeasInfCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HaarOn

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting

namespace Formalism.L2.SG.Pf.MeasInfW

abbrev HI (I : AutInst) : Type := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) I.cm.sig I.J

def IsoStep : Prop :=
  ∀ (I : AutInst) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso I),
    ∃ E : I.Ginf ≃ₜ* HI I, ∀ s, E s = Formalism.L2.SG.Pf.MeasInf.toInfL I hb s

def NStep : Prop :=
  ∀ (I : AutInst) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso I) (r : ℕ) (e f : Fin r → Fin I.n → I.E)
    (z : Fin I.n → I.E) (T : I.F), (⟨e, f, z⟩ : Formalism.L2.SG.Sub.Frame I.E I.n r).IsStd I.cm.sig I.J T →
    ∀ s : I.Ginf, Formalism.L2.SG.Pf.MeasInf.toInfL I hb s ∈ Formalism.L2.SG.Sub.Nsub (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F)
      I.cm.sig I.J (⟨e, f, z⟩ : Formalism.L2.SG.Sub.Frame I.E I.n r) ↔ s ∈ Ninf I e z

def HStep : Prop :=
  ∀ (I : AutInst) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso I) (r : ℕ) (e f : Fin r → Fin I.n → I.E)
    (z : Fin I.n → I.E),
    ∀ s : I.Ginf, Formalism.L2.SG.Pf.MeasInf.toInfL I hb s ∈ Formalism.L2.SG.Sub.Hsub (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F)
      I.cm.sig I.J (⟨e, f, z⟩ : Formalism.L2.SG.Sub.Frame I.E I.n r) ↔
      s ∈ Hset I (Set.range e ∪ Set.range f ∪ {z})

def NClosed : Prop :=
  ∀ (I : AutInst) (r : ℕ) (e : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E), IsClosed (Ninf I e z)

def HClosed : Prop := ∀ (I : AutInst) (S : Set (Fin I.n → I.E)), IsClosed (Hset I S)

section Transport

variable (I : AutInst) {H : Type} [Group H] [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H]

theorem symm_mem (E : I.Ginf ≃ₜ* H) (K : Subgroup H) (y : K) :
    E.symm y ∈ K.comap E.toMulEquiv.toMonoidHom := by
  rw [Subgroup.mem_comap]; show E (E.symm y) ∈ K; rw [ContinuousMulEquiv.apply_symm_apply]; exact y.2

def resEquiv (E : I.Ginf ≃ₜ* H) (K : Subgroup H) :
    (K.comap E.toMulEquiv.toMonoidHom) ≃ₜ K where
  toFun x := ⟨E x, x.2⟩
  invFun y := ⟨E.symm y, symm_mem I E K y⟩
  left_inv x := Subtype.ext (E.symm_apply_apply x)
  right_inv y := Subtype.ext (E.apply_symm_apply y)
  continuous_toFun := (E.continuous.comp continuous_subtype_val).subtype_mk (fun x => x.2)
  continuous_invFun := (E.symm.continuous.comp continuous_subtype_val).subtype_mk (fun y => symm_mem I E K y)

theorem resEquiv_mul (E : I.Ginf ≃ₜ* H) (K : Subgroup H) (x y : K.comap E.toMulEquiv.toMonoidHom) :
    resEquiv I E K (x * y) = resEquiv I E K x * resEquiv I E K y :=
  Subtype.ext (map_mul E (x : I.Ginf) y)

theorem transport (E : I.Ginf ≃ₜ* H) (K : Subgroup H) (S : Set I.Ginf) (hS : ∀ s, E s ∈ K ↔ s ∈ S)
    (hcl : IsClosed S) (μ : Measure I.Ginf) (hμ : IsHaarOnSet I S μ) :
    ∃ ν : Measure K, ν.IsHaarMeasure ∧ Formalism.L2.SG.Measures.amb ν = μ.map E := by
  set S' : Subgroup I.Ginf := K.comap E.toMulEquiv.toMonoidHom with hS'def
  have hSS : (S' : Set I.Ginf) = S := by
    ext s
    exact hS s
  have hcl' : IsClosed (S' : Set I.Ginf) := hSS ▸ hcl
  have hμ' : IsHaarOnSet I (S' : Set I.Ginf) μ := hSS ▸ hμ
  obtain ⟨hHaar, -, -⟩ := Formalism.L2.SG.Pf.haarOnSet_isHaar_inst I S' hcl' μ hμ'
  set μ' := μ.comap ((↑) : S' → I.Ginf) with hμ'def
  set ψ := resEquiv I E K with hψ
  have hψm : Measurable ψ := ψ.continuous.measurable
  have hψsm : Measurable ψ.symm := ψ.symm.continuous.measurable
  set Ψ : S' ≃ᵐ K := ψ.toMeasurableEquiv with hΨ
  have hcoeΨ : (Ψ : S' → K) = ψ := rfl
  refine ⟨μ'.map ψ, ?_, ?_⟩
  · have hmul : ∀ (c : K), (fun y : K => c * y) = ψ ∘ (fun x : S' => ψ.symm c * x) ∘ ψ.symm := by
      intro c
      funext y
      simp only [Function.comp_apply]
      rw [resEquiv_mul, ← hψ, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
    have hmeas : ∀ c : K, Measurable (fun y : K => c * y) := by
      intro c
      rw [hmul c]
      exact hψm.comp ((measurable_const_mul _).comp hψsm)
    refine { toIsFiniteMeasureOnCompacts := ⟨fun C hC => ?_⟩,
             toIsMulLeftInvariant := ⟨fun c => ?_⟩,
             toIsOpenPosMeasure := ψ.continuous.isOpenPosMeasure_map ψ.surjective }
    · rw [← hcoeΨ, Ψ.map_apply]
      have : (Ψ : S' → K) ⁻¹' C = ψ.symm '' C := by
        rw [hcoeΨ, Homeomorph.image_symm]
      rw [this]
      exact (hC.image ψ.symm.continuous).measure_lt_top
    · rw [Measure.map_map (hmeas c) hψm]
      have : (fun y : K => c * y) ∘ ψ = ψ ∘ (fun x : S' => ψ.symm c * x) := by
        funext x
        simp only [Function.comp_apply]
        rw [resEquiv_mul, ← hψ, Homeomorph.apply_symm_apply]
      rw [this, ← Measure.map_map hψm (measurable_const_mul _), map_mul_left_eq_self]
  · have hval : Measurable ((↑) : K → H) := measurable_subtype_coe
    have hvalS : Measurable ((↑) : S' → I.Ginf) := measurable_subtype_coe
    have hE : Measurable E := E.continuous.measurable
    show (μ'.map ψ).map ((↑) : K → H) = μ.map E
    rw [Measure.map_map hval hψm]
    have : ((↑) : K → H) ∘ ψ = E ∘ ((↑) : S' → I.Ginf) := rfl
    rw [this, ← Measure.map_map hE hvalS, hμ'def,
      Formalism.L2.SG.Pf.map_comap_subgroup S' hcl' μ hμ'.2.2.1]

end Transport

instance borelHI (I : AutInst) : BorelSpace (HI I) := ⟨rfl⟩

theorem measInfXfer_of (h1 : IsoStep) (h2 : NStep) (h3 : HStep) (h4 : NClosed) (h5 : HClosed) :
    Formalism.L2.SG.Pf.MeasInf.InfTransfer := by
  intro I hb r e f z T hstd muN muH hN hH
  obtain ⟨E, hE⟩ := h1 I hb
  obtain ⟨ν1, hν1, hamb1⟩ := transport I E _ (Ninf I e z)
    (fun s => by rw [hE]; exact h2 I hb r e f z T hstd s) (h4 I r e z) muN hN
  obtain ⟨ν2, hν2, hamb2⟩ := transport I E _ (Hset I (Set.range e ∪ Set.range f ∪ {z}))
    (fun s => by rw [hE]; exact h3 I hb r e f z s) (h5 I _) muH hH
  have hEfun : (E : I.Ginf → HI I) = Formalism.L2.SG.Pf.MeasInf.toInfL I hb := funext hE
  refine ⟨ν1, ν2, hν1, hν2, ?_, ?_⟩
  · rw [hamb1, hEfun]
  · rw [hamb2, hEfun]

end Formalism.L2.SG.Pf.MeasInfW
