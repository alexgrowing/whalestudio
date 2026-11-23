import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SubSplit
import Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.AdelicCoordinatesEvalZeroFormMemAdmissible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationDarbouxChangeIntertwine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerPreservesAdelicSchwartz

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

variable {F : Type} [Field F] [NumberField F]

theorem slice0_box {κ' κ'' : Type} (φ' : (κ' → AF F) → ℂ) (φ₁ : (κ'' → AF F) → ℂ) :
    slice0 κ' κ'' (boxFun φ' φ₁) = φ₁ 0 • φ' := by
  funext x
  simp [slice0, boxFun, mul_comm]

theorem slice0_box_one {κ' κ'' : Type} (φ' : (κ' → AF F) → ℂ) {φ₁ : (κ'' → AF F) → ℂ} (h : φ₁ 0 = 1) :
    slice0 κ' κ'' (boxFun φ' φ₁) = φ' := by
  rw [slice0_box, h, one_smul]

theorem schr_box {κ' κ'' : Type} [Fintype κ'] [Fintype κ''] (ψ : AddChar (AF F) ℂ) (p : (κ' → AF F) × (κ' → AF F))
    (φ' : (κ' → AF F) → ℂ) (φ₀ : (κ'' → AF F) → ℂ) :
    schr ψ (Sum.elim p.1 (0 : κ'' → AF F), Sum.elim p.2 (0 : κ'' → AF F)) (boxFun φ' φ₀) = boxFun (schr ψ p φ') φ₀ := by
  funext x
  simp only [schr, boxFun, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Pi.zero_apply, mul_zero, add_zero, Function.comp_apply, Pi.add_apply]
  have h1 : (x + Sum.elim p.1 (0 : κ'' → AF F)) ∘ Sum.inl = x ∘ Sum.inl + p.1 := by
    funext i; simp
  have h2 : (x + Sum.elim p.1 (0 : κ'' → AF F)) ∘ Sum.inr = x ∘ Sum.inr := by
    funext i; simp
  rw [h1, h2]
  simp only [Function.comp_apply, mul_assoc, Finset.sum_const_zero, add_zero]

theorem subSplit_of : SliceFacts → SubSplit := by
  intro hSF F _ _ ψ hψ κ' κ'' _ _ W W' _ _ _ _ B B' dd dd' emb hemb G G' _ _ _ _ act act' j hj
    hact om om' hom φ₀ hφ₀ h0 hn hg
  obtain ⟨hsl, hadm, -, hmeas⟩ := hSF F κ' κ''
  have key : ∀ g : G', ∀ φ ∈ schA F κ', om' g φ = slice0 κ' κ'' (om (j g) (boxFun φ φ₀)) := by
    intro g φ hφ
    obtain ⟨φ₁, -, h1, -, hbox⟩ := hg g
    rw [hbox φ hφ, slice0_box_one _ h1]
  have hbx : ∀ φ ∈ schA F κ', boxFun φ φ₀ ∈ schA F (κ' ⊕ κ'') := fun φ hφ =>
    GlobalTheory.SchwartzBox.boxFun_mem_schA F κ' κ'' φ hφ φ₀ hφ₀
  have pres : ∀ g : G', ∀ φ ∈ schA F κ', om' g φ ∈ schA F κ' := by
    intro g φ hφ
    rw [key g φ hφ]
    exact hsl _ (hom.pres (j g) _ (hbx φ hφ))
  refine ⟨⟨pres, ?_, ?_⟩, ?_, ?_⟩
  · intro g w' φ hφ
    obtain ⟨φ₁, hφ₁, h1, -, hbox⟩ := hg g
    have hs : Darboux.rho dd' ψ w' φ ∈ schA F κ' :=
      GlobalTheory.SchrKeepsSchA.schr_mem_schA F ψ hψ κ' _ φ hφ
    rw [key g _ hs]
    have e1 : boxFun (Darboux.rho dd' ψ w' φ) φ₀ = Darboux.rho dd ψ (emb w') (boxFun φ φ₀) := by
      simp only [Darboux.rho]
      rw [hemb w', schr_box]
    rw [e1, hom.impl (j g) (emb w') _ (hbx φ hφ), hact g w', hbox φ hφ]
    simp only [Darboux.rho]
    rw [hemb, schr_box, slice0_box_one _ h1]
  · intro g l hl
    have hL : ((l ∘ₗ slice0 κ' κ'') ∘ₗ om (j g)) ∘ₗ PositivityTheory.ThKF0.Chr.boxL κ' φ₀ ∈
        (adeleClass F).adm κ' :=
      PositivityTheory.ThKF0.Chr.box_adm κ' κ'' φ₀ hφ₀ _ (hom.adm (j g) _ (hadm l hl))
    intro g0 hg0
    obtain ⟨T, hT⟩ := hL g0 hg0
    refine ⟨T, fun f => ?_⟩
    rw [← hT f]
    have hm : pureA F (⇑f) g0 ∈ schA F κ' := Submodule.subset_span ⟨f, g0, hg0, rfl⟩
    simp only [LinearMap.comp_apply]
    rw [key g _ hm]
    rfl
  · intro μ' hμ' g φ hφ
    obtain ⟨φ₁, hφ₁, h1, hn1, hbox⟩ := hg g
    letI : MeasurableSpace (κ'' → AF F) := borel _
    haveI : BorelSpace (κ'' → AF F) := ⟨rfl⟩
    obtain ⟨μ'', hμ''⟩ : ∃ μ'' : Measure (κ'' → AF F), μ''.IsAddHaarMeasure :=
      ⟨Measure.addHaar, inferInstance⟩
    obtain ⟨μ, hμ, hprod⟩ := hmeas μ' μ'' hμ' hμ''
    have hp1 := hprod (om' g φ) (pres g φ hφ) φ₁ hφ₁
    have hp0 := hprod φ hφ φ₀ hφ₀
    rw [← hbox φ hφ, hom.unit μ hμ (j g) _ (hbx φ hφ), hp0, hn1 μ'' hμ''] at hp1
    obtain ⟨hne, hnt⟩ := hn μ'' hμ''
    exact ((ENNReal.mul_left_inj hne hnt).mp hp1).symm
  · intro l hl φ hφ
    have hc := hom.cont (l ∘ₗ slice0 κ' κ'') (hadm l hl) _ (hbx φ hφ)
    have e2 : (fun g : G' => l (om' g φ)) =
        (fun h : G => (l ∘ₗ slice0 κ' κ'') (om h (boxFun φ φ₀))) ∘ j := by
      funext g
      simp only [Function.comp_apply, LinearMap.comp_apply]
      rw [key g φ hφ]
    rw [e2]
    exact hc.comp hj

end PositivityTheory.SiegelWeilFormula.Ald

end
