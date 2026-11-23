import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PPrAdm

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.LevelTypeProj PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.AdmDiscPf

variable {E : Type} [Field E] {n : ℕ}

variable (E n) in

def contK : Submodule ℂ (Kinf E n → ℂ) where
  carrier := {f | Continuous f}
  add_mem' := fun hf hg => hf.add hg
  zero_mem' := continuous_zero
  smul_mem' := fun c _ hf => hf.const_smul c

def lI (X : Submodule ℂ (Kinf E n → ℂ)) : Submodule ℂ (Kinf E n → ℂ) :=
  ⨅ k₀ : Kinf E n, X.comap (LinearMap.funLeft ℂ ℂ (fun k => k₀ * k))

theorem mem_lI {X : Submodule ℂ (Kinf E n → ℂ)} {w : Kinf E n → ℂ} :
    w ∈ lI X ↔ ∀ k₀, (fun k => w (k₀ * k)) ∈ X := by
  simp only [lI, Submodule.mem_iInf, Submodule.mem_comap]
  rfl

theorem lI_le (X : Submodule ℂ (Kinf E n → ℂ)) : lI X ≤ X := fun w hw => by
  simpa only [one_mul] using mem_lI.1 hw 1

theorem lI_left {X : Submodule ℂ (Kinf E n → ℂ)} {w : Kinf E n → ℂ} (hw : w ∈ lI X) (k₁ : Kinf E n) :
    (fun k => w (k₁ * k)) ∈ lI X :=
  mem_lI.2 fun k₀ => by simpa only [mul_assoc] using mem_lI.1 hw (k₁ * k₀)

def rS (X : Submodule ℂ (Kinf E n → ℂ)) : Submodule ℂ (Kinf E n → ℂ) :=
  Submodule.span ℂ {v | ∃ w ∈ X, ∃ k : Kinf E n, v = fun x => w (x * k)}

theorem le_rS (X : Submodule ℂ (Kinf E n → ℂ)) : X ≤ rS X := fun w hw =>
  Submodule.subset_span ⟨w, hw, 1, funext fun x => by rw [mul_one]⟩

theorem rS_right {X : Submodule ℂ (Kinf E n → ℂ)} {w : Kinf E n → ℂ} (hw : w ∈ rS X) (k : Kinf E n) :
    (fun x => w (x * k)) ∈ rS X := by
  induction hw using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨u, hu, k', rfl⟩ := hv
    exact Submodule.subset_span ⟨u, hu, k * k', funext fun x => by simp only [mul_assoc]⟩
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul a x _ hx => exact Submodule.smul_mem _ a hx

theorem fd_rS_lI (X : Submodule ℂ (Kinf E n → ℂ)) [FiniteDimensional ℂ X] : FiniteDimensional ℂ (rS (lI X)) := by
  have : FiniteDimensional ℂ (lI X) := Submodule.finiteDimensional_of_le (lI_le X)
  let Lm : Kinf E n → lI X →ₗ[ℂ] lI X := fun k₀ =>
    { toFun := fun y => ⟨fun k => y.1 (k₀ * k), lI_left y.2 k₀⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let B : Module.Dual ℂ (lI X) →ₗ[ℂ] lI X →ₗ[ℂ] (Kinf E n → ℂ) :=
    LinearMap.mk₂ ℂ (fun ℓ y => fun k₀ => ℓ (Lm k₀ y))
      (fun _ _ _ => by funext k₀; simp)
      (fun _ _ _ => by funext k₀; simp)
      (fun _ _ _ => by funext k₀; simp)
      (fun _ _ _ => by funext k₀; simp)
  have hle : rS (lI X) ≤ LinearMap.range (TensorProduct.lift B) := by
    refine Submodule.span_le.2 ?_
    rintro v ⟨w, hw, k, rfl⟩
    refine ⟨((LinearMap.proj k : (Kinf E n → ℂ) →ₗ[ℂ] ℂ).comp (lI X).subtype) ⊗ₜ ⟨w, hw⟩, ?_⟩
    rw [TensorProduct.lift.tmul]
    rfl
  exact Submodule.finiteDimensional_of_le hle

def rR (U : Submodule ℂ (Kinf E n → ℂ)) (hU : ∀ u ∈ U, ∀ k, (fun x => u (x * k)) ∈ U) :
    Representation ℂ (Kinf E n) U where
  toFun k :=
    { toFun := fun u => ⟨fun x => u.1 (x * k), hU u.1 u.2 k⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := LinearMap.ext fun u => Subtype.ext (funext fun x => by
    change u.1 (x * 1) = u.1 x
    rw [mul_one])
  map_mul' k₁ k₂ := LinearMap.ext fun u => Subtype.ext (funext fun x => by
    change u.1 (x * (k₁ * k₂)) = u.1 (x * k₁ * k₂)
    rw [mul_assoc])

theorem isContRep_rR (U : Submodule ℂ (Kinf E n → ℂ)) (hU : ∀ u ∈ U, ∀ k, (fun x => u (x * k)) ∈ U)
    (hc : ∀ u ∈ U, Continuous u) [FiniteDimensional ℂ U] : GlobalTheory.Published.AutFin.IsContRep (rR U hU) := by
  intro ℓ w
  have h : Submodule.span ℂ (Set.range fun x : Kinf E n =>
      ((LinearMap.proj x : (Kinf E n → ℂ) →ₗ[ℂ] ℂ).comp U.subtype : U →ₗ[ℂ] ℂ)) = ⊤ := by
    refine Submodule.span_eq_top_of_ne_zero fun z hz => ?_
    by_contra hcon
    push Not at hcon
    exact hz (Subtype.ext (funext fun x => hcon _ ⟨x, rfl⟩))
  have hl : ℓ ∈ (⊤ : Submodule ℂ (U →ₗ[ℂ] ℂ)) := Submodule.mem_top
  rw [← h] at hl
  induction hl using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, rfl⟩ := hy
    exact (hc w.1 w.2).comp (continuous_const_mul x)
  | zero => exact continuous_const
  | add y z _ _ hy hz => exact hy.add hz
  | smul c y _ hy => exact hy.const_smul c

theorem cont_K [NumberField E] [IsCMField E] (φ : Sm E n) (g : GA E n) :
    Continuous fun k : Kinf E n => φ.1 (g * infGL E n (Unitary.toUnits k)) := by
  have h1 : Continuous fun k : Kinf E n => chart φ.1 g (toL (Unitary.toUnits k).val) :=
    (φ.2 g).continuousOn.comp_continuous (f := fun k : Kinf E n => toL (Unitary.toUnits k).val)
      continuous_subtype_val fun k => val_mem_invSet _
  simp only [chart_val] at h1
  exact h1

theorem cont_rS (W : Submodule ℂ (Kinf E n → ℂ)) :
    ∀ u ∈ rS (lI (W ⊓ contK E n)), Continuous u := by
  intro u hu
  induction hu using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨w, hw, k, rfl⟩ := hv
    have hc : Continuous w := (lI_le _ hw).2
    exact hc.comp (continuous_mul_const k)
  | zero => exact continuous_zero
  | add x y _ _ hx hy => exact hx.add hy
  | smul a x _ hx => exact hx.const_smul a

end AdmDiscPf

open AdmDiscPf in

theorem admissible_discrete_spaces : AdmDisc := by
  intro E _ _ _ M K' W' hK' hW' V hV
  obtain ⟨φ₀, hφ₀, h0⟩ := (Submodule.ne_bot_iff _).1 hV.ne_bot
  have hA : PrAdm.SupSpansPsiPart V φ₀ = V := by
    rcases hV.irred _ (PrAdm.admissible_span_le V φ₀) (PrAdm.isStable_admissible_span hV.stable φ₀) with h | h
    · exact absurd ((Submodule.mem_bot ℂ).1 (h ▸ PrAdm.mem_admissible_span_self hφ₀)) h0
    · exact h
  have : FiniteDimensional ℂ (W' ⊓ contK E M : Submodule ℂ (Kinf E M → ℂ)) :=
    Submodule.finiteDimensional_of_le inf_le_left
  have : FiniteDimensional ℂ (rS (lI (W' ⊓ contK E M))) := fd_rS_lI _
  have hU : ∀ u ∈ rS (lI (W' ⊓ contK E M)), ∀ k, (fun x => u (x * k)) ∈ rS (lI (W' ⊓ contK E M)) :=
    fun u hu k => rS_right hu k
  have hfd := PrAdm.finiteDimensional_admissible_isotypic hV.aut (hV.aut φ₀ hφ₀) hK' (rR _ hU) (isContRep_rR _ hU (cont_rS W'))
  refine Submodule.finiteDimensional_of_le
    (S₂ := PrAdm.SupSpansPsiPart V φ₀ ⊓ typePart K' (rR (rS (lI (W' ⊓ contK E M))) hU)) (Submodule.span_le.2 ?_)
  rintro φ ⟨hφV, hT⟩
  refine ⟨hA.symm ▸ hφV, fun k hk => Subtype.ext (funext fun g => hT.1 k hk g), fun g => ?_⟩
  have hf : (fun k : Kinf E M => (cptRep E M k φ).1 g) ∈ lI (W' ⊓ contK E M) := by
    refine mem_lI.2 fun k₀ => ⟨?_, ?_⟩
    · show (fun k => φ.1 (g * infGL E M (Unitary.toUnits (k₀ * k)))) ∈ W'
      have := hT.2 (g * infGL E M (Unitary.toUnits k₀))
      simpa only [map_mul, mul_assoc] using this
    · show Continuous fun k => φ.1 (g * infGL E M (Unitary.toUnits (k₀ * k)))
      have := cont_K φ (g * infGL E M (Unitary.toUnits k₀))
      simpa only [map_mul, mul_assoc] using this
  have hfU := le_rS _ hf
  refine Submodule.subset_span ⟨(LinearMap.proj 1 : (Kinf E M → ℂ) →ₗ[ℂ] ℂ).comp
    (rS (lI (W' ⊓ contK E M))).subtype, ⟨_, hfU⟩, funext fun k => ?_⟩
  change (cptRep E M k φ).1 g = (cptRep E M (1 * k) φ).1 g
  rw [one_mul]

end PositivityTheory.Rg.BcB.SpectralAccumulation

end
