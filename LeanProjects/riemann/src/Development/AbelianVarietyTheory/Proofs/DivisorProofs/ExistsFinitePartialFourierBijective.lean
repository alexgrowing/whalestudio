import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDblOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicWeilRepSchrodingerModelUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerRestriction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRealisedOnAdelicSchwartzWeylFourier
import GroundTheory.AutomorphicForms.GL2.GJMatrixFinite

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixXChar GlobalTheory.DblEval
open GlobalTheory.Doubling (absE)

open scoped Classical
attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField
  GlobalTheory.DiagForm.measAf GlobalTheory.DiagForm.borelAf

open GroundTheory.Global GroundTheory.Automorphic.GJMatrix

noncomputable section

namespace GlobalTheory.PartialFourierFin

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def chiF (t : FiniteAdeleRing (𝓞 F) F) : ℂ := (finiteAdelicChar F t : ℂ)

theorem psi_fin_eq {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (t : FiniteAdeleRing (𝓞 F) F) :
    ψ (((0, t) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) : AF F) = chiF t := by
  refine (GlobalTheory.AdelicSvN.Weyl.isStd_eq hψ _).trans ?_
  rw [chiF, finiteAdelicChar_apply]
  rfl

def slice (g : (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (v : κ → FiniteAdeleRing (𝓞 F) F) :
    (κ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
  fun ξ => g (Sum.elim v ξ)

def pf (g : (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (w : κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) : ℂ :=
  finiteFourierPi F (slice g (w ∘ Sum.inl)) (w ∘ Sum.inr)

theorem slice_mem {g : (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ finiteSchwartzBruhatPi F)
    (v : κ → FiniteAdeleRing (𝓞 F) F) : slice g v ∈ finiteSchwartzBruhatPi F := by
  have hc : Continuous fun ξ : κ → FiniteAdeleRing (𝓞 F) F => (Sum.elim v ξ : κ ⊕ κ → _) :=
    continuous_pi fun i => by cases i <;> simp [continuous_const, continuous_apply]
  refine ⟨hg.1.comp_continuous hc, ?_⟩
  refine HasCompactSupport.intro ((hg.2.isCompact).image
    (continuous_pi fun i => continuous_apply (Sum.inr i))) fun ξ hξ => ?_
  exact image_eq_zero_of_notMem_tsupport (f := g) (x := Sum.elim v ξ) fun h => hξ ⟨_, h, rfl⟩

theorem slice_add (f g : (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (v) : slice (f + g) v = slice f v + slice g v := rfl
theorem slice_smul (c : ℂ) (f : (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (v) : slice (c • f) v = c • slice f v := rfl

theorem pf_add {f g : (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hf : f ∈ finiteSchwartzBruhatPi F)
    (hg : g ∈ finiteSchwartzBruhatPi F) : pf (f + g) = pf f + pf g := by
  funext w
  simp only [pf, slice_add, Pi.add_apply]
  rw [finiteFourierPi_add (integrable_of_mem_finiteSchwartzBruhatPi (slice_mem hf _))
    (integrable_of_mem_finiteSchwartzBruhatPi (slice_mem hg _))]
  rfl

theorem pf_smul (c : ℂ) (f : (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) → ℂ) : pf (c • f) = c • pf f := by
  funext w
  simp only [pf, slice_smul, Pi.smul_apply]
  rw [finiteFourierPi_smul]
  rfl

theorem pf_zero : pf (0 : (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) → ℂ) = 0 := by
  have := pf_smul (F := F) (κ := κ) 0 0
  simpa using this

def gmap (c : κ ⊕ κ → FiniteAdeleRing (𝓞 F) F → ℂ) : κ ⊕ κ → FiniteAdeleRing (𝓞 F) F → ℂ :=
  Sum.elim (c ∘ Sum.inl) (fun j => finiteFourier F (c (Sum.inr j)))

theorem pf_tensor (c : κ ⊕ κ → FiniteAdeleRing (𝓞 F) F → ℂ) :
    pf (finiteTensor c) = finiteTensor (gmap c) := by
  funext w
  have hs : slice (finiteTensor c) (w ∘ Sum.inl) =
      (∏ j, c (Sum.inl j) (w (Sum.inl j))) • finiteTensor (c ∘ Sum.inr) := by
    funext ξ
    simp [slice, finiteTensor, Fintype.prod_sum_type]
  rw [pf, hs, finiteFourierPi_smul, finiteFourierPi_finiteTensor]
  simp [finiteTensor, gmap, Fintype.prod_sum_type]

theorem pf_mem {g : (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ finiteSchwartzBruhatPi F) :
    pf g ∈ finiteSchwartzBruhatPi F := by
  rw [finiteSchwartzBruhatPi_eq_span] at hg
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨⟨I, a⟩, rfl⟩ := hg
    rw [pf_tensor]
    refine finiteTensor_mem fun i => ?_
    cases i with
    | inl j => exact cosetIndicator_mem_finiteSchwartzBruhat _ _
    | inr j => exact finiteFourier_mem_finiteSchwartzBruhat (cosetIndicator_mem_finiteSchwartzBruhat _ _)
  | zero => rw [pf_zero]; exact zero_mem _
  | add g h hg hh ihg ihh =>
    rw [← finiteSchwartzBruhatPi_eq_span] at hg hh
    rw [pf_add hg hh]
    exact add_mem ihg ihh
  | smul c g _ ih =>
    rw [pf_smul]
    exact Submodule.smul_mem _ c ih

theorem fourier_four {f : FiniteAdeleRing (𝓞 F) F → ℂ} (hf : f ∈ finiteSchwartzBruhat F) :
    finiteFourier F (finiteFourier F (finiteFourier F (finiteFourier F f))) = f := by
  have h2 := finiteFourier_mem_finiteSchwartzBruhat (finiteFourier_mem_finiteSchwartzBruhat hf)
  rw [finiteFourier_finiteFourier h2, finiteFourier_finiteFourier hf]
  funext x
  simp

theorem pf_surj {h : (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hh : h ∈ finiteSchwartzBruhatPi F) :
    ∃ g ∈ finiteSchwartzBruhatPi F, pf g = h := by
  rw [finiteSchwartzBruhatPi_eq_span] at hh
  induction hh using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨⟨I, a⟩, rfl⟩ := hg
    let c : κ ⊕ κ → FiniteAdeleRing (𝓞 F) F → ℂ := fun i => cosetIndicator I (a i)
    have hc : ∀ i, c i ∈ finiteSchwartzBruhat F := fun i => cosetIndicator_mem_finiteSchwartzBruhat _ _
    let d : κ ⊕ κ → FiniteAdeleRing (𝓞 F) F → ℂ :=
      Sum.elim (c ∘ Sum.inl) (fun j => finiteFourier F (finiteFourier F (finiteFourier F (c (Sum.inr j)))))
    refine ⟨finiteTensor d, finiteTensor_mem fun i => ?_, ?_⟩
    · cases i with
      | inl j => exact hc _
      | inr j => exact finiteFourier_mem_finiteSchwartzBruhat (finiteFourier_mem_finiteSchwartzBruhat
          (finiteFourier_mem_finiteSchwartzBruhat (hc _)))
    · rw [pf_tensor]
      congr 1
      funext i
      cases i with
      | inl j => rfl
      | inr j => exact fourier_four (hc _)
  | zero => exact ⟨0, zero_mem _, pf_zero⟩
  | add g h _ _ ihg ihh =>
    obtain ⟨g1, hg1, e1⟩ := ihg
    obtain ⟨g2, hg2, e2⟩ := ihh
    exact ⟨g1 + g2, add_mem hg1 hg2, by rw [pf_add hg1 hg2, e1, e2]⟩
  | smul c g _ ih =>
    obtain ⟨g1, hg1, e1⟩ := ih
    exact ⟨c • g1, Submodule.smul_mem _ c hg1, by rw [pf_smul, e1]⟩

theorem chiF_add (a b : FiniteAdeleRing (𝓞 F) F) : chiF (a + b) = chiF a * chiF b := by
  simp only [chiF, AddChar.map_add_eq_mul, Circle.coe_mul]

theorem isLocallyConstant_chiF : IsLocallyConstant (chiF (F := F)) := by
  letI : NonarchimedeanAddGroup (FiniteAdeleRing (𝓞 F) F) :=
    { is_nonarchimedean := fun U hU => by
        obtain ⟨J, hJ⟩ := exists_idealFiniteAdeles_subset hU
        exact ⟨⟨idealFiniteAdeles J, isOpen_idealFiniteAdeles J⟩, hJ⟩ }
  have := GlobalTheory.WeilM.isLocallyConstant_addChar (Circle.coeHom.compAddChar (finiteAdelicChar F))
    (continuous_subtype_val.comp continuous_finiteAdelicChar)
  exact this

def phi (u : κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) : κ ⊕ κ → FiniteAdeleRing (𝓞 F) F :=
  Sum.elim (u ∘ Sum.inl - u ∘ Sum.inr) (u ∘ Sum.inr)

def phiInv (w : κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) : κ ⊕ κ → FiniteAdeleRing (𝓞 F) F :=
  Sum.elim (w ∘ Sum.inl + w ∘ Sum.inr) (w ∘ Sum.inr)

theorem phiInv_phi (u : κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) : phiInv (phi u) = u := by
  funext i; cases i <;> simp [phi, phiInv]

theorem phi_phiInv (w : κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) : phi (phiInv w) = w := by
  funext i; cases i <;> simp [phi, phiInv]

theorem continuous_phi : Continuous (phi (F := F) (κ := κ)) :=
  continuous_pi fun i => by
    cases i with
    | inl j => exact (continuous_apply (Sum.inl j)).sub (continuous_apply (Sum.inr j))
    | inr j => exact continuous_apply (Sum.inr j)

theorem continuous_phiInv : Continuous (phiInv (F := F) (κ := κ)) :=
  continuous_pi fun i => by
    cases i with
    | inl j => exact (continuous_apply (Sum.inl j)).add (continuous_apply (Sum.inr j))
    | inr j => exact continuous_apply (Sum.inr j)

theorem comp_mem {g : (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ finiteSchwartzBruhatPi F)
    {a b : (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) → (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F)}
    (ha : Continuous a) (hb : Continuous b) (hba : ∀ u, b (a u) = u) :
    g ∘ a ∈ finiteSchwartzBruhatPi F :=
  ⟨hg.1.comp_continuous ha, HasCompactSupport.intro (hg.2.isCompact.image hb) fun u hu =>
    image_eq_zero_of_notMem_tsupport (f := g) (x := a u) fun h => hu ⟨_, h, hba u⟩⟩

def B0 (g : (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) → ℂ) : (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
  pf g ∘ phi

theorem finitePartialFourier_mem_finiteSchwartzBruhatPi {g : (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ finiteSchwartzBruhatPi F) :
    B0 g ∈ finiteSchwartzBruhatPi F :=
  comp_mem (pf_mem hg) continuous_phi continuous_phiInv phiInv_phi

theorem finitePartialFourier_surjective {h : (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hh : h ∈ finiteSchwartzBruhatPi F) :
    ∃ g ∈ finiteSchwartzBruhatPi F, B0 g = h := by
  obtain ⟨g, hg, e⟩ := pf_surj (comp_mem hh continuous_phiInv continuous_phi phi_phiInv)
  refine ⟨g, hg, ?_⟩
  funext u
  simp only [B0, Function.comp_apply, e, phiInv_phi]

theorem finitePartialFourier_add' {f g : (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hf : f ∈ finiteSchwartzBruhatPi F)
    (hg : g ∈ finiteSchwartzBruhatPi F) : B0 (f + g) = B0 f + B0 g := by
  simp only [B0, pf_add hf hg]; rfl

theorem finitePartialFourier_smul' (c : ℂ) (f : (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) → ℂ) : B0 (c • f) = c • B0 f := by
  simp only [B0, pf_smul]; rfl

theorem pf_mul_char (g : (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (z w : κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) :
    pf (fun u => chiF (u ⬝ᵥ z) * g u) w =
      chiF ((w ∘ Sum.inl) ⬝ᵥ (z ∘ Sum.inl)) * pf g (Sum.elim (w ∘ Sum.inl) (w ∘ Sum.inr + z ∘ Sum.inr)) := by
  simp only [pf, finiteFourierPi, slice, Sum.elim_comp_inl, Sum.elim_comp_inr]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  have e1 : Sum.elim (w ∘ Sum.inl) ξ ⬝ᵥ z = (w ∘ Sum.inl) ⬝ᵥ (z ∘ Sum.inl) + ∑ i, ξ i * z (Sum.inr i) := by
    simp [dotProduct, Fintype.sum_sum_type]
  have e2 : ∑ i, ξ i * (w ∘ Sum.inr + z ∘ Sum.inr) i = ∑ i, ξ i * (w ∘ Sum.inr) i + ∑ i, ξ i * z (Sum.inr i) := by
    simp [mul_add, Finset.sum_add_distrib]
  change chiF _ * g _ * chiF _ = chiF _ * (g _ * chiF _)
  rw [e1, e2, chiF_add, chiF_add]
  ring

theorem integral_diag :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ g ∈ finiteSchwartzBruhatPi F (ι := κ ⊕ κ),
      ∫ v : κ → FiniteAdeleRing (𝓞 F) F, B0 g (Sum.elim v v) ∂Measure.addHaar = C * g 0 := by
  have hμ := Measure.isAddLeftInvariant_eq_smul (Measure.addHaar : Measure (κ → FiniteAdeleRing (𝓞 F) F))
    (finiteMeasurePi F)
  set c := (Measure.addHaar : Measure (κ → FiniteAdeleRing (𝓞 F) F)).addHaarScalarFactor (finiteMeasurePi F)
    with hcdef
  have hc : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  refine ⟨(c : ℂ), by exact_mod_cast hc.ne', fun g hg => ?_⟩
  have hphi : ∀ v : κ → FiniteAdeleRing (𝓞 F) F, phi (Sum.elim v v) = Sum.elim (0 : κ → FiniteAdeleRing (𝓞 F) F) v := by
    intro v; funext i; cases i <;> simp [phi]
  have h1 : ∀ v, B0 g (Sum.elim v v) = finiteFourierPi F (slice g 0) v := by
    intro v
    simp only [B0, Function.comp_apply, hphi, pf, Sum.elim_comp_inl, Sum.elim_comp_inr]
  simp_rw [h1]
  rw [hμ, integral_smul_nnreal_measure]
  have e : finiteFourierPi F (finiteFourierPi F (slice g 0)) 0 =
      ∫ v, finiteFourierPi F (slice g 0) v ∂finiteMeasurePi F := by
    rw [finiteFourierPi]
    simp
  have h2 := congrFun (finiteFourierPi_finiteFourierPi (slice_mem hg 0)) 0
  rw [← e, h2]
  simp [slice, NNReal.smul_def]

end GlobalTheory.PartialFourierFin

open GlobalTheory.PartialFourierFin in

theorem GlobalTheory.PartialFourierFin.exists_partialFourier_diag : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ],
    ∃ B : ((κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) → ℂ) →ₗ[ℂ] ((κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
      (∀ g ∈ SB (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F), B g ∈ SB (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F)) ∧
      (∀ g ∈ SB (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F), ∃ g' ∈ SB (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F), B g' = g) ∧
      (∀ z : κ ⊕ κ → FiniteAdeleRing (𝓞 F) F, ∃ x y : κ → FiniteAdeleRing (𝓞 F) F,
        ∀ g ∈ SB (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F),
          B (fun u => ψ (((0, u ⬝ᵥ z) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) : AF F) * g u) =
            fun u => ψ (((0, u ⬝ᵥ Sum.elim y (-y)) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) : AF F) *
              B g (u + Sum.elim x x)) ∧
      ∃ C : ℂ, C ≠ 0 ∧ ∀ g ∈ SB (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F),
        ∫ v : κ → FiniteAdeleRing (𝓞 F) F, B g (Sum.elim v v) ∂Measure.addHaar = C * g 0 := by
  intro F _ _ ψ hψ κ _
  let L : SB (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) →ₗ[ℂ] ((κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :=
    { toFun := fun g => B0 g.1
      map_add' := fun f g => finitePartialFourier_add' f.2 g.2
      map_smul' := fun c f => finitePartialFourier_smul' c f.1 }
  obtain ⟨B, hB⟩ := LinearMap.exists_extend L
  have hB' : ∀ g ∈ SB (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F), B g = B0 g := fun g hg =>
    LinearMap.congr_fun hB ⟨g, hg⟩
  obtain ⟨C, hC0, hC⟩ := integral_diag (F := F) (κ := κ)
  refine ⟨B, fun g hg => ?_, fun g hg => ?_, fun z => ⟨z ∘ Sum.inr, z ∘ Sum.inl, fun g hg => ?_⟩,
    C, hC0, fun g hg => ?_⟩
  · rw [hB' g hg]; exact finitePartialFourier_mem_finiteSchwartzBruhatPi hg
  · obtain ⟨g', hg', e⟩ := finitePartialFourier_surjective hg
    exact ⟨g', hg', by rw [hB' g' hg', e]⟩
  · simp only [psi_fin_eq hψ]
    have hcont : Continuous fun u : κ ⊕ κ → FiniteAdeleRing (𝓞 F) F => u ⬝ᵥ z :=
      continuous_finset_sum _ fun i _ => (continuous_apply i).mul continuous_const
    have hm : (fun u => chiF (u ⬝ᵥ z) * g u) ∈ SB (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) :=
      ⟨(isLocallyConstant_chiF.comp_continuous hcont).mul hg.1, hg.2.mul_left⟩
    rw [hB' _ hm, hB' g hg]
    funext u
    simp only [B0, Function.comp_apply, pf_mul_char]
    have e1 : (phi u ∘ Sum.inl) ⬝ᵥ (z ∘ Sum.inl) = u ⬝ᵥ Sum.elim (z ∘ Sum.inl) (-(z ∘ Sum.inl)) := by
      simp [phi, dotProduct, Fintype.sum_sum_type, sub_eq_add_neg, add_mul, Finset.sum_add_distrib]
    have e2 : Sum.elim (phi u ∘ Sum.inl) (phi u ∘ Sum.inr + z ∘ Sum.inr) =
        phi (u + Sum.elim (z ∘ Sum.inr) (z ∘ Sum.inr)) := by
      funext i; cases i <;> simp [phi]
    rw [e1, e2]
  · rw [hB' g hg]
    exact hC g hg
