import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PProjA

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.ParabolicProjection

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Trees

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem mulChi_absC_comp (n : ℕ) (z z' : ℂ) (φ : Sm E n) :
    mulChi n (Model.absC E z) (mulChi n (Model.absC E z') φ) = mulChi n (Model.absC E (z' + z)) φ := by
  refine Subtype.ext (funext fun g => ?_)
  rw [mulChi_apply, mulChi_apply, mulChi_apply, ExponentTwist.chiDet_absC_val, ExponentTwist.chiDet_absC_val,
    ExponentTwist.chiDet_absC_val, mul_assoc, ← Complex.exp_add]
  congr 2
  ring

theorem chiDet_unip_absC {N r : ℕ} (z : ℂ) (x : BlockIx N r → Ad E) : chiDet N (Model.absC E z) (unip x) = 1 := by
  rw [chiDet, MonoidHom.comp_apply, det_unip, map_one]

theorem chiDet_lev_absC {r s : ℕ} (z : ℂ) (m : GA E r × GA E s) :
    chiDet (r + s) (Model.absC E z) (lev (Ad E) r s m) =
      chiDet r (Model.absC E z) m.1 * chiDet s (Model.absC E z) m.2 := by
  simp only [chiDet, MonoidHom.comp_apply, lev, det_emb₂, map_mul]

theorem mulChi_mem_finVec {n : ℕ} (χ : HChar E) {φ : Sm E n} (h : φ ∈ finVec (cptRep E n)) :
    mulChi n χ φ ∈ finVec (cptRep E n) := by
  haveI h' : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E n k φ)) := h
  change FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E n k (mulChi n χ φ)))
  refine Submodule.finiteDimensional_of_le
    (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E n k φ) ⊔ Submodule.span ℂ {φ}).map
      (mulChi n χ).toLinearMap) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  exact ⟨_, add_mem (Submodule.smul_mem _ _ (Submodule.mem_sup_left (Submodule.subset_span ⟨k, rfl⟩)))
    (Submodule.smul_mem _ _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self φ))),
    (act_mulChi χ (.cpt k) φ).symm⟩

theorem memInd2_mulChi {r s : ℕ} {A A' : Submodule ℂ (Sm E r)} {B B' : Submodule ℂ (Sm E s)} (z : ℂ)
    (hA : ∀ ψ ∈ A, mulChi r (Model.absC E z) ψ ∈ A') (hB : ∀ ψ ∈ B, mulChi s (Model.absC E z) ψ ∈ B')
    {φ : Sm E (r + s)} (h : MemInd2 A B φ) : MemInd2 A' B' (mulChi (r + s) (Model.absC E z) φ) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun x g => ?_, fun k g => ?_⟩
  · rw [mulChi_apply, mulChi_apply, h1, map_mul, chiDet_unip_absC, one_mul]
  · obtain ⟨n, ψ₁, ψ₂, m₁, m₂, e⟩ := tensor_pair_finite_sum (h2 k g)
    have key := sum_mem_tens2 (V₁ := A') (V₂ := B')
      (ψ₁ := fun i => ((chiDet (r + s) (Model.absC E z)
        (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g) : ℂˣ) : ℂ) • mulChi r (Model.absC E z) (ψ₁ i))
      (ψ₂ := fun i => mulChi s (Model.absC E z) (ψ₂ i))
      (fun i => A'.smul_mem _ (hA _ (m₁ i))) (fun i => hB _ (m₂ i))
    convert key using 1
    funext m
    rw [mulChi_apply, e m, map_mul, chiDet_lev_absC, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mulChi_apply, Units.val_mul]
    ring

theorem mulChi_mem_shift (z : ℂ) {N : ℕ} (t : Tr E N) :
    ∀ φ ∈ t.space, mulChi N (Model.absC E z) φ ∈ (t.shift z).space := by
  induction t with
  | leaf V z' =>
    rintro _ ⟨ψ, hψ, rfl⟩
    exact ⟨ψ, hψ, (mulChi_absC_comp _ _ _ _).symm⟩
  | @node r s t₁ t₂ ih₁ ih₂ =>
    intro φ hφ
    have hA : ∀ ψ ∈ tw t₁.space ((s : ℂ) / 2), mulChi r (Model.absC E z) ψ ∈ tw (t₁.shift z).space ((s : ℂ) / 2) := by
      rintro _ ⟨ψ, hψ, rfl⟩
      refine ⟨_, ih₁ ψ hψ, ?_⟩
      change mulChi r _ (mulChi r _ ψ) = mulChi r _ (mulChi r _ ψ)
      rw [mulChi_absC_comp, mulChi_absC_comp, add_comm]
    have hB : ∀ ψ ∈ tw t₂.space (-(r : ℂ) / 2), mulChi s (Model.absC E z) ψ ∈ tw (t₂.shift z).space (-(r : ℂ) / 2) := by
      rintro _ ⟨ψ, hψ, rfl⟩
      refine ⟨_, ih₂ ψ hψ, ?_⟩
      change mulChi s _ (mulChi s _ ψ) = mulChi s _ (mulChi s _ ψ)
      rw [mulChi_absC_comp, mulChi_absC_comp, add_comm]
    change φ ∈ Submodule.span ℂ _ at hφ
    change _ ∈ Submodule.span ℂ _
    induction hφ using Submodule.span_induction with
    | mem φ h => exact Submodule.subset_span ⟨memInd2_mulChi z hA hB h.1, mulChi_mem_finVec _ h.2⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

theorem twShift : TwShift := by
  rintro E _ _ _ N V t z hV ⟨f, hf, hinj, heq⟩
  refine ⟨twMap N z f, ?_, twMap_ne hinj, twMap_equiv hV heq⟩
  rintro _ ⟨φ, hφ, rfl⟩
  change twMap N z f (mulChi N (Model.absC E z) φ) ∈ _
  rw [twMap_apply, mulChi_absC_neg]
  exact mulChi_mem_shift z t _ (hf φ hφ)

end PositivityTheory.Rg.BcB.SpectralAccumulation.Trees

end
