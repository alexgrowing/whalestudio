import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TwistStripLimits.BlockTypes
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PProjA

noncomputable section

open NumberField MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def Tr.Pos : {N : ℕ} → Tr E N → Prop
  | M, .leaf V _ => 0 < M ∧ IsDiscrete V
  | _, .node t₁ t₂ => Tr.Pos t₁ ∧ Tr.Pos t₂

theorem strip_shift (z : ℂ) {N : ℕ} (t : Tr E N) : (t.shift z).strip = t.strip := by
  induction t with
  | leaf V z' => rfl
  | node t₁ t₂ ih₁ ih₂ => simp only [Tr.shift, Tr.strip, ih₁, ih₂]

theorem twists_shift (z : ℂ) {N : ℕ} (t : Tr E N) : (t.shift z).twists = t.twists.map (· + z) := by
  induction t with
  | leaf V z' => rfl
  | node t₁ t₂ ih₁ ih₂ => simp only [Tr.shift, Tr.twists, ih₁, ih₂, List.map_append]

theorem length_twists_strip {N : ℕ} (t : Tr E N) : t.strip.twists.length = t.twists.length := by
  induction t with
  | leaf V z' => rfl
  | node t₁ t₂ ih₁ ih₂ => simp only [Tr.strip, Tr.twists, List.length_append, ih₁, ih₂]

theorem length_twists_of_strip {N : ℕ} {t t' : Tr E N} (h : t.strip = t'.strip) :
    t.twists.length = t'.twists.length := by
  rw [← length_twists_strip t, ← length_twists_strip t', h]

theorem pos_shift (z : ℂ) {N : ℕ} {t : Tr E N} (h : Tr.Pos t) : Tr.Pos (t.shift z) := by
  induction t with
  | leaf V z' => exact h
  | node t₁ t₂ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩

theorem allLeaves_shift (z : ℂ) {P : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop} {N : ℕ} {t : Tr E N}
    (h : t.AllLeaves P) : (t.shift z).AllLeaves P := by
  induction t with
  | leaf V z' => exact h
  | node t₁ t₂ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩

theorem disc_of_pos {N : ℕ} {t : Tr E N} (h : Tr.Pos t) : t.Disc := by
  induction t with
  | leaf V z' => exact Or.inr h
  | node t₁ t₂ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩

theorem good_of_pos {N : ℕ} {t : Tr E N} (h : Tr.Pos t) (hz : ∀ z ∈ t.twists, z.re = 0) : t.Good := by
  induction t with
  | leaf V z' => exact Or.inr ⟨h.1, h.2, hz z' (by simp [Tr.twists])⟩
  | node t₁ t₂ ih₁ ih₂ =>
    exact ⟨ih₁ h.1 fun z hz' => hz z (by simp [Tr.twists, hz']),
      ih₂ h.2 fun z hz' => hz z (by simp [Tr.twists, hz'])⟩

theorem stable_of_pos {N : ℕ} {t : Tr E N} (h : Tr.Pos t) : t.AllLeaves fun _ V => IsStable V := by
  induction t with
  | leaf V z' => exact h.2.stable
  | node t₁ t₂ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩

theorem allLeaves_and {P Q : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop} {N : ℕ} {t : Tr E N}
    (hP : t.AllLeaves P) (hQ : t.AllLeaves Q) : t.AllLeaves fun M V => P M V ∧ Q M V := by
  induction t with
  | leaf V z' => exact ⟨hP, hQ⟩
  | node t₁ t₂ ih₁ ih₂ => exact ⟨ih₁ hP.1 hQ.1, ih₂ hP.2 hQ.2⟩

theorem allLeaves_pos {N : ℕ} {t : Tr E N} (h : Tr.Pos t) : t.AllLeaves fun M _ => 0 < M := by
  induction t with
  | leaf V z' => exact h.1
  | node t₁ t₂ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩

theorem allLeaves_mono {P Q : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop} (hPQ : ∀ M V, P M V → Q M V) {N : ℕ}
    {t : Tr E N} (h : t.AllLeaves P) : t.AllLeaves Q := by
  induction t with
  | leaf V z' => exact hPQ _ _ h
  | node t₁ t₂ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩

theorem getD_map_add (l : List ℂ) (z : ℂ) (i : ℕ) :
    (l.map (· + z)).getD i 0 = if i < l.length then l.getD i 0 + z else 0 := by
  split_ifs with h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_none (not_lt.1 h)]

theorem getD_append (l l' : List ℂ) (i : ℕ) :
    (l ++ l').getD i 0 = if i < l.length then l.getD i 0 else l'.getD (i - l.length) 0 := by
  split_ifs with h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (not_lt.1 h)]

variable {N : ℕ}

theorem emb_trans {U U' : Submodule ℂ (Sm E N)} {P : Sm E N → Prop} (h₁ : Emb U (· ∈ U')) (h₂ : Emb U' P) : Emb U P := by
  obtain ⟨f₁, hf₁, hi₁, he₁⟩ := h₁
  obtain ⟨f₂, hf₂, hi₂, he₂⟩ := h₂
  refine ⟨f₂ ∘ₗ f₁, fun φ hφ => hf₂ _ (hf₁ φ hφ), fun φ hφ h0 => hi₁ φ hφ (hi₂ _ (hf₁ φ hφ) h0), fun o φ hφ => ?_⟩
  simp only [LinearMap.comp_apply]
  rw [he₁ o φ hφ, he₂ o _ (hf₁ φ hφ)]

theorem emb_of_isoV {V V' : Submodule ℂ (Sm E N)} (hV : IsStable V) (h : IsoV V V') : Emb V (· ∈ V') := by
  obtain ⟨T, hT⟩ := h
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl V
  let p := Submodule.linearProjOfIsCompl V C hC
  have hp : ∀ φ (hφ : φ ∈ V), p φ = ⟨φ, hφ⟩ := fun φ hφ => Submodule.linearProjOfIsCompl_apply_left hC ⟨φ, hφ⟩
  refine ⟨V'.subtype ∘ₗ T.toLinearMap ∘ₗ p, fun φ hφ => by simp, fun φ hφ h0 => ?_, fun o φ hφ => ?_⟩
  · simp only [LinearMap.comp_apply, hp φ hφ, Submodule.subtype_apply, LinearEquiv.coe_coe,
      ZeroMemClass.coe_eq_zero, LinearEquiv.map_eq_zero_iff] at h0
    simpa using congrArg Subtype.val h0
  · have hψ : act o φ ∈ V := hV o φ hφ
    simp only [LinearMap.comp_apply, hp φ hφ, hp _ hψ, Submodule.subtype_apply, LinearEquiv.coe_coe]
    exact hT o ⟨φ, hφ⟩ ⟨act o φ, hψ⟩ rfl

theorem isoV_of_common {V₁ V₂ V' : Submodule ℂ (Sm E N)} (hV₂ : IsStable V₂) (h₁ : IsoV V₁ V') (h₂ : IsoV V₂ V') :
    IsoV V₁ V₂ := by
  obtain ⟨T₁, hT₁⟩ := h₁
  obtain ⟨T₂, hT₂⟩ := h₂
  refine ⟨T₁.trans T₂.symm, fun o φ ψ hψ => ?_⟩
  set χ := T₂.symm (T₁ φ) with hχ
  have hmem : act o χ.1 ∈ V₂ := hV₂ o χ.1 χ.2
  have key : T₂ ⟨act o χ.1, hmem⟩ = T₁ ψ := by
    apply Subtype.ext
    rw [hT₂ o χ ⟨act o χ.1, hmem⟩ rfl, hχ, LinearEquiv.apply_symm_apply, hT₁ o φ ψ hψ]
  simp only [LinearEquiv.trans_apply]
  rw [← key, LinearEquiv.symm_apply_apply]

theorem mulChi_absC_zero (φ : Sm E N) : mulChi N (Model.absC E 0) φ = φ :=
  Subtype.ext (funext fun g => by rw [mulChi_apply, ExponentTwist.chiDet_absC_val]; simp)

theorem tw_zero (V : Submodule ℂ (Sm E N)) : tw V 0 = V := by
  ext φ
  constructor
  · rintro ⟨ψ, hψ, rfl⟩
    simpa [mulChi_absC_zero] using hψ
  · intro hφ
    exact ⟨φ, hφ, mulChi_absC_zero φ⟩

theorem exists_subseq_const {α : Type*} {S : Set α} (hS : S.Finite) (f : ℕ → α) (hf : ∀ k, f k ∈ S) :
    ∃ a ∈ S, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ k, f (ψ k) = a := by
  have : ∃ a ∈ S, ∃ᶠ k in atTop, f k = a := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ᶠ k in atTop, ∀ a ∈ S, f k ≠ a := by
      have := (hS.eventually_all (l := atTop) (p := fun a k => f k ≠ a)).2
      exact this fun a ha => hcon a ha
    obtain ⟨k, hk⟩ := hall.exists
    exact hk (f k) (hf k) rfl
  obtain ⟨a, ha, hfr⟩ := this
  obtain ⟨ψ, hψ, hψa⟩ := Filter.extraction_of_frequently_atTop hfr
  exact ⟨a, ha, ψ, hψ, hψa⟩

end PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5

end
