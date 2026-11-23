import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.JoinType

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcN.F2

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F.Tail

section Leaves

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem mem_leafList_of_allLeaves {P : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop} :
    ∀ {N : ℕ} (t : Tr E N), t.AllLeaves P → ∀ x ∈ t.leafList, P x.1 x.2
  | _, .leaf V z, h, x, hx => by
    simp only [Tr.leafList, List.mem_singleton] at hx
    subst hx
    exact h
  | _, .node t₁ t₂, h, x, hx => by
    simp only [Tr.leafList, List.mem_append] at hx
    rcases hx with hx | hx
    · exact mem_leafList_of_allLeaves t₁ h.1 x hx
    · exact mem_leafList_of_allLeaves t₂ h.2 x hx

theorem mem_parts_of_treeParts {N : ℕ} {t : Tr E N} {P : Pre E N} {Q : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop}
    (ht : TreeParts t P) (hl : t.AllLeaves Q) : ∀ x ∈ parts P, 0 < x.1 ∧ Q x.1 x.2 := by
  intro x hx
  have hx' : x ∈ t.leafList.filter fun y => 0 < y.1 := by
    rw [← ht]
    exact hx
  rw [List.mem_filter] at hx'
  exact ⟨by simpa using hx'.2, mem_leafList_of_allLeaves t hl x hx'.1⟩

end Leaves

section Twist

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def mulK (N : ℕ) (χ : HChar E) : (Kinf E N → ℂ) →ₗ[ℂ] (Kinf E N → ℂ) where
  toFun f k := (chiDet N χ (infGL E N (Unitary.toUnits k)) : ℂ) * f k
  map_add' f g := by
    funext k
    simp only [Pi.add_apply, mul_add]
  map_smul' c f := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem hasKType_twist {N : ℕ} (χ : HChar E) {K' : Subgroup (GL (Fin N) (Af E))} {W' : Submodule ℂ (Kinf E N → ℂ)}
    {V : Submodule ℂ (Sm E N)} (h : HasType K' W' V) :
    HasKType (W'.map (mulK N χ)) (V.map (mulChi N χ).toLinearMap) := by
  obtain ⟨φ, hφV, hφ0, -, hT⟩ := h
  refine ⟨mulChi N χ φ, Submodule.mem_map_of_mem hφV, ?_, fun g => ?_⟩
  · exact (LinearEquiv.map_ne_zero_iff (mulChi N χ)).2 hφ0
  · have e : (fun k : Kinf E N => ((mulChi N χ φ : Sm E N) : GA E N → ℂ) (g * infGL E N (Unitary.toUnits k))) =
        (chiDet N χ g : ℂ) • mulK N χ (fun k : Kinf E N => (φ : GA E N → ℂ) (g * infGL E N (Unitary.toUnits k))) := by
      funext k
      simp only [mulChi_apply, map_mul, Units.val_mul, Pi.smul_apply, smul_eq_mul, mulK, LinearMap.coe_mk,
        AddHom.coe_mk]
      ring
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.mem_map_of_mem (hT g))

theorem HasKType.mono {N : ℕ} {W₁ W₂ : Submodule ℂ (Kinf E N → ℂ)} {V : Submodule ℂ (Sm E N)} (h : W₁ ≤ W₂)
    (hV : HasKType W₁ V) : HasKType W₂ V := by
  obtain ⟨φ, hφ, h0, hW⟩ := hV
  exact ⟨φ, hφ, h0, fun g => h (hW g)⟩

end Twist

theorem joinType : JoinType := by
  intro E _ _ _ n μ Ω hΩ
  have : ∀ M, Finite (Ω M) := fun M => (hΩ M).1.to_subtype
  let W : ∀ N : ℕ, Submodule ℂ (Kinf E N → ℂ) := fun N =>
    ⨆ p : Ω N × Fin (n + 1), (p.1 : Submodule ℂ (Kinf E N → ℂ)).map (mulK N (μ ^ (p.2 : ℕ)))
  have hle : ∀ (N k : ℕ) (W' : Submodule ℂ (Kinf E N → ℂ)), W' ∈ Ω N → k ≤ n → W'.map (mulK N (μ ^ k)) ≤ W N :=
    fun N k W' hW' hk => le_iSup (fun p : Ω N × Fin (n + 1) => (p.1 : Submodule ℂ (Kinf E N → ℂ)).map
      (mulK N (μ ^ (p.2 : ℕ)))) (⟨W', hW'⟩, ⟨k, Nat.lt_succ_of_le hk⟩)
  refine ⟨W, fun N => ?_, ?_⟩
  · have : ∀ p : Ω N × Fin (n + 1), FiniteDimensional ℂ
        ((p.1 : Submodule ℂ (Kinf E N → ℂ)).map (mulK N (μ ^ (p.2 : ℕ)))) := fun p => by
      have := (hΩ N).2 _ p.1.2
      infer_instance
    infer_instance
  intro a b hab s₁ s₂ Pa Pb D hc h₁ h₂ i
  have key : ∀ (k : ℕ), k ≤ n → ∀ x : Σ M : ℕ, Submodule ℂ (Sm E M),
      (0 < x.1 ∧ (x.1 = 0 ∨ ∃ K', ∃ W' ∈ Ω x.1, HasType K' W' x.2)) →
      HasKType (W (twPart (μ ^ k) x).1) (twPart (μ ^ k) x).2 := by
    rintro k hk ⟨M, V⟩ ⟨hM, h0 | ⟨K', W', hW', hT⟩⟩
    · exact absurd h0 (Nat.pos_iff_ne_zero.1 hM)
    · exact HasKType.mono (hle M k W' hW' hk) (hasKType_twist (μ ^ k) hT)
  have hmem : (⟨D.N i, D.V i⟩ : Σ M : ℕ, Submodule ℂ (Sm E M)) ∈ parts D :=
    List.mem_ofFn.2 ⟨i, rfl⟩
  have hj := hc.join
  unfold IsJoin at hj
  rw [hj, List.mem_append, List.mem_map, List.mem_map] at hmem
  rcases hmem with ⟨x, hx, e⟩ | ⟨x, hx, e⟩
  · have := key b (by omega) x (mem_parts_of_treeParts hc.t₁ h₁ x hx)
    rw [e] at this
    exact this
  · have := key a (by omega) x (mem_parts_of_treeParts hc.t₂ h₂ x hx)
    rw [e] at this
    exact this

end PositivityTheory.Rg.BcB.F.Tail

end
