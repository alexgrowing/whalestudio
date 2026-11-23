import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.InfInd2Holds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceOperatorEigenvalueSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieCentralElementTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivSplitCentre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasInfCharGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeSpehOfDiscreteSeries

noncomputable section

open scoped Classical
open NumberField IsDedekindDomain MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Untw

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem hasInfCharGL_mono {N : ℕ} {V W : Submodule ℂ (Sm E N)} {τ : E →+* ℂ} {m : Multiset ℂ}
    (h : HasInfCharGL V τ m) (hle : W ≤ V) : HasInfCharGL W τ m :=
  ⟨h.1, fun u φ hφ => h.2 u φ (hle hφ)⟩

theorem hasInfCharGL_tw {N : ℕ} {V : Submodule ℂ (Sm E N)} {τ : E →+* ℂ} {m : Multiset ℂ}
    (h : HasInfCharGL V τ m) (z : ℂ) : HasInfCharGL (tw V z) τ (m.map (· + z)) := by
  have hW := GlobalTheory.NormIndCap.hasInfCharGL_map_mulChi h (GlobalTheory.CuspRep.Model.absC E z)
  rw [GlobalTheory.CuspRep.Model.expo_absC] at hW
  exact hW

theorem prod_cancel (m₁ m₂ : Multiset ℂ) (u : ℂ) (r s : ℕ) :
    ((m₁.map (· + (s : ℂ) / 2)).map (u - (s : ℂ) / 2 + ·)).prod *
        ((m₂.map (· + -(r : ℂ) / 2)).map (u + (r : ℂ) / 2 + ·)).prod = ((m₁ + m₂).map (u + ·)).prod := by
  rw [Multiset.map_add, Multiset.prod_add, Multiset.map_map, Multiset.map_map]
  congr 2
  · exact Multiset.map_congr rfl fun x _ => by simp only [Function.comp_apply]; ring
  · exact Multiset.map_congr rfl fun x _ => by simp only [Function.comp_apply]; ring

theorem hasInfCharGL_node {r s : ℕ} {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {τ : E →+* ℂ}
    {m₁ m₂ : Multiset ℂ} (h₁ : HasInfCharGL U₁ τ m₁) (h₂ : HasInfCharGL U₂ τ m₂) :
    HasInfCharGL (Submodule.span ℂ {φ | MemInd2 (tw U₁ ((s : ℂ) / 2)) (tw U₂ (-(r : ℂ) / 2)) φ}) τ (m₁ + m₂) := by
  refine ⟨by rw [Multiset.card_add, h₁.1, h₂.1], fun u φ hφ => ?_⟩
  induction hφ using Submodule.span_induction with
  | mem F hF =>
    have hc : cap τ u F = (((m₁.map (· + (s : ℂ) / 2)).map (u - (s : ℂ) / 2 + ·)).prod *
        ((m₂.map (· + -(r : ℂ) / 2)).map (u + (r : ℂ) / 2 + ·)).prod) • F :=
      PositivityTheory.Rg.Rs.PInfInd2A.casimir_on_parabolic_induction (n := ![r, s]) (tw U₁ ((s : ℂ) / 2)) (tw U₂ (-(r : ℂ) / 2)) τ _ _
        (hasInfCharGL_tw h₁ _) (hasInfCharGL_tw h₂ _) u F hF
    rw [hc, prod_cancel]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
  | smul a x _ hx => rw [map_smul, hx, smul_comm]

theorem hasInfCharGL_space {N : ℕ} (t : Tr E N) (τ : E →+* ℂ) (m : Multiset ℂ) (h : t.InfOf τ m) :
    HasInfCharGL t.space τ m := by
  induction t generalizing m with
  | leaf V z =>
    obtain ⟨m₀, h₀, rfl⟩ := h
    exact hasInfCharGL_tw h₀ z
  | @node r s t₁ t₂ ih₁ ih₂ =>
    obtain ⟨m₁, m₂, h₁, h₂, rfl⟩ := h
    refine hasInfCharGL_mono (hasInfCharGL_node (ih₁ m₁ h₁) (ih₂ m₂ h₂)) ?_
    rw [Tr.space]
    exact Submodule.span_mono fun φ hφ => hφ.1

theorem hasInfCharGL_top_zero (τ : E →+* ℂ) : HasInfCharGL (⊤ : Submodule ℂ (Sm E 0)) τ 0 := by
  refine ⟨rfl, fun u φ _ => ?_⟩
  simp [cap, Formalism.REAL.qdet, Formalism.REAL.qminor]

theorem exists_infOf {N : ℕ} (t : Tr E N) (ht : t.Good) (τ : E →+* ℂ) : ∃ m, t.InfOf τ m := by
  induction t with
  | leaf V z =>
    rcases ht with ⟨rfl, rfl, rfl⟩ | ⟨_, hV, _⟩
    · exact ⟨0, 0, hasInfCharGL_top_zero τ, by simp⟩
    · obtain ⟨m₀, h₀⟩ := GlobalTheory.ResW.IrrInfChar.exists_hasInfCharGL hV τ
      exact ⟨_, m₀, h₀, rfl⟩
  | node t₁ t₂ ih₁ ih₂ =>
    obtain ⟨m₁, h₁⟩ := ih₁ ht.1
    obtain ⟨m₂, h₂⟩ := ih₂ ht.2
    exact ⟨_, m₁, m₂, h₁, h₂, rfl⟩

theorem trace_eq {N : ℕ} {V : Submodule ℂ (Sm E N)} {τ : E →+* ℂ} {m : Multiset ℂ} (hm : HasInfCharGL V τ m) :
    ∀ φ ∈ V, (∑ i : Fin N, Eop τ i i) φ = m.sum • φ := by
  intro φ hφ
  obtain ⟨hc, hu⟩ := hm
  rcases N with _ | n
  · obtain rfl : m = 0 := Multiset.card_eq_zero.1 hc
    simp
  · obtain ⟨l, rfl⟩ := Quot.exists_rep m
    refine GlobalTheory.CompanionTheory.CapelliTrace.trace_of_qdet (Eop τ) l (by simpa using hc) φ fun v => ?_
    have := hu (v - (n : ℂ) / 2) φ hφ
    rw [cap, show v - (n : ℂ) / 2 + (((n + 1 : ℕ) : ℂ) - 1) / 2 = v by push_cast; ring] at this
    simpa using this

theorem lie_oneL_eq_zero {N : ℕ} (φ : Sm E N) (h : ∀ t g, φ.1 (splitCentre E N t * g) = φ.1 g) :
    lie E N (oneL E N) φ = 0 := by
  refine Subtype.ext (funext fun g => ?_)
  have h1 := GlobalTheory.CuspRep.SplitDeriv.hasDerivAt_splitCentre φ g 0
  have h2 : (fun t : ℝ => φ.1 (g * splitCentre E N t)) = fun _ => φ.1 g := by
    funext t
    rw [← GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm, h]
  rw [h2] at h1
  have h3 := h1.unique (hasDerivAt_const (0 : ℝ) (φ.1 g))
  rw [GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_zero, mul_one] at h3
  exact h3

theorem sum_trace_eq_zero {N : ℕ} {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) (m : (E →+* ℂ) → Multiset ℂ)
    (hm : ∀ τ, HasInfCharGL V τ (m τ)) : ∑ τ, (m τ).sum = 0 := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV.ne_bot
  have h := lie_oneL_eq_zero φ (hV.sqInt φ hφ).1
  rw [GlobalTheory.CompanionTheory.ClozelLie.lie_oneL_eq_sum_Eop, LinearMap.sum_apply,
    Finset.sum_congr rfl fun τ _ => trace_eq (hm τ) φ hφ, ← Finset.sum_smul] at h
  exact (smul_eq_zero.1 h).resolve_right h0

theorem im_sum_of {s : Multiset ℂ} {c : ℝ} (h : ∀ x ∈ s, x.im = c) :
    s.sum.im = (Multiset.card s : ℝ) * c := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.sum_cons, Complex.add_im, h a (by simp), ih fun x hx => h x (by simp [hx]), Multiset.card_cons]
    push_cast
    ring

theorem twist_eq_zero {N : ℕ} (hN : 0 < N) {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) {z : ℂ} (hz : z.re = 0)
    (m : (E →+* ℂ) → Multiset ℂ) (hm : ∀ τ, HasInfCharGL V τ (m τ)) (hr : ∀ τ, ∀ x ∈ m τ, (x + z).im = 0) :
    z = 0 := by
  have h := congrArg Complex.im (sum_trace_eq_zero hV m hm)
  have hτ : ∀ τ, ((m τ).sum).im = (N : ℝ) * (-z.im) := fun τ => by
    rw [im_sum_of (c := -z.im) fun x hx => by
        have := hr τ x hx
        simp only [Complex.add_im] at this
        linarith, (hm τ).1]
  rw [Complex.im_sum, Finset.sum_congr rfl fun τ _ => hτ τ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Complex.zero_im] at h
  have hc : (Fintype.card (E →+* ℂ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have him : z.im = 0 := by
    have := mul_eq_zero.1 h
    rcases this with h1 | h1
    · exact absurd h1 hc
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · exact absurd h2 hN'
      · linarith
  exact Complex.ext hz him

theorem untw_of_infOf {N : ℕ} (t : Tr E N) (ht : t.Good) (mf : (E →+* ℂ) → Multiset ℂ)
    (h : ∀ τ, t.InfOf τ (mf τ)) (hr : ∀ τ, ∀ x ∈ mf τ, x.im = 0) : t.Untw := by
  induction t generalizing mf with
  | leaf V z =>
    intro w hw
    simp only [Tr.twists, List.mem_singleton] at hw
    subst hw
    rcases ht with ⟨_, _, hz⟩ | ⟨hN, hV, hz⟩
    · exact hz
    · choose m₀ h₀ he using h
      refine twist_eq_zero hN hV hz m₀ h₀ fun τ x hx => ?_
      exact hr τ (x + w) (by rw [he τ]; exact Multiset.mem_map_of_mem _ hx)
  | node t₁ t₂ ih₁ ih₂ =>
    choose m₁ m₂ h₁ h₂ he using h
    intro w hw
    simp only [Tr.twists, List.mem_append] at hw
    rcases hw with hw | hw
    · exact ih₁ ht.1 m₁ h₁ (fun τ x hx => hr τ x (by rw [he τ]; exact Multiset.mem_add.2 (Or.inl hx))) w hw
    · exact ih₂ ht.2 m₂ h₂ (fun τ x hx => hr τ x (by rw [he τ]; exact Multiset.mem_add.2 (Or.inr hx))) w hw

theorem untwOfReal_holds : UntwOfReal := by
  intro E _ _ _ N t n ht hne hn hrs
  choose mf hmf using exists_infOf t ht
  have heq : ∀ τ, n τ = mf τ := fun τ =>
    GlobalTheory.BcSpehProof.hasInfCharGL_unique hne (hn τ) (hasInfCharGL_space t τ (mf τ) (hmf τ))
  exact untw_of_infOf t ht mf hmf fun τ x hx => (hrs τ).1 x (heq τ ▸ hx)

end PositivityTheory.Rg.BcB.SpectralAccumulation.Untw

end
