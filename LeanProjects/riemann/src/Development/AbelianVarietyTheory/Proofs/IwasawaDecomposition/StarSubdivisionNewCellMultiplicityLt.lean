import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfToRealRel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BalancedFormCellMultiplicityPosStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLinFormCutFaceOfCellInConeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLinFormCutFaceOfFaceOfConeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeGeneratorsOfLinFormEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqSubfamilyOfFaceSimplicialConePrimitiveStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NatCardTorsionQuotSpanDvdOfRangeSubsetStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearIndependentConsBalancedFormOfCoordNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellMultiplicityPositiveConeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRescalePrimitiveLinearIndependentCellStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.PolFan.StarNewCell

variable {X : Type} [AddCommGroup X]

theorem inRCone_trans {m n : ℕ} {δ : Fin m → LinearMap.BilinForm ℤ X} {γ : Fin n → LinearMap.BilinForm ℤ X}
    {β : LinearMap.BilinForm ℤ X} (hγ : ∀ k, InRCone δ (γ k)) (hβ : InRCone γ β) : InRCone δ β := by
  obtain ⟨c, hc, hβ⟩ := hβ
  choose a ha hγ using hγ
  refine ⟨fun i => ∑ k, c k * a k i, fun i => Finset.sum_nonneg fun k _ => mul_nonneg (hc k) (ha k i), ?_⟩
  rw [hβ]
  simp only [hγ, Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

theorem val_eq (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X}
    {β : LinearMap.BilinForm ℤ X} {c : Fin m → ℝ} (e : toReal β = ∑ i, c i • toReal (γ i)) :
    (h β : ℝ) = ∑ i, c i * (h (γ i) : ℝ) := by
  have := sum_mul_eq_of_sum_toReal_eq (j := LinearMap.id) Function.injective_id h (u := fun _ : Fin 1 => β) (w := γ)
    (a := fun _ => 1) (b := c) (by simpa using e)
  simpa using this

theorem val_nonneg (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X}
    {β : LinearMap.BilinForm ℤ X} (h0 : ∀ i, 0 ≤ h (γ i)) (hβ : InRCone γ β) : 0 ≤ h β := by
  obtain ⟨c, hc, e⟩ := hβ
  have : (0 : ℝ) ≤ h β := by
    rw [val_eq h e]; exact Finset.sum_nonneg fun i _ => mul_nonneg (hc i) (by exact_mod_cast h0 i)
  exact_mod_cast this

theorem val_zero (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X}
    {β : LinearMap.BilinForm ℤ X} (h0 : ∀ i, h (γ i) = 0) (hβ : InRCone γ β) : h β = 0 := by
  obtain ⟨c, hc, e⟩ := hβ
  have : (h β : ℝ) = 0 := by
    rw [val_eq h e]; exact Finset.sum_eq_zero fun i _ => by rw [h0 i]; simp
  exact_mod_cast this

theorem inRCone_cons_succ {n : ℕ} (x : LinearMap.BilinForm ℤ X) (p : Fin n → LinearMap.BilinForm ℤ X) (k : Fin n) :
    InRCone (Fin.cons x p : Fin (n + 1) → LinearMap.BilinForm ℤ X) (p k) := by
  simpa using inRCone_self (Fin.cons x p : Fin (n + 1) → LinearMap.BilinForm ℤ X) k.succ

theorem inRCone_cons_zero {n : ℕ} (x : LinearMap.BilinForm ℤ X) (p : Fin n → LinearMap.BilinForm ℤ X) :
    InRCone (Fin.cons x p : Fin (n + 1) → LinearMap.BilinForm ℤ X) x := by
  simpa using inRCone_self (Fin.cons x p : Fin (n + 1) → LinearMap.BilinForm ℤ X) 0

end GlobalTheory.PolFan.StarNewCell

open GlobalTheory.PolFan.StarNewCell in

theorem GlobalTheory.PolFan.cellMult_lt_of_star_new : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ lab w ψ' : InvFun (𝓞 E)),
    SimpLab H.bar q φ lab → IsCentreSet H.bar q φ w →
    (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
        Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell H.bar φ δ),
          LinearIndependent ℤ δ → (∀ i, IsPrim H.bar (⟨δ i, h.mem i⟩ : balForms H.bar X)) →
          ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 →
          ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal β = ∑ i, c i • toReal (δ i) → ∀ i, c i < 1) →
    ∀ M : ℕ, maxMult H.bar q φ ≤ M →
    ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
      Module.finrank (𝓞 E) X ≤ q → ∀ (n : ℕ) (γ' : Fin n → LinearMap.BilinForm ℤ X) (hγ' : IsCell H.bar ψ' γ'),
        LinearIndependent ℤ γ' → (∀ i, IsPrim H.bar (⟨γ' i, hγ'.mem i⟩ : balForms H.bar X)) →
        ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (β₀ : LinearMap.BilinForm ℤ X) (m' : ℕ) (s : Fin m' ↪ Fin m)
          (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell H.bar φ γ → β₀ ∈ balForms H.bar X → (∀ y, 0 ≤ β₀ y y) →
          w.evalZ β₀ = 1 → InRCone γ β₀ → IsFaceCut γ s h → 0 < h β₀ →
          IsCell H.bar ψ' (Fin.cons β₀ fun j => γ (s j)) → (∀ j, InRCone (Fin.cons β₀ fun j => γ (s j)) (γ' j)) →
          cellMult H.bar (fun i => (⟨γ' i, hγ'.mem i⟩ : balForms H.bar X)) < M := by
  intro E _ _ _ H q φ lab w ψ' hSL hCS hcoord M hM X _ _ _ _ hX n γ' hγ' hliγ' hprimγ' m γ β₀ m' s h hγ hβ₀ hβ₀p hw
    hβ₀γ hcut hpos hτ hγ'τ
  classical

  obtain ⟨m₀, δ, hδ, hliδ, -, hγδ⟩ := hSL.2 X hX m γ hγ
  obtain ⟨δt, hδt, hliδt, hprimδt, hδδt⟩ := GlobalTheory.T.exists_rescale_primitive_linearIndependent_cell H.bar φ δ hδ hliδ
  have hγδt : ∀ k, InRCone δt (γ k) := fun k => hδδt _ (hγδ k)

  obtain ⟨h₂, h₂0, h₂γ, h₂cut⟩ := GlobalTheory.T.exists_linForm_cut_face_of_cell_in_cone H.bar φ δt γ hδt hγ hγδt
  have hcutγ : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → h β = 0 →
      InRCone (fun k => γ (s k)) β :=
    fun β _ _ hβ hβ0 => GlobalTheory.T.inRealCone_generators_of_linForm_eq_zero γ h s β hcut.1 (fun i hi => (hcut.2 i).1 hi) hβ hβ0
  have hhs : ∀ k, h (γ (s k)) = 0 := fun k => (hcut.2 (s k)).2 ⟨k, rfl⟩
  obtain ⟨h₃, h₃0, h₃γs, h₃cut⟩ := GlobalTheory.T.exists_linForm_cut_face_of_face_of_cone H.bar δt γ (fun k => γ (s k)) h₂ h hδt.mem hδt.nonneg
    (fun k => inRCone_self γ (s k)) h₂0 h₂γ h₂cut hcut.1 hhs hcutγ

  set I : Finset (Fin m₀) := Finset.univ.filter (fun i => h₃ (δt i) = 0) with hI
  set eI : Fin I.card ↪ Fin m₀ := (I.orderEmbOfFin rfl).toEmbedding with heIdef
  have heI : ∀ i, i ∈ Set.range eI ↔ h₃ (δt i) = 0 := by
    intro i
    show i ∈ Set.range (I.orderEmbOfFin rfl) ↔ _
    rw [Finset.range_orderEmbOfFin]
    simp [I]
  have hsupp : ∀ β, InRCone δt β → h₃ β = 0 → InRCone (fun k => δt (eI k)) β :=
    fun β hβ h0 => GlobalTheory.T.inRealCone_generators_of_linForm_eq_zero δt h₃ eI β h₃0 (fun i hi => (heI i).2 hi) hβ h0

  obtain ⟨c, hc0, hcβ⟩ : InRCone δt β₀ := inRCone_trans hγδt hβ₀γ
  have hclt : ∀ i, c i < 1 := hcoord X hX m₀ δt hδt hliδt hprimδt β₀ hβ₀ hβ₀p hw c hc0 hcβ
  obtain ⟨j, hcj, hjI⟩ : ∃ j, 0 < c j ∧ h₃ (δt j) ≠ 0 := by
    by_contra hno
    push_neg at hno
    have h30 : h₃ β₀ = 0 := by
      have : (h₃ β₀ : ℝ) = 0 := by
        rw [val_eq h₃ hcβ]
        refine Finset.sum_eq_zero fun i _ => ?_
        rcases (hc0 i).eq_or_lt with hi | hi
        · rw [← hi, zero_mul]
        · rw [hno i hi]; simp
      exact_mod_cast this
    have := val_zero h hhs (h₃cut β₀ hβ₀ hβ₀p ⟨c, hc0, hcβ⟩ h30)
    omega

  have hprimβ₀ : ∀ hx : β₀ ∈ balForms H.bar X, IsPrim H.bar (⟨β₀, hx⟩ : balForms H.bar X) := by
    intro hx k β' hk
    refine (hCS X hX).2.1 β₀ hβ₀ hβ₀p hw k β' ?_
    have h' : β₀ = ((k • β' : balForms H.bar X) : LinearMap.BilinForm ℤ X) := congrArg Subtype.val hk
    rw [h', Submodule.coe_smul_of_tower, natCast_zsmul]

  set δs : Fin m₀ → balForms H.bar X := fun i => ⟨δt i, hδt.mem i⟩ with hδs
  set βs : balForms H.bar X := ⟨β₀, hβ₀⟩ with hβs
  have hliδs : LinearIndependent ℤ δs := LinearIndependent.of_comp (balForms H.bar X).subtype hliδt

  set ρs : Fin (I.card + 1) → balForms H.bar X := Fin.cons βs (fun k => δs (eI k)) with hρsdef
  obtain ⟨ρ, hρ0, hρs, hρv⟩ : ∃ ρ : Fin (I.card + 1) → LinearMap.BilinForm ℤ X, ρ 0 = β₀ ∧
      (∀ k, ρ k.succ = δt (eI k)) ∧ ∀ i, ρ i = (ρs i : LinearMap.BilinForm ℤ X) :=
    ⟨fun i => (ρs i : LinearMap.BilinForm ℤ X), by simp [ρs, βs], fun k => by simp [ρs, δs], fun i => rfl⟩
  have hjeI : j ∉ Set.range eI := fun hh => hjI ((heI j).1 hh)
  have hliρ : LinearIndependent ℤ ρ := by
    have h1 := GlobalTheory.T.linearIndependent_cons_balancedForm_of_coord_ne_zero H.bar δs βs c j eI hliδs hcβ hcj.ne' hjeI
    have h2 := h1.map' (balForms H.bar X).subtype (Submodule.ker_subtype _)
    have : ρ = (balForms H.bar X).subtype ∘ ρs := funext hρv
    rw [this]; exact h2
  have hρmem : ∀ i, ρ i ∈ balForms H.bar X := fun i => by rw [hρv]; exact (ρs i).2
  have hρnn : ∀ i y, 0 ≤ ρ i y y := by
    intro i; refine Fin.cases ?_ (fun k => ?_) i
    · rw [hρ0]; exact hβ₀p
    · rw [hρs]; exact hδt.nonneg _
  have hρprim : ∀ i, IsPrim H.bar (⟨ρ i, hρmem i⟩ : balForms H.bar X) := by
    have key : ∀ (x y : LinearMap.BilinForm ℤ X) (hx : x ∈ balForms H.bar X) (hy : y ∈ balForms H.bar X), x = y →
        IsPrim H.bar (⟨y, hy⟩ : balForms H.bar X) → IsPrim H.bar (⟨x, hx⟩ : balForms H.bar X) := by
      rintro x y hx hy rfl hp; exact hp
    intro i; refine Fin.cases ?_ (fun k => ?_) i
    · exact key _ _ _ hβ₀ hρ0 (hprimβ₀ hβ₀)
    · exact key _ _ _ (hδt.mem _) (hρs k) (hprimδt _)

  have hτρ : ∀ i, InRCone ρ ((Fin.cons β₀ fun j => γ (s j) : Fin (m' + 1) → LinearMap.BilinForm ℤ X) i) := by
    intro i; refine Fin.cases ?_ (fun k => ?_) i
    · rw [Fin.cons_zero, ← hρ0]; exact inRCone_self ρ 0
    · rw [Fin.cons_succ]
      exact inRCone_trans (fun l => hρs l ▸ inRCone_self ρ l.succ) (hsupp _ (hγδt (s k)) (h₃γs k))
  have hρτ : ∀ i, InRCone (Fin.cons β₀ fun j => γ (s j) : Fin (m' + 1) → LinearMap.BilinForm ℤ X) (ρ i) := by
    intro i; refine Fin.cases ?_ (fun k => ?_) i
    · rw [hρ0]; exact inRCone_cons_zero _ _
    · rw [hρs]
      exact inRCone_trans (fun l => inRCone_cons_succ β₀ (fun j => γ (s j)) l)
        (h₃cut _ (hδt.mem _) (hδt.nonneg _) (inRCone_self δt _) ((heI _).1 ⟨k, rfl⟩))

  obtain ⟨h₁, h₁0, h₁γ', h₁cut⟩ := GlobalTheory.T.exists_linForm_cut_face_of_cell_in_cone H.bar ψ' _ γ' hτ hγ' hγ'τ
  obtain ⟨s', hs', -⟩ := GlobalTheory.T.eq_subfamily_of_face_simplicialCone_primitive H.bar ρ γ' hρmem hγ'.mem h₁ hliρ hliγ' hρprim hprimγ'
    (fun k => inRCone_trans hτρ (hγ'τ k)) (fun i => val_nonneg h₁ h₁0 (hρτ i)) h₁γ'
    (fun i hi => h₁cut (ρ i) (hρmem i) (hρnn i) (hρτ i) hi)

  set J : Finset (Fin m₀) := Finset.univ.erase j with hJ
  have hJc : J.card = m₀ - 1 := by simp [J]
  set eJ : Fin (m₀ - 1) ↪ Fin m₀ := (J.orderEmbOfFin hJc).toEmbedding with heJdef
  have heJ : ∀ i, i ∈ Set.range eJ ↔ i ≠ j := by
    intro i
    show i ∈ Set.range (J.orderEmbOfFin hJc) ↔ _
    rw [Finset.range_orderEmbOfFin]
    simp [J]
  set ρ's : Fin (m₀ - 1 + 1) → balForms H.bar X := Fin.cons βs (fun k => δs (eJ k)) with hρ'sdef
  have hliρ' : LinearIndependent ℤ ρ's := GlobalTheory.T.linearIndependent_cons_balancedForm_of_coord_ne_zero H.bar δs βs c j eJ hliδs hcβ hcj.ne' (fun hh => (heJ j).1 hh rfl)
  have hmultρ' : (cellMult H.bar ρ's : ℝ) = c j * cellMult H.bar δs :=
    GlobalTheory.T.cell_multiplicity_positive_cone H.bar δs βs c j eJ hliδs hcβ hcj heJ (GlobalTheory.T.balancedFormCellMultiplicity_pos H.bar δs)
  have hrange : Set.range (fun i => (⟨γ' i, hγ'.mem i⟩ : balForms H.bar X)) ⊆ Set.range ρ's := by
    rintro _ ⟨k, rfl⟩
    have e := hs' k
    rcases Fin.eq_zero_or_eq_succ (s' k) with h0 | ⟨l, hl⟩
    · refine ⟨0, Subtype.ext ?_⟩
      simp [ρ's, βs]
      rw [e, h0, hρ0]
    · have hne : eI l ≠ j := fun hh => hjI (hh ▸ (heI (eI l)).1 ⟨l, rfl⟩)
      obtain ⟨r, hr⟩ := (heJ (eI l)).2 hne
      refine ⟨r.succ, Subtype.ext ?_⟩
      simp [ρ's, δs]
      rw [e, hl, hρs, hr]
  have hdvd : cellMult H.bar (fun i => (⟨γ' i, hγ'.mem i⟩ : balForms H.bar X)) ∣ cellMult H.bar ρ's :=
    GlobalTheory.T.natCard_torsion_quot_span_dvd_of_range_subset' (balForms H.bar X) ρ's _ hliρ' hrange
  have hle := Nat.le_of_dvd (GlobalTheory.T.balancedFormCellMultiplicity_pos H.bar ρ's) hdvd
  have hδpos := GlobalTheory.T.balancedFormCellMultiplicity_pos H.bar δs
  have hlt : (cellMult H.bar ρ's : ℝ) < cellMult H.bar δs := by
    rw [hmultρ']; exact mul_lt_of_lt_one_left (by exact_mod_cast hδpos) (hclt j)
  have hlt' : cellMult H.bar ρ's < cellMult H.bar δs := by exact_mod_cast hlt
  have hδsM : cellMult H.bar δs ≤ M := by
    have := (SmoothEnd.cellMult_le_maxMult hX hδt hliδt hprimδt).trans hM
    exact_mod_cast this
  omega
