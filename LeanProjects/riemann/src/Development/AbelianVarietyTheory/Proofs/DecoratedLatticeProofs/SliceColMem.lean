import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationTwoVariableModelAndLineExte
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatContrIntIndicator
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsPreserveSchwartzBruhatAndSurjective
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.LocMod.GValProof

section
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem card_frame {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k N Y) : Fintype.card Y = N := by
  apply le_antisymm
  · calc Fintype.card Y = (F.γ * F.β).rank := by rw [F.γβ, Matrix.rank_one]
      _ ≤ F.β.rank := Matrix.rank_mul_le_right _ _
      _ ≤ Fintype.card (Fin N) := Matrix.rank_le_card_height _
      _ = N := Fintype.card_fin N
  · calc N = Fintype.card (Fin N) := (Fintype.card_fin N).symm
      _ = (F.β * F.γ).rank := by rw [F.βγ, Matrix.rank_one]
      _ ≤ F.γ.rank := Matrix.rank_mul_le_right _ _
      _ ≤ Fintype.card Y := Matrix.rank_le_card_height _

theorem core_of_bes (p : Place D k) {ρ : ℕ} (B : BesLev D ρ) (s : k) {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
    (FA : Frame k B.A.rank n) (G : Frame k B.V.rank (n ⊕ Fin c)) (h : p.IsBesFrame B s FA G) :
    ∃ F₀ : Frame k B.V₀.rank (n ⊕ Unit), p.IsCoreFrame B s FA F₀ := by
  obtain ⟨hc, hA, -, hz, -⟩ := h
  let f : D.host.E →+* k := p.π.comp (incA D)
  have hpr : ∀ a, p.pr a = f a := fun _ => rfl
  let e : n ⊕ Unit → n ⊕ Fin c := Sum.elim Sum.inl fun _ => Sum.inr ⟨ρ, by omega⟩
  have he : Function.Injective e := by
    rintro (a | ⟨⟩) (b | ⟨⟩) hab <;> simp_all [e]
  let βA : Matrix (Fin B.V₀.rank) n k := B.o.iA.map p.pr * FA.β
  let β : Matrix (Fin B.V₀.rank) (n ⊕ Unit) k :=
    Matrix.of fun r y => Sum.elim (fun a => βA r a) (fun _ => s * p.pr (vecB B.o B.ζ r)) y
  let I : Matrix (Fin B.V.rank) (Fin B.V₀.rank) k := B.d.i₀.map p.pr
  have hmap : I * B.o.iA.map p.pr = (B.d.i₀ * B.o.iA).map p.pr := (Matrix.map_mul (f := f)).symm
  have hIβ : I * β = G.β.submatrix id e := by
    ext r (a | ⟨⟩)
    · simp only [submatrix_apply, id, e, Sum.elim_inl]
      rw [hA]
      have : (I * β) r (Sum.inl a) = (I * βA) r a := by
        simp only [Matrix.mul_apply, β, Matrix.of_apply, Sum.elim_inl]
      rw [this, ← Matrix.mul_assoc, hmap]
    · simp only [submatrix_apply, id, e, Sum.elim_inr]
      rw [hz ⟨ρ, by omega⟩ rfl r, hpr, RingHom.map_mulVec]
      simp only [Matrix.mul_apply, β, Matrix.of_apply, Sum.elim_inr, mulVec, dotProduct, Finset.mul_sum, I,
        Function.comp_apply, hpr]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Matrix.map_apply, hpr]
      ring
  let γ : Matrix (n ⊕ Unit) (Fin B.V₀.rank) k := G.γ.submatrix e id * I
  have hγβ : γ * β = 1 := by
    rw [Matrix.mul_assoc, hIβ, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, G.γβ, Matrix.submatrix_one _ he]
  have hcard : Fintype.card (n ⊕ Unit) = B.V₀.rank := by
    have h1 := card_frame G
    have h2 := B.d.rank_add
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit] at h1 ⊢
    omega
  have hβγ : β * γ = 1 := (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivFinOfCardEq hcard)).1 hγβ
  exact ⟨⟨β, γ, hβγ, hγβ⟩, fun r a => rfl, fun r => rfl⟩

theorem hz_link (p : Place D k) {ρ σ : ℕ} (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) :
    p.hz B = -p.xi ^ 2 * p.hz B' := by
  let f : D.host.E →+* k := p.π.comp (incA D)
  have hpr : ∀ a, p.pr a = f a := fun _ => rfl
  rw [Place.hz, Place.hz, Place.xi, l.norm, hpr, hpr, hpr, map_mul, map_mul, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, map_neg]
  ring

theorem cont_of_cond (ψ : AddChar k Circle) (h : HasConductor ψ 1) : Continuous ψ := h.continuous

theorem one_mem_SB (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] :
    (Set.indicator {x : Matrix n n' k | ∀ r q, x r q ∈ 𝒪[k]} fun _ => (1 : ℂ)) ∈ SB (Matrix n n' k) := by
  set S : Set (Matrix n n' k) := {x | ∀ r q, x r q ∈ 𝒪[k]} with hSdef
  have hS : (S : Set (n → n' → k)) = Set.univ.pi fun _ => Set.univ.pi fun _ => (𝒪[k] : Set k) := by
    ext x
    exact ⟨fun h r _ q _ => h r q, fun h r q => h r (Set.mem_univ _) q (Set.mem_univ _)⟩
  have hO : IsOpen S := by
    change IsOpen (S : Set (n → n' → k))
    rw [hS]
    exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ =>
      Valuation.isOpen_integer (v := valuation k)
  have hK : IsCompact S := by
    change IsCompact (S : Set (n → n' → k))
    rw [hS]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k 1
  refine ⟨?_, HasCompactSupport.intro hK fun x hx => by simp [Set.indicator, hx]⟩
  refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
  by_cases hx : x ∈ S
  · exact ⟨S, hO, hx, fun y hy => by simp [Set.indicator, hy, hx]⟩
  · exact ⟨Sᶜ, hK.isClosed.isOpen_compl, hx, fun y hy => by
      have hy' : y ∉ S := hy
      simp [Set.indicator, hy', hx]⟩

theorem sliceCol_mem {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {f : Matrix n (n' ⊕ Unit) k → ℂ}
    (hf : f ∈ SB _) : (fun a : Matrix n n' k => f (fromCols a 0)) ∈ SB _ := by
  have hc : Continuous fun a : Matrix n n' k => fromCols a (0 : Matrix n Unit k) := by
    refine continuous_matrix fun i j => ?_
    rcases j with j | j
    · simp only [fromCols_apply_inl]; exact continuous_id.matrix_elem i j
    · simp only [fromCols_apply_inr]; exact continuous_const
  have hd : Continuous fun x : Matrix n (n' ⊕ Unit) k => x.toCols₁ :=
    continuous_matrix fun i j => continuous_id.matrix_elem i (Sum.inl j)
  refine ⟨hf.1.comp_continuous hc, HasCompactSupport.intro (hf.2.isCompact.image hd) fun a ha => ?_⟩
  by_contra h0
  exact ha ⟨fromCols a 0, subset_tsupport _ h0, toCols₁_fromCols _ _⟩

theorem sliceRow_mem {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {f : Matrix (n ⊕ Unit) n' k → ℂ}
    (hf : f ∈ SB _) : (fun a : Matrix n n' k => f (fromRows a 0)) ∈ SB _ := by
  have hc : Continuous fun a : Matrix n n' k => fromRows a (0 : Matrix Unit n' k) := by
    refine continuous_matrix fun i j => ?_
    rcases i with i | i
    · simp only [fromRows_apply_inl]; exact continuous_id.matrix_elem i j
    · simp only [fromRows_apply_inr]; exact continuous_const
  have hd : Continuous fun x : Matrix (n ⊕ Unit) n' k => x.toRows₁ :=
    continuous_matrix fun i j => continuous_id.matrix_elem (Sum.inl i) j
  refine ⟨hf.1.comp_continuous hc, HasCompactSupport.intro (hf.2.isCompact.image hd) fun a ha => ?_⟩
  by_contra h0
  exact ha ⟨fromRows a 0, subset_tsupport _ h0, toRows₁_fromRows _ _⟩
end

theorem gval : ∀ (D : D7), FlatBF D → FlatFB D → ContrLoc D → GlobalTheory.LocFlat.SymCollapse →
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν →
  ∀ (p : Place D k) (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]
    (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.IsChar ψ S.ψ → ∀ (j c : ℕ) (H : j + 1 + 1 + c = s), ∃ C : ℂ, C ≠ 0 ∧
  ∀ (σ : ℕ) (B : BesLev D (σ + 1))
    (J : JacLev D (σ + 1)) (B' : BesLev D σ) (F : Dbl p B J B' (XIx (Fin κ) t j) (XIx (Fin κ) t (j + 1)) (XIx (Fin κ) t (j + 1 + 1)) c)
    (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank)
    (c₁ : WO B.A J.W₀ →₀ ℂ) (c₂ : WO J.W₀ B'.A →₀ ℂ),
    p.IsCombAt ψ F.F₀ F.F₁ c₁ ((S.T t).entry S.ψ ν j (c + 1) (by omega) 1 1) →
    p.IsCombAt ψ F.F₁ F.F₂ c₂ ((S.T t).entry S.ψ ν (j + 1) c H 1 1) →
  ∀ T₁ T₂, p.IsModel ψ F.G₀ F.G₁ T₁ → p.IsModel ψ F.G₁ F.G₂ T₂ → ∀ Φ₁ Φ₂ O₁ O₂,
    Φ₁.1 = (S.T t).Phi j (c + 1 + 1) (by omega) → Φ₂.1 = (S.T t).Phi (j + 1) (c + 1) (by omega) → IsOne O₁ → IsOne O₂ →
    GlobalTheory.Unf.contr l J.W₀ vL (flatBF s₁ (T₁ Φ₁)) (flatFB s₂ (T₂ Φ₂)) =
      C • biComb ψ B.A J.W₀ B'.A c₁ c₂ (GlobalTheory.Unf.contr l J.W₀ vL (flatBF s₁ (T₁ O₁)) (flatFB s₂ (T₂ O₂))) := by
  intro D hBF hFB hCL hSym k _ _ _ _ _ _ ν hν p s κ S t _ _ ψ hstd hchar j c H
  by_cases hc : ∃ r, c = 2 * r
  swap
  · refine ⟨1, one_ne_zero, ?_⟩
    intro σ B J B' F
    exact absurd ⟨σ, by have := F.bes.1; omega⟩ hc
  obtain ⟨r, hr⟩ := hc
  obtain ⟨-, hPC, hPR, hDS⟩ := hSym k ν hν s κ S t
  obtain ⟨-, C, hC, hval⟩ := hDS j c H r hr
  refine ⟨(C : ℂ), by exact_mod_cast hC.ne', ?_⟩
  intro σ B J B' F s₁ s₂ l vL c₁ c₂ hc₁ hc₂ T₁ T₂ hT₁ hT₂ Φ₁ Φ₂ O₁ O₂ hΦ₁ hΦ₂ hO₁ hO₂
  have hσ : σ = r := by have := F.bes.1; omega
  subst hσ
  have hψc : Continuous S.ψ := cont_of_cond S.ψ S.cond
  obtain ⟨C₀, hC₀⟩ := core_of_bes p B F.s F.F₀ F.G₀ F.bes
  obtain ⟨C₂, hC₂⟩ := core_of_bes p B' (F.s * p.xi) F.F₂ F.G₂ F.bes'
  have hjac : p.IsJacFrame J F.s (-p.xi ^ 2 * p.hz B') F.F₁ F.G₁ := by
    rw [← hz_link p B B' l]; exact F.jac
  obtain ⟨U₁, hU₁, hU₁e⟩ := hBF k p ν hν.1 ψ S.ψ hchar (σ + 1) B J s₁ F.s F.s_ne _ _ (c + 1 + 1) F.F₀ C₀ F.G₀ F.F₁ F.G₁ hC₀ F.bes F.jac T₁ hT₁
  obtain ⟨U₂, hU₂, hU₂e⟩ := hFB k p ν hν.1 ψ S.ψ hchar σ J B' s₂ F.s F.s_ne _ _ (c + 1) F.F₁ F.G₁ F.F₂ C₂ F.G₂ hjac hC₂ F.bes' T₂ hT₂
  obtain ⟨Λ, hΛ, hΛe⟩ := hCL k p ν hν.1 ψ hstd S.ψ hchar (σ + 1) σ B B' l J.W₀ vL F.s F.s_ne _ _ _ F.F₀ C₀ F.F₁ F.F₂ C₂ hC₀ hC₂ U₁ U₂ hU₁ hU₂
  have hfl := GlobalTheory.LocFlat.flat_SB_onto k S.ψ ν hψc hν.1
  have m₁ := fun Φ : SB _ => ((hfl (XIx (Fin κ) t (j + 1)) (XIx (Fin κ) t j) (c + 1 + 1) (σ + 1 + 1) (by omega)).1 (by omega)).1 Φ.1 Φ.2
  have m₂ := fun Φ : SB _ => ((hfl (XIx (Fin κ) t (j + 1 + 1)) (XIx (Fin κ) t (j + 1)) (c + 1) (σ + 1) (by omega)).2 (by omega)).1 Φ.1 Φ.2
  let Ψ₁ : SB _ := ⟨_, m₁ Φ₁⟩
  let Ψ₂ : SB _ := ⟨_, m₂ Φ₂⟩
  let P₁ : SB _ := ⟨_, m₁ O₁⟩
  let P₂ : SB _ := ⟨_, m₂ O₂⟩
  rw [hU₁e Φ₁ Ψ₁ rfl, hU₂e Φ₂ Ψ₂ rfl, hU₁e O₁ P₁ rfl, hU₂e O₂ P₂ rfl]
  obtain ⟨Ξ, hΞ, e1⟩ := hΛe Ψ₁ Ψ₂
  obtain ⟨ΞO, hΞO, e2⟩ := hΛe P₁ P₂
  rw [e1, e2]

  have hE₁ : (S.T t).entry S.ψ ν j (c + 1) (by omega) 1 1 ∈ SB _ := by
    obtain ⟨C', hC', hpc⟩ := hPC j (c + 1) (by omega) (σ + 1) (by omega)
    have hs := sliceCol_mem Ψ₁.2
    have e : (S.T t).entry S.ψ ν j (c + 1) (by omega) 1 1 = (C'⁻¹ : ℂ) • fun a => Ψ₁.1 (fromCols a 0) := by
      funext a
      simp only [Ψ₁, Pi.smul_apply, smul_eq_mul]
      rw [hΦ₁, hpc]
      have hC'0 : (C' : ℂ) ≠ 0 := by exact_mod_cast hC'.ne'
      simp only [toCols₁_fromCols, fromCols_apply_inr, Matrix.zero_apply]
      have hz : (fun _ => (0 : k)) ∈ box (XIx (Fin κ) t (j + 1)) (S.ϖ ^ (σ + 1))⁻¹ := (box _ _).zero_mem
      simp only [hz, if_true, mul_one]
      rw [← mul_assoc, inv_mul_cancel₀ hC'0, one_mul]
    rw [e]; exact (SB _).smul_mem _ hs
  have hE₂ : (S.T t).entry S.ψ ν (j + 1) c H 1 1 ∈ SB _ := by
    obtain ⟨C', hC', hpr⟩ := hPR (j + 1) c H σ hr
    have hs := sliceRow_mem Ψ₂.2
    have e : (S.T t).entry S.ψ ν (j + 1) c H 1 1 = (C'⁻¹ : ℂ) • fun a => Ψ₂.1 (fromRows a 0) := by
      funext a
      simp only [Ψ₂, Pi.smul_apply, smul_eq_mul]
      rw [hΦ₂, hpr]
      have hC'0 : (C' : ℂ) ≠ 0 := by exact_mod_cast hC'.ne'
      simp only [toRows₁_fromRows, fromRows_apply_inr, Matrix.zero_apply]
      have hz : a.fromRows (0 : Matrix Unit (XIx (Fin κ) t (j + 1)) k) (Sum.inr ()) ∈ box (XIx (Fin κ) t (j + 1)) (S.ϖ ^ (σ + 1)) := (box _ _).zero_mem
      simp only [hz, if_true, mul_one]
      rw [← mul_assoc, inv_mul_cancel₀ hC'0, one_mul]
    rw [e]; exact (SB _).smul_mem _ hs
  let E₁ : SB _ := ⟨_, hE₁⟩
  let E₂ : SB _ := ⟨_, hE₂⟩
  have hCne : (C : ℂ) ≠ 0 := by exact_mod_cast hC.ne'
  have hΞ' : ∀ q, ((C : ℂ)⁻¹ • Ξ).1 q = E₁.1 q.1 * E₂.1 q.2 := by
    intro q
    rw [Submodule.coe_smul, Pi.smul_apply, hΞ]
    simp only [Ψ₁, Ψ₂, E₁, E₂]
    rw [hΦ₁, hΦ₂, hval q, smul_eq_mul]
    field_simp
  have hΞe : Ξ = (C : ℂ) • ((C : ℂ)⁻¹ • Ξ) := by rw [smul_smul, mul_inv_cancel₀ hCne, one_smul]

  have hun := GlobalTheory.LocFlat.flat_contr_intIndicator k S.ψ ν S.cond hν
  let Q₁ : SB (Matrix (XIx (Fin κ) t (j + 1)) (XIx (Fin κ) t j) k) := ⟨_, one_mem_SB _ _⟩
  let Q₂ : SB (Matrix (XIx (Fin κ) t (j + 1 + 1)) (XIx (Fin κ) t (j + 1)) k) := ⟨_, one_mem_SB _ _⟩
  have hP₁ : P₁.1 = Set.indicator {x : Matrix (XIx (Fin κ) t (j + 1)) (XIx (Fin κ) t j ⊕ Unit) k | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1 := by
    simp only [P₁]
    rw [hO₁, (hun (XIx (Fin κ) t (j + 1)) (XIx (Fin κ) t j) (XIx (Fin κ) t j) (c + 1 + 1) (σ + 1 + 1)).1, if_neg (by omega)]
  have hP₂ : P₂.1 = Set.indicator {x : Matrix (XIx (Fin κ) t (j + 1 + 1) ⊕ Unit) (XIx (Fin κ) t (j + 1)) k | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1 := by
    simp only [P₂]
    rw [hO₂, (hun (XIx (Fin κ) t (j + 1 + 1)) (XIx (Fin κ) t (j + 1)) (XIx (Fin κ) t j) (c + 1) (σ + 1)).2.1 (by omega) (by omega)]
  have hΞO' : ∀ q, ΞO.1 q = Q₁.1 q.1 * Q₂.1 q.2 := by
    intro q
    rw [hΞO, hP₁, hP₂]
    exact (hun (XIx (Fin κ) t (j + 1)) (XIx (Fin κ) t j) (XIx (Fin κ) t (j + 1 + 1)) 0 0).2.2 q
  have hbi := (GlobalTheory.BiComb.comb_bimodel_and_line D k p ψ _ _ _).1 B.A J.W₀ B'.A F.F₀ F.F₁ F.F₂ Λ c₁ c₂ E₁ Q₁ E₂ Q₂ ((C : ℂ)⁻¹ • Ξ) ΞO hΛ hc₁ hc₂ rfl rfl hΞ' hΞO'
  rw [hΞe, map_smul, hbi]

theorem gval_of_laws : ∀ (D : D7), FlatBF D → FlatFB D → ContrLoc D → GlobalTheory.LocFlat.SymCollapse → GVal D := by
  intro D hBF hFB hCL hSym k _ _ _ _ _ _ ν hν p s κ S t _ _ ψ hchar j c H
  by_cases hstd : IsStdChar D ψ (-1)
  · exact gval D hBF hFB hCL hSym k ν hν p s κ S t ψ hstd hchar j c H
  · refine ⟨1, one_ne_zero, ?_⟩
    intro σ B J B' F s₁
    exact absurd s₁.weil.std hstd

end GlobalTheory.LocMod.GValProof
