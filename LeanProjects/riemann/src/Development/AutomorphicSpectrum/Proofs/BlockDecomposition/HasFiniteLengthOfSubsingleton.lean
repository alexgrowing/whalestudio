import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibRepApply
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthCoinvariantsExactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTwistedRankQuotientStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmegaEquivInducedFibreStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoinvariantsFiniteOfSmoothLeviStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreRepresentationSmoothStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthCoinvariantsSwapStatement

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology

namespace GlobalTheory.CompanionTheory.ThetaGLLen

section Small

variable {Γ G V U : Type} [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]

theorem hasFiniteLength_of_subsingleton [Subsingleton V] (ρ : Representation ℂ G V) : HasFiniteLength ρ := by
  have : Subsingleton ρ.asModule := inferInstanceAs (Subsingleton V)
  rw [HasFiniteLength, isFiniteLength_iff_isNoetherian_isArtinian]
  exact ⟨inferInstance, inferInstance⟩

theorem coinv_of_subsingleton [Subsingleton V] (τ : Representation ℂ (Γ × G) V) (ψ : Γ →* ℂˣ) :
    HasFiniteLength (coinv τ ψ) :=
  have : Subsingleton (V ⧸ twRel (τ.comp (MonoidHom.inl Γ G)) ψ) := Submodule.Quotient.subsingleton_iff.2 (Subsingleton.elim _ _)
  hasFiniteLength_of_subsingleton _

theorem coinv_of_equiv {τ : Representation ℂ (Γ × G) V} {τ' : Representation ℂ (Γ × G) U} (E : τ.Equiv τ')
    (ψ : Γ →* ℂˣ) (h : HasFiniteLength (coinv τ' ψ)) : HasFiniteLength (coinv τ ψ) := by
  let τ₀ : Representation ℂ (Γ × G) PUnit := Representation.trivial ℂ _ _
  let i : τ₀.IntertwiningMap τ := ⟨0, fun g => by ext v; simp⟩
  refine GlobalTheory.T.finite_length_coinvariants_exact Γ G PUnit V U τ₀ τ τ' i E.toIntertwiningMap E.toLinearEquiv.surjective
    (fun x => ?_) ψ (coinv_of_subsingleton _ _) h
  constructor
  · intro hx
    refine ⟨0, ?_⟩
    have : E.toLinearEquiv x = 0 := hx
    exact ((E.toLinearEquiv.map_eq_zero_iff).1 this).symm ▸ rfl
  · rintro ⟨y, rfl⟩
    show E.toLinearEquiv 0 = 0
    simp

end Small

section Strata

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

theorem stratum_finiteLength (hI : InductionFiniteLength k) {μ : kˣ →* ℂˣ} (hμ : IsSmoothChar μ) (κ : ℕ)
    (ψ : GL a k →* ℂˣ) : HasFiniteLength (coinv (omegaOn a b μ {κ}) ψ) := by
  by_cases hκ : κ ≤ Fintype.card b
  · let e : Fin κ ⊕ Fin (Fintype.card b - κ) ≃ b :=
      (stdSum (Nat.add_sub_cancel' hκ)).trans (Fintype.equivFin b).symm
    obtain ⟨E⟩ := GlobalTheory.T.omega_equiv_induced_fibre k a b (Fin κ) (Fin (Fintype.card b - κ)) e κ (Fintype.card_fin κ).symm μ hμ
    refine coinv_of_equiv E ψ (GlobalTheory.T.coinvariants_finite_of_smooth_levi k hI _ _ b _ _ e _ (GlobalTheory.T.fibre_representation_smooth k a _ _ μ hμ κ) ψ ?_)
    let τ := fibRep (k := k) a (Fin κ) (Fin (Fintype.card b - κ)) μ κ
    let ω : GL a k →* ℂˣ := (fibChar a (Fin κ) (Fin (Fintype.card b - κ)) μ).comp (MonoidHom.inl _ _)
    have hfin := GlobalTheory.T.finite_twisted_rank_quotient k a (Fin κ) κ (Fintype.card_fin κ).symm (ψ * ω⁻¹)
    have hle : twRel (rightRep (k := k) a (Fin κ) κ) (ψ * ω⁻¹) ≤ twRel (τ.comp (MonoidHom.inl _ _)) ψ := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g, φ, rfl⟩
      have h1 : ∀ φ' : SB (RankIn k a (Fin κ) {κ}), τ (g, 1) φ' = (ω g : ℂ) • rightRep (k := k) a (Fin κ) κ g φ' := by
        intro φ'
        refine Subtype.ext (funext fun y => ?_)
        show (fibRep a (Fin κ) (Fin (Fintype.card b - κ)) μ κ (g, 1, 1) φ').1 y = _
        rw [fibRep_apply]
        rfl
      have h2 : rightRep (k := k) a (Fin κ) κ g φ - (((ψ * ω⁻¹) g : ℂˣ) : ℂ) • φ =
          ((ω g)⁻¹ : ℂˣ).1 • (τ (g, 1) φ - (ψ g : ℂ) • φ) := by
        rw [h1, smul_sub, smul_smul, smul_smul]
        simp [mul_comm]
      rw [SetLike.mem_coe, h2]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, φ, rfl⟩)
    exact Module.Finite.of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle)
  · have : IsEmpty (RankIn k a b {κ}) := ⟨fun x => hκ (by
      have h := rank_le_card_height x.1
      rw [show x.1.rank = κ from x.2] at h
      exact h)⟩
    have : Subsingleton (SB (RankIn k a b {κ})) :=
      ⟨fun f g => Subtype.ext (funext fun x => isEmptyElim x)⟩
    exact coinv_of_subsingleton _ _

theorem filt_finiteLength (hI : InductionFiniteLength k) {μ : kˣ →* ℂˣ} (hμ : IsSmoothChar μ)
    (ψ : GL a k →* ℂˣ) (N : ℕ) (j κ : ℕ) (h : κ + j = N) :
    HasFiniteLength (coinv (filt a b μ (Set.Iio N) κ).toRepresentation ψ) := by
  induction j generalizing κ with
  | zero =>
    obtain rfl : κ = N := h
    have : Subsingleton (filt a b μ (Set.Iio κ) κ).toSubmodule :=
      ⟨fun f g => Subtype.ext (Subtype.ext (funext fun x =>
        (f.2 x x.2).trans (g.2 x x.2).symm))⟩
    exact coinv_of_subsingleton _ _
  | succ j ih =>
    have hs : ∀ r, r ∈ ({κ} : Set ℕ) ↔ κ ≤ r ∧ r < κ + 1 := fun r => by
      rw [Set.mem_singleton_iff]; omega
    have hmn : κ + 1 ≤ N := by omega
    have hle : (filt a b μ (Set.Iio N) (κ + 1)).toSubmodule ≤ (filt a b μ (Set.Iio N) κ).toSubmodule :=
      fun Φ hΦ x hx => hΦ x (Nat.lt_succ_of_lt hx)
    let i : (filt a b μ (Set.Iio N) (κ + 1)).toRepresentation.IntertwiningMap
        (filt a b μ (Set.Iio N) κ).toRepresentation :=
      ⟨Submodule.inclusion hle, fun g => by ext; rfl⟩
    refine GlobalTheory.T.finite_length_coinvariants_exact _ _ _ _ _ _ _ _ i (resFilt μ hmn hs) (resFilt_surjective μ hmn hs) (fun Φ => ?_) ψ
      (ih (κ + 1) (by omega)) (stratum_finiteLength hI hμ κ ψ)
    constructor
    · intro h0
      have := (ker_resFilt μ hmn hs Φ).1 h0
      exact ⟨⟨Φ.1, this⟩, rfl⟩
    · rintro ⟨Ψ, rfl⟩
      exact (ker_resFilt μ hmn hs _).2 Ψ.2

def toFilt (μ : kˣ →* ℂˣ) (N : ℕ) (hN : ∀ x : Matrix b a k, x.rank < N) :
    (omega a b μ).Equiv (filt a b μ (Set.Iio N) 0).toRepresentation :=
  .mk
    { toFun := fun Φ => ⟨⟨fun x => Φ.1 x.1, comp_mem_SB_of_isInducing IsInducing.subtypeVal Φ isClosed_univ
          (fun _ => trivial) fun x _ _ => ⟨⟨x, hN x⟩, rfl⟩⟩, fun _ hx => absurd hx (Nat.not_lt_zero _)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun Ψ => ⟨fun x => Ψ.1.1 ⟨x, hN x⟩, comp_mem_SB_of_isInducing
          ((IsInducing.subtypeVal.of_comp_iff (f := fun x : Matrix b a k => (⟨x, hN x⟩ : RankIn k a b (Set.Iio N)))).1 IsInducing.id) Ψ.1 isClosed_univ (fun _ => trivial)
          fun x _ _ => ⟨x.1, rfl⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl } (fun _ => rfl)

end Strata

section Main

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

abbrev thetaQuot (μ χ : kˣ →* ℂˣ) := coinv (omega a b μ⁻¹) (detChar a χ)

variable {a b}

theorem twRel_omega (μ χ : kˣ →* ℂˣ) :
    twRel ((omega a b μ⁻¹).comp (MonoidHom.inl _ _)) (detChar a χ) =
      Submodule.span ℂ {w : SB (Matrix b a k) | ∃ (g : GL a k) (Φ : SB (Matrix b a k)),
        w.1 = om μ g 1 Φ.1 - (χ (GeneralLinearGroup.det g) : ℂ) • Φ.1} := by
  unfold twRel
  refine congrArg (Submodule.span ℂ) (Set.ext fun w => ?_)
  constructor
  · rintro ⟨g, Φ, rfl⟩
    refine ⟨g, Φ, ?_⟩
    have := omega_eq_om μ⁻¹ g (1 : GL b k) Φ
    rw [inv_inv] at this
    exact congrArg₂ (· - ·) this rfl
  · rintro ⟨g, Φ, h⟩
    refine ⟨g, Φ, Subtype.ext ?_⟩
    have := omega_eq_om μ⁻¹ g (1 : GL b k) Φ
    rw [inv_inv] at this
    exact h.trans (congrArg₂ (· - ·) this.symm rfl)

theorem thetaQuot_mk (μ χ : kˣ →* ℂˣ) (h : GL b k) (Φ Ψ : SB (Matrix b a k)) (hΨ : Ψ.1 = om μ 1 h Φ.1) :
    thetaQuot a b μ χ h (Submodule.Quotient.mk Φ) = Submodule.Quotient.mk Ψ := by
  have := omega_eq_om μ⁻¹ (1 : GL a k) h Φ
  rw [inv_inv] at this
  exact congrArg Submodule.Quotient.mk (Subtype.ext (this.trans hΨ.symm))

theorem thetaQuot_finiteLength (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) {μ : kˣ →* ℂˣ}
    (hμ : IsSmoothChar μ) (χ : kˣ →* ℂˣ) : HasFiniteLength (thetaQuot a b μ χ) := by
  have hI : InductionFiniteLength k := (hBZ k).2.2.1
  have hN : ∀ x : Matrix b a k, x.rank < Fintype.card a + 1 := fun x =>
    Nat.lt_succ_of_le (rank_le_card_width x)
  exact coinv_of_equiv (toFilt μ⁻¹ _ hN) _
    (filt_finiteLength hI hμ.inv _ (Fintype.card a + 1) (Fintype.card a + 1) 0 (by omega))

variable (a b)

abbrev thetaQuotSwap (μ χ : kˣ →* ℂˣ) :=
  coinv ((omega a b μ⁻¹).comp (MulEquiv.prodComm (M := GL b k) (N := GL a k)).toMonoidHom) (detChar b χ)

variable {a b}

theorem thetaQuotSwap_finiteLength (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) {μ : kˣ →* ℂˣ}
    (hμ : IsSmoothChar μ) (χ : kˣ →* ℂˣ) : HasFiniteLength (thetaQuotSwap a b μ χ) :=
  GlobalTheory.T.finite_length_coinvariants_swap k a b μ χ (thetaQuot_finiteLength hBZ hμ χ⁻¹)

theorem main (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) (n r : ℕ) {μ : kˣ →* ℂˣ} (hμ : IsSmoothChar μ)
    (χ : kˣ →* ℂˣ) : HasFiniteLength (thetaQuot (k := k) (Fin r) (Fin n) μ χ) ∧
      HasFiniteLength (thetaQuotSwap (k := k) (Fin r) (Fin n) μ χ) :=
  ⟨thetaQuot_finiteLength hBZ hμ χ, thetaQuotSwap_finiteLength hBZ hμ χ⟩

end Main

end GlobalTheory.CompanionTheory.ThetaGLLen
