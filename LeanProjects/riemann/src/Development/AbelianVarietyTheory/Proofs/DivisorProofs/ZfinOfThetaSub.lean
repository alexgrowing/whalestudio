import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompFinEqZeroOfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordHolomorphicAndUniform
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalSpanCommutant
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLineCorrespondsToLineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralOperatorCommutesLineDerivativeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLineFactorAsProductLinesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtProductOfRealLinesStatement

noncomputable section

namespace GlobalTheory.ThK.FiniteLevelDerivatives

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open GlobalTheory.WeakHolFamily

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Fun

variable {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

omit [NumberField E] in
theorem dop_eq_sum (z : List (ℝ → GAd σ J) →₀ ℂ) (f : GAd σ J → ℂ) :
    dop z f = ∑ l ∈ z.support, z l • l.foldr lineDer f := by
  funext g
  simp [dop, Finsupp.sum, Finset.sum_apply]

theorem dop_add {z : List (ℝ → GAd σ J) →₀ ℂ} (hz : ∀ l ∈ z.support, ∀ γ ∈ l, IsRealLine σ J γ) {f h : GAd σ J → ℂ}
    (hf : IsSm σ J f) (hh : IsSm σ J h) : dop z (f + h) = dop z f + dop z h := by
  simp only [dop_eq_sum, ← Finset.sum_add_distrib, ← smul_add]
  exact Finset.sum_congr rfl fun l hl => by rw [foldr_add hf hh l (hz l hl)]

theorem dop_smul (z : List (ℝ → GAd σ J) →₀ ℂ) (c : ℂ) (f : GAd σ J → ℂ) : dop z (c • f) = c • dop z f := by
  simp only [dop_eq_sum, Finset.smul_sum, foldr_smul]
  exact Finset.sum_congr rfl fun l _ => smul_comm _ _ _

theorem zfin_add {f h : GAd σ J → ℂ} (hf : IsSm σ J f) (hh : IsSm σ J h)
    (h1 : FiniteDimensional ℂ (Submodule.span ℂ {u | ∃ z, IsCentral σ J z ∧ u = dop z f}))
    (h2 : FiniteDimensional ℂ (Submodule.span ℂ {u | ∃ z, IsCentral σ J z ∧ u = dop z h})) :
    FiniteDimensional ℂ (Submodule.span ℂ {u | ∃ z, IsCentral σ J z ∧ u = dop z (f + h)}) := by
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {u | ∃ z, IsCentral σ J z ∧ u = dop z f} ⊔
    Submodule.span ℂ {u | ∃ z, IsCentral σ J z ∧ u = dop z h}) (Submodule.span_le.2 ?_)
  rintro _ ⟨z, hz, rfl⟩
  rw [dop_add hz.1 hf hh]
  exact Submodule.add_mem_sup (Submodule.subset_span ⟨z, hz, rfl⟩) (Submodule.subset_span ⟨z, hz, rfl⟩)

theorem zfin_smul {f : GAd σ J → ℂ} (c : ℂ)
    (h1 : FiniteDimensional ℂ (Submodule.span ℂ {u | ∃ z, IsCentral σ J z ∧ u = dop z f})) :
    FiniteDimensional ℂ (Submodule.span ℂ {u | ∃ z, IsCentral σ J z ∧ u = dop z (c • f)}) := by
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {u | ∃ z, IsCentral σ J z ∧ u = dop z f})
    (Submodule.span_le.2 ?_)
  rintro _ ⟨z, hz, rfl⟩
  rw [dop_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨z, hz, rfl⟩)

theorem zfin_zero : FiniteDimensional ℂ (Submodule.span ℂ {u | ∃ z, IsCentral σ J z ∧ u = dop z (0 : GAd σ J → ℂ)}) := by
  refine Submodule.finiteDimensional_of_le (S₂ := ⊥) (Submodule.span_le.2 ?_)
  rintro _ ⟨z, -, rfl⟩
  have := dop_smul z 0 (0 : GAd σ J → ℂ)
  simpa using this

theorem zfin_of_chains (A : Submodule ℂ (GAd σ J → ℂ)) (hsm : ∀ ψ ∈ A, IsSm σ J ψ)
    (hder : ∀ γ, IsRealLine σ J γ → ∀ ψ ∈ A, lineDer γ ψ ∈ A) (K : Set (GAd σ J)) (hK : ∀ k ∈ K, k ∈ infPts σ J)
    (hKA : ∀ k ∈ K, ∀ ψ ∈ A, (fun x => ψ (x * k)) ∈ A) (hr : Module.rank ℂ A ≤ Cardinal.aleph0)
    (hL : ∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GAd σ J → ℂ)), StrictMono N →
      (∀ i, N i ≤ A ∧ (∀ γ, IsRealLine σ J γ → ∀ ψ ∈ N i, lineDer γ ψ ∈ N i) ∧
        ∀ k ∈ K, ∀ ψ ∈ N i, (fun x => ψ (x * k)) ∈ N i) → m ≤ L)
    {ψ : GAd σ J → ℂ} (hψ : ψ ∈ A) :
    FiniteDimensional ℂ (Submodule.span ℂ {u | ∃ z, IsCentral σ J z ∧ u = dop z ψ}) := by
  let D : ∀ γ, IsRealLine σ J γ → Module.End ℂ A := fun γ hγ =>
    { toFun := fun u => ⟨lineDer γ u.1, hder γ hγ _ u.2⟩
      map_add' := fun u v => Subtype.ext (lineDer_add (hsm _ u.2) (hsm _ v.2) hγ)
      map_smul' := fun c u => Subtype.ext (lineDer_smul c u.1 γ) }
  let R : ∀ k ∈ K, Module.End ℂ A := fun k hk =>
    { toFun := fun u => ⟨fun x => u.1 (x * k), hKA k hk _ u.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let S : Set (Module.End ℂ A) := {s | ∃ γ hγ, s = D γ hγ} ∪ {s | ∃ k hk, s = R k hk}
  have hfold : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) → ∀ u ∈ A, l.foldr lineDer u ∈ A := fun l hl u hu => by
    induction l with
    | nil => exact hu
    | cons γ l ih => exact hder γ (hl γ List.mem_cons_self) _ (ih fun γ' h => hl γ' (List.mem_cons_of_mem _ h))
  have hfin := GlobalTheory.FiniteLengthCommutant.finiteDimensional_span_commutant A S hr (by
    obtain ⟨L, hL⟩ := hL
    refine ⟨L, fun m N hN hS => hL m (fun i => (N i).map A.subtype)
      ((Submodule.map_strictMono_of_injective A.injective_subtype).comp hN) fun i => ⟨Submodule.map_subtype_le _ _, ?_, ?_⟩⟩
    · rintro γ hγ _ ⟨u, hu, rfl⟩
      exact ⟨_, hS i _ (Or.inl ⟨γ, hγ, rfl⟩) u hu, rfl⟩
    · rintro k hk _ ⟨u, hu, rfl⟩
      exact ⟨_, hS i _ (Or.inr ⟨k, hk, rfl⟩) u hu, rfl⟩) ⟨ψ, hψ⟩
  refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ
    {w : A | ∃ T : Module.End ℂ A, (∀ s ∈ S, s * T = T * s) ∧ T ⟨ψ, hψ⟩ = w}).map A.subtype) (Submodule.span_le.2 ?_)
  rintro _ ⟨z, hz, rfl⟩
  let T : Module.End ℂ A :=
    { toFun := fun u => ⟨dop z u.1, by
        rw [dop_eq_sum]
        exact A.sum_mem fun l hl => A.smul_mem _ (hfold l (hz.1 l hl) _ u.2)⟩
      map_add' := fun u v => Subtype.ext (dop_add hz.1 (hsm _ u.2) (hsm _ v.2))
      map_smul' := fun c u => Subtype.ext (dop_smul z c u.1) }
  refine ⟨T ⟨ψ, hψ⟩, Submodule.subset_span ⟨T, ?_, rfl⟩, rfl⟩
  rintro _ (⟨γ, hγ, rfl⟩ | ⟨k, hk, rfl⟩)
  · exact LinearMap.ext fun u => Subtype.ext (GlobalTheory.T.central_operator_commutes_line_derivative F E σ n J z hz u.1 (hsm _ u.2) γ hγ)
  · exact LinearMap.ext fun u => Subtype.ext (funext fun g => (hz.2 u.1 (hsm _ u.2) k (hK k hk) g).symm)

end Fun

theorem zfin_of_thetaSub (hσ : ∀ x, σ (σ x) = x) (hcm : IsCMExt F E σ) {n d : ℕ} {X : Spc F E n} {W : Spc F E d}
    (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (om : Rep σ X W) {c : E} (hc : c ≠ 0)
    (hr : Module.rank ℂ (M.Pol ψ τ) ≤ Cardinal.aleph0)
    (hL : ∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ _), StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf M ψ τ om (N i)) → m ≤ L)
    (hP1 : ∀ γ ∈ Lines σ X, ∀ f ∈ M.Pol ψ τ, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ → f₁ ∈ M.Pol ψ τ)
    (hP2 : ∀ k ∈ KInf σ X τ, ∀ f ∈ M.Pol ψ τ, ∀ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (k, 1)) f f₁ → f₁ ∈ M.Pol ψ τ)
    (hP3 : ∀ γ ∈ Lines σ W, ∀ f ∈ M.Pol ψ τ, ∃ f₁ ∈ M.Pol ψ τ,
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ ∧ ∀ f₂ : SInf F (Fin n × Fin d),
        ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₂ → f₂ = f₁)
    (hP4 : ∀ k ∈ KInf σ W τ, ∀ f ∈ M.Pol ψ τ, ∃ f₁ ∈ M.Pol ψ τ,
      Acts (evI F) (om (1, k)) f f₁ ∧ ∀ f₂ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) f f₂ → f₂ = f₁)
    (T : SInf F (Fin n × Fin d) →ₗ[ℂ] (GAd σ (c • W.J.map σ) → ℂ))
    (hsm : ∀ f ∈ M.Pol ψ τ, IsSm σ (c • W.J.map σ) (T f))
    (hX1 : ∀ γ ∈ Lines σ X, ∀ f ∈ M.Pol ψ τ, ∀ f₁ ∈ M.Pol ψ τ,
      ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ → T f₁ = 0)
    (hX2 : ∀ k ∈ KInf σ X τ, ∀ f ∈ M.Pol ψ τ, ∀ f₁ ∈ M.Pol ψ τ, Acts (evI F) (om (k, 1)) f f₁ → T f₁ = T f)
    (hW1 : ∀ γ ∈ Lines σ W, ∀ f ∈ M.Pol ψ τ, ∀ f₁ ∈ M.Pol ψ τ,
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ → ∀ x,
        HasDerivAt (fun t : ℝ => T f (x * toGAd hσ W.J hc (γ (Multiplicative.ofAdd t)))) (T f₁ x) 0)
    (hW2 : ∀ k ∈ KInf σ W τ, ∀ f ∈ M.Pol ψ τ, ∀ f₁ ∈ M.Pol ψ τ, Acts (evI F) (om (1, k)) f f₁ →
      T f₁ = fun x => T f (x * toGAd hσ W.J hc k))
    {f : SInf F (Fin n × Fin d)} (hf : f ∈ M.Pol ψ τ) :
    FiniteDimensional ℂ (Submodule.span ℂ {u | ∃ z, IsCentral σ (c • W.J.map σ) z ∧ u = dop z (T f)}) := by
  refine zfin_of_chains ((M.Pol ψ τ).map T) ?_ ?_ (toGAd hσ W.J hc '' KInf σ W τ) ?_ ?_ ?_ ?_ ⟨f, hf, rfl⟩
  · rintro _ ⟨f, hf, rfl⟩
    exact hsm f hf
  · rintro γ hγ _ ⟨f, hf, rfl⟩
    obtain ⟨γL, hγL, e⟩ := GlobalTheory.T.real_line_corresponds_to_line F E σ hσ hcm W c hc γ hγ
    obtain ⟨f₁, hf₁, h1, -⟩ := hP3 γL hγL f hf
    refine ⟨f₁, hf₁, funext fun x => ?_⟩
    have := (hW1 γL hγL f hf f₁ hf₁ h1 x).deriv
    simp only [← e, MulEquiv.apply_symm_apply] at this
    exact this.symm
  · rintro _ ⟨k, hk, rfl⟩
    exact toGAd_mem_infPts hσ W hc hk.1
  · rintro _ ⟨k, hk, rfl⟩ _ ⟨f, hf, rfl⟩
    obtain ⟨f₁, hf₁, h1, -⟩ := hP4 k hk f hf
    exact ⟨f₁, hf₁, hW2 k hk f hf f₁ hf₁ h1⟩
  · exact (rank_map_le T _).trans hr
  · obtain ⟨L, hL⟩ := hL
    refine ⟨L, fun m N hN hS => hL m (fun i => M.Pol ψ τ ⊓ (N i).comap T) (fun i j hij => ?_) fun i => ⟨inf_le_left, ?_, ?_, ?_, ?_⟩⟩
    · refine lt_of_le_of_ne (inf_le_inf_left _ (Submodule.comap_mono (hN hij).le)) fun e => (hN hij).not_ge fun u hu => ?_
      obtain ⟨g, hg, rfl⟩ := (hS j).1 hu
      have : g ∈ M.Pol ψ τ ⊓ (N i).comap T := (show M.Pol ψ τ ⊓ (N i).comap T = _ from e) ▸ ⟨hg, hu⟩
      exact this.2
    · intro γ hγ g hg g₁ h
      have h₁ := hP1 γ hγ g hg g₁ h
      exact ⟨h₁, show T g₁ ∈ N i by rw [hX1 γ hγ g hg g₁ h₁ h]; exact zero_mem _⟩
    · intro k hk g hg g₁ h
      have h₁ := hP2 k hk g hg g₁ h
      exact ⟨sub_mem h₁ hg, show T (g₁ - g) ∈ N i by rw [map_sub, hX2 k hk g hg g₁ h₁ h, sub_self]; exact zero_mem _⟩
    · intro γ hγ g hg g₁ h
      obtain ⟨g₂, hg₂, -, hu⟩ := hP3 γ hγ g hg.1
      obtain rfl := hu g₁ h
      refine ⟨hg₂, show T g₁ ∈ N i from ?_⟩
      obtain ⟨k, δ, hδ, e⟩ := GlobalTheory.T.real_line_factor_as_product_lines F E σ hσ hcm W c hc γ hγ
      have e2 : T g₁ = ∑ j, lineDer (δ j) (T g) := funext fun x => by
        have h1 := hW1 γ hγ g hg.1 g₁ hg₂ h x
        simp only [e] at h1
        rw [Finset.sum_apply]
        exact h1.unique (GlobalTheory.T.has_deriv_at_product_of_real_lines F E σ hcm d _ k δ hδ (T g) (hsm g hg.1) x)
      rw [e2]
      exact (N i).sum_mem fun j _ => (hS i).2.1 _ (hδ j) _ hg.2
    · intro k hk g hg g₁ h
      obtain ⟨g₂, hg₂, -, hu⟩ := hP4 k hk g hg.1
      obtain rfl := hu g₁ h
      refine ⟨hg₂, show T g₁ ∈ N i from ?_⟩
      rw [hW2 k hk g hg.1 g₁ hg₂ h]
      exact (hS i).2.2 _ ⟨k, hk, rfl⟩ _ hg.2

end GlobalTheory.ThK.FiniteLevelDerivatives

end
