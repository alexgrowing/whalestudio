import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParaSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolActs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealmapsIsomorphism
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBThetaUnfolding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDatumActionOfPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineDecompositionUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilLineCommutatorActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilCompactLineActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowPartCompactStableStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.IndLine.LowGen

open GlobalTheory.IndLine.PGenReal

open GlobalTheory.ThK.RealUniq in

theorem pGen_of_kStab_adapted (hKP : GlobalTheory.ThK.KP) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {B : Base F E} {a a' d₁ i₀ i₁ : ℕ} {G : Geo σ a a'} {W₁ : Spc F E d₁} {H' : Plane E (a + a') d₁}
    (hH' : H'.IsAdapted σ B G.W W₁ i₀ i₁) {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} {R : RealMaps F a a'}
    {Rf : FinMaps F a a'} (hM : IsMatched B G X om om' R Rf) (V : Submodule ℂ R.Pi) (hV : V ≠ ⊥)
    (hKV : KStab B G.M om R.p V) : PGen B G.M om R.p W₁ H' V := by
  have hR := hM.real
  have hPV := isPair_V hM.triple
  have actV := GlobalTheory.T.polynomial_datum_action_of_pair hKP.base _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hPV
  have ksL : ∀ γ ∈ Lines σ G.W, ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin a × Fin (a + a')),
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ → R.p f = 0 → R.p f₁ = 0 :=
    fun γ hγ f hf f₁ h1 h0 => by
      have := hR.lie γ hγ f hf 0 (zero_mem _) f₁ 0 h1 (actsD_zero _) (by rw [h0, map_zero])
      rwa [map_zero] at this
  have ksK : ∀ k ∈ KInf σ G.W B.emb, ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin a × Fin (a + a')),
      Acts (evI F) (om (1, k)) f f₁ → R.p f = 0 → R.p f₁ = 0 :=
    fun k hk f hf f₁ h1 h0 => by
      have := hR.cpt k hk f hf 0 (zero_mem _) f₁ 0 h1 (acts_zero _) (by rw [h0, map_zero])
      rwa [map_zero] at this
  have onto : ∀ y, ∃ f ∈ G.M.Pol B.ψ B.emb, R.p f = y := fun y => by
    have : y ∈ (G.M.Pol B.ψ B.emb).map R.p := hR.quot.onto ▸ Submodule.mem_top
    exact Submodule.mem_map.1 this
  choose DL hDLm hDLi using actV.2.2.1
  choose DK hDKm hDKi using actV.2.2.2
  let π : G.M.Pol B.ψ B.emb →ₗ[ℂ] R.Pi := R.p ∘ₗ (G.M.Pol B.ψ B.emb).subtype
  have hπ : Function.Surjective π := fun y => by
    obtain ⟨f, hf, e⟩ := onto y
    exact ⟨⟨f, hf⟩, e⟩
  let ρ : {γ // γ ∈ Lines σ G.W} → Module.End ℂ R.Pi := fun γ =>
    induced π hπ ((DL γ.1 γ.2).restrict (hDLm γ.1 γ.2))
      (fun u hu => ksL γ.1 γ.2 u.1 u.2 _ ((hDLi γ.1 γ.2 u.1 u.2 _).2 rfl) hu)
  let τ : {k // k ∈ KInf σ G.W B.emb} → Module.End ℂ R.Pi := fun k =>
    induced π hπ ((DK k.1 k.2).restrict (hDKm k.1 k.2))
      (fun u hu => ksK k.1 k.2 u.1 u.2 _ ((hDKi k.1 k.2 u.1 u.2 _).2 rfl) hu)
  have hρ : ∀ γ, ∀ f (hf : f ∈ G.M.Pol B.ψ B.emb), ρ γ (R.p f) = R.p (DL γ.1 γ.2 f) := fun γ f hf =>
    induced_apply π hπ _ _ ⟨f, hf⟩
  have hτ : ∀ k, ∀ f (hf : f ∈ G.M.Pol B.ψ B.emb), τ k (R.p f) = R.p (DK k.1 k.2 f) := fun k f hf =>
    induced_apply π hπ _ _ ⟨f, hf⟩
  have dL : ∀ γ (hγ : γ ∈ Lines σ G.W), ∀ f ∈ G.M.Pol B.ψ B.emb,
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f (DL γ hγ f) :=
    fun γ hγ f hf => (hDLi γ hγ f hf _).2 rfl
  have dK : ∀ k (hk : k ∈ KInf σ G.W B.emb), ∀ f ∈ G.M.Pol B.ψ B.emb, Acts (evI F) (om (1, k)) f (DK k hk f) :=
    fun k hk f hf => (hDKi k hk f hf _).2 rfl
  let IsP : {γ // γ ∈ Lines σ G.W} → Prop := fun γ => (∀ s, γ.1 s ∈ unip σ G.W H') ∨
    ∃ (t : Multiplicative ℝ →* (AE F E)ˣ) (γ₁ : Multiplicative ℝ →* UA σ W₁.J), γ₁ ∈ Lines σ W₁ ∧
      ∀ s, IsLevi H' (t s) (γ₁ s) (γ.1 s)
  let IsK : {γ // γ ∈ Lines σ G.W} → Prop := fun γ => ∀ s, γ.1 s ∈ KInf σ G.W B.emb
  have dec : ∀ i, ∃ a b c, IsP a ∧ IsP b ∧ IsK c ∧ ρ i = ρ a + ρ b + ρ c := by
    rintro ⟨γ, hγ⟩
    obtain ⟨γu, hu, γl, hl, γk, hk, hu', hl', hk', key⟩ :=
      GlobalTheory.T.line_decomposition_unipotent hKP.base F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hPV _ W₁ H' _ _ hH' γ hγ
    refine ⟨⟨γu, hu⟩, ⟨γl, hl⟩, ⟨γk, hk⟩, Or.inl hu', Or.inr hl', hk', LinearMap.ext fun x => ?_⟩
    obtain ⟨f, hf, rfl⟩ := onto x
    simp only [LinearMap.add_apply, hρ _ f hf]
    rw [key f hf _ _ _ _ (dL _ _ f hf) (dL _ _ f hf) (dL _ _ f hf) (dL _ _ f hf), map_add, map_add]
  have br : ∀ i j, IsK i → ∃ e, ρ i * ρ j - ρ j * ρ i = ρ e := by
    rintro ⟨κ, hκ⟩ ⟨δ, hδ⟩ -
    obtain ⟨ε, hε, key⟩ := GlobalTheory.T.weil_line_commutator_action hKP.base F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hPV κ hκ δ hδ
    refine ⟨⟨ε, hε⟩, LinearMap.ext fun x => ?_⟩
    obtain ⟨f, hf, rfl⟩ := onto x
    have m1 := hDLm κ hκ f hf
    have m2 := hDLm δ hδ f hf
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hρ _ f hf, hρ _ _ m1, hρ _ _ m2]
    rw [← map_sub, key f hf _ _ _ _ _ (dL _ _ f hf) (dL _ _ f hf) (dL _ _ _ m1) (dL _ _ _ m2) (dL _ _ f hf)]
  have ad : ∀ k i, ∃ e, τ k * ρ i = ρ e * τ k := by
    rintro ⟨k, hk⟩ ⟨δ, hδ⟩
    obtain ⟨ε, hε, key⟩ := GlobalTheory.T.weil_compact_line_action hKP.base F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hPV k hk δ hδ
    refine ⟨⟨ε, hε⟩, LinearMap.ext fun x => ?_⟩
    obtain ⟨f, hf, rfl⟩ := onto x
    have m1 := hDKm k hk f hf
    have m2 := hDLm δ hδ f hf
    simp only [Module.End.mul_apply, hρ _ f hf, hτ _ f hf, hρ _ _ m1, hτ _ _ m2]
    have := key f hf (DK k hk f) (DL δ hδ f) (DK k hk (DL δ hδ f)) (dK k hk f hf) (dL δ hδ f hf) (dK k hk _ m2)
    rw [(hDLi ε hε _ m1 _).1 this]
  have hVK : ∀ i, IsK i → ∀ x ∈ V, ρ i x ∈ V := by
    rintro ⟨γ, hγ⟩ hk x hx
    obtain ⟨f, hf, rfl⟩ := onto x
    rw [hρ _ f hf]
    exact hKV.2 γ hγ hk f hf _ (dL _ _ f hf) hx
  have hVk : ∀ k, ∀ x ∈ V, τ k x ∈ V := by
    rintro ⟨k, hk⟩ x hx
    obtain ⟨f, hf, rfl⟩ := onto x
    rw [hτ _ f hf]
    exact hKV.1 k hk f hf _ (dK _ _ f hf) hx
  obtain ⟨N', hVN', hmin, hstL, hstK⟩ := exists_gen (ρ := ρ) (IsP := IsP) (V := V) τ dec br ad hVK hVk
  intro N hVN hU hLv
  have hN : ∀ i, IsP i → ∀ x ∈ N, ρ i x ∈ N := by
    rintro ⟨γ, hγ⟩ hi x hx
    obtain ⟨f, hf, rfl⟩ := onto x
    rw [hρ _ f hf]
    rcases hi with hi | hi
    · exact hU γ hγ hi f hf _ (dL _ _ f hf) hx
    · exact hLv γ hγ hi f hf _ (dL _ _ f hf) hx
  have hle := hmin N hVN hN
  have hirr := hR.irred N' (fun γ hγ f hf f₁ h1 hx => by
      rw [(hDLi γ hγ f hf f₁).1 h1, ← hρ ⟨γ, hγ⟩ f hf]
      exact hstL _ _ hx)
    (fun k hk f hf f₁ h1 hx => by
      rw [(hDKi k hk f hf f₁).1 h1, ← hτ ⟨k, hk⟩ f hf]
      exact hstK _ _ hx)
  rcases hirr with h0 | h0
  · exact absurd (le_bot_iff.1 (h0 ▸ hVN')) hV
  · exact top_le_iff.1 (h0 ▸ hle)

theorem paraSpan_eq_top : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F (b + 2) a') (Rf : FinMaps F (b + 2) a'),
      IsMatched B G X om om' R Rf → paraSpan B G.M om G₁.W H' R.p = ⊤ := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hC X om om' R Rf hM
  have hne : lowPartInf B G.M R.p ≠ ⊥ := by
    haveI := hM.real.nontriv
    obtain ⟨y, hy⟩ := exists_ne (0 : R.Pi)
    have hy' : y ∈ (G.M.Pol B.ψ B.emb).map R.p := hM.real.quot.onto ▸ Submodule.mem_top
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hy'
    exact lowPartInf_ne_bot B G.M R.p ⟨f, hf, hy⟩
  have hgen := pGen_of_kStab_adapted hKP hC.hH' hM _ hne (GlobalTheory.T.low_part_compact_stable hKP F E σ B _ _ G X om om' R Rf hM)
  refine sInf_eq_top.2 fun S hS => hgen S hS.1 (fun γ hγ hu => hS.2 γ hγ (Or.inl hu)) ?_
  rintro γ hγ ⟨t, γ₁, hγ₁, hl⟩
  exact hS.2 γ hγ (Or.inr ⟨γ₁, hγ₁, t, hl⟩)

end GlobalTheory.IndLine.LowGen
