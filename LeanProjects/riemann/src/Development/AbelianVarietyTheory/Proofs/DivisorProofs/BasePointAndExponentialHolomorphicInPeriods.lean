import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDifferentiableOnTransfer
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHolomorphicChart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NotInjOnOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothBaseDimEqPeriodSpaceDimStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformisationExpUniqueFullLevelMarkingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicMapLiftsLocallyToPeriodFamiliesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PerCoordExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationAtTransportIsometryStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory.PELUHol

open GlobalTheory.HolPeriods

theorem isHolTo_point_and_exp : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (Λ : Type) (F : Fam ℂ O Λ g) (N : ℕ) (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop) (d : ℕ) (D' : PLat O bar) (t : Λ → D'.La) (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D'.La →+ (Fin g → ℂ))) (y : (Fin m → ℂ) → (Sp ℂ ⟶ F.X)) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ F.A)), 3 ≤ N → (∀ a, F.eta a ^ N = 1) → SmoothOfRelativeDimension d F.s → QuasiCompact F.s → FineAt F (RingHom.id ℂ) ρ N C → C D' t → FullMark N D' t → IsOpen B → IsHolPeriods D' ρ B P → (∀ b ∈ B, UnifAt F (RingHom.id ℂ) ρ N D' t (P b) (y b) (e b)) → IsHolTo B y ∧ IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) := by
  intro O _ bar g ρ Λ F N C d D' t m B P y e hN heta hsm hqc hfine hC hfull hB hP hU
  have hN0 : 0 < N := by omega
  have hrefl : IsMarkedIsom N D' D' t t (LinearEquiv.refl O D'.La) :=
    ⟨fun _ _ => rfl, fun a => ⟨0, by simp⟩⟩
  have uniq : ∀ {Q Q' : D'.La →+ (Fin g → ℂ)} {x x' : Sp ℂ ⟶ F.X}
      {u : (Fin g → ℂ) → (Over.mk x ⟶ F.A)} {u' : (Fin g → ℂ) → (Over.mk x' ⟶ F.A)},
      UnifAt F (RingHom.id ℂ) ρ N D' t Q x u → UnifAt F (RingHom.id ℂ) ρ N D' t Q' x' u' →
      ∀ k : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), (∀ a, Q' a = k (Q a)) → x = x' := by
    intro Q Q' x x' u u' h h' k hk
    exact hfine.sep D' D' t t Q Q' x x' u u' h h' (LinearEquiv.refl O D'.La) k hrefl fun a => hk a
  have expo : ∀ {Q Q' : D'.La →+ (Fin g → ℂ)} {x x' : Sp ℂ ⟶ F.X}
      {u : (Fin g → ℂ) → (Over.mk x ⟶ F.A)} {u' : (Fin g → ℂ) → (Over.mk x' ⟶ F.A)},
      UnifAt F (RingHom.id ℂ) ρ N D' t Q x u → UnifAt F (RingHom.id ℂ) ρ N D' t Q' x' u' →
      ∀ k : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), (∀ a, Q' a = k (Q a)) →
      ∀ z, (show Sp ℂ ⟶ F.A.left from (u z).left) = (u' (k z)).left := by
    intro Q Q' x x' u u' h h' k hk z
    obtain rfl := uniq h h' k hk
    have h2 := GlobalTheory.T.uniformisationAt_transport_isometry O bar g ρ ℂ (RingHom.id ℂ) Λ F N D' D' t t Q Q' x u (LinearEquiv.refl O D'.La) k
      hN0 h hrefl (fun a => hk a) h'.2.1
    have h3 := congrFun (GlobalTheory.T.complexUniformisation_exp_unique_full_level_marking O bar g ρ ℂ (RingHom.id ℂ) Λ F N D' t Q' x _ _ hN hfull h2 h') (k z)
    simp only [LinearEquiv.symm_apply_apply] at h3
    rw [h3]
  have near : ∀ {n : ℕ} {C' : Set (Fin n → ℂ)} {R : (Fin n → ℂ) → (D'.La →+ (Fin g → ℂ))}
      (P₀ : D'.La →+ (Fin g → ℂ)) (s : Finset D'.La) (ε : ℝ), IsOpen C' → IsHolPeriods D' ρ C' R →
      IsOpen {c | c ∈ C' ∧ ∀ x ∈ s, ‖R c x - P₀ x‖ < ε} := by
    intro n C' R P₀ s ε hC' hR
    refine isOpen_iff_mem_nhds.2 fun c hc => ?_
    refine Filter.Eventually.and (hC'.mem_nhds hc.1) ((Filter.eventually_all_finset s).2 fun x hx => ?_)
    have : ContinuousAt (fun c => ‖R c x - P₀ x‖) c :=
      (((hR.2 x).continuousOn.continuousAt (hC'.mem_nhds hc.1)).sub continuousAt_const).norm
    exact this.eventually_lt continuousAt_const (hc.2 x hx)
  have loc : ∀ b₀ ∈ B, ∃ B' : Set (Fin m → ℂ), b₀ ∈ B' ∧ B' ⊆ B ∧ IsHolTo B' y ∧
      IsHolTo (B' ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) := by
    intro b₀ hb₀
    obtain ⟨d', hd'⟩ := GlobalTheory.T.exists_perCoord O bar g ρ D'
    have hdd : d = d' := GlobalTheory.T.smoothBase_dim_eq_periodSpace_dim O bar g ρ Λ F N C d d' D' t hN0 heta hsm hqc hfine hC ⟨_, hP.1 b₀ hb₀⟩ hd'
    subst hdd
    obtain ⟨C₀, y₁, -, -, -, -, hC₀, h0, hy0, hover, hhol, hinj, -⟩ :=
      GlobalTheory.SubfieldChart.exists_holomorphic_chart ℂ (RingHom.id ℂ) F.X F.s d (y b₀) hsm (hU b₀ hb₀).1
    obtain ⟨e₀, he₀⟩ : ∃ e₀, UnifAt F (RingHom.id ℂ) ρ N D' t (P b₀) (y₁ 0) e₀ := by
      rw [hy0]; exact ⟨_, hU b₀ hb₀⟩
    haveI : Smooth F.s := SmoothOfRelativeDimension.smooth d _
    obtain ⟨C₁, P₁, e₁, hC₁, h01, hsub, hP0, hP₁, he₁, hU₁⟩ :=
      GlobalTheory.T.holomorphicMap_lifts_locally_to_periodFamilies O bar g ρ Λ F N D' t d C₀ y₁ 0 (P b₀) e₀ hN0 heta inferInstance hC₀ h0 hover hhol he₀
    obtain ⟨Bq, Q, Z, s, ε, hBq, hε, hQ, hZ0, hQZ, hZQ, hnear, hinv, hZ⟩ := hd' (P b₀) (hP.1 b₀ hb₀)
    have zinj : ∀ R R' : D'.La →+ (Fin g → ℂ), IsPeriod D' ρ R → IsPeriod D' ρ R' →
        (∀ x ∈ s, ‖R x - P b₀ x‖ < ε) → (∀ x ∈ s, ‖R' x - P b₀ x‖ < ε) → Z R = Z R' →
        ∃ k : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ a, R' a = k (R a) := by
      intro R R' hR hR' hn hn' hZZ
      obtain ⟨-, h, hh⟩ := hnear R hR hn
      obtain ⟨-, h', hh'⟩ := hnear R' hR' hn'
      refine ⟨h.symm.trans h', fun a => ?_⟩
      rw [hh' a, hh a, hZZ]
      simp
    set C₂ := {c | c ∈ C₁ ∧ ∀ x ∈ s, ‖P₁ c x - P b₀ x‖ < ε} with hC₂def
    have hC₂ : IsOpen C₂ := near (P b₀) s ε hC₁ hP₁
    have h02 : (0 : Fin d → ℂ) ∈ C₂ := ⟨h01, fun x _ => by simpa [hP0] using hε⟩
    have hF : DifferentiableOn ℂ (fun c => Z (P₁ c)) C₂ :=
      hZ _ C₂ P₁ hC₂ ⟨fun c hc => hP₁.1 c hc.1, fun x => (hP₁.2 x).mono fun c hc => hc.1⟩ fun c hc => hc.2
    have hFinj : Set.InjOn (fun c => Z (P₁ c)) C₂ := by
      intro c hc c' hc' hcc
      obtain ⟨k, hk⟩ := zinj _ _ (hP₁.1 c hc.1) (hP₁.1 c' hc'.1) hc.2 hc'.2 hcc
      exact hinj (hsub hc.1) (hsub hc'.1) (uniq (hU₁ c hc.1) (hU₁ c' hc'.1) k hk)
    obtain ⟨W, G, hW, hW0, hG, hGW⟩ :=
      exists_local_section hC₂ hF h02 (GlobalTheory.InjHol.bijective_fderiv_of_injOn _ C₂ _ hC₂ hF hFinj 0 h02)
    set B₁ := {b | b ∈ B ∧ ∀ x ∈ s, ‖P b x - P b₀ x‖ < ε} with hB₁def
    have hB₁ : IsOpen B₁ := near (P b₀) s ε hB hP
    have hZP : DifferentiableOn ℂ (fun b => Z (P b)) B₁ :=
      hZ _ B₁ P hB₁ ⟨fun c hc => hP.1 c hc.1, fun x => (hP.2 x).mono fun c hc => hc.1⟩ fun c hc => hc.2
    set B₂ := B₁ ∩ (fun b => Z (P b)) ⁻¹' W with hB₂def
    have hB₂ : IsOpen B₂ := hZP.continuousOn.isOpen_inter_preimage hB₁ hW
    have hb₂ : b₀ ∈ B₂ := ⟨⟨hb₀, fun x _ => by simpa using hε⟩, by simpa [hP0] using hW0⟩
    have hβ : DifferentiableOn ℂ (fun b => G (Z (P b))) B₂ :=
      hG.comp (hZP.mono Set.inter_subset_left) fun b hb => hb.2
    have hβC : ∀ b ∈ B₂, G (Z (P b)) ∈ C₂ := fun b hb => (hGW _ hb.2).1
    have hk : ∀ b, ∃ k : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), b ∈ B₂ → ∀ a, P₁ (G (Z (P b))) a = k (P b a) := by
      intro b
      by_cases hb : b ∈ B₂
      · obtain ⟨k, hk⟩ := zinj _ _ (hP.1 b hb.1.1) (hP₁.1 _ (hβC b hb).1) hb.1.2 (hβC b hb).2
          (hGW _ hb.2).2.symm
        exact ⟨k, fun _ => hk⟩
      · exact ⟨LinearEquiv.refl _ _, fun h => absurd h hb⟩
    choose k hk using hk
    obtain ⟨B₃, hB₃, hb₃, hsub₃, hkd⟩ := exists_differentiableOn_transfer (Q := P)
      (Q' := fun b => P₁ (G (Z (P b)))) hB₂ (fun x => (hP.2 x).mono fun b hb => hb.1.1)
      (fun x => (hP₁.2 x).comp hβ fun b hb => (hβC b hb).1) hb₂ (hP.1 b₀ hb₀).2.2.2.1
      (fun b => (k b).toLinearMap) fun b hb x => hk b hb x
    refine ⟨B₃, hb₃, fun b hb => (hsub₃ hb).1.1, ?_, ?_⟩
    · refine isHolTo_congr (isHolTo_comp hhol hB₃ (hβ.mono hsub₃)
        fun b hb => hsub (hβC b (hsub₃ hb)).1) fun b hb => ?_
      exact uniq (hU b (hsub₃ hb).1.1) (hU₁ _ (hβC b (hsub₃ hb)).1) (k b) (hk b (hsub₃ hb))
    · have hφ : DifferentiableOn ℂ (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (G (Z (P bz.1)), k bz.1 bz.2))
          (B₃ ×ˢ Set.univ) :=
        (hβ.comp differentiableOn_fst fun bz hbz => hsub₃ hbz.1).prodMk hkd
      refine isHolTo_congr (isHolTo_comp he₁ (hB₃.prod isOpen_univ) hφ
        fun bz hbz => ⟨(hβC _ (hsub₃ hbz.1)).1, trivial⟩) fun bz hbz => ?_
      exact expo (hU _ (hsub₃ hbz.1).1.1) (hU₁ _ (hβC _ (hsub₃ hbz.1)).1) (k bz.1)
        (hk _ (hsub₃ hbz.1)) bz.2
  refine ⟨isHolTo_of_local fun b hb => ?_, isHolTo_of_local fun bz hbz => ?_⟩
  · obtain ⟨B', h1, h2, h3, -⟩ := loc b hb
    exact ⟨B', h1, h2, h3⟩
  · obtain ⟨B', h1, h2, -, h4⟩ := loc bz.1 hbz.1
    exact ⟨B' ×ˢ Set.univ, ⟨h1, trivial⟩, Set.prod_mono h2 le_rfl, h4⟩

end GlobalTheory.PELUHol
