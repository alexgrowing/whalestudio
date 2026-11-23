import Formalism.WachLatticeTwists.HerrComplexInjectivity.LiftCaseAHerrSources
import Formalism.WachLatticeTwists.HerrComplexInjectivity.HerrComplexProofs.InvariantsShortExact
import Formalism.WachLatticeTwists.HerrComplexInjectivity.HerrComplexProofs.GammaSubOneInvariantsHolds

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JN

open Formalism.CoboundaryTransfers Formalism.RepresentationBoundsCohomology.N1 Formalism.RepresentationBoundsCohomology.N2

theorem card_unit (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) (hn : n = ℓ - 1) : IsUnit ((n : ℕ) : ℤ_[ℓ]) := by
  have h2 : 2 ≤ ℓ := (Fact.out : ℓ.Prime).two_le
  rw [hn, Nat.cast_sub (by omega), Nat.cast_one]
  have h0 : IsUnit (1 - (ℓ : ℤ_[ℓ])) :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ PadicInt.prime_p.not_isUnit
  have : (ℓ : ℤ_[ℓ]) - 1 = -(1 - (ℓ : ℤ_[ℓ])) := by ring
  rw [this]
  exact h0.neg

theorem card_unit' (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] (n : ℕ)
    (hn : n = ℓ - 1) : IsUnit ((n : ℕ) : A) := by
  have := (card_unit ℓ n hn).map (algebraMap ℤ_[ℓ] A)
  rwa [map_natCast] at this

theorem extension_nonlinear_holds : StatExtNL := by
  intro ℓ _ A A₀ _ _ _ _ S B Δ _ _ _ IB ι _ pr D _ _ _ _ W ρ M₀ D' _ _ _ _ V J Hh _ _ cl Hf M h H hs hR
    hD hP2 hP5 hL hM hH hcard hΔ hGQ hcap hJ hE κ hκ
  obtain ⟨Dp, Dt, i1, i2, i3, i4, i5, i6, i7, i8, Wp, Wt, E, ρp, ρt, e, p2p, p2t, p5p, p5t, lp, lt, p6,
    dp, dt, hι, hπ, he, hφe, hγe, hρe, hdict⟩ := hE κ hκ
  obtain ⟨np, κp, _, bp, hbp⟩ := delta_basis_holds ℤ_[ℓ] A S Δ ι pr Dp Wp ρp hR (card_unit' ℓ A _ hcard) dp
  obtain ⟨nt, κt, _, bt, hbt⟩ := delta_basis_holds ℤ_[ℓ] A S Δ ι pr Dt Wt ρt hR (card_unit' ℓ A _ hcard) dt
  obtain ⟨sp, fp, gp, -, -⟩ := dp
  obtain ⟨st, ft, gt, -, -⟩ := dt
  obtain ⟨Dp', k1, k2, k3, k4, jp, φp, γp, x1, x2, x3, x4, x5, x6⟩ :=
    invariants_exist_holds ℤ_[ℓ] A A₀ S B Δ IB ι pr Dp Wp ρp sp fp gp
  obtain ⟨Dt', m1, m2, m3, m4, jt, φt, γt, y1, y2, y3, y4, y5, y6⟩ :=
    invariants_exist_holds ℤ_[ℓ] A A₀ S B Δ IB ι pr Dt Wt ρt st ft gt
  have g9p := gamma_sub_one_invariants_holds ℤ_[ℓ] A A₀ S B Δ IB ι pr Dp Wp ρp κp bp hs p2p sp np hbp gp hcap
  have g9t := gamma_sub_one_invariants_holds ℤ_[ℓ] A A₀ S B Δ IB ι pr Dt Wt ρt κt bt hs p2t st nt hbt gt hcap
  obtain ⟨Vp, Jp, ep, epφ, epγ⟩ := wach_invariants_holds ℤ_[ℓ] A A₀ S B Δ IB ι pr Dp Wp ρp M h M₀ Dp' jp φp γp hs
    hΔ hGQ p5p hM x1 x2 x3 x4 x5 x6 g9p
  obtain ⟨Vt, Jt, et, etφ, etγ⟩ := wach_invariants_holds ℤ_[ℓ] A A₀ S B Δ IB ι pr Dt Wt ρt M h M₀ Dt' jt φt γt hs
    hΔ hGQ p5t hM y1 y2 y3 y4 y5 y6 g9t
  obtain ⟨-, -, -, hsat, -⟩ := wach_top_statement ℤ_[ℓ] A S ι pr D Dp Dt W Wp Wt E M h M₀ H H hR hD hP2 p2p p2t hP5
    p5p p5t hL lp lt p6 hM (fun i => by have := hH i; omega) hH
  have cp : Jp.Compat := ⟨by rw [ep, epφ]; exact x4, by rw [ep, epγ]; exact x5⟩
  have ct : Jt.Compat := ⟨by rw [et, etφ]; exact y4, by rw [et, etγ]; exact y5⟩
  obtain ⟨Sq, hSι, hSπ⟩ := invariants_short_exact ℤ_[ℓ] A A₀ S B Δ IB ι pr D Dp Dt W Wp Wt E ρ ρp ρt M₀ D' Dp' Dt'
    V Vp Vt J Jp Jt hJ cp ct hι hπ hsat
  obtain ⟨e', he'⟩ := (Jt.j_range e).1 hρe
  refine ⟨{ Dp := Dp', Dt := Dt', Wp := Vp, Wt := Vt, S := Sq, e := e', e_mem := ?_, φe := ?_,
            γe := ?_ }, Dp, Dt, i1, i2, i3, i4, i5, i6, i7, i8, Wp, Wt, E, ρp, ρt, Jp, Jt, p2p, p2t, p5p,
    p5t, lp, lt, p6, cp, ct, ⟨np, hπ, st⟩, hSπ, ?_⟩
  · exact (Jt.j_N e').2 fun i => by rw [he']; exact he i
  · exact Jt.j_inj (funext fun i => by rw [ct.1, he', hφe])
  · exact Jt.j_inj (funext fun i => by rw [ct.2, he', hγe])
  · intro c x p h1 h2 h3
    refine hdict c (Jp.j x) p ((Jp.j_range _).2 ⟨x, rfl⟩) (fun i => ?_) (fun i => ?_) (fun i => ?_)
    · have h1' : Sq.π.f x = c • e' := h1
      rw [← hSπ, h1', map_smul, he']
      rfl
    · have h2' : Sq.ι.f (p : D' × D').1 = Vp.φ x - x := h2
      rw [← hSι, h2', map_sub, Pi.sub_apply, cp.1]
    · have h3' : Sq.ι.f (p : D' × D').2 = Vp.γ x - x := h3
      rw [← hSι, h3', map_sub, Pi.sub_apply, cp.2]

theorem lift_case_a_odd_prime : LiftCaseAOddPrime := by
  intro ℓ _ hℓ2 A A₀ _ _ _ _ S B Δ _ _ _ IB ι _ pr D₀ D₁ D₂ _ _ _ _ _ _ _ _ _ _ _ _ W₀ W₁ W₂ E M h M₀ H
    ρ₀ ρ₁ ρ₂ D₀' D₁' D₂' _ _ _ _ _ _ _ _ _ _ _ _ j₀ j₁ j₂ φ₀ γ₀ φ₁ γ₁ φ₂ γ₂ u jumps hℓ hs hc hu hR hD
    a0 a1 a2 b0 b1 b2 c0 c1 c2 hP6 hM hH hp hcard hΔ hmodπ hcap hreg hQL hdiv hjac i0 i1 i2 d0 d1 d2
    hι hπ hnt
  have hGQ := gamma_quotient_case_a ℤ_[ℓ] A₀ B hQL hdiv hjac
  obtain ⟨n0, κ0, _, β0, hβ0⟩ := delta_basis_holds ℤ_[ℓ] A S Δ ι pr D₀ W₀ ρ₀ hR (card_unit' ℓ A _ hcard) d0
  obtain ⟨n1, κ1, _, β1, hβ1⟩ := delta_basis_holds ℤ_[ℓ] A S Δ ι pr D₁ W₁ ρ₁ hR (card_unit' ℓ A _ hcard) d1
  obtain ⟨n2, κ2, _, β2, hβ2⟩ := delta_basis_holds ℤ_[ℓ] A S Δ ι pr D₂ W₂ ρ₂ hR (card_unit' ℓ A _ hcard) d2
  obtain ⟨s0, -, q0, -, -⟩ := d0
  obtain ⟨s1, -, q1, -, -⟩ := d1
  obtain ⟨s2, -, q2, -, -⟩ := d2
  have g0 := gamma_sub_one_invariants_holds ℤ_[ℓ] A A₀ S B Δ IB ι pr D₀ W₀ ρ₀ κ0 β0 hs a0 s0 n0 hβ0 q0 hcap
  have g1 := gamma_sub_one_invariants_holds ℤ_[ℓ] A A₀ S B Δ IB ι pr D₁ W₁ ρ₁ κ1 β1 hs a1 s1 n1 hβ1 q1 hcap
  have g2 := gamma_sub_one_invariants_holds ℤ_[ℓ] A A₀ S B Δ IB ι pr D₂ W₂ ρ₂ κ2 β2 hs a2 s2 n2 hβ2 q2 hcap
  obtain ⟨x1, x2, x3, x4, x5, x6⟩ := i0
  obtain ⟨y1, y2, y3, y4, y5, y6⟩ := i1
  obtain ⟨z1, z2, z3, z4, z5, z6⟩ := i2
  obtain ⟨V₀, J₀, e0, e0φ, e0γ⟩ := wach_invariants_holds ℤ_[ℓ] A A₀ S B Δ IB ι pr D₀ W₀ ρ₀ M h M₀ D₀' j₀ φ₀ γ₀ hs
    hΔ hGQ b0 hM x1 x2 x3 x4 x5 x6 g0
  obtain ⟨V₁, J₁, e1, e1φ, e1γ⟩ := wach_invariants_holds ℤ_[ℓ] A A₀ S B Δ IB ι pr D₁ W₁ ρ₁ M h M₀ D₁' j₁ φ₁ γ₁ hs
    hΔ hGQ b1 hM y1 y2 y3 y4 y5 y6 g1
  obtain ⟨V₂, J₂, e2, e2φ, e2γ⟩ := wach_invariants_holds ℤ_[ℓ] A A₀ S B Δ IB ι pr D₂ W₂ ρ₂ M h M₀ D₂' j₂ φ₂ γ₂ hs
    hΔ hGQ b2 hM z1 z2 z3 z4 z5 z6 g2
  obtain ⟨-, -, -, hsat, -⟩ := wach_top_statement ℤ_[ℓ] A S ι pr D₀ D₁ D₂ W₀ W₁ W₂ E M h M₀ H H hR hD a0 a1 a2 b0 b1
    b2 c0 c1 c2 hP6 hM (fun i => by have := hH i; omega) hH
  have k0 : J₀.Compat := ⟨by rw [e0, e0φ]; exact x4, by rw [e0, e0γ]; exact x5⟩
  have k1 : J₁.Compat := ⟨by rw [e1, e1φ]; exact y4, by rw [e1, e1γ]; exact y5⟩
  have k2 : J₂.Compat := ⟨by rw [e2, e2φ]; exact z4, by rw [e2, e2γ]; exact z5⟩
  obtain ⟨Sq, hSι, hSπ⟩ := invariants_short_exact ℤ_[ℓ] A A₀ S B Δ IB ι pr D₀ D₁ D₂ W₀ W₁ W₂ E ρ₀ ρ₁ ρ₂ M₀ D₀' D₁'
    D₂' V₀ V₁ V₂ J₀ J₁ J₂ k0 k1 k2 hι hπ hsat
  refine ⟨V₀, V₁, V₂, Sq, J₀, J₁, J₂, ⟨e0, e0φ, e0γ⟩, ⟨e1, e1φ, e1γ⟩, ⟨e2, e2φ, e2γ⟩, hSι, hSπ, ?_⟩
  intro δ R P ρ κ _ _ _ _ _ _ _ L H₁ H₂ _ _ _ _ cl₁ cl₂ Hf₁ Hf₂ g _ hδ hP4 hj hnat hc1 hc2 hinj he1 he2
    hrat
  exact composition_case_a ℓ hℓ2 A A₀ S B Δ IB ι pr D₀ D₁ D₂ W₀ W₁ W₂ E M h M₀ H ρ₀ ρ₁ ρ₂ D₀' D₁' D₂' V₀ V₁ V₂
    Sq J₀ J₁ J₂ u jumps δ R P ρ κ L H₁ H₂ cl₁ cl₂ Hf₁ Hf₂ g hℓ hs hc hu hR hD a0 a1 a2 b0 b1 b2 c0 c1 c2
    hP6 hM hH hp hcard hΔ hmodπ hcap hreg hQL hdiv hjac k0 k1 k2 ⟨n1, hπ, s2⟩ hSπ hδ hnt hP4 hj hnat hc1
    hc2 hinj
    (extension_nonlinear_holds ℓ A A₀ S B Δ IB ι pr D₁ W₁ ρ₁ M₀ D₁' V₁ J₁ H₁ cl₁ Hf₁ M h H hs hR hD a1 b1 c1 hM hH
      hcard hΔ hGQ hcap k1 he1)
    (extension_nonlinear_holds ℓ A A₀ S B Δ IB ι pr D₂ W₂ ρ₂ M₀ D₂' V₂ J₂ H₂ cl₂ Hf₂ M h H hs hR hD a2 b2 c2 hM hH
      hcard hΔ hGQ hcap k2 he2) hrat

end Formalism.RepresentationBoundsCohomology.JN
