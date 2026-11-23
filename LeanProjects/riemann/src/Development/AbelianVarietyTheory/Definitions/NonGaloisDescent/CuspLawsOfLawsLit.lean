import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CuspLaws
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.HasPairGammaZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSteinberg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivContraOfChar
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands.CuspModel

section Dual

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem dualCl_ofChar (χ ψ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (hψ : IsSmoothChar ψ) (e : ψ = χ⁻¹) :
    DualCl (IrrGL.ofChar χ hχ) (IrrGL.ofChar ψ hψ) := by
  subst e
  exact ⟨1, IrrRep.det (Fin 1) χ hχ, IrrRep.det (Fin 1) χ⁻¹ hψ, rfl, rfl,
    ProjLine.nonempty_equiv_contra_ofChar (χ := detChar (Fin 1) χ) hχ.detChar⟩

theorem dualCl_fst {x y : IrrGL k} (H : DualCl x y) : y.1 = x.1 := by
  obtain ⟨n, π, π', rfl, rfl, -⟩ := H
  rfl

theorem dualCl_unique {x y y' : IrrGL k} (H : DualCl x y) (H' : DualCl x y') : y = y' := by
  obtain ⟨n, π, σ, rfl, rfl, ⟨e⟩⟩ := H
  obtain ⟨n', π', σ', h1, rfl, ⟨e'⟩⟩ := H'
  obtain rfl : n = n' := congrArg Sigma.fst h1
  obtain ⟨f⟩ := IrrRep.cl_eq_iff.1 (sigma_mk_injective (β := fun n => IrrCl (GL (Fin n) k)) h1)
  exact congrArg (Sigma.mk n) (IrrRep.cl_eq_iff.2 ⟨(e.trans (ContraRefl.contraEquiv f.symm)).trans e'.symm⟩)

theorem segDual_unique {Δ Γ Γ' : Segment k} (H : SegDual Δ Γ) (H' : SegDual Δ Γ') : Γ = Γ' :=
  Segment.ext_first (dualCl_unique H.2 H'.2) (H.1.trans H'.1.symm)

theorem segDual_ofChar (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (hχ' : IsSmoothChar χ⁻¹) (l : ℕ) (hl : 0 < l) :
    SegDual (Segment.ofChar χ hχ l hl) ((Segment.ofChar χ⁻¹ hχ' l hl).nu (1 - (l : ℂ))) := by
  refine ⟨rfl, ?_⟩
  change DualCl ((IrrGL.ofChar χ hχ).nu ((l : ℂ) - 1)) ((IrrGL.ofChar χ⁻¹ hχ').nu (1 - (l : ℂ)))
  rw [IrrGL.nu, IrrGL.nu, IrrGL.tw_ofChar, IrrGL.tw_ofChar]
  refine dualCl_ofChar _ _ _ _ ?_
  rw [mul_inv, ← absPow_neg, neg_sub]

theorem not_segDual_self :
    ¬ SegDual (Segment.ofChar (1 : kˣ →* ℂˣ) isSmoothChar_one 2 two_pos) (.ofChar 1 isSmoothChar_one 2 two_pos) := by
  intro H
  have h0 : IsSmoothChar (1 : kˣ →* ℂˣ)⁻¹ := by rw [inv_one]; exact isSmoothChar_one
  have h1 := congrArg Segment.first (segDual_unique H (segDual_ofChar 1 isSmoothChar_one h0 2 two_pos))
  change IrrGL.ofChar 1 isSmoothChar_one = (IrrGL.ofChar 1⁻¹ h0).nu (1 - ((2 : ℕ) : ℂ)) at h1
  simp only [inv_one] at h1
  have h2 : (IrrGL.ofChar (1 : kˣ →* ℂˣ) isSmoothChar_one).nu (0 : ℝ) =
      (IrrGL.ofChar 1 isSmoothChar_one).nu ((-1 : ℝ) : ℂ) := by
    rw [Complex.ofReal_zero, IrrGL.nu_zero, show ((-1 : ℝ) : ℂ) = 1 - ((2 : ℕ) : ℂ) by push_cast; ring]
    exact h1
  have := (IrrGL.nu_ofChar_inj _ _).1 h2
  norm_num at this

end Dual

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
  {e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ} {r rc : IrrGL (w.adicCompletion E) → WD h}

theorem isLExt_self (H : LawsMin a ha e rc) : IsLExt rc rc := H.langlands

theorem eq_of_isLExt (H : IsLExt r rc) {x : IrrGL (w.adicCompletion E)} (hx : x.IsCusp) : rc x = r x := by
  have h1 := H [.single x hx] x (single_spec hx).2.2.2
  rw [h1]
  change (((r x).lpTw ((((1 : ℕ) : ℝ) - 1) / 2)).lpChar (WD.lpSp h 1)).lpSum (WD.lpZero h) = r x
  rw [WD.lpSum_zero, Test.lpChar_lpSp_one]
  simp [WD.lpTw_zero]

theorem cuspLaws_of_lawsLit (H : LawsLit a ha e rc)
    (hgap : ∀ ψ : AddChar (w.adicCompletion E) Circle, Continuous ψ → ψ ≠ 1 →
      ∀ x y : IrrGL (w.adicCompletion E), x.IsCusp → y.IsCusp → y.1 + 1 < x.1 →
        HasPairGamma ψ x.rep y.rep (e ψ ((rc x).lpChar (rc y)))) : CuspLaws a ha e rc where
  bij := ⟨fun x hx => (H.cusp x).1 hx, H.bij.1.injOn, fun y hy => by
    obtain ⟨x, rfl⟩ := H.bij.2 y
    exact ⟨x, (H.cusp x).2 hy, rfl⟩⟩
  dim x _ := H.dim x
  twist x _ χ hχ := by rw [H.twist, H.one, lpChar_lpOfChar]
  central x _ := H.central x
  dual x y _ _ := by
    rintro ⟨n, π, π', rfl, rfl, hd⟩
    exact H.dual n π π' hd
  eps ψ hc h1 x y hx hy hlt := by
    rcases (Nat.succ_le_of_lt hlt).eq_or_lt with h2 | h2
    · obtain ⟨n, c⟩ := x
      obtain ⟨m, d⟩ := y
      obtain rfl : m + 1 = n := h2
      obtain ⟨t, ht⟩ := exists_hasConductor_of_continuous ψ hc h1
      have := H.eps ψ hc h1 m c.rep d.rep hx.2
      rw [show cls c.rep = ⟨m + 1, c⟩ from congrArg (Sigma.mk _) c.cl_rep,
        show cls d.rep = ⟨m, d⟩ from congrArg (Sigma.mk _) d.cl_rep] at this
      exact (GammaModel.hasPairGamma_succ_iff ht _ _ _).2 this
    · exact hgap ψ hc h1 x y hx hy h2

theorem one_of_cuspLaws (H : CuspLaws a ha e r) (χ : (w.adicCompletion E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    r (.ofChar χ hχ) = WD.lpOfChar h (χ.comp a) (ha.smooth hχ) := by
  have hc := IrrGL.isCusp_ofChar χ hχ
  have hd := H.dim _ hc
  have hω : HasCentralChar (IrrGL.ofChar χ hχ).rep χ := by
    intro z v
    let φ := equivRep (IrrRep.det (Fin 1) χ hχ)
    obtain ⟨u, rfl⟩ := φ.toLinearEquiv.surjective v
    have h1 := φ.toIntertwiningMap.isIntertwining _ _ (GeneralLinearGroup.scalar (Fin 1) z) u
    have h2 : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 1) z) = z := by
      ext; simp [GeneralLinearGroup.scalar]
    refine h1.symm.trans ?_
    refine Eq.trans ?_ (φ.toLinearEquiv.map_smul _ u)
    refine congrArg φ.toLinearEquiv ?_
    change ((χ (GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 1) z)) : ℂˣ) : ℂ) • u = _
    rw [h2]
  have he := H.central _ hc χ hω
  obtain ⟨n, b, hb⟩ := (r (.ofChar χ hχ)).exists_rep
  rw [← hb] at hd he ⊢
  obtain rfl : n = 1 := by simpa [IrrGL.ofChar] using hd
  have one : ∀ f : Module.End ℂ (Fin 1 → ℂ), ∀ v, f v = f (fun _ => 1) 0 • v := fun f v => by
    have hv : v = v 0 • fun _ => (1 : ℂ) := funext fun i => by simp [Subsingleton.elim i 0]
    funext i
    rw [Subsingleton.elim i 0]
    conv_lhs => rw [hv, map_smul]
    simp [mul_comm]
  refine WD.sound ⟨.refl _ _, fun σ v => ?_, fun v => ?_⟩
  · have h1 := he σ
    rw [WD.eig_mk] at h1
    have h2 : (b.ρ σ).charpoly.roots.prod = LinearMap.det (b.ρ σ) := by
      rw [← LinearMap.charpoly_toMatrix _ (Pi.basisFun ℂ (Fin 1)), ← Matrix.det_eq_prod_roots_charpoly,
        LinearMap.det_toMatrix]
    have h3 : b.ρ σ = b.ρ σ (fun _ => 1) 0 • LinearMap.id := LinearMap.ext (one _)
    have h4 : LinearMap.det (b.ρ σ) = b.ρ σ (fun _ => 1) 0 := by
      conv_lhs => rw [h3]
      simp
    funext i
    have := congrFun (one (b.ρ σ) v) i
    rw [← h4, ← h2, h1] at this
    simpa using this
  · obtain ⟨m, hm⟩ := b.nilpotent
    have h3 : b.N = b.N (fun _ => 1) 0 • 1 := LinearMap.ext (one _)
    have h4 : b.N (fun _ => 1) 0 ^ m = 0 := by
      rw [h3, _root_.smul_pow, one_pow] at hm
      simpa using congrFun (LinearMap.congr_fun hm fun _ => 1) 0
    have h5 : b.N (fun _ => 1) 0 = 0 := eq_zero_of_pow_eq_zero h4
    have h6 := one b.N v
    rw [h5, zero_smul] at h6
    simpa using h6

theorem not_cuspLaws_const (y : WD h) : ¬ CuspLaws a ha e fun _ => y := fun H => by
  have := H.bij.injOn ((IrrGL.isCusp_ofChar 1 isSmoothChar_one).nu (0 : ℝ))
    ((IrrGL.isCusp_ofChar 1 isSmoothChar_one).nu (1 : ℝ)) rfl
  exact zero_ne_one ((IrrGL.nu_ofChar_inj _ _).1 this)

end GlobalTheory.LocLanglands.CuspModel

end
