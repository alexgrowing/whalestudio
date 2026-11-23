import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EqCHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EquivFramesSameSecondLatticeFiberProofStatement
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset

noncomputable section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals

namespace GlobalTheory.TypeAsm.FibCard
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Main
variable {D : D7} {X : HidaSetting D}

theorem stab_of_fix' (u : D.what₂.Word) {a : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hi : a ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hfix : ∀ c, a ((F0 X u).e c) = (F0 X u).e c) : a ∈ stabF D (X.Fu u) := by
  refine ⟨hi, fun j => ?_, ?_⟩
  · unfold FlagG.Xa
    rw [Submodule.map_span, Set.image_image]
    congr 1
    apply Set.image_congr
    intro i _
    have h' : (F0 X u).e i.castSucc = (X.Fu u).e i := fv_cast (lf D (X.Fu u)).fl i
    have := hfix i.castSucc
    rw [h'] at this
    exact this
  · have h' : (F0 X u).e (Fin.last _) = (X.Fu u).z := fv_last (lf D (X.Fu u)).fl
    have := hfix (Fin.last _)
    rw [h'] at this
    exact this

theorem fix_X (u : D.what₂.Word) {a : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hfix : ∀ c, a ((F0 X u).e c) = (F0 X u).e c) : ∀ x ∈ (X.Fu u).X, a x = x := by
  intro x hx
  have h : Set.EqOn (⇑(a : (VS D).V →ₗ[D.host.E] (VS D).V)) (⇑(LinearMap.id : (VS D).V →ₗ[D.host.E] (VS D).V))
      (Set.range (X.Fu u).e) := by
    rintro _ ⟨i, rfl⟩
    have h' : (F0 X u).e i.castSucc = (X.Fu u).e i := fv_cast (lf D (X.Fu u)).fl i
    have := hfix i.castSucc
    rw [h'] at this
    exact this
  simpa using LinearMap.eqOn_span h hx

theorem perp_pres (u : D.what₂.Word) {a : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hi : a ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hfix : ∀ c, a ((F0 X u).e c) = (F0 X u).e c) :
    ∀ y ∈ perpS (VS D) (X.Fu u).X, a y ∈ perpS (VS D) (X.Fu u).X := by
  intro y hy x hx
  rw [← fix_X u hfix x hx, hi x y]
  exact hy x hx

theorem ind_exists (u : D.what₂.Word) {a : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hi : a ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hfix : ∀ c, a ((F0 X u).e c) = (F0 X u).e c) :
    ∃ φ : WbQ D (X.Fu u) → WbQ D (X.Fu u), ∀ (x : perpS (VS D) (X.Fu u).X) (hx : a x.1 ∈ perpS (VS D) (X.Fu u).X),
      φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk ⟨a x.1, hx⟩ := by
  let f : perpS (VS D) (X.Fu u).X →ₗ[D.host.E] perpS (VS D) (X.Fu u).X :=
    (a : (VS D).V →ₗ[D.host.E] (VS D).V).restrict (perp_pres u hi hfix)
  let q := (X.Fu u).X.comap (perpS (VS D) (X.Fu u).X).subtype
  have hq : q ≤ q.comap f := by
    intro x hx
    simp only [q, Submodule.mem_comap, Submodule.subtype_apply] at hx ⊢
    show a x.1 ∈ (X.Fu u).X
    rw [fix_X u hfix x.1 hx]; exact hx
  refine ⟨Submodule.mapQ q q f hq, fun x hx => ?_⟩
  rw [Submodule.mapQ_apply]
  rfl

end Main
end GlobalTheory.TypeAsm.FibCard

namespace GlobalTheory.TypeAsm.FibCard
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Main2
variable {D : D7} {X : HidaSetting D}

theorem symm_fix (u : D.what₂.Word) {a : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hfix : ∀ c, a ((F0 X u).e c) = (F0 X u).e c) : ∀ x ∈ (X.Fu u).X, a.symm x = x :=
  fun x hx => a.symm_apply_eq.2 (fix_X u hfix x hx).symm

theorem aut_iff {Λ : Submodule (𝓞 D.host.E) (VS D).V} {a : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hga : Formalism.HermitianLatticesTheory.gmap a Λ = Λ) (y : (VS D).V) : a.symm y ∈ Λ ↔ y ∈ Λ := by
  rw [← GlobalTheory.LoopC.FrEqv.mem_gmap (Λ := Λ) a y, hga]

theorem nlam_of_same (u : D.what₂.Word) {Λ : Submodule (𝓞 D.host.E) (VS D).V} {a b : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hia : a ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hib : b ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hga : Formalism.HermitianLatticesTheory.gmap a Λ = Λ) (hgb : Formalism.HermitianLatticesTheory.gmap b Λ = Λ)
    (hfa : ∀ c, a ((F0 X u).e c) = (F0 X u).e c) (hfb : ∀ c, b ((F0 X u).e c) = (F0 X u).e c)
    (hsame : ∀ x ∈ perpS (VS D) (X.Fu u).X, b x - a x ∈ (X.Fu u).X) :
    a⁻¹ * b ∈ NLam Λ (lf D (X.Fu u)) := by
  have happ : ∀ x, (a⁻¹ * b) x = a.symm (b x) := fun x => rfl
  refine ⟨⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem ((Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem hia) hib, ?_⟩,
    fun j x hx => ?_, fun x hx => ?_⟩
  · ext y
    rw [GlobalTheory.LoopC.FrEqv.mem_gmap]
    have : (a⁻¹ * b).symm y = b.symm (a y) := by
      apply (a⁻¹ * b).injective
      rw [LinearEquiv.apply_symm_apply, happ, LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
    rw [this, aut_iff hgb]
    have h2 := aut_iff hga (a y)
    rw [LinearEquiv.symm_apply_apply] at h2
    exact h2.symm
  · have hX : x ∈ (X.Fu u).X := by
      have hle : Xflag (lf D (X.Fu u)) (j + 1) ≤ (X.Fu u).X :=
        Submodule.span_mono (by rintro _ ⟨i, -, rfl⟩; exact ⟨i, rfl⟩)
      exact hle hx
    rw [happ, fix_X u hfb x hX, symm_fix u hfa x hX, sub_self]
    exact zero_mem _
  · have hp : x ∈ perpS (VS D) (X.Fu u).X := by
      simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx
      exact fun y hy => hx y hy
    have e : (a⁻¹ * b) x - x = a.symm (b x - a x) := by
      rw [happ, map_sub, LinearEquiv.symm_apply_apply]
    rw [e, symm_fix u hfa _ (hsame x hp)]
    exact hsame x hp

end Main2
end GlobalTheory.TypeAsm.FibCard

namespace GlobalTheory.TypeAsm.FibCard
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem fibCardC : FibCardC := by
  intro D large₂ X Y u hStd t₀ s hs
  show (s.card : ℝ) * ((Nat.card (autLz D (X.Fu u) t₀.lam') : ℝ))⁻¹ ≤ 1
  by_cases hfin : Finite (autLz D (X.Fu u) t₀.lam')
  swap
  · have : Infinite (autLz D (X.Fu u) t₀.lam') := not_finite_iff_infinite.1 hfin
    rw [Nat.card_eq_zero_of_infinite]; simp
  have H : ∀ t : s, ∃ a : (VS D).V ≃ₗ[D.host.E] (VS D).V, a ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧
      Formalism.HermitianLatticesTheory.gmap a t₀.lam' = t₀.lam' ∧ (∀ c, a ((F0 X u).e c) = (F0 X u).e c) ∧ t₀.lam' = t.1.lam' ∧
      ∃ n ∈ NLam t₀.lam (lf D (X.Fu u)), ∃ n' ∈ NLam t₀.lam' (lf D (X.Fu u)), t.1.lin = n * t₀.lin * a * n' := by
    intro t
    obtain ⟨hl, n, a, hn, ha, hga, hfa, n', hn', he⟩ :=
      GlobalTheory.T.equivFramesSameSecondLatticeFiber_proof D large₂ X Y u hStd t₀ t.1 (hs t.1 t.2).1 (hs t.1 t.2).2
    exact ⟨a, ha, hga, hfa, hl, n, hn, n', hn', he⟩
  choose A hA using H
  have Hφ : ∀ t : s, ∃ φ : WbQ D (X.Fu u) → WbQ D (X.Fu u), ∀ (x : perpS (VS D) (X.Fu u).X)
      (hx : A t x.1 ∈ perpS (VS D) (X.Fu u).X), φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk ⟨A t x.1, hx⟩ :=
    fun t => ind_exists u (hA t).1 (hA t).2.2.1
  choose Φ hΦ using Hφ
  have hmem : ∀ t, Φ t ∈ autLz D (X.Fu u) t₀.lam' :=
    fun t => ⟨A t, stab_of_fix' u (hA t).1 (hA t).2.2.1, (hA t).2.1, hΦ t⟩
  let f : s → autLz D (X.Fu u) t₀.lam' := fun t => ⟨Φ t, hmem t⟩
  have hinj : Function.Injective f := by
    intro t₁ t₂ h12
    have hΦe : Φ t₁ = Φ t₂ := congrArg Subtype.val h12
    obtain ⟨hi1, hg1, hf1, hl1, n₁, hn₁, n₁', hn₁', he1⟩ := hA t₁
    obtain ⟨hi2, hg2, hf2, hl2, n₂, hn₂, n₂', hn₂', he2⟩ := hA t₂
    have hsame : ∀ x ∈ perpS (VS D) (X.Fu u).X, A t₂ x - A t₁ x ∈ (X.Fu u).X := by
      intro x hx
      have p1 := perp_pres u hi1 hf1 x hx
      have p2 := perp_pres u hi2 hf2 x hx
      have k1 := hΦ t₁ ⟨x, hx⟩ p1
      have k2 := hΦ t₂ ⟨x, hx⟩ p2
      rw [hΦe, k2] at k1
      have := (Submodule.Quotient.eq _).1 k1
      rw [Submodule.mem_comap] at this
      simpa using this
    have hm := nlam_of_same u hi1 hi2 hg1 hg2 hf1 hf2 hsame
    apply Subtype.ext
    apply GlobalTheory.TypeAsm.eqC_holds D X Y u t₁.1 t₂.1
    · rw [← (hs t₁.1 t₁.2).1, ← (hs t₂.1 t₂.2).1]
    · rw [← hl1, ← hl2]
    · refine ⟨n₂ * n₁⁻¹, ?_, n₁'⁻¹ * ((A t₁)⁻¹ * A t₂) * n₂', ?_, ?_⟩
      · rw [← (hs t₁.1 t₁.2).1]; exact Formalism.L2.SG.Pf.nlam_mul hn₂ (Formalism.L2.SG.Pf.nlam_inv hn₁)
      · rw [← hl1]; exact Formalism.L2.SG.Pf.nlam_mul (Formalism.L2.SG.Pf.nlam_mul (Formalism.L2.SG.Pf.nlam_inv hn₁') hm) hn₂'
      · rw [he1, he2]; group
  have hcard : Nat.card s ≤ Nat.card (autLz D (X.Fu u) t₀.lam') := Nat.card_le_card_of_injective f hinj
  have hs' : Nat.card s = s.card := by simp
  rw [hs'] at hcard
  rcases Nat.eq_zero_or_pos (Nat.card (autLz D (X.Fu u) t₀.lam')) with h0 | hpos
  · rw [h0]; simp
  · have hp : (0 : ℝ) < Nat.card (autLz D (X.Fu u) t₀.lam') := by exact_mod_cast hpos
    rw [← div_eq_mul_inv, div_le_one hp]; exact_mod_cast hcard

end GlobalTheory.TypeAsm.FibCard
