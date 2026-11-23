import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

abbrev cls {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    (π : IrrRep (GL (Fin n) k)) : IrrGL k := ⟨n, π.cl⟩

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def sumList (l : List (WD h)) : WD h := l.foldr WD.lpSum (WD.lpZero h)

def IsIrrWD (x : WD h) : Prop := ∃ (n : ℕ) (a : WDRep h (Fin n → ℂ)), WD.mk a = x ∧ a.ρ.IsIrreducible

def IsTameWD (x : WD h) : Prop :=
  ∃ (n : ℕ) (a : WDRep h (Fin n → ℂ)), WD.mk a = x ∧
    ∀ σ : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) → a.ρ σ = 1

structure Laws (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (ε : EpsFamily A)
    (rc : IrrGL (w.adicCompletion E) → WD h) : Prop where

  bij : Function.Bijective rc

  dim : ∀ x, (rc x).lpDim = x.1

  one : ∀ χ hχ, rc (.ofChar χ hχ) = WD.lpOfChar h (χ.comp a) (ha.smooth hχ)

  eps : ∀ ψ : AddChar (w.adicCompletion E) Circle, Continuous ψ → ψ ≠ 1 →
    ∀ (m : ℕ) (π : IrrRep (GL (Fin (m + 1)) (w.adicCompletion E))) (τ : IrrRep (GL (Fin m) (w.adicCompletion E))),
      IsCuspidal π.ρ → HasPairEps ψ π.ρ τ.ρ (ε E w h ψ ((rc (cls π)).lpChar (rc (cls τ))))

  twist : ∀ x χ hχ, rc (x.tw χ hχ) = (rc x).lpChar (rc (.ofChar χ hχ))

  central : ∀ (x : IrrGL (w.adicCompletion E)) ω, HasCentralChar x.rep ω →
    ∀ σ, ((rc x).eig σ).prod = (ω (a σ) : ℂ)

  dual : ∀ (n : ℕ) (π π' : IrrRep (GL (Fin n) (w.adicCompletion E))), Nonempty (π'.ρ.Equiv (contra π.ρ)) →
    rc (cls π') = (rc (cls π)).lpDual

  cusp : ∀ x, x.IsCusp ↔ IsIrrWD (rc x)

  langlands : ∀ (l : List (Segment (w.adicCompletion E))) (x : IrrGL (w.adicCompletion E)),
    IsL (l : Multiset (Segment (w.adicCompletion E))) x.rep →
    rc x = sumList (l.map fun Δ => ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp h Δ.len))

  det : ∀ (t : ℕ) χ hχ, rc (cls (IrrRep.det (Fin t) χ hχ)) =
    sumList ((List.range t).map fun j : ℕ => (rc (.ofChar χ hχ)).lpTw (((t : ℝ) - 1) / 2 - j))

  prod : ∀ (r t : ℕ) (σ : IrrRep (GL (Fin r) (w.adicCompletion E))) (τ : IrrRep (GL (Fin t) (w.adicCompletion E)))
    (π : IrrRep (GL (Fin (r + t)) (w.adicCompletion E))), Nonempty (π.ρ.Equiv (prod₂ σ.ρ τ.ρ)) →
    rc (cls π) = (rc (cls σ)).lpSum (rc (cls τ))

  supp : ∀ (x : IrrGL (w.adicCompletion E)) s, HasSupport x.rep s →
    ∀ σ, (rc x).charPol σ = (s.map fun y => (rc y).charPol σ).prod

  sph : ∀ x : IrrGL (w.adicCompletion E), IsSpherical x.rep ↔ (rc x).unr

  sat : ∀ (x : IrrGL (w.adicCompletion E)) (α : Fin x.1 → ℂˣ), HasSatake x.rep α →
    rc x = WD.mk (WDRep.diag h fun i => (α i)⁻¹)

  depth : ∀ x : IrrGL (w.adicCompletion E),
    fixed x.rep (KOne (w.adicCompletion E) (Fin x.1)) ≠ ⊥ ↔ IsTameWD (rc x)

variable (h) in

def IsRec (rc : IrrGL (w.adicCompletion E) → WD h) : Prop :=
  ∃ (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (ε : EpsFamily A), IsDeligneEps ε ∧ Laws a ha ε rc

def FieldCompatible {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
    {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}
    (rc : IrrGL (w.adicCompletion E) → WD h) (rc' : IrrGL (w'.adicCompletion E') → WD h') : Prop :=
  ∀ (φ : Ω ≃+* Ω') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'),
    (∀ z, φ z ∈ A' ↔ z ∈ A) → (∀ x, φ (algebraMap E Ω x) = algebraMap E' Ω' (j x)) → Continuous i →
    (∀ x, i (algebraMap E _ x) = algebraMap E' _ (j x)) →
    ∀ (n : ℕ) (π : IrrRep (GL (Fin n) (w.adicCompletion E))) (π' : IrrRep (GL (Fin n) (w'.adicCompletion E')))
      (e : π.V ≃ₗ[ℂ] π'.V), (∀ g v, e (π.ρ g v) = π'.ρ (GeneralLinearGroup.map i.toRingHom g) (e v)) →
      ∃ (b : WDRep h (Fin n → ℂ)) (b' : WDRep h' (Fin n → ℂ)), WD.mk b = rc (cls π) ∧ WD.mk b' = rc' (cls π') ∧
        b.N = b'.N ∧ ∀ (σ : Weil h) (σ' : Weil h'), (∀ z, φ ((σ : G E Ω) z) = (σ' : G E' Ω') (φ z)) → b.ρ σ = b'.ρ σ'

end GlobalTheory.LocLanglands

namespace GlobalTheory.Published

open GlobalTheory.LocLanglands

def LocalLanglandsGL : Prop :=
  (∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), ∃! rc : IrrGL (w.adicCompletion E) → WD h, IsRec h rc) ∧
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] (A' : ValuationSubring Ω')
    (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A' w')
    (rc : IrrGL (w.adicCompletion E) → WD h) (rc' : IrrGL (w'.adicCompletion E') → WD h'),
    IsRec h rc → IsRec h' rc' → FieldCompatible rc rc'

end GlobalTheory.Published

namespace GlobalTheory.LocLanglands

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem lpChar_lpOfChar (x : WD h) (ξ : Weil h →* ℂˣ) (hξ : WeilDeligne.IsSmooth ξ) :
    x.lpChar (WD.lpOfChar h ξ hξ) = x.lpTwist ξ hξ := by
  obtain ⟨n, b, rfl⟩ := x.exists_rep
  rw [WD.lpOfChar, WD.lpChar_mk, WD.lpTwist_mk]
  refine WD.sound ⟨(TensorProduct.congr (.refl ℂ _) (LinearEquiv.funUnique (Fin 1) ℂ ℂ)).trans
    (TensorProduct.rid ℂ _), fun σ v => ?_, fun v => ?_⟩
  · induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [smul_smul, mul_comm]
    | add x y hx hy => simp only [map_add, hx, hy]
  · induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp
    | add x y hx hy => simp only [map_add, hx, hy]

variable (w) in

theorem resCard_eq_normV : resCard (w.adicCompletion E) = normV w := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  have hO : 𝒪[w.adicCompletion E] = (w.adicCompletionIntegers E).toSubring := by
    ext y
    rw [Valuation.mem_integer_iff, he.le_one_iff_le_one]
    exact Iff.rfl
  have hq : resCard (w.adicCompletion E) = Formalism.UG.qV E w := by
    rw [← Formalism.UG.P.tjcosets_card_residue]
    exact Nat.card_congr (IsLocalRing.ResidueField.mapEquiv (RingEquiv.subringCongr hO)).toEquiv
  exact hq

variable {a : Weil h →* (w.adicCompletion E)ˣ}

theorem IsLocalArtin.unrChar_comp (ha : IsLocalArtin h a) (c : ℂˣ) :
    (SmGL.unrChar (w.adicCompletion E) c).comp a = WeilDeligne.unrChar h c⁻¹ := by
  refine MonoidHom.ext fun σ => ?_
  rw [MonoidHom.comp_apply, SmGL.unrChar_apply, ha.ord_eq, WeilDeligne.unrChar_apply, _root_.zpow_neg, _root_.inv_zpow]

theorem IsLocalArtin.absPow_comp (ha : IsLocalArtin h a) (s : ℝ) :
    (absPow (w.adicCompletion E) s).comp a = WeilDeligne.unrChar h (qPow w s) := by
  refine MonoidHom.ext fun σ => Units.ext ?_
  have hq : (0 : ℝ) ≤ ((normV w : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [MonoidHom.comp_apply, val_absPow_ofReal, GlobalTheory.LGrp.nabs_eq_zpow, ha.ord_eq, neg_neg, resCard_eq_normV,
    WeilDeligne.unrChar_apply, Units.val_zpow_eq_zpow_val, coe_qPow, ← Real.rpow_intCast, ← Real.rpow_mul hq, mul_comm,
    Real.rpow_mul hq, Real.rpow_intCast, Complex.ofReal_zpow, Complex.ofReal_cpow hq, Complex.ofReal_natCast]

variable {ha : IsLocalArtin h a} {ε : EpsFamily A} {rc : IrrGL (w.adicCompletion E) → WD h}

theorem Laws.tw_eq (H : Laws a ha ε rc) (x : IrrGL (w.adicCompletion E)) (χ : (w.adicCompletion E)ˣ →* ℂˣ)
    (hχ : IsSmoothChar χ) : rc (x.tw χ hχ) = (rc x).lpTwist (χ.comp a) (ha.smooth hχ) := by
  rw [H.twist, H.one, lpChar_lpOfChar]

theorem Laws.nu_eq (H : Laws a ha ε rc) (x : IrrGL (w.adicCompletion E)) (s : ℝ) : rc (x.nu s) = (rc x).lpTw s := by
  rw [IrrGL.nu, H.tw_eq, WD.lpTw]
  congr 1
  exact ha.absPow_comp s

theorem Laws.eq_iff (H : Laws a ha ε rc) {n : ℕ} (π π' : IrrRep (GL (Fin n) (w.adicCompletion E))) :
    rc (cls π) = rc (cls π') ↔ Nonempty (π.ρ.Equiv π'.ρ) :=
  H.bij.1.eq_iff.trans (IrrGL.of_eq_of (π := π.ρ) (σ := π'.ρ) (hs := π.smooth) (hi := π.irr) (hs' := π'.smooth)
    (hi' := π'.irr))

theorem Laws.exists_rep (H : Laws a ha ε rc) (y : WD h) :
    ∃ π : IrrRep (GL (Fin y.lpDim) (w.adicCompletion E)), rc (cls π) = y := by
  obtain ⟨⟨n, c⟩, rfl⟩ := H.bij.2 y
  have key : ∀ m, m = n → ∃ π : IrrRep (GL (Fin m) (w.adicCompletion E)), rc (cls π) = rc ⟨n, c⟩ := by
    rintro _ rfl
    exact ⟨c.rep, congrArg rc (congrArg (Sigma.mk _) c.cl_rep)⟩
  exact key _ (H.dim _)

end GlobalTheory.LocLanglands
