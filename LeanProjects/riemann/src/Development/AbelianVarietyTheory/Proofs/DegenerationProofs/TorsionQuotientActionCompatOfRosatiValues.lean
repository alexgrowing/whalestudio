import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WithISelf
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistIsoTorsionRepresentativeMulEquiv
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusExtensionActionInValues
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

noncomputable section
namespace GlobalTheory.Relabel

theorem c_smul_val {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {N : NumD F} {O : Type} [CommRing O] [StarRing O] [Module O D.X]
    (ν : NumOf D F N) (oa : D.OAct O) (x : O) (χ : N.X) :
    N.c (ν.eX.symm (x • ν.eX χ)) = actV ν oa.onB x (N.c χ) := by
  rw [actV, ν.eA.eq_symm_apply, ν.c_eq, ν.c_eq, ν.eX.apply_symm_apply, DegPre.cF, oa.c_lin, Category.assoc]

theorem actq_cancel {F : Type} [Field F] {s s' s₀ s₀' t h₁ h₂ h₃ h₄ h₅ h₆ : Fˣ} {ρ ρ' : F}
    (e₁ : (s : F) = s₀ * ρ) (e₂ : s' * h₃ = s * t * h₅ * h₆) (e₃ : s₀' * h₄ = s₀ * t * h₁ * h₂)
    (e₄ : ρ' * (h₁ * h₂ * h₃ : Fˣ) = ρ * (h₄ * h₅ * h₆ : Fˣ)) : (s' : F) = s₀' * ρ' := by
  have a := congrArg Units.val e₂
  have b := congrArg Units.val e₃
  simp only [Units.val_mul] at a b e₄
  refine mul_right_cancel₀ (mul_ne_zero h₃.ne_zero h₄.ne_zero) ?_
  rw [e₁] at a
  linear_combination (h₄ : F) * a - ρ' * h₃ * b - (s₀ : F) * t * e₄

theorem actCompat_of_rosV : GlobalFnsSt → BrGtSt → AllD fun {E} _ _ _ {H} D => letI := H.starRing; ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] (A : ArcF D R F) (D' : DegPre R') [Module (𝓞 E) D'.X] (oa' : D'.OAct (𝓞 E)), D'.PsiEven → D'.TauBimult → ∀ (N' : NumD F) (ν' : NumOf D' F N') (k : ℕ) (β : A.N.Form k) (u : Fˣ) (r : ℕ → Fˣ) (J : NumD.Iso (A.N.twist β u) N'), Roots u r → A.Bal β → (∀ (x : 𝓞 E) y, ν'.eX (J.e (A.act x y)) = x • ν'.eX (J.e y)) → (∀ (x : 𝓞 E) b, J.φ (actV (N := A.N) A.ν A.oa.onB x b) = actV ν' oa'.onB x (J.φ b)) → (∀ a : 𝓞 E, ∃ ρ ρ', RosV A.ν A.oa.onB a ρ ∧ RosV ν' oa'.onB a ρ' ∧ ∀ b b' : A.N.A, ρ' (J.φ b) (J.φ b') * (J.h (actV (N := A.N) A.ν A.oa.onB (star a) b) * J.h b' * J.h (b * actV (N := A.N) A.ν A.oa.onB a b') : Fˣ) = ρ b b' * (J.h (actV (N := A.N) A.ν A.oa.onB (star a) b * b') * J.h b * J.h (actV (N := A.N) A.ν A.oa.onB a b') : Fˣ)) → ActCompat A.ν A.oa ν' oa' β u r J := by
  intro hG hB E _ _ _ H D
  letI := H.starRing
  intro R R' _ _ _ _ F _ _ _ _ A D' _ oa' he' hb' N' ν' k β u r J hr hbal hX hA hρ
  intro j hj x p₀ p₁ p₀' p₁' q₀ q₁ q₀' q₁' ⟨q, hqy, hqg, hqe⟩ h₀ h₁ t₀ t₁ h₀' h₁'
  obtain ⟨-, -, -, -, B⟩ := hB R A.D₀ A.even A.bimult F A.N A.ν
  obtain ⟨-, -, -, -, B'⟩ := hB R' D' he' hb' F N' ν'
  obtain ⟨τ, hτ, hτe, -⟩ := (twJ_mulEquiv F A.N N' k β u J).1 (r j) j (hr.pow hj)
  obtain ⟨qv, hqv, -⟩ := (B j).1 q
  obtain ⟨q', hq'⟩ := (B' j).2.1 (τ qv)
  have tq := (hτ qv _).1 rfl
  obtain ⟨ρ, ρ', hρ₁, hρ₂, hρ₃⟩ := hρ x
  obtain ⟨vb, vs⟩ := ((gtAct_values hG R A.D₀ F A.N A.ν (𝓞 E)).2 A.oa x ρ hρ₁ _ _ _ _ h₀.2 hqv.2).1 hqg
  have hy : qv.1.1.toAdd = A.act x q₀.1.1.toAdd := by
    rw [ArcF.act, A.ν.eX.eq_symm_apply, hqv.1, h₀.1, hqy]
  obtain ⟨P, ⟨Py, Pb, Ps⟩, Py', Pb', Ps'⟩ := tq
  obtain ⟨P₀, ⟨P₀y, P₀b, P₀s⟩, P₀y', P₀b', P₀s'⟩ := t₀
  refine ⟨q', ?_, ?_, ?_⟩
  · rw [← hq'.1, ← h₀'.1, Py', P₀y', Py, P₀y]
    exact (congrArg (fun y => ν'.eX (J.e y)) hy).trans (hX _ _)
  · refine ((gtAct_values hG R' D' F N' ν' (𝓞 E)).2 oa' x ρ' hρ₂ _ _ _ _ h₀'.2 hq'.2).2 ⟨?_, ?_⟩
    · rw [Pb', P₀b', Pb, P₀b, vb]
      exact hA _ _
    · rw [J.e.surjective.forall]
      intro (χ : A.N.X)
      have e₁ := vs χ
      have e₂ := Ps' χ
      have e₃ := P₀s' (A.act (star x) χ)
      have e₄ := hρ₃ (A.N.c χ) q₀.1.2.b
      have c₁ : (A.N.twist β u).c (A.act (star x) χ) = actV (N := A.N) A.ν A.oa.onB (star x) (A.N.c χ) :=
        c_smul_val A.ν A.oa (star x) χ
      rw [Ps, Pb, vb, hy, hbal] at e₂
      rw [P₀s, P₀b, c₁] at e₃
      have l : ν'.eX.symm (star x • ν'.eX (J.e χ)) = J.e (A.act (star x) χ) := by
        rw [ν'.eX.symm_apply_eq, hX]
      have c₂ : N'.c (J.e χ) = J.φ (A.N.c χ) := J.c_eq χ
      rw [l, c₂, P₀b', P₀b]
      exact actq_cancel e₁ e₂ e₃ e₄
  · refine ((B' j).2.2 q' p₁' _ _ hq' h₁').2 ?_
    rw [← (hτ q₁ q₁').2 t₁]
    exact (hτe _ _).1 (((B j).2.2 q p₁ _ _ hqv h₁).1 hqe)

end GlobalTheory.Relabel
end
