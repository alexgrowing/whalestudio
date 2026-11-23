import Development.WeilBound.CoreStatements.SesquilinearFractions.QReInr
import Development.WeilBound.CoreStatements.SesquilinearFractions.ImIMulDivSq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace PositivityTheory.Xgf

theorem gram_signature_orthogonal_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (p q : ℕ) (x : Fin p ⊕ Fin q → D.La), IsTypeFn H p q ty → p + q = D.p + D.q → LinearIndependent (𝓞 E) x → (∀ a b, sesq D (x (.inl a)) (x (.inr b)) = 0) → (∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → ((gramE D (x ∘ Sum.inl)).map fun a => Complex.I * τ a).PosDef ∧ (-((gramE D (x ∘ Sum.inr)).map fun a => Complex.I * τ a)).PosDef) → ∃ (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P), IsPure hP x := by
  intro E _ _ _ H D g ty p q x hty hpq hx horth hpos
  have := D.fin
  have := D.proj
  have hcard : Fintype.card (Fin p ⊕ Fin q) = Module.finrank (𝓞 E) D.La := by
    rw [D.rank, ← hpq]; simp
  obtain ⟨n, hn0, hn⟩ := exists_nsmul_mem_span_full_family x hcard hx
  have hc0 : ∀ y, DPer.coef D x hx n hn y = 0 → y = 0 := DPer.eq_zero_of_coef D x hx n hn hn0
  have hcx := DPer.planeCoef_mulVec_smul_x_eq_zero_of_ne D x hx n hn
  have hP : IsPeriod D ty (DPer.per hty (DPer.coef D x hx n hn) n) := by
    refine ⟨DPer.per_smul hty _ n, ?_, DPer.per_discrete hty _ n hn0 hc0, DPer.per_span hty x _ n hn0 hcx,
      DPer.Hm hty (gramE D x), DPer.Hm_herm hty _ ?_, DPer.Hm_pos hty _ (fun τ h => (hpos τ h).1) (fun τ h => (hpos τ h).2),
      DPer.herm_EF hty _ n hn0 x (DPer.coef_sum D x hx n hn) horth⟩
    · rw [injective_iff_map_eq_zero]
      exact fun y h => hc0 y (DPer.coef_zero_of_per hty _ n hn0 y h)
    · exact fun m m' => (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.2.2.2.1 (x m) (x m')
  refine ⟨_, hP, fun a => ?_, fun b => ?_⟩
  · intro k hk
    exact DPer.per_inl hty _ n _ a (hcx _) k (by simpa [sgnRt] using hk)
  · intro k hk
    exact DPer.per_inr hty _ n _ b (hcx _) k (by simpa [sgnRt] using hk)

end PositivityTheory.Xgf
