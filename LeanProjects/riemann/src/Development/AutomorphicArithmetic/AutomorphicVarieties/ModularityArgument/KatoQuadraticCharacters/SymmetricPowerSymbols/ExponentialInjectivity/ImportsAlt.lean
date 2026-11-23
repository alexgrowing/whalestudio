import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CycSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ExistsAlgebraicClosureLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.MvEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.MvComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.MvNear
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.Recip
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SiegelAdmissibleToRat
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CycSpecAlt

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

theorem UpperTheory.V.Z.Kato.Sym.PC.eqv :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (m c d M : ℕ), 0 < m → 1 < c → 1 < d → Nat.Coprime c 6 → Nat.Coprime d 6 → Lv c d M → ∀ t w, IsSec X m t → IsSymb X m c d M t w → ∀ s, Eqv X m M (w s) := by
  classical
  intro Ω _ _ _ ε X m c d M hm hc hd hc6 hd6 hL t w hT hW s x y hxy
  refine ⟨(hW s x y hxy).1, fun γ => ?_⟩
  have hR := rowB Ω M hL.1
  have hSg := sgB Ω ε X
  have hAd := admB Ω ε X
  have hUτ : ∀ (τ : X.K ≃+* X.K) (s' : Gal(Ω/ℚ)), admitted X τ s' → ∀ a, IsU X a → IsU X (τ a) :=
    fun τ s' h => (hAd.2.2.2.2.2.1 τ s' h).1
  have hgr : ∀ z : Row M, gr M s (gr M s⁻¹ z) = z := by
    intro z
    rw [← (hR.1 s s⁻¹ z).1, mul_inv_cancel, (hR.1 1 1 z).2]
  have hok0 : Ok (gr M s⁻¹ x) (gr M s⁻¹ y) := (hR.2.1 x y hxy).2.2.1 s⁻¹
  have hokγ : Ok (rt x γ) (rt y γ) := (hR.2.1 x y hxy).2.2.2 γ
  have hok1 : Ok (gr M s⁻¹ (rt x γ)) (gr M s⁻¹ (rt y γ)) := (hR.2.1 _ _ hokγ).2.2.1 s⁻¹
  have sx0 := hSg c M hc hc6 hL.1 hL.2.1 _ (hR.2.1 _ _ hok0).1
  have sy0 := hSg d M hd hd6 hL.1 hL.2.2 _ (hR.2.1 _ _ hok0).2.1
  have sx := hSg c M hc hc6 hL.1 hL.2.1 _ (hR.2.1 _ _ hxy).1
  have sy := hSg d M hd hd6 hL.1 hL.2.2 _ (hR.2.1 _ _ hxy).2.1
  have sxγ := hSg c M hc hc6 hL.1 hL.2.1 _ (hR.2.1 _ _ hokγ).1
  have syγ := hSg d M hd hd6 hL.1 hL.2.2 _ (hR.2.1 _ _ hokγ).2.1
  have sx1 := hSg c M hc hc6 hL.1 hL.2.1 _ (hR.2.1 _ _ hok1).1
  have sy1 := hSg d M hd hd6 hL.1 hL.2.2 _ (hR.2.1 _ _ hok1).2.1
  have ga_u : X.gal s (sg X c M (gr M s⁻¹ x)) = sg X c M x := by rw [sx0.2.2.1 s, hgr]
  have ga_v : X.gal s (sg X d M (gr M s⁻¹ y)) = sg X d M y := by rw [sy0.2.2.1 s, hgr]
  have hP := (hT _ _ sx0.1 sy0.1).1
  obtain ⟨S, hSn⟩ := mvNear Ω ε X m hm _ _ _ hP
  obtain ⟨γ', hγ'⟩ := recip Ω ε X s γ
    (insert (sg X c M (gr M s⁻¹ x)) (insert (sg X d M (gr M s⁻¹ y)) S))
  have hB : IsPt X m (sg X c M (rt x γ)) (sg X d M (rt y γ))
      (t (sg X c M (rt x γ)) (sg X d M (rt y γ))) := (hT _ _ sxγ.1 syγ.1).1
  have h2 := (hT _ _ sx.1 sy.1).2 γ
  rw [sx.2.1 γ, sy.2.1 γ] at h2
  have p1 := mvComp Ω ε X m hm (X.gal s) (slR X (ofSL γ)) s 1 (hAd.2.1 s) (hAd.1 _) _ _ _ _ _ hP
    (by rw [ga_u, ga_v]; exact (hT _ _ sx.1 sy.1).1)
    (by
      change IsPt X m (X.sl (ofSL γ) (X.gal s _)) (X.sl (ofSL γ) (X.gal s _)) _
      rw [ga_u, ga_v, sx.2.1 γ, sy.2.1 γ]
      exact hB) _ _ (hW s x y hxy).2 h2
  have a1 := hAd.2.2.2.1 _ _ _ _ (hAd.2.1 s) (hAd.1 (ofSL γ))
  rw [one_mul] at a1 p1
  have e_u : X.sl (ofSL γ') (sg X c M (gr M s⁻¹ x)) = sg X c M (gr M s⁻¹ (rt x γ)) := by
    apply (X.gal s).injective
    rw [← hγ' _ (by simp), ga_u, sx.2.1 γ, sx1.2.2.1 s, hgr]
  have e_v : X.sl (ofSL γ') (sg X d M (gr M s⁻¹ y)) = sg X d M (gr M s⁻¹ (rt y γ)) := by
    apply (X.gal s).injective
    rw [← hγ' _ (by simp), ga_v, sy.2.1 γ, sy1.2.2.1 s, hgr]
  have h3 := (hT _ _ sx0.1 sy0.1).2 γ'
  rw [e_u, e_v] at h3
  have p2 := mvComp Ω ε X m hm (slR X (ofSL γ')) (X.gal s) 1 s (hAd.1 _) (hAd.2.1 s) _ _ _ _ _ hP
    (by
      change IsPt X m (X.sl (ofSL γ') _) (X.sl (ofSL γ') _) _
      rw [e_u, e_v]
      exact (hT _ _ sx1.1 sy1.1).1)
    (by
      change IsPt X m (X.gal s (X.sl (ofSL γ') _)) (X.gal s (X.sl (ofSL γ') _)) _
      rw [e_u, e_v, sx1.2.2.1 s, sy1.2.2.1 s, hgr, hgr]
      exact hB) _ _ h3 (hW s (rt x γ) (rt y γ) hokγ).2
  have a2 := hAd.2.2.2.1 _ _ _ _ (hAd.1 (ofSL γ')) (hAd.2.1 s)
  rw [mul_one] at a2 p2
  rw [map_one, one_pow, one_mul] at p2
  have hfix : ∀ f ∈ insert (sg X c M (gr M s⁻¹ x)) (insert (sg X d M (gr M s⁻¹ y)) S),
      (((X.gal s).trans (slR X (ofSL γ))).trans ((slR X (ofSL γ')).trans (X.gal s)).symm) f = f := by
    intro f hf
    rw [RingEquiv.trans_apply]
    have k : ((X.gal s).trans (slR X (ofSL γ))) f = ((slR X (ofSL γ')).trans (X.gal s)) f := hγ' f hf
    rw [k, RingEquiv.symm_apply_apply]
  have aρ := hAd.2.2.2.1 _ _ _ _ a1 (hAd.2.2.2.2.1 _ _ a2)
  rw [inv_mul_cancel] at aρ
  have near := hSn _ 1 aρ (fun f hf => hfix f (by simp [hf]))
  have p3 := mvComp Ω ε X m hm _ ((slR X (ofSL γ')).trans (X.gal s)) 1 s aρ a2 _ _ _ _ _ hP
    (by rw [hfix _ (by simp), hfix _ (by simp)]; exact hP)
    (by
      rw [hfix _ (by simp), hfix _ (by simp)]
      change IsPt X m (X.gal s (X.sl (ofSL γ') _)) (X.gal s (X.sl (ofSL γ') _)) _
      rw [e_u, e_v, sx1.2.2.1 s, sy1.2.2.1 s, hgr, hgr]
      exact hB) _ _ near p2
  rw [map_one, one_pow, one_mul, mul_one] at p3
  have htr : ((((X.gal s).trans (slR X (ofSL γ))).trans
      ((slR X (ofSL γ')).trans (X.gal s)).symm).trans ((slR X (ofSL γ')).trans (X.gal s)))
      = (X.gal s).trans (slR X (ofSL γ)) := by
    ext f
    simp only [RingEquiv.trans_apply, RingEquiv.apply_symm_apply]
  rw [htr] at p3
  have hC := ((mvEx Ω ε X m hm _ s a1 _ _ _ hP).2.2.2 _
    (by
      change IsPt X m (X.sl (ofSL γ) (X.gal s _)) (X.sl (ofSL γ) (X.gal s _)) _
      rw [ga_u, ga_v, sx.2.1 γ, sy.2.1 γ]
      exact hB) _ _ p3).mp p1
  rw [mul_one] at hC
  have hu : (unU X (slR X (ofSL γ))) (w s x y) = slU X (ofSL γ) (w s x y) := Units.ext rfl
  rw [hu] at hC
  rcases Nat.lt_or_ge 1 m with h1m | h1m
  · haveI : Fact (1 < m) := ⟨h1m⟩
    have hcyc := ((lgB Ω ε X m hm).2.2.2.2.2.2 1 1).2.1
    rw [hcyc, ZMod.val_one, pow_one] at hC
    exact hC
  · obtain rfl : m = 1 := by omega
    exact ⟨(w s (rt x γ) (rt y γ))⁻¹ * slU X (ofSL γ) (w s x y), by group⟩
