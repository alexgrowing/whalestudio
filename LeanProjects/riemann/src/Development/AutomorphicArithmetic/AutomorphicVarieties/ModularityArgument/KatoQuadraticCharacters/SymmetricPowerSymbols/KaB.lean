import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CycSpec

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

theorem UpperTheory.V.Z.Kato.Sym.kaB :
    UpperTheory.V.Z.Kato.Sym.KaB := by
  intro Ω _ _ _ ε X m hm θ u hu hθ
  haveI : NeZero m := ⟨hm.ne'⟩
  obtain ⟨hprim, hrep, huniq, hcoc, hmul, hequiv, -⟩ := lgB Ω ε X m hm
  have hio : ∀ {x : X.K}, x ≠ 0 → io X x ≠ 0 := fun hx => (map_ne_zero (io X)).mpr hx
  have hne : ∀ {y : Kb X} {w : X.K}, w ≠ 0 → y ^ m = io X w → y ≠ 0 := by
    rintro y w hw hy rfl
    rw [zero_pow hm.ne'] at hy
    exact hio hw hy.symm
  have hθ0 : θ ≠ 0 := hne hu hθ
  have hpow : ∀ {y : Kb X} {w : X.K} (h : RingAut (Kb X)), InD X h → y ^ m = io X w →
      (h y) ^ m = y ^ m := by
    intro y w h hh hy
    rw [← map_pow, hy, hh w]
  have hzt : ∀ (g : RingAut (Kb X)), InD X g → g (zt X m) = zt X m := fun g hg => hg _
  have hkey : ∀ (h : RingAut (Kb X)), InD X h → h θ = zt X m ^ (ka X m θ h).val * θ :=
    fun h hh => hrep _ _ hθ0 (hpow h hh hθ)
  have hself : ∀ a : Kb X, a ≠ 0 → lg X m a a = 0 := fun a ha =>
    huniq a a 0 ha (by rw [ZMod.val_zero, pow_zero, one_mul])
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g h hg hh
    have e1 : (g * h) θ = g (h θ) := rfl
    have hgθ : g θ ≠ 0 := (map_ne_zero g).mpr hθ0
    have hA : ((g * h) θ) ^ m = (g θ) ^ m := by
      rw [e1, ← map_pow, hpow h hh hθ, map_pow]
    have hB : (g θ) ^ m = θ ^ m := hpow g hg hθ
    have hC : ka X m θ (g * h) = lg X m ((g * h) θ) (g θ) + ka X m θ g := hcoc _ _ _ hθ0 hA hB
    have hD : lg X m ((g * h) θ) (g θ) = ka X m θ h := by
      apply huniq _ _ _ hgθ
      rw [e1, hkey h hh, map_mul, map_pow, hzt g hg]
    rw [hC, hD, add_comm]
  · intro θ' hθ' h hh
    obtain ⟨j, hj⟩ : ∃ j : ZMod m, θ' = zt X m ^ j.val * θ :=
      ⟨_, hrep _ _ hθ0 (by rw [hθ', hθ])⟩
    subst hj
    have hz0 : zt X m ^ j.val ≠ 0 := pow_ne_zero _ (hprim.ne_zero hm.ne')
    show lg X m (h (zt X m ^ j.val * θ)) (zt X m ^ j.val * θ) = lg X m (h θ) θ
    rw [map_mul, map_pow, hzt h hh, hmul _ _ _ _ hz0 hθ0 rfl (hpow h hh hθ), hself _ hz0, zero_add]
  · exact ⟨{θ}, fun h h' _ _ hb => by
      show lg X m (h θ) θ = lg X m (h' θ) θ
      rw [hb θ (by simp)]⟩
  · intro hU B h hOv hh hsmall
    by_contra hk
    have hone : ∀ y : Kb X, y ≠ 0 → y ∈ B → y⁻¹ ∈ B → B.valuation y = 1 := by
      intro y hy0 hy1 hy2
      have h1 := (B.valuation_le_one_iff y).mpr hy1
      have h2 := (B.valuation_le_one_iff _).mpr hy2
      rw [map_inv₀] at h2
      have hpos : 0 < B.valuation y := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hy0)
      exact le_antisymm h1 ((inv_le_one₀ hpos).mp h2)
    have hWu : (B.comap (io X)).valuation u = 1 := hU.2 _ hOv
    have hu1 : u ∈ B.comap (io X) := ((B.comap (io X)).valuation_le_one_iff u).mp hWu.le
    have hu2 : u⁻¹ ∈ B.comap (io X) := by
      apply ((B.comap (io X)).valuation_le_one_iff _).mp
      rw [map_inv₀, hWu, inv_one]
    have hvu : B.valuation (io X u) = 1 := by
      apply hone _ (hio hu) (ValuationSubring.mem_comap.mp hu1)
      rw [← map_inv₀]
      exact ValuationSubring.mem_comap.mp hu2
    have hvθ : B.valuation θ = 1 := by
      have : B.valuation θ ^ m = 1 := by rw [← map_pow, hθ, hvu]
      exact (pow_eq_one_iff.mp this).resolve_right hm.ne'
    set k := ka X m θ h with hkdef
    have hkne : k.val ≠ 0 := fun h0 => hk ((ZMod.val_eq_zero k).mp h0)
    have hζ1 : zt X m ^ k.val ≠ 1 := hprim.pow_ne_one_of_pos_of_lt hkne (ZMod.val_lt k)
    set c : Ω := eOm ε (1 / (m : ℚ)) ^ k.val - 1 with hcdef
    have hc : zt X m ^ k.val - 1 = io X (algebraMap Ω X.K c) := by
      simp only [hcdef, zt, map_sub, map_pow, map_one]
    have hc0 : c ≠ 0 := by
      intro h0
      rw [h0, map_zero, map_zero] at hc
      exact hζ1 (sub_eq_zero.mp hc)
    have hv1 : B.valuation (zt X m ^ k.val - 1) = 1 := by
      apply hone _ (sub_ne_zero.mpr hζ1)
      · rw [hc]; exact ValuationSubring.mem_comap.mp (hOv.1 c)
      · rw [hc, ← map_inv₀, ← map_inv₀]; exact ValuationSubring.mem_comap.mp (hOv.1 c⁻¹)
    have hs := hsmall θ hvθ.le
    rw [hkey h hh, ← sub_one_mul, map_mul, hv1, hvθ, one_mul] at hs
    exact lt_irrefl _ hs
  · intro σ τ s hA hLf h hh
    have hD : InD X (σ⁻¹ * h * σ) := by
      intro f
      show σ.symm (h (σ (io X f))) = io X f
      rw [hLf f, hh, ← hLf f, RingEquiv.symm_apply_apply]
    refine ⟨hD, ?_⟩
    show lg X m (h (σ θ)) (σ θ) = cyc m s * lg X m ((σ⁻¹ * h * σ) θ) θ
    have hy : ((σ⁻¹ * h * σ) θ) ^ m = θ ^ m := hpow _ hD hθ
    have e : h (σ θ) = σ ((σ⁻¹ * h * σ) θ) := by
      show _ = σ (σ.symm (h (σ θ)))
      rw [RingEquiv.apply_symm_apply]
    rw [e]
    exact hequiv σ τ s hA hLf _ _ hθ0 hy
  · intro θ' u' hu' hθ' h hh
    have hθ'0 := hne hu' hθ'
    show lg X m (h (θ * θ')) (θ * θ') = lg X m (h θ) θ + lg X m (h θ') θ'
    rw [map_mul]
    exact hmul _ _ _ _ hθ0 hθ'0 (hpow h hh hθ) (hpow h hh hθ')
