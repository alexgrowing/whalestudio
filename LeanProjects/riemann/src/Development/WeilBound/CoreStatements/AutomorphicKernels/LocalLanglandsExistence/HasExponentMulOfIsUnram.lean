import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DeligneLocalConstants
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PowFamIsDeligneMeas

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Pf1.LocalLanglands

section Tate

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ψ : AddChar k Circle} {χ : kˣ →* ℂˣ} {t : ℝ} {e : ℂ}

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem val_mul_le_iff (b : kˣ) {x y : k} :
    valuation k ((b : k) * y) ≤ valuation k ((b : k) * x) ↔ valuation k y ≤ valuation k x := by
  constructor
  · intro h
    have := mul_le_mul' (le_refl (valuation k ((b⁻¹ : kˣ) : k))) h
    rwa [← map_mul, ← map_mul, ← mul_assoc, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul,
      one_mul] at this
  · intro h
    rw [map_mul, map_mul]
    exact mul_le_mul' le_rfl h

theorem IsShellReps.map_mul {c : kˣ} {a : ℕ} {R : Finset kˣ} (hR : IsShellReps c a R) (b : kˣ) :
    IsShellReps (b * c) a (R.map (mulLeftEmbedding b)) := by
  refine ⟨fun r hr => ?_, fun y hy => ?_⟩
  · obtain ⟨s, hs, rfl⟩ := Finset.mem_map.1 hr
    simp only [mulLeftEmbedding_apply, ord_mul, hR.1 s hs]
    ring
  · have h1 : ord k (b⁻¹ * y) = ord k c - a := by
      have := ord_mul k b (b⁻¹ * y)
      rw [mul_inv_cancel_left] at this
      rw [ord_mul] at hy
      omega
    have h2 : ∀ r : kˣ, valuation k ((y : k) - (b * r : kˣ)) ≤ valuation k ((b * c : kˣ) : k) ↔
        valuation k (((b⁻¹ * y : kˣ) : k) - r) ≤ valuation k (c : k) := fun r => by
      rw [← val_mul_le_iff b (x := (c : k)) (y := ((b⁻¹ * y : kˣ) : k) - r)]
      have e2 : (b : k) * (((b⁻¹ * y : kˣ) : k) - r) = (y : k) - (b * r : kˣ) := by
        simp [mul_sub]
      rw [e2]
      simp only [Units.val_mul]
    obtain ⟨r, hr, hr'⟩ := hR.2 _ h1
    refine ⟨b * r, ⟨Finset.mem_map_of_mem _ hr.1, (h2 r).2 hr.2⟩, ?_⟩
    rintro _ ⟨hm, hv⟩
    obtain ⟨r', hm', rfl⟩ := Finset.mem_map.1 hm
    rw [mulLeftEmbedding_apply, hr' r' ⟨hm', (h2 r').1 hv⟩]

theorem hasExponent_mul_of_isUnram {μ : kˣ →* ℂˣ} (hμ : IsUnram μ) {a : ℕ} :
    HasExponent (χ * μ) a ↔ HasExponent χ a := by
  have key : ∀ b, ∀ x ∈ unitFilt k b, (χ * μ) x = χ x := fun b x hx => by
    rw [MonoidHom.mul_apply, hμ x hx.1, mul_one]
  unfold HasExponent
  exact and_congr (forall₂_congr fun x hx => by rw [key _ x hx])
    (forall₂_congr fun b _ => exists_congr fun x => and_congr_right fun hx => by rw [key _ x hx])

theorem isTateMeas_mul_of_const {μ : kˣ →* ℂˣ} (hμ : IsUnram μ) {c : kˣ} {a : ℕ} (hc : HasConductor ψ c)
    (ha : HasExponent χ a) {m : ℂˣ} (hm : ∀ r : kˣ, ord k r = ord k c - a → μ r = m) (he : IsTateMeas ψ t χ e) :
    IsTateMeas ψ t (χ * μ) (((m⁻¹ : ℂˣ) : ℂ) * e) := by
  obtain ⟨c', a', R, hc', ha', hR, rfl⟩ := he
  obtain rfl := ha'.unique ha
  have hord : ord k c' = ord k c :=
    valuation_eq_iff_ord.1 (le_antisymm ((hc _).1 ((hc' _).2 le_rfl)) ((hc' _).1 ((hc _).2 le_rfl)))
  refine ⟨c', a', R, hc', (hasExponent_mul_of_isUnram hμ).2 ha', hR, ?_⟩
  have hs : ∑ r ∈ R, ((((χ * μ) r)⁻¹ : ℂˣ) : ℂ) * (ψ (r : k) : ℂ) =
      ((m⁻¹ : ℂˣ) : ℂ) * ∑ r ∈ R, (((χ r)⁻¹ : ℂˣ) : ℂ) * (ψ (r : k) : ℂ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [MonoidHom.mul_apply, hm r ((hR.1 r hr).trans (by rw [hord])), mul_inv, Units.val_mul]
    ring
  rw [hs]
  ring

theorem isTateMeas_mul_unrChar (α : ℂˣ) {c : kˣ} {a : ℕ} (hc : HasConductor ψ c) (ha : HasExponent χ a)
    (he : IsTateMeas ψ t χ e) :
    IsTateMeas ψ t (χ * GlobalTheory.SmGL.unrChar k α) (((α ^ ((a : ℤ) - ord k c) : ℂˣ) : ℂ) * e) := by
  have := isTateMeas_mul_of_const (isUnram_unrChar k α) hc ha (m := α ^ (ord k c - a))
    (fun r hr => by rw [GlobalTheory.SmGL.unrChar_apply, hr]) he
  rwa [← zpow_neg, neg_sub] at this

end Tate

section WDTwist

variable {Ω : Type} [Field Ω] {A : ValuationSubring Ω}
  {E : Type} [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω] {w : HeightOneSpectrum (𝓞 E)}
  {h : IsPlaceOver A w}

theorem lpTwist_lpOfChar_unr {a : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h a)
    {χ : (w.adicCompletion E)ˣ →* ℂˣ} (hχ : IsSmoothChar χ) (z : ℂˣ) :
    (WD.lpOfChar h (χ.comp a) (ha.smooth hχ)).lpTwist (GlobalTheory.WeilDeligne.unrChar h z) (isSmooth_unrChar h z) =
      WD.lpOfChar h ((χ * GlobalTheory.SmGL.unrChar _ z⁻¹).comp a)
        (ha.smooth (hχ.mul (isSmoothChar_of_isUnram (isUnram_unrChar _ _)))) := by
  rw [WD.lpOfChar, WD.lpOfChar, WD.lpTwist_mk]
  refine WD.sound ⟨.refl _ _, fun σ u => ?_, fun u => rfl⟩
  have key : GlobalTheory.SmGL.unrChar _ z⁻¹ (a σ) = GlobalTheory.WeilDeligne.unrChar h z σ := by
    rw [GlobalTheory.SmGL.unrChar_apply, GlobalTheory.WeilDeligne.unrChar_apply, ha.ord_eq, inv_zpow', neg_neg]
  funext i
  simp [WDRep.twist, key, mul_comm, mul_left_comm]

end WDTwist

end PositivityTheory.Pf1.LocalLanglands

end
