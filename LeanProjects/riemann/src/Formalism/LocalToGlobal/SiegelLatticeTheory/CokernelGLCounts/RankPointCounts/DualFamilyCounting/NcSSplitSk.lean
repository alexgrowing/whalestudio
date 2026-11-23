import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSplitS

noncomputable section

namespace Formalism.L2.SG.Pf.NcS.SplitSk

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.Volumes Formalism.L2.SG.LocVol
  NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

def AdTup : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E),
    IsCMExt F E σ → IsHermND σ J →
    Measurable (splitA σ J) ∧
    (∀ (g₁ : HA (Ainf F) σ J) (g₂ : HA (Af F) σ J), ∃ g, splitA σ J g = (g₁, g₂)) ∧
    (∀ (a : ℕ) (g : HA (AF F) σ J) (X : Fin a → Fin n → AF F ⊗[F] E),
      projInf (g • X) = (splitA σ J g).1 • projInf X ∧ projFin (g • X) = (splitA σ J g).2 • projFin X) ∧
    (∀ (a : ℕ) (X0 : Fin a → Fin n → E), projInf (ratTup (F := F) (AF F) X0) = ratTup (Ainf F) X0 ∧
      projFin (ratTup (F := F) (AF F) X0) = ratTup (Af F) X0) ∧
    (∀ (a : ℕ) (X Y : Fin a → Fin n → AF F ⊗[F] E), projInf X = projInf Y → projFin X = projFin Y → X = Y) ∧
    (∀ g : HA (Ainf F) σ J, Measurable (fun h : HA (Ainf F) σ J => g * h)) ∧
    (∀ g : HA (Af F) σ J, Measurable (fun h : HA (Af F) σ J => g * h)) ∧
    (∀ μ : Measure (HA (Ainf F) σ J), μ.IsHaarMeasure → SFinite μ) ∧
    (∀ μ : Measure (HA (Af F) σ J), μ.IsHaarMeasure → SFinite μ) ∧
    (∀ (r : ℕ) (P : Frame E n r) (μ : Measure (Hsub (Ainf F) σ J P)), μ.IsHaarMeasure → SFinite (amb μ)) ∧
    (∀ (r : ℕ) (P : Frame E n r) (μ : Measure (Hsub (Af F) σ J P)), μ.IsHaarMeasure → SFinite (amb μ)) ∧
    (∀ Λ : Set (Fin n → E), (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
      MeasurableSet (Kf σ J Λ : Set (HA (Af F) σ J))) ∧
    (∀ (Λ : Set (Fin n → E)) (μf : Measure (HA (Af F) σ J)), (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) → μf.IsHaarMeasure →
      0 < μf (Kf σ J Λ) → μf (Kf σ J Λ) < ⊤ →
      ∀ (r : ℕ) (P : Frame E n r) (μ : Measure (Hsub (Af F) σ J P)), μ.IsHaarMeasure →
        0 < μ (Subtype.val ⁻¹' (Kf σ J Λ : Set (HA (Af F) σ J))) ∧
        μ (Subtype.val ⁻¹' (Kf σ J Λ : Set (HA (Af F) σ J))) < ⊤)

def OmDecomp : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ) (a : ℕ)
    (X0 : Fin a → Fin n → E) (hT : ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j)
    (νX : Measure (Fin a → Fin n → AF F ⊗[F] E)),
    StdHyp σ J ψ → (gramE σ J X0).det ≠ 0 → 1 ≤ a → 2 * a < n → Formalism.MainNotions.UnusedSlot34.SWa1 F E σ n J →
    Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility F E σ n J → IsOmT F E σ n J ψ (gramE σ J X0) hT νX →
    ∀ (μinf : Measure (Fin a → Fin n → Ainf F ⊗[F] E)) (νinf : Measure (HermR (Ainf F) σ a))
      (fibInf : HermR (Ainf F) σ a → Measure (Fin a → Fin n → Ainf F ⊗[F] E)),
      SdW F E σ n J (Ainf F) (psiInf F ψ) a μinf → SdHerm F E σ (Ainf F) (psiInf F ψ) a νinf →
      IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
        {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fibInf →
      ∃ ωf : Measure (Fin a → Fin n → Af F ⊗[F] E),
        ∀ (A : (Fin a → Fin n → Ainf F ⊗[F] E) → ENNReal) (S : Set (Fin a → Fin n → Af F ⊗[F] E)),
          MeasurableSet S →
          ∫⁻ y, A (projInf y) * S.indicator 1 (projFin y) ∂νX =
            ωf S * ∫⁻ z, A z ∂(fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT))

def OmFinVol : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ) (a : ℕ)
    (X0 : Fin a → Fin n → E) (hT : ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j)
    (νX : Measure (Fin a → Fin n → AF F ⊗[F] E)) (Λ : Set (Fin n → E)) (μf : Measure (HA (Af F) σ J)),
    StdHyp σ J ψ → (gramE σ J X0).det ≠ 0 → 1 ≤ a → 2 * a < n → Formalism.MainNotions.UnusedSlot34.SWa1 F E σ n J →
    Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility F E σ n J →
    (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    IsOmT F E σ n J ψ (gramE σ J X0) hT νX →
    μf.IsHaarMeasure → 0 < μf (Kf σ J Λ) → μf (Kf σ J Λ) < ⊤ →
    MeasurableSet {X : Fin a → Fin n → Af F ⊗[F] E | ∃ k ∈ Kf σ J Λ, X = k • ratTup (Af F) X0} ∧
    ∀ (μinf : Measure (Fin a → Fin n → Ainf F ⊗[F] E)) (νinf : Measure (HermR (Ainf F) σ a))
      (fibInf : HermR (Ainf F) σ a → Measure (Fin a → Fin n → Ainf F ⊗[F] E)),
      SdW F E σ n J (Ainf F) (psiInf F ψ) a μinf → SdHerm F E σ (Ainf F) (psiInf F ψ) a νinf →
      IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
        {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fibInf →
      fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT) ≠ 0 →
      ∀ ωf : Measure (Fin a → Fin n → Af F ⊗[F] E),
        (∀ (A : (Fin a → Fin n → Ainf F ⊗[F] E) → ENNReal) (S : Set (Fin a → Fin n → Af F ⊗[F] E)),
          MeasurableSet S →
          ∫⁻ y, A (projInf y) * S.indicator 1 (projFin y) ∂νX =
            ωf S * ∫⁻ z, A z ∂(fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT))) →
        ωf {X | ∃ k ∈ Kf σ J Λ, X = k • ratTup (Af F) X0} =
          ENNReal.ofReal (∏' v : HeightOneSpectrum (𝓞 F),
            (omAt σ J ψ v ((gramE σ J X0).map (inclR (Fv F v)))
              {X | ∃ k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v, X = k • ratTup (Fv F v) X0}).toReal)

section Red

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {P : Frame E n r}

theorem SplitSk_finFactor (Λ : Set (Fin n → E)) (μ : Measure (Hsub (Af F) σ J P)) (hμ : μ.IsHaarMeasure)
    (hmulF : ∀ g : HA (Af F) σ J, Measurable (fun h : HA (Af F) σ J => g * h))
    (hK : MeasurableSet (Kf σ J Λ : Set (HA (Af F) σ J))) (c2 : HA (Af F) σ J)
    (x : Fin (r + 1 + r) → Fin n → Af F ⊗[F] E) (hx : c2 • ratTup (F := F) (Af F) (tupH P) = x) :
    ∫⁻ h, (Kf σ J Λ : Set (HA (Af F) σ J)).indicator 1 (c2 * (h : HA (Af F) σ J)) ∂μ =
      μ (Subtype.val ⁻¹' (Kf σ J Λ : Set (HA (Af F) σ J))) *
        {X : Fin (r + 1 + r) → Fin n → Af F ⊗[F] E | ∃ k ∈ Kf σ J Λ, X = k • ratTup (Af F) (tupH P)}.indicator 1 x := by
  classical
  have := hμ
  have hmeas : Measurable (fun h : ↥(Hsub (Af F) σ J P) => c2 * (h : HA (Af F) σ J)) :=
    (hmulF c2).comp measurable_subtype_coe
  have hS : MeasurableSet {h : ↥(Hsub (Af F) σ J P) | c2 * (h : HA (Af F) σ J) ∈ Kf σ J Λ} := hmeas hK
  have e1 : (fun h : ↥(Hsub (Af F) σ J P) =>
      (Kf σ J Λ : Set (HA (Af F) σ J)).indicator (1 : HA (Af F) σ J → ENNReal) (c2 * (h : HA (Af F) σ J))) =
      {h : ↥(Hsub (Af F) σ J P) | c2 * (h : HA (Af F) σ J) ∈ Kf σ J Λ}.indicator 1 := by
    funext h
    by_cases hh : c2 * (h : HA (Af F) σ J) ∈ Kf σ J Λ <;> simp [Set.indicator, hh]
  rw [e1, lintegral_indicator_one hS]
  by_cases hxK : x ∈ {X : Fin (r + 1 + r) → Fin n → Af F ⊗[F] E | ∃ k ∈ Kf σ J Λ, X = k • ratTup (Af F) (tupH P)}
  · rw [Set.indicator_of_mem hxK, Pi.one_apply, mul_one]
    obtain ⟨k, hk, hkx⟩ := hxK
    have hmem : k⁻¹ * c2 ∈ Hsub (Af F) σ J P := by
      show k⁻¹ * c2 ∈ MulAction.stabilizer (HA (Af F) σ J) (ratTup (F := F) (Af F) (tupH P))
      rw [MulAction.mem_stabilizer_iff, mul_smul, hx, hkx, inv_smul_smul]
    let h1 : ↥(Hsub (Af F) σ J P) := ⟨k⁻¹ * c2, hmem⟩
    have e2 : {h : ↥(Hsub (Af F) σ J P) | c2 * (h : HA (Af F) σ J) ∈ Kf σ J Λ} =
        (fun h => h1 * h) ⁻¹' (Subtype.val ⁻¹' (Kf σ J Λ : Set (HA (Af F) σ J))) := by
      ext h
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Subgroup.coe_mul, SetLike.mem_coe, h1]
      rw [mul_assoc, (Kf σ J Λ).mul_mem_cancel_left ((Kf σ J Λ).inv_mem hk)]
    have hm1 : Measurable (fun h : ↥(Hsub (Af F) σ J P) => h1 * h) := by
      refine Measurable.subtype_mk (f := fun h : ↥(Hsub (Af F) σ J P) => (h1 : HA (Af F) σ J) * (h : HA (Af F) σ J)) ?_
      exact (hmulF _).comp measurable_subtype_coe
    rw [e2, ← Measure.map_apply hm1 (measurable_subtype_coe hK), map_mul_left_eq_self]
  · have e0 : {X : Fin (r + 1 + r) → Fin n → Af F ⊗[F] E | ∃ k ∈ Kf σ J Λ, X = k • ratTup (Af F) (tupH P)}.indicator
        (1 : (Fin (r + 1 + r) → Fin n → Af F ⊗[F] E) → ENNReal) x = 0 := by
      simp only [Set.indicator, hxK, if_false]
    rw [e0, mul_zero]
    have e3 : {h : ↥(Hsub (Af F) σ J P) | c2 * (h : HA (Af F) σ J) ∈ Kf σ J Λ} = ∅ := by
      ext h
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hh
      apply hxK
      refine ⟨c2 * (h : HA (Af F) σ J), hh, ?_⟩
      have hst : (h : HA (Af F) σ J) • ratTup (F := F) (Af F) (tupH P) = ratTup (F := F) (Af F) (tupH P) :=
        MulAction.mem_stabilizer_iff.mp (show (h : HA (Af F) σ J) ∈ MulAction.stabilizer (HA (Af F) σ J)
          (ratTup (F := F) (Af F) (tupH P)) from h.2)
      rw [mul_smul, hst, hx]
    rw [e3, measure_empty]

theorem SplitSk_ident (MG : MeasG σ J r) (MW : MeasW σ J P) (νH : Measure (Fin (r + 1 + r) → Fin n → AF F ⊗[F] E))
    (Λ : Set (Fin n → E)) (hsplit : Measurable (splitA σ J))
    (hsurj : ∀ (g₁ : HA (Ainf F) σ J) (g₂ : HA (Af F) σ J), ∃ g, splitA σ J g = (g₁, g₂))
    (hproj : ∀ (g : HA (AF F) σ J) (X : Fin (r + 1 + r) → Fin n → AF F ⊗[F] E),
      projInf (g • X) = (splitA σ J g).1 • projInf X ∧ projFin (g • X) = (splitA σ J g).2 • projFin X)
    (hrat : projInf (ratTup (F := F) (AF F) (tupH P)) = ratTup (Ainf F) (tupH P) ∧
      projFin (ratTup (F := F) (AF F) (tupH P)) = ratTup (Af F) (tupH P))
    (hinj : ∀ X Y : Fin (r + 1 + r) → Fin n → AF F ⊗[F] E, projInf X = projInf Y → projFin X = projFin Y → X = Y)
    (hmulF : ∀ g : HA (Af F) σ J, Measurable (fun h : HA (Af F) σ J => g * h))
    (hmulI : ∀ g : HA (Ainf F) σ J, Measurable (fun h : HA (Ainf F) σ J => g * h))
    [SFinite MG.μGinf] [SFinite MG.μGf] [SFinite (amb MW.μHinf)] [SFinite (amb MW.μHf)]
    (hK : MeasurableSet (Kf σ J Λ : Set (HA (Af F) σ J)))
    (hG : MG.IsTextNorm) (hW : MW.IsTextNorm)
    (hC : IsCompatT F E σ n J (tupH P) MG.μG MW.μH νH)
    (fibI : Measure (Fin (r + 1 + r) → Fin n → Ainf F ⊗[F] E)) (w : ENNReal)
    (hdec : ∀ A : (Fin (r + 1 + r) → Fin n → Ainf F ⊗[F] E) → ENNReal,
      ∫⁻ y, A (projInf y) * {X : Fin (r + 1 + r) → Fin n → Af F ⊗[F] E |
        ∃ k ∈ Kf σ J Λ, X = k • ratTup (Af F) (tupH P)}.indicator 1 (projFin y) ∂νH = w * ∫⁻ z, A z ∂fibI)
    (hc : MW.μHf (Subtype.val ⁻¹' (Kf σ J Λ : Set (HA (Af F) σ J))) ≠ ⊤)
    (f : HA (Ainf F) σ J → ENNReal) (hf : Measurable f)
    (s : (Fin (r + 1 + r) → Fin n → Ainf F ⊗[F] E) → HA (Ainf F) σ J)
    (hs : ∀ y, (∃ g : HA (Ainf F) σ J, g • ratTup (F := F) (Ainf F) (tupH P) = y) →
      s y • ratTup (F := F) (Ainf F) (tupH P) = y) :
    (∫⁻ g, f g ∂MG.μGinf) * MG.μGf (Kf σ J Λ) =
      MW.μHf (Subtype.val ⁻¹' (Kf σ J Λ : Set (HA (Af F) σ J))) *
        (w * ∫⁻ y, ∫⁻ h', f (s y * (h' : HA (Ainf F) σ J)) ∂MW.μHinf ∂fibI) := by
  classical
  obtain ⟨-, hGinf, hGf, -, -, hGsplit⟩ := hG
  obtain ⟨-, hHinf, hHf, -, -, -, -, -, hHsplit, -, -⟩ := hW
  have hind : Measurable ((Kf σ J Λ : Set (HA (Af F) σ J)).indicator (1 : HA (Af F) σ J → ENNReal)) :=
    measurable_one.indicator hK
  let sf : (Fin (r + 1 + r) → Fin n → Af F ⊗[F] E) → HA (Af F) σ J := fun x =>
    if h : ∃ k : HA (Af F) σ J, k • ratTup (F := F) (Af F) (tupH P) = x then h.choose else 1
  have hsf : ∀ x, (∃ k : HA (Af F) σ J, k • ratTup (F := F) (Af F) (tupH P) = x) →
      sf x • ratTup (F := F) (Af F) (tupH P) = x := by
    intro x hx
    simp only [sf, dif_pos hx]
    exact hx.choose_spec
  let sA : (Fin (r + 1 + r) → Fin n → AF F ⊗[F] E) → HA (AF F) σ J := fun y =>
    (hsurj (s (projInf y)) (sf (projFin y))).choose
  have hsA : ∀ y, splitA σ J (sA y) = (s (projInf y), sf (projFin y)) := fun y => (hsurj _ _).choose_spec
  have horb : ∀ y, (∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) (tupH P) = y) →
      (∃ g : HA (Ainf F) σ J, g • ratTup (F := F) (Ainf F) (tupH P) = projInf y) ∧
      (∃ k : HA (Af F) σ J, k • ratTup (F := F) (Af F) (tupH P) = projFin y) := by
    rintro y ⟨g0, hg0⟩
    refine ⟨⟨(splitA σ J g0).1, ?_⟩, ⟨(splitA σ J g0).2, ?_⟩⟩
    · rw [← hg0, (hproj g0 _).1, hrat.1]
    · rw [← hg0, (hproj g0 _).2, hrat.2]
  have hsec : ∀ y, (∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) (tupH P) = y) →
      sA y • ratTup (F := F) (AF F) (tupH P) = y := by
    intro y hy
    obtain ⟨hI, hF⟩ := horb y hy
    apply hinj
    · rw [(hproj (sA y) _).1, hsA y, hrat.1]
      exact hs _ hI
    · rw [(hproj (sA y) _).2, hsA y, hrat.2]
      exact hsf _ hF
  have hφ : Measurable (fun p : HA (Ainf F) σ J × HA (Af F) σ J =>
      f p.1 * (Kf σ J Λ : Set (HA (Af F) σ J)).indicator 1 p.2) :=
    (hf.comp measurable_fst).mul (hind.comp measurable_snd)
  have key : ∫⁻ g, f (splitA σ J g).1 * (Kf σ J Λ : Set (HA (Af F) σ J)).indicator 1 (splitA σ J g).2 ∂MG.μG =
      ∫⁻ y, ∫⁻ h' : ↥(Hsub (AF F) σ J P), f (splitA σ J (sA y * (h' : HA (AF F) σ J))).1 *
        (Kf σ J Λ : Set (HA (Af F) σ J)).indicator 1 (splitA σ J (sA y * (h' : HA (AF F) σ J))).2 ∂MW.μH ∂νH :=
    hC.2 _ (hφ.comp hsplit) sA hsec
  have hL : ∫⁻ g, f (splitA σ J g).1 * (Kf σ J Λ : Set (HA (Af F) σ J)).indicator 1 (splitA σ J g).2 ∂MG.μG =
      (∫⁻ g, f g ∂MG.μGinf) * MG.μGf (Kf σ J Λ) := by
    calc ∫⁻ g, f (splitA σ J g).1 * (Kf σ J Λ : Set (HA (Af F) σ J)).indicator 1 (splitA σ J g).2 ∂MG.μG
        = ∫⁻ p, f p.1 * (Kf σ J Λ : Set (HA (Af F) σ J)).indicator 1 p.2 ∂(MG.μG.map (splitA σ J)) :=
          (lintegral_map hφ hsplit).symm
      _ = ∫⁻ p, f p.1 * (Kf σ J Λ : Set (HA (Af F) σ J)).indicator 1 p.2 ∂(MG.μGinf.prod MG.μGf) := by
          rw [hGsplit]
      _ = (∫⁻ g, f g ∂MG.μGinf) * ∫⁻ g, (Kf σ J Λ : Set (HA (Af F) σ J)).indicator 1 g ∂MG.μGf :=
          lintegral_prod_mul hf.aemeasurable hind.aemeasurable
      _ = _ := by rw [lintegral_indicator_one hK]
  have hinner : ∀ y, (∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) (tupH P) = y) →
      ∫⁻ h' : ↥(Hsub (AF F) σ J P), f (splitA σ J (sA y * (h' : HA (AF F) σ J))).1 *
        (Kf σ J Λ : Set (HA (Af F) σ J)).indicator 1 (splitA σ J (sA y * (h' : HA (AF F) σ J))).2 ∂MW.μH =
      (∫⁻ h', f (s (projInf y) * (h' : HA (Ainf F) σ J)) ∂MW.μHinf) *
        (MW.μHf (Subtype.val ⁻¹' (Kf σ J Λ : Set (HA (Af F) σ J))) *
          {X : Fin (r + 1 + r) → Fin n → Af F ⊗[F] E | ∃ k ∈ Kf σ J Λ, X = k • ratTup (Af F) (tupH P)}.indicator 1
            (projFin y)) := by
    intro y hy
    obtain ⟨-, hF⟩ := horb y hy
    have hψ : Measurable (fun p : HA (Ainf F) σ J × HA (Af F) σ J =>
        f (s (projInf y) * p.1) * (Kf σ J Λ : Set (HA (Af F) σ J)).indicator 1 (sf (projFin y) * p.2)) :=
      ((hf.comp (hmulI _)).comp measurable_fst).mul ((hind.comp (hmulF _)).comp measurable_snd)
    have e : ∀ g : HA (AF F) σ J,
        f (splitA σ J (sA y * g)).1 * (Kf σ J Λ : Set (HA (Af F) σ J)).indicator 1 (splitA σ J (sA y * g)).2 =
        f (s (projInf y) * (splitA σ J g).1) *
          (Kf σ J Λ : Set (HA (Af F) σ J)).indicator 1 (sf (projFin y) * (splitA σ J g).2) := by
      intro g
      rw [map_mul, hsA y]
      rfl
    calc ∫⁻ h' : ↥(Hsub (AF F) σ J P), f (splitA σ J (sA y * (h' : HA (AF F) σ J))).1 *
          (Kf σ J Λ : Set (HA (Af F) σ J)).indicator 1 (splitA σ J (sA y * (h' : HA (AF F) σ J))).2 ∂MW.μH
        = ∫⁻ h' : ↥(Hsub (AF F) σ J P), f (s (projInf y) * (splitA σ J (h' : HA (AF F) σ J)).1) *
          (Kf σ J Λ : Set (HA (Af F) σ J)).indicator 1 (sf (projFin y) * (splitA σ J (h' : HA (AF F) σ J)).2) ∂MW.μH :=
          lintegral_congr fun h' => e _
      _ = ∫⁻ g, f (s (projInf y) * (splitA σ J g).1) *
          (Kf σ J Λ : Set (HA (Af F) σ J)).indicator 1 (sf (projFin y) * (splitA σ J g).2) ∂(amb MW.μH) :=
          (lintegral_map (hψ.comp hsplit) measurable_subtype_coe).symm
      _ = ∫⁻ p, f (s (projInf y) * p.1) *
          (Kf σ J Λ : Set (HA (Af F) σ J)).indicator 1 (sf (projFin y) * p.2) ∂((amb MW.μH).map (splitA σ J)) :=
          (lintegral_map hψ hsplit).symm
      _ = ∫⁻ p, f (s (projInf y) * p.1) *
          (Kf σ J Λ : Set (HA (Af F) σ J)).indicator 1 (sf (projFin y) * p.2) ∂((amb MW.μHinf).prod (amb MW.μHf)) := by
          rw [hHsplit]
      _ = (∫⁻ g, f (s (projInf y) * g) ∂(amb MW.μHinf)) *
          ∫⁻ g, (Kf σ J Λ : Set (HA (Af F) σ J)).indicator 1 (sf (projFin y) * g) ∂(amb MW.μHf) :=
          lintegral_prod_mul (hf.comp (hmulI _)).aemeasurable (hind.comp (hmulF _)).aemeasurable
      _ = (∫⁻ h', f (s (projInf y) * (h' : HA (Ainf F) σ J)) ∂MW.μHinf) *
          ∫⁻ h', (Kf σ J Λ : Set (HA (Af F) σ J)).indicator 1 (sf (projFin y) * (h' : HA (Af F) σ J)) ∂MW.μHf := by
          rw [amb, amb]
          congr 1
          · exact lintegral_map (hf.comp (hmulI _)) measurable_subtype_coe
          · exact lintegral_map (hind.comp (hmulF _)) measurable_subtype_coe
      _ = _ := by
          rw [SplitSk_finFactor Λ MW.μHf hHf hmulF hK _ _ (hsf _ hF)]
  have hae : ∀ᵐ y ∂νH, ∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) (tupH P) = y := ae_iff.2 hC.1
  rw [← hL, key]
  calc ∫⁻ y, ∫⁻ h' : ↥(Hsub (AF F) σ J P), f (splitA σ J (sA y * (h' : HA (AF F) σ J))).1 *
        (Kf σ J Λ : Set (HA (Af F) σ J)).indicator 1 (splitA σ J (sA y * (h' : HA (AF F) σ J))).2 ∂MW.μH ∂νH
      = ∫⁻ y, (∫⁻ h', f (s (projInf y) * (h' : HA (Ainf F) σ J)) ∂MW.μHinf) *
        (MW.μHf (Subtype.val ⁻¹' (Kf σ J Λ : Set (HA (Af F) σ J))) *
          {X : Fin (r + 1 + r) → Fin n → Af F ⊗[F] E | ∃ k ∈ Kf σ J Λ, X = k • ratTup (Af F) (tupH P)}.indicator 1
            (projFin y)) ∂νH :=
        lintegral_congr_ae (hae.mono fun y hy => hinner y hy)
    _ = ∫⁻ y, MW.μHf (Subtype.val ⁻¹' (Kf σ J Λ : Set (HA (Af F) σ J))) *
        ((∫⁻ h', f (s (projInf y) * (h' : HA (Ainf F) σ J)) ∂MW.μHinf) *
          {X : Fin (r + 1 + r) → Fin n → Af F ⊗[F] E | ∃ k ∈ Kf σ J Λ, X = k • ratTup (Af F) (tupH P)}.indicator 1
            (projFin y)) ∂νH :=
        lintegral_congr fun y => by ring
    _ = MW.μHf (Subtype.val ⁻¹' (Kf σ J Λ : Set (HA (Af F) σ J))) *
        ∫⁻ y, (∫⁻ h', f (s (projInf y) * (h' : HA (Ainf F) σ J)) ∂MW.μHinf) *
          {X : Fin (r + 1 + r) → Fin n → Af F ⊗[F] E | ∃ k ∈ Kf σ J Λ, X = k • ratTup (Af F) (tupH P)}.indicator 1
            (projFin y) ∂νH :=
        lintegral_const_mul' _ _ hc
    _ = _ := by rw [hdec (fun z => ∫⁻ h', f (s z * (h' : HA (Ainf F) σ J)) ∂MW.μHinf)]

end Red

theorem splitOm_of (h0 : AdTup) (h1 : OmDecomp) (h2 : OmFinVol) : Formalism.L2.SG.Pf.NcSplitS.SplitOm := by
  intro F E _ _ _ _ _ σ n J ψ r P MG MW hT νH Λ hStd hLat hdet hn hSWa hSWc hG hW hOm hC hK0 hKt
  classical
  obtain ⟨hsplit, hsurj, hproj, hrat, hinj, hmulI, hmulF, hsfI, hsfF, hsfHI, hsfHF, hKm, hKH⟩ :=
    h0 F E σ n J hStd.1 hStd.2.1
  have : SFinite MG.μGinf := hsfI _ hG.2.1
  have : SFinite MG.μGf := hsfF _ hG.2.2.1
  have : SFinite (amb MW.μHinf) := hsfHI r P _ hW.2.1
  have : SFinite (amb MW.μHf) := hsfHF r P _ hW.2.2.1
  obtain ⟨hc0, hcT⟩ := hKH Λ MG.μGf hLat hG.2.2.1 hK0 hKt r P MW.μHf hW.2.2.1
  obtain ⟨hKYm, hfin⟩ := h2 F E σ n J ψ (r + 1 + r) (tupH P) hT νH Λ MG.μGf hStd hdet (by omega) hn hSWa hSWc
    hLat hOm hG.2.2.1 hK0 hKt
  obtain ⟨Pv, hPv⟩ : ∃ Pv : ℝ, Pv = ∏' v : HeightOneSpectrum (𝓞 F),
      (omAt σ J ψ v ((gramE σ J (tupH P)).map (inclR (Fv F v)))
        {X | ∃ k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v, X = k • ratTup (Fv F v) (tupH P)}).toReal := ⟨_, rfl⟩
  rw [← hPv]
  simp only [← hPv] at hfin
  let s0 : (Fin (r + 1 + r) → Fin n → Ainf F ⊗[F] E) → HA (Ainf F) σ J := fun y =>
    if h : ∃ g : HA (Ainf F) σ J, g • ratTup (F := F) (Ainf F) (tupH P) = y then h.choose else 1
  have hs0 : ∀ y, (∃ g : HA (Ainf F) σ J, g • ratTup (F := F) (Ainf F) (tupH P) = y) →
      s0 y • ratTup (F := F) (Ainf F) (tupH P) = y := by
    intro y hy
    simp only [s0, dif_pos hy]
    exact hy.choose_spec
  have hpos1 : (∫⁻ _ : HA (Ainf F) σ J, (1 : ENNReal) ∂MG.μGinf) * MG.μGf (Kf σ J Λ) ≠ 0 := by
    have := hG.2.1
    rw [lintegral_one]
    exact mul_ne_zero (IsOpen.measure_pos MG.μGinf isOpen_univ ⟨1, trivial⟩).ne' hK0.ne'
  have core : ∀ (μinf : Measure (Fin (r + 1 + r) → Fin n → Ainf F ⊗[F] E))
      (νinf : Measure (HermR (Ainf F) σ (r + 1 + r)))
      (fibInf : HermR (Ainf F) σ (r + 1 + r) → Measure (Fin (r + 1 + r) → Fin n → Ainf F ⊗[F] E)),
      SdW F E σ n J (Ainf F) (psiInf F ψ) (r + 1 + r) μinf →
      SdHerm F E σ (Ainf F) (psiInf F ψ) (r + 1 + r) νinf →
      IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
        {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fibInf →
      ∀ f : HA (Ainf F) σ J → ENNReal, Measurable f →
      ∀ s : (Fin (r + 1 + r) → Fin n → Ainf F ⊗[F] E) → HA (Ainf F) σ J,
        (∀ y, (∃ g : HA (Ainf F) σ J, g • ratTup (F := F) (Ainf F) (tupH P) = y) →
          s y • ratTup (F := F) (Ainf F) (tupH P) = y) →
        (∫⁻ g, f g ∂MG.μGinf) * MG.μGf (Kf σ J Λ) =
          MW.μHf (Subtype.val ⁻¹' (Kf σ J Λ : Set (HA (Af F) σ J))) *
            (ENNReal.ofReal Pv * ∫⁻ y, ∫⁻ h', f (s y * (h' : HA (Ainf F) σ J)) ∂MW.μHinf
              ∂(fibInf (hermOf (Ainf F) σ (gramE σ J (tupH P)) hT))) := by
    intro μinf νinf fibInf hμ hν hfib
    obtain ⟨ωf, hdec⟩ := h1 F E σ n J ψ (r + 1 + r) (tupH P) hT νH hStd hdet (by omega) hn hSWa hSWc hOm
      μinf νinf fibInf hμ hν hfib
    have hI := fun f hf s hs => SplitSk_ident MG MW νH Λ hsplit hsurj (hproj (r + 1 + r)) (hrat (r + 1 + r) (tupH P))
      (hinj (r + 1 + r)) hmulF hmulI (hKm Λ hLat) hG hW hC (fibInf (hermOf (Ainf F) σ (gramE σ J (tupH P)) hT))
      (ωf {X | ∃ k ∈ Kf σ J Λ, X = k • ratTup (Af F) (tupH P)}) (fun A => hdec A _ hKYm) hcT.ne f hf s hs
    have hne : fibInf (hermOf (Ainf F) σ (gramE σ J (tupH P)) hT) ≠ 0 := by
      intro hz
      have h3 := hI (fun _ => 1) measurable_const s0 hs0
      rw [hz, lintegral_zero_measure, mul_zero, mul_zero] at h3
      exact hpos1 h3
    rw [← hfin μinf νinf fibInf hμ hν hfib hne ωf hdec]
    exact hI
  obtain ⟨μ0, hμ0⟩ := hOm.2.1
  obtain ⟨ν0, hν0⟩ := (hOm.2.2 μ0 hμ0).1
  obtain ⟨⟨μv, hμv⟩, hX⟩ := (hOm.2.2 μ0 hμ0).2 ν0 hν0
  obtain ⟨⟨νv, hνv⟩, hY⟩ := hX μv hμv
  obtain ⟨fib0, hfib0⟩ := (hY νv hνv).1
  have hPpos : 0 < Pv := by
    have h := core μ0 ν0 fib0 hμ0 hν0 hfib0 (fun _ => 1) measurable_const s0 hs0
    have h' : MW.μHf (Subtype.val ⁻¹' (Kf σ J Λ : Set (HA (Af F) σ J))) *
        (ENNReal.ofReal Pv * ∫⁻ y, ∫⁻ h', (fun _ : HA (Ainf F) σ J => (1 : ENNReal)) (s0 y * (h' : HA (Ainf F) σ J))
          ∂MW.μHinf ∂(fib0 (hermOf (Ainf F) σ (gramE σ J (tupH P)) hT))) ≠ 0 := h ▸ hpos1
    exact ENNReal.ofReal_pos.mp (pos_iff_ne_zero.mpr (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp h').2).1)
  have hm0 : MG.μGf (Kf σ J Λ) ≠ 0 := hK0.ne'
  have hmT : MG.μGf (Kf σ J Λ) ≠ ⊤ := hKt.ne
  have hmR : 0 < (MG.μGf (Kf σ J Λ)).toReal := ENNReal.toReal_pos hm0 hmT
  have hcR : 0 < (MW.μHf (Subtype.val ⁻¹' (Kf σ J Λ : Set (HA (Af F) σ J)))).toReal :=
    ENNReal.toReal_pos hc0.ne' hcT.ne
  have ha' : 0 < (MW.μHf (Subtype.val ⁻¹' (Kf σ J Λ : Set (HA (Af F) σ J)))).toReal * Pv /
      (MG.μGf (Kf σ J Λ)).toReal := div_pos (mul_pos hcR hPpos) hmR
  refine ⟨(MW.μHf (Subtype.val ⁻¹' (Kf σ J Λ : Set (HA (Af F) σ J)))).toReal * Pv / (MG.μGf (Kf σ J Λ)).toReal,
    ha', ⟨hOm.2.1, fun μinf hμ => ⟨(hOm.2.2 μinf hμ).1, fun νinf hν => ⟨?_, fun fibInf hfib f hf s hs => ?_⟩⟩⟩, ?_⟩
  · obtain ⟨⟨μv', hμv'⟩, hX'⟩ := (hOm.2.2 μinf hμ).2 νinf hν
    obtain ⟨⟨νv', hνv'⟩, hY'⟩ := hX' μv' hμv'
    exact (hY' νv' hνv').1
  · have h := core μinf νinf fibInf hμ hν hfib f hf s hs
    have hA : ENNReal.ofReal ((MW.μHf (Subtype.val ⁻¹' (Kf σ J Λ : Set (HA (Af F) σ J)))).toReal * Pv /
        (MG.μGf (Kf σ J Λ)).toReal) * MG.μGf (Kf σ J Λ) =
        MW.μHf (Subtype.val ⁻¹' (Kf σ J Λ : Set (HA (Af F) σ J))) * ENNReal.ofReal Pv := by
      calc _ = ENNReal.ofReal ((MW.μHf (Subtype.val ⁻¹' (Kf σ J Λ : Set (HA (Af F) σ J)))).toReal * Pv /
            (MG.μGf (Kf σ J Λ)).toReal) * ENNReal.ofReal (MG.μGf (Kf σ J Λ)).toReal := by
            rw [ENNReal.ofReal_toReal hmT]
        _ = ENNReal.ofReal ((MW.μHf (Subtype.val ⁻¹' (Kf σ J Λ : Set (HA (Af F) σ J)))).toReal * Pv /
            (MG.μGf (Kf σ J Λ)).toReal * (MG.μGf (Kf σ J Λ)).toReal) := (ENNReal.ofReal_mul ha'.le).symm
        _ = ENNReal.ofReal ((MW.μHf (Subtype.val ⁻¹' (Kf σ J Λ : Set (HA (Af F) σ J)))).toReal * Pv) := by
            rw [div_mul_cancel₀ _ hmR.ne']
        _ = ENNReal.ofReal (MW.μHf (Subtype.val ⁻¹' (Kf σ J Λ : Set (HA (Af F) σ J)))).toReal *
            ENNReal.ofReal Pv := ENNReal.ofReal_mul hcR.le
        _ = _ := by rw [ENNReal.ofReal_toReal hcT.ne]
    refine (ENNReal.mul_left_inj hm0 hmT).mp ?_
    rw [h, mul_right_comm, hA]
    ring
  · rw [mul_comm]
    exact div_mul_cancel₀ _ hmR.ne'

end Formalism.L2.SG.Pf.NcS.SplitSk
