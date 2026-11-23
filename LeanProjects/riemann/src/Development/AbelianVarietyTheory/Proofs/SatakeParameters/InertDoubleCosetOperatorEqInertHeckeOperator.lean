import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteOfTrivOutside
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxCompactOfTrivOutsideLocalIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteInertHeckeSupportCosets
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosets
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Heckebasic
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertDCOp

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
  {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)}

theorem loc_mul (Dv : InertDatum L n v w) (x y : GAf L n) : Dv.loc (x * y) = Dv.loc x * Dv.loc y :=
  (GlobalTheory.SatInd.CosetFin.locHom Dv).map_mul x y

theorem mem_dc_iff (Dv : InertDatum L n v w) (h1 : ∀ x : GAf L n, Dv.loc x ∈ Formalism.UG.GU Dv.σw n)
    (h2 : ∀ κ : GAf L n, κ ∈ Umax L n → ∀ hκ : Dv.loc κ ∈ Formalism.UG.GU Dv.σw n,
      (⟨Dv.loc κ, hκ⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n)
    (h3 : ∀ k : GL (Fin n) (w.adicCompletion L), k ∈ Formalism.UG.GU Dv.σw n →
      ∃ x : GAf L n, TrivOutside {v} x ∧ Dv.loc x = k)
    (h4 : ∀ x y : GAf L n, TrivOutside {v} x → TrivOutside {v} y → Dv.loc x = Dv.loc y → x = y)
    {a x : GAf L n} (ha : TrivOutside {v} a) (hx : TrivOutside {v} x) :
    (⟨Dv.loc x, h1 x⟩ : Formalism.UG.GU Dv.σw n) ∈ DoubleCoset.doubleCoset (⟨Dv.loc a, h1 a⟩ : Formalism.UG.GU Dv.σw n)
        (Formalism.UG.KU Dv.σw n : Set (Formalism.UG.GU Dv.σw n)) (Formalism.UG.KU Dv.σw n : Set (Formalism.UG.GU Dv.σw n)) ↔
      ∃ k₁ ∈ InertSph.Kv L n v, ∃ k₂ ∈ InertSph.Kv L n v, x = k₁ * a * k₂ := by
  rw [DoubleCoset.mem_doubleCoset]
  constructor
  · rintro ⟨k₁, hk₁, k₂, hk₂, e⟩
    obtain ⟨κ₁, t₁, e₁⟩ := h3 k₁.1 k₁.2
    obtain ⟨κ₂, t₂, e₂⟩ := h3 k₂.1 k₂.2
    have u₁ : κ₁ ∈ Umax L n := GlobalTheory.InertUmax.mem_Umax_of_trivOutside_of_loc_integral L n v w Dv κ₁ t₁
      (fun i j => by rw [e₁]; exact GlobalTheory.SatInd.CosetFin.entries_int hk₁ i j)
    have u₂ : κ₂ ∈ Umax L n := GlobalTheory.InertUmax.mem_Umax_of_trivOutside_of_loc_integral L n v w Dv κ₂ t₂
      (fun i j => by rw [e₂]; exact GlobalTheory.SatInd.CosetFin.entries_int hk₂ i j)
    refine ⟨κ₁, ⟨u₁, t₁⟩, κ₂, ⟨u₂, t₂⟩, h4 _ _ hx
      (GlobalTheory.SatInd.CosetFin.trivOutside_mul (GlobalTheory.SatInd.CosetFin.trivOutside_mul t₁ ha) t₂) ?_⟩
    calc Dv.loc x = k₁.1 * Dv.loc a * k₂.1 := congrArg Subtype.val e
      _ = Dv.loc κ₁ * Dv.loc a * Dv.loc κ₂ := by rw [e₁, e₂]
      _ = Dv.loc (κ₁ * a * κ₂) := by rw [loc_mul, loc_mul]
  · rintro ⟨k₁, hk₁, k₂, hk₂, rfl⟩
    refine ⟨⟨Dv.loc k₁, h1 k₁⟩, h2 k₁ hk₁.1 (h1 k₁), ⟨Dv.loc k₂, h1 k₂⟩,
      h2 k₂ hk₂.1 (h1 k₂), ?_⟩
    apply Subtype.ext
    show Dv.loc (k₁ * a * k₂) = Dv.loc k₁ * Dv.loc a * Dv.loc k₂
    rw [loc_mul, loc_mul]

end GlobalTheory.InertDCOp

namespace GlobalTheory.InertDCOp

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
  {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)}

theorem exists_reps (Dv : InertDatum L n v w) (h1 : ∀ x : GAf L n, Dv.loc x ∈ Formalism.UG.GU Dv.σw n)
    (h2 : ∀ κ : GAf L n, κ ∈ Umax L n → ∀ hκ : Dv.loc κ ∈ Formalism.UG.GU Dv.σw n,
      (⟨Dv.loc κ, hκ⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n)
    {a : GAf L n} (ha : TrivOutside {v} a) :
    ∃ R : Finset (GAf L n), GlobalTheory.SphLabelOps.Reps (InertSph.Kv L n v) a R := by
  classical
  set K := InertSph.Kv L n v
  let p : GAf L n → Prop := fun x => ∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * a * k₂
  have tp : ∀ x, p x → TrivOutside {v} x := by
    rintro _ ⟨k₁, hk₁, k₂, hk₂, rfl⟩
    exact GlobalTheory.SatInd.CosetFin.trivOutside_mul (GlobalTheory.SatInd.CosetFin.trivOutside_mul hk₁.2 ha) hk₂.2
  have hfin : Set.Finite {c : GAf L n ⧸ K | ∃ x : GAf L n, (x : GAf L n ⧸ K) = c ∧ p x} := by
    refine GlobalTheory.SatInd.CosetFin.finite_cosets (GlobalTheory.SatInd.CosetFin.locHom Dv) (Formalism.UG.GU Dv.σw n)
      (Formalism.UG.KU Dv.σw n) K p _
      (GlobalTheory.SatInd.DCoset.finite_dcoset Dv.ϖ Dv.σw _ n Dv.unram ⟨Dv.loc a, h1 a⟩) ?_ ?_
    · rintro x ⟨k₁, hk₁, k₂, hk₂, rfl⟩
      refine ⟨h1 _, ⟨Dv.loc k₁, h1 k₁⟩, h2 k₁ hk₁.1 (h1 k₁), ?_⟩
      have e : (⟨GlobalTheory.SatInd.CosetFin.locHom Dv (k₁ * a * k₂), h1 _⟩ : Formalism.UG.GU Dv.σw n) =
          (⟨Dv.loc k₁, h1 k₁⟩ * ⟨Dv.loc a, h1 a⟩ : Formalism.UG.GU Dv.σw n) * ⟨Dv.loc k₂, h1 k₂⟩ := by
        apply Subtype.ext
        show Dv.loc (k₁ * a * k₂) = Dv.loc k₁ * Dv.loc a * Dv.loc k₂
        rw [loc_mul, loc_mul]
      rw [e]
      exact (QuotientGroup.mk_mul_of_mem _ (h2 k₂ hk₂.1 (h1 k₂))).symm
    · intro x y hx hy hz hk
      have ht : TrivOutside {v} (x⁻¹ * y) :=
        GlobalTheory.SatInd.CosetFin.trivOutside_mul (GlobalTheory.SatInd.CosetFin.trivOutside_inv (tp x hx)) (tp y hy)
      exact ⟨GlobalTheory.InertUmax.mem_Umax_of_trivOutside_of_loc_integral L n v w Dv _ ht
        (fun i j => GlobalTheory.SatInd.CosetFin.entries_int hk i j), ht⟩
  refine ⟨hfin.toFinset.image (fun c => c.out), ?_, ?_⟩
  · intro γ hγ
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hγ
    obtain ⟨x, hxc, k₁, hk₁, k₂, hk₂, rfl⟩ := (Set.Finite.mem_toFinset hfin).1 hc
    have hm : (k₁ * a * k₂)⁻¹ * c.out ∈ K := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq', hxc]
    exact ⟨k₁, hk₁, k₂ * ((k₁ * a * k₂)⁻¹ * c.out), mul_mem hk₂ hm, by group⟩
  · intro x hx
    have hc : (x : GAf L n ⧸ K) ∈ hfin.toFinset := (Set.Finite.mem_toFinset hfin).2 ⟨x, rfl, hx⟩
    refine ⟨(x : GAf L n ⧸ K).out, ⟨Finset.mem_image_of_mem _ hc, ?_⟩, ?_⟩
    · rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    · rintro γ ⟨hγ, hγx⟩
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hγ
      have : c = (x : GAf L n ⧸ K) := by
        rw [← QuotientGroup.out_eq' c]
        exact QuotientGroup.eq.2 hγx
      rw [this]

end GlobalTheory.InertDCOp

namespace GlobalTheory.InertDCOp

theorem dcOp_eq_heckeFunI : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w), (∀ x : GAf L n, Dv.loc x ∈ Formalism.UG.GU Dv.σw n) → (∀ κ : GAf L n, κ ∈ Umax L n → ∀ hκ : Dv.loc κ ∈ Formalism.UG.GU Dv.σw n, (⟨Dv.loc κ, hκ⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n) → (∀ k : GL (Fin n) (w.adicCompletion L), k ∈ Formalism.UG.GU Dv.σw n → ∃ x : GAf L n, TrivOutside {v} x ∧ Dv.loc x = k) → (∀ x y : GAf L n, TrivOutside {v} x → TrivOutside {v} y → Dv.loc x = Dv.loc y → x = y) → ∀ a : GAf L n, TrivOutside {v} a → ∃ (R : Finset (GAf L n)) (ha : Formalism.UG.GU Dv.σw n → ℂ), GlobalTheory.SphLabelOps.Reps (GlobalTheory.InertSph.Kv L n v) a R ∧ ha ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n) ∧ ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (φ : GAf L n → W), (∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ φ = φ) → ∑ γ ∈ R, NG.rt L n γ φ = heckeFunI L n (Umax L n) Dv ha φ := by
  intro L _ _ _ n v w Dv h1 h2 h3 h4 a ha
  classical
  set K := InertSph.Kv L n v
  obtain ⟨R, hR⟩ := exists_reps Dv h1 h2 ha
  have tR : ∀ γ ∈ R, TrivOutside {v} γ := by
    intro γ hγ
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := hR.1 γ hγ
    exact GlobalTheory.SatInd.CosetFin.trivOutside_mul (GlobalTheory.SatInd.CosetFin.trivOutside_mul hk₁.2 ha) hk₂.2
  refine ⟨R, Formalism.UG.dosetInd ℂ (Formalism.UG.KU Dv.σw n) ⟨Dv.loc a, h1 a⟩, hR,
    Formalism.UG.P.double_coset_indicator_mem _ _ _ _, fun W _ _ φ hφ => ?_⟩

  have hv1 : ∀ x : GAf L n, TrivOutside {v} x → (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * a * k₂) →
      Dv.hval (Formalism.UG.dosetInd ℂ (Formalism.UG.KU Dv.σw n) ⟨Dv.loc a, h1 a⟩) (Dv.loc x) = 1 := by
    intro x hx hp
    unfold Formalism.AUTREP.InertDatum.hval
    rw [dif_pos (h1 x)]
    exact Formalism.UG.P.dosetInd_of_mem ℂ _ _ _ ((mem_dc_iff Dv h1 h2 h3 h4 ha hx).2 hp)
  have hv0 : ∀ x : GAf L n, TrivOutside {v} x →
      Dv.hval (Formalism.UG.dosetInd ℂ (Formalism.UG.KU Dv.σw n) ⟨Dv.loc a, h1 a⟩) (Dv.loc x) ≠ 0 →
      ∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * a * k₂ := by
    intro x hx h0
    unfold Formalism.AUTREP.InertDatum.hval at h0
    rw [dif_pos (h1 x)] at h0
    refine (mem_dc_iff Dv h1 h2 h3 h4 ha hx).1 ?_
    by_contra hn
    exact h0 (Formalism.UG.P.dosetInd_of_not_mem ℂ _ _ _ hn)
  funext g
  rw [Finset.sum_apply]
  unfold heckeFunI
  rw [finsum_eq_sum_of_support_subset (s := R.image (QuotientGroup.mk : GAf L n → GAf L n ⧸ Umax L n))]
  · rw [Finset.sum_image]
    · refine Finset.sum_congr rfl fun γ hγ => ?_
      have hc : ∃ x : GAf L n, (x : GAf L n ⧸ Umax L n) = (γ : GAf L n ⧸ Umax L n) ∧ TrivOutside {v} x :=
        ⟨γ, rfl, tR γ hγ⟩
      rw [dif_pos hc]
      obtain ⟨e, hxt⟩ := hc.choose_spec
      have hU : γ⁻¹ * hc.choose ∈ Umax L n := QuotientGroup.eq.1 e.symm
      have hT : TrivOutside {v} (γ⁻¹ * hc.choose) :=
        GlobalTheory.SatInd.CosetFin.trivOutside_mul (GlobalTheory.SatInd.CosetFin.trivOutside_inv (tR γ hγ)) hxt
      have hp : ∃ k₁ ∈ K, ∃ k₂ ∈ K, hc.choose = k₁ * a * k₂ := by
        obtain ⟨k₁, hk₁, k₂, hk₂, e'⟩ := hR.1 γ hγ
        exact ⟨k₁, hk₁, k₂ * (γ⁻¹ * hc.choose), mul_mem hk₂ ⟨hU, hT⟩, by rw [← mul_assoc, ← e']; group⟩
      rw [hv1 _ hxt hp, one_smul]
      have := congrFun (hφ _ hU hT) (g * γ)
      show φ (g * γ) = φ (g * hc.choose)
      rw [← this]
      show φ (g * γ * (γ⁻¹ * hc.choose)) = φ (g * hc.choose)
      group
    · intro γ hγ γ' hγ' e
      have hU : γ⁻¹ * γ' ∈ Umax L n := QuotientGroup.eq.1 e
      have hT : TrivOutside {v} (γ⁻¹ * γ') :=
        GlobalTheory.SatInd.CosetFin.trivOutside_mul (GlobalTheory.SatInd.CosetFin.trivOutside_inv (tR γ hγ)) (tR γ' hγ')
      exact (hR.2 γ' (hR.1 γ' hγ')).unique ⟨hγ, hU, hT⟩ ⟨hγ', by rw [inv_mul_cancel]; exact one_mem _⟩
  · intro c hc0
    rw [Function.mem_support] at hc0
    by_cases hc : ∃ x : GAf L n, (x : GAf L n ⧸ Umax L n) = c ∧ TrivOutside {v} x
    · rw [dif_pos hc] at hc0
      obtain ⟨e, hxt⟩ := hc.choose_spec
      have h0 : Dv.hval (Formalism.UG.dosetInd ℂ (Formalism.UG.KU Dv.σw n) ⟨Dv.loc a, h1 a⟩) (Dv.loc hc.choose) ≠ 0 := by
        intro h0; rw [h0, zero_smul] at hc0; exact hc0 rfl
      obtain ⟨γ, ⟨hγ, hγx⟩, -⟩ := hR.2 _ (hv0 _ hxt h0)
      rw [Finset.coe_image]
      refine ⟨γ, hγ, ?_⟩
      show (γ : GAf L n ⧸ Umax L n) = c
      rw [← e]
      exact QuotientGroup.eq.2 hγx.1
    · exact absurd (dif_neg hc) hc0

end GlobalTheory.InertDCOp
