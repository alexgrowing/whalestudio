import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryRowPairRelationStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistQuadraticLevelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistQuadraticValueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryRowPairPropertyStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam

theorem comb_smul_coef {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (κ : ℂ) (d : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T (κ • d) f = κ • comb ψ S T d f := by
  by_cases hκ : κ = 0
  · subst hκ; simp [comb]
  · unfold comb
    rw [Finsupp.support_smul_eq hκ, Finset.smul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finsupp.smul_apply, smul_eq_mul, mul_smul]

theorem isRatDatum_const_mul {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {e : AE D}
    {Ξ : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ} {f₀ f : WO S T → ℂ} (h : IsRatDatum ψ S T e Ξ f₀ f) (κ : ℂ) :
    IsRatDatum ψ S T e (fun z => κ * Ξ z) f₀ (κ • f) := by
  obtain ⟨Φ, hSB, hval, hth⟩ := h
  refine ⟨κ • Φ, ?_, fun γ => by simp [hval γ], ?_⟩
  · obtain ⟨hs, k, hk, hinv, hsupp⟩ := hSB
    refine ⟨fun t ht => hs t fun h0 => ht (by simp [h0]), k, hk, fun v hv hv' t => by simp [hinv v hv hv' t],
      fun t ht => hsupp t fun h0 => ht (by simp [h0])⟩
  · unfold IsThetaAt AllSome at hth ⊢
    refine ⟨hth.1, fun T hT => ?_⟩
    have h := hth.2 T hT
    simp only at h ⊢
    rw [h, map_smul]

def chartRescale {Ch : ℕ → Type} (m : ℕ) (cc : ℕ → ℂ) (b : ∀ j, Ch (j + 1) → ℂ) : ∀ j, Ch j → ℂ
  | 0 => fun _ => 1
  | j + 1 => fun γ => if j < m then cc j * b j γ else 1

theorem datRoot_ne_zero {x : ℂ} (h : ∃ n : ℕ, 0 < n ∧ x ^ n = 1) : x ≠ 0 := by
  obtain ⟨n, hn, hx⟩ := h
  rintro rfl
  simp [zero_pow hn.ne'] at hx

theorem datRoot_mul {x y : ℂ} (hx : ∃ n : ℕ, 0 < n ∧ x ^ n = 1) (hy : ∃ n : ℕ, 0 < n ∧ y ^ n = 1) :
    ∃ n : ℕ, 0 < n ∧ (x * y) ^ n = 1 := by
  obtain ⟨a, ha, hxa⟩ := hx
  obtain ⟨b, hb, hyb⟩ := hy
  refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
  rw [mul_pow, pow_mul, hxa, one_pow, mul_comm a b, pow_mul, hyb, one_pow, one_mul]

theorem datRoot_prod {ι : Type*} (s : Finset ι) (x : ι → ℂ) (h : ∀ i ∈ s, ∃ n : ℕ, 0 < n ∧ x i ^ n = 1) :
    ∃ n : ℕ, 0 < n ∧ (∏ i ∈ s, x i) ^ n = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact datRoot_mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem QJ.dat_exists : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → (∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) → ∃ C : ℕ → ℂ, (∀ j, j < B.R.m → C j ≠ 0) ∧ ∀ t (J : QJ a t), J.Reads → ∃ s ζ ρ, J.Dat C s ζ ρ := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr hoT
  obtain ⟨C, hC0, hC⟩ := GlobalTheory.T.true_geometry_row_pair_relation W hW u a ha hTr hoT
  refine ⟨C, hC0, fun t J hR => ?_⟩
  obtain ⟨e₀, he₀, hAe⟩ := GlobalTheory.T.true_geometry_twist_quadratic_level W hW u a ha hTr t J hR
  obtain ⟨p, q, hA, hB, ⟨c0, hc0, h0⟩, hstep, hD⟩ := GlobalTheory.T.true_geometry_row_pair_property W hW u a ha hTr hoT t J hR

  set Af : ∀ j, J.Ch j → ℂ := fun j α => p j α * (J.A.chr (j + 1) (J.A.xr j (J.ι j α)) : ℂ) with hAf
  set Bf : ∀ j, J.Ch (j + 1) → ℂ := fun j γ => q j γ * ((J.A.chr (j + 1) (J.A.xr (j + 1) (J.ι (j + 1) γ)) : ℂ))⁻¹ with hBf
  let k : ℕ → ℂ := fun j => if h : j + 1 < B.R.m then (hstep j h).choose else 1
  have hk : ∀ j, ∃ n : ℕ, 0 < n ∧ k j ^ n = 1 := fun j => by
    by_cases h : j + 1 < B.R.m
    · simp only [k, dif_pos h]; exact (hstep j h).choose_spec.1
    · simp only [k, dif_neg h]; exact ⟨1, one_pos, by simp⟩
  let cc : ℕ → ℂ := fun j => c0 * ∏ i ∈ Finset.range j, k i
  have hcc : ∀ j, ∃ n : ℕ, 0 < n ∧ cc j ^ n = 1 := fun j =>
    datRoot_mul hc0 (datRoot_prod _ _ fun i _ => hk i)
  let s : ∀ j, J.Ch j → ℂ := chartRescale B.R.m cc Bf
  have hs0 : ∀ α, s 0 α = 1 := fun _ => rfl
  have hsS : ∀ j γ, j < B.R.m → s (j + 1) γ = cc j * Bf j γ := fun j γ h => by
    show (if j < B.R.m then cc j * Bf j γ else 1) = _
    rw [if_pos h]
  have hsA : ∀ j, j < B.R.m → ∀ α, s j α * Af j α = cc j := by
    intro j
    induction j with
    | zero => intro _ α; rw [hs0, one_mul]; simp [cc, Af, h0 α]
    | succ j ih =>
      intro hj γ
      rw [hsS j γ (by omega)]
      have hk' : k j = (hstep j hj).choose := by simp only [k, dif_pos hj]
      have := (hstep j hj).choose_spec.2 γ
      calc cc j * Bf j γ * Af (j + 1) γ = cc j * (Bf j γ * Af (j + 1) γ) := by ring
        _ = cc j * k j := by rw [hk', ← this]
        _ = cc (j + 1) := by simp only [cc, Finset.prod_range_succ]; ring
  have hsroot : ∀ j α, ∃ n : ℕ, 0 < n ∧ s j α ^ n = 1 := by
    intro j
    cases j with
    | zero => intro α; exact ⟨1, one_pos, by rw [hs0, one_pow]⟩
    | succ j =>
      intro γ
      by_cases h : j < B.R.m
      · rw [hsS j γ h]; exact datRoot_mul (hcc j) (hB j h γ)
      · refine ⟨1, one_pos, ?_⟩
        show (if j < B.R.m then cc j * Bf j γ else 1) ^ 1 = 1
        rw [if_neg h, one_pow]
  refine ⟨s, fun j α γ => s j α * (s (j + 1) γ)⁻¹ * (p j α * q j γ), fun _ => 1, hsroot, hs0,
    fun _ => ⟨1, one_pos, one_pow 1⟩, fun j hj α γ => ⟨?_, ?_⟩⟩
  · have h1 := hD e₀ he₀ j hj α γ _ _ (hC t J hR e₀ he₀ j hj α γ)
    have h2 := isRatDatum_const_mul h1 (s j α * (s (j + 1) γ)⁻¹ * J.wt j α)
    rw [← hAe] at h2
    have hdQ : J.dQ s j α γ = (s j α * (s (j + 1) γ)⁻¹ * J.wt j α) • aconv (List.ofFn fun i => (J.E i).dL j (α i) (γ i)) := by
      simp only [QJ.dQ, smul_smul]
    rw [hdQ, comb_smul_coef]
    convert h2 using 2
    rename_i z
    beta_reduce
    rw [GlobalTheory.T.true_geometry_twist_quadratic_value W hW u a ha hTr t J hR j hj α γ z]
    ring
  · have hjm : j < B.R.m := by omega
    have hSA := hsA j hjm α
    have hBn : Bf j γ ≠ 0 := datRoot_ne_zero (hB j hjm γ)
    have hcn : cc j ≠ 0 := datRoot_ne_zero (hcc j)
    beta_reduce
    rw [hsS j γ hjm]
    have hx : ((J.A.chr (j + 1) (J.A.xr (j + 1) (J.ι (j + 1) γ)) : ℂ)) ≠ 0 := by
      exact Circle.coe_ne_zero _
    calc s j α * (cc j * Bf j γ)⁻¹ * (p j α * q j γ) * (J.A.chr (j + 1) (J.A.xr j (J.ι j α)) : ℂ) *
          ((J.A.chr (j + 1) (J.A.xr (j + 1) (J.ι (j + 1) γ)) : ℂ))⁻¹
        = (s j α * Af j α) * Bf j γ * (cc j * Bf j γ)⁻¹ := by simp only [hAf, hBf]; ring
      _ = 1 := by rw [hSA]; exact mul_inv_cancel₀ (mul_ne_zero hcn hBn)

end GlobalTheory.Fam

end
