import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.ResidualAutomorphyOfLinkedEnds
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.SideGLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.SideGTerm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.SideGTau
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.SideGSupp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.FinG
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.ThetaThetaAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.NormPosPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.ClassG
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.MapStarMulVec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.CharpolyThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.PosLaw
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.ModelFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.BasePt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.FinSupp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.DatSmul

namespace UpperTheory.V.Z.Sym.Glob

open NumberField Loc

private theorem sum_sub {α : Type} (p : α → Prop) (f : α → ℂ) :
    ∑ᶠ i : {a // p a}, f i.1 = ∑ᶠ a, one (p a) * f a := by
  rw [show (∑ᶠ i : {a // p a}, f i.1) = ∑ᶠ a ∈ {a | p a}, f a from
    finsum_set_coe_eq_finsum_mem (f := f) {a | p a}, finsum_mem_def]
  congr 1
  ext a
  by_cases h : p a <;> simp [one, Set.indicator, h]

private theorem const_sum {α : Type} (c : ℂ) (f : α → ℂ) : ∑ᶠ i, c * f i = c * ∑ᶠ i, f i := by
  exact (mul_finsum f c).symm

variable {F : Type} [Field F] [NumberField F] {Δ : F} (D : Dat Δ)

private theorem aux_statement_10 (hD : D.Ok) (t : Dat.Par F) (ht : D.Cone t) (τ : F) (h : D.admitted t τ) : τ ^ 2 - 4 ≠ 0 := by
  intro h0
  obtain ⟨v, hv⟩ := hD.ne
  refine ((hD.sig v hv).reg (t v) (ht v hv) _ (h v hv)).2 ?_
  have h2 : IsIntegral (Ov v) (2 : Kv v) := by
    have := isIntegral_algebraMap (R := Ov v) (A := Kv v) (x := 2)
    rwa [map_ofNat] at this
  have h1 : (τ - 2) * (τ + 2) = 0 := by rw [← h0]; ring
  rcases mul_eq_zero.mp h1 with h1 | h1
  · rw [sub_eq_zero.mp h1, map_ofNat]; exact h2
  · rw [eq_neg_of_add_eq_zero_left h1, map_neg, map_ofNat]; exact h2.neg

private theorem delta_ne (hD : D.Ok) : Δ ≠ 0 := by
  intro h0
  haveI := hD.real
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hw : w.IsReal := IsTotallyReal.isReal w
  have := hD.neg (InfinitePlace.embedding_of_isReal hw)
  rw [h0, map_zero] at this
  exact lt_irrefl _ this

private def GI (t : Dat.Par F) (τ : F) : Prop := D.Good t τ ∧ ∀ v ∉ D.Sg, cv v τ ∈ (algebraMap (Ov v) (Kv v)).range

private theorem sum_GI (hD : D.Ok) (t : Dat.Par F) (ht : D.Cone t) (ch : F → ℂ) (e : ℂ) :
    ∑ᶠ τ : {τ // GI D t τ}, ch τ.1 * ms τ.1 * (D.nS τ.1 + e * D.nK τ.1) = D.sumS ch t + e * D.sumK ch t := by
  have key : ∀ (h : F → ℂ) (τ : F),
      (D.Good t τ → ¬ (∀ v ∉ D.Sg, (cv v) τ ∈ (algebraMap (Ov v) (Kv v)).range) → h τ = 0) →
      one (D.Good t τ) * h τ = one (GI D t τ) * h τ := by
    intro h τ hh
    by_cases hg : D.Good t τ
    · by_cases hi : ∀ v ∉ D.Sg, (cv v) τ ∈ (algebraMap (Ov v) (Kv v)).range
      · have hG : GI D t τ := ⟨hg, hi⟩
        simp only [one, if_pos hg, if_pos hG]
      · rw [hh hg hi, mul_zero, mul_zero]
    · have hG : ¬ GI D t τ := fun h' => hg h'.1
      simp only [one, if_neg hg, if_neg hG]
  have van : ∀ τ, D.Good t τ → ¬ (∀ v ∉ D.Sg, (cv v) τ ∈ (algebraMap (Ov v) (Kv v)).range) →
      D.nS τ = 0 ∧ D.nK τ = 0 := fun τ hg hi => sg_vanish D hD (aux_statement_10 D hD t ht τ hg.2) hi
  have kS : ∀ τ, one (D.Good t τ) * (ch τ * ms τ * D.nS τ) = one (GI D t τ) * (ch τ * ms τ * D.nS τ) :=
    fun τ => key (fun τ => ch τ * ms τ * D.nS τ) τ (fun hg hi => by
      show ch τ * ms τ * D.nS τ = 0
      rw [(van τ hg hi).1, mul_zero])
  have kK : ∀ τ, one (D.Good t τ) * (ch τ * ms τ * D.nK τ) = one (GI D t τ) * (ch τ * ms τ * D.nK τ) :=
    fun τ => key (fun τ => ch τ * ms τ * D.nK τ) τ (fun hg hi => by
      show ch τ * ms τ * D.nK τ = 0
      rw [(van τ hg hi).2, mul_zero])
  have hfin := finSupp F Δ D hD t ht
  have sup : ∀ h : F → ℂ, (Function.support fun τ => one (GI D t τ) * h τ).Finite := fun h =>
    hfin.subset (fun τ hτ => by
      by_contra hn
      exact hτ (by simp only [one, if_neg (show ¬ GI D t τ from hn), zero_mul]))
  have sup' : ∀ h : F → ℂ, (Function.support fun τ => e * (one (GI D t τ) * h τ)).Finite := fun h =>
    hfin.subset (fun τ hτ => by
      by_contra hn
      exact hτ (by simp only [one, if_neg (show ¬ GI D t τ from hn), zero_mul, mul_zero]))
  rw [sum_sub (GI D t) (fun τ => ch τ * ms τ * (D.nS τ + e * D.nK τ))]
  simp only [Dat.sumS, Dat.sumK]
  rw [finsum_congr kS, finsum_congr kK, ← const_sum, ← finsum_add_distrib (sup _) (sup' _)]
  exact finsum_congr (fun τ => by ring)

set_option maxHeartbeats 800000 in
private theorem term_eq (hD : D.Ok) {V : Type} [AddCommGroup V] [Module ℂ V] {ch : F → ℂ} {B : Base (U3 Δ) (GA Δ) V} {s : B.Tw}
    (hB : D.IsBG ch B s) {t : Dat.Par F} (ht : D.Cone t) {τ c : F} {d m : EL Δ τ} {δ i P} (hτ : D.Good t τ) (hd : IsDat c d m)
    (h : Models c d m δ i P) :
    s.term (D.FG t) δ = (1 / 2 * ∏ v ∈ D.Sg, ((D.S v).cG : ℂ)) * (ch τ * ms τ * D.nL c d m) := by
  obtain ⟨h1, h2, h3, h4⟩ := modelFacts F Δ τ c d m δ i P (delta_ne D hD) hd h
  obtain ⟨hF, hT⟩ := finG F Δ D hD V ch B s hB
  have a := sideGTerm _ _ V _ B hF s (D.FG t) (hT t ht) hB.ω hB.Γ₀ δ (negU Δ) i h3
    (fun x => by rw [hB.θΓ]; exact h4 x) D.UG (scalE τ) hB.U h2
  have b := gqG F Δ D hD B.ι hB.ι s.θ.toMonoidHom hB.θ t ht τ c d m δ i P hτ.1 hd h
  have o : one (D.admitted t τ) = 1 := if_pos hτ.2
  have a' := a.trans (congrArg₂ (fun x y : ℂ => x * y) (hB.tr δ τ h1) b)
  simp only [o] at a'
  linear_combination (1 / 2 : ℂ) * a'

private theorem weight_eq (hD : D.Ok) {τ : F} {d m : EL Δ τ} (hd : IsDat 1 d m) (hp : PosF 1 m)
    (c : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) (u : Fˣ) (A : ℂ) :
    one (∃ δ ι P, Models (c.out : F) d ((u : F) • m) δ ι P) * (A * D.nL (c.out : F) d ((u : F) • m)) =
      A * (one (c ∈ D.Sel (2 - τ)) * (one (TPos (u : F)) * D.nL (c.out : F) d ((u : F) • m))) := by
  have hd' : IsDat (c.out : F) d ((u : F) • m) := by
    have h1 := datSmul F Δ τ 1 d m hd u
    exact ⟨h1.reg, Units.ne_zero _, h1.d_norm, h1.m_unit, h1.m_star, h1.m_sig⟩
  by_cases hn : D.nL (c.out : F) d ((u : F) • m) = 0
  · rw [hn]
    simp
  · have hev := sg_ev D hD hd' hn
    by_cases hm : ∃ δ ι P, Models (c.out : F) d ((u : F) • m) δ ι P
    · obtain ⟨δ, ι, P, hM⟩ := hm
      have hq := (posLaw F Δ D hD τ d m hp (c.out : F) (u : F)).2 δ ι P hM
      have hS : c ∈ D.Sel (2 - τ) := ⟨hq.1, hev⟩
      simp only [one, if_pos (show ∃ δ ι P, Models (c.out : F) d ((u : F) • m) δ ι P from ⟨δ, ι, P, hM⟩),
        if_pos hS, if_pos hq.2]
      ring
    · have hno : ¬ (c ∈ D.Sel (2 - τ) ∧ TPos (u : F)) := by
        rintro ⟨hS, hu⟩
        exact hm (exG F Δ D hD τ (c.out : F) d _ hd'
          ((posLaw F Δ D hD τ d m hp (c.out : F) (u : F)).1 hS.1 hu) hev)
      by_cases hS : c ∈ D.Sel (2 - τ)
      · have hu : ¬ TPos (u : F) := fun hu => hno ⟨hS, hu⟩
        simp only [one, if_neg hm, if_pos hS, if_neg hu]
        ring
      · simp only [one, if_neg hm, if_neg hS]
        ring

private theorem cls_eq {K : Type} [Field K] {τ : K} {x y : (Kˣ ⧸ (powMonoidHom 2 : Kˣ →* Kˣ).range) × (Kˣ ⧸ NE τ)}
    (h : IsSquare (y.1.out / x.1.out) ∧ y.2.out / x.2.out ∈ NE τ) : x = y := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  simp only at h1 h2
  rw [Prod.mk.injEq]
  constructor
  · rw [← QuotientGroup.out_eq' x1, ← QuotientGroup.out_eq' y1, QuotientGroup.eq]
    obtain ⟨r, hr⟩ := h1
    exact ⟨r, by rw [powMonoidHom_apply, pow_two, ← hr, div_eq_inv_mul]⟩
  · rw [← QuotientGroup.out_eq' x2, ← QuotientGroup.out_eq' y2, QuotientGroup.eq, ← div_eq_inv_mul]
    exact h2

set_option maxHeartbeats 1600000 in
theorem sideG : SideG := by
  intro F _ _ Δ D hD
  obtain ⟨e, he⟩ := basePt F Δ D hD
  obtain ⟨hS1f, hS1n, -⟩ := selCard F Δ D hD
  have hΔ := delta_ne D hD
  have hp : 0 < ∏ v ∈ D.Sg, (D.S v).cG := Finset.prod_pos (fun v hv => (hD.sig v hv).cG)
  have hn : 0 < (D.Sel 1).ncard := (Set.ncard_pos hS1f).mpr hS1n
  refine ⟨(∏ v ∈ D.Sg, (D.S v).cG) * (D.Sel 1).ncard / 4, e,
    div_pos (mul_pos hp (Nat.cast_pos.mpr hn)) (by norm_num), ?_⟩
  intro V _ _ _ ch B s hB t ht
  obtain ⟨hFin, hTest⟩ := finG F Δ D hD V ch B s hB
  have spl : ∀ τ : {τ // GI D t τ}, D.Spl τ.1 := fun τ v hv =>
    ((hD.sig v hv).reg (t v) (ht v hv) (cv v τ.1) (τ.2.1.2 v hv)).1
  have bp : ∀ τ : {τ // GI D t τ}, ∃ d m : EL Δ τ.1, IsDat 1 d m ∧ PosF 1 m ∧
      ∀ (c : F), TPos c → D.Ev (c * (2 - τ.1)) →
        ∏ᶠ (v : Pl F) (_ : v ∉ D.Sg), kapSum (Ov v) ((cv v) c) (elmap (cv v) d) (elmap (cv v) m) =
          (e : ℂ) * D.nK τ.1 :=
    fun τ => he τ.1 τ.2.1.1 (spl τ) τ.2.2
  choose d m hdm using bp
  have hex : ∀ (τ : {τ // GI D t τ})
      (x : {x : (Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) × (Fˣ ⧸ NE τ.1) //
        ∃ δ ι P, Models (x.1.out : F) (d τ) ((x.2.out : F) • m τ) δ ι P}),
      ∃ δ ι P, Models (x.1.1.out : F) (d τ) ((x.1.2.out : F) • m τ) δ ι P := fun τ x => x.2
  choose δf ιf Pf hM using hex
  have isD : ∀ (τ : {τ // GI D t τ}) (c u : Fˣ), IsDat (c : F) (d τ) ((u : F) • m τ) := by
    intro τ c u
    have h1 := datSmul F Δ τ.1 1 (d τ) (m τ) (hdm τ).1 u
    exact ⟨h1.reg, Units.ne_zero _, h1.d_norm, h1.m_unit, h1.m_star, h1.m_sig⟩
  have inj : ∀ i j : (Σ τ : {τ // GI D t τ}, {x : (Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) × (Fˣ ⧸ NE τ.1) //
        ∃ δ ι P, Models (x.1.out : F) (d τ) ((x.2.out : F) • m τ) δ ι P}),
      s.Rel (δf i.1 i.2) (δf j.1 j.2) → i = j := by
    rintro ⟨τ, x⟩ ⟨τ', x'⟩ ⟨g, z, hz, hrel⟩
    rw [hB.Γ₀, Subgroup.mem_bot] at hz
    subst hz
    rw [mul_one, hB.θΓ] at hrel
    have h1 := (modelFacts F Δ τ.1 _ _ _ _ _ _ hΔ (isD τ _ _) (hM τ x)).1
    have h2 := (modelFacts F Δ τ'.1 _ _ _ _ _ _ hΔ (isD τ' _ _) (hM τ' x')).1
    have heq : τ.1 = τ'.1 := sideGTau.2.1 F Δ (δf τ' x') τ.1 τ'.1
      (by rw [hrel]; exact sideGTau.1 F Δ _ g τ.1 h1) h2
    obtain ⟨τ, hτ⟩ := τ
    obtain ⟨τ', hτ'⟩ := τ'
    simp only at heq
    subst heq
    have hc := (conjG F Δ τ (d ⟨τ, hτ⟩) (m ⟨τ, hτ⟩) hΔ (hdm ⟨τ, hτ⟩).1 x.1.1.out x'.1.1.out x.1.2.out x'.1.2.out
      _ _ _ _ _ _ (hM ⟨τ, hτ⟩ x) (hM ⟨τ, hτ'⟩ x')).mp ⟨g, hrel⟩
    exact Sigma.ext rfl (heq_of_eq (Subtype.ext (cls_eq hc)))
  have surj : ∀ γ : U3 Δ, (∃ y, s.ker (D.FG t) γ y ≠ 0) →
      ∃ i : (Σ τ : {τ // GI D t τ}, {x : (Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) × (Fˣ ⧸ NE τ.1) //
        ∃ δ ι P, Models (x.1.out : F) (d τ) ((x.2.out : F) • m τ) δ ι P}), s.Rel (δf i.1 i.2) γ := by
    rintro γ ⟨y, hy⟩
    obtain ⟨τ, hγτ, hcm⟩ := tauEx F Δ D hD γ
    have hsupp := sideGSupp F Δ D hD B.ι hB.ι s.θ.toMonoidHom hB.θ t ht γ τ y.out hγτ hy
    have hG : GI D t τ := ⟨⟨hcm (aux_statement_10 D hD t ht τ hsupp.1), hsupp.1⟩, hsupp.2⟩
    obtain ⟨c, u, ι, P, hMod⟩ := classG F Δ τ (d ⟨τ, hG⟩) (m ⟨τ, hG⟩) hΔ (hdm ⟨τ, hG⟩).1 γ hγτ
    obtain ⟨x, P', hx⟩ := sg_out hMod
    refine ⟨⟨⟨τ, hG⟩, ⟨x, γ, ι, P', hx⟩⟩, ?_⟩
    obtain ⟨g, hg⟩ := (conjG F Δ τ (d ⟨τ, hG⟩) (m ⟨τ, hG⟩) hΔ (hdm ⟨τ, hG⟩).1 x.1.out x.1.out x.2.out x.2.out
      _ γ _ ι _ P' (hM ⟨τ, hG⟩ ⟨x, γ, ι, P', hx⟩) hx).mpr
      ⟨by rw [div_self']; exact ⟨1, (mul_one 1).symm⟩, by rw [div_self']; exact one_mem _⟩
    exact ⟨g, 1, by rw [hB.Γ₀]; exact one_mem _, by rw [mul_one, hB.θΓ]; exact hg⟩
  have htr := UpperTheory.V.Z.Sym.Tf.trace (U3 Δ) (GA Δ) V B hFin s (D.FG t) (hTest t ht)
    (Σ τ : {τ // GI D t τ}, {x : (Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) × (Fˣ ⧸ NE τ.1) //
        ∃ δ ι P, Models (x.1.out : F) (d τ) ((x.2.out : F) • m τ) δ ι P})
    (fun i => δf i.1 i.2) inj surj
  rw [htr.2]
  have indicator_eq_one_of_true : ∀ {p : Prop}, p → one p = 1 := fun h => if_pos h
  have hterm : ∀ i : (Σ τ : {τ // GI D t τ}, {x : (Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) × (Fˣ ⧸ NE τ.1) //
        ∃ δ ι P, Models (x.1.out : F) (d τ) ((x.2.out : F) • m τ) δ ι P}),
      s.term (D.FG t) (δf i.1 i.2) = (1 / 2 * ∏ v ∈ D.Sg, ((D.S v).cG : ℂ)) * (ch i.1.1 * ms i.1.1) *
        D.nL (i.2.1.1.out : F) (d i.1) ((i.2.1.2.out : F) • m i.1) := fun i => by
    rw [term_eq D hD hB ht i.1.2.1 (isD i.1 _ _) (hM i.1 i.2)]
    ring
  haveI : Finite {τ // GI D t τ} := (finSupp F Δ D hD t ht).to_subtype
  have hinner : ∀ τ : {τ // GI D t τ},
      (Function.support fun x : {x : (Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) × (Fˣ ⧸ NE τ.1) //
        ∃ δ ι P, Models (x.1.out : F) (d τ) ((x.2.out : F) • m τ) δ ι P} =>
          (1 / 2 * ∏ v ∈ D.Sg, ((D.S v).cG : ℂ)) * (ch τ.1 * ms τ.1) *
            D.nL (x.1.1.out : F) (d τ) ((x.1.2.out : F) • m τ)).Finite ∧
      ∑ᶠ x : {x : (Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) × (Fˣ ⧸ NE τ.1) //
        ∃ δ ι P, Models (x.1.out : F) (d τ) ((x.2.out : F) • m τ) δ ι P},
          (1 / 2 * ∏ v ∈ D.Sg, ((D.S v).cG : ℂ)) * (ch τ.1 * ms τ.1) *
            D.nL (x.1.1.out : F) (d τ) ((x.1.2.out : F) • m τ) =
        (((∏ v ∈ D.Sg, (D.S v).cG) * (D.Sel 1).ncard / 4 : ℝ) : ℂ) *
          (ch τ.1 * ms τ.1 * (D.nS τ.1 + (e : ℂ) * D.nK τ.1)) := by
    intro τ
    have hsg := sg_inner D hD τ.2.1.1 (spl τ) (hdm τ).1 (hdm τ).2.2
    constructor
    · refine (hsg.1.preimage Subtype.val_injective.injOn).subset (fun x hx => ?_)
      simp only [Set.mem_preimage, Function.mem_support] at hx ⊢
      intro h0
      apply hx
      have hw := weight_eq D hD (hdm τ).1 (hdm τ).2.1 x.1.1 x.1.2.out
        ((1 / 2 * ∏ v ∈ D.Sg, ((D.S v).cG : ℂ)) * (ch τ.1 * ms τ.1))
      rw [indicator_eq_one_of_true x.2, one_mul] at hw
      rw [hw, h0, mul_zero]
    · rw [sum_sub (fun (x : (Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) × (Fˣ ⧸ NE τ.1)) => ∃ δ ι P, Models (x.1.out : F) (d τ) ((x.2.out : F) • m τ) δ ι P)
        (fun (x : (Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) × (Fˣ ⧸ NE τ.1)) => (1 / 2 * ∏ v ∈ D.Sg, ((D.S v).cG : ℂ)) * (ch τ.1 * ms τ.1) *
          D.nL (x.1.out : F) (d τ) ((x.2.out : F) • m τ))]
      rw [finsum_congr (fun (x : (Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) × (Fˣ ⧸ NE τ.1)) => weight_eq D hD (hdm τ).1 (hdm τ).2.1 x.1 x.2.out
        ((1 / 2 * ∏ v ∈ D.Sg, ((D.S v).cG : ℂ)) * (ch τ.1 * ms τ.1))), const_sum, hsg.2]
      push_cast
      ring
  rw [finsum_congr hterm]
  rw [sg_sigma _ (fun τ => (hinner τ).1)]
  rw [finsum_congr (fun τ => (hinner τ).2), const_sum, sum_GI D hD t ht ch (e : ℂ)]

end UpperTheory.V.Z.Sym.Glob
