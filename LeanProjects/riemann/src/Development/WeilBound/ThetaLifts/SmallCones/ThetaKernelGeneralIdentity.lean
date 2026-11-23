import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq

set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem split2_unique {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} {W : Spc F E (a + a')} {d₁ : ℕ} {W₁ : Spc F E d₁} {H' : Plane E (a + a') d₁} {X : Chars F E}
    (hlt : a' < a)
    (hdom : ∃ (μ : Measure (unip σ W H')) (𝓕 : Set (unip σ W H')), μ.IsHaarMeasure ∧
      IsFundamentalDomain ((ratU σ W.J).subgroupOf (unip σ W H')) 𝓕 μ ∧ μ 𝓕 = 1)
    (hlevi : ∃ (t : (AE F E)ˣ) (m : UA σ W.J), IsLevi (W₁ := W₁) H' t 1 m ∧ 1 < (absE F E t : ℝ))
    {f fa fb fa' fb' : UA σ W.J → ℂ} (h₁ : Split2 W₁ H' X f fa fb) (h₂ : Split2 W₁ H' X f fa' fb') :
    fa = fa' ∧ fb = fb' := by
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := hdom
  obtain ⟨t, m, hm, ht⟩ := hlevi
  have hsum : ∀ h, fa h + fb h = fa' h + fb' h := by
    intro h
    have e1 := h₁.1 μ 𝓕 hμ h𝓕 h1 h
    have e2 := h₂.1 μ 𝓕 hμ h𝓕 h1 h
    simp only [Pi.add_apply] at e1 e2
    rw [e1, e2]
  have key : ∀ h, fa h = fa' h := by
    intro h
    by_contra hne
    have hA := h₁.2.1 t m hm h
    have hA' := h₂.2.1 t m hm h
    have hB := h₁.2.2 t m hm h
    have hB' := h₂.2.2 t m hm h
    have s1 := hsum (m * h)
    have s0 := hsum h
    set cA' : ℂ := (X.α t : ℂ) * (((absE F E t : ℝ) ^ ((a' : ℝ) / 2) : ℝ) : ℂ) with hcA
    set cB : ℂ := (X.β t : ℂ) * (((absE F E t : ℝ) ^ ((a : ℝ) / 2) : ℝ) : ℂ) with hcB
    have e : cA' * (fa h - fa' h) = cB * (fa h - fa' h) := by
      linear_combination -hA + hA' + s1 - hB + hB' - cB * s0
    have e' : cA' = cB := mul_right_cancel₀ (sub_ne_zero.2 hne) e
    have n1 : ‖cA'‖ = (absE F E t : ℝ) ^ ((a' : ℝ) / 2) := by
      rw [hcA, norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)]
    have n2 : ‖cB‖ = (absE F E t : ℝ) ^ ((a : ℝ) / 2) := by
      rw [hcB, norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)]
    have hlt' : (a' : ℝ) / 2 < (a : ℝ) / 2 := by
      have : (a' : ℝ) < a := by exact_mod_cast hlt
      linarith
    have := Real.rpow_lt_rpow_of_exponent_lt ht hlt'
    rw [← n1, ← n2, e'] at this
    exact lt_irrefl _ this
  refine ⟨funext key, funext fun h => ?_⟩
  have := hsum h
  rw [key h] at this
  exact add_left_cancel this

theorem IsPair.cast {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
    {r s r' s' a b a' b' : ℕ} (h : IsPair B M χX χW om r s r' s') (h1 : r = a) (h2 : s = b) (h3 : r' = a') (h4 : s' = b') :
    IsPair B M χX χW om a b a' b' := by subst h1 h2 h3 h4; exact h

def reM {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (Y : Spc F E n) : Model σ (reS X Y) W :=
  ⟨M.co, M.vac, M.μ, M.dom⟩

theorem reM_good {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ} (h : M.IsGood ψ) (Y : Spc F E n) :
    (reM M Y).IsGood ψ := ⟨h.rat, h.vac, h.std, h.haar, h.dom⟩

theorem reM_pair {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
    {r s r' s' : ℕ} (h : IsPair B M χX χW om r s r' s') {Y : Spc F E n} (hY : (reS X Y).IsHerm σ B r s) :
    IsPair B (reM M Y) χX χW om r s r' s' :=
  ⟨h.base, hY, h.skew, reM_good h.good Y, h.hX, h.hW, h.resX, h.resW, h.weil⟩

theorem reM_ev {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁} {B : Base F E} {M : Model σ X W} {M₁ : Model σ X W₁}
    {ι ι' I e} (h : IsEv B M M₁ ι ι' I e) (Y : Spc F E n) : IsEv B (reM M Y) (reM M₁ Y) ι ι' I e :=
  ⟨h.maps, h.Heisenberg₂, h.inv, h.loc⟩

theorem reM_so {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (Y : Spc F E n) (ψ) {v : Pl F} (t : E →ₐ[F] Fv F v) :
    (reM M Y).So ψ t = M.So ψ t := by
  have : (reM M Y).SoLoc ψ t = M.SoLoc ψ t := Set.ext fun φ =>
    ⟨fun ⟨h, ι, hι, r⟩ => ⟨h, ι, ⟨hι.bij, hι.trans, hι.mult⟩, r⟩, fun ⟨h, ι, hι, r⟩ => ⟨h, ι, ⟨hι.bij, hι.trans, hι.mult⟩, r⟩⟩
  unfold Model.So
  rw [this]
  rfl

theorem adapted_x_ne {n n₁ : ℕ} {B : Base F E} {H : Plane E n n₁} {Y : Spc F E n} {Y₁ : Spc F E n₁} {i₀ i₁ : ℕ}
    (h : H.IsAdapted σ B Y Y₁ i₀ i₁) : H.x ≠ 0 := by
  intro h0
  have := h.xy
  rw [h0] at this
  simp [form] at this

theorem res_low {χ : Chr F E} {n n₁ : ℕ} (h : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ n) (e : n = n₁ + 2) :
    ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ n₁ := by
  intro a
  rw [h a, e, pow_add]
  simp

theorem split_uniq (hU : UnipEx) {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om om'} (hT : IsTriple B G X om om')
    {d₁ : ℕ} {W₁ : Spc F E d₁} {H' : Plane E (a + a') d₁} {i₀ i₁ : ℕ} (hH : H'.IsAdapted σ B G.W W₁ i₀ i₁)
    {f fa fb fa' fb' : UA σ G.W.J → ℂ} (h₁ : Split2 W₁ H' X f fa fb) (h₂ : Split2 W₁ H' X f fa' fb') : fa = fa' ∧ fb = fb' := by
  obtain ⟨h1, -, -, -, ⟨lev, -, hl, -⟩, -, t, ht⟩ := hU F E σ B _ _ G.W W₁ H' i₀ i₁ _ _ hT.base (Or.inr hT.geo.hW) hH
  exact split2_unique hT.geo.lt h1 ⟨t, _, hl t 1, ht⟩ h₁ h₂

def AnySplit (cond : ℕ → ℕ → ℕ → ℕ → Prop) (so : Bool) : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d d₁ : ℕ)
    (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r s r' s' : ℕ) (M : Model σ X W) (M₁ : Model σ X W₁),
    3 ≤ n → cond n d r s → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ e₀, IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ →
    ∃ C₀ : ℂ, C₀ ≠ 0 ∧ ∀ χX χW om om₁, IsPair B M χX χW om r s (r' + 1) (s' + 1) → IsPair B M₁ χX χW om₁ r s r' s' →
      ∀ Φ ∈ PolData B M, (so = true → Φ ∈ M.So B.ψ B.τ₁) →
      ∃ A₀ A₁ : UA σ W.J → ℂ, IsCT H' (M.I om Φ) (A₀ + A₁) ∧ HasLaw W₁ H' χX ((n : ℝ) / 2) A₀ ∧
        HasLaw W₁ H' (χX / χW) (((d : ℝ) - n) / 2) A₁ ∧ ∀ h₁ p, IsLevi H' 1 h₁ p → ∀ h,
          (so = true → e₀ (om (1, h) Φ) ∈ M₁.So B.ψ B.τ₁) → A₀ (p * h) = C₀ * M₁.I om₁ (e₀ (om (1, h) Φ)) h₁

theorem theta_kernel_general_identity (hA : GenAniso) (hK : KFinData) (hS : StabEx) (hI : IwaEx) (hP : PairEx) (hPl : PlaneHerm) (hC : EvCone)
    (cond : ℕ → ℕ → ℕ → ℕ → Prop) (so : Bool)
    (gen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
      (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H : Plane E n n₁) (H' : Plane E d d₁)
      (j₀ j₁ i₀ i₁ r s r' s' : ℕ) (M : Model σ X W) (M₀ : Model σ X₁ W₁), H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
      ∀ (M₁ : Model σ X W₁) e₀ eA eB, M₁.IsGood B.ψ → M₀.IsGood B.ψ → IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ →
      IsEv B M M₀ H.ι H'.ι (isoA H H') eA → IsEv B M M₀ H.ι H'.ι (isoB H H') eB → cond n d (r + 1) (s + 1) →
      ∀ (K : Subgroup (UA σ X.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), Iwa H K → μK.IsHaarMeasure → μ.IsHaarMeasure →
      ∃ C₀ : ℂ, C₀ ≠ 0 ∧ ∀ χX χW om om₁ om₀, IsPair B M χX χW om (r + 1) (s + 1) (r' + 1) (s' + 1) →
        IsPair B M₁ χX χW om₁ (r + 1) (s + 1) r' s' → IsPair B M₀ χX χW om₀ r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d),
        (so = true → Φ ∈ M.So B.ψ B.τ₁) → KFinite om K Φ →
        ∃ A₀ A₁ : UA σ W.J → ℂ, IsCT H' (M.I om Φ) (A₀ + A₁) ∧ HasLaw W₁ H' χX ((n : ℝ) / 2) A₀ ∧
          HasLaw W₁ H' (χX / χW) (((d : ℝ) - n) / 2) A₁ ∧ ∀ h₁ p, IsLevi H' 1 h₁ p → ∀ h,
            (so = true → e₀ (om (1, h) Φ) ∈ M₁.So B.ψ B.τ₁) → A₀ (p * h) = C₀ * M₁.I om₁ (e₀ (om (1, h) Φ)) h₁) :
    AnySplit cond so := by
  intro F E _ _ _ _ _ σ B n d d₁ X W W₁ H' i₀ i₁ r s r' s' M M₁ hn hc hH' e₀ he₀
  by_cases h0 : min r s = 0
  · obtain ⟨C, hC0, h⟩ := hA F E σ B n d d₁ X W W₁ H' i₀ i₁ r s (r' + 1) (s' + 1) r' s' X M M₁ rfl h0 hH' e₀ he₀
    refine ⟨C, hC0, fun χX χW om om₁ hp hp₁ Φ hΦ _ => ?_⟩
    obtain ⟨K, μK, μ, hK1, -⟩ := hS F E σ B n X r s hp.base hp.herm
    obtain ⟨A₀, h1, h2, h3⟩ := h χX χW om om₁ hp hp₁ Φ (hK F E σ B n d X W M χX χW om _ _ _ _ hp K hK1 Φ hΦ).1
    exact ⟨A₀, 0, by rwa [add_zero], h2, fun t m _ h => by simp, fun h₁ p hp h _ => h3 h₁ p hp h⟩
  by_cases hex : ∃ χX χW om om₁, IsPair B M χX χW om r s (r' + 1) (s' + 1) ∧ IsPair B M₁ χX χW om₁ r s r' s'
  swap
  · exact ⟨1, one_ne_zero, fun χX χW om om₁ hp hp₁ => absurd ⟨χX, χW, om, om₁, hp, hp₁⟩ hex⟩
  obtain ⟨χ0, χ0', o, o₁, hq, hq₁⟩ := hex
  obtain ⟨r, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  obtain ⟨s, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  obtain ⟨Y, X₁, H, hY, hX₁, hH⟩ := hPl F E σ B hq.base n (n - 2) (by omega) (by omega) X (r + 1) (s + 1) (by omega) (by omega)
    hq.herm 0 1 (by omega) (by omega)
  simp only [Nat.add_sub_cancel] at hX₁
  obtain ⟨⟨M₀, hM₀⟩, hW⟩ := hP F E σ B hq.base _ _ X₁ W₁ r s r' s' hX₁ hq₁.skew
  obtain ⟨⟨eA, heA⟩, eB, heB⟩ := hC F E σ B n d _ W (reM M Y) χ0 χ0' o _ _ _ _ (reM_pair hq hY) _ _ X₁ W₁ H H' i₀ i₁ 0 1 M₀ hH hH' hM₀
  obtain ⟨K, μK, μ, hK1, -, hμK, hμ⟩ := hS F E σ B n X _ _ hq.base hq.herm
  have hIw : Iwa (X := X) H K := hI F E σ B n _ X _ _ H hq.base hq.herm (adapted_x_ne hH) hH.xx K hK1
  obtain ⟨C₀, hC₀, h⟩ := gen F E σ B n d _ d₁ (reS X Y) W X₁ W₁ H H' 0 1 i₀ i₁ r s r' s' (reM M Y) M₀ hH hH' (reM M₁ Y) e₀ eA eB
    (reM_good hq₁.good Y) hM₀ (reM_ev he₀ Y) heA heB hc K μK μ hIw hμK hμ
  refine ⟨C₀, hC₀, fun χX χW om om₁ hp hp₁ Φ hΦ hso => ?_⟩
  obtain ⟨om₀, hp₀⟩ := hW χX χW hp.hX hp.hW (res_low hp.resX hH.rank) hp₁.resW M₀ hM₀
  obtain ⟨hs, hf⟩ := hK F E σ B n d X W M χX χW om _ _ _ _ hp K hK1 Φ hΦ
  have := h χX χW om om₁ om₀ (reM_pair hp hY) (reM_pair hp₁ hY) hp₀ Φ hs (by rwa [reM_so]) hf
  simp only [reM_so] at this
  exact this

theorem anyBig (hG : GenBig) (hA : GenAniso) (hK : KFinData) (hS : StabEx) (hI : IwaEx) (hP : PairEx) (hPl : PlaneHerm) (hC : EvCone) :
    AnySplit (fun n d r s => ∃ z, 2 * n = d + 2 * z ∧ min r s + 1 ≤ z) false := by
  refine theta_kernel_general_identity hA hK hS hI hP hPl hC _ _ ?_
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ r s r' s' M M₀ hH hH' M₁ e₀ eA eB h1 h0 he₀ hA' _ ⟨z, hz, hz'⟩ K μK μ hI hμK hμ
  obtain ⟨C₀, C₁, hC₀, -, h⟩ := hG F E σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ r s r' s' M M₀ hH hH' M₁ e₀ eA h1 h0 he₀ hA' z
    ⟨hz, by omega⟩ K μK μ hI hμK hμ
  refine ⟨C₀, hC₀, fun χX χW om om₁ om₀ hp hp₁ hp₀ Φ hΦ _ hf => ?_⟩
  obtain ⟨A₀, A₁, a, b, c, e⟩ := h χX χW om om₁ om₀ hp hp₁ hp₀ Φ hΦ hf
  exact ⟨A₀, A₁, a, b, c, fun h₁ p hp h _ => (e h₁ p hp h).2⟩

theorem anySmall (hG : GenSmall) (hA : GenAniso) (hK : KFinData) (hS : StabEx) (hI : IwaEx) (hP : PairEx) (hPl : PlaneHerm)
    (hC : EvCone) : AnySplit (fun n d _ _ => ∃ z, d + 2 = 2 * n + 2 * z ∧ 2 ≤ z) true := by
  refine theta_kernel_general_identity hA hK hS hI hP hPl hC _ _ ?_
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ r s r' s' M M₀ hH hH' M₁ e₀ eA eB h1 h0 he₀ _ hB' ⟨z, hz⟩ K μK μ hI hμK hμ
  obtain ⟨C₀, C₁, hC₀, -, h⟩ := hG F E σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ r s r' s' M M₀ hH hH' M₁ e₀ eB h1 h0 he₀ hB' z
    hz K μK μ hI hμK hμ
  refine ⟨C₀, hC₀, fun χX χW om om₁ om₀ hp hp₁ hp₀ Φ _ hso hf => ?_⟩
  obtain ⟨A₀, A₁, a, b, c, e⟩ := h χX χW om om₁ om₀ hp hp₁ hp₀ Φ (hso rfl) hf
  exact ⟨A₀, A₁, a, b, c, fun h₁ p hp h hs => (e h₁ p hp h).2 (hs rfl)⟩

end PositivityTheory.ThKCT

end
