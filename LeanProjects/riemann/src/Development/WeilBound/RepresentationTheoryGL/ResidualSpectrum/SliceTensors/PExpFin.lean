import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ExpNegGlue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermUnipotentIntegralVariant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermAutomorphicCriterion

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Polynomial Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin

namespace PositivityTheory.Rg.Rs

namespace PExpFin

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}

omit [NumberField E] [IsTotallyComplex E] in
theorem aInf_add (r : ℕ) (s t : ℝ) : aInf E N r (s + t) = aInf E N r s * aInf E N r t := by
  apply Units.ext
  change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i w
  simp only [Pi.mul_apply]
  split_ifs <;> simp [← Complex.exp_add]

theorem aT_add (r : ℕ) (s t : ℝ) : aT E N r (s + t) = aT E N r s * aT E N r t := by
  rw [aT, aT, aT, aInf_add, map_mul]

theorem aT_zero (r : ℕ) : aT E N r 0 = 1 := by
  have h : aInf E N r 0 = 1 := Units.ext (by
    change Matrix.diagonal _ = 1
    rw [← Matrix.diagonal_one]
    congr 1
    funext i w
    simp)
  rw [aT, h, map_one]

theorem aT_comm (r : ℕ) (u v : ℝ) : aT E N r u * aT E N r v = aT E N r v * aT E N r u := by
  rw [← aT_add, add_comm, aT_add]

def Kl (r : ℕ) (s : ℝ) (p : ℂ[X]) (F : GA E N → ℂ) : Prop :=
  ∀ g, ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * F (aT E N r (s * j) * g) = 0

def klSub (r : ℕ) (s : ℝ) (p : ℂ[X]) : Submodule ℂ (GA E N → ℂ) where
  carrier := {F | Kl r s p F}
  add_mem' := fun {F G} (hF : Kl r s p F) (hG : Kl r s p G) g => by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hF g, hG g, add_zero]
  zero_mem' := fun g => by simp
  smul_mem' := fun c F (hF : Kl r s p F) g => by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← mul_zero c, ← hF g, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring

theorem kl_translate {r : ℕ} {s : ℝ} {p : ℂ[X]} {F : GA E N → ℂ} (h : Kl r s p F) (t : ℝ) :
    Kl r s p (fun g => F (aT E N r t * g)) := by
  intro g
  rw [← h (aT E N r t * g)]
  refine Finset.sum_congr rfl fun j _ => ?_
  show _ * F (aT E N r t * (aT E N r (s * j) * g)) = _
  rw [← mul_assoc, ← mul_assoc, aT_comm]

theorem kl_span {r : ℕ} {s : ℝ} {p : ℂ[X]} {F : GA E N → ℂ} (h : Kl r s p F) {F' : GA E N → ℂ}
    (hF' : F' ∈ Submodule.span ℂ (Set.range fun t : ℝ => fun g => F (aT E N r t * g))) : Kl r s p F' := by
  have hle : Submodule.span ℂ (Set.range fun t : ℝ => fun g => F (aT E N r t * g)) ≤ klSub r s p := by
    rw [Submodule.span_le]
    rintro _ ⟨t, rfl⟩
    exact kl_translate h t
  exact hle hF'

theorem kl_right {r : ℕ} {s : ℝ} {p : ℂ[X]} {F : GA E N → ℂ} (h : Kl r s p F) (k : GA E N) :
    Kl r s p (fun g => F (g * k)) := by
  intro g
  rw [← h (g * k)]
  simp only [mul_assoc]

theorem kl_lie {r : ℕ} {s : ℝ} {p : ℂ[X]} {F : Sm E N} (h : Kl r s p F.1) (X : Lie E N) :
    Kl r s p (lie E N X F).1 := by
  intro g
  have hd : ∀ j : ℕ, DifferentiableAt ℝ (chart F.1 (aT E N r (s * j) * g)) (oneL E N) :=
    fun j => differentiableAt_chart F.2 _
  have hz : (fun x => ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j • chart F.1 (aT E N r (s * j) * g) x) = 0 := by
    funext x
    by_cases hx : IsUnit (Matrix.of x)
    · simp only [chart, dif_pos hx, smul_eq_mul, Pi.zero_apply]
      rw [← h (g * infGL E N hx.unit)]
      simp only [mul_assoc]
    · simp [chart, dif_neg hx]
  have hs : HasFDerivAt (fun x => ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j • chart F.1 (aT E N r (s * j) * g) x)
      (∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j • fderiv ℝ (chart F.1 (aT E N r (s * j) * g)) (oneL E N))
      (oneL E N) := by
    exact HasFDerivAt.fun_sum fun j _ => (hd j).hasFDerivAt.const_smul (p.coeff j)
  rw [hz] at hs
  have h2 := congrArg (fun L : Lie E N →L[ℝ] ℂ => L X) (hs.unique (hasFDerivAt_const 0 _))
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply,
    smul_eq_mul, zero_apply] at h2
  simpa only [lie_apply, lieD] using h2

theorem kl_eigen {r : ℕ} {s : ℝ} {p : ℂ[X]} {F : GA E N → ℂ} (h : Kl r s p F) (h0 : F ≠ 0) {c : ℂ}
    (hc : ∀ (t : ℝ) g, F (aT E N r t * g) = Complex.exp (c * t) * F g) : p.IsRoot (Complex.exp (c * s)) := by
  obtain ⟨g, hg⟩ : ∃ g, F g ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact h0 (funext hcon)
  have e : ∀ j : ℕ, Complex.exp (c * ((s * j : ℝ) : ℂ)) = Complex.exp (c * s) ^ j := by
    intro j
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h1 := h g
  simp only [hc, e] at h1
  rw [Polynomial.IsRoot, Polynomial.eval_eq_sum_range]
  have h2 : (∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * Complex.exp (c * s) ^ j) * F g = 0 := by
    rw [← h1, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  exact (mul_eq_zero.1 h2).resolve_right hg

theorem exists_kl (r : ℕ) (s : ℝ) (F : GA E N → ℂ)
    (hfd : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun t : ℝ => fun g => F (aT E N r t * g)))) :
    ∃ p : ℂ[X], p.Monic ∧ Kl r s p F := by
  set W := Submodule.span ℂ (Set.range fun t : ℝ => fun g => F (aT E N r t * g))
  let L : Module.End ℂ (GA E N → ℂ) :=
    { toFun := fun f g => f (aT E N r s * g)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hW : ∀ f ∈ W, L f ∈ W := by
    have hle : W ≤ W.comap L := by
      rw [Submodule.span_le]
      rintro _ ⟨t, rfl⟩
      refine Submodule.subset_span ⟨t + s, funext fun g => ?_⟩
      change F (aT E N r (t + s) * g) = F (aT E N r t * (aT E N r s * g))
      rw [aT_add, mul_assoc]
    exact fun f hf => hle hf
  let L' := L.restrict hW
  have hpow : ∀ (i : ℕ) (f : GA E N → ℂ), (L ^ i) f = fun g => f (aT E N r (s * i) * g) := by
    intro i
    induction i with
    | zero =>
      intro f
      funext g
      simp [aT_zero]
    | succ i ih =>
      intro f
      funext g
      rw [pow_succ, Module.End.mul_apply, ih]
      change f (aT E N r s * (aT E N r (s * i) * g)) = _
      rw [← mul_assoc, ← aT_add]
      congr 3
      push_cast
      ring
  have hpow' : ∀ (i : ℕ) (x : W), ((L' ^ i) x).1 = (L ^ i) x.1 := by
    intro i
    induction i with
    | zero => intro x; rfl
    | succ i ih =>
      intro x
      rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
      rfl
  have hF : F ∈ W := Submodule.subset_span ⟨0, funext fun g => by simp [aT_zero]⟩
  refine ⟨L'.charpoly, LinearMap.charpoly_monic L', fun g => ?_⟩
  have h0 := congrArg (fun T : Module.End ℂ W => (T ⟨F, hF⟩).1 g) (LinearMap.aeval_self_charpoly L')
  rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply] at h0
  simp only [LinearMap.smul_apply, Submodule.coe_smul, hpow', hpow, Pi.smul_apply, smul_eq_mul,
    LinearMap.zero_apply, ZeroMemClass.coe_zero, Pi.zero_apply] at h0
  exact h0

section CT

variable {r : ℕ} [MeasurableSpace (BlockIx N r → Ad E)] [BorelSpace (BlockIx N r → Ad E)]
  (μ : Measure (BlockIx N r → Ad E)) [μ.IsAddHaarMeasure] (𝓕 : Set (BlockIx N r → Ad E))

theorem ct_add (h𝓕 : IsAddFundamentalDomain (ratN E N r) 𝓕 μ) {φ ψ : Sm E N} (hφ : IsAutForm φ)
    (hψ : IsAutForm ψ) : PositivityTheory.Affgl.CT.ct μ 𝓕 (φ + ψ).1 = PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1 + PositivityTheory.Affgl.CT.ct μ 𝓕 ψ.1 := by
  funext g
  exact integral_add (GlobalTheory.CompanionTheory.CTFin.Central.integrable_unip_mul μ 𝓕 h𝓕 hφ.left hφ.level g)
    (GlobalTheory.CompanionTheory.CTFin.Central.integrable_unip_mul μ 𝓕 h𝓕 hψ.left hψ.level g)

omit [BorelSpace (BlockIx N r → Ad E)] [μ.IsAddHaarMeasure] in
theorem ct_smul (c : ℂ) (φ : Sm E N) :
    PositivityTheory.Affgl.CT.ct μ 𝓕 (c • φ).1 = c • PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1 := by
  funext g
  exact integral_smul c _

theorem kl_act (h𝓕 : IsAddFundamentalDomain (ratN E N r) 𝓕 μ) {s : ℝ} {p : ℂ[X]} {φ : Sm E N}
    (hφ : IsAutForm φ) (h : Kl r s p (PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1)) (o : Op E N) :
    Kl r s p (PositivityTheory.Affgl.CT.ct μ 𝓕 (act o φ).1) := by
  cases o with
  | fin k =>
    have e : PositivityTheory.Affgl.CT.ct μ 𝓕 (act (.fin k) φ).1 = fun g => PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1 (g * finGL E N k) := by
      funext g
      exact congrArg (fun f : (BlockIx N r → Ad E) → ℂ => ∫ x in 𝓕, f x ∂μ)
        (funext fun x => congrArg φ.1 (mul_assoc _ _ _))
    rw [e]
    exact kl_right h _
  | cpt k =>
    have e : PositivityTheory.Affgl.CT.ct μ 𝓕 (act (.cpt k) φ).1 =
        fun g => PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1 (g * infGL E N (Unitary.toUnits k)) := by
      funext g
      exact congrArg (fun f : (BlockIx N r → Ad E) → ℂ => ∫ x in 𝓕, f x ∂μ)
        (funext fun x => congrArg φ.1 (mul_assoc _ _ _))
    rw [e]
    exact kl_right h _
  | lie X =>
    obtain ⟨F, hF1, hF2⟩ := GlobalTheory.CompanionTheory.CTSmooth.ct_smooth E N r φ hφ.left hφ.level μ 𝓕 inferInstance h𝓕
    have e1 : F.1 = PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1 := funext hF1
    have e2 : (lie E N X F).1 = PositivityTheory.Affgl.CT.ct μ 𝓕 (act (.lie X) φ).1 := funext (hF2 X)
    rw [← e2]
    exact kl_lie (e1 ▸ h) X

theorem kl_all (h𝓕 : IsAddFundamentalDomain (ratN E N r) 𝓕 μ) {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V)
    {s : ℝ} {p : ℂ[X]} {φ₀ : Sm E N} (hφ₀ : φ₀ ∈ V) (h0 : φ₀ ≠ 0) (hk : Kl r s p (PositivityTheory.Affgl.CT.ct μ 𝓕 φ₀.1)) :
    ∀ φ ∈ V, Kl r s p (PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1) := by
  let W : Submodule ℂ (Sm E N) :=
    { carrier := {φ | φ ∈ V ∧ Kl r s p (PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1)}
      add_mem' := fun {φ ψ} hφ hψ => ⟨V.add_mem hφ.1 hψ.1, by
        rw [ct_add μ 𝓕 h𝓕 (hV.aut φ hφ.1) (hV.aut ψ hψ.1)]
        exact (klSub r s p).add_mem hφ.2 hψ.2⟩
      zero_mem' := ⟨V.zero_mem, by
        have : PositivityTheory.Affgl.CT.ct μ 𝓕 (0 : Sm E N).1 = 0 := by
          funext g
          simp [PositivityTheory.Affgl.CT.ct]
        rw [this]
        exact (klSub r s p).zero_mem⟩
      smul_mem' := fun c φ hφ => ⟨V.smul_mem c hφ.1, by
        rw [ct_smul]
        exact (klSub r s p).smul_mem c hφ.2⟩ }
  have hle : W ≤ V := fun φ hφ => hφ.1
  have hst : IsStable W := fun o φ hφ => ⟨hV.stable o φ hφ.1, kl_act μ 𝓕 h𝓕 (hV.aut φ hφ.1) hφ.2 o⟩
  rcases hV.irred W hle hst with hW | hW
  · have : φ₀ ∈ W := ⟨hφ₀, hk⟩
    rw [hW] at this
    exact absurd ((Submodule.mem_bot ℂ).1 this) h0
  · intro φ hφ
    rw [← hW] at hφ
    exact hφ.2

end CT

theorem exp_pair_inj {c c' : ℂ} (h1 : Complex.exp (c * ((1 : ℝ) : ℂ)) = Complex.exp (c' * ((1 : ℝ) : ℂ)))
    (h2 : Complex.exp (c * ((√2 : ℝ) : ℂ)) = Complex.exp (c' * ((√2 : ℝ) : ℂ))) : c = c' := by
  rw [Complex.exp_eq_exp_iff_exists_int] at h1 h2
  obtain ⟨n, hn⟩ := h1
  obtain ⟨m, hm⟩ := h2
  simp only [Complex.ofReal_one, mul_one] at hn
  rw [hn] at hm
  have e : ((n : ℂ) * ((√2 : ℝ) : ℂ) - m) * (2 * Real.pi * Complex.I) = 0 := by linear_combination hm
  have e2 := congrArg Complex.re ((mul_eq_zero.1 e).resolve_right Complex.two_pi_I_ne_zero)
  simp at e2
  by_cases hn0 : n = 0
  · rw [hn, hn0]
    simp
  · exact absurd (by linarith : (n : ℝ) * √2 = m) ((irrational_sqrt_two.intCast_mul hn0).ne_int m)

end PExpFin

open PExpFin in
theorem expFin_of (hD : Dict) (hT : FinTr) : ExpFin := by
  intro E _ _ _ N V hV r hr hrN
  obtain ⟨φ₀, hφ₀, h0⟩ := (Submodule.ne_bot_iff _).1 hV.ne_bot
  obtain ⟨-, -, -, hDct⟩ := hD E N
  let _ : MeasurableSpace (BlockIx N r → Ad E) := borel _
  have _ : BorelSpace (BlockIx N r → Ad E) := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, h𝓕, -⟩ := (hDct φ₀ (hV.aut φ₀ hφ₀) r hr hrN).1
  have _ := hμ
  have hpoly : ∀ s : ℝ, ∃ p : ℂ[X], p.Monic ∧ ∀ φ ∈ V, Kl r s p (PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1) := by
    intro s
    obtain ⟨p, hp, hk⟩ := exists_kl r s _
      (hT E N φ₀ (hV.aut φ₀ hφ₀) r hr hrN (PositivityTheory.Affgl.CT.ct μ 𝓕 φ₀.1) ⟨μ, 𝓕, hμ, h𝓕, rfl⟩)
    exact ⟨p, hp, kl_all μ 𝓕 h𝓕 hV hφ₀ h0 hk⟩
  obtain ⟨p₁, hp₁, hk₁⟩ := hpoly 1
  obtain ⟨p₂, hp₂, hk₂⟩ := hpoly √2
  let f : ℂ → ℂ × ℂ := fun c => (Complex.exp (c * ((1 : ℝ) : ℂ)), Complex.exp (c * ((√2 : ℝ) : ℂ)))
  have hfin : ({z | p₁.IsRoot z} ×ˢ {z | p₂.IsRoot z} : Set (ℂ × ℂ)).Finite :=
    (Polynomial.finite_setOfPred_isRoot hp₁.ne_zero).prod (Polynomial.finite_setOfPred_isRoot hp₂.ne_zero)
  refine (hfin.preimage (f := f) fun c _ c' _ e =>
    exp_pair_inj (congrArg Prod.fst e) (congrArg Prod.snd e)).subset ?_
  rintro c ⟨φ, hφ, F₀, hCT, F, hFspan, hF0, hFe⟩
  obtain ⟨-, huniq⟩ := hDct φ (hV.aut φ hφ) r hr hrN
  obtain ⟨c₁, -, e₁⟩ := huniq F₀ hCT
  obtain ⟨c₂, hc₂, e₂⟩ := huniq _ ⟨μ, 𝓕, hμ, h𝓕, rfl⟩
  have eF₀ : F₀ = (c₁ / c₂) • PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1 := by
    funext g
    rw [e₁, Pi.smul_apply, e₂, smul_eq_mul]
    field_simp
  have hk : ∀ s p, Kl r s p (PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1) → p.IsRoot (Complex.exp (c * s)) := by
    intro s p h
    refine kl_eigen (kl_span ?_ hFspan) hF0 hFe
    rw [eF₀]
    exact (klSub r s p).smul_mem _ h
  exact ⟨hk 1 p₁ (hk₁ φ hφ), hk √2 p₂ (hk₂ φ hφ)⟩

end PositivityTheory.Rg.Rs

end
