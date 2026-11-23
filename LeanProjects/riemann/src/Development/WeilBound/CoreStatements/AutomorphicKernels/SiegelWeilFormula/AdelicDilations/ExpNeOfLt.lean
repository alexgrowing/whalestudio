import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.DegCut

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.AStep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exp_ne_of_lt {m n : ℕ} (h : m < n) : Complex.exp ((2 * n - m : ℕ) : ℂ) ≠ Complex.exp (m : ℂ) := by
  intro e
  have e' : Real.exp ((2 * n - m : ℕ) : ℝ) = Real.exp (m : ℝ) := by
    have := congrArg Complex.re e
    rwa [← Complex.ofReal_natCast, ← Complex.ofReal_natCast (m : ℕ), Complex.exp_ofReal_re, Complex.exp_ofReal_re] at this
  have := Real.exp_injective e'
  have h2 : (2 * n - m : ℕ) = m := by exact_mod_cast this
  omega

theorem deg (H : Hyps) {d : SD σ} (R : RD d) (L : LD d) (R' : RD L.sd) (hmn : d.m < d.n) (hIH : MainV 2 R') {Φ : d.Fn}
    (hΦ : Φ ∈ d.sch) (hv : d.T Φ ∈ R.vac) {U p Ê t} (hE : EData d (d.sec0 Φ) (s0 d.m d.n) (s0 d.m d.n) U p Ê t) (j : ℕ)
    (hj : j ≤ p.rootMultiplicity (s0 d.m d.n)) (hlow : ∀ i < j, ∀ g, iteratedDeriv i (Ê · g) (s0 d.m d.n) = 0)
    {nb lam 𝓖} (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b} (hT : L.IsSub T T')
    (x : d.G) : fc d.B.ψ d.b nb lam 𝓖 (Bj d Φ p Ê j) T x = 0 := by
  have hK := H.polyKFin F E σ d R Φ hΦ ((H.vacK F E σ d R).2.1 hv)
  have hsec := H.secK F E σ d Φ hK
  have hEis := H.eisWk F E σ d _ _ hsec
  have hE' := hE
  obtain ⟨hUo, hR, hs, hp, hd, hcont, hinv, hfar⟩ := hE'
  obtain ⟨-, -, hI⟩ := H.tAll.2.2.2.2 F E σ d
  obtain ⟨-, hIc, hIi⟩ := hI Φ hΦ
  set s := s0 d.m d.n with hsdef
  set A : d.G → ℂ := fun g => iteratedDeriv j (Ê · g) s with hAdef
  have hAc : Continuous A := famCont U Ê hUo hd hcont _ hs j
  have hAi : ∀ γ ∈ rat2 σ d.Y, ∀ g, A (γ * g) = A g :=
    fun γ hγ g => derivInv U Ê hUo _ hs γ g (fun z hz => hinv z hz γ hγ g) j

  have hB : Bj d Φ p Ê j = (-(iteratedDeriv j (fun z => p.eval z) s * 2)) • d.I Φ + A := by
    funext g; simp only [Bj, hAdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hfcB : ∀ x', fc d.B.ψ d.b nb lam 𝓖 (Bj d Φ p Ê j) T x' =
      fc d.B.ψ d.b nb lam 𝓖 A T x' - iteratedDeriv j (fun z => p.eval z) s * (2 * fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x') := by
    intro x'
    rw [hB, (fcAll d hc T x').1 _ _ _ hIc hAc hIi hAi]; ring

  let w : InfinitePlace F := Classical.arbitrary _
  obtain ⟨y, hy⟩ := dilEx d.n (Pi.single L.i₀ 1) 1
  obtain ⟨pp, qq, e, hpq, hhol⟩ := holA H R hmn hΦ hv hE w j hj hlow
  obtain ⟨hlawA, huA⟩ := holCoef H R L w hc hT A hAc hAi pp qq e hpq hhol
  obtain ⟨uM, ν, 𝓤, hu⟩ := (H.uEx F E σ d R L).1
  obtain ⟨nb', lam', 𝓖', hc'⟩ := H.coefEx F E σ L.sd
  obtain ⟨t', hct⟩ := H.cTSplit F E σ d R L _ _ hsec hEis
  have hspl : ∀ z : ℂ, t' < z.re → ∃ c₂ : d.G → ℂ,
      (∀ x, avg d L uM ν 𝓤 nb lam 𝓖 (d.eis (d.sec0 Φ) s z) T x = cOne d L (d.sec0 Φ) s z nb' lam' 𝓖' T' x + c₂ x) ∧
      ∀ x, c₂ (R.ι w y * x) = Complex.exp (((1 : ℝ) : ℂ) * (d.n - 2 * z)) * c₂ x := by
    intro z hz
    obtain ⟨c₂, h1, h2⟩ := hct z hz nb lam 𝓖 hc nb' lam' 𝓖' hc' uM ν 𝓤 hu T T' hT
    exact ⟨c₂, h1, fun x => h2 w 1 y x hy⟩
  let c2 : ℂ → d.G → ℂ := fun z => if h : t' < z.re then Classical.choose (hspl z h) else 0
  have hc2 : ∀ z : ℂ, t' < z.re → (∀ x, avg d L uM ν 𝓤 nb lam 𝓖 (d.eis (d.sec0 Φ) s z) T x =
      cOne d L (d.sec0 Φ) s z nb' lam' 𝓖' T' x + c2 z x) ∧
      ∀ x, c2 z (R.ι w y * x) = Complex.exp (((1 : ℝ) : ℂ) * (d.n - 2 * z)) * c2 z x := by
    intro z hz
    simp only [c2, dif_pos hz]
    exact Classical.choose_spec (hspl z hz)

  have havg_smul : ∀ (c : ℂ) (φ : d.G → ℂ) x', avg d L uM ν 𝓤 nb lam 𝓖 (fun g => c * φ g) T x' =
      c * avg d L uM ν 𝓤 nb lam 𝓖 φ T x' := by
    intro c φ x'
    simp only [avg, fc, mul_assoc]
    simp only [integral_const_mul]
  have hhol1 := avgHol H L hE hc T hT hu

  have hsep := lawSep U p (max t t') s j (fun z => avg d L uM ν 𝓤 nb lam 𝓖 (Ê z) T x)
    (fun z => avg d L uM ν 𝓤 nb lam 𝓖 (Ê z) T (R.ι w y * x))
    (fun z => cOne d L (d.sec0 Φ) s z nb' lam' 𝓖' T' x) (fun z => cOne d L (d.sec0 Φ) s z nb' lam' 𝓖' T' (R.ι w y * x))
    (fun z => c2 z x) (fun z => c2 z (R.ι w y * x)) (2 * fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x)
    (2 * fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T (R.ι w y * x)) (d.n : ℂ) (-2) hUo hR hs hp hj (hhol1 x).1 (hhol1 _).1
    (fun i hi => by
      rw [(hhol1 x).2 i]
      have : (fun g => iteratedDeriv i (Ê · g) s) = fun _ => 0 := funext fun g => hlow i hi g
      rw [this]; simp [avg, fc])
    (fun i hi => by
      rw [(hhol1 _).2 i]
      have : (fun g => iteratedDeriv i (Ê · g) s) = fun _ => 0 := funext fun g => hlow i hi g
      rw [this]; simp [avg, fc])
    (fun z hz => by
      have h1 := (hfar z (lt_of_le_of_lt (le_max_left _ _) hz)).2
      have e1 : Ê z = fun g => p.eval z * d.eis (d.sec0 Φ) s z g := funext h1
      rw [e1, havg_smul, (hc2 z (lt_of_le_of_lt (le_max_right _ _) hz)).1 x])
    (fun z hz => by
      have h1 := (hfar z (lt_of_le_of_lt (le_max_left _ _) hz)).2
      have e1 : Ê z = fun g => p.eval z * d.eis (d.sec0 Φ) s z g := funext h1
      rw [e1, havg_smul, (hc2 z (lt_of_le_of_lt (le_max_right _ _) hz)).1 _])
    (cOneVal H R L R' hIH hΦ hv hc hc' hT x) (cOneVal H R L R' hIH hΦ hv hc hc' hT _)
    (fun z hz => by
      rw [(hc2 z (lt_of_le_of_lt (le_max_right _ _) hz)).2 x]
      congr 1; push_cast; ring_nf)

  have havgA : ∀ x', iteratedDeriv j (fun z => avg d L uM ν 𝓤 nb lam 𝓖 (Ê z) T x') s = fc d.B.ψ d.b nb lam 𝓖 A T x' := by
    intro x'
    rw [(hhol1 x').2 j]
    show avg d L uM ν 𝓤 nb lam 𝓖 A T x' = _
    simp only [avg, huA uM ν 𝓤 hu, setIntegral_const]
    simp [Measure.real, hu.2.2.2]
  rw [havgA, havgA] at hsep

  have hth : fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T (R.ι w y * x) = Complex.exp (d.m : ℂ) * fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x := by
    have := valLaw (fun z => cOne d L (d.sec0 Φ) s z nb' lam' 𝓖' T' x)
      (fun z => cOne d L (d.sec0 Φ) s z nb' lam' 𝓖' T' (R.ι w y * x)) 0 (d.n : ℂ) 2 s _ _
      (fun z _ => by rw [cOneLaw H R L hΦ w hc' T' 1 y hy z x]; congr 1; push_cast; ring_nf)
      (cOneVal H R L R' hIH hΦ hv hc hc' hT x) (cOneVal H R L R' hIH hΦ hv hc hc' hT _)
    have e2 : (d.n : ℂ) + 2 * s = d.m := by rw [hsdef, s0]; ring
    rw [e2] at this
    linear_combination this / 2
  have hA1 := hlawA 1 y hy x
  rw [Complex.ofReal_one, one_mul] at hA1
  rw [hfcB x]
  rw [hA1, hth] at hsep
  have e3 : (d.n : ℂ) + -2 * s = ((2 * d.n - d.m : ℕ) : ℂ) := by
    have h2 : ((2 * d.n - d.m : ℕ) : ℂ) = 2 * (d.n : ℂ) - d.m := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [h2, hsdef, s0]; ring
  rw [e3] at hsep
  have hne := exp_ne_of_lt hmn
  have key : (Complex.exp ((2 * d.n - d.m : ℕ) : ℂ) - Complex.exp (d.m : ℂ)) *
      (fc d.B.ψ d.b nb lam 𝓖 A T x - iteratedDeriv j (fun z => p.eval z) s * (2 * fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x)) = 0 := by
    linear_combination -hsep
  rcases mul_eq_zero.1 key with h | h
  · exact absurd (sub_eq_zero.1 h) hne
  · exact h

end PositivityTheory.SiegelWeilFormula.AStep

end
