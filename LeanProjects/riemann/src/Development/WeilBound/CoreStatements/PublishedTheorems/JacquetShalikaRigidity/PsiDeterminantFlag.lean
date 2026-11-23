import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemUnipBOfMemUnipotent

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace PsiDeterminantFlag

theorem exists_psiOK {E : Type} [Field E] [NumberField E] (w : Pl E) :
    ∃ χ : AddChar (w.adicCompletion E) ℂ, PositivityTheory.JacquetShalikaLocal.PsiOK χ := by
  obtain ⟨ψ₁, hψ₁⟩ := GlobalTheory.SplitWeil.exists_hasConductor_one (w.adicCompletion E)
  exact ⟨_, GlobalTheory.CompanionTheory.JSBound.psiOK_of_hasConductor hψ₁⟩

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {k : ℕ}

theorem dt_fl (hG0 : jumpWindows.G0) (hD0 : D0) (w : Pl E)
    (n : GL (Fin k) (w.adicCompletion E)) (hn : n ∈ Iwasawa.unipotent (w.adicCompletion E) k)
    (κ : GL (Fin k) (w.adicCompletion E)) (hκ : κ ∈ GLnLocal.integralGL (w.adicCompletion E) k)
    (l : Fin k → ℤ) :
    Dt (fl k w (n * Iwasawa.torusPow (w.adicCompletion E) k l * κ)) =
      (Ideal.absNorm w.asIdeal : ℝ) ^ (-∑ i, l i) := by
  obtain ⟨_, hmul, _, _, hUU, _, _, _, _, htor, hint⟩ := hD0 E k
  obtain ⟨_, _, hci, hcl, hcl', -⟩ := hG0 E k
  have h1 : Dt (fl k w n) = 1 := by
    obtain ⟨t1, t2, -⟩ := GlobalTheory.T.localUpperUnipotent_adelic_upperUnipotent E k w n (fun i j hij => hn.1 hij) hn.2
    exact hUU 0 _ ⟨t1, t2, fun i c hc => absurd hc (Nat.not_lt_zero _)⟩
  have h2 : Dt (fl k w κ) = 1 := by
    refine hint _ (hci w κ) fun v => ?_
    by_cases hv : v = w
    · subst hv; rw [hcl]; exact hκ
    · rw [hcl' w v κ hv]; exact one_mem _
  rw [map_mul, map_mul, hmul, hmul, h1, h2, htor, one_mul, mul_one]

end PsiDeterminantFlag

theorem mean_convergence_of : jumpWindows.G0 → D0 → P2 → C0 → C2 → D1 → M0 → LocalHeckeAlgebra → CAUCHY → M1 := by
  intro hG0 hD0 hP2 _ hC2 hD1 hM0 hK8a hC E _ _ _ k μ _ hk β hβ ψ hψ S m α α' u f φ hkm hα hα' hD
  have : BorelSpace (GA E k) := ⟨rfl⟩
  obtain ⟨hpos, hmul, hcont, -, hUU, -⟩ := hD0 E k
  obtain ⟨hlaw, hpsN, hUU01, hwhit, -, hgood, -⟩ := hP2 E k ψ hψ
  obtain ⟨β', σ₀', hβ', hM⟩ := hM0 E k μ hk β hβ ψ hψ S m α α' u f φ hD
  have hk1 : k - 1 < k := by omega
  have hWf : Pre ψ 0 (whit ψ (k - 1) f) := hwhit _ hk1 f hD.pre
  have hWφ : Pre ψ 0 (whit ψ (k - 1) φ) := hwhit _ hk1 φ (hgood _ φ hD.good)
  have hPc : Continuous (PW ψ f φ) := hWf.cont.mul (Complex.continuous_conj.comp hWφ.cont)
  have hPu : ∀ n, UU 0 n → ∀ g, PW ψ f φ (n * g) = PW ψ f φ g := by
    intro n hn g
    have h1 := hlaw 0 _ hWf n (hUU01 n hn) g
    have h2 := hlaw 0 _ hWφ n (hUU01 n hn) g
    simp only [PW, h1, h2, map_mul]
    have e : psN ψ n * conj (psN ψ n) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hpsN]; simp
    linear_combination (whit ψ (k - 1) f g * conj (whit ψ (k - 1) φ g)) * e
  have hDtu : ∀ n, UU 0 n → ∀ g, Dt (n * g) = Dt g := fun n hn g => by rw [hmul, hUU 0 n hn, one_mul]
  have hDtm : Measurable fun g : GA E k => (Dt g : ℂ) := Complex.measurable_ofReal.comp hcont.measurable
  have hΦm : ∀ z : ℂ, Measurable fun g => PW ψ f φ g * (Dt g : ℂ) ^ z := fun z =>
    hPc.measurable.mul (hDtm.pow_const z)
  have hΦu : ∀ z : ℂ, ∀ n, UU 0 n → ∀ g,
      PW ψ f φ (n * g) * (Dt (n * g) : ℂ) ^ z = PW ψ f φ g * (Dt g : ℂ) ^ z := by
    intro z n hn g; rw [hPu n hn, hDtu n hn]
  have hχ : ∀ w : Off E S, ∃ χ : AddChar (w.1.adicCompletion E) ℂ, PositivityTheory.JacquetShalikaLocal.PsiOK χ :=
    fun w => PsiDeterminantFlag.exists_psiOK w.1
  let a' : ℂ → Off E S → (Fin k → ℤ) → ℂ := fun z w l =>
    aLoc α α' w l * (((nq w : ℝ) ^ (-∑ i, l i) : ℝ) : ℂ) ^ z
  have ha0 : ∀ z w, a' z w 0 = 1 := by
    intro z w
    obtain ⟨χ, hχ'⟩ := hχ w
    simp [a', (hK8a E S m k α α' w χ hχ' hk hkm).1]
  have hlawz : ∀ z, LawOff S (fun g => PW ψ f φ g * (Dt g : ℂ) ^ z) (a' z) := by
    intro z w g hg n hn κ hκ l
    simp only [a']
    rw [hD.law w g hg n hn κ hκ l, hmul, PsiDeterminantFlag.dt_fl hG0 hD0 w.1 n hn κ hκ l, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hpos g).le (by positivity)]
    simp only [nq]; ring
  have hI : ∀ s : ℂ, 2 < s.re → σ₀' < (s - ((m : ℂ) - k) / 2).re →
      ∫ g, PW ψ f φ g * (Dt g : ℂ) ^ (s - ((m : ℂ) - k) / 2) ∂μ.withDensity β' =
        (∫ g in G0 S, PW ψ f φ g * (Dt g : ℂ) ^ (s - ((m : ℂ) - k) / 2) ∂μ.withDensity β') * LS S α α' s := by
    intro s hs hs'
    have hsum := hC2 E k μ hk β' hβ' S _ (a' (s - ((m : ℂ) - k) / 2)) (hΦm _) (hΦu _) (hlawz _) (ha0 _)
      (hM _ hs').1
    obtain ⟨-, hL⟩ := hC E S m k α α' s hkm hα hα' hs
    have e : (fun l : Off E S →₀ (Fin k → ℤ) => ∏ w ∈ l.support, loc (nq w) (α w) (α' w) s (l w)) =
        fun l => ∏ w ∈ l.support, (nq w : ℂ) ^ rhoPair (l w) * a' (s - ((m : ℂ) - k) / 2) w (l w) := by
      funext l
      refine Finset.prod_congr rfl fun w _ => ?_
      obtain ⟨χ, hχ'⟩ := hχ w
      exact (((hK8a E S m k α α' w χ hχ' hk hkm).2 (l w)).1 s).symm
    rw [e] at hL
    have hL2 := hL.mul_right (∫ g in G0 S, PW ψ f φ g * (Dt g : ℂ) ^ (s - ((m : ℂ) - k) / 2) ∂μ.withDensity β')
    rw [mul_comm _ (LS S α α' s)]
    exact hsum.unique hL2
  obtain ⟨hdiff, hnz⟩ := hD1 E k μ hk β' hβ' S (PW ψ f φ) u ((σ₀' + 1 : ℝ) : ℂ) hPc hPu hD.one hD.pos
    (hM _ (by simp)).1
  refine ⟨fun s => ∫ g in G0 S, PW ψ f φ g * (Dt g : ℂ) ^ (s - ((m : ℂ) - k) / 2) ∂μ.withDensity β',
    max 2 (σ₀' + ((m : ℝ) - k) / 2), hdiff.comp (differentiable_id.sub_const _), ?_, ?_⟩
  · intro σ
    have e : ((σ : ℂ) + u * Complex.I) - ((m : ℂ) - k) / 2 =
        ((σ - ((m : ℝ) - k) / 2 : ℝ) : ℂ) + u * Complex.I := by push_cast; ring
    dsimp only
    rw [e]
    exact hnz _
  · intro s hs
    have hs2 : 2 < s.re := lt_of_le_of_lt (le_max_left _ _) hs
    have hre : (s - ((m : ℂ) - k) / 2).re = s.re - ((m : ℝ) - k) / 2 := by simp
    have hs' : σ₀' < (s - ((m : ℂ) - k) / 2).re := by
      rw [hre]; linarith [le_max_right 2 (σ₀' + ((m : ℝ) - k) / 2)]
    have e1 : ∀ g, sumF f g * conj (φ g) * (Dt g : ℂ) ^ (-(((m : ℂ) - k) / 2)) * (Dt g : ℂ) ^ s =
        sumF f g * conj (φ g) * (Dt g : ℂ) ^ (s - ((m : ℂ) - k) / 2) := by
      intro g
      rw [mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 (hpos g).ne'), neg_add_eq_sub]
    simp_rw [e1]
    rw [(hM _ hs').2, hI s hs2 hs']

end PositivityTheory.AdelicQuotientData

end
