import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.Descend

noncomputable section

open Filter Topology PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.RgEisScale

variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

lemma ht_rep {Γ K P : Subgroup G} {l : G → ℝ} (hl : IsHt Γ K ⊤ l) (q : Cos P Γ) (g : G) :
    l (rep q * g) = l g := by
  have hq : rep q ∈ Γ := (Quotient.out q).2
  rw [hl.left _ (Subgroup.mem_top _), hl.rat _ hq (Subgroup.mem_top _), zero_add]

lemma eis_twist {Γ K P : Subgroup G} {l : G → ℝ} (hl : IsHt Γ K ⊤ l) (c : G → ℂ)
    (ρ : K →* (W →L[ℂ] W)) (Λ Λ' : G → ℂ) (t : ℂ) (h : ∀ x, Λ' x = Λ x + t * l x) (g : G) (w : W) :
    eis Γ K P c ρ Λ' g w = Complex.exp (t * l g) • eis Γ K P c ρ Λ g w := by
  unfold eis
  rw [← tsum_const_smul'']
  refine tsum_congr fun q => ?_
  rw [h, ht_rep hl, Complex.exp_add, smul_smul, mul_comm]

lemma conv_twist {Γ K P : Subgroup G} {l : G → ℝ} (hl : IsHt Γ K ⊤ l) {f f' : G → ℝ} (t : ℝ)
    (h : ∀ x, f' x = f x + t * l x) (hc : Conv Γ P f) : Conv Γ P f' := by
  intro g
  refine ((hc g).mul_right (Real.exp (t * l g))).congr fun q => ?_
  rw [h, ht_rep hl, Real.exp_add]

theorem wall_scale [IsTopologicalGroup G] {K Γ P P' : Subgroup G} {ρ : K →* (W →L[ℂ] W)} {c : G → ℂ}
    {η η' β l : G → ℝ} {s : ℝ} (hs : 0 < s) (hl : IsHt Γ K ⊤ l) {R : ℝ} {D : ℂ → ℂ}
    {Op : ℂ → (secSp K P c ρ →L[ℂ] secSp K P' c ρ)} {H : ℂ → G → (secSp K P c ρ →L[ℂ] W)}
    (hw : Wall Γ K P P' c η η' β ρ (secSp K P c ρ) R D Op H) :
    Wall Γ K P P' c (fun g => s * (η g + l g)) (fun g => s * (η' g - l g)) β ρ (secSp K P c ρ) (R / s)
      (fun z => D (s * z)) (fun z => Op (s * z))
      (fun z g => Complex.exp (s * z * l g) • H (s * z) g) := by
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hre : ∀ z : ℂ, ((s : ℂ) * z).re = s * z.re := fun z => by simp
  have hσ : Differentiable ℂ (fun z : ℂ => (s : ℂ) * z) := by fun_prop
  have hgtx : ∀ x : ℝ, R / s < x → R < s * x := fun x hx => by
    rwa [div_lt_iff₀' hs] at hx
  have hltx : ∀ x : ℝ, x < -(R / s) → s * x < -R := fun x hx => by
    have h1 := mul_lt_mul_of_pos_left hx hs
    have h2 : s * -(R / s) = -R := by field_simp
    linarith
  have hlec : ∀ {x : ℝ} {z : ℂ}, x ≤ z.re → s * x ≤ ((s : ℂ) * z).re := fun h => by
    rw [hre]; exact mul_le_mul_of_nonneg_left h hs.le
  have hlec' : ∀ {y : ℝ} {z : ℂ}, z.re ≤ y → ((s : ℂ) * z).re ≤ s * y := fun h => by
    rw [hre]; exact mul_le_mul_of_nonneg_left h hs.le
  have hlc : Continuous fun g => (l g : ℂ) := Complex.continuous_ofReal.comp hl.cont
  refine
    { le := hw.le
      pos := div_nonneg hw.pos hs.le
      convR := fun x hx => ?_
      convL := fun x hx => ?_
      dEnt := ⟨hw.dEnt.1.comp hσ, fun b a => ?_⟩
      dNe := ?_
      op := ⟨?_, fun b a ha => ?_⟩
      hol := fun g => ?_
      cont := ?_
      bdd := fun b a g => ?_
      eqR := fun z hz g w => ?_
      eqL := fun z hz g w => ?_ }
  · exact conv_twist hl (s * x) (fun y => by ring) (hw.convR (s * x) (hgtx x hx))
  · exact conv_twist hl (s * x) (fun y => by ring) (hw.convL (s * x) (hltx x hx))
  · obtain ⟨M, hM⟩ := hw.dEnt.2 (s * b) (s * a)
    exact ⟨M, fun z h1 h2 => hM _ (hlec h1) (hlec' h2)⟩
  · obtain ⟨z, hz⟩ := hw.dNe
    refine ⟨z / s, ?_⟩
    have : (s : ℂ) * (z / s) = z := by field_simp
    simpa [this] using hz
  · refine hw.op.1.comp hσ.differentiableOn fun z hz => ?_
    have hz' : z.re < -(R / s) := hz
    show ((s : ℂ) * z).re < -R
    rw [hre]; exact hltx _ hz'
  · obtain ⟨M, hM⟩ := hw.op.2 (s * b) (s * a) (hltx a ha)
    exact ⟨M, fun z h1 h2 => hM _ (hlec h1) (hlec' h2)⟩
  · have h1 : Differentiable ℂ fun z : ℂ => Complex.exp (s * z * l g) := by fun_prop
    exact h1.smul ((hw.hol g).comp hσ)
  · have h1 : Continuous fun y : ℂ × G => Complex.exp (s * y.1 * l y.2) :=
      ((continuous_const.mul continuous_fst).mul (hlc.comp continuous_snd)).cexp
    have h2 : Continuous fun y : ℂ × G => H (s * y.1) y.2 :=
      hw.cont.comp (f := fun y : ℂ × G => ((s : ℂ) * y.1, y.2)) (by fun_prop)
    exact h1.smul h2
  · obtain ⟨U, hU, M, hM⟩ := hw.bdd (s * b) (s * a) g
    have hV : {g' | |l g'| < |l g| + 1} ∈ 𝓝 g :=
      (isOpen_lt (continuous_abs.comp hl.cont) continuous_const).mem_nhds (by simp)
    refine ⟨U ∩ {g' | |l g'| < |l g| + 1}, inter_mem hU hV,
      Real.exp (s * max |b| |a| * (|l g| + 1)) * M, fun z h1 h2 g' hg' => ?_⟩
    have hH := hM _ (hlec h1) (hlec' h2) g' hg'.1
    have hg2 : |l g'| < |l g| + 1 := hg'.2
    have hz : |z.re| ≤ max |b| |a| := abs_le_max_abs_abs h1 h2
    have hE : ‖Complex.exp (s * z * l g')‖ ≤ Real.exp (s * max |b| |a| * (|l g| + 1)) := by
      rw [Complex.norm_exp, Complex.re_mul_ofReal, hre]
      apply Real.exp_le_exp.mpr
      calc s * z.re * l g' ≤ |s * z.re * l g'| := le_abs_self _
        _ = s * |z.re| * |l g'| := by rw [abs_mul, abs_mul, abs_of_pos hs]
        _ ≤ s * max |b| |a| * (|l g| + 1) := by gcongr
    rw [norm_smul]
    exact mul_le_mul hE hH (norm_nonneg _) (Real.exp_pos _).le
  · rw [eis_twist hl c ρ (fun x => s * z * η x) _ (s * z) (fun x => by push_cast; ring),
      ContinuousLinearMap.smul_apply, hw.eqR _ (by rw [hre]; exact hgtx _ hz) g w, smul_comm]
  · rw [eis_twist hl c ρ (fun x => β x - s * z * η' x) _ (s * z) (fun x => by push_cast; ring),
      ContinuousLinearMap.smul_apply, hw.eqL _ (by rw [hre]; exact hltx _ hz) g w]

theorem scale : PositivityTheory.RgEis.Scale := by
  intro G _ _ _ _ _ W _ _ _ K ρ _ _ Γ P P' c η η' β l s hs hl hW
  obtain ⟨R, D, Op, H, hw⟩ := hW
  exact ⟨_, _, _, _, wall_scale hs hl hw⟩

end GlobalTheory.CompanionTheory.RgEisScale
