import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.RgEis PositivityTheory.RgEis.MG GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GodementSection

namespace GlobalTheory.CompanionTheory.EisCore

section Abstract

variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem avg_const_mul {K : Subgroup G} [MeasurableSpace K] (μ : Measure K) (ρ : K →* (W →L[ℂ] W)) (a : ℂ) (f : K → ℂ) :
    avg μ ρ (fun κ => a * f κ) = a • avg μ ρ f := by
  simp only [avg, mul_smul]
  exact integral_smul a _

theorem eis_const_smul (Γ K P : Subgroup G) (c : G → ℂ) (ρ : K →* (W →L[ℂ] W)) (Λ : G → ℂ) (g : G) (a : ℂ) (w : W) :
    eis Γ K P c ρ Λ g (a • w) = a • eis Γ K P c ρ Λ g w := by
  simp only [eis, map_smul]
  rw [← tsum_const_smul'']
  exact tsum_congr fun q => smul_comm _ _ _

theorem rep_mem {P Γ : Subgroup G} (q : Cos P Γ) : rep q ∈ Γ := (Quotient.out q).2

theorem ht_rep {Γ K : Subgroup G} {l : G → ℝ} (hl : IsHt Γ K ⊤ l) {P : Subgroup G} (q : Cos P Γ) (g : G) :
    l (rep q * g) = l g := by
  rw [hl.left _ (Subgroup.mem_top _), hl.rat _ (rep_mem q) (Subgroup.mem_top _), zero_add]

theorem eis_add_ht {Γ K : Subgroup G} {l : G → ℝ} (hl : IsHt Γ K ⊤ l) (P : Subgroup G) (c : G → ℂ)
    (ρ : K →* (W →L[ℂ] W)) (Λ : G → ℂ) (g : G) (w : W) :
    eis Γ K P c ρ (fun x => (l x : ℂ) + Λ x) g w = Complex.exp (l g) • eis Γ K P c ρ Λ g w := by
  simp only [eis]
  rw [← tsum_const_smul'']
  refine tsum_congr fun q => ?_
  rw [ht_rep hl, Complex.exp_add, mul_smul]

theorem conv_add_ht {Γ K : Subgroup G} {l : G → ℝ} (hl : IsHt Γ K ⊤ l) {P : Subgroup G} {f : G → ℝ}
    (h : Conv Γ P f) : Conv Γ P fun g => l g + f g := by
  intro g
  refine ((h g).mul_left (Real.exp (l g))).congr fun q => ?_
  show _ = Real.exp (l (rep q * g) + f (rep q * g))
  rw [ht_rep hl, Real.exp_add]

end Abstract

section ModPow

variable {k : Type} [Field k] [NumberField k]

theorem modPow_differentiable (x : IdeleGroup k) : Differentiable ℂ (modPow x) := by
  unfold modPow
  exact differentiable_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.2 (IdeleGroup.ideleModule k x).2.ne'))

theorem modPow_strip (x : IdeleGroup k) (b c : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, b ≤ z.re → z.re ≤ c → ‖modPow x z‖ ≤ M := by
  have hr : (0 : ℝ) < (IdeleGroup.ideleModule k x : ℝ) := (IdeleGroup.ideleModule k x).2
  set r : ℝ := (IdeleGroup.ideleModule k x : ℝ) with hrdef
  refine ⟨r ^ b + r ^ c, by positivity, fun z hb hc => ?_⟩
  have e : ‖modPow x z‖ = r ^ z.re := Complex.norm_cpow_eq_rpow_re_of_pos hr z
  rw [e]
  have h1 : 0 ≤ r ^ b := by positivity
  have h2 : 0 ≤ r ^ c := by positivity
  rcases le_total 1 r with h | h
  · have := Real.rpow_le_rpow_of_exponent_le h hc
    linarith
  · have := Real.rpow_le_rpow_of_exponent_ge hr h hb
    linarith

theorem polyEnt_mul_modPow (u : ℂ) (x : IdeleGroup k) {a : ℂ → ℂ} (ha : PolyEnt a) :
    PolyEnt fun z => u * modPow x z * a z := by
  refine ⟨((differentiable_const u).mul (modPow_differentiable x)).mul ha.1, fun b c => ?_⟩
  obtain ⟨M₁, h₁, hM₁⟩ := modPow_strip x b c
  obtain ⟨M₂, hM₂⟩ := ha.2 b c
  refine ⟨‖u‖ * M₁ * M₂, fun z hb hc => ?_⟩
  rw [norm_mul, norm_mul, mul_assoc (‖u‖ * M₁)]
  have := hM₂ z hb hc
  have := hM₁ z hb hc
  gcongr

end ModPow

section Fam

variable {G : Type} [Group G] [TopologicalSpace G] {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem polyFam_of {π : G →* GL ι 𝔸[k]} (hπ : Continuous π) {Ψ : (ι → 𝔸[k]) → ℂ} {ω : HeckeCharacter k}
    {F : ℂ → GL ι 𝔸[k] → ℂ} (h : IsEpCont Ψ ω F) (D : GL ι 𝔸[k]) :
    PolyFam fun z g => F z (π g * D) := by
  have hc : Continuous fun g => π g * D := hπ.mul continuous_const
  refine ⟨fun g => h.entire _, ?_, fun a b C hC => ?_⟩
  · exact h.cont.comp (continuous_fst.prodMk (hc.comp continuous_snd))
  · obtain ⟨M, hM⟩ := h.strip a b _ (hC.image hc)
    exact ⟨M, fun z h1 h2 g hg => hM z h1 h2 _ (Set.mem_image_of_mem _ hg)⟩

theorem leftFam_of {T : Type} [TopologicalSpace T] {t : ℂ → T → ℂ} (x : IdeleGroup k) (A B : ℂ) {N : ℝ} (hN : 3 / 2 ≤ N)
    (h1 : ∀ κ, DifferentiableOn ℂ (fun s => t s κ) {s | 1 < s.re})
    (h2 : ContinuousOn (fun y : ℂ × T => t y.1 y.2) ({s | 1 < s.re} ×ˢ Set.univ))
    (h3 : ∀ a b : ℝ, 1 < a → ∃ M : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ∀ κ, ‖t s κ‖ ≤ M) :
    LeftFam fun z κ => -A * ((N : ℂ) - z) * B * modPow x ((N : ℂ) - z) * t ((N : ℂ) - z) κ := by
  have hmaps : ∀ z : ℂ, z.re < 1 / 2 → 1 < ((N : ℂ) - z).re := fun z hz => by
    simp only [Complex.sub_re, Complex.ofReal_re]; linarith
  have hd : Differentiable ℂ fun z : ℂ => (N : ℂ) - z := by fun_prop
  have hp : Differentiable ℂ fun z : ℂ => -A * ((N : ℂ) - z) * B * modPow x ((N : ℂ) - z) :=
    (((differentiable_const _).mul hd).mul (differentiable_const _)).mul ((modPow_differentiable x).comp hd)
  refine ⟨fun κ => ?_, ?_, fun b c hc => ?_⟩
  · exact hp.differentiableOn.mul ((h1 κ).comp hd.differentiableOn fun z hz => hmaps z hz)
  · refine ContinuousOn.mul (hp.continuous.comp continuous_fst).continuousOn ?_
    refine h2.comp (f := fun y : ℂ × T => ((N : ℂ) - y.1, y.2)) (by fun_prop) fun y hy => ?_
    exact ⟨hmaps y.1 hy.1, Set.mem_univ _⟩
  · obtain ⟨M, hM⟩ := h3 (N - c) (N - b) (by linarith)
    obtain ⟨M₁, h₁, hM₁⟩ := modPow_strip x (N - c) (N - b)
    refine ⟨‖A‖ * (|N| + 1) * ‖B‖ * M₁ * |M|, fun z hb hcz κ => ?_⟩
    have hre : N - c ≤ ((N : ℂ) - z).re := by simp only [Complex.sub_re, Complex.ofReal_re]; linarith
    have hre' : ((N : ℂ) - z).re ≤ N - b := by simp only [Complex.sub_re, Complex.ofReal_re]; linarith
    have ht : ‖t ((N : ℂ) - z) κ‖ ≤ |M| := (hM _ hre hre' κ).trans (le_abs_self M)
    have hm := hM₁ _ hre hre'
    have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
    have hn : ‖(N : ℂ) - z‖ ≤ (|N| + 1) * (1 + ‖z‖) ^ 2 := by
      have e1 : ‖(N : ℂ) - z‖ ≤ |N| + ‖z‖ := by
        refine (norm_sub_le _ _).trans ?_
        simp
      have e0 : 0 ≤ |N| := abs_nonneg N
      nlinarith [mul_nonneg e0 hz0, mul_nonneg hz0 hz0, mul_nonneg e0 (mul_nonneg hz0 hz0)]
    simp only [norm_mul, norm_neg]
    calc ‖A‖ * ‖(N : ℂ) - z‖ * ‖B‖ * ‖modPow x ((N : ℂ) - z)‖ * ‖t ((N : ℂ) - z) κ‖
        ≤ ‖A‖ * ((|N| + 1) * (1 + ‖z‖) ^ 2) * ‖B‖ * M₁ * |M| := by gcongr
      _ = _ := by ring

end Fam

theorem wall_core : EpMain → DGood → Master → SideOf → Term → ZetaK → SideUnfold → SideConv → ZetaOne → Core := by
  intro hEp hDG hMa hSO hTe hZK hSU hSC hZ1 G _ _ _ _ _ W _ _ _ K ρ hK hρ _ _ μ hμ hP k _ _ ι _ _ π Γ i₀ i₁ ω d c η η' l hM
    Ψ Ψ₁ φ L J hΨ hΨ₁ hzt hne hL hJ
  haveI : Nonempty ι := ⟨i₀⟩
  obtain ⟨V, hV, hEk⟩ := hEp k
  obtain ⟨F, F', hF, hF', hFE, hval⟩ := hEk ι Ψ ω hΨ hM.sq
  obtain ⟨hS, hS', htr, hdet⟩ := hSO G K hK k ι π Γ i₀ i₁ ω d c η η' l hM
  obtain ⟨a₁, ha₁, ha₁eq⟩ := hZ1 k Ψ₁ ω hΨ₁ hM.sq
  have hΨh : GJMatrix.adelicFourierPi k Ψ ∈ GJMatrix.schwartzBruhatPi k ι :=
    GJMatrix.adelicFourierPi_mem_schwartzBruhatPi hΨ
  generalize hΨhd : GJMatrix.adelicFourierPi k Ψ = Ψh at hF' hval hΨh
  generalize hd' : (fun i => (d i)⁻¹ : ι → IdeleGroup k) = d' at hS' htr
  have hpar' : IsPar Γ K ((stab 𝔸[k] {i₁}ᶜ).comap π) c := hM.par'
  obtain ⟨Nr, hNr⟩ : ∃ Nr : ℝ, Nr = (Fintype.card ι : ℝ) := ⟨_, rfl⟩
  have hN2 : (2 : ℝ) ≤ Nr := by rw [hNr]; exact_mod_cast hM.two
  have hcast : ((Fintype.card ι : ℕ) : ℂ) = (Nr : ℂ) := by rw [hNr]; simp
  rw [← hNr]
  simp only [hcast] at hFE hval
  have hFeq : ∀ z : ℂ, Nr < z.re → ∀ m, F z m = z * (z - Nr) * epstein Ψ ω z m := fun z hz m => by
    rw [hF.eq z (hNr ▸ hz) m, hcast]
  have hF'eq : ∀ z : ℂ, Nr < z.re → ∀ m, F' z m = z * (z - Nr) * epstein Ψh ω z m := fun z hz m => by
    rw [hF'.eq z (hNr ▸ hz) m, hcast]
  have hlK : ∀ g (κ : K), l (g * κ) = l g := fun g κ => hM.htl.right g κ κ.2
  obtain ⟨u, hu⟩ : ∃ u : ℂ, u = (ω.toIdele (d i₀) : ℂ) := ⟨_, rfl⟩
  have hu0 : u ≠ 0 := by rw [hu]; exact Circle.coe_ne_zero _
  obtain ⟨A, hA⟩ : ∃ A : ℂ, A = modPow (Matrix.GeneralLinearGroup.det (dgl d)) 1 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℂ, B = (ω.toIdele (d' i₁) : ℂ) := ⟨_, rfl⟩
  let a : ℂ → ℂ := fun z => u * modPow (d i₀) z * a₁ z
  let Φ : ℂ → G → ℂ := fun z g => F z (π g * dgl d)
  let ζ : ℂ → K → ℂ := fun z κ => -A * ((Nr : ℂ) - z) * B * modPow (d' i₁) ((Nr : ℂ) - z) *
    zt (tInv.comp π) d' i₁ Ψh ω ((Nr : ℂ) - z) κ
  have hPE : PolyEnt a := polyEnt_mul_modPow u (d i₀) ha₁
  have hPF : PolyFam Φ := polyFam_of hM.cont hF (dgl d)
  obtain ⟨hz1, hz2, hz3⟩ := hZK G K hK k ι (tInv.comp π) Γ ((stab 𝔸[k] {i₁}ᶜ).comap π) i₁ ω d' c η' hS' Ψh hΨh
  have hLF : LeftFam ζ := leftFam_of (d' i₁) A B (by linarith) hz1 hz2 hz3
  have hLaw : ∀ z, Law K ((stab 𝔸[k] {i₁}ᶜ).comap π) c (ζ z) := fun z r κ hr => by
    have := (hTe G K hK k ι (tInv.comp π) Γ ((stab 𝔸[k] {i₁}ᶜ).comap π) i₁ ω d' c η' hS').2 Ψh ((Nr : ℂ) - z)
    have h2 : zt (tInv.comp π) d' i₁ Ψh ω ((Nr : ℂ) - z) ((r * κ : K) : G) = c r * zt (tInv.comp π) d' i₁ Ψh ω ((Nr : ℂ) - z) (κ : G) := this.2.1 r κ hr
    show _ * zt _ _ _ _ _ _ ((r * κ : K) : G) = c r * (_ * zt _ _ _ _ _ _ (κ : G))
    rw [h2]; ring
  have hconvR : ∀ x : ℝ, Nr < x → Conv Γ ((stab 𝔸[k] {i₀}).comap π) fun g => x * η g := fun x hx =>
    hSC G K hK k ι π Γ ((stab 𝔸[k] {i₀}).comap π) i₀ ω d c η hS x (hNr ▸ hx)
  have hconvL : ∀ x : ℝ, x < -Nr → Conv Γ ((stab 𝔸[k] {i₁}ᶜ).comap π) fun g => (l g + Nr * η' g) - x * η' g := fun x hx => by
    have h := conv_add_ht hM.htl (hSC G K hK k ι (tInv.comp π) Γ ((stab 𝔸[k] {i₁}ᶜ).comap π) i₁ ω d' c η' hS' (Nr - x) (by rw [← hNr]; linarith))
    convert h using 2
    ring
  obtain ⟨z₀, hz₀, ht₀⟩ := hne
  rw [← hNr] at hz₀
  have hne' : ∃ z, z ≠ (Nr : ℂ) ∧ a z ≠ 0 := by
    refine ⟨z₀, fun h => ?_, ?_⟩
    · rw [h, Complex.ofReal_re] at hz₀; exact lt_irrefl _ hz₀
    · have hre : 1 < z₀.re := by linarith
      have n0 : z₀ ≠ 0 := fun h => by rw [h] at hre; simp at hre; linarith
      have n1 : z₀ - 1 ≠ 0 := fun h => by
        rw [sub_eq_zero] at h; rw [h] at hre; simp at hre
      show u * modPow (d i₀) z₀ * a₁ z₀ ≠ 0
      rw [ha₁eq z₀ hre]
      exact mul_ne_zero (mul_ne_zero hu0 (modPow_ne_zero _ _)) (mul_ne_zero (mul_ne_zero n0 n1) ht₀)
  have hRight : ∀ z : ℂ, Nr < z.re → ∀ g (w : L), (z - 1) • avg μ ρ (fun κ => Φ z (g * κ)) (J w) =
      ((z - Nr) * a z) • eis Γ K ((stab 𝔸[k] {i₀}).comap π) c ρ (fun x => z * η x) g w := by
    intro z hz g w
    have hre : 1 < z.re := by linarith
    have e1 : (fun κ : K => Φ z (g * κ)) = fun κ : K => (z * (z - Nr)) * epstein Ψ ω z (π (g * κ) * dgl d) :=
      funext fun κ => hFeq z hz _
    have hU := hSU G W K ρ hK hρ μ hμ hP k ι π Γ ((stab 𝔸[k] {i₀}).comap π) i₀ ω d c η hS Ψ hΨ z (hNr ▸ hz) g (J w)
    have e2 : (fun κ : K => zt π d i₀ Ψ ω z κ) = fun κ => tate Ψ₁ ω z * φ κ := funext (hzt z)
    rw [e2, avg_const_mul, ContinuousLinearMap.smul_apply, hJ, eis_const_smul, ← hu] at hU
    rw [e1, avg_const_mul, ContinuousLinearMap.smul_apply, hU]
    simp only [smul_smul]
    congr 1
    show _ = (z - Nr) * (u * modPow (d i₀) z * a₁ z)
    rw [ha₁eq z hre]; ring
  have hLeft : ∀ z : ℂ, z.re < -Nr → ∀ g (w : W), avg μ ρ (fun κ => Φ z (g * κ)) w =
      z • eis Γ K ((stab 𝔸[k] {i₁}ᶜ).comap π) c ρ (fun x => ((l x + Nr * η' x : ℝ) : ℂ) - z * η' x) g (avg μ ρ (ζ z) w) := by
    intro z hz g w
    have hs : Nr < ((Nr : ℂ) - z).re := by
      simp only [Complex.sub_re, Complex.ofReal_re]; linarith
    have e1 : (fun κ : K => Φ z (g * κ)) = fun κ : K => (Complex.exp (l g) * A * (((Nr : ℂ) - z) * (-z))) *
        epstein Ψh ω ((Nr : ℂ) - z) ((tInv.comp π) (g * κ) * dgl d') := by
      funext κ
      show F z (π (g * κ : G) * dgl d) = _
      rw [hFE, hdet, htr, hF'eq _ hs, hlK, ← hA]
      ring
    have hU := hSU G W K ρ hK hρ μ hμ hP k ι (tInv.comp π) Γ ((stab 𝔸[k] {i₁}ᶜ).comap π) i₁ ω d' c η' hS' Ψh hΨh ((Nr : ℂ) - z) (hNr ▸ hs) g w
    have e2 : (fun x => ((l x + Nr * η' x : ℝ) : ℂ) - z * η' x) = fun x => (l x : ℂ) + ((Nr : ℂ) - z) * η' x := by
      funext x; push_cast; ring
    have e3 : ζ z = fun κ : K => (-A * ((Nr : ℂ) - z) * B * modPow (d' i₁) ((Nr : ℂ) - z)) *
        zt (tInv.comp π) d' i₁ Ψh ω ((Nr : ℂ) - z) κ := rfl
    rw [e1, avg_const_mul, ContinuousLinearMap.smul_apply, hU, e2, eis_add_ht hM.htl, e3, avg_const_mul,
      ContinuousLinearMap.smul_apply, eis_const_smul, ← hB]
    simp only [smul_smul]
    congr 1
    ring
  obtain ⟨Op, H, hWall, hH, O, hO, hOp⟩ := hMa G W K ρ hK hρ μ hμ hP Γ ((stab 𝔸[k] {i₀}).comap π) ((stab 𝔸[k] {i₁}ᶜ).comap π) c η η' (fun g => l g + Nr * η' g) L J Nr Nr Φ a ζ
    hpar' hL (by linarith) hconvR hconvL hPF hPE hne' hLF hLaw hRight hLeft
  refine ⟨Nr, fun z => (z - Nr) * (Complex.exp (z ^ 2) * a z), Op, H, hWall,
    ⟨fun z => Complex.exp (z ^ 2) * a z, (hDG a Nr hPE).1, fun z => rfl, fun ht => ?_⟩, ⟨O, hO, hOp⟩, fun hω => ?_⟩
  · have hre : 1 < ((Nr : ℂ)).re := by rw [Complex.ofReal_re]; linarith
    have n0 : (Nr : ℂ) ≠ 0 := by
      rw [Ne, Complex.ofReal_eq_zero]; linarith
    have n1 : (Nr : ℂ) - 1 ≠ 0 := by
      have : (Nr - 1 : ℝ) ≠ 0 := by linarith
      exact_mod_cast this
    show Complex.exp ((Nr : ℂ) ^ 2) * (u * modPow (d i₀) Nr * a₁ Nr) ≠ 0
    rw [ha₁eq _ hre]
    exact mul_ne_zero (Complex.exp_ne_zero _) (mul_ne_zero (mul_ne_zero hu0 (modPow_ne_zero _ _))
      (mul_ne_zero (mul_ne_zero n0 n1) ht))
  · have hv := hval hω
    have hav : ∀ (C : ℂ), avg μ ρ (fun _ : K => C) = C • avg μ ρ (fun _ => 1) := fun C => by
      have := avg_const_mul μ ρ C (fun _ => 1)
      simpa using this
    refine ⟨⟨-(Nr * V), ?_, fun g w => ?_⟩, ⟨Complex.exp ((Nr : ℂ) ^ 2) * ((Nr : ℂ) - 1) * (Nr * V * A * Ψh 0), fun g w => ?_⟩⟩
    · have : (Nr : ℂ) * V ≠ 0 := by
        have h1 : Nr * V ≠ 0 := by
          have := mul_pos (by linarith : (0 : ℝ) < Nr) hV
          exact this.ne'
        exact_mod_cast h1
      exact neg_ne_zero.2 this
    · rw [hH]
      have e1 : (fun κ : K => Φ 0 (g * κ)) = fun _ => (Nr : ℂ) * V * Ψ 0 := funext fun κ => (hv _).1
      rw [e1, hav, ContinuousLinearMap.smul_apply, smul_smul]
      congr 1
      simp
    · rw [hH]
      have e1 : (fun κ : K => Φ Nr (g * κ)) = fun _ => (Nr : ℂ) * V * (Complex.exp (l g) * A) * Ψh 0 := funext fun κ => by
        show F Nr (π (g * κ : G) * dgl d) = _
        rw [(hv _).2, hdet, hlK, ← hA]
      rw [e1, hav, ContinuousLinearMap.smul_apply, smul_smul]
      congr 1
      ring

end GlobalTheory.CompanionTheory.EisCore
