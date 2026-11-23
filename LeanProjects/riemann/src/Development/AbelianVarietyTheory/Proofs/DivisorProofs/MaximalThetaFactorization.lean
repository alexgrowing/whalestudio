import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaxNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalThetaPolynomialDataStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ThetaRadZero

theorem radZero : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ N, GlobalTheory.ThetaFac.IsMaxTh B om (GlobalTheory.ThK.PolData B G.M) N → (∀ Ψ ∈ GlobalTheory.ThK.PolData B G.M, G.M.I om Ψ = 0 → Ψ ∈ N) → ∀ (f : SInf F (Fin a × Fin (a + a'))) (φ : ∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ), f ∈ G.M.Pol B.ψ B.emb → (∀ v, φ v ∈ SB _) → (∀ᶠ v in Filter.cofinite, φ v = G.M.vac v) → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∉ N → ∀ v : Pl F, ∃ P : Submodule ℂ ((Fin a × Fin (a + a') → Fv F v) → ℂ), Maximal (fun Q => GlobalTheory.Published.ThetaSub om v Q ∧ Q ≠ SB _) P ∧ φ v ∉ P := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' hT N hN hI f φ hf hφ hφc hn v
  classical
  have hP := GlobalTheory.ThK.Inhab.pairV hT
  have hA := GlobalTheory.T.theta_action_exists hKP.base
  have hstd : ∀ᶠ w in Filter.cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 :=
    (hφc.and hP.good.std).mono fun w hw => hw.1.trans hw.2
  obtain ⟨ρ, hρ, hρt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hstd
  let lin : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] Fn F a (a + a') :=
    { toFun := fun χ => tens (evFin F v) χ ρ
      map_add' := fun χ χ' => by funext x; simp [tens, add_mul]
      map_smul' := fun c χ => by funext x; simp [tens, mul_assoc] }
  have hlin : ∀ χ, lin χ = pure f (Function.update φ v χ) := fun χ => hρt χ
  have hupd : ∀ χ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ w, Function.update φ v χ w ∈ SB _ := by
    intro χ hχ w
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]; exact hχ
    · rw [Function.update_of_ne hw]; exact hφ w
  have hD : ∀ χ ∈ SB (Fin a × Fin (a + a') → Fv F v), lin χ ∈ PolData B G.M := by
    intro χ hχ
    rw [hlin]
    refine Submodule.subset_span ⟨f, hf, Function.update φ v χ, hupd χ hχ, ?_, rfl⟩
    filter_upwards [hφc, Filter.eventually_cofinite_ne v] with w hw hne
    rw [Function.update_of_ne hne]; exact hw
  have hRest : ∀ χ ∈ SB (Fin a × Fin (a + a') → Fv F v), Rest (evFin F v) χ ρ := fun χ hχ =>
    ⟨hρ, by rw [hρt]; exact GlobalTheory.TensUniq.pure_mem_schA f _ (hupd χ hχ) (GlobalTheory.PureFactor.update_eventually φ v χ hstd)⟩
  have h1V : (1 : UA σ G.V.J) ∈ UAt σ G.V (evFin F v) := by
    intro u _
    show u • (mat (1 : UA σ G.V.J) - 1) = 0
    have : mat (1 : UA σ G.V.J) = 1 := rfl
    rw [this, sub_self, smul_zero]
  have hex : ∀ h ∈ UAt σ G.W (evFin F v), ∀ χ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      ∃ χ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) χ χ₁ := by
    intro h hh χ hχ
    obtain ⟨χ₁, ⟨h1, h2⟩, -⟩ := (hA F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ hP v).1 1 h1V h hh χ hχ
    exact ⟨χ₁, h1, h2⟩
  have hact : ∀ g, ∀ χ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ χ₁, Acts (evFin F v) (om g) χ χ₁ →
      om g (lin χ) = lin χ₁ := fun g χ hχ χ₁ hA => hA ρ (hRest χ hχ)

  set D := PolData B G.M with hDdef
  set SBv := SB (Fin a × Fin (a + a') → Fv F v) with hSBv
  let St : Submodule ℂ (Fn F a (a + a')) → Prop :=
    fun P => ∀ h ∈ UAt σ G.W (evFin F v), ∀ Φ ∈ P, om (1, h) Φ ∈ P
  have hStN : St N := fun h hh Φ hΦ => hN.stab.fin v h hh Φ hΦ
  set M := N ⊔ SBv.map lin with hMdef
  have hMD : M ≤ D := sup_le hN.le (by rintro _ ⟨χ, hχ, rfl⟩; exact hD χ hχ)

  have hStImg : ∀ Q : Submodule ℂ ((Fin a × Fin (a + a') → Fv F v) → ℂ), Q ≤ SBv →
      (∀ h ∈ UAt σ G.W (evFin F v), ∀ χ ∈ Q, ∀ χ₁ ∈ SBv, Acts (evFin F v) (om (1, h)) χ χ₁ → χ₁ ∈ Q) →
      St (N ⊔ Q.map lin) := by
    intro Q hQ hQs h hh Φ hΦ
    obtain ⟨n, hn, y, ⟨χ, hχ, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hΦ
    obtain ⟨χ₁, hχ₁, hA₁⟩ := hex h hh χ (hQ hχ)
    rw [map_add, hact _ χ (hQ hχ) χ₁ hA₁]
    exact Submodule.add_mem_sup (hStN h hh n hn) ⟨χ₁, hQs h hh χ hχ χ₁ hχ₁ hA₁, rfl⟩
  have hStM : St M := hStImg SBv le_rfl (fun _ _ _ _ χ₁ hχ₁ _ => hχ₁)
  have hx : pure f φ ∈ M := by
    have e : lin (φ v) = pure f φ := by rw [hlin, Function.update_eq_self]
    rw [← e]
    exact Submodule.mem_sup_right ⟨φ v, hφ v, rfl⟩
  obtain ⟨Ph, hPhSt, hNPh, hPhM, hxPh, hPhmax⟩ := GlobalTheory.ThetaFacW.exists_max_not_mem St M N hStN le_sup_left
    (fun c hne hc hcs h hh Φ hΦ => by
      obtain ⟨P, hP, hΦP⟩ := (Submodule.mem_sSup_of_directed hne hc.directedOn).1 hΦ
      exact (Submodule.mem_sSup_of_directed hne hc.directedOn).2 ⟨P, hP, hcs P hP h hh Φ hΦP⟩)
    (fun N₁ N₂ h₁ h₂ _ _ h hh Φ hΦ => by
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hΦ
      rw [map_add]; exact Submodule.add_mem_sup (h₁ h hh y hy) (h₂ h hh z hz))
    (fun P hPSt hNP hPM => by
      obtain ⟨C, hCD, hCSt, hsup, hinf⟩ := GlobalTheory.T.maximal_theta_polynomial_data hKP F E σ B a a' G X om om' hT N hN hI v P hNP (hPM.trans hMD) hPSt
      refine ⟨C ⊓ M, fun h hh Φ hΦ => ⟨hCSt h hh Φ hΦ.1, hStM h hh Φ hΦ.2⟩, inf_le_right, ?_, ?_⟩
      · rw [← sup_inf_assoc_of_le C hPM, hsup]; exact inf_eq_right.2 hMD
      · rw [← inf_assoc, hinf]; exact inf_eq_left.2 le_sup_left)
    (pure f φ) hx hn

  set Pl := Ph.comap lin ⊓ SBv with hPl
  have hmemM : ∀ m ∈ M, ∃ n ∈ N, ∃ χ ∈ SBv, m = n + lin χ := by
    intro m hm
    obtain ⟨n, hn, y, ⟨χ, hχ, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hm
    exact ⟨n, hn, χ, hχ, rfl⟩
  have hPlSub : GlobalTheory.Published.ThetaSub om v Pl := by
    refine ⟨?_, inf_le_right, ?_⟩
    · rw [augAt, Submodule.span_le]
      rintro _ ⟨g, hg, χ, hχ, χ₁, hχ₁, hA₁, rfl⟩
      refine ⟨?_, Submodule.sub_mem _ hχ₁ hχ⟩
      show lin (χ₁ - χ) ∈ Ph
      rw [map_sub, ← hact _ χ hχ χ₁ hA₁]
      exact hNPh (hN.coinv.fin v g hg _ (hD χ hχ))
    · intro h hh χ hχ χ₁ hχ₁ hA₁
      refine ⟨?_, hχ₁⟩
      show lin χ₁ ∈ Ph
      rw [← hact _ χ hχ.2 χ₁ hA₁]
      exact hPhSt h hh _ hχ.1
  have hvPl : φ v ∉ Pl := fun h => hxPh (by
    have := h.1
    simpa [Submodule.mem_comap, hlin, Function.update_eq_self] using this)
  refine ⟨Pl, ⟨⟨hPlSub, fun e => hvPl (e ▸ hφ v)⟩, ?_⟩, hvPl⟩
  rintro Q ⟨hQ, hQne⟩ hPlQ
  have hQSB : Q ≤ SBv := hQ.2.1
  have hStQ := hStImg Q hQSB (fun h hh χ hχ χ₁ hχ₁ hA₁ => hQ.2.2 h hh χ hχ χ₁ hχ₁ hA₁)
  have hQM : N ⊔ Q.map lin ≤ M := sup_le_sup_left (Submodule.map_mono hQSB) _
  have hPhQ : Ph ≤ N ⊔ Q.map lin := by
    intro m hm
    obtain ⟨n, hn, χ, hχ, rfl⟩ := hmemM m (hPhM hm)
    have hχP : χ ∈ Pl := ⟨by
      show lin χ ∈ Ph
      have := Ph.sub_mem hm (hNPh hn)
      simpa using this, hχ⟩
    exact Submodule.add_mem_sup hn ⟨χ, hPlQ hχP, rfl⟩
  rcases hPhmax _ hPhQ hQM hStQ with e | e
  · intro χ hχ
    refine ⟨?_, hQSB hχ⟩
    show lin χ ∈ Ph
    rw [← e]; exact Submodule.mem_sup_right ⟨χ, hχ, rfl⟩
  · exfalso
    refine hQne (le_antisymm hQSB fun χ hχ => ?_)
    have hm : lin χ ∈ N ⊔ Q.map lin := e ▸ Submodule.mem_sup_right ⟨χ, hχ, rfl⟩
    obtain ⟨n, hn, y, ⟨χ', hχ', rfl⟩, hsum⟩ := Submodule.mem_sup.1 hm
    have hd : χ - χ' ∈ Pl := by
      refine ⟨?_, Submodule.sub_mem _ hχ (hQSB hχ')⟩
      show lin (χ - χ') ∈ Ph
      rw [map_sub, ← hsum, add_sub_cancel_right]
      exact hNPh hn
    simpa using Q.add_mem (hPlQ hd) hχ'

end GlobalTheory.ThetaRadZero

end
