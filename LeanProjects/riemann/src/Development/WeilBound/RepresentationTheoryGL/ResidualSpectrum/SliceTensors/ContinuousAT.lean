import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PExpFin
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehDataUnique

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Polynomial Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin

namespace PositivityTheory.Rg.Rs

namespace PDich

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a N : ℕ}

open PExpFin in

theorem continuous_aT (F : Sm E N) (r : ℕ) (g : GA E N) : Continuous fun t : ℝ => F.1 (aT E N r t * g) := by
  set y := Matrix.GeneralLinearGroup.map (pInf E) g
  set k := Matrix.GeneralLinearGroup.map (pFin E) g
  have hg : g = infGL E N y * finGL E N k := (infGL_mul_finGL g).symm
  have e : ∀ t, aT E N r t * g = g * infGL E N (y⁻¹ * aInf E N r t * y) := by
    intro t
    calc aT E N r t * g = infGL E N (y * (y⁻¹ * aInf E N r t * y)) * finGL E N k := by
          rw [hg, aT, ← mul_assoc, ← map_mul]
          congr 2
          group
      _ = g * infGL E N (y⁻¹ * aInf E N r t * y) := by
          rw [hg, map_mul, mul_assoc, mul_assoc, infGL_comm, mul_assoc]
  have e2 : (fun t : ℝ => F.1 (aT E N r t * g)) =
      chart F.1 g ∘ fun t : ℝ => toL (y⁻¹ * aInf E N r t * y).val := by
    funext t
    rw [Function.comp_apply, chart_val, e]
  rw [e2]
  refine (F.2 g).continuousOn.comp_continuous ?_ fun t => val_mem_invSet _
  change Continuous fun t : ℝ => (y⁻¹).val * Matrix.diagonal (fun (i : Fin N) (_ : InfinitePlace E) =>
    Complex.exp (if (i : ℕ) < r then (t : ℂ) else 0)) * y.val
  have hi : ∀ (i : Fin N) (t : ℝ), (if (i : ℕ) < r then (t : ℂ) else 0) = (if (i : ℕ) < r then 1 else 0) * t := by
    intro i t
    split_ifs <;> simp
  simp_rw [hi]
  fun_prop

theorem ascEmb_one {π π' : CuspSub E a} (h : π.Iso π') : AscEmb π.V π' 1 := by
  obtain ⟨T, hT⟩ := h
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl π.V
  let P := Submodule.projectionOnto π.V q hq
  have hP : ∀ φ (hφ : φ ∈ π.V), P φ = ⟨φ, hφ⟩ := fun φ hφ =>
    Submodule.projectionOnto_apply_left hq ⟨φ, hφ⟩
  have hs : ∑ _ : Fin 1, a = a := by simp
  refine ⟨hs, fun _ => 1, fun i => ?_, π'.V.subtype ∘ₗ T.toLinearMap ∘ₗ P, fun φ hφ => ?_, fun φ hφ h0 => ?_,
    fun o φ hφ => ?_⟩
  · have e : -spehExp 1 i + a * spehExp 1 i = 0 := by simp [spehExp]
    rw [e]
    exact ⟨fun _ _ _ => rfl, fun _ => by simp [HChar.val, HChar.locK], fun _ => by simp [HChar.inf]⟩
  · rw [show (fun _ : Fin 1 => π'.twist 1) = fun _ => π' from funext fun _ => π'.twist_one, indForms_one]
    exact (T (P φ)).2
  · simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe, hP φ hφ] at h0
    have h1 : T ⟨φ, hφ⟩ = 0 := Subtype.ext h0
    have h2 : (⟨φ, hφ⟩ : π.V) = 0 := T.injective (h1.trans T.map_zero.symm)
    exact congrArg Subtype.val h2
  · simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
      hP φ hφ, hP _ (π.stable o φ hφ)]
    have e : (⟨act o φ, π.stable o φ hφ⟩ : π.V) = π.op o ⟨φ, hφ⟩ := rfl
    rw [e, hT]
    rfl

end PDich

open PExpFin PDich in
theorem dich_of (hD : Dict) (hT : FinTr) (hK : KillPoly) : Dich := by
  intro E _ _ _ N hN V hV
  obtain ⟨-, -, -, hDct⟩ := hD E N
  by_cases hex : ∃ r, 0 < r ∧ r < N ∧ ∃ φ ∈ V, An.ctn r φ.1 ≠ 0
  · right
    obtain ⟨r, hr, hrN, φ, hφ, hne⟩ := hex
    obtain ⟨hct, -⟩ := hDct φ (hV.aut φ hφ) r hr hrN
    have hcont : ∀ g, Continuous fun t => An.ctn r φ.1 (aT E N r t * g) := by
      let _ : MeasurableSpace (BlockIx N r → Ad E) := _root_.borel _
      have _ : BorelSpace (BlockIx N r → Ad E) := ⟨rfl⟩
      obtain ⟨μ, 𝓕, hμ, h𝓕, e⟩ := hct
      obtain ⟨F, hF, -⟩ := GlobalTheory.CompanionTheory.CTSmooth.ct_smooth E N r φ (hV.aut φ hφ).left (hV.aut φ hφ).level μ 𝓕 hμ h𝓕
      have e2 : An.ctn r φ.1 = F.1 := e.trans (funext fun g => (hF g).symm)
      intro g
      rw [e2]
      exact PDich.continuous_aT F r g
    obtain ⟨p, hp, hk, hroot⟩ := hK (GA E N) (aT E N r) (An.ctn r φ.1) (fun u v => aT_add r u v) hcont
      (hT E N φ (hV.aut φ hφ) r hr hrN _ hct)
    have hdeg : 0 < p.degree := hp.degree_pos.2 fun h1 => hne (funext fun g => by
      have := hk g
      rw [h1] at this
      simpa [aT_zero] using this)
    obtain ⟨z, hz⟩ := Complex.exists_root hdeg
    obtain ⟨c, -, F, hF, hF0, hFe⟩ := hroot z hz
    exact ⟨r, hr, hrN, c, φ, hφ, An.ctn r φ.1, hct, F, hF, hF0, hFe⟩
  · left
    push Not at hex
    have hcusp : ∀ φ ∈ V, IsCuspForm φ := fun φ hφ => ⟨hV.aut φ hφ, by
      intro r hr hrN inst1 inst2 μ 𝓕 hμ hF g
      obtain rfl : inst1 = _root_.borel _ := inst2.measurable_eq
      obtain ⟨c, -, e⟩ := (hDct φ (hV.aut φ hφ) r hr hrN).2 _ ⟨μ, 𝓕, hμ, hF, rfl⟩
      have := congrFun e g
      rw [hex r hr hrN φ hφ] at this
      simpa [PositivityTheory.Affgl.CT.ct] using this⟩
    let π : CuspSub E N := ⟨V, hcusp, hV.stable, hV.ne_bot, hV.irred⟩
    have hn : IsNormalised π := fun φ hφ => (hV.sqInt φ hφ).1
    exact ⟨π, GlobalTheory.SpehPair.isUnitary_of_isNormalised hn, hn, fun π' hiso => ascEmb_one hiso⟩

end PositivityTheory.Rg.Rs

end
