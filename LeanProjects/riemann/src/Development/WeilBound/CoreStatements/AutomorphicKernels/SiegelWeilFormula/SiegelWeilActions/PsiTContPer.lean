import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PadZeroMemNilradical
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ParabolicUnipotents

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Act.C4

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ} (L : LD d)

instance countableCs (d : SD σ) : Countable (Cs d) := by
  have : Countable (rat2 σ d.Y) := GlobalTheory.EisBL.DoubledGroupTopology.countable_rational_points_doubled σ d.Y
  infer_instance

theorem cont_E {s₁ z : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f)
    (hmaj : ∀ C : Set d.G, IsCompact C → ∃ u : GlobalTheory.Eis.Cosets (par2 σ d.Y) (rat2 σ d.Y) → ℝ, Summable u ∧ ∀ g ∈ C, ∀ q,
      ‖GlobalTheory.Eis.term (par2 σ d.Y) (rat2 σ d.Y) (fun x => ((d.Ht x : ℝ) : ℂ) ^ (z - s₁) * f x) g q‖ ≤ u q)
    {nb' : nA σ L.Y L.b → G2 σ L.Y} (hnb' : IsNMap L.b nb') (x : d.G) :
    Continuous fun β' : nA σ L.Y L.b => ∑' q' : Cs L.sd, phz d f s₁ z (L.j (rep q' * nb' β') * x) := by
  obtain ⟨e, he⟩ := cos_bij L
  have hphz : Continuous (phz d f s₁ z) := by
    rw [phz_eq_flat]
    exact continuous_flat hf.cont (kunf.continuous_a d) (kunf.a_pos d) z
  have hg : Continuous fun β' : nA σ L.Y L.b => L.j (nb' β') * x :=
    (L.cont.comp (kunf.continuous_nb hnb')).mul continuous_const
  have hterm : ∀ q' β', phz d f s₁ z (L.j (rep q' * nb' β') * x) =
      phz d f s₁ z (rep (e q').1 * (L.j (nb' β') * x)) := by
    intro q' β'
    obtain ⟨p₀, hp₀, hr₀, hrep⟩ := he q'
    rw [hrep, mul_assoc, phz_rat hf z hp₀ hr₀, map_mul, mul_assoc]
  refine continuous_iff_continuousAt.2 fun β₀ => ?_
  obtain ⟨C, hCc, hC⟩ := exists_compact_mem_nhds (L.j (nb' β₀) * x)
  obtain ⟨u, hu, hbd⟩ := hmaj C hCc
  have hN : (fun β' : nA σ L.Y L.b => L.j (nb' β') * x) ⁻¹' C ∈ 𝓝 β₀ := hg.continuousAt.preimage_mem_nhds hC
  refine (continuousOn_tsum (u := u ∘ Subtype.val ∘ e) (fun q' => ?_) (hu.comp_injective
    (Subtype.val_injective.comp e.injective)) (fun q' β' hβ' => ?_)).continuousAt hN
  · exact (hphz.comp ((L.cont.comp (continuous_const.mul (kunf.continuous_nb hnb'))).mul continuous_const)).continuousOn
  · rw [hterm]
    exact hbd _ hβ' _

theorem per_E {s₁ z : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) {nb' : nA σ L.Y L.b → G2 σ L.Y} (hnb' : IsNMap L.b nb')
    (x : d.G) (β₀ : nA σ L.Y L.b) (h₀ : β₀ ∈ nF σ L.Y L.b) (β' : nA σ L.Y L.b) :
    ∑' q' : Cs L.sd, phz d f s₁ z (L.j (rep q' * nb' (β₀ + β')) * x) =
      ∑' q' : Cs L.sd, phz d f s₁ z (L.j (rep q' * nb' β') * x) := by
  have hinv : GlobalTheory.AutomorphicL2Unitary.LeftInv (par2 σ L.Y ⊓ rat2 σ L.Y) (fun y : G2 σ L.Y => phz d f s₁ z (L.j y * x)) := by
    intro γ hγ g
    simp only [map_mul, mul_assoc]
    exact phz_rat hf z (j_par L (Subgroup.mem_inf.1 hγ).1) (j_rat L (Subgroup.mem_inf.1 hγ).2) _
  have h := GlobalTheory.Eis.leftInv_cosetSum hinv (nb' β₀) (kunf.nb_rat hnb' h₀) (nb' β')
  simp only [GlobalTheory.Eis.cosetSum, GlobalTheory.Eis.term] at h
  rw [kunf.nb_add hnb']
  exact h

theorem psiT_cont_per (T' : nF σ L.Y L.b) :
    Continuous (fun β' : nA σ L.Y L.b => d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T'.1.1 * β'.1))))) ∧
    ∀ β₀ ∈ nF σ L.Y L.b, ∀ β' : nA σ L.Y L.b,
      d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T'.1.1 * (β₀ + β').1)))) =
        d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T'.1.1 * β'.1)))) := by
  have hstd := d.ok.good.std
  refine ⟨?_, fun β₀ h₀ β' => ?_⟩
  · have : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
    have htr : Continuous (Algebra.trace (AF F) (AE F E)) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF F) (AE F E))
    exact hstd.1.comp (htr.comp ((continuous_const.matrix_mul continuous_subtype_val).matrix_trace)).neg
  · have h1 := kunf.psi_rat hstd T' ⟨β₀, h₀⟩
    rw [AddSubgroup.coe_add, Matrix.mul_add, Matrix.trace_add, map_add, neg_add, AddChar.map_add_eq_mul,
      AddChar.map_neg_eq_inv, h1, inv_one, one_mul]

theorem firstEq_of : AbsConv → FirstEq := by
  intro hA F E _ _ _ _ _ σ d L s₁ f hf he
  obtain ⟨t₁, ht₁⟩ := hA F E σ d L s₁ f hf he
  obtain ⟨U, p, Ê, t₂, -, -, -, -, -, -, -, hmaj⟩ := he 0
  refine ⟨max t₁ t₂, fun z hz nb lam 𝓖 hc hGc nb' lam' 𝓖' hc' hGc' uM ν 𝓤 hU hUc T T' hT x => ?_⟩
  have hz₁ : t₁ < z.re := lt_of_le_of_lt (le_max_left _ _) hz
  have hz₂ : t₂ < z.re := lt_of_le_of_lt (le_max_right _ _) hz
  obtain ⟨hint, hsum⟩ := ht₁ z hz₁ nb lam 𝓖 hc hGc uM ν 𝓤 hU hUc T x
  obtain ⟨e, he'⟩ := cos_bij L
  haveI : IsFiniteMeasure (lam.restrict 𝓖) := ⟨by rw [Measure.restrict_apply_univ, hc.2.2.2]; exact ENNReal.one_lt_top⟩
  haveI : IsFiniteMeasure (ν.restrict 𝓤) := ⟨by rw [Measure.restrict_apply_univ, hU.2.2.2]; exact ENNReal.one_lt_top⟩
  set ψT : nA σ L.Y L.b → ℂ := fun β' => d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T'.1.1 * β'.1))))
    with hψT
  set H : Cs L.sd → nA σ L.Y L.b → ℂ := fun q' β' => phz d f s₁ z (L.j (rep q' * nb' β') * x) * ψT β' with hH
  have hpt : ∀ q' (pr : (Fin L.n → AE F E) × nA σ d.Y d.b),
      kq L f s₁ z nb T uM (rep (e q').1) x pr = H q' (prj L pr.2) := by
    rintro q' ⟨u, β⟩
    obtain ⟨p₀, hp₀, hr₀, hrep⟩ := he' q'
    obtain ⟨p₁, t, hp₁, hdet, hid⟩ := key_id L hc.1 hc'.1 hU (rep q') β u x
    simp only [kq, hH, hψT]
    rw [hrep, mul_assoc, phz_rat hf z hp₀ hr₀, hid, phz_par hf z hp₁ hdet, tr_sub L hT β]
  have hν1 : (ν.restrict 𝓤).real Set.univ = 1 := by
    simp [Measure.real, hU.2.2.2]
  have hkq : ∀ q', kq L f s₁ z nb T uM (rep (e q').1) x = fun pr => H q' (prj L pr.2) := fun q' => funext (hpt q')
  have htm : ∀ q', tm L f s₁ z nb lam 𝓖 T uM ν 𝓤 (rep (e q').1) x = ∫ β in 𝓖, H q' (prj L β) ∂lam := by
    intro q'
    have h1 : ∀ u, fc d.B.ψ d.b nb lam 𝓖 (fun g => phz d f s₁ z (rep (e q').1 * g)) T (uM u * x) =
        ∫ β in 𝓖, H q' (prj L β) ∂lam := by
      intro u
      refine integral_congr_ae (Filter.Eventually.of_forall fun β => ?_)
      exact hpt q' (u, β)
    simp only [tm, h1]
    rw [setIntegral_const]
    simp [Measure.real, hU.2.2.2]
  have hint' : ∀ q', Integrable (fun β => H q' (prj L β)) (lam.restrict 𝓖) := by
    intro q'
    have h1 := (hint (e q').1).integral_prod_right
    rw [hkq] at h1
    simpa only [integral_const, hν1, one_smul] using h1
  have hnorm : ∀ q', ∫ pr, ‖kq L f s₁ z nb T uM (rep (e q').1) x pr‖ ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖)) =
      ∫ β in 𝓖, ‖H q' (prj L β)‖ ∂lam := by
    intro q'
    have hI := (hint (e q').1).norm
    rw [integral_prod _ hI]
    simp only [hkq, integral_const, hν1, one_smul]
  have hsum' : Summable fun q' => ∫ β in 𝓖, ‖H q' (prj L β)‖ ∂lam := by
    have h2 := hsum.comp_injective (Subtype.val_injective.comp e.injective)
    exact h2.congr fun q' => hnorm q'
  set G : nA σ L.Y L.b → ℂ := fun β' => (∑' q' : Cs L.sd, phz d f s₁ z (L.j (rep q' * nb' β') * x)) * ψT β' with hG
  have hHG : ∀ β', ∑' q', H q' β' = G β' := fun β' => tsum_mul_right
  have hGc : Continuous G := by
    refine (cont_E L hf (hmaj z hz₂).1 hc'.1 x).mul (psiT_cont_per L T').1
  have hGp : ∀ β₀ ∈ nF σ L.Y L.b, ∀ β', G (β₀ + β') = G β' := by
    intro β₀ h₀ β'
    simp only [hG, hψT]
    rw [per_E L hf hc'.1 x β₀ h₀ β', (psiT_cont_per L T').2 β₀ h₀ β']
  calc ∑' q : {q : Cs d // LagrangianCondition L (rep q)}, tm L f s₁ z nb lam 𝓖 T uM ν 𝓤 (rep q.1) x
      = ∑' q', tm L f s₁ z nb lam 𝓖 T uM ν 𝓤 (rep (e q').1) x :=
        (e.tsum_eq (fun q => tm L f s₁ z nb lam 𝓖 T uM ν 𝓤 (rep q.1) x)).symm
    _ = ∑' q', ∫ β in 𝓖, H q' (prj L β) ∂lam := tsum_congr htm
    _ = ∫ β in 𝓖, ∑' q', H q' (prj L β) ∂lam := by
        haveI : Countable (Cs L.sd) := countableCs L.sd
        exact integral_tsum_of_summable_integral_norm hint' hsum'
    _ = ∫ β in 𝓖, G (prj L β) ∂lam := by simp only [hHG]
    _ = ∫ β' in 𝓖', G β' ∂lam' := fiber L hc hc' G hGc hGp
    _ = first L f s₁ z nb' lam' 𝓖' T' x := by
        simp only [first, fc, GlobalTheory.Eis.cosetSum, GlobalTheory.Eis.term, mul_one, hG, hψT]
        rfl

end PositivityTheory.SiegelWeilFormula.Act.C4

namespace PositivityTheory.SiegelWeilFormula.Act

theorem firstEq : FirstEq := C4.firstEq_of absConv

end PositivityTheory.SiegelWeilFormula.Act

end
