import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocallyCompactSecondCountableT2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainIntegralMulRight
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SobolevFormEqZeroOfSmoothOrbitStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GelfandInvariantActionSmoothVectorsScalarStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivariantMapCarriesGelfandInvariantToFunctionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteDimensionalKStableSmoothVectorsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurLemmaEquivariantPairBoundedFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqConstMulProdInnerOfSlotwiseStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory
  Matrix
open scoped TensorProduct InnerProductSpace Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MultFinite

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
  {S : D.what₂.Tau → SPar} {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ}

def pt (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (τ : D.what₂.Tau)
    (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : GA D V :=
  atTau θ V τ ((M.fr τ)⁻¹ * g * M.fr τ)

theorem mem_sm {τ : D.what₂.Tau} {w : M.H τ} :
    w ∈ M.sm τ ↔ w ∈ smSub (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) := by rw [sm_eq]

theorem sigma_mem_sm {τ : D.what₂.Tau} (w : M.sm τ) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ UJset (M.ε τ)) : M.σ τ g w ∈ M.sm τ :=
  mem_sm.2 (sigma_mem (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 (mem_sm.1 w.2) hg)

theorem map_sigma {T : MMap M} (hT : IsMultMap θ M J χ T) (τ : D.what₂.Tau) (v : M.Vec) (w : M.sm τ)
    {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : g ∈ UJset (M.ε τ)) :
    T (Function.update v τ ⟨M.σ τ g w, sigma_mem_sm w hg⟩) = rTr V (pt θ M τ g) (T (Function.update v τ w)) := by
  have := hT.equiv τ _ (conj_mem_UH (M.fr_unit τ) (M.fr_gram τ) hg) (Function.update v τ w)
    ⟨M.σ τ g w, sigma_mem_sm w hg⟩ (by
      rw [Function.update_self]
      exact (congrArg (fun L : M.H τ →L[ℂ] M.H τ => L w) (trRep_conj (σ := M.σ τ) (M.fr_unit τ) g)).symm)
  rwa [Function.update_idem] at this

theorem exists_continuousLinearMap_tens_update {T : MMap M} (hT : IsMultMap θ M J χ T) (τ : D.what₂.Tau) (v : M.Vec) :
    ∃ a : M.H τ →ₗ[ℂ] (GA D V → ℂ), (∀ w : M.sm τ, a w = T (Function.update v τ w)) ∧
      (∀ x, Sobolev₂ (lieG (gramAt D V τ)) (trRep (M.σ τ) (M.fr τ)) ((LinearMap.proj x).comp a)) ∧
      ∀ g ∈ UJset (M.ε τ), ∀ w ∈ smSub (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)),
        a (M.σ τ g w) = rTr V (pt θ M τ g) (a w) := by
  obtain ⟨a, ha⟩ := LinearMap.exists_extend (T.toLinearMap v τ)
  have ha' : ∀ w : M.sm τ, a w = T (Function.update v τ w) := fun w => LinearMap.congr_fun ha w
  refine ⟨a, ha', fun x => ?_, fun g hg w hw => ?_⟩
  · obtain ⟨ℓ, ⟨L, C, h1, h2⟩, e⟩ := hT.cont τ v x
    refine ⟨L, C, h1, fun w hw => ?_⟩
    have := h2 w hw
    rw [e ⟨w, mem_sm.2 hw⟩, ← ha'] at this
    exact this
  · rw [ha' ⟨w, mem_sm.2 hw⟩, ← map_sigma hT τ v _ hg, ← ha']

theorem eq_zero_of_apply {T : MMap M} (hT : IsMultMap θ M J χ T) (v₀ : M.Vec) (h₀ : ∀ τ, v₀ τ ≠ 0) (h : T v₀ = 0) :
    T = 0 := by
  have key : ∀ s : Finset D.what₂.Tau, ∀ v : M.Vec, (∀ ρ, ρ ∉ s → v ρ = v₀ ρ) → T v = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro v hv; rw [show v = v₀ from funext fun ρ => hv ρ (by simp), h]
    | insert τ s _ ih =>
      intro v hv
      have h2 : T (Function.update v τ (v₀ τ)) = 0 := by
        refine ih _ fun ρ hρ => ?_
        by_cases hh : ρ = τ
        · subst hh; simp
        · rw [Function.update_of_ne hh]; exact hv ρ (by simp [hh, hρ])
      obtain ⟨a, e, hs, hq⟩ := exists_continuousLinearMap_tens_update hT τ v
      have := (M.ds τ).1
      funext x
      have h3 := GlobalTheory.T.sobolevForm_eq_zero_of_smooth_orbit _ _ _ _ _ _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 (M.ds τ).2.2.2.1 _ (hs x)
        (v₀ τ) (mem_sm.1 (v₀ τ).2) (fun c => h₀ τ (Subtype.ext c)) (fun g hg => by
          show a _ x = 0
          rw [hq g hg _ (mem_sm.1 (v₀ τ).2), e, h2]
          rfl) (v τ) (mem_sm.1 (v τ).2)
      have h4 : a (v τ) x = 0 := h3
      rwa [e, Function.update_eq_self] at h4
  exact MultilinearMap.ext fun v => key Finset.univ v (by simp)

def kRep {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) (W : Submodule ℂ H)
    (hW : ∀ k ∈ Formalism.REAL.Kset ε, ∀ w ∈ W, σ k w ∈ W) : Representation ℂ (Formalism.REAL.KG ε) W where
  toFun k := (σ (Formalism.REAL.toMK k) : H →ₗ[ℂ] H).restrict fun w hw => hW _ k.2 w hw
  map_one' := by
    ext w
    show σ 1 w = w
    rw [hσ.1.1]; rfl
  map_mul' k k' := by
    ext w
    show σ (Formalism.REAL.toMK k * Formalism.REAL.toMK k') w = σ (Formalism.REAL.toMK k) (σ (Formalism.REAL.toMK k') w)
    rw [hσ.1.2 _ (k : Formalism.REAL.UJ ε).2 _ (k' : Formalism.REAL.UJ ε).2]; rfl

theorem isContRep_kRep {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) (W : Submodule ℂ H)
    [FiniteDimensional ℂ W] (hW : ∀ k ∈ Formalism.REAL.Kset ε, ∀ w ∈ W, σ k w ∈ W) :
    GlobalTheory.Published.AutFin.IsContRep (kRep hσ W hW) := fun ℓ w =>
  (LinearMap.continuous_of_finiteDimensional ℓ).comp
    (Continuous.subtype_mk ((continuous_orbit hσ w).comp continuous_subtype_val) _)

theorem hcFinite (hP : GlobalTheory.Published.HarishChandraFinite) : HCFinite θ M J χ := by
  rintro hθ ⟨U, hU, hUJ⟩
  have hc := fun τ => (M.ds τ).1
  choose W hWf hW0 hWs hWk using fun τ => GlobalTheory.T.exists_finiteDimensional_kStable_smoothVectors _ _ _ _ _ _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1
    ⟨_, (M.ds τ).2.2.2.2.2.1⟩
  choose c hcs using fun τ => GlobalTheory.T.gelfandInvariantAction_smoothVectors_scalar _ _ _ _ _ _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 (M.ds τ).2.2.2.1
  choose u huW hu0 using fun τ => (Submodule.ne_bot_iff _).1 (hW0 τ)
  let v₀ : M.Vec := fun τ => ⟨u τ, mem_sm.2 (hWs τ (huW τ))⟩
  have hfin := hP D θ hθ V U hU M.ε M.fr (fun τ => ⟨M.fr_unit τ, M.fr_gram τ⟩) (fun τ => W τ)
    (fun τ => kRep (M.ds τ).2.2.1 (W τ) (hWk τ)) (fun τ => isContRep_kRep _ _ _) c
  have hmem : ∀ T : Mult θ M J χ, (T : MMap M) v₀ ∈ GlobalTheory.Published.AutFin.forms θ V U M.ε M.fr
      (fun τ => kRep (M.ds τ).2.2.1 (W τ) (hWk τ)) c := by
    intro T
    have hT := (GlobalTheory.MultMem.mem_mult_iff D θ V S M J χ T).1 T.2
    refine ⟨hT.aut v₀, fun k hk hf g => ?_, fun τ => ?_, fun τ k => ?_⟩
    · rw [hT.lev v₀ k (hUJ k hk hf).1, (hUJ k hk hf).2, one_mul]
    · obtain ⟨a, e, -, hq⟩ := exists_continuousLinearMap_tens_update hT τ v₀
      have := GlobalTheory.Published.AutFin.hasTypeAt_of_map θ V τ (M.ε τ) (M.fr τ) (kRep (M.ds τ).2.2.1 (W τ) (hWk τ))
        (a.comp (W τ).subtype) (fun k w => hq (Formalism.REAL.toMK k) (GlobalTheory.LowTypeRestriction.kset_subset k.2) w (hWs τ w.2)) ⟨u τ, huW τ⟩
      have e' : (a.comp (W τ).subtype) ⟨u τ, huW τ⟩ = (T : MMap M) v₀ := by
        rw [← Function.update_eq_self τ v₀, ← e]; rfl
      rwa [e'] at this
    · rw [GlobalTheory.T.equivariant_map_carries_gelfandInvariant_to_function D θ V S M J χ hθ T hT τ k v₀ (c τ k • v₀ τ) (hcs τ k _ (mem_sm.1 (v₀ τ).2)).symm,
        MultilinearMap.map_update_smul, Function.update_eq_self]
  let ev : Mult θ M J χ →ₗ[ℂ] Submodule.span ℂ (GlobalTheory.Published.AutFin.forms θ V U M.ε M.fr
      (fun τ => kRep (M.ds τ).2.2.1 (W τ) (hWk τ)) c) :=
    { toFun := fun T => ⟨(T : MMap M) v₀, Submodule.subset_span (hmem T)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine FiniteDimensional.of_injective ev ((injective_iff_map_eq_zero ev).2 fun T hT => Subtype.ext ?_)
  exact eq_zero_of_apply ((GlobalTheory.MultMem.mem_mult_iff D θ V S M J χ T).1 T.2) v₀
    (fun τ h => hu0 τ (congrArg Subtype.val h)) (congrArg Subtype.val hT)

theorem schur_multMap (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) {μ : Measure (GA D V)} {𝓕 : Set (GA D V)}
    (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) {T T' : MMap M} (hT : IsMultMap θ M J χ T)
    (hT' : IsMultMap θ M J χ T') (τ : D.what₂.Tau) (v v' : M.Vec) :
    ∃ c : ℂ, ∀ w w' : M.sm τ,
      ∫ g in 𝓕, star (T (Function.update v τ w) g) * T' (Function.update v' τ w') g ∂μ = c * ⟪w, w'⟫_ℂ := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig V.gram
  have : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  have : SecondCountableTopology (GA D V) := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V).2.1
  have := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V μ hμ
  have : IsFiniteMeasure (μ.restrict 𝓕) :=
    isFiniteMeasure_restrict.2 (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V μ 𝓕 hμ h𝓕).ne
  have := (M.ds τ).1
  obtain ⟨a, e, hs, hq⟩ := exists_continuousLinearMap_tens_update hT τ v
  obtain ⟨a', e', hs', hq'⟩ := exists_continuousLinearMap_tens_update hT' τ v'
  have hpt : Continuous fun g : Formalism.REAL.UJ (M.ε τ) => pt θ M τ (umat g) :=
    (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ V τ).comp_continuous
      ((continuous_const.matrix_mul continuous_umat).matrix_mul continuous_const)
      fun g => conj_mem_UH (M.fr_unit τ) (M.fr_gram τ) g.2
  have hf : ∀ w ∈ smSub (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)), IsAutFunSm θ V (a w) ∧ IsCuspFun V (a w) :=
    fun w hw => by rw [e ⟨w, mem_sm.2 hw⟩]; exact ⟨hT.aut _, hT.cusp _⟩
  have hf' : ∀ w ∈ smSub (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)), IsAutFunSm θ V (a' w) ∧ IsCuspFun V (a' w) :=
    fun w hw => by rw [e' ⟨w, mem_sm.2 hw⟩]; exact ⟨hT'.aut _, hT'.cusp _⟩
  have hinv : ∀ (φ ψ : GA D V → ℂ) (k : GA D V), IsAutFunSm θ V φ → IsAutFunSm θ V ψ →
      ∫ x in 𝓕, star (rTr V k φ x) * rTr V k ψ x ∂μ = ∫ x in 𝓕, star (φ x) * ψ x ∂μ := fun φ ψ k hφ hψ =>
    (GlobalTheory.fundamentalDomain_integral_mul_right μ (GQ V) 𝓕 (fun x => star (φ x) * ψ x) k h𝓕 fun γ hγ g => by
      rw [hφ.left γ hγ, hψ.left γ hγ]).2
  obtain ⟨c, hc⟩ := GlobalTheory.T.schurLemma_equivariant_pair_boundedFunctions_alt _ _ _ _ _ _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 (M.ds τ).2.2.2.1 (GA D V)
    (μ.restrict 𝓕) (fun g x => x * pt θ M τ (umat g)) (continuous_snd.mul (hpt.comp continuous_fst)) a a'
    (fun w hw => ⟨(hf w hw).1.cont, GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ (hf w hw).1 (hf w hw).2,
      fun g x => congrFun (hq _ g.2 w hw) x⟩) hs
    (fun w hw => ⟨(hf' w hw).1.cont, GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ (hf' w hw).1 (hf' w hw).2,
      fun g x => congrFun (hq' _ g.2 w hw) x⟩) hs'
    (fun g hg u hu w hw => by rw [hq g hg u hu, hq g hg w hw]; exact hinv _ _ _ (hf u hu).1 (hf w hw).1)
    (fun g hg u hu w hw => by rw [hq' g hg u hu, hq' g hg w hw]; exact hinv _ _ _ (hf' u hu).1 (hf' w hw).1)
    (fun g hg u hu w hw => by rw [hq g hg u hu, hq' g hg w hw]; exact hinv _ _ _ (hf u hu).1 (hf' w hw).1)
  refine ⟨c, fun w w' => ?_⟩
  rw [← e, ← e']
  exact hc w (mem_sm.1 w.2) w' (mem_sm.1 w'.2)

theorem schurMult (hP : GlobalTheory.Published.CuspRapidDecay) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) :
    SchurMult θ M J χ μ 𝓕 := by
  intro hθ hμ h𝓕 T hT T' hT'
  rw [GlobalTheory.MultMem.mem_mult_iff] at hT hT'
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_eq_const_mul_prod_inner_of_slotwise' D.what₂.Tau (fun τ => M.sm τ) (fun v v' => ∫ g in 𝓕, star (T v g) * T' v' g ∂μ)
    fun τ v v' => schur_multMap hP hθ hμ h𝓕 hT hT' τ v v'
  exact ⟨c, fun v v' => ⟨GlobalTheory.CuspDecay.integrableOn_star_mul hP GlobalTheory.Mem.VolFin.finVol hθ μ 𝓕 hμ h𝓕 (hT.aut v)
    (hT'.aut v') (hT'.cusp v'), hc v v'⟩⟩

theorem hcFinite_and_schurMult : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay →
    ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (S : D.what₂.Tau → SPar)
      (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)),
      HCFinite θ M J χ ∧ SchurMult θ M J χ μ 𝓕 :=
  fun h h' _ _ _ _ _ _ _ μ 𝓕 => ⟨hcFinite h, schurMult h' μ 𝓕⟩

end GlobalTheory.MultFinite

end
