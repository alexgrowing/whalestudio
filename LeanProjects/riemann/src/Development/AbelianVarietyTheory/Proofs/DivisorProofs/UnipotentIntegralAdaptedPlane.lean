import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftLeftInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilConvergenceOfKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFinitePureTensors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentFundamentalDomainConstantTermStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralInvariantFirstGroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentConstantTermThetaStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.CtLocFac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem I_mul_right {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : Rep σ X W)
    (Φ : (Fin n × Fin d → AF F) → ℂ) (h k : UA σ W.J) : M.I om Φ (h * k) = M.I om (om (1, k) Φ) h := by
  unfold Model.I theta
  congr 1
  funext g
  have e : ((g, h * k) : UA σ X.J × UA σ W.J) = (g, h) * (1, k) := by ext <;> simp
  rw [e, map_mul, Module.End.mul_apply]

theorem theta_add {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (om : Rep σ X W)
    (hpres : ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), om x Φ ∈ schA F (Fin n × Fin d))
    {Φ₁ Φ₂ : (Fin n × Fin d → AF F) → ℂ} (h₁ : Φ₁ ∈ schA F (Fin n × Fin d)) (h₂ : Φ₂ ∈ schA F (Fin n × Fin d))
    (g : UA σ X.J) (h : UA σ W.J) : theta om (Φ₁ + Φ₂) g h = theta om Φ₁ g h + theta om Φ₂ g h := by
  unfold theta thetaSum
  rw [map_add]
  exact (summable_of_mem_schA F (hpres _ _ h₁)).tsum_add (summable_of_mem_schA F (hpres _ _ h₂))

theorem theta_smul {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (om : Rep σ X W) (c : ℂ)
    (Φ : (Fin n × Fin d → AF F) → ℂ) (g : UA σ X.J) (h : UA σ W.J) : theta om (c • Φ) g h = c * theta om Φ g h := by
  unfold theta thetaSum
  rw [map_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  exact tsum_mul_left

theorem I_add {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : Rep σ X W)
    (hpres : ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), om x Φ ∈ schA F (Fin n × Fin d))
    (hconv : ∀ Φ ∈ schA F (Fin n × Fin d), M.Conv om Φ)
    {Φ₁ Φ₂ : (Fin n × Fin d → AF F) → ℂ} (h₁ : Φ₁ ∈ schA F (Fin n × Fin d)) (h₂ : Φ₂ ∈ schA F (Fin n × Fin d))
    (h : UA σ W.J) : M.I om (Φ₁ + Φ₂) h = M.I om Φ₁ h + M.I om Φ₂ h := by
  unfold Model.I
  simp only [theta_add om hpres h₁ h₂]
  exact integral_add (hconv Φ₁ h₁ h) (hconv Φ₂ h₂ h)

theorem I_smul {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : Rep σ X W) (c : ℂ)
    (Φ : (Fin n × Fin d → AF F) → ℂ) (h : UA σ W.J) : M.I om (c • Φ) h = c * M.I om Φ h := by
  unfold Model.I
  simp only [theta_smul]
  exact integral_const_mul c _

theorem tens_add {R κ : Type} (ev : AF F → R) (φ₁ φ₂ : (κ → R) → ℂ) (r : (κ → AF F) → ℂ) :
    tens ev (φ₁ + φ₂) r = tens ev φ₁ r + tens ev φ₂ r := by
  funext x; simp only [tens, Pi.add_apply, add_mul]

theorem tens_smul' {R κ : Type} (ev : AF F → R) (c : ℂ) (φ : (κ → R) → ℂ) (r : (κ → AF F) → ℂ) :
    tens ev (c • φ) r = c • tens ev φ r := by
  funext x; simp only [tens, Pi.smul_apply, smul_eq_mul, mul_assoc]

end GlobalTheory.CtLocFac

open GlobalTheory.CtLocFac in

theorem GlobalTheory.CtLocFac.fac : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ Φ ∈ PolData B G.M, ∀ (μ : Measure (unip σ G.W H')) (𝓕 : Set (unip σ G.W H')), μ.IsHaarMeasure → IsFundamentalDomain ((ratU σ G.W.J).subgroupOf (unip σ G.W H')) 𝓕 μ → μ 𝓕 = 1 → ∀ (v : Pl F) (g : UA σ G.W.J), ∃ (n : ℕ) (ψ : Fin n → (Fin a × Fin (a + a') → Fv F v) → ℂ) (ℓ : Fin n → ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ), (∀ j, ψ j ∈ SB (Fin a × Fin (a + a') → Fv F v)) ∧ (∀ j, augAt om v ≤ LinearMap.ker (ℓ j)) ∧ (∀ j, ∀ u ∈ unip σ G.W H', u ∈ UAt σ G.W (evFin F v) → ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, u)) φ φ₁ → ℓ j φ₁ = ℓ j φ) ∧ ∀ m ∈ UAt σ G.W (evFin F v), ∃ ψ₁ : Fin n → (Fin a × Fin (a + a') → Fv F v) → ℂ, (∀ j, ψ₁ j ∈ SB (Fin a × Fin (a + a') → Fv F v) ∧ Acts (evFin F v) (om (1, m)) (ψ j) (ψ₁ j)) ∧ GlobalTheory.CtTyp.ctf H' μ 𝓕 (G.M.I om Φ) (m * g) = ∑ j, ℓ j (ψ₁ j) := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH Φ hΦ μ 𝓕 hμ h𝓕 h1 v g
  classical
  have hV : IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) :=
    { base := hT.base, herm := hT.geo.hV, skew := hT.geo.hW, good := hT.geo.hM, hX := hT.chars.heckeβ,
      hW := GlobalTheory.ThKRatInv.isHecke_div hT.chars.heckeβ hT.chars.heckeα, resX := hT.chars.resβ,
      resW := GlobalTheory.ThKRatInv.resEtaPow_div hT.chars.resβ hT.chars.resα, weil := hT.weil }
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om :=
    hT.weil
  have hpres : ∀ x, ∀ Ψ ∈ schA F (Fin a × Fin (a + a')), om x Ψ ∈ schA F (Fin a × Fin (a + a')) :=
    fun x Ψ hΨ => hwp.isUSplitting.pres x Ψ hΨ
  have hineq : a + a' + 2 * min (a - G.p) G.p < 2 * a := by
    have e1 := hT.geo.eBig
    have e2 := hT.geo.lt
    have e3 : min (a - G.p) G.p ≤ G.p := min_le_right _ _
    omega
  have hconv : ∀ Ψ ∈ schA F (Fin a × Fin (a + a')), G.M.Conv om Ψ := fun Ψ hΨ =>
    ((GlobalTheory.T.weil_convergence_of_kernel hK F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ hV (Or.inl hineq)).1 Ψ hΨ).1
  have hInt := GlobalTheory.T.unipotent_fundamental_domain_constant_term hK F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH μ 𝓕 hμ h𝓕 h1
  have hInvV := GlobalTheory.T.theta_integral_invariant_first_group hK F E σ B a a' G X om om' hT
  have hInvN := GlobalTheory.T.unipotent_constant_term_theta hK F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH μ 𝓕 hμ h𝓕 h1
  have hΨ : om (1, g) Φ ∈ schA F (Fin a × Fin (a + a')) :=
    hpres _ _ (GlobalTheory.ThKRatInv.polData_le_schA B G.M hT.geo.hM hΦ)
  obtain ⟨T, m, f, φ, hSB, hstd, hsum⟩ := GlobalTheory.SchADecomp.exists_sum_pure F _ (om (1, g) Φ) hΨ
  have hev : ∀ i, ∀ᶠ w in Filter.cofinite, φ i w = Set.indicator {x | ∀ j, x j ∈ w.adicCompletionIntegers F} 1 :=
    fun i => (T.finite_toSet.eventually_cofinite_notMem).mono fun w hw => hstd i w hw
  choose r hr1 hr2 using fun i => GlobalTheory.PureFactor.exists_rest_factor v (f i) (φ i) (hev i)
  have hRest : ∀ i, ∀ φ' ∈ SB (Fin a × Fin (a + a') → Fv F v), Rest (evFin F v) φ' (r i) := fun i φ' hφ' =>
    ⟨hr1 i, by
      rw [hr2 i]
      refine GlobalTheory.TensUniq.pure_mem_schA (f i) _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually _ v φ' (hev i))
      by_cases hw : w = v
      · subst hw; rw [Function.update_self]; exact hφ'
      · rw [Function.update_of_ne hw]; exact hSB i w⟩
  have hdec : om (1, g) Φ = ∑ i, tens (evFin F v) (φ i v) (r i) := by
    rw [hsum]
    exact Finset.sum_congr rfl fun i _ => by rw [hr2 i, Function.update_eq_self]
  let Tct : ((Fin a × Fin (a + a') → AF F) → ℂ) → ℂ := fun Ψ => GlobalTheory.CtTyp.ctf H' μ 𝓕 (G.M.I om Ψ) 1
  have hTadd : ∀ Ψ₁ ∈ schA F (Fin a × Fin (a + a')), ∀ Ψ₂ ∈ schA F (Fin a × Fin (a + a')),
      Tct (Ψ₁ + Ψ₂) = Tct Ψ₁ + Tct Ψ₂ := by
    intro Ψ₁ h₁ Ψ₂ h₂
    simp only [Tct, GlobalTheory.CtTyp.ctf]
    simp only [I_add G.M om hpres hconv h₁ h₂]
    exact integral_add (hInt Ψ₁ h₁ 1) (hInt Ψ₂ h₂ 1)
  have hTsmul : ∀ (c : ℂ) Ψ, Tct (c • Ψ) = c * Tct Ψ := by
    intro c Ψ
    simp only [Tct, GlobalTheory.CtTyp.ctf, I_smul]
    exact integral_const_mul c _
  have hT0 : Tct 0 = 0 := by simpa using hTsmul 0 0
  let Lsub : Fin m → (SB (Fin a × Fin (a + a') → Fv F v)) →ₗ[ℂ] ℂ := fun i =>
    { toFun := fun φ' => Tct (tens (evFin F v) φ'.1 (r i))
      map_add' := fun x y => by
        simp only [Submodule.coe_add]
        rw [tens_add, hTadd _ (hRest i _ x.2).2 _ (hRest i _ y.2).2]
      map_smul' := fun c x => by
        simp only [SetLike.val_smul, RingHom.id_apply, smul_eq_mul]
        rw [tens_smul', hTsmul] }
  choose ℓ hℓe using fun i => LinearMap.exists_extend (Lsub i)
  have hℓ : ∀ i, ∀ φ' (h : φ' ∈ SB (Fin a × Fin (a + a') → Fv F v)), ℓ i φ' = Tct (tens (evFin F v) φ' (r i)) :=
    fun i φ' h => LinearMap.congr_fun (hℓe i) ⟨φ', h⟩
  refine ⟨m, fun i => φ i v, ℓ, fun i => hSB i v, ?_, ?_, ?_⟩
  · intro i
    refine Submodule.span_le.2 ?_
    rintro z ⟨g', hg', φ₀, hφ₀, φ₁, hφ₁, hact, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, hℓ i φ₁ hφ₁, hℓ i φ₀ hφ₀, ← hact (r i) (hRest i φ₀ hφ₀)]
    have e : G.M.I om (om (g', 1) (tens (evFin F v) φ₀ (r i))) = G.M.I om (tens (evFin F v) φ₀ (r i)) :=
      funext fun h => hInvV _ (hRest i φ₀ hφ₀).2 g' h
    simp only [Tct, e, sub_self]
  · intro i u hu _ φ₀ hφ₀ φ₁ hφ₁ hact
    rw [hℓ i φ₁ hφ₁, hℓ i φ₀ hφ₀, ← hact (r i) (hRest i φ₀ hφ₀)]
    simp only [Tct, GlobalTheory.CtTyp.ctf, mul_one]
    rw [← hInvN _ (hRest i φ₀ hφ₀).2 u hu]
    congr 1
    funext x
    exact (I_mul_right G.M om _ x.1 u).symm
  · intro mm hm
    have h1V : (1 : UA σ G.V.J) ∈ UAt σ G.V (evFin F v) := by
      intro u _
      show u • (mat (1 : UA σ G.V.J) - 1) = 0
      rw [show mat (1 : UA σ G.V.J) = 1 from rfl, sub_self, smul_zero]
    have hloc := fun i => ((GlobalTheory.T.theta_action_exists hK.base) F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ hV v).1
      1 h1V mm hm (φ i v) (hSB i v)
    choose ψ₁ hψ₁ _ using hloc
    refine ⟨ψ₁, fun i => hψ₁ i, ?_⟩
    have hmv : om (1, mm) (om (1, g) Φ) = ∑ i, tens (evFin F v) (ψ₁ i) (r i) := by
      rw [hdec, map_sum]
      exact Finset.sum_congr rfl fun i _ => (hψ₁ i).2 (r i) (hRest i _ (hSB i v))
    have hmem : ∀ i, tens (evFin F v) (ψ₁ i) (r i) ∈ schA F (Fin a × Fin (a + a')) := fun i => (hRest i _ (hψ₁ i).1).2
    have hsumT : ∀ s : Finset (Fin m), Tct (∑ i ∈ s, tens (evFin F v) (ψ₁ i) (r i)) =
        ∑ i ∈ s, Tct (tens (evFin F v) (ψ₁ i) (r i)) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp [hT0]
      | insert j s hj ih =>
        rw [Finset.sum_insert hj, Finset.sum_insert hj, hTadd _ (hmem j) _ (Submodule.sum_mem _ fun i _ => hmem i), ih]
    rw [Finset.sum_congr rfl fun i _ => hℓ i (ψ₁ i) (hψ₁ i).1, ← hsumT Finset.univ, ← hmv]
    simp only [Tct, GlobalTheory.CtTyp.ctf, mul_one]
    congr 1
    funext x
    rw [I_mul_right, show ((1, mm * g) : UA σ G.V.J × UA σ G.W.J) = (1, mm) * (1, g) by ext <;> simp, map_mul,
      Module.End.mul_apply]

end
