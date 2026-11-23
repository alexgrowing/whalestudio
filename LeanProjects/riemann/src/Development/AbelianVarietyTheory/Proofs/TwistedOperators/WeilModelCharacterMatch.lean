import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsPairReading
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSubgroupsActOnFockVectorsAllSignatures
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubstitutionTotalDegreeLe
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTransformDarbouxModelLinearInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasArchimedeanCharExponentsConjOfHasInfExp
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ContinuousSplitInv
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ExistsExpEqOfMemKset
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ConjTransposeEqOfInG

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.CompactStable

theorem hasDerivAt_linear {X E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (U : Submodule ℂ (X → ℂ))
    [FiniteDimensional ℂ U] (φ : (X → ℂ) →ₗ[ℂ] E) {u : ℝ → X → ℂ} {u' : X → ℂ} {t : ℝ} (hu : ∀ s, u s ∈ U) (hu' : u' ∈ U)
    (hd : ∀ z, HasDerivAt (fun s => u s z) (u' z) t) : HasDerivAt (fun s => φ (u s)) (φ u') t := by
  rw [hasDerivAt_iff_tendsto_slope]
  have h1 : Filter.Tendsto (slope u t) (nhdsWithin t {t}ᶜ) (nhds u') := by
    rw [tendsto_pi_nhds]
    intro z
    exact hasDerivAt_iff_tendsto_slope.1 (hd z)
  have hm : ∀ s, slope u t s ∈ U := fun s => U.smul_of_tower_mem _ (U.sub_mem (hu s) (hu t))
  have h2 : Filter.Tendsto (fun s => (⟨slope u t s, hm s⟩ : U)) (nhdsWithin t {t}ᶜ) (nhds ⟨u', hu'⟩) :=
    tendsto_subtype_rng.2 h1
  have h3 := ((φ ∘ₗ U.subtype).continuous_of_finiteDimensional.tendsto _).comp h2
  refine h3.congr fun s => ?_
  simp [slope, LinearMap.map_smul_of_tower]

theorem oneParam_stable {X Q : Type} [AddCommGroup Q] [Module ℂ Q] (ι : Q →ₗ[ℂ] (X → ℂ)) (hι : Function.Injective ι)
    (V N : Submodule ℂ Q) [FiniteDimensional ℂ V] (ρ : ℝ → Module.End ℂ (X → ℂ)) (h0 : ρ 0 = 1)
    (hadd : ∀ s t, ρ (s + t) = ρ s * ρ t) (hV : ∀ t, ∀ P ∈ V, ∃ P' ∈ V, ρ t (ι P) = ι P') (L : Module.End ℂ Q)
    (hL : ∀ P z, HasDerivAt (fun t => ρ t (ι P) z) (ι (L P) z) 0) (hN : ∀ P ∈ N, L P ∈ N) (t : ℝ) :
    ∀ P ∈ N, P ∈ V → ∃ P' ∈ N, ρ t (ι P) = ι P' := by
  intro P hPN hPV
  obtain ⟨g, hg⟩ := ι.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hι)
  have hg' : ∀ P, g (ι P) = P := fun P => LinearMap.congr_fun hg P

  have der : ∀ {n : ℕ} (φ : Q →ₗ[ℂ] (Fin n → ℂ)), ∀ R ∈ V, HasDerivAt (fun s => φ (g (ρ s (ι R)))) (φ (L R)) 0 := by
    intro n φ R hR
    have := hasDerivAt_linear (V.map ι ⊔ Submodule.span ℂ {ι (L R)}) (φ ∘ₗ g) (u := fun s => ρ s (ι R)) (u' := ι (L R))
      (fun s => by
        obtain ⟨R', h1, h2⟩ := hV s R hR
        exact Submodule.mem_sup_left ⟨R', h1, h2.symm⟩)
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)) (hL R)
    simpa only [LinearMap.comp_apply, hg'] using this
  have hLV : ∀ R ∈ V, L R ∈ V := by
    intro R hR
    by_contra hne
    obtain ⟨f, hf1, hf2⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hne inferInstance
    have h1 := der (LinearMap.pi fun _ : Fin 1 => f) R hR
    have h2 : (fun s => (LinearMap.pi fun _ : Fin 1 => f) (g (ρ s (ι R)))) = fun _ => 0 := by
      funext s i
      obtain ⟨R', h1, h2⟩ := hV s R hR
      rw [h2, hg']
      exact (Submodule.mem_bot ℂ).1 (hf2 ▸ Submodule.mem_map_of_mem h1)
    rw [h2] at h1
    exact hf1 (congrFun (h1.unique (hasDerivAt_const _ _)) 0)
  let N' : Submodule ℂ V := N.comap V.subtype
  let L' : V →ₗ[ℂ] V := L.restrict hLV
  have hN' : N' ≤ N'.comap L' := fun x hx => hN _ hx
  let e := (Module.finBasis ℂ (V ⧸ N')).equivFun
  let A := (e.toLinearMap ∘ₗ N'.mapQ N' L' hN' ∘ₗ e.symm.toLinearMap).toContinuousLinearMap
  obtain ⟨π, hπ⟩ := (e.toLinearMap ∘ₗ N'.mkQ).exists_extend
  have hπ' : ∀ x : V, π x = e (N'.mkQ x) := fun x => LinearMap.congr_fun hπ x
  have hA : ∀ R ∈ V, π (L R) = A (π R) := by
    intro R hR
    rw [hπ' ⟨R, hR⟩, hπ' ⟨L R, hLV R hR⟩]
    simp [A, L']
    rfl
  have hw : ∀ s, HasDerivAt (fun s => π (g (ρ s (ι P)))) (A (π (g (ρ s (ι P))))) s := by
    intro s
    obtain ⟨R, h1, h2⟩ := hV s P hPV
    have h3 := der π R h1
    rw [h2, hg', ← hA R h1]
    have h4 : HasDerivAt (fun r => π (g (ρ (r - s) (ι R)))) (π (L R)) s := by
      have h5 : HasDerivAt (fun r => π (g (ρ r (ι R)))) (π (L R)) (s - s) := by rwa [sub_self]
      exact h5.comp_sub_const s s
    refine h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => ?_)
    simp only [← h2, ← Module.End.mul_apply, ← hadd, sub_add_cancel]
  have hz := ODE_solution_unique_univ (v := fun _ => A) (s := fun _ => Set.univ) (K := ‖A‖₊) (t₀ := 0)
    (f := fun s => π (g (ρ s (ι P)))) (g := fun _ => 0) (fun _ => A.lipschitz.lipschitzOnWith)
    (fun s => ⟨hw s, trivial⟩) (fun s => ⟨by simpa using hasDerivAt_const s (0 : Fin _ → ℂ), trivial⟩) (by
      simp only [h0, Module.End.one_apply, hg']
      rw [hπ' ⟨P, hPV⟩, map_eq_zero_iff _ e.injective]
      exact (Submodule.Quotient.mk_eq_zero _).2 hPN)
  obtain ⟨R, h1, h2⟩ := hV t P hPV
  refine ⟨R, ?_, h2⟩
  have h3 := congrFun hz t
  simp only [h2, hg'] at h3
  rw [hπ' ⟨R, h1⟩, map_eq_zero_iff _ e.injective] at h3
  exact (Submodule.Quotient.mk_eq_zero N').1 h3

variable {D : D7}

theorem fr_mem_Kset {V : HSp D} (B : Fr V) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : gᴴ * gramAt D V τ * g = gramAt D V τ) (hc : Commute g (B.cart τ)) :
    B.fr τ * g * (B.fr τ)⁻¹ ∈ Formalism.REAL.Kset (B.ε τ) := by
  have h1 := GlobalTheory.CompactFockAction.fr_mul_inv B τ
  have h2 := GlobalTheory.CompactFockAction.inv_mul_fr B τ
  have h3 : ((B.fr τ)⁻¹)ᴴ * (B.fr τ)ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  have hJ := Formalism.REAL.Jm_mul_self (B.ε τ)
  have hk : B.fr τ * g * (B.fr τ)⁻¹ * Formalism.REAL.Jm (B.ε τ) = Formalism.REAL.Jm (B.ε τ) * (B.fr τ * g * (B.fr τ)⁻¹) := by
    calc _ = B.fr τ * (g * B.cart τ) * (B.fr τ)⁻¹ := by
          simp only [Fr.cart, Matrix.mul_assoc, h1, Matrix.mul_one]
      _ = (B.fr τ * (B.fr τ)⁻¹) * Formalism.REAL.Jm (B.ε τ) * (B.fr τ * g * (B.fr τ)⁻¹) := by
          rw [hc.eq]; simp only [Fr.cart, Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.one_mul]
  have hu : (B.fr τ * g * (B.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (B.ε τ) * (B.fr τ * g * (B.fr τ)⁻¹) = Formalism.REAL.Jm (B.ε τ) := by
    calc _ = ((B.fr τ)⁻¹)ᴴ * (gᴴ * ((B.fr τ)ᴴ * Formalism.REAL.Jm (B.ε τ) * B.fr τ) * g) * (B.fr τ)⁻¹ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (((B.fr τ)⁻¹)ᴴ * (B.fr τ)ᴴ) * Formalism.REAL.Jm (B.ε τ) * (B.fr τ * (B.fr τ)⁻¹) := by
          rw [B.fr_gram, hg, ← B.fr_gram]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, h3, Matrix.one_mul, Matrix.mul_one]
  refine ⟨Matrix.mem_unitaryGroup_iff'.2 ?_, hk⟩
  rw [Matrix.mul_assoc, ← hk, ← Matrix.mul_assoc] at hu
  rw [Matrix.star_eq_conjTranspose, ← hJ, ← Matrix.mul_one (_ * _), ← hJ, ← Matrix.mul_assoc, hu]

theorem mem_closure_elt {V : HSp D} (B : Fr V) {a : GA D V} (ha : a ∈ GinfC V)
    (hc : ∀ τ, Commute ((Eqv.matA D V a).map (Eqv.psiT D τ)) (B.cart τ)) :
    a ∈ Submonoid.closure {x | ∃ τ, ∃ k ∈ Formalism.REAL.Kset (B.ε τ), x = B.elt (Eqv.thetaC D) τ k} := by
  classical
  set gs : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ := fun τ => infMat D.sp.cm.sig V.gram (Eqv.thetaC D τ) a
  have hgs : Eqv.IsUnitFam D V gs := Eqv.infMat_unitary' D V a
  have hu : ∀ s : Finset D.what₂.Tau, Eqv.IsUnitFam D V (fun τ => if τ ∈ s then gs τ else 1) := by
    intro s τ
    by_cases hτ : τ ∈ s
    · simp only [hτ, if_true]; exact hgs τ
    · simp only [hτ, if_false]; simp
  have key : ∀ s : Finset D.what₂.Tau, Eqv.famH D V _ (hu s) ∈
      Submonoid.closure {x | ∃ τ, ∃ k ∈ Formalism.REAL.Kset (B.ε τ), x = B.elt (Eqv.thetaC D) τ k} := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have e : Eqv.famH D V _ (hu ∅) = 1 := by
        apply Eqv.matA_inj D V
        rw [Eqv.matA_famH, Eqv.matA_one]
        convert Eqv.famM_one D V using 2
        funext τ
        simp
      rw [e]
      exact Submonoid.one_mem _
    | insert τ0 s hτ0 ih =>
      have e : Eqv.famH D V _ (hu (insert τ0 s)) = Eqv.atH D V τ0 (gs τ0) (hgs τ0) * Eqv.famH D V _ (hu s) := by
        apply Eqv.matA_inj D V
        rw [Eqv.matA_famH, Eqv.matA_mul, Eqv.matA_atH, Eqv.matA_famH]
        apply Eqv.mat_ext D
        · intro τ
          rw [Matrix.map_mul, Eqv.psi_famM, Eqv.psi_atM, Eqv.psi_famM]
          by_cases h : τ = τ0
          · subst h; simp [hτ0]
          · simp [h]
        · rw [Matrix.map_mul, Eqv.fin_famM, Eqv.fin_atM, Eqv.fin_famM, Matrix.one_mul]
      rw [e]
      refine Submonoid.mul_mem _ (Submonoid.subset_closure ⟨τ0, _, fr_mem_Kset B τ0 (hgs τ0)
        (by simpa only [gs, Eqv.infMat_thetaC] using hc τ0), ?_⟩) ih
      rw [← Eqv.atTau_eq D V τ0 (gs τ0) (hgs τ0), Fr.elt]
      congr 1
      calc gs τ0 = ((B.fr τ0)⁻¹ * B.fr τ0) * gs τ0 * ((B.fr τ0)⁻¹ * B.fr τ0) := by
            rw [GlobalTheory.CompactFockAction.inv_mul_fr, Matrix.one_mul, Matrix.mul_one]
        _ = _ := by simp only [Matrix.mul_assoc]
  have e : a = Eqv.famH D V _ (hu Finset.univ) :=
    Eqv.famH_unique D V _ (hu Finset.univ) a ha (fun τ => by simp [gs])
  rw [e]
  exact key _

theorem toUX_surj (X : HSp D) {J : Matrix (Fin X.rank) (Fin X.rank) D.host.E}
    (hJ : J = D.host.xi0 • (X.gramᵀ).submatrix (Equiv.refl _) (Equiv.refl _)) (k : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J) :
    ∃ h, GlobalTheory.TripleRead.toUX X (Equiv.refl _) hJ h = k := by
  subst hJ
  have h1 : (k.1.1)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (D.host.xi0 • X.gramᵀ) * (k.1.1).map (cA D) =
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (D.host.xi0 • X.gramᵀ) := k.2
  rw [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul, Matrix.mul_smul, Matrix.smul_mul] at h1
  have h2 := congrArg (fun Y => (incA D D.host.xi0⁻¹ • Y)ᵀ) h1
  simp only [smul_smul, ← map_mul, inv_mul_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one, one_smul, transpose_mul,
    transpose_transpose, ← Matrix.mul_assoc] at h2
  exact ⟨⟨k.1, h2⟩, Subtype.ext (Units.ext rfl)⟩

theorem exists_of_mem_KInf {X : HSp D} (B : Fr X) {Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank}
    (hJ : Ws.J = D.host.xi0 • (X.gramᵀ).submatrix (Equiv.refl _) (Equiv.refl _))
    {τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w}
    (hc : ∀ w, ∃ t, (∀ x, (τ w).1 x = conj (tauE D t x)) ∧ Ws.θ w = (B.cart t).map conj)
    {k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Ws.J} (hk : k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig Ws τ) :
    ∃ h ∈ Submonoid.closure {x | ∃ τ, ∃ k ∈ Formalism.REAL.Kset (B.ε τ), x = B.elt (Eqv.thetaC D) τ k},
      GlobalTheory.TripleRead.toUX X (Equiv.refl _) hJ h = k := by
  obtain ⟨h, rfl⟩ := toUX_surj X hJ k
  refine ⟨h, mem_closure_elt B ((Eqv.mem_GinfC D X h).2 ?_) fun ρ => ?_, rfl⟩
  · ext i j
    have h1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Eqv.matA D X h i j - (1 : Matrix _ _ (AE D)) i j) :=
      fun u hu => congrFun (congrFun (hk.1 u hu) i) j
    have h2 := GlobalTheory.ConjInfExp.finPart_eq_one (Eqv.matA D X h i j - (1 : Matrix _ _ (AE D)) i j + 1)
      (by rwa [add_sub_cancel_right])
    rw [RingHom.map_add, RingHom.map_one, add_eq_right, RingHom.map_sub, sub_eq_zero] at h2
    rw [Matrix.map_apply, h2]
    by_cases e : i = j
    · subst e; simp
    · simp [Matrix.one_apply_ne e]
  · obtain ⟨t, h1, h2⟩ := hc (placeOf D ρ)
    have h3 : (τ (placeOf D ρ)).1 = (starRingEnd ℂ).comp (tauE D t) := RingHom.ext h1
    have h4 : ((starRingEnd ℂ).comp (tauE D t)).comp (algebraMap D.host.F D.host.E) = (placeOf D ρ).embedding :=
      h3 ▸ (τ (placeOf D ρ)).2
    have h5 : t = ρ := by
      apply (placeOf_bijective D).1
      rw [← InfinitePlace.mk_embedding (placeOf D ρ), ← h4, placeOf]
      exact (InfinitePlace.mk_conjugate_eq _).symm
    subst h5
    have h6 := hk.2 (placeOf D t)
    have h7 : τ (placeOf D t) = ⟨_, h4⟩ := Subtype.ext h3
    have hθ : IsInfFam (Eqv.thetaC D) := by
      obtain ⟨θ, hθ⟩ := exists_isInfFam D
      exact Eqv.eq_thetaC D hθ ▸ hθ
    have h8 : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.TripleRead.toUX X (Equiv.refl _) hJ h)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (τ (placeOf D t))) =
        ((Eqv.matA D X h).map (Eqv.psiT D t)).map conj := by
      ext i j
      rw [h7]
      exact GlobalTheory.ConjInfExp.piInf_eq _ hθ t _ h4 _
    rw [h8, h2] at h6
    have h9 := h6.eq
    rw [← Matrix.map_mul, ← Matrix.map_mul] at h9
    exact Matrix.map_injective (starRingEnd ℂ).injective h9

theorem elt_stable {V W : HSp D} (A : Fr V) (B : Fr W) {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ}
    {χS χT : (AE D)ˣ →* Circle} {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {f : WO V W → ℂ} {τ : D.what₂.Tau}
    {aS aT : ℚ} (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ V W χS χT ω) (hS : HasInfExp D χS τ aS) (hT : HasInfExp D χT τ aT)
    (hf : IsVacF ψ θ A B f) (hf0 : f ≠ 0) (hi : Function.Injective (ptF ψ θ A B f)) (N : Submodule ℂ (PolF D W.rank V.rank))
    (hN : ∀ Y ∈ lieAt W τ, ∀ P ∈ N, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (A.ε τ) (B.ε τ) (B.fr τ * Y * (B.fr τ)⁻¹) P +
      ((aS : ℂ) * Y.trace) • P ∈ N)
    {k : Matrix (Fin W.rank) (Fin W.rank) ℂ} (hk : k ∈ Formalism.REAL.Kset (B.ε τ)) :
    ∀ P ∈ N, ∃ Q ∈ N, ω (1, B.elt θ τ k) (ptF ψ θ A B f P) = ptF ψ θ A B f Q := by
  intro P hP
  obtain ⟨Z, hZ, rfl⟩ := ReciprocityTheory.ChartRestriction.DS.exists_exp_eq_of_mem_Kset hk
  have h1 := GlobalTheory.CompactFockAction.fr_mul_inv B τ
  have h3 : ((B.fr τ)⁻¹)ᴴ * (B.fr τ)ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  have hZ1 : Zᴴ * Formalism.REAL.Jm (B.ε τ) + Formalism.REAL.Jm (B.ε τ) * Z = 0 := hZ.1
  have hZ2 : Z * Formalism.REAL.Jm (B.ε τ) = Formalism.REAL.Jm (B.ε τ) * Z := hZ.2
  have hY : (B.fr τ)⁻¹ * Z * B.fr τ ∈ lieAt W τ := by
    show ((B.fr τ)⁻¹ * Z * B.fr τ)ᴴ * gramAt D W τ + gramAt D W τ * ((B.fr τ)⁻¹ * Z * B.fr τ) = 0
    rw [← B.fr_gram τ]
    calc _ = (B.fr τ)ᴴ * (Zᴴ * (((B.fr τ)⁻¹)ᴴ * (B.fr τ)ᴴ) * Formalism.REAL.Jm (B.ε τ) +
          Formalism.REAL.Jm (B.ε τ) * (B.fr τ * (B.fr τ)⁻¹) * Z) * B.fr τ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
      _ = 0 := by rw [h1, h3, Matrix.mul_one, Matrix.mul_one, hZ1, Matrix.mul_zero, Matrix.zero_mul]
  have hK : ∀ t : ℝ, NormedSpace.exp (t • Z) ∈ Formalism.REAL.Kset (B.ε τ) := fun t =>
    ReciprocityTheory.ChartRestriction.DS.exp_mem_Kset (Z := t • Z) ⟨by
      show (t • Z)ᴴ * Formalism.REAL.Jm (B.ε τ) + Formalism.REAL.Jm (B.ε τ) * (t • Z) = 0
      rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hZ1, smul_zero], by
      show (t • Z) * Formalism.REAL.Jm (B.ε τ) = Formalism.REAL.Jm (B.ε τ) * (t • Z)
      rw [Matrix.smul_mul, Matrix.mul_smul, hZ2]⟩
  have hE : ∀ t : ℝ, oneP θ W τ ((B.fr τ)⁻¹ * Z * B.fr τ) t = B.elt θ τ (NormedSpace.exp (t • Z)) := fun t => by
    rw [oneP, Fr.elt, ← Matrix.exp_conj' _ _ (B.fr_unit τ), Matrix.mul_smul, Matrix.smul_mul]
  have hA1 : A.elt θ τ 1 = 1 := by
    rw [Fr.elt, Matrix.mul_one, GlobalTheory.CompactFockAction.inv_mul_fr]
    simpa [oneP] using GlobalTheory.Mem.Lift.oneP_zero (V := V) (τ := τ) (X := 0) hθ
  obtain ⟨x, y, -, -, hc⟩ := GlobalTheory.CompactFockAction.compactFockAll D V W A B θ ψ χS χT ω f τ aS aT hθ hω hS hT hf hf0
  have hl := (GlobalTheory.LieScalar.lieFockAll D V W A B θ ψ χS χT ω f τ aS aT hθ hω hS hT hf).2 _ hY
  have := oneParam_stable (pureTensorO ψ θ V W A.cart B.cart A.onb B.onb f) hi
    (MvPolynomial.restrictTotalDegree _ ℂ P.totalDegree) N (fun t => ω (1, oneP θ W τ ((B.fr τ)⁻¹ * Z * B.fr τ) t))
    (by simp only [GlobalTheory.Mem.Lift.oneP_zero hθ, Prod.mk_one_one, map_one])
    (fun s t => by rw [GlobalTheory.Mem.Lift.oneP_add hθ hY, ← map_mul, Prod.mk_mul_mk, one_mul])
    (fun t R hR => by
      have e := hc 1 ⟨one_mem _, by rw [Matrix.one_mul, Matrix.mul_one]⟩ _ (hK t) R
      rw [hA1, ← hE] at e
      refine ⟨_, Submodule.smul_mem _ _ ?_, e.trans (map_smul _ _ _).symm⟩
      rw [MvPolynomial.mem_restrictTotalDegree] at hR ⊢
      exact (GlobalTheory.Chain.RealIt.SubstDeg.totalDegree_subst_le _ _ _ _ _ _ _ _ _).trans hR)
    (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (A.ε τ) (B.ε τ) (B.fr τ * ((B.fr τ)⁻¹ * Z * B.fr τ) * (B.fr τ)⁻¹) +
      ((aS : ℂ) * ((B.fr τ)⁻¹ * Z * B.fr τ).trace) • 1) hl (hN _ hY) 1 P hP
    ((MvPolynomial.mem_restrictTotalDegree _ _ _).2 le_rfl)
  simp only [hE, one_smul] at this
  exact this

theorem closure_stable {V W : HSp D} (A : Fr V) (B : Fr W) {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ}
    {χS χT : (AE D)ˣ →* Circle} {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {f : WO V W → ℂ}
    {aS aT : D.what₂.Tau → ℚ} (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ V W χS χT ω)
    (hE : ∀ τ, HasInfExp D χS τ (aS τ) ∧ HasInfExp D χT τ (aT τ))
    (hf : IsVacF ψ θ A B f) (hf0 : f ≠ 0) (hi : Function.Injective (ptF ψ θ A B f)) (N : Submodule ℂ (PolF D W.rank V.rank))
    (hN : ∀ τ, ∀ Y ∈ lieAt W τ, ∀ P ∈ N, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (A.ε τ) (B.ε τ) (B.fr τ * Y * (B.fr τ)⁻¹) P +
      ((aS τ : ℂ) * Y.trace) • P ∈ N)
    {h : GA D W} (hh : h ∈ Submonoid.closure {x | ∃ τ, ∃ k ∈ Formalism.REAL.Kset (B.ε τ), x = B.elt θ τ k}) :
    ∀ P ∈ N, ∃ Q ∈ N, ω (1, h) (ptF ψ θ A B f P) = ptF ψ θ A B f Q := by
  induction hh using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨t, k, hk, rfl⟩ := hx
    exact elt_stable A B hθ hω (hE t).1 (hE t).2 hf hf0 hi N (hN t) hk
  | one => exact fun P hP => ⟨P, hP, by rw [Prod.mk_one_one, map_one]; rfl⟩
  | mul x y _ _ hx hy =>
    intro P hPN
    obtain ⟨Q, hQ, e⟩ := hy P hPN
    obtain ⟨R, hR', e'⟩ := hx Q hQ
    refine ⟨R, hR', ?_⟩
    rw [← e', ← e, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]

theorem tens_inj {F : Type} [Field F] [NumberField F] {κ : Type} {r : (κ → AF F) → ℂ}
    (hr : ∀ x z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) z → r (x + z) = r x) (h0 : r ≠ 0)
    {f g : (κ → mixedEmbedding.mixedSpace F) → ℂ}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) g r) : f = g := by
  obtain ⟨x, hx⟩ := Function.ne_iff.1 h0
  funext y
  let z : κ → AF F := fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i) - (x i).1, 0)
  have hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) z := by
    intro u hu
    have hu1 : u.1 = 0 := (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).1 hu
    funext i
    refine Prod.ext ?_ ?_
    · show u.1 * _ = 0
      rw [hu1, zero_mul]
    · show u.2 * 0 = 0
      rw [mul_zero]
  have he : (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F ((x + z) i)) = y := by
    funext i
    show InfiniteAdeleRing.ringEquiv_mixedSpace F ((x i).1 + ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i) - (x i).1)) = _
    rw [add_sub_cancel, RingEquiv.apply_symm_apply]
  have := congrFun h (x + z)
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens] at this
  rw [he, hr x z hz] at this
  exact mul_right_cancel₀ hx this

theorem kInf_stable : GlobalTheory.FunPr.Hypotheses₂ →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  ∀ (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank)
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws) (ψ' : AddChar (AF D.host.F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Xs Ws)
    (τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w),
    GlobalTheory.RealDict.PublishedHyps D Xs Ws Mo ψ' χX χW om τ → GlobalTheory.RealDict.IsPairReading ψ ε A B ω Xs Ws Mo ψ' om τ →
    ∀ Φ : PolF D X.rank M.rank →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
    Function.Injective Φ → LinearMap.range Φ = Mo.Pol ψ' τ → GlobalTheory.RealDict.IsFockMap ψ θ ε A B Mo Φ →
      ∀ N : Submodule ℂ (PolF D X.rank M.rank),
        GlobalTheory.RealQuot.IsStab (fun i : GlobalTheory.RealQuot.LieIx X => GlobalTheory.RealQuot.actT ε A B eS i.1.1 i.1.2) N →
        ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig Ws τ, ∀ f ∈ N.map Φ, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (om (1, k)) f f₁ → f₁ ∈ N.map Φ := by
  intro _ D ψ θ _ hθ ε M X A B χS χT ω eS eT hω hE Xs Ws Mo ψ' χX χW om τ hH hR Φ hΦ _ hF N hN k hk f hf f₁ hact
  obtain ⟨-, hstd, -, hdX, -, hdW, -, -, -, -, hW, -, -⟩ := hH
  obtain ⟨f₀, r, hv, hv0, hP⟩ := hF
  obtain rfl := hR.psi
  obtain rfl := Eqv.eq_thetaC D hθ
  obtain ⟨T, hT, hTi⟩ := GlobalTheory.T.thetaTransform_darbouxModel_linear_injective D Mo ψ' (sgn ε M).gram (Equiv.refl (Fin X.rank)) hR.good hstd hdX hdW
    (gram_det_ne (sgn ε M))
  have hinj : ∀ a ∈ schA D.host.F (Fin M.rank × Fin X.rank), ∀ b ∈ schA D.host.F (Fin M.rank × Fin X.rank),
      GlobalTheory.TripleRead.thO Mo ψ' (sgn ε M).gram (Equiv.refl (Fin X.rank)) a =
        GlobalTheory.TripleRead.thO Mo ψ' (sgn ε M).gram (Equiv.refl (Fin X.rank)) b → a = b := by
    intro a ha b hb e
    rw [← hT a ha, ← hT b hb, ← sub_eq_zero, ← map_sub] at e
    exact sub_eq_zero.1 (hTi _ (Submodule.sub_mem _ ha hb) e)
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply hv0
    have e1 : ptF ψ' (Eqv.thetaC D) (frSgn ε A) B f₀ 1 = f₀ := by
      have : (1 : PolF D X.rank M.rank) = MvPolynomial.basisMonomials _ ℂ 0 := by simp
      rw [this]
      exact (Module.Basis.constr_basis _ _ _ _).trans (by simp [opPow])
    have e2 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Φ 1) 0 = 0 := by
      funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens]
    rw [← e1, ← (hP 1).2, e2, ← hT 0 (Submodule.zero_mem _), map_zero]
  have hcan : ∀ (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank)) (Q : PolF D X.rank M.rank),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) g r ∈ schA D.host.F (Fin M.rank × Fin X.rank) →
      GlobalTheory.TripleRead.thO Mo ψ' (sgn ε M).gram (Equiv.refl (Fin X.rank))
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) g r) = ptF ψ' (Eqv.thetaC D) (frSgn ε A) B f₀ Q → g = Φ Q := by
    intro g Q hg e
    exact DFunLike.coe_injective (tens_inj (hP Q).1.1 hr0 (hinj _ hg _ (hP Q).1.2 (e.trans (hP Q).2.symm)))
  have hi : Function.Injective (ptF ψ' (Eqv.thetaC D) (frSgn ε A) B f₀) := fun P Q e =>
    hΦ (hcan _ Q (hP P).1.2 ((hP P).2.trans e))
  obtain ⟨h, hh, rfl⟩ := exists_of_mem_KInf B hR.JW (fun w => (hR.cart w).imp fun t ht => ⟨ht.1, ht.2.2⟩) hk
  have key := closure_stable (frSgn ε A) B hθ hω hE hv hv0 hi N (fun t Y hY P hP => hN ⟨(t, Y), hY⟩ P hP) hh
  obtain ⟨P, hPN, rfl⟩ := hf
  obtain ⟨Q, hQ, e⟩ := key P hPN
  refine ⟨Q, hQ, (hcan f₁ Q ?_ ?_).symm⟩
  · rw [← hact r (hP P).1]
    letI := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.invTwo (F := D.host.F)
    exact hW.1.1.pres _ _ (hP P).1.2
  · have h1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M (GlobalTheory.RealDict.sgE (D := D) ε) hR.JX 1 = 1 :=
      Subtype.ext (by show GeneralLinearGroup.map (cA D) (Formalism.L2.Theta.matHom M 1) = 1; rw [map_one, map_one])
    have h2 := hR.transp _ (hP P).1.2 1 h
    rw [h1, (hP P).2] at h2
    have h3 : ω.toSgn ε (1, h) = ω (1, h) := congrArg ω (Prod.ext (map_one (ofSgn ε M)) rfl)
    rw [h3] at e
    rw [← hact r (hP P).1]
    exact h2.trans e

end GlobalTheory.CompactStable

end
