import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.ChainRows
import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.CupFlipContinuousCocycleStatement
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ExistsDualLatticesStatement
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.LatticeOpenCompactNhdsBasisStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

namespace GlobalTheory.CompanionTheory.LocDual.Kernels

theorem mem_of_forall_pow {O M : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [AddCommGroup M] [Module O M] (Λ E : Submodule O M) (hΛ : Λ.FG) (ϖ : O) (hϖ : ¬ IsUnit ϖ)
    (w : M) (h : ∀ n : ℕ, ∃ e ∈ E, ∃ t ∈ Λ, w = e + ϖ ^ n • t) : w ∈ E := by
  classical
  set N : Submodule O (M ⧸ E) := Λ.map E.mkQ with hNdef
  have hNfg : N.FG := hΛ.map _
  haveI : Module.Finite O N := Module.Finite.iff_fg.2 hNfg
  have hE : ∀ e ∈ E, E.mkQ e = 0 := fun e he => (Submodule.Quotient.mk_eq_zero E).2 he
  obtain ⟨e₀, he₀, t₀, ht₀, hw₀⟩ := h 0
  have hwN : E.mkQ w ∈ N := ⟨t₀, ht₀, by rw [hw₀, pow_zero, one_smul, map_add, hE e₀ he₀, zero_add]⟩
  have hI : Ideal.span {ϖ} ≠ ⊤ := fun h' => hϖ (Ideal.span_singleton_eq_top.1 h')
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := N) (Ideal.span {ϖ}) hI
  have hmem : (⟨E.mkQ w, hwN⟩ : N) ∈ (⨅ i : ℕ, Ideal.span {ϖ} ^ i • ⊤ : Submodule O N) := by
    refine Submodule.mem_iInf _ |>.2 fun i => ?_
    obtain ⟨e, he, t, ht, hw⟩ := h i
    have htN : E.mkQ t ∈ N := ⟨t, ht, rfl⟩
    have heq : (⟨E.mkQ w, hwN⟩ : N) = ϖ ^ i • (⟨E.mkQ t, htN⟩ : N) := by
      apply Subtype.ext
      rw [Submodule.coe_smul]
      show E.mkQ w = ϖ ^ i • E.mkQ t
      rw [hw, map_add, map_smul, hE e he, zero_add]
    rw [heq]
    exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self ϖ) i) Submodule.mem_top
  rw [hbot, Submodule.mem_bot] at hmem
  have h0 : E.mkQ w = 0 := congrArg Subtype.val hmem
  exact (Submodule.Quotient.mk_eq_zero E).1 h0

theorem exists_finset_sep {k U G X : Type} [Field k] [AddCommGroup U] [Module k U]
    [FiniteDimensional k U] [AddCommGroup X] [Module k X] (φ : U →ₗ[k] G → X) :
    ∃ F : Finset G, ∀ u, (∀ g ∈ F, φ u g = 0) → φ u = 0 := by
  classical
  let Kf : Finset G → Submodule k U := fun F => ⨅ g ∈ F, LinearMap.ker ((LinearMap.proj g).comp φ)
  obtain ⟨_, ⟨F, rfl⟩, hmin⟩ := WellFounded.has_min (wellFounded_lt (α := Submodule k U)) (Set.range Kf)
    ⟨Kf ∅, Set.mem_range_self _⟩
  have hall : ∀ g, Kf F ≤ LinearMap.ker ((LinearMap.proj g).comp φ) := by
    intro g
    have hle : Kf (insert g F) ≤ Kf F := by
      refine le_iInf₂ fun g' hg' => iInf₂_le g' (Finset.mem_insert_of_mem hg')
    have heq : Kf (insert g F) = Kf F := by
      by_contra hne
      exact hmin _ (Set.mem_range_self _) (lt_of_le_of_ne hle hne)
    rw [← heq]
    exact iInf₂_le g (Finset.mem_insert_self g F)
  refine ⟨F, fun u hu => funext fun g => ?_⟩
  have huF : u ∈ Kf F := by
    simp only [Kf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj, Function.eval]
    exact hu
  have := hall g huF
  simpa using this

theorem right_kernel (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l)
    (hD : DualD ((D.loc l).PD K)) (hC : CobLO ((D.loc l).PD K))
    (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O]
    [Algebra O LL] (hO : GoodO (Qp := ℚ_[l]) LL O) (A A' : GRep ↥(GK K) ℚ_[l] LL O)
    (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL) (hP : IsDual1 ((D.loc l).PD K) A.ρ A'.ρ P)
    (b : ↥(GK K) → A'.V) (hb : b ∈ continuousCocycles A'.ρ)
    (hab : ∀ a ∈ continuousCocycles A.ρ, CobL ((D.loc l).PD K) (cupL A'.ρ P a b)) : b ∈ B1 A'.ρ := by
  classical
  obtain ⟨⟨hdom, hdvr, hfrac⟩, -⟩ := id hO
  haveI := hdom
  haveI := hdvr
  haveI := hfrac
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨LA, LA', hLat, -⟩ := (GlobalTheory.T.exists_dual_lattices D l K).2 LL O hO A A' P hP
  obtain ⟨-, hLat2⟩ := id hLat
  obtain ⟨L1, hL1⟩ := (GlobalTheory.T.exists_dual_lattices D l K).1 LL O hO
  have h52 := GlobalTheory.T.lattice_open_compact_nhds_basis D l K LL O hO A' LA' ϖ hϖ
  have h53 := GlobalTheory.T.cup_flip_continuous_cocycle D l K LL O hO A A' P hP
  have hb' : Continuous b ∧ ∀ g h, b (g * h) = b g + A'.ρ g (b h) := hb
  obtain ⟨β, hβdef⟩ : ∃ β : LL, β = algebraMap O LL ϖ := ⟨_, rfl⟩
  have hβ : β ≠ 0 := by
    rw [hβdef]
    exact fun h => hϖ.ne_zero (IsFractionRing.injective O LL (h.trans (map_zero _).symm))
  have hmkLC : IsLocallyConstant (Submodule.Quotient.mk (p := LA'.T)) := by
    refine (IsLocallyConstant.iff_exists_open _).2 fun x => ⟨(· + -x) ⁻¹' (LA'.T : Set A'.V),
      h52.1.preimage (continuous_add_const _), ?_, fun x' hx' => ?_⟩
    · simp
    · exact (Submodule.Quotient.eq _).2 (by simpa [sub_eq_add_neg] using hx')
  have hactD : ∀ g (v : A'.V), Formalism.WeaklyAdmissibleFiltrations.actD LA' g (Submodule.Quotient.mk v) = Submodule.Quotient.mk (A'.ρ g v) :=
    fun g v => rfl
  have hlift : ∀ q : A'.V ⧸ LA'.T, Submodule.Quotient.mk (Formalism.MainNotions.N.liftD LA' q) = q := fun q => by
    unfold Formalism.MainNotions.N.liftD
    generalize_proofs hq
    exact hq.choose_spec
  have e1 : ∀ (v : A'.V) g, (LinearMap.pi fun g => Formalism.WeaklyAdmissibleFiltrations.actD LA' g - LinearMap.id)
      (Submodule.Quotient.mk v : A'.V ⧸ LA'.T) g = Submodule.Quotient.mk (A'.ρ g v - v) := fun v g => by
    simp only [LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply, hactD, Submodule.Quotient.mk_sub]
  have hBZ : BD LA' ≤ divisibleCocycles LA' := by
    intro s hs
    obtain ⟨z, rfl⟩ := LinearMap.mem_range.1 hs
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    show IsLocallyConstant _ ∧ ∀ g h, _ = _ + Formalism.WeaklyAdmissibleFiltrations.actD LA' g _
    refine ⟨?_, fun g h => ?_⟩
    · have hf : (fun g => (LinearMap.pi fun g => Formalism.WeaklyAdmissibleFiltrations.actD LA' g - LinearMap.id)
          (Submodule.Quotient.mk v : A'.V ⧸ LA'.T) g) =
          (Submodule.Quotient.mk (p := LA'.T)) ∘ fun g => A'.ρ g v + -v := funext fun g => by
        rw [e1, sub_eq_add_neg]; rfl
      have hcont : Continuous fun g : ↥(GK K) => A'.ρ g v + -v := (A'.cont v).add continuous_const
      have hlc := hmkLC.comp_continuous hcont
      convert hlc using 1
    · rw [e1, e1, e1, hactD, ← Submodule.Quotient.mk_add]
      congr 1
      rw [map_mul, Module.End.mul_apply, map_sub]
      abel
  have step : ∀ n : ℕ, ∃ x : A'.V, ∀ g, (β ^ n)⁻¹ • b g - (A'.ρ g x - x) ∈ LA'.T := by
    intro n
    have hc : (fun g => (Submodule.Quotient.mk ((β ^ n)⁻¹ • b g) : A'.V ⧸ LA'.T)) ∈ divisibleCocycles LA' := by
      show IsLocallyConstant _ ∧ ∀ g h, _ = _ + Formalism.WeaklyAdmissibleFiltrations.actD LA' g _
      refine ⟨hmkLC.comp_continuous (hb'.1.const_smul _), fun g h => ?_⟩
      simp only
      rw [hactD, ← Submodule.Quotient.mk_add, hb'.2 g h, smul_add, map_smul]
    have hcS := hD LL O hO L1 hL1 A A' LA LA' P hLat (BD LA') le_rfl hBZ _ hc (by
      intro d hd _
      have hd1 : d ∈ continuousCocycles A.ρ := (Submodule.mem_inf.1 hd).1
      have hdT : ∀ g, d g ∈ LA.T := fun g => (Submodule.mem_pi.1 (Submodule.mem_inf.1 hd).2) g (Set.mem_univ g)
      have hcup := (hC LL O hO L1 hL1 _ (h53.2 d hd1 b hb).1).1 (hab d hd1) ((β ^ n)⁻¹)
      unfold Formalism.MainNotions.N.CobO at hcup ⊢
      convert hcup using 2
      rename_i x
      rw [Submodule.Quotient.eq, hL1]
      have hl := (Submodule.Quotient.eq LA'.T).1 (hlift (Submodule.Quotient.mk ((β ^ n)⁻¹ • b x.2)))
      obtain ⟨a, ha⟩ := (hLat2 _).1 (LA'.stable x.1 _ hl) (d x.1) (hdT x.1)
      refine ⟨a, ?_⟩
      rw [Algebra.linearMap_apply, ← ha]
      simp only [Formalism.MainNotions.N.cupLD, Formalism.MainNotions.N.cupL, Pi.smul_apply, smul_eq_mul, map_sub, map_smul])
    obtain ⟨z, hz⟩ := LinearMap.mem_range.1 hcS
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    refine ⟨x, fun g => ?_⟩
    have h1 := congr_fun hz g
    rw [e1] at h1
    have h2 := LA'.T.neg_mem ((Submodule.Quotient.eq LA'.T).1 h1)
    rwa [neg_sub] at h2
  obtain ⟨U, hU⟩ : ∃ U : Submodule LL (↥(GK K) → A'.V), U = Submodule.span LL {b} ⊔ B1 A'.ρ := ⟨_, rfl⟩
  haveI hB1fd : FiniteDimensional LL ↥(B1 A'.ρ) := LinearMap.finiteDimensional_range _
  haveI : FiniteDimensional LL ↥U := by
    rw [hU]
    exact Submodule.finiteDimensional_sup _ _
  obtain ⟨F, hF⟩ := exists_finset_sep (k := LL) U.subtype
  let Φ : A'.V →ₗ[O] (↥F → A'.V) := (LinearMap.pi fun f : ↥F => A'.ρ f - LinearMap.id).restrictScalars O
  let Λ : Submodule O (↥F → A'.V) := ⨆ f : ↥F, LA'.T.map (LinearMap.single O (fun _ : ↥F => A'.V) f)
  have hΛ : Λ.FG := Submodule.fg_iSup _ fun f => LA'.fg.map _
  have hw : (fun f : ↥F => b f) ∈ LinearMap.range Φ := by
    refine mem_of_forall_pow Λ (LinearMap.range Φ) hΛ ϖ hϖ.not_isUnit _ fun n => ?_
    obtain ⟨x, hx⟩ := step n
    refine ⟨Φ (β ^ n • x), LinearMap.mem_range_self _ _, fun f => (β ^ n)⁻¹ • b f - (A'.ρ f x - x), ?_, ?_⟩
    · rw [← Finset.univ_sum_single (fun f : ↥F => (β ^ n)⁻¹ • b f - (A'.ρ f x - x))]
      exact Submodule.sum_mem _ fun f _ => Submodule.mem_iSup_of_mem f ⟨_, hx f, rfl⟩
    · funext f
      have e2 : (ϖ ^ n) • ((β ^ n)⁻¹ • b f - (A'.ρ f x - x)) = b f - β ^ n • (A'.ρ f x - x) := by
        rw [← algebraMap_smul LL (ϖ ^ n), map_pow, ← hβdef, smul_sub, smul_inv_smul₀ (pow_ne_zero n hβ)]
      show b f = Φ (β ^ n • x) f + (ϖ ^ n) • ((β ^ n)⁻¹ • b f - (A'.ρ f x - x))
      rw [e2]
      simp only [Φ, LinearMap.restrictScalars_apply, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply,
        map_smul, smul_sub]
      abel
  obtain ⟨x, hx⟩ := LinearMap.mem_range.1 hw
  have hu : b - Formalism.WeaklyAdmissibleFiltrations.cob A'.ρ x ∈ U := by
    rw [hU]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.mem_span_singleton_self b))
      (Submodule.mem_sup_right (LinearMap.mem_range_self (Formalism.WeaklyAdmissibleFiltrations.cob A'.ρ) x))
  have hzero : b - Formalism.WeaklyAdmissibleFiltrations.cob A'.ρ x = 0 := hF ⟨_, hu⟩ fun g hg => by
    have h1 := congr_fun hx ⟨g, hg⟩
    simp only [Φ, LinearMap.restrictScalars_apply, LinearMap.pi_apply, LinearMap.sub_apply,
      LinearMap.id_apply] at h1
    simp only [Submodule.coe_subtype, Pi.sub_apply, Formalism.WeaklyAdmissibleFiltrations.cob, LinearMap.pi_apply, LinearMap.sub_apply,
      LinearMap.id_apply]
    rw [h1, sub_self]
  exact LinearMap.mem_range.2 ⟨x, (sub_eq_zero.1 hzero).symm⟩

theorem nondegL : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l), DualD ((D.loc l).PD K) →
    CobLO ((D.loc l).PD K) → NondegL ((D.loc l).PD K) := by
  intro D l _ K hD hC
  unfold GlobalTheory.CompanionTheory.LocDual.NondegL
  intro LL _ _ _ O _ _ hO A A' P hP
  have h53 := GlobalTheory.T.cup_flip_continuous_cocycle D l K LL O hO A A' P hP
  refine ⟨fun a ha hab => ?_, fun b hb hab => right_kernel D l K hD hC LL O hO A A' P hP b hb hab⟩
  exact right_kernel D l K hD hC LL O hO A' A P.flip h53.1 a ha fun b hb => ((h53.2 a ha b hb).2.2.1).1 (hab b hb)

end GlobalTheory.CompanionTheory.LocDual.Kernels
