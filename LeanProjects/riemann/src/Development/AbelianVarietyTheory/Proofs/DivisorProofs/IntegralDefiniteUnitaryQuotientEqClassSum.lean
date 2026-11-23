import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfOpenCompact
import Formalism.LocalToGlobal.GroupLattices.LevelCharts.FiniteClassSetOfFiniteIndex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameEquivApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicPointFinitePartEqRealOne
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormDictClassSum

section Compact

open Formalism.MainNotions.StandardLattice Matrix
open scoped TensorProduct ComplexOrder MatrixOrder

theorem negDef_of_signature {n q : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.UG.HasSignature G 0 q) : (-G).PosDef := by
  obtain ⟨e, P, hP⟩ := h
  have h1 : Formalism.UG.Jpq 0 q = -1 := by
    ext (i | i) (j | j)
    · exact i.elim0
    · exact i.elim0
    · exact j.elim0
    · simp [Formalism.UG.Jpq, Matrix.one_apply]
  have h2 : (star P.1 * (-G).reindex e e * P.1).PosDef := by
    have e1 : (-G).reindex e e = -(G.reindex e e) := by ext i j; simp
    have : star P.1 * (-G).reindex e e * P.1 = 1 := by
      have hP' : star P.1 * G.reindex e e * P.1 = Formalism.UG.Jpq 0 q := hP
      rw [e1, Matrix.mul_neg, Matrix.neg_mul, hP', h1, neg_neg]
    rw [this]; exact Matrix.PosDef.one
  have h3 := ((Matrix.IsUnit.posDef_star_left_conjugate_iff P.isUnit).1 h2).submatrix e.injective
  simpa using h3

theorem exists_bound_definite {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef ∨ (-G).PosDef) :
    ∃ R : ℝ, ∀ g : Matrix (Fin n) (Fin n) ℂ, gᴴ * G * g = G → ∀ i j, ‖g i j‖ ≤ R := by
  rcases hG with hG | hG
  · exact GlobalTheory.DefiniteQuotient.exists_bound_unitary hG
  · obtain ⟨R, hR⟩ := GlobalTheory.DefiniteQuotient.exists_bound_unitary hG
    refine ⟨R, fun g hg => hR g ?_⟩
    rw [Matrix.mul_neg, Matrix.neg_mul, hg]

variable {D : D7}

theorem definite_gramAt (V : HSp D) (hs : V.SigOK) (hd : V.IsDefinite) (τ : D.what₂.Tau) :
    (gramAt D V τ).PosDef ∨ (-gramAt D V τ).PosDef := by
  have h1 := hs (tauE D τ)
  rcases hd (tauE D τ) with h | h
  · left; rw [h] at h1; exact GlobalTheory.DefiniteQuotient.posDef_of_signature h1
  · right; rw [h] at h1; exact negDef_of_signature h1

theorem exists_compact_def (V : HSp D) (hs : V.SigOK) (hd : V.IsDefinite) :
    ∃ C : Set (GA D V), IsCompact C ∧ ∀ h : GA D V, ∃ γ ∈ GQ V, ∃ c ∈ C, h = γ * c := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  haveI : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig V.gram
  have hf : GlobalTheory.Mass.FiniteClasses (GQ V) ((GlobalTheory.Mass.stdLevel D.sp.cm.sig V.gram).comap π) := by
    refine (GlobalTheory.Mass.finiteClasses_comap π (GlobalTheory.Mass.ratIn _ _ _) _ hπ.surjective hπ.injOn).2 ?_
    rw [hπ.map_ratIn]
    exact GlobalTheory.Mass.finiteClasses_unitary (GlobalTheory.DefiniteQuotient.cmExt D) (GlobalTheory.DefiniteQuotient.gram_hermND V)
      (Formalism.L2.G.gram_totDef D.sp.cm V hs hd)
      (GlobalTheory.Mass.isCompact_stdLevel _ _ (GlobalTheory.DefiniteQuotient.gram_hermND V).2) (GlobalTheory.Mass.isOpen_stdLevel _ _)
  choose R hR using fun τ => exists_bound_definite (definite_gramAt V hs hd τ)
  obtain ⟨C, hC, hCe⟩ := (GlobalTheory.Mass.intTens_open_compact D.host.F D.host.E).2
  obtain ⟨C', hC', hCe'⟩ := GlobalTheory.StabCompact.exists_compact_adele D θ hθ (∑ τ, |R τ|) C hC
  obtain ⟨K, hK, hKe⟩ := GlobalTheory.StabCompact.exists_compact_of_entries (AF D.host.F) D.sp.cm.sig V.gram
    (GlobalTheory.DefiniteQuotient.gram_hermND V).2 C' hC'
  have hsub : ∀ k : GA D V, π k ∈ GlobalTheory.Mass.stdLevel D.sp.cm.sig V.gram → k ∈ K := by
    intro k hk
    refine hKe k fun i j => hCe' _ (hCe _ ?_) fun τ => ?_
    · have := ((GlobalTheory.Mass.mem_stdLevel _ _ _).1 hk i j).1
      rwa [hπ k] at this
    · have hJ : (V.gram.map (incA D)).map ((θ τ).comp (infPart D)) = gramAt D V τ := by
        ext i j; exact GlobalTheory.FockCompare.comp_incA hθ τ _
      have hu : Formalism.UG.cT (cA D) (mt V k) * V.gram.map (incA D) * mt V k = V.gram.map (incA D) := k.2
      have e : (Formalism.UG.cT (cA D) (mt V k)).map ((θ τ).comp (infPart D)) =
          ((mt V k).map ((θ τ).comp (infPart D)))ᴴ := by
        ext i j; exact GlobalTheory.FockCompare.comp_cA hθ τ _
      have := congrArg (fun M => M.map ((θ τ).comp (infPart D))) hu
      simp only [Matrix.map_mul, e, hJ] at this
      exact ((hR τ _ this i j).trans (le_abs_self _)).trans
        (Finset.single_le_sum (f := fun τ => |R τ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ τ))
  haveI := hf.1
  refine ⟨⋃ c : Formalism.UG.ClassSet (GQ V) ((GlobalTheory.Mass.stdLevel D.sp.cm.sig V.gram).comap π),
    (fun k => c.out * k) '' K, isCompact_iUnion fun c => hK.image (continuous_const_mul _), fun h => ?_⟩
  obtain ⟨γ, k, hγ, hk, e⟩ := DoubleCoset.mk_out_eq_mul (GQ V) ((GlobalTheory.Mass.stdLevel D.sp.cm.sig V.gram).comap π) h
  refine ⟨γ⁻¹, inv_mem hγ, _, Set.mem_iUnion.2 ⟨DoubleCoset.mk _ _ h, k⁻¹, hsub _ (inv_mem hk), rfl⟩, ?_⟩
  simp only [e]
  group

end Compact

set_option maxHeartbeats 4000000 in

theorem integral_eq_classSum : ∀ {D : D7} (V : HSp D) (n : ℕ) (ι : Formalism.MainNotions.StandardLatticesGL3.GA D n →* GA D V) (J : Subgroup (Formalism.MainNotions.StandardLatticesGL3.GA D n))
  (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)),
  GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsDefiniteSpace V → Function.Injective ι → ι.range = GfC V →
  (∀ x, (∃ γ ∈ GQ V, finHom V γ = finHom V (ι x)) ↔ x ∈ ratG D n) →
  GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel V K → (∀ x, Lev.finE V (ι x) ∈ K ↔ x ∈ J) → Links.IsMeasDef V K μ 𝓕 →
  ∀ Φ : GA D V → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsClassFun V K Φ →
    Finite (Cls D n J) ∧ Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ V) Φ) (GlobalTheory.AutomorphicL2Unitary.autMeasure V μ) ∧
    ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ V) Φ q ∂GlobalTheory.AutomorphicL2Unitary.autMeasure V μ =
      ∑ᶠ x : Cls D n J, ((gam D J x.out : ℂ))⁻¹ * Φ (ι x.out) := by
  intro D V n ι J K μ 𝓕 hV hinj hran hrat hK hJ hμ Φ hΦ
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hT.2.2.2.2.1
  haveI : μ.IsHaarMeasure := hμ.1.1
  have hF : IsFundamentalDomain (GQ V) 𝓕 μ := hμ.2
  have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) Φ := hΦ.left
  let Ψ : Formalism.MainNotions.StandardLatticesGL3.GA D n →* Bridge.Gf V := (finHom V).rangeRestrict.comp ι
  have hΨi : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : ι x ∈ GinfC V := congrArg Subtype.val hx
    have h2 : ι x ∈ GfC V := by rw [← hran]; exact ⟨x, rfl⟩
    exact hinj ((GlobalTheory.AutFunCounterexample.GfC_inf_GinfC V h2 h1).trans (map_one ι).symm)
  have hΨs : Function.Surjective Ψ := by
    intro g
    obtain ⟨α, hα, e⟩ := GlobalTheory.Mem.FinPartLift.exists_gfC_finHom_eq V g
    rw [← hran] at hα
    obtain ⟨x, rfl⟩ := hα
    exact ⟨x, Subtype.ext e⟩
  have hratΨ : ∀ x, x ∈ ratG D n ↔ ∃ γ : GQ V, Bridge.ratF V γ = Ψ x := by
    intro x
    rw [← hrat x]
    constructor
    · rintro ⟨γ, hγ, h⟩; exact ⟨⟨γ, hγ⟩, Subtype.ext h⟩
    · rintro ⟨γ, h⟩; exact ⟨γ, γ.2, congrArg Subtype.val h⟩
  have hJΨ : ∀ x, x ∈ J ↔ Ψ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.levelFin V K := fun x =>
    (hJ x).symm.trans (GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.mem_levelFin (ι x)).symm
  have hΨdef : ∀ x, Ψ x = (finHom V).rangeRestrict (ι x) := fun _ => rfl
  clear_value Ψ
  obtain ⟨e, he⟩ : ∃ e : Formalism.MainNotions.StandardLatticesGL3.GA D n ≃* Bridge.Gf V, ∀ x, e x = Ψ x :=
    ⟨MulEquiv.ofBijective Ψ ⟨hΨi, hΨs⟩, fun _ => rfl⟩
  have hre : ∀ y, Ψ (e.symm y) = y := fun y => (he _).symm.trans (e.apply_symm_apply y)

  obtain ⟨C, hC, hCe⟩ := exists_compact_def V hV.1 hV.2
  obtain ⟨m, c, hc⟩ := GlobalTheory.RepsObj.exists_cover_of_compact (GQ V) (finHom V).rangeRestrict
    (finHom V).rangeRestrict_surjective (GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.levelFin V K) hK.1 hC hCe
  have hsurj : Function.Surjective fun a : Fin m => (DoubleCoset.mk (ratG D n) J (e.symm (c a)) : Cls D n J) := by
    intro q
    obtain ⟨a, γ, k, hk⟩ := hc (Ψ q.out)
    refine ⟨a, ?_⟩
    show DoubleCoset.mk (ratG D n) J (e.symm (c a)) = q
    conv_rhs => rw [← DoubleCoset.out_eq' _ _ q]
    rw [DoubleCoset.eq]
    refine ⟨e.symm (Bridge.ratF V γ), (hratΨ _).2 ⟨γ, (hre _).symm⟩, e.symm k,
      (hJΨ _).2 (by rw [hre]; exact k.2), ?_⟩
    apply hΨi
    simp only [map_mul, hre]
    exact hk
  haveI hfin : Finite (Cls D n J) := Finite.of_surjective _ hsurj
  haveI : Fintype (Cls D n J) := Fintype.ofFinite _

  have hreps : Bridge.IsReps (Bridge.ratF V) (GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.levelFin V K) (fun q : Cls D n J => Ψ q.out) := by
    intro g
    refine (hΨs g).elim fun x hx => ?_
    rw [← hx]
    refine ⟨DoubleCoset.mk (ratG D n) J x, ?_, ?_⟩
    · obtain ⟨h, k, hh, hk, hout⟩ := DoubleCoset.mk_out_eq_mul (ratG D n) J x
      obtain ⟨γ, hγ⟩ := (hratΨ h⁻¹).1 (inv_mem hh)
      refine ⟨γ, ⟨Ψ k⁻¹, (hJΨ _).1 (inv_mem hk)⟩, ?_⟩
      show Ψ x = Bridge.ratF V γ * Ψ (DoubleCoset.mk (ratG D n) J x).out * Ψ k⁻¹
      rw [hγ, hout, ← map_mul Ψ, ← map_mul Ψ]
      congr 1
      group
    · rintro q ⟨γ, k, hq⟩
      rw [← DoubleCoset.out_eq' _ _ q, DoubleCoset.eq]
      refine ⟨e.symm (Bridge.ratF V γ), (hratΨ _).2 ⟨γ, (hre _).symm⟩, e.symm k,
        (hJΨ _).2 (by rw [hre]; exact k.2), ?_⟩
      apply hΨi
      simp only [map_mul, hre]
      exact hq
  obtain ⟨-, hIO, hsum⟩ := GlobalTheory.DefiniteClassSum.classSumIntegral D V hV K hK μ 𝓕 hμ (Cls D n J)
    (fun q => Ψ q.out) hreps (fun q => ι q.out) (fun q => (hΨdef _).symm) Φ hΦ

  have hcard : ∀ x, Nat.card (GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.classGroupAt V K (Ψ x)) = gam D J x := by
    intro x
    unfold gam
    refine Nat.card_eq_of_bijective (fun γ => ⟨e.symm (Bridge.ratF V γ.1), (hratΨ _).2 ⟨γ.1, (hre _).symm⟩,
      (hJΨ _).2 ?_⟩) ⟨?_, ?_⟩
    · simp only [map_mul, map_inv, hre]
      exact (Bridge.mem_stab _).1 γ.2
    · intro a b hab
      have h1 := congrArg (fun s : {γ : Formalism.MainNotions.StandardLatticesGL3.GA D n // γ ∈ ratG D n ∧ x⁻¹ * γ * x ∈ J} => Ψ s.1) hab
      simp only [hre] at h1
      exact Subtype.ext (GlobalTheory.FormInner.ratF_injective V h1)
    · rintro ⟨y, hy1, hy2⟩
      refine ((hratΨ y).1 hy1).elim fun γ hγ => ?_
      refine ⟨⟨γ, (Bridge.mem_stab _).2 ?_⟩, ?_⟩
      · rw [hγ, ← map_inv Ψ, ← map_mul Ψ, ← map_mul Ψ]
        exact (hJΨ _).1 hy2
      · apply Subtype.ext
        apply hΨi
        exact (hre _).trans hγ
  refine ⟨hfin, ?_, ?_⟩
  · have h1 : MemLp (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) (GlobalTheory.AutomorphicL2Unitary.descend (GQ V) Φ)) 1 (μ.restrict 𝓕) := by
      rw [hL.lift_descend]; exact memLp_one_iff_integrable.2 hIO
    exact memLp_one_iff_integrable.1 ((GlobalTheory.AutomorphicL2Unitary.memLp_quotMeasure_iff hF).2 h1)
  · show ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ V) Φ q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure (GQ V) μ = _
    rw [GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure hF]
    simp only [hL.descend_mk]
    rw [hsum, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hcard]

end GlobalTheory.NormDictClassSum
