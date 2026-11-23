import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFramesStrongApproximationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeRealCompletion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagDomainDataPrincipalCongruenceLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormOneTorusClassNumberBoundProof
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryDetIsTA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivalenceGeneratedTorusRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaTermTsumLeTwo
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LogClassNumberLeLogAbsDiscrDiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelIndexBoundOfPrintsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyCompactSecondCountableBorelCountable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsInertPlOfInertOff
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
import Formalism.LocalToGlobal.LatticeGeometry.DegFlLApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousEquivariantDetOneFactorProjectioStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupMeasureDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagDomainOrthonormalFrameIdentificationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousRealComponentHomUnitaryAdelicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureTranslateLevelRealBoxLeIndexMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCountableCosetRepresentativesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePartMemFullLevelOfKeepsSelfDualLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCompletionImageFinHomMulVecStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundamentalSetMeasureRealSUStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExplicitHeightBoundLogDiscriminantStatement

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.VolUp

theorem measure_le_tsum_of_cover {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G)
    [μ.IsMulLeftInvariant] (Γ : Subgroup G) [Countable Γ] {𝓕 : Set G} (h : IsFundamentalDomain Γ 𝓕 μ) {J : Type} [Countable J]
    (S : J → Set G) (hS : ∀ j, MeasurableSet (S j)) (hc : ∀ x, ∃ j, ∃ γ ∈ Γ, γ * x ∈ S j) : μ 𝓕 ≤ ∑' j, μ (S j) := by
  refine le_trans ?_ (measure_iUnion_le S)
  rw [h.measure_eq_tsum (⋃ j, S j)]
  refine le_trans (measure_mono ?_) (measure_iUnion_le _)
  intro x hx
  obtain ⟨j, γ, hγ, hj⟩ := hc x
  refine Set.mem_iUnion.2 ⟨(⟨γ, hγ⟩ : Γ)⁻¹, ?_, hx⟩
  rw [Set.mem_inv_smul_set_iff]
  exact Set.mem_iUnion.2 ⟨j, hj⟩

noncomputable def torBd (E : Type) [Field E] [NumberField E] (r : ℕ) : ℝ :=
  (classNumber E : ℝ) * 3 ^ (2 * fdeg E) * ((3 : ℝ) ^ (2 * fdeg E * r ^ 2) * rdE E ^ ((fdeg E : ℝ) * ((r : ℝ) ^ 2 - 1) / 2) *
    (Real.sqrt r * ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i) ^ fdeg E)

theorem sum_covolume_le_torBd (hT : GlobalTheory.Published.TamagawaSpecialUnitary) (E : Type) [Field E] [NumberField E] [IsCMField E]
    (r m : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (X : Fin m → Data E r)
    (g : Fin m → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)) (x0 : ∀ i, Frame (X i).Ψ r)
    (hr : 2 ≤ r) (hU : Unr E) (hSD : SelfDualLat G Λ)
    (hUA : ∀ i, IsUA (IsCMField.complexConj E) G (g i))
    (hdist : ∀ i j, UEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) 3 (g i) (g j) → i = j)
    (hX : ∀ i, (X i).Gm = G ∧ (X i).Ψ = Ψ ∧
      ((X i).Λ : Set (Fin r → E)) = latOf (maximalRealSubfield E) (g i) (Λ : Set (Fin r → E)) ∧
      (∀ γ, γ ∈ (X i).Γ ↔ IsUStab G (X i).Λ γ ∧
        ∀ x ∈ (X i).Λ, ∃ y ∈ (X i).Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ x - x = 3 • y) ∧ IsOrth (X i) (x0 i)) :
    ∑ i, covolume (inReal (X i).Ψ (X i).Gm (X i).Γ) (realSU (X i).Ψ (X i).Gm) (riemHaar (X i).Ψ (X i).Gm (x0 i)) ≤
      ENNReal.ofReal (torBd E r) := by
  classical
  have htor := GlobalTheory.UCls.torusBound E r 3 G Λ (by omega) (by omega) hU hSD
  set h : ℕ := classNumber E * 3 ^ (2 * fdeg E) with hh
  set K : ℝ := ((3 : ℕ) : ℝ) ^ (2 * fdeg E * r ^ 2) * rdE E ^ ((fdeg E : ℝ) * ((r : ℝ) ^ 2 - 1) / 2) *
    (Real.sqrt r * ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i) ^ fdeg E with hK
  let cv : Fin m → ℝ≥0∞ := fun i => covolume (inReal (X i).Ψ (X i).Gm (X i).Γ) (realSU (X i).Ψ (X i).Gm)
    (riemHaar (X i).Ψ (X i).Gm (x0 i))
  have hTA : ∀ i, IsTA (IsCMField.complexConj E) (g i).det := fun i => GlobalTheory.unitary_det_isTA E r G (g i) hSD.2.1 (hUA i)
  let f : Fin m → Quot fun a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t} =>
      TEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) 3 a.1 b.1 := fun i => Quot.mk _ ⟨(g i).det, hTA i⟩
  have hQfin : Finite (Quot fun a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t} =>
      TEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) 3 a.1 b.1) := by
    by_contra hinf
    rw [not_finite_iff_infinite] at hinf
    have h1 : torusNo (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) 3 = ⊤ := ENat.card_eq_top_of_infinite
    rw [h1] at htor
    exact absurd htor (by simp)
  have hcard : (Finset.univ.image f).card ≤ h := by
    have h1 : (Finset.univ.image f).card ≤ Nat.card (Quot fun a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t} =>
        TEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) 3 a.1 b.1) := by
      haveI := Fintype.ofFinite (Quot fun a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t} =>
        TEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) 3 a.1 b.1)
      rw [Nat.card_eq_fintype_card]; exact Finset.card_le_univ _
    have h2 : ((Nat.card (Quot fun a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t} =>
        TEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) 3 a.1 b.1) : ℕ) : ℕ∞) ≤ h := by
      rw [← ENat.card_eq_coe_natCard]; exact htor
    exact h1.trans (by exact_mod_cast h2)
  have hfib : ∀ q ∈ Finset.univ.image f, ∑ i ∈ Finset.univ.filter (fun i => f i = q), cv i ≤ ENNReal.ofReal K := by
    intro q hq
    obtain ⟨i0, -, hi0⟩ := Finset.mem_image.1 hq
    refine GlobalTheory.T.unitary_frames_strong_approximation hT E r 3 m G Λ Ψ X g x0 _ (g i0) hr le_rfl hU hSD (hUA i0) hUA ?_ (fun i _ j _ => hdist i j)
      (fun i _ => hX i)
    intro i hi
    have hfi : f i0 = f i := by rw [hi0, (Finset.mem_filter.1 hi).2]
    exact GlobalTheory.UCls.torus_eqvGen_main E r 3 G (Λ : Set (Fin r → E)) ⟨(g i0).det, hTA i0⟩ ⟨(g i).det, hTA i⟩ (Quot.eqvGen_exact hfi)
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image f) (g := f)
    (fun i _ => Finset.mem_image_of_mem f (Finset.mem_univ i))]
  calc _ ≤ ∑ q ∈ Finset.univ.image f, ENNReal.ofReal K := Finset.sum_le_sum hfib
    _ = ((Finset.univ.image f).card : ℝ≥0∞) * ENNReal.ofReal K := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (h : ℝ≥0∞) * ENNReal.ofReal K := by gcongr
    _ = ENNReal.ofReal (h * K) := by rw [ENNReal.ofReal_mul (p := (h : ℝ)) (by positivity), ENNReal.ofReal_natCast]
    _ = _ := by rw [hh, hK, torBd]; push_cast; rfl

theorem exists_frame_transport {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (p0 : ℕ) (x : Frame Ψ r) (h1 : X.Ψ = Ψ) (h2 : X.Gm = G)
    (h3 : X.p0 = p0)
    (hx : ∀ τ : Ψ, ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 G (mat x τ) = Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) :
    ∃ x' : Frame X.Ψ r, IsOrth X x' ∧ covolume (inReal Ψ G X.Γ) (realSU Ψ G) (riemHaar Ψ G x) =
      covolume (inReal X.Ψ X.Gm X.Γ) (realSU X.Ψ X.Gm) (riemHaar X.Ψ X.Gm x') := by
  subst h1 h2 h3
  exact ⟨x, hx, rfl⟩

set_option maxHeartbeats 1000000 in

theorem mass_le (hT : GlobalTheory.Published.TamagawaSpecialUnitary) (D : D7) (V : HSp D) (hV : V.SigOK) (P Q : ℕ)
    (hsig : ∀ τ, V.sig τ = (P, Q)) (r : ℕ) (hrk : V.rank = r) (hr : 2 ≤ r) (hU : Unr D.host.E)
    (K K₀ : Subgroup (GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))) (hle : K ≤ K₀) (hn : K.relIndex K₀ ≠ 0)
    (hKo : IsOpen {h : GA D V | finE V h ∈ K}) (hK₀o : IsOpen {h : GA D V | finE V h ∈ K₀})
    (hK₀ : ∀ h : GA D V, IsKM (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) 1
      ((finHom V h).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) → finE V h ∈ K₀)
    (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (hF : IsMeasFD V K μ 𝓕) :
    μ 𝓕 ≤ (K.relIndex K₀ : ℝ≥0∞) *
      ENNReal.ofReal ((1000 * (D.R.f : ℝ) * (r : ℝ) ^ 3) ^ (D.R.f * r ^ 2)) * ENNReal.ofReal (torBd D.host.E r) := by
  classical
  subst hrk
  obtain ⟨-, -, hB, hC⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable V
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI := hF.1.1
  obtain ⟨⟨θ, hθ⟩, H1⟩ := hF.1.2
  obtain ⟨⟨A, hA⟩, H2⟩ := H1 θ hθ
  obtain ⟨⟨m, hm⟩, -⟩ := H2 A hA
  obtain ⟨X₀, σ, x, e, hG, hσ, hx, hid⟩ := GlobalTheory.T.exists_flagDomain_orthonormalFrame_identification D V P Q hV hsig A hA
  have hcard : X₀.Ψ.card = D.R.f := by
    rw [← Fintype.card_coe, ← Fintype.card_congr σ, D.what₂.card_Tau]
  have hf : 1 ≤ X₀.Ψ.card := by rw [hcard]; unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity); omega
  obtain ⟨rp, hrpc, hrp⟩ := GlobalTheory.T.exists_continuous_realComponentHom_unitaryAdelic D V θ A hV hθ hA
  let a₀ : ∀ ρ : D.what₂.Tau, Fin (V.sig (tauE D ρ)).1 ⊕ Fin (V.sig (tauE D ρ)).2 := fun ρ => (e ρ).symm ⟨0, by omega⟩
  obtain ⟨π, hπc, hπ, hπe⟩ := GlobalTheory.T.exists_continuous_equivariant_detOneFactorProjection D.host.E V.rank D.what₂.Tau _ _ X₀.Ψ X₀.Gm x σ A e a₀ hid
  have hreal := GlobalTheory.T.unitary_group_measure_decomposition D.host.E V.rank D.what₂.Tau _ _ X₀.Ψ X₀.Gm x σ A e a₀ π m (by omega) hf hid hπc hπ hπe hm
  rw [hcard] at hreal
  obtain ⟨J, hJ, g, hg, hdist, hcov⟩ := GlobalTheory.T.exists_countable_coset_representatives D V (GlobalTheory.Member.latC V) K₀ hK₀o hK₀
  have hSD := GlobalTheory.Member.selfDualLat_neg_gram_transpose D V
  have hUA := fun j => GlobalTheory.FinUA.isUA_finHom D V (g j)
  choose L hL hLhat hLsd using fun j => GlobalTheory.UCls.selfDual_latOf_translate D.host.E V.rank _ _ _ hSD (hUA j)
  choose X hXG hXΨ hXp hXΛ hXΓ using fun j =>
    GlobalTheory.PrincData.exists_princ_data D.host.E V.rank 3 X₀ (L j) le_rfl (hLsd j).2.2.1 (hLsd j).2.2.2.1
  haveI : (riemHaar X₀.Ψ X₀.Gm x).IsMulLeftInvariant := by unfold riemHaar; infer_instance
  choose S hSm hSv hSc using fun j => GlobalTheory.T.exists_fundamental_set_measure_realSU_stabilizer D.host.E V.rank X₀.Ψ X₀.Gm (L j) (X j).Γ (riemHaar X₀.Ψ X₀.Gm x) X₀.cmType
    (hLsd j).2.2.1 (hLsd j).2.2.2.1 (fun γ hγ => ((hXΓ j γ).1 hγ).1)
  choose y hy hyv using fun j => exists_frame_transport (X j) X₀.Ψ X₀.Gm X₀.p0 x (hXΨ j) (hXG j) (hXp j) hx
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
  have hBm : ∀ j, MeasurableSet (π ⁻¹' S j) := fun j => hπc.measurable (hSm j)
  let T : J → Set (GA D V) := fun j => {h | finE V ((g j)⁻¹ * h) ∈ K₀ ∧ rp h ∈ π ⁻¹' S j}
  have hTm : ∀ j, MeasurableSet (T j) := fun j =>
    ((hK₀o.preimage (continuous_const.mul continuous_id)).measurableSet).inter (hrpc.measurable (hBm j))
  have hTc : ∀ h, ∃ j, ∃ γ ∈ GQ V, γ * h ∈ T j := by
    intro h
    obtain ⟨j, γ, hγ, hk⟩ := hcov h
    obtain ⟨δ, hδ, hδs, hδS⟩ := hSc j (π (rp (γ * h)))
    obtain ⟨γ', hγ', hinf, hKM⟩ := GlobalTheory.T.lattice_completion_image_finHom_mulVec D V (GlobalTheory.Member.latC V) (L j) (g j) δ (hLhat j) (hG ▸ ((hXΓ j δ).1 hδ).1)
    refine ⟨j, γ' * γ, (GQ V).mul_mem hγ' hγ, ?_, ?_⟩
    · have := K₀.mul_mem (hK₀ _ hKM) hk
      rw [← map_mul] at this
      convert this using 2
      group
    · change π (rp (γ' * γ * h)) ∈ S j
      rw [mul_assoc, map_mul, hπe ⟨embGL X₀.Ψ V.rank δ, hδs⟩ (rp γ') fun ρ => ?_]
      · exact hδS
      · rw [hrp γ' ρ, hinf (σ ρ).1 _ ((hσ ρ).symm ▸ hθ ρ)]
        rfl
  set C := ENNReal.ofReal ((1000 * (D.R.f : ℝ) * (V.rank : ℝ) ^ 3) ^ (D.R.f * V.rank ^ 2)) with hC'
  have hTle : ∀ j, μ (T j) ≤ (K.relIndex K₀ : ℝ≥0∞) * C *
      covolume (inReal (X j).Ψ (X j).Gm (X j).Γ) (realSU (X j).Ψ (X j).Gm) (riemHaar (X j).Ψ (X j).Gm (y j)) := by
    intro j
    refine (GlobalTheory.T.measure_translateLevel_realBox_le_index_mul D V θ A m rp K K₀ μ hV hθ hA hm hrpc hrp hle hn hKo hF.1 (g j) (hg j) _ (hBm j)).trans ?_
    rw [mul_assoc, ← hyv j, ← hSv j]
    gcongr
    exact hreal _ (hSm j)
  refine (measure_le_tsum_of_cover μ (GQ V) hF.2 T hTm hTc).trans ((ENNReal.tsum_le_tsum hTle).trans ?_)
  rw [ENNReal.tsum_mul_left]
  gcongr
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  rw [← Finset.sum_coe_sort s, ← s.equivFin.symm.sum_comp]
  exact sum_covolume_le_torBd hT D.host.E V.rank s.card _ (GlobalTheory.Member.latC V) X₀.Ψ (fun i => X (s.equivFin.symm i))
    (fun i => (finHom V (g (s.equivFin.symm i))).1) (fun i => y (s.equivFin.symm i)) hr hU hSD (fun i => hUA _)
    (fun i j h => s.equivFin.symm.injective (Subtype.ext (hdist _ _ h)))
    (fun i => ⟨(hXG _).trans hG, hXΨ _, by rw [hXΛ]; exact hL _, fun γ => by rw [hXΛ, hXΓ, hG], hy _⟩)

end GlobalTheory.CovTop.VolUp

namespace GlobalTheory.CovTop.VolUp

open Formalism.IndefR.Links in

theorem log_mass_le (hP : GlobalTheory.CovTop.Hypotheses2) (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0) (i : Fin D.R.m)
    (P : Formalism.L2.DIV.LevelP C.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i)))
    (hF : IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i P) μ 𝓕) (L : ℝ) (hL : GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.Sizes D L) :
    Real.log (μ 𝓕).toReal ≤ D.R.f * (D.R.r : ℝ) ^ 2 * Real.log ((D.R.r : ℝ) + 3) + (38 + 81) * (D.R.f * (D.R.r : ℝ) ^ 2 * L) := by
  obtain ⟨hn, hnl⟩ := GlobalTheory.T.level_index_bound_of_classicalTheorems hP D Tu C t0 hC i P
  have hrk : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hr : 2 ≤ D.R.r := Formalism.L2.Geo.two_le_r D
  have hm := mass_le hP.p6 D (Wc D i) (D.sp.W_sig _) _ _ (D.sp.W_sigval _ (Nat.le_add_left _ _) i.2) _ hrk hr
    (GlobalTheory.InertOfConj.unram D) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i P) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i (Formalism.L2.DIV.LevelP.full _ _ _))
    (fun k hk => ⟨hk.1, Subgroup.mem_top _⟩) hn (GlobalTheory.ParahoricCompact.isOpen_comap_lev _ _ _)
    (GlobalTheory.ParahoricCompact.isOpen_comap_lev _ _ _)
    (GlobalTheory.T.finitePart_mem_fullLevel_of_keeps_selfDualLattice D (Wc D i) (C.βW i) (C.ΛW i) _ (hC.βW i) hrk.le rfl) μ 𝓕 hF
  set n := (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i P).relIndex (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i (Formalism.L2.DIV.LevelP.full _ _ _)) with hndef
  have hfin : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [show Module.finrank ℚ D.host.E = 4 * D.R.ord from D.host.finrank_cmField]
    unfold Ranks.f Ranks.n; ring
  have hfd : fdeg D.host.E = D.R.f := by unfold fdeg; omega
  have hf : 2 ≤ D.R.f := by unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity); omega
  have hnV : D.R.r ≤ D.R.nV := Nat.le_add_right _ _
  obtain ⟨h1, -, h3, h4⟩ := hL
  have hfR : (2 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hrR : (2 : ℝ) ≤ D.R.r := by exact_mod_cast hr
  have hnR : (D.R.r : ℝ) ≤ D.R.nV := by exact_mod_cast hnV
  have hfr : (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 ≤ Real.exp L := by
    refine le_trans ?_ h1
    rw [sq, ← mul_assoc]; gcongr
  have hL1 : 1 ≤ L := by
    have : Real.exp 1 ≤ Real.exp L := by
      have := Real.exp_one_lt_d9
      nlinarith
    exact Real.exp_le_exp.1 this
  have hd1 : (1 : ℝ) ≤ |(discr D.host.E : ℝ)| := by
    have := Int.one_le_abs (discr_ne_zero D.host.E)
    exact_mod_cast this
  have hrd1 : 1 ≤ rdE D.host.E := Real.one_le_rpow hd1 (by positivity)
  have hlog : Real.log (rdE D.host.E) = Real.log |(discr D.host.E : ℝ)| / (2 * D.R.f) := by
    unfold rdE dE
    rw [Real.log_rpow (by linarith), hfin]; push_cast; ring
  have hh := GlobalTheory.log_classNumber_le_log_abs_discr_div D.host.E D.R.f hfin
  rw [← hlog] at hh
  have hrdL : Real.log (rdE D.host.E) ≤ 2 * L := by
    have : rdE D.host.E = D.host.rdE := rfl
    rw [this]; linarith [abs_nonneg (dlogL D 1)]
  have hP0 : 0 ≤ Real.sqrt D.R.r * ∏ i ∈ Finset.Icc 2 D.R.r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i :=
    mul_nonneg (Real.sqrt_nonneg _) (Finset.prod_nonneg fun i _ => tsum_nonneg fun n => by positivity)
  have ha := GlobalTheory.T.explicit_height_bound_log_discriminant D.R.f D.R.r L n _ (classNumber D.host.E) (rdE D.host.E) _ hf hr hL1 hfr hrd1 hrdL
    (by exact_mod_cast Nat.pos_of_ne_zero hn) hnl h3 (by exact_mod_cast classNumber_pos D.host.E) hh hP0
    (GlobalTheory.volumeConstant_le D.R.r hr)
  have hle : (μ 𝓕).toReal ≤ Real.exp (119 * (D.R.f * (D.R.r : ℝ) ^ 2 * L)) := by
    refine ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le (hm.trans ?_)
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    unfold torBd
    rw [hfd]
    exact ha
  have h0 : 0 ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * Real.log ((D.R.r : ℝ) + 3) :=
    mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
  have h5 : Real.log (μ 𝓕).toReal ≤ 119 * (D.R.f * (D.R.r : ℝ) ^ 2 * L) := by
    rcases (ENNReal.toReal_nonneg (a := μ 𝓕)).eq_or_lt with h | h
    · rw [← h, Real.log_zero]; positivity
    · exact (Real.log_le_iff_le_exp h).2 hle
  linarith

end GlobalTheory.CovTop.VolUp
