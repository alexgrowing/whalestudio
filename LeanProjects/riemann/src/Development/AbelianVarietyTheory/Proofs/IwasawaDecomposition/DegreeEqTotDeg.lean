import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAlgOfFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntMulMemInvHalfDifferent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotMemVGsOfMemQE
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPreHasLetters
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrdSubConjEqNeg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GmapToAddSubgroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmulLatMatOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetIdLatGmap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VacuumEntireAndNormalizedJetsAlgebraicStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAlgJetSet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalisedFamilySatisfiesEquivarianceLawsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsWeilOThZeroTriv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovesOfSelfDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanRangeEmb4EqTop
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalisedFamilyLatticeHypAndSmooth
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AbsNormEqOfSplit
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NotDvdDifferent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeTransportPreservesSelfDual

noncomputable section

namespace GlobalTheory.Mem.Col2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker
open ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open Formalism.L2.Host (HChar)

namespace JetEx

@[reducible] def hostFields {R : Ranks} (H : Host R) : Fields where
  F := H.F
  E := H.E
  K := H.E
  starE := H.cmStar
  starK := H.cmStar
  Tau := Tau R
  deTau := Classical.decEq _
  emb τ := (H.sigmaOf (τ : R.GG) : H.E →+* H.E)

def hostAmb {R : Ranks} {H : Host R} (J : AmbIn H) (χ : Submodule (𝓞 H.E) H.E → ℂ) : Amb (hostFields H) where
  σ₀ := H.φ₀
  δ := J.δ
  d := H.d
  sc := (TaylorLogMetric.area (Th.lamOf H ⊤ J.δ))⁻¹
  AA := Th.perAA H ⊤
  cD := J.cD
  e a b N N' := J.V.eNat χ a b N N'
  chiF a b N N' := Th.chiFac H χ a b N N'

theorem jetSet_amb (B : Base) (J : AmbIn B.host) (χ : Submodule (𝓞 B.host.E) B.host.E → ℂ) (a b : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 B.host.E))) (M n : ℕ) :
    jetSet (J.amb B χ) a b S M n = jetSet (hostAmb J χ) a b S M n := by
  have h : B.fields.embC (J.amb B χ).σ₀ = (hostFields B.host).embC (hostAmb J χ).σ₀ := funext fun τ => B.fields_embC τ
  have h2 : ∀ N N' c x, (J.amb B χ).thInd (a := a) (b := b) S N N' c x = (hostAmb J χ).thInd S N N' c x := by
    intro N N' c x
    unfold Amb.thInd
    rw [h]
    rfl
  unfold jetSet
  simp only [h2]
  rfl

open Classical in

@[reducible] def hostWts (P : Pre) : Wts (hostFields P.host) P.Word P.R where
  row := fun τ => RowPar.of (P.hc τ)
  hc := P.hcW
  tops := Finset.univ.filter fun τ : Tau P.R => (τ : P.R.GG) ∈ P.host.topPlaces

def totDeg (P : Pre) (u : P.Word) (i : ℕ) : ℕ := (∑ τ, ∑ r, ((hostWts P).nuW u (i + 1) τ).w r).toNat

theorem degree_eq_totDeg (B : Base) (u : B.Word) (i : ℕ) (e : DVar B.fields.Tau (B.R.N i) (B.R.N (i + 1)) →₀ ℕ)
    (he : ∀ τ, (monoDeg e τ : ℤ) = nuDeg B u i τ) : e.degree = totDeg B.toPre u i := by
  have h1 : e.degree = ∑ τ, monoDeg e τ := by
    simp only [monoDeg_eq_sum]
    rw [Finsupp.degree_eq_sum, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun τ _ => Fintype.sum_prod_type _
  have h2 : ((∑ τ, monoDeg e τ : ℕ) : ℤ) = ∑ τ, ∑ r, ((hostWts B.toPre).nuW u (i + 1) τ).w r := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl fun τ _ => he τ
  rw [h1, totDeg, ← h2, Int.toNat_natCast]

def ramSet {R : Ranks} (H : Host R) (ξ : HChar H.E) : Set (HeightOneSpectrum (𝓞 H.F)) :=
  {v | ¬ ∀ a : Ideles H.E, finAf H.F H.E a ∈ inertAt H.E v → ξ.1 a = 1}

theorem qprime_eq_ramSet {R : Ranks} (H : Host R) {K : Type} [Field K] {σ : K →+* ℂ} {μ : Chr H.F H.E K} {ξ : HChar H.E}
    (h : Reads σ μ ξ) : Qprime μ = ramSet H ξ := by
  have key : ∀ a, ξ.1 a = 1 ↔ μ (finAf H.F H.E a) = 1 := fun a => by
    rw [Units.ext_iff, h a, Units.ext_iff, Units.val_one, Units.val_one, map_eq_one_iff _ σ.injective]
  ext v
  refine not_congr ⟨fun h1 a ha => (key a).2 (h1 ha), fun h1 y hy => ?_⟩
  obtain ⟨a, rfl⟩ := finAf_surjective H.F H.E y
  exact (key a).1 (h1 a hy)

def badP (P : Pre) (Ξ : Set (HChar P.host.E)) : Set (HeightOneSpectrum (𝓞 P.host.E)) :=
  (⋃ u, {Q | ((P.T u : ℕ) : 𝓞 P.host.E) ∈ Q.asIdeal}) ∪ (⋃ i, {Q | ((P.host.g i : ℕ) : 𝓞 P.host.E) ∈ Q.asIdeal}) ∪
    ⋃ ξ ∈ {ξ ∈ Ξ | (ramSet P.host ξ).Finite}, ⋃ v ∈ ramSet P.host ξ, {Q | Q.asIdeal.under (𝓞 P.host.F) = v.asIdeal}

theorem finite_mem {E : Type} [Field E] [NumberField E] {a : 𝓞 E} (ha : a ≠ 0) :
    {Q : HeightOneSpectrum (𝓞 E) | a ∈ Q.asIdeal}.Finite := by
  simpa only [Ideal.dvd_span_singleton] using Ideal.finite_factors (I := Ideal.span {a}) (by simpa using ha)

theorem badPrimes_finite₂ (P : Pre) {Ξ : Set (HChar P.host.E)} (h : Ξ.Finite) : (badP P Ξ).Finite := by
  refine ((Set.finite_iUnion fun u => finite_mem ?_).union (Set.finite_iUnion fun i => finite_mem ?_)).union
    ((h.subset fun _ hξ => hξ.1).biUnion fun ξ hξ => Set.Finite.biUnion hξ.2 fun v _ => ?_)
  · exact Nat.cast_ne_zero.2 (P.T_prime u).ne_zero
  · exact Nat.cast_ne_zero.2 (P.host.g_prime i).ne_zero
  · obtain ⟨a, ha, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    refine (finite_mem (a := algebraMap (𝓞 P.host.F) (𝓞 P.host.E) a) ?_).subset fun Q hQ => ?_
    · exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).2 h0
    · have : a ∈ Q.asIdeal.under (𝓞 P.host.F) := hQ ▸ ha
      exact this

theorem mem_of_mem_divs {A : Type} [CommRing A] [IsDedekindDomain A] {a : A} {Q : HeightOneSpectrum A} (h : Q ∈ divs a) :
    a ∈ Q.asIdeal := by
  unfold divs at h
  split_ifs at h with h1
  · exact h1.mem_toFinset.1 h
  · simp at h

variable {B : Base} {X : PreX B.toPre}

theorem rowSG_subset {I : ColIn B X} (h : I.Ok) (a : I.ι) :
    ∀ Q ∈ rowSG (B.primes X) I.sel (I.tup a), Q ∈ badP B.toPre (Set.range I.xi) := by
  classical
  intro Q hQ
  rcases Finset.mem_union.1 hQ with hQ | hQ
  · obtain ⟨i, hi⟩ : ∃ i, Q ∈ (B.primes X).vG i := by
      rcases Finset.mem_union.1 hQ with h | h
      exacts [⟨0, h⟩, ⟨1, h⟩]
    refine Or.inl (Or.inr (Set.mem_iUnion.2 ⟨i, ?_⟩))
    have := Q.asIdeal.mul_mem_left ((B.primes X).piG i) (mem_of_mem_divs hi)
    rwa [B.primes_piG_norm X i] at this
  · unfold QE at hQ
    split_ifs at hQ with h1
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hQ
      have e := qprime_eq_ramSet B.host (h.xi_reads a)
      exact Or.inr (Set.mem_iUnion₂.2 ⟨I.xi a, ⟨⟨a, rfl⟩, e ▸ h1⟩,
        Set.mem_iUnion₂.2 ⟨v, e ▸ h1.mem_toFinset.1 hv, h.sel_ok v⟩⟩)
    · simp at hQ

theorem Sb_subset {I : ColIn B X} (h : I.Ok) (a : I.ι) (u : B.Word) :
    ∀ Q ∈ I.Sb a u, Q ∈ badP B.toPre (Set.range I.xi) := by
  classical
  intro Q hQ
  rcases Finset.mem_union.1 hQ with hQ | hQ
  · refine Or.inl (Or.inl (Set.mem_iUnion.2 ⟨u, ?_⟩))
    have := Q.asIdeal.mul_mem_right (B.fields.conjO ((B.primes X).piT u)) (mem_of_mem_divs hQ)
    rwa [B.primes_piT_norm X u] at this
  · exact rowSG_subset h a Q hQ

section Lat

open Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.ThetaMove.SeamMoves

theorem eNat_mem {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (V : Formalism.L2.Ker.Base D cc δ) (hc : StandardLatticesGL3.Crv D cc δ)
    (χ : TaylorLogMetric.IdE D → ℂ) {a b : ℕ} {L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)}
    (hL : StandardLatticesGL3.SD D L) (hL' : StandardLatticesGL3.SD D L') : V.eNat χ a b L L' ∈ TaylorLogMetric.Th D (TaylorLogMetric.tor0 D cc δ) L L' := by
  have s0 := GlobalTheory.VacuumScalar.sd_of_moves (GlobalTheory.VacuumScalar.moves_one D a)
  have s0' := GlobalTheory.VacuumScalar.sd_of_moves (GlobalTheory.VacuumScalar.moves_one D b)
  have h0 := WeilVac.thZero_mem V (GlobalTheory.FourthRootStd.stdOK_of_crv D cc δ V hc) a b
  have h1 := (GlobalTheory.theta_translation_intertwiner_unitary D cc δ hc a b _ _ (Or.inr ⟨_, _, s0, s0', rfl⟩)
    (Or.inr ⟨_, _, hL, s0', rfl⟩) _ h0).2.1
  have h2 := (GlobalTheory.theta_translation_intertwiner_unitary D cc δ hc a b _ _ (Or.inr ⟨_, _, hL, s0', rfl⟩)
    (Or.inr ⟨_, _, hL, hL', rfl⟩) _ h1).2.1
  exact GlobalTheory.InertSign.ThSp_smul (Formalism.L2.Ker.Base.chiFac χ a b L L') h2

theorem laHyp_empty {D : D7} {X : Fields} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (V : Formalism.L2.Ker.Base D cc δ)
    (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) {a b : ℕ} (hX : X.Ok) (hs : s.Ok) (hc : StandardLatticesGL3.Crv D cc δ) (ha : Even a) (hb : Even b) :
    (ambOf s V χ cD).LaHyp a b ∅ := by
  have hL := LatticeFacts.latAll V hc.1 hc.2
  obtain ⟨hsd, hlam⟩ := GlobalTheory.PeriodTransport.seam_lattices X D s cc δ V χ cD hs
  have hq := qIntAll_of_latAll D cc δ V hL
  have hadm : ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N' →
      TaylorLogMetric.admitted D a b (s.lat N) (s.lat N') := fun N N' h h' => ⟨ha, hb, hsd _ _ h, hsd _ _ h'⟩
  refine ⟨delta_ne_zero V, Fintype.card_pos_iff.1 hX.f_pos, by simp, fun P hP => absurd hP (Finset.notMem_empty P),
    aa_fg s V χ cD, fun N N' h h' => ?_⟩
  obtain ⟨h1, h2, h3⟩ := (Transport.inter_transport _ _ (reidx s a b) (Formalism.L2.Ker.HV (ambOf s V χ cD).sc)
    (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (alV (ambOf s V χ cD).d (ambOf s V χ cD).sc) (TaylorLogMetric.al D V.tor)
    (lam (ambOf s V χ cD) N N') (lam (ambOf s V χ cD) N N') (TaylorLogMetric.La D V.tor (s.lat N) (s.lat N'))
    (TaylorLogMetric.La D V.tor (s.lat N) (s.lat N')) 0 (form_reidx s _ a b) (hlam a b N N') (hlam a b N N')
    (fun x hx => by
      obtain ⟨m, hm⟩ := hq a b _ _ (hadm N N' h h') (reidx s a b x) ((hlam a b N N' x).1 hx)
      exact alV_eq s V x hm)
    (isHerm_formV _ _ _ _) (hL.1 a b _ _ (hadm N N' h h')).1 (hL.1 a b _ _ (hadm N N' h h')).2).1
  exact ⟨h3 (V.eNat χ a b (s.lat N) (s.lat N')) (eNat_mem V hc χ (hsd _ _ h) (hsd _ _ h')).2, h1, h2⟩

end Lat

theorem finAlg_step (hL : StagesInhab.HasLetters B.toPre) {I : ColIn B X} (h : I.Ok) (a : I.ι) (u : B.Word) (i j M n : ℕ)
    (hM : 0 < M) : FinAlg (jetSet I.A (B.R.N i) (B.R.N j) (I.Sb a u) M n) := by
  obtain ⟨⟨B, C, W, V, S, N, G⟩, rfl, -⟩ := StagesInhab.exists_stages_over B hL 1
  have hs := seamOf_ok B C W V S N G
  obtain ⟨hδ, hc⟩ := (AmbIn.ok_iff B C W V S N G I.J).1 h.amb_ok
  have hcc : TaylorLogMetric.IsCurveIdeal (assemble B C W V S N G) ⊤ := ⟨top_ne_bot, by simp⟩
  have hχ : TaylorLogMetric.IsChi (assemble B C W V S N G) I.chi := GlobalTheory.Mem.ChiIdeal.isChi_chiId _ _ I.C.isChi
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  have hi := GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree.even_N B.R i
  have hj := GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree.even_N B.R j
  have hA : I.A = ambOf (seamOf B C W V S N G) (I.J.toRec B C W V S N G) I.chi I.J.cD :=
    AmbIn.amb_eq_ambOf B C W V S N G I.J I.chi
  have hne : I.A.AA ≠ ⊥ := by
    rw [hA]
    exact GlobalTheory.ThetaMove.SeamMoves.aa_ne_bot _ _ _ _ top_ne_bot
  have hLa : I.A.LaHyp (B.R.N i) (B.R.N j) (I.Sb a u) := by
    have bad := GlobalTheory.ThetaMove.BadPrimes.bad_primes _ (B.primes X) I.sel I.S (I.tup a) u hX hPr h.sel_ok (h.T_mem u) h.g_mem
    have h0 := laHyp_empty (seamOf B C W V S N G) (I.J.toRec B C W V S N G) I.chi I.J.cD hX hs ⟨hcc, hδ⟩ hi hj
    rw [hA]
    exact ⟨h0.1, h0.2.1, fun P hP => (bad P hP).1, fun P hP => GlobalTheory.PeriodIdealUnit.locP_AA_eq_one _ _ _ _ _ _ _ _ P
      (bad P hP).2.1 (bad P hP).2.2.1 (by rw [Ideal.absNorm_top]; exact Nat.coprime_one_left _), h0.2.2.2.2⟩
  have hE := GlobalTheory.T.normalisedFamily_satisfies_equivarianceLaws _ _ _ (I.J.toRec B C W V S N G) _ hcc hδ hχ
  have hJ := GlobalTheory.T.vacuum_entire_and_normalizedJets_algebraic _ _ (seamOf B C W V S N G) _ _ (I.J.toRec B C W V S N G) I.chi I.J.cD _ _ hX hs hcc hδ hχ hi hj
  rw [← hA] at hJ
  refine JetFin.finAlg_jetSet _ _ _ _ _ _ _ hX hM hJ.1 (IndEq.thIndEq_of_vacEq _ _ _ _ _ _ hX hLa hne hM ?_) ?_ (hJ.2 _ _)
    fun τ => ?_
  · rw [hA]
    exact VacEqPf.vacEq_ambOf _ _ _ _ _ _ _ _ _ _ hs hE hi hj
  · rw [hA]
    exact ChiFacLaw.chiLaw_ambOf _ _ _ _ _ _ _ _ _ _ hs hχ
  · obtain ⟨K, _, -, hK⟩ := h.amb_ok.dgen
    obtain ⟨s, hs, -⟩ := hK τ
    rw [I.A_cD, ← hs]
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) s).algHom K.val

theorem exists_replace {I : ColIn B X} (h : I.Ok) (J : AmbIn B.host) (hJ : J.Ok)
    (hr : ∀ a, ∀ Q ∈ rowSG (B.primes X) I.sel (I.tup a), ∃ ζ : B.LL, IsPrimitiveRoot ζ (qOf Q ^ (2 * B.R.m))) :
    ∃ I' : ColIn B X, I'.Ok ∧ I'.C = I.C ∧ I'.S = I.S ∧ Set.range I'.xi = Set.range I.xi ∧ I'.J = J ∧
      ∀ a, (I'.cst a).A = B.R.m ∧ (I'.cst a).B = B.R.m := by
  have hX := base_fields_primes_ok B X
  choose cst idx h1 h2 h3 h4 h5 h6 h7 using fun a => exists_chIdx hX.1 hX.2.1 I.Ch I.sel h.sel_ok h.g_mem (I.tup a) I.glob
    (fun j τ => (B.hc τ).e j) (fun j τ => (B.hc τ).e_int j) I.C.eta h.ch_tied h.weil (h.idx_ok a).xiUnitAtPrime
    B.R.m B.R.m B.R.m (2 * B.R.m) le_rfl le_rfl le_rfl le_rfl (fun P => ⟨_, (h.idx_ok a).cst_ok.sq_sq P⟩)
    (fun P _ => hr a P.1 P.2)
  exact ⟨{ I with cst := cst, idx := idx, J := J }, { h with sharp := h1, idx_ok := h6, amb_ok := hJ }, rfl, rfl, rfl, rfl,
    fun a => ⟨h3 a, h4 a⟩⟩

def amb0 {R : Ranks} (H : Host R) : AmbIn H := (exists_ambIn_ok H).choose

def stepSet (P : Pre) (χ : HChar P.host.E)
    (k : P.Word × ℕ × Finset (HeightOneSpectrum (𝓞 P.host.E)) × Finset (HeightOneSpectrum (𝓞 P.host.E))) : Set ℂ :=
  jetSet (hostAmb (amb0 P.host) (chiId χ)) (P.R.N k.2.1) (P.R.N (k.2.1 + 1)) k.2.2.1
    ((∏ Q ∈ k.2.2.2, qOf Q) ^ P.R.m * (P.T k.1 * (∏ Q ∈ k.2.2.2, qOf Q) ^ P.R.m)) (totDeg P k.1 k.2.1)

def allSet (P : Pre) (χ : HChar P.host.E) (Ξ : Set (HChar P.host.E)) : Set ℂ :=
  (⋃ k ∈ {k : P.Word × ℕ × Finset (HeightOneSpectrum (𝓞 P.host.E)) × Finset (HeightOneSpectrum (𝓞 P.host.E)) |
      (k.2.1 < P.R.m ∧ (∀ Q ∈ k.2.2.1, Q ∈ badP P Ξ) ∧ ∀ Q ∈ k.2.2.2, Q ∈ badP P Ξ) ∧ FinAlg (stepSet P χ k)}, stepSet P χ k) ∪
    (fun Q => Complex.exp (2 * Real.pi * Complex.I / ((qOf Q ^ (2 * P.R.m) : ℕ) : ℂ))) '' badP P Ξ

theorem qPow_ne_zero {E : Type} [Field E] [NumberField E] (Q : HeightOneSpectrum (𝓞 E)) (n : ℕ) : qOf Q ^ n ≠ 0 :=
  pow_ne_zero _ (Ideal.absNorm_eq_zero_iff.not.2 Q.ne_bot)

theorem finAlg_allSet (P : Pre) (χ : HChar P.host.E) {Ξ : Set (HChar P.host.E)} (h : Ξ.Finite) : FinAlg (allSet P χ Ξ) := by
  have hb := badPrimes_finite₂ P h
  have hs : {S : Finset (HeightOneSpectrum (𝓞 P.host.E)) | ∀ Q ∈ S, Q ∈ badP P Ξ}.Finite :=
    hb.toFinset.powerset.finite_toSet.subset fun S hS =>
      Finset.mem_coe.2 (Finset.mem_powerset.2 fun Q hQ => hb.mem_toFinset.2 (hS Q hQ))
  refine (finAlg_biUnion ?_ fun k hk => hk.2).union (finAlg_of_finite (hb.image _) ?_)
  · exact (Set.finite_univ.prod ((Set.finite_Iio P.R.m).prod (hs.prod hs))).subset fun k hk => ⟨trivial, hk.1⟩
  · rintro _ ⟨Q, -, rfl⟩
    exact ((Complex.isPrimitiveRoot_exp _ (qPow_ne_zero Q _)).isIntegral
      (Nat.pos_of_ne_zero (qPow_ne_zero Q _))).tower_top.isAlgebraic

open Classical in

def gens (P : Pre) (χ : HChar P.host.E) (Ξ : Set (HChar P.host.E)) : Finset ℂ :=
  if h : FinAlg (allSet P χ Ξ) then h.choose else ∅

theorem gens_algebraic (P : Pre) (χ : HChar P.host.E) (Ξ : Set (HChar P.host.E)) : ∀ z ∈ gens P χ Ξ, IsAlgebraic ℚ z := by
  unfold gens
  split_ifs with h
  · exact h.choose_spec.1
  · simp

theorem allSet_subset (P : Pre) (χ : HChar P.host.E) {Ξ : Set (HChar P.host.E)} (h : Ξ.Finite) {K : Subfield ℂ}
    (hK : ∀ z ∈ gens P χ Ξ, z ∈ K) : allSet P χ Ξ ⊆ K := by
  have h1 := finAlg_allSet P χ h
  rw [gens, dif_pos h1] at hK
  exact h1.choose_spec.2.trans (Subfield.closure_le.2 hK)

theorem exists_jetsIn (hL : StagesInhab.HasLetters B.toPre) {I : ColIn B X} (h : I.Ok)
    (hK : ∀ z ∈ gens B.toPre I.C.chiPsi (Set.range I.xi), z ∈ B.embLL.fieldRange) :
    ∃ I' : ColIn B X, I'.Ok ∧ I'.JetsIn ∧ I'.C = I.C ∧ I'.S = I.S ∧ Set.range I'.xi = Set.range I.xi := by
  have hall := allSet_subset B.toPre I.C.chiPsi (Set.finite_range I.xi) hK
  obtain ⟨I', h', e1, e2, e3, e4, e5⟩ := exists_replace h (amb0 B.host) (exists_ambIn_ok B.host).choose_spec fun a Q hQ => by
    obtain ⟨ζ, hζ⟩ := hall (Or.inr ⟨Q, rowSG_subset h a Q hQ, rfl⟩)
    refine ⟨ζ, IsPrimitiveRoot.of_map_of_injective (f := B.embLL) ?_ B.embLL.injective⟩
    rw [hζ]
    exact Complex.isPrimitiveRoot_exp _ (qPow_ne_zero Q _)
  refine ⟨I', h', I'.jetsIn_iff.2 fun a u i hi N N' c x hx e he => ?_, e1, e2, e3⟩
  rw [← e1, ← e3] at hall
  have hM : I'.modulus a u = (∏ Q ∈ rowSG (B.primes X) I'.sel (I'.tup a), qOf Q) ^ B.R.m *
      (B.T u * (∏ Q ∈ rowSG (B.primes X) I'.sel (I'.tup a), qOf Q) ^ B.R.m) := by
    unfold ColIn.modulus cAof cBof
    rw [(e5 a).1, (e5 a).2, Finset.prod_coe_sort _ qOf]
  have hS : stepSet B.toPre I'.C.chiPsi (u, i, I'.Sb a u, rowSG (B.primes X) I'.sel (I'.tup a)) =
      jetSet I'.A (B.R.N i) (B.R.N (i + 1)) (I'.Sb a u) (I'.modulus a u) (totDeg B.toPre u i) := by
    rw [hM, ColIn.A, e4]
    exact (jetSet_amb B _ _ _ _ _ _ _).symm
  have hpos : 0 < I'.modulus a u := by
    rw [hM]
    have := Finset.prod_pos fun Q (_ : Q ∈ rowSG (B.primes X) I'.sel (I'.tup a)) =>
      Nat.pos_of_ne_zero (by simpa using qPow_ne_zero Q 1 : qOf Q ≠ 0)
    have := (B.T_prime u).pos
    positivity
  refine hall (Or.inl (Set.mem_iUnion₂.2 ⟨(u, i, I'.Sb a u, rowSG (B.primes X) I'.sel (I'.tup a)),
    ⟨⟨hi, Sb_subset h' a u, rowSG_subset h' a⟩, ?_⟩, ?_⟩))
  · rw [hS]
    exact finAlg_step hL h' a u _ _ _ _ hpos
  · rw [hS]
    exact ⟨N, N', c, x, e, hx, degree_eq_totDeg B u i e he, rfl⟩

end JetEx

end GlobalTheory.Mem.Col2

end
