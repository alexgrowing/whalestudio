import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.BelowFiniteNonempty
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPreHasLetters
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameHeckeCharLocalEqInvTypeCharacter
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntMulMemInvHalfDifferent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrdSubConjEqNeg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValPowClassNumber
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormOneDetIdealTransportedLattice

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker

namespace GlobalTheory.KerT

theorem exists_cst_one {Z : Dat} (hZ : Z.Ok) {sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)} (hsel : IsSel Z.X sel)
    (S : Set ℕ) {m0 : Fin Z.R.m → Formalism.L2.Host.HChar Z.X.E} {eta : Formalism.L2.Host.HChar Z.X.E}
    (ht : Z.Ch.Tied Z.sig0 (fun j τ => (Z.W.row τ).e j) m0 eta) (hsq : ∀ k, ∃ r : Z.X.K, r ^ 2 = (Z.Pr.g k : Z.X.K))
    (hω : ∀ k, ∃ ω : Z.X.K, Z.sig0 ω = Complex.exp (2 * Real.pi * Complex.I / (Z.Pr.g k : ℂ))) :
    ∃ cst : LocCst Z.X (rowSG Z.Pr sel (1 : Tup Z.X.F Z.X.E Z.X.K S)),
      cst.Ok ∧ MuqTieG (Pr := Z.Pr) (R := Z.R) sel 1 cst Z.sig0 m0 := by
  classical
  obtain ⟨c₀, hc₀⟩ := GlobalTheory.CharValCompare.exists_cst hZ ht sel (1 : Tup Z.X.F Z.X.E Z.X.K S)
  have hq : ∀ P : rowSG Z.Pr sel (1 : Tup Z.X.F Z.X.E Z.X.K S), ∃ k, qOf P.1 = Z.Pr.g k := by
    intro P
    rcases Finset.mem_union.1 P.2 with h | h
    · obtain ⟨k, hk⟩ := (GlobalTheory.Mem.DatHecke.mem_vGs P.1).1 h
      exact ⟨k, hZ.primes.vG_norm k P.1 hk⟩
    · have h0 : Qprime ((1 : Tup Z.X.F Z.X.E Z.X.K S) : Chr Z.X.F Z.X.E Z.X.K) = ∅ := by
        ext v
        simp [Qprime]
      unfold QE at h
      simp only [h0] at h
      simp at h
  choose k hk using hq
  choose r hr using hsq
  choose ω hω using hω
  have h1 : ∀ P : HeightOneSpectrum (𝓞 Z.X.E), IntAt P (1 : Z.X.E) ∧ redP P (1 : Z.X.E) ≠ 0 := fun P => by
    have := P.isPrime
    refine ⟨by simpa using IntAt.coe P 1, ?_⟩
    have h := reduction_coe P 1
    rw [map_one, map_one] at h
    rw [h]
    exact one_ne_zero
  choose ψ hadd hint hne _ using fun P : rowSG Z.Pr sel (1 : Tup Z.X.F Z.X.E Z.X.K S) =>
    GlobalTheory.Mem.Col2.exists_psi Z.sig0 (GlobalTheory.Mem.Col2.degOneUnram_rowSG hZ.fields hZ.primes hsel 1 P) (le_refl 1) (h1 P.1).1 (h1 P.1).2
      (ω := ω (k P)) (by rw [hω, pow_one, hk])
  exact ⟨⟨ψ, fun _ => 1, fun P => r (k P), c₀.muq, 1, 1, 1, true⟩,
    ⟨hadd, hint, hne, fun _ => le_rfl, fun P => by rw [hk]; exact hr _, le_rfl, le_rfl, le_rfl, le_rfl⟩, hc₀⟩

open GlobalTheory.Mem GlobalTheory.Mem.Col2 in

theorem exists_hyp : ∃ (Z : Dat) (H : D7) (s : Seam H Z.X) (δ : ℂ) (χ : TaylorLogMetric.IdE H → ℂ) (cD : H.what₂.Tau → ℂ)
    (sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)) (S : Set ℕ)
    (cst : LocCst Z.X (rowSG Z.Pr sel (1 : Tup Z.X.F Z.X.E Z.X.K S))),
    2 ≤ Fintype.card Z.Pr.Word ∧ Nonempty (Formalism.L2.Ker.Base H ⊤ δ) ∧ ∀ u, Hyp Z s ⊤ δ χ cD sel S 1 cst u := by
  classical
  obtain ⟨P, hP, ⟨X⟩, h2⟩ := StagesInhab.exists_pre_hasLetters
  choose r hr using fun k : Fin 2 => IsAlgClosed.exists_pow_nat_eq (P.host.g k : ℂ) (n := 2) (by norm_num)
  let e : Fin 2 → ℂ := fun k => Complex.exp (2 * Real.pi * Complex.I / (P.host.g k : ℂ))
  have hg : ∀ k, P.host.g k ≠ 0 := fun k => (P.host.g_prime k).ne_zero
  obtain ⟨B, rfl, Ch, hZ, -, -, hS⟩ := DatHecke.exists_base_dat_ok P X ∅ ∅ (Finset.univ.image r ∪ Finset.univ.image e)
    (by simp) (by simp) (fun z hz => by
      rcases Finset.mem_union.1 hz with h | h <;> obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 h
      · exact IsAlgebraic.of_pow two_pos (by rw [hr]; exact isAlgebraic_nat _)
      · exact IsAlgebraic.of_pow (Nat.pos_of_ne_zero (hg k))
          (by rw [(Complex.isPrimitiveRoot_exp _ (hg k)).pow_eq_one]; exact isAlgebraic_one))
  obtain ⟨⟨B', C, W, V, S, N, G⟩, rfl, -⟩ := StagesInhab.exists_stages_over B hP 1
  obtain ⟨J, hJ⟩ := exists_ambIn_ok B'.host
  obtain ⟨m0, eta, ht⟩ := hZ.hecke
  obtain ⟨sel, hsel⟩ := GlobalTheory.CharValCompare.exists_isSel B'.fields
  have heta : Formalism.L2.Host.IsEtaT B'.host eta :=
    ⟨ht.etaT.unitary, ht.etaT.unr, ht.etaT.res, by
      have h := ht.etaT.inf
      rwa [show B'.fields.embC B'.embLL = Formalism.L2.Host.embPsi B'.host from funext B'.fields_embC] at h⟩
  obtain ⟨cst, hc, htie⟩ := exists_cst_one hZ hsel Set.univ ht
    (fun k => by
      obtain ⟨x, hx⟩ := hS (r k) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
      exact ⟨x, B'.embLL.injective (by rw [map_pow, hx, hr, map_natCast])⟩)
    (fun k => hS (e k) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))))
  have hJ' := (J.ok_iff B' C W V S N G).1 hJ
  refine ⟨B'.dat X Ch, assemble B' C W V S N G, seamOf B' C W V S N G, J.δ, chiId (eta * eta), J.cD, sel, Set.univ, cst, h2,
    ⟨J.toRec B' C W V S N G⟩, fun u => ⟨hZ, ⟨seamOf_ok B' C W V S N G, rfl, ⟨top_ne_bot, by simp⟩, hJ'.1,
      ChiIdeal.isChi_chiId _ _ heta.sq_chiPsi, hJ'.2⟩, fun 𝔞 _ => ?_, hsel, Set.subset_univ _, fun _ _ => Set.mem_univ _, fun _ _ => by simp, hc, m0, eta, ht, htie⟩⟩
  refine ChiVal.chiId_mem (eta * eta) B'.embLL.fieldRange (fun w => ?_) 𝔞
  rw [Formalism.L2.Host.HChar.val_mul, Units.val_mul, ChiVal.val_sq_eq]
  have h3 : eta.valTw (1 / 2) w ∈ B'.embLL.fieldRange := ⟨_, ht.etaVal w⟩
  exact mul_mem (pow_mem h3 2) (natCast_mem _ _)

open GlobalTheory.Mem GlobalTheory.Mem.Col2 in

theorem hyp_of_colIn (B : GlobalTheory.Mem.Base) (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (N : NStage B C W)
    (G : GJStage B C) {X : PreX B.toPre} (I : ColIn B X) (h : I.Ok) (a : I.ι) (u : B.Word) :
    Hyp I.dat (seamOf B C W V S N G) ⊤ I.J.δ I.chi I.J.cD I.sel I.S (I.tup a) (I.cst a) u := by
  have hJ := (I.J.ok_iff B C W V S N G).1 h.amb_ok
  refine ⟨GlobalTheory.T.definiteBaseData_admissible B X I.Ch h.ch_ok h.fromHecke, ⟨seamOf_ok B C W V S N G, rfl, ⟨top_ne_bot, by simp⟩, hJ.1,
    ChiIdeal.isChi_chiId _ _ I.C.isChi, hJ.2⟩, fun 𝔞 _ => (ChiVal.chi_values B X I h).2 𝔞, h.sel_ok, ?_, fun _ hl => h.small_mem hl, fun _ _ => by simp,
    (h.idx_ok a).cst_ok, I.C.mu0, I.C.eta, h.ch_tied, (h.idx_ok a).muqG⟩
  rintro p ((rfl | rfl | rfl | rfl | rfl) | ⟨u, rfl⟩)
  exacts [h.two_q_d_mem.1, h.two_q_d_mem.2.1, h.two_q_d_mem.2.2, h.g_mem 0, h.g_mem 1, h.T_mem u]

open GlobalTheory.Mem GlobalTheory.Mem.Col2 in

theorem jetsAll_of_colIn (B : GlobalTheory.Mem.Base) (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (N : NStage B C W)
    (G : GJStage B C) {X : PreX B.toPre} (I : ColIn B X) (h : I.Ok) (hJ : I.JetsIn) (a : I.ι) (u : B.Word) {i : ℕ} (hi : i < B.R.m) :
    JetsAll (Pr := B.primes X) B.wts I.sel (I.tup a) (I.cst a)
      (ambOf (seamOf B C W V S N G) (I.J.toRec B C W V S N G) I.chi I.J.cD) u i (i + 1) := by
  have hP := (hyp_of_colIn B C W V S N G I h a u).ok.primes
  rw [← AmbIn.amb_eq_ambOf]
  intro L L' hL hL'
  exact (GlobalTheory.MoveCompare.jetsIn_iff _ _ _ _ _ _ _ (GlobalTheory.MoveCompare.degNu_eq (Pr := B.primes X) B.wts u hi) L L').2
    (GlobalTheory.MoveCompare.jetsAll_of_deg _ _ _ _ _ (hJ a u i hi) (GlobalTheory.MoveCompare.cBof_pos hP _ _ _ u) hL hL')

end GlobalTheory.KerT
