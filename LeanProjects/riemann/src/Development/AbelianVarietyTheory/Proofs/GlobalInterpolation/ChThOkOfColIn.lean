import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.JetsAllOfColIn
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JetOpIdentityOfEntire
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NotDvdDifferent
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AbsNormEqOfSplit
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ThetaStepDistributionEquivariantRationalStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalisedFamilyLatticeHypAndSmoothStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteQuotOfReps

open NumberField IsDedekindDomain

noncomputable section

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.KerT
open GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree (degAt degNu)

namespace GlobalTheory.ChainTheta

section Step

variable {X : Fields} (A : Amb X) {a b : ℕ} (Sa SB : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (mI : SB → X.E → X.K)
  (lam : X.Tau → DomWeight a) (lam' : X.Tau → DomWeight b) (n : X.Tau → ℕ)

theorem thDistC_add_deg (hadd : A.IndAdd a b Sa D) (hsm : A.IndSmooth a b Sa D)
    (hrat : ∀ N N' c x, InRange Sa D c N N' x → ∀ m : DVar X.Tau a b →₀ ℕ, (∀ τ, (degAt m τ : ℤ) = degNu lam n τ) →
      ∃ k : X.K, A.σ₀ k = (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd Sa N N' c x) m)
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (fr : Frs X.E a SB) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (fr' : Frs X.E b SB)
    (c c' : ℕ) (x : HomE X.E a b) (hc : 0 < c) (hc' : 0 < c') (hR : InRange Sa D (c * c') N N' x) :
    thDistC A Sa SB D sel mU mI lam lam' n N fr N' fr' c x =
      latSum (mulLat c (homAt Sa N N')) (mulLat (c * c') (homAt Sa N N')) fun y =>
        thDistC A Sa SB D sel mU mI lam lam' n N fr N' fr' (c * c') (x + y) := by
  have := latFin X a b Sa N N' c c' hR.1 hR.2.1 hc hc'
  let _ := Fintype.ofFinite
    (↥(mulLat c (homAt Sa N N')) ⧸ (mulLat (c * c') (homAt Sa N N')).comap (mulLat c (homAt Sa N N')).subtype)
  set rep := fun z : ↥(mulLat c (homAt Sa N N')) ⧸ (mulLat (c * c') (homAt Sa N N')).comap (mulLat c (homAt Sa N N')).subtype =>
    ((Function.surjInv (Submodule.Quotient.mk_surjective
      ((mulLat (c * c') (homAt Sa N N')).comap (mulLat c (homAt Sa N N')).subtype)) z :
      ↥(mulLat c (homAt Sa N N'))) : HomE X.E a b) with hrep
  have hRz : ∀ z, InRange Sa D (c * c') N N' (x + rep z) := fun z => hR.add (Subtype.coe_prop _)
  have h1 : A.thInd Sa N N' c x = fun w => ∑ z, A.thInd Sa N N' (c * c') (x + rep z) w := by
    funext w
    rw [hadd N N' c c' x hc hc' hR w]
    unfold latSum
    rw [finsum_eq_sum_of_fintype]
  have hJ : jetOp lam lam' (A.jetK Sa N N' c x) n =
      jetOp lam lam' (fun m => ∑ z, A.jetK Sa N N' (c * c') (x + rep z) m) n := by
    refine GlobalTheory.JetIdentity.jetOp_congr lam lam' n _ _ fun m hm => ?_
    have h2 : derivAt0 (A.thInd Sa N N' c x) m = ∑ z, derivAt0 (A.thInd Sa N N' (c * c') (x + rep z)) m := by
      unfold derivAt0
      rw [h1, iteratedFDeriv_sum (fun z _ => hsm N N' (c * c') (x + rep z) (hRz z) _)]
      rw [Finset.sum_apply, _root_.sum_apply]
    choose k hk using fun z => hrat N N' (c * c') (x + rep z) (hRz z) m hm
    have h3 : (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd Sa N N' c x) m = A.σ₀ (∑ z, k z) := by
      rw [map_sum]
      simp only [hk]
      unfold jetC
      rw [h2, Finset.mul_sum, Finset.mul_sum]
    unfold Amb.jetK
    rw [h3, desc_map]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [← hk z, desc_map]
  unfold latSum
  rw [finsum_eq_sum_of_fintype]
  unfold thDistC
  rw [if_pos ⟨(Dvd.intro _ rfl).trans hR.2.2.2.1, hR.2.2.2.2⟩, hJ, Formalism.L2.Ker.jetOp_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  exact (if_pos ⟨hR.2.2.2.1, mem_divLat_add D c _ hR.2.2.2.2 (Subtype.coe_prop _)⟩).symm

end Step

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (A : Amb X) (u : Pr.Word)

theorem stepC_ok_deg (i : ℕ) (hi : i < R.m) (j : ℕ) (hT : 0 < Pr.T u) (hq : MuqTie Ch sel mu cst)
    (hL : A.LaHyp (R.N i) (R.N j) (Sall sel mu u)) (hE : A.ESmooth (R.N i) (R.N j))
    (hrat : ∀ N N' c x, InRange (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) c N N' x →
      ∀ m : DVar X.Tau (R.N i) (R.N j) →₀ ℕ, (∀ τ, (degAt m τ : ℤ) = degNu (W.lamTrue u i) (nuLast W u i) τ) →
      ∃ k : X.K, A.σ₀ k = (A.chiF _ _ N N')⁻¹ * jetC A.cD (A.thInd (Sall sel mu u) N N' c x) m)
    (hR : RatStep W Ch sel mu cst A u i j) :
    ThDist.Ok (stepC W Ch sel mu cst A u i (W.lamTrue u j)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
      ((rhoVr X.emb (W.lamTrue u i)).comp (ufGL X.E (R.N i))) ((rhoVr X.emb (W.lamTrue u j)).comp (ufGL X.E (R.N j)))
      (rhoS Ch sel mu i) (rhoT Ch sel mu i) := by
  have hD := modulus_pos sel mu cst u hT
  unfold RatStep at hR
  rw [← stepC_eq_stepT W Ch sel mu cst hq A u i hi] at hR
  exact
    { cong := fun N fr N' fr' c x x' _ _ h => thDistC_cong A _ _ sel _ _ _ _ _ _ N fr N' fr' c x x' h
      add := fun N fr N' fr' c c' x hN hN' hc hc' hd hx =>
        thDistC_add_deg A _ _ _ sel _ _ _ _ _
          (indAdd_of A _ _ _ _ hD (latFin X _ _ _) (indTieD_of_la A _ _ _ _ hD hL)) (indSmooth_of A _ _ _ _ hE) hrat
          N fr N' fr' c c' x hc hc' ⟨hN, hN', Nat.mul_pos hc hc', hd, hx⟩
      equiv := thDistC_equiv A _ _ sel _ _ _ _ _ _ hD _ _ hR
      det := fun N fr N' fr' c x κ κ' _ _ =>
        thDistC_det A _ _ sel _ _ _ _ _ _ _ _ (muDetLaw_chain Ch sel mu cst i _) (muDetLaw_chain Ch sel mu cst i _)
          (unitInv_rho Ch sel mu i) N fr N' fr' c x κ κ' }

end Chain

theorem chTh_ok_of_hyp {Z : Dat} {H : D7} {s : Seam H Z.X} {cc : Ideal (𝓞 H.host.K)} {δ : ℂ} (B : Base H cc δ) {χ : TaylorLogMetric.IdE H → ℂ}
    {cD : H.what₂.Tau → ℂ} {sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)} {S : Set ℕ}
    {mu : Tup Z.X.F Z.X.E Z.X.K S} {cst : LocCst Z.X (rowSG Z.Pr sel mu)} {u : Z.Pr.Word} {m2 : ℕ} (hm : Z.R.m = m2 + 2)
    (h : Hyp Z s cc δ χ cD sel S mu cst u) (hE : B.EqP χ) (hV : B.VecP χ) (hq : MuqTie Z.Ch sel mu cst)
    (hJ : ∀ i, i < Z.R.m → ∀ N N' c x, InRange (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) c N N' x →
      ∀ m : DVar Z.X.Tau (Z.R.N i) (Z.R.N (i + 1)) →₀ ℕ, (∀ τ, (degAt m τ : ℤ) = degNu (Z.W.lamTrue u i) (nuLast Z.W u i) τ) →
      ∃ k : Z.X.K, (ambOf s B χ cD).σ₀ k = ((ambOf s B χ cD).chiF _ _ N N')⁻¹ *
        jetC (ambOf s B χ cD).cD ((ambOf s B χ cD).thInd (Sall sel mu u) N N' c x) m) :
    ChTh.Ok (Ch := Z.Ch) cst (chTh Z.W Z.Ch sel mu cst (ambOf s B χ cD) u m2) := by
  have bad := GlobalTheory.ThetaMove.BadPrimes.bad_primes Z.X Z.Pr sel S mu u h.ok.fields h.ok.primes h.isSel h.T_mem h.g_mem
  have key : ∀ i j, i < Z.R.m → j = i + 1 →
      ThDist.Ok (stepC Z.W Z.Ch sel mu cst (ambOf s B χ cD) u i (Z.W.lamTrue u j)) (Sall sel mu u)
        (cAof sel mu cst * cBof sel mu cst u) ((rhoVr Z.X.emb (Z.W.lamTrue u i)).comp (ufGL Z.X.E (Z.R.N i)))
        ((rhoVr Z.X.emb (Z.W.lamTrue u j)).comp (ufGL Z.X.E (Z.R.N j))) (rhoS Z.Ch sel mu i) (rhoT Z.Ch sel mu i) := by
    rintro i _ hi rfl
    obtain ⟨hL, hS⟩ := GlobalTheory.T.normalisedFamily_latticeHyp_and_smooth H Z.X s cc δ B χ cD (Z.R.N i) (Z.R.N (i + 1)) h.ok.fields h.ana.1 h.ana.2.2.1 h.ana.2.2.2.1 hV
      (GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree.even_N _ _) (GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree.even_N _ _)
    exact stepC_ok_deg Z.W Z.Ch sel mu cst _ u i hi (i + 1) (h.ok.primes.T_prime u).pos hq
      ⟨hL.1, hL.2.1, fun P hP => (bad P hP).1,
        fun P hP => GlobalTheory.PeriodIdealUnit.locP_AA_eq_one Z.X H s cc δ B χ cD P (bad P hP).2.1 (bad P hP).2.2.1 (h.cop P hP),
        hL.2.2.2.2⟩ hS (hJ i hi)
      (GlobalTheory.T.thetaStepDistribution_equivariant_rational Z H s cc δ B χ cD sel S mu cst u i hi h hE hV hq (hJ i hi))
  exact ⟨fun i hi => key i (i + 1) (by omega) rfl, key (m2 + 1) Z.R.m (by omega) hm⟩

open GlobalTheory.Mem GlobalTheory.Mem.Col2 in

theorem chTh_ok_of_colIn (B : GlobalTheory.Mem.Base) (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (N : NStage B C W)
    (G : GJStage B C) {X : PreX B.toPre} (I : ColIn B X) (h : I.Ok) (hJ : I.JetsIn)
    (hE : (I.J.toRec B C W V S N G).EqP I.chi) (hV : (I.J.toRec B C W V S N G).VecP I.chi)
    (a : I.ι) (u : B.Word) (m2 : ℕ) (hm : B.R.m = m2 + 2) :
    ChTh.Ok (Ch := I.Ch) (I.cst a) (chTh (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) I.A u m2) := by
  have h1 := chTh_ok_of_hyp (Z := I.dat) (I.J.toRec B C W V S N G) hm (hyp_of_colIn B C W V S N G I h a u) hE hV
    (muqTie_of_ok _ _ _ _ _ (h.idx_ok a)) (by
      rw [← AmbIn.amb_eq_ambOf]
      intro i hi L L' c x hx m hd
      refine hJ.exists_eq hi hx fun τ => ?_
      rw [monoDeg_eq_sum]
      exact (hd τ).trans (GlobalTheory.MoveCompare.degNu_eq (Pr := B.primes X) B.wts u hi τ))
  rw [← AmbIn.amb_eq_ambOf] at h1
  exact h1

open GlobalTheory.Mem GlobalTheory.Mem.Col2 in

theorem chTh_ok_of_colIn' (B : GlobalTheory.Mem.Base) (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (N : NStage B C W)
    (G : GJStage B C) {X : PreX B.toPre} (I : ColIn B X) (h : I.Ok) (hJ : I.JetsIn)
    (hE : (I.J.toRec B C W V S N G).EqP I.chi) (hV : (I.J.toRec B C W V S N G).VecP I.chi) (a : I.ι) (u : B.Word) :
    ChTh.Ok (Ch := I.Ch) (I.cst a) (chTh (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) I.A u (B.R.m - 2)) :=
  chTh_ok_of_colIn B C W V S N G I h hJ hE hV a u _ h.hm

end GlobalTheory.ChainTheta
