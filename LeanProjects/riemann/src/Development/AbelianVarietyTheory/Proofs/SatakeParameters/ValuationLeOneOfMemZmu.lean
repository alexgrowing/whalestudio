import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeFactsAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDivLatticeQuotient
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChainWideTwistTransport

noncomputable section

namespace GlobalTheory.ColPeriod

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke.FourierColumnIndicator (FnModAt FnMod facTop facPen Zmu)
open GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance (DegOneUnram)
open GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation (StdOver IsFrames)
open GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable (jetSum RatIdx)
open GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint (WtCompat InDeg HAt LatWithBasis)

section Frames

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {a b : ℕ} {P : HeightOneSpectrum (𝓞 E)}
  {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)} {f : Sp E a ≃ₗ[E] Sp E a} {f' : Sp E b ≃ₗ[E] Sp E b}

theorem inFr_mem_iff (hf : ∀ x, f x ∈ localization₂ P.asIdeal N ↔ x ∈ stdAt E a P) (hf' : ∀ x, f' x ∈ localization₂ P.asIdeal N' ↔ x ∈ stdAt E b P)
    (x : HomE E a b) : inFr f f' x ∈ homAt {P} (stdLat E a) (stdLat E b) ↔ x ∈ homAt {P} N N' := by
  constructor
  · intro h Q hQ y hy
    rw [Finset.mem_singleton] at hQ
    subst hQ
    have h1 : f.symm y ∈ stdAt E a Q := (hf _).1 (by simpa using hy)
    have h2 := (hf' _).2 (h Q (Finset.mem_singleton_self _) _ h1)
    simpa [inFr] using h2
  · intro h Q hQ y hy
    rw [Finset.mem_singleton] at hQ
    subst hQ
    refine (hf' _).1 ?_
    simpa [inFr] using h Q (Finset.mem_singleton_self _) _ ((hf _).2 hy)

omit [NumberField E] [StarRing E] in
theorem inFr_add_smul (x z : HomE E a b) (c : E) : inFr f f' (x + c • z) = inFr f f' x + c • inFr f f' z := by
  ext y
  simp [inFr]

theorem fnModAt_inFr (hf : ∀ x, f x ∈ localization₂ P.asIdeal N ↔ x ∈ stdAt E a P)
    (hf' : ∀ x, f' x ∈ localization₂ P.asIdeal N' ↔ x ∈ stdAt E b P) {Φ : HomE E a b → K} (h : FnMod P Φ) :
    FnModAt P N N' fun x => Φ (inFr f f' x) :=
  ⟨fun x hx => (inFr_mem_iff hf hf' x).1 (h.1 _ hx),
    fun x z hz => by
      dsimp only
      rw [inFr_add_smul, h.2.1 _ _ ((inFr_mem_iff hf hf' z).2 hz)],
    fun _ => h.2.2 _⟩

theorem awayAt_inFr [NumberField K] (hf : ∀ x, f x ∈ localization₂ P.asIdeal N ↔ x ∈ stdAt E a P)
    (hf' : ∀ x, f' x ∈ localization₂ P.asIdeal N' ↔ x ∈ stdAt E b P) {w : HeightOneSpectrum (𝓞 K)} {B : ℕ} {Φ : HomE E a b → K}
    (h : AwayAt P w B (stdLat E a) (stdLat E b) Φ) : AwayAt P w B N N' fun x => Φ (inFr f f' x) :=
  ⟨fun _ => h.1 _, fun x z hz => by
    dsimp only
    rw [inFr_add_smul, h.2 _ _ ((inFr_mem_iff hf hf' z).2 hz)]⟩

theorem valuation_le_one_of_mem_Zmu [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {g : ℕ} (hg : g.Prime) {x : K}
    (hx : x ∈ Zmu K g) : w.valuation K x ≤ 1 := by
  have h1 : IsIntegral ℤ x := by
    refine (Algebra.adjoin_le (S := integralClosure ℤ K) fun ζ hζ => ?_) hx
    have h2 : 0 < g * (g - 1) := Nat.mul_pos hg.pos (by have := hg.two_le; omega)
    exact IsIntegral.of_pow h2 (by rw [show ζ ^ (g * (g - 1)) = 1 from hζ]; exact isIntegral_one)
  exact w.valuation_le_one (K := K) ⟨x, h1⟩

omit [StarRing E] in
theorem exists_of_mem_mulLat {S : Finset (HeightOneSpectrum (𝓞 E))} {c q : ℕ} (hq : q ∣ c) {z : HomE E a b}
    (hz : z ∈ mulLat c (homAt S N N')) (hP : P ∈ S) : ∃ z' ∈ homAt {P} N N', z = (q : E) • z' := by
  obtain ⟨k, rfl⟩ := hq
  obtain ⟨y, hy, rfl⟩ := hz
  refine ⟨k • y, nsmul_mem (fun Q hQ => ?_) k, ?_⟩
  · rw [Finset.mem_singleton] at hQ
    subst hQ
    exact hy Q hP
  · rw [LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, mul_smul]

theorem phiT_add {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))} (d : Deco E a ST SG) {d' : Deco E b ST SG'} (hd' : d'.Ok)
    {T : ℕ} (hT : ∀ Q : ST, (T : 𝓞 E) ∈ Q.1.asIdeal) (x : HomE E a b) {z : HomE E a b}
    (hz : ∀ Q : ST, ∃ z' ∈ homAt {Q.1} d.N d'.N, z = (T : E) • z') : phiT K d d' (x + z) = phiT K d d' x := by
  have key : ∀ (x z : HomE E a b), (∀ Q : ST, ∃ z' ∈ homAt {Q.1} d.N d'.N, z = (T : E) • z') →
      (∀ Q : ST, ∀ y ∈ d.at Q.1, x y ∈ d'.at Q.1 ∧ d'.f Q (x y) = d.f Q y) →
      ∀ Q : ST, ∀ y ∈ d.at Q.1, (x + z) y ∈ d'.at Q.1 ∧ d'.f Q ((x + z) y) = d.f Q y := by
    intro x z hz h Q y hy
    obtain ⟨z', hz', rfl⟩ := hz Q
    have h1 : z' y ∈ d'.at Q.1 := hz' Q.1 (Finset.mem_singleton_self _) y hy
    have e : (x + (T : E) • z') y = x y + (T : 𝓞 E) • z' y := by
      rw [LinearMap.add_apply, LinearMap.smul_apply, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    rw [e]
    refine ⟨add_mem (h Q y hy).1 (Submodule.smul_mem _ _ h1), ?_⟩
    rw [hd'.f_add Q _ (h Q y hy).1 _ (Submodule.smul_mem _ _ h1), hd'.f_smul Q _ _ h1,
      Ideal.Quotient.eq_zero_iff_mem.2 (hT Q), zero_mul, add_zero, (h Q y hy).2]
  classical
  unfold phiT
  refine if_congr ⟨fun h => ?_, key x z hz⟩ rfl rfl
  have := key (x + z) (-z) (fun Q => by
    obtain ⟨z', hz', rfl⟩ := hz Q
    exact ⟨-z', neg_mem hz', (smul_neg _ _).symm⟩) h
  rwa [add_neg_cancel_right] at this

end Frames

section Datum

variable {X : Fields} {Pr : Primes X} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)}

theorem g_mem_of_mem_vG (hPr : Pr.Ok) {i : Fin 2} {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ Pr.vG i) :
    ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal := by
  rw [← hPr.piG_norm i]
  exact P.asIdeal.mul_mem_left _ (mem_divs h)

theorem vG_subset (i : Fin 2) : Pr.vG i ⊆ Pr.vGs := by
  classical
  fin_cases i
  exacts [Finset.subset_union_left, Finset.subset_union_right]

theorem exists_mem_vG {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ Pr.vGs) : ∃ i, P ∈ Pr.vG i := by
  classical
  rcases Finset.mem_union.1 h with h2 | h2
  exacts [⟨0, h2⟩, ⟨1, h2⟩]

theorem datumAt_prod (hPr : Pr.Ok) (hc : cst.Ok) (u : Pr.Word) (i : Fin 2) (w : HeightOneSpectrum (𝓞 X.K)) {a b : ℕ}
    {SG SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (d : Deco X.E a (Pr.vT u) SG) {d' : Deco X.E b (Pr.vT u) SG'} (hd' : d'.Ok)
    (Φ : rowSG Pr sel mu → HomE X.E a b → X.K) (hg : ∀ P, P.1 ∈ Pr.vGs → FnModAt P.1 d.N d'.N (Φ P))
    (hq : ∀ P, P.1 ∉ Pr.vGs → AwayAt P.1 w cst.B d.N d'.N (Φ P)) :
    DatumAt (Pr.vG i) (Sall sel mu u) (Pr.g i) (cBof sel mu cst u) w d.N d'.N
      fun x => phiT X.K d d' x * ∏ P, Φ P x := by
  classical
  refine ⟨fun x => ?_, fun x hx P hP => ?_, fun x z hz hz' => ?_⟩
  · rw [map_mul, map_prod]
    refine mul_le_one' ?_ (Finset.prod_le_one' fun P _ => ?_)
    · unfold phiT
      split_ifs <;> simp
    · by_cases h : P.1 ∈ Pr.vGs
      · obtain ⟨k, hk⟩ := exists_mem_vG h
        refine valuation_le_one_of_mem_Zmu w (g := qOf P.1) ?_ ((hg P h).2.2 x)
        rw [qOf, hPr.vG_norm k _ hk]
        exact hPr.g_prime k
      · exact (hq P h).1 x
  · have h1 : P ∈ rowSG Pr sel mu := Finset.mem_union_left _ (vG_subset i hP)
    exact (hg ⟨P, h1⟩ (vG_subset i hP)).1 x
      (Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hx) ⟨P, h1⟩ (Finset.mem_univ _)) P (Finset.mem_singleton_self _)
  · dsimp only
    have hdv : ∀ P : rowSG Pr sel mu, qOf P.1 ^ cst.B ∣ cBof sel mu cst u := fun P =>
      Dvd.dvd.mul_left (pow_dvd_pow_of_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ P)) _) _
    congr 1
    · refine phiT_add d hd' (T := Pr.T u) (fun Q => T_mem_of_piT_mem hPr u (mem_divs Q.2)) x fun Q => ?_
      refine exists_of_mem_mulLat (Dvd.intro _ rfl) hz' ?_
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_union_left _ Q.2, fun h => ?_⟩
      exact natCast_notMem_of_ne (hPr.T_prime u) (hPr.g_prime i) (hPr.T_ne_g u i) _ (g_mem_of_mem_vG hPr h)
        (T_mem_of_piT_mem hPr u (mem_divs Q.2))
    · refine Finset.prod_congr rfl fun P _ => ?_
      by_cases h0 : P.1 ∈ Pr.vG i
      · obtain ⟨z', h1, rfl⟩ := exists_of_mem_mulLat (q := qOf P.1) (by rw [qOf, hPr.vG_norm i _ h0]) hz h0
        exact (hg P (vG_subset i h0)).2.1 x z' h1
      · have h2 : P.1 ∈ Sall sel mu u \ Pr.vG i := by
          rw [Finset.mem_sdiff]
          exact ⟨Finset.mem_union_right _ P.2, h0⟩
        by_cases h : P.1 ∈ Pr.vGs
        · obtain ⟨z', h1, rfl⟩ := exists_of_mem_mulLat (q := qOf P.1)
            ((dvd_pow_self _ (by have := hc.B_pos; omega)).trans (hdv P)) hz' (by convert h2)
          exact (hg P h).2.1 x z' h1
        · obtain ⟨z', h1, rfl⟩ := exists_of_mem_mulLat (hdv P) hz' (by convert h2)
          rw [Nat.cast_pow]
          exact (hq P h).2 x z' h1

theorem isFrames_frsF {R : Ranks} {u : Pr.Word} {j : ℕ} (p : ChPt (R := R) sel mu u j) : IsFrames p.deco.1.N (frsF sel mu p) := by
  classical
  intro P x
  unfold frsF
  split_ifs with h
  · exact (GlobalTheory.TopStep.liftFr_spec p.deco.2 ⟨P.1, h⟩).1 x
  · exact p.2 ⟨P.1, (Finset.mem_union.mp P.2).resolve_left h⟩ x

theorem isFrames_frsT {R : Ranks} {u : Pr.Word} (d : RowPt Pr R sel mu) : IsFrames (tilQ sel mu u d).1.N (frsT sel mu u d) :=
  fun P x => (GlobalTheory.TopStep.liftFr_spec (tilQ sel mu u d).2 P).1 x

end Datum

section Jets

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {a b : ℕ}

theorem jetOp_sum (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (n : ι → ℕ) {I : Type} [Fintype I] (c : I → K)
    (J : I → (DVar ι a b →₀ ℕ) → K) :
    jetOp lam lam' (fun m => ∑ i, c i * J i m) n = ∑ i, c i • jetOp lam lam' (J i) n := by
  have h : jetLin (fun m => ∑ i, c i * J i m) = ∑ i, c i • jetLin (J i) := by
    refine (MvPolynomial.basisMonomials _ K).ext fun m => ?_
    simp only [jetLin, Module.Basis.constr_basis, LinearMap.sum_apply, LinearMap.smul_apply, map_sum,
      MvPolynomial.smul_monomial, smul_eq_mul]
  ext1 F
  simp only [jetOp, jetMap, h, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]

variable {X : Fields} (A : Amb X)

theorem kerOf_thDistC (Sa SB : Finset (HeightOneSpectrum (𝓞 X.E))) {cA cB : ℕ} (hA : 0 < cA) (hB : 0 < cB)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ)
    (mI : SB → X.E → X.K) (lam : X.Tau → DomWeight a) (lam' : X.Tau → DomWeight b) (n : X.Tau → ℕ)
    {N : Submodule (𝓞 X.E) (Sp X.E a)} {N' : Submodule (𝓞 X.E) (Sp X.E b)} (hN : Submodule.IsLattice X.E N)
    (hN' : Submodule.IsLattice X.E N') (fr : Frs X.E a SB) (fr' : Frs X.E b SB) (Ξ : HomE X.E a b → X.K) :
    kerOf (thDistC A Sa SB (cA * cB) sel mU mI lam lam' n) Sa cA cB N fr N' fr' Ξ =
      (muInvDet sel SB mU mI N fr * (muInvDet sel SB mU mI N' fr')⁻¹) • jetOp lam lam' (jetSum A Sa cA cB N N' Ξ) n := by
  have hfin := GlobalTheory.finite_divLat_quot_mulLat_homAt X.E a b Sa N N' cA cB hN hN' hA hB
  let _ := Fintype.ofFinite (↥(divLat cA (homAt Sa N N')) ⧸ (mulLat cB (homAt Sa N N')).comap (divLat cA (homAt Sa N N')).subtype)
  unfold kerOf jetSum latSum
  simp only [finsum_eq_sum_of_fintype]
  rw [jetOp_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [smul_comm]
  congr 1
  unfold thDistC
  rw [if_pos]
  refine ⟨Dvd.intro_left _ rfl, ?_⟩
  have h := (Function.surjInv (Submodule.Quotient.mk_surjective
    ((mulLat cB (homAt Sa N N')).comap (divLat cA (homAt Sa N N')).subtype)) z).2
  change ((cA * cB : ℕ) : 𝓞 X.E) • _ ∈ homAt Sa N N'
  rw [Nat.cast_mul, mul_comm, mul_smul]
  exact Submodule.smul_mem _ _ h

end Jets

section Point

theorem latWithBasis_of_stdOver {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] {ι : Type} [Fintype ι]
    (emb : ι → E →+* K) {n p : ℕ} (hp : p ≠ 0) {N : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsLattice E N) (hs : StdOver p N)
    (w : HeightOneSpectrum (𝓞 K)) (hw : (p : 𝓞 K) ∈ w.asIdeal) : LatWithBasis w (fun τ => tauLat emb τ N) 1 := by
  intro τ
  let _ : StarRing K := starRingOfComm
  refine ⟨(GlobalTheory.TauLat.tauLatLattice E K ι n emb τ N hN).fg, ?_⟩
  let φ : 𝓞 E →+* 𝓞 K := RingOfIntegers.mapRingHom (emb τ)
  have hpm : (p : 𝓞 E) ∈ w.asIdeal.comap φ := by
    rw [Ideal.mem_comap, map_natCast]
    exact hw
  let P : HeightOneSpectrum (𝓞 E) := ⟨w.asIdeal.comap φ, Ideal.comap_isPrime _ _, fun h => by
    rw [h, Ideal.mem_bot] at hpm
    exact hp (by exact_mod_cast hpm)⟩
  have key : ∀ L L' : Submodule (𝓞 E) (Sp E n), localization₂ P.asIdeal L ≤ localization₂ P.asIdeal L' →
      localization₂ w.asIdeal (tauLat emb τ L) ≤ localization₂ w.asIdeal (tauLat emb τ L') := by
    intro L L' h
    have h1 : tauLat emb τ L ≤ localization₂ w.asIdeal (tauLat emb τ L') := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨s, hs, hsx⟩ := (Formalism.L2.Col.mem_locP P _ _).1 (h (Formalism.L2.Col.le_locP P _ hx))
      refine (Formalism.L2.Col.mem_locP w _ _).2 ⟨φ s, hs, Submodule.subset_span ⟨s • x, hsx, ?_⟩⟩
      funext a
      simp only [Pi.smul_apply, Algebra.smul_def, map_mul]
      rfl
    intro x hx
    obtain ⟨s, hs, hsx⟩ := (Formalism.L2.Col.mem_locP w _ _).1 hx
    obtain ⟨t, ht, htx⟩ := (Formalism.L2.Col.mem_locP w _ _).1 (h1 hsx)
    exact (Formalism.L2.Col.mem_locP w _ _).2 ⟨t * s, fun hm => (w.isPrime.mem_or_mem hm).elim ht hs, by rwa [mul_smul]⟩
  have e : tauLat emb τ (stdLat E n) = colLat (1 : GL (Fin n) K) := by
    apply le_antisymm
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨x, hx, rfl⟩
      choose r hr using (mem_stdLat x).1 hx
      have : (fun a => emb τ (x a)) = ∑ j, φ (r j) • fun a => ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a j := by
        funext a
        simp only [Finset.sum_apply, Pi.smul_apply, Units.val_one, Matrix.one_apply, Algebra.smul_def, mul_ite, mul_zero, mul_one,
          Finset.sum_ite_eq, Finset.mem_univ, if_true, ← hr]
        rfl
      change (fun a => emb τ (x a)) ∈ _
      rw [this]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨j, rfl⟩
      refine Submodule.subset_span ⟨Pi.single j 1, by simpa using single_mem_stdLat (E := E) j 1, ?_⟩
      funext a
      simp only [Units.val_one, Matrix.one_apply, Pi.single_apply]
      split_ifs <;> simp
  change localization₂ w.asIdeal (tauLat emb τ N) = localization₂ w.asIdeal (colLat (1 : GL (Fin n) K))
  rw [← e]
  exact le_antisymm (key _ _ (hs P hpm).le) (key _ _ (hs P hpm).ge)

theorem smul_mem_localizationAt_of_le {K : Type} [Field K] [NumberField K] {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z]
    [IsScalarTower (𝓞 K) K Z] (w : HeightOneSpectrum (𝓞 K)) (M : Submodule (𝓞 K) Z) {a : K} (ha : w.valuation K a ≤ 1) {y : Z}
    (hy : y ∈ localization₂ w.asIdeal M) : a • y ∈ localization₂ w.asIdeal M := by
  obtain ⟨r, t, h⟩ := w.exists_primeCompl_mul_eq_of_integer a ha
  refine GlobalTheory.TestLat.WeylLocal.smul_mem_locP w M ((GlobalTheory.TestLat.WeylLocal.mem_locRing w a).2 ⟨r, t, t.2, ?_⟩) hy
  rw [← h, mul_inv_cancel_right₀ (GlobalTheory.TestLat.WeylLocal.ne_zero_of_mem w t.2)]

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)

def lossAt (i : Fin 2) (u : Pr.Word) (j : ℕ) : X.K :=
  (Pr.g i : X.K) ^ (X.f * R.N j * R.N (j + 1)) *
    ∏ τ, X.emb τ (star ((Pr.piG i : 𝓞 X.E) : X.E)) ^ (∑ a, (W.nuW u (j + 1) τ).w a).toNat

variable (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (A : Amb X)

theorem cAof_pos : 0 < cAof sel mu cst :=
  pow_pos (Finset.prod_pos fun P _ => Nat.pos_of_ne_zero (by
    rw [qOf, Ne, Ideal.absNorm_eq_zero_iff]; exact P.1.ne_bot)) _

theorem cBof_pos (hPr : Pr.Ok) (u : Pr.Word) : 0 < cBof sel mu cst u :=
  Nat.mul_pos (hPr.T_prime u).pos (pow_pos (Finset.prod_pos fun P _ => Nat.pos_of_ne_zero (by
    rw [qOf, Ne, Ideal.absNorm_eq_zero_iff]; exact P.1.ne_bot)) _)

end Point

end GlobalTheory.ColPeriod
