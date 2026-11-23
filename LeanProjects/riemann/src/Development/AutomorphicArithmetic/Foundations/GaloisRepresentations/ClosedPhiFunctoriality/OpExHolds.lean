import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IntBasisAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IsOp2One
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPreframeBoundedPolesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisTorsionFreeCompleteFrobeniusPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantUnitMatrixBcrisFrame
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

private theorem phi_zC (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (n : ℕ) (z : ℤ_[l]) :
    (phiA l ^ n) (zC l z) = zC l z := by
  have h1 : phiA l (zC l z) = zC l z := by
    have h := (GlobalTheory.T.acris_torsionFree_complete_frobenius_properties l K bk).2.2.2.1 (Per.zA l z)
    have h2 : WittVector.frobenius (Per.zA l z) = Per.zA l z := by
      rw [← GlobalTheory.RingBasics.φA_apply]; exact (ActLaws.act_laws l).2.2.2.2.2.2.2.2.1 z
    rw [h2] at h
    exact h
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    change (phiA l ^ n) (phiA l (zC l z)) = _
    rw [h1, ih]

private theorem map_link (hFix : FixW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (P : LocPrime l) (AI : LocAinf l P)
    (T : LocTied l P AI) (n : ℕ) (hn : FixUr K n) (d d' M : ℕ) (Pi : Matrix (Fin d) (Fin d') ℤ_[l])
    (R : Matrix (Fin d) (Fin d') bk.S) (Z : Matrix (Fin d) (Fin d) (Per.Acris l)) (Z₁ : Matrix (Fin d') (Fin d') (Per.Acris l))
    (h : ∀ i j, (l : Per.Acris l) ^ M ∣ (Pi.map (zC l) * Z₁ - Z * R.map (f0 bk)) i j) :
    ∀ i j, (l : Per.Acris l) ^ M ∣
      (Pi.map (zC l) * Z₁.map ⇑(phiA l ^ n) - Z.map ⇑(phiA l ^ n) * R.map (f0 bk)) i j := by
  intro i j
  have hP : (Pi.map (zC l)).map ⇑(phiA l ^ n) = Pi.map (zC l) := by
    ext a b; simp only [Matrix.map_apply]; exact phi_zC l K bk n _
  have hR : (R.map (f0 bk)).map ⇑(phiA l ^ n) = R.map (f0 bk) := by
    ext a b; simp only [Matrix.map_apply]; exact hFix l K bk P AI T n hn _
  have h1 := map_dvd (phiA l ^ n) (h i j)
  rw [map_pow, map_natCast] at h1
  have h2 : (phiA l ^ n) ((Pi.map (zC l) * Z₁ - Z * R.map (f0 bk)) i j) =
      (Pi.map (zC l) * Z₁.map ⇑(phiA l ^ n) - Z.map ⇑(phiA l ^ n) * R.map (f0 bk)) i j := by
    have h3 : (Pi.map (zC l) * Z₁ - Z * R.map (f0 bk)).map ⇑(phiA l ^ n) =
        Pi.map (zC l) * Z₁.map ⇑(phiA l ^ n) - Z.map ⇑(phiA l ^ n) * R.map (f0 bk) := by
      rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul, hP, hR]
    rw [← h3, Matrix.map_apply]
  rwa [h2] at h1

private theorem one (hInvQ : InvQ) (hInvU : InvU) (hOp : OpOne2) (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l)
    (hτ : bk.IsPer τ) (N k n₁ n₂ : ℕ)
    (hk : ∀ (d : ℕ) (A A' : Matrix (Fin d) (Fin d) bk.S),
      A * A' = bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) bk.S) → ∃ Q Q', IsSecQ bk N k A Q Q')
    (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (G : Frame bk N d fun g => (ρ g).val) (hG : G.IsCr) :
    ∃ (Y Y' : Matrix (Fin d) (Fin d) (Ainf l)) (Q Q' : Matrix (Fin d) (Fin d) (Per.Acris l)),
      Y.map (inclW l) = inclW l τ ^ N • G.T ∧ IsSecQ bk N k G.A Q Q' ∧
      (Y.map (fI l) * Q) * (Q' * Y'.map (fI l)) =
        (fI l τ ^ (2 * N) * (l : Per.Acris l) ^ (2 * k)) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) ∧
      (Q' * Y'.map (fI l)) * (Y.map (fI l) * Q) =
        (fI l τ ^ (2 * N) * (l : Per.Acris l) ^ (2 * k)) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) ∧
      IsUnit (iB l ((phiA l ^ n₂) (fI l τ) ^ (3 * N) * (l : Per.Acris l) ^ (4 * k) * (phiA l ^ n₁) (fI l τ) ^ N)) ∧
      IsOp2 ρ n₁ n₂ (iB l ((phiA l ^ n₂) (fI l τ) ^ (3 * N) * (l : Per.Acris l) ^ (4 * k) * (phiA l ^ n₁) (fI l τ) ^ N))
        (((phiA l ^ n₂) (fI l τ ^ (2 * N) * (l : Per.Acris l) ^ (2 * k)) •
          ((Y.map (fI l) * Q).map ⇑(phiA l ^ n₁) * (Q' * Y'.map (fI l)).map ⇑(phiA l ^ n₂))).map (iB l)) := by
  obtain ⟨Y, Y', hY, hYY⟩ := GlobalTheory.T.breuilKisinPreframe_bounded_poles l K bk τ hτ N d _ G.toPre
  obtain ⟨Q, Q', hQ⟩ := hk d G.A G.A' G.A_mul
  have hinv := hInvQ l K bk τ hτ N k d ρ G hG Q Q' hQ
  have hyy : Y.map (fI l) * Y'.map (fI l) = fI l τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) := by
    rw [← Matrix.map_mul, hYY, GlobalTheory.BcrisInv.map_smul_matrix, Matrix.map_one _ (map_zero _) (map_one _), map_pow]
  obtain ⟨U, hU, hUe⟩ := (hInvU l K bk τ hτ).2 N k d ρ G Y Y' Q Q' hY hYY hQ.mul hinv
  exact ⟨Y, Y', Q, Q', hY, hQ,
    hOp l (fI l τ) (hInvU l K bk τ hτ).1 K N k n₁ n₂ d ρ (Y.map (fI l)) (Y'.map (fI l)) Q Q' U hyy hQ.mul hU hUe⟩

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.opEx_holds :
    SecU → InvQ → InvU → LinkZ → LinkOp2 → FixW → OpOne2 → OpEx2 := by
  intro hSec hInvQ hInvU hLinkZ hLinkOp hFix hOp l _ K bk τ hτ P AI T n₁ n₂ hn₁ hn₂ d N ρ tw F F₀ r hF hF₀ hlink
  obtain ⟨k, hk⟩ := hSec l K bk N
  obtain ⟨Y₀, Y₀', Q₀, Q₀', hY₀, hQ₀, a1, a2, a3, a4⟩ :=
    one hInvQ hInvU hOp l K bk τ hτ N k n₁ n₂ hk d ρ F₀ hF₀
  choose Y Y' Q Q' hY hQ b1 b2 b3 b4 using fun m =>
    one hInvQ hInvU hOp l K bk τ hτ N k n₁ n₂ hk (tw.d' m) (tw.ρ' m) (F m) (hF m)
  refine ⟨_, (phiA l ^ n₂) (fI l τ ^ (2 * N) * (l : Per.Acris l) ^ (2 * k)) •
      ((Y₀.map (fI l) * Q₀).map ⇑(phiA l ^ n₁) * (Q₀' * Y₀'.map (fI l)).map ⇑(phiA l ^ n₂)),
    fun m => (phiA l ^ n₂) (fI l τ ^ (2 * N) * (l : Per.Acris l) ^ (2 * k)) •
      (((Y m).map (fI l) * Q m).map ⇑(phiA l ^ n₁) * (Q' m * (Y' m).map (fI l)).map ⇑(phiA l ^ n₂)),
    a3, a4, b4, ?_⟩
  intro M
  obtain ⟨n, hn⟩ := hLinkZ l K bk τ hτ N M
  obtain ⟨m, hm, R, -, hdiv, -⟩ := hlink (max n M)
  refine ⟨m, le_trans (le_max_right _ _) hm, ?_⟩
  have hd : ∀ i j, (l : WCb l) ^ n ∣ (zW (tw.Pi m) * (F m).T - F₀.T * R.map bk.evW) i j :=
    fun i j => (pow_dvd_pow _ (le_max_left _ _)).trans (hdiv i j)
  have h0 := hn k d (tw.d' m) _ _ F₀ (F m) Y₀ (Y m) hY₀ (hY m) Q₀ Q₀' (Q m) (Q' m) hQ₀ (hQ m) (tw.Pi m) R hd
  have h1 := map_link hFix l K bk P AI T n₁ hn₁ d (tw.d' m) M (tw.Pi m) R _ _ h0
  have h2 := map_link hFix l K bk P AI T n₂ hn₂ d (tw.d' m) M (tw.Pi m) R _ _ h0
  have e1 : (Q₀' * Y₀'.map (fI l)).map ⇑(phiA l ^ n₂) * (Y₀.map (fI l) * Q₀).map ⇑(phiA l ^ n₂) =
      (phiA l ^ n₂) (fI l τ ^ (2 * N) * (l : Per.Acris l) ^ (2 * k)) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) := by
    rw [← Matrix.map_mul, a2, GlobalTheory.BcrisInv.map_smul_matrix, Matrix.map_one _ (map_zero _) (map_one _)]
  have e2 : ((Y m).map (fI l) * Q m).map ⇑(phiA l ^ n₂) * (Q' m * (Y' m).map (fI l)).map ⇑(phiA l ^ n₂) =
      (phiA l ^ n₂) (fI l τ ^ (2 * N) * (l : Per.Acris l) ^ (2 * k)) •
        (1 : Matrix (Fin (tw.d' m)) (Fin (tw.d' m)) (Per.Acris l)) := by
    rw [← Matrix.map_mul, b1 m, GlobalTheory.BcrisInv.map_smul_matrix, Matrix.map_one _ (map_zero _) (map_one _)]
  exact hLinkOp (Per.Acris l) ((l : Per.Acris l) ^ M) _ d (tw.d' m) _ _ _ _ _ _ ((tw.Pi m).map (zC l)) (R.map (f0 bk))
    e1 e2 h2 h1
