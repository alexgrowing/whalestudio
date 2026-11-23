import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IntBasisAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisTorsionFreeCompleteFrobeniusPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinDistinguishedPowerSeriesAdicComplete
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

private theorem map_smul_ringHom {S T : Type} [CommRing S] [CommRing T] (f : S →+* T) {d : ℕ} (c : S)
    (M : Matrix (Fin d) (Fin d) S) : (c • M).map f = f c • M.map f := by
  ext i j; simp

private theorem dvd_mul_entries_left {T : Type} [CommRing T] {a b e : ℕ} (c : T) (A : Matrix (Fin a) (Fin b) T)
    (B : Matrix (Fin b) (Fin e) T) (h : ∀ i j, c ∣ B i j) (i : Fin a) (j : Fin e) : c ∣ (A * B) i j := by
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum fun k _ => Dvd.dvd.mul_left (h k j) _

private theorem dvd_mul_entries_right {T : Type} [CommRing T] {a b e : ℕ} (c : T) (A : Matrix (Fin a) (Fin b) T)
    (B : Matrix (Fin b) (Fin e) T) (h : ∀ i j, c ∣ A i j) (i : Fin a) (j : Fin e) : c ∣ (A * B) i j := by
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum fun k _ => Dvd.dvd.mul_right (h i k) _

private theorem map_intertwine {S T : Type} [CommRing S] [CommRing T] (f : S →+* T) (ψ : S →+* S) (φ : T →+* T)
    (hf : ∀ s, φ (f s) = f (ψ s)) {d d' : ℕ} (c : S) (A : Matrix (Fin d) (Fin d) S) (A₁ : Matrix (Fin d') (Fin d') S)
    (R : Matrix (Fin d) (Fin d') S) (h : ∀ i j, c ∣ (R * A₁ - A * R.map ψ) i j) (i : Fin d) (j : Fin d') :
    f c ∣ (R.map f * A₁.map f - A.map f * (R.map f).map φ) i j := by
  have e : R.map f * A₁.map f - A.map f * (R.map f).map φ = (R * A₁ - A * R.map ψ).map f := by
    have e' : (R.map f).map φ = (R.map ψ).map f := by
      ext i j; simp [hf]
    rw [e']
    ext i j
    simp [Matrix.mul_apply, map_sum]
  rw [e, Matrix.map_apply]
  exact map_dvd f (h i j)

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.linkQ_holds :
    ZeroAp → LinkRec → LinkQ := by
  intro hZ hR l _ K bk N M
  obtain ⟨n, hn⟩ := hZ l K bk (3 * N) M
  refine ⟨n, ?_⟩
  intro k d d' A A₁ A₁' Q Q' Q₁ Q₁' R hA hS hS₁ hRel
  obtain ⟨-, -, ⟨v, hv⟩, hφι, -⟩ := GlobalTheory.T.acris_torsionFree_complete_frobenius_properties l K bk
  have hv' : fA bk bk.E = (l : Per.Acris l) * v := hv
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : (Per.Acris l)ˣ, f0 bk bk.E = (l : Per.Acris l) * w₀ := by
    obtain ⟨w, hw⟩ := bk.coeff_zero
    have hc : PowerSeries.constantCoeff bk.E = (l : Wq l bk.a) * w := by
      rw [← hw]; simp
    refine ⟨(Units.map (PowerSeries.C (R := Wq l bk.a)).toMonoidHom w).map (fA bk).toMonoidHom, ?_⟩
    simp [f0, hc]
  have hφA : ∀ s, phiA l (fA bk s) = fA bk (frobS l bk.a s) := fun s => by
    simp only [fA, RingHom.comp_apply, hφι, bk.ev_frob]
  have hφ0 : ∀ s, phiA l (f0 bk s) = f0 bk (frobS l bk.a s) := fun s => by
    rw [show f0 bk s = fA bk (PowerSeries.C (PowerSeries.constantCoeff s)) from rfl, hφA, frobS_C,
      show f0 bk (frobS l bk.a s) = fA bk (PowerSeries.C (PowerSeries.constantCoeff (frobS l bk.a s))) from rfl,
      constantCoeff_frobS_apply]
  have hdiff : ∀ s, uC bk ∣ fA bk s - f0 bk s := fun s => by
    obtain ⟨t, ht⟩ := (PowerSeries.X_dvd_iff (φ := s - PowerSeries.C (PowerSeries.constantCoeff s))).2 (by simp)
    have e : fA bk s - f0 bk s = uC bk ^ l * fA bk t := by
      rw [show f0 bk s = fA bk (PowerSeries.C (PowerSeries.constantCoeff s)) from rfl, ← map_sub, ht, map_mul]
      congr 1
      simp [fA, uC, frobS_X]
    rw [e]
    exact Dvd.dvd.mul_right (dvd_pow_self _ (Fact.out : l.Prime).ne_zero) _
  have hlc : ∀ f : bk.S →+* Per.Acris l, f ((l : bk.S) ^ n) = (l : Per.Acris l) ^ n := fun f => by
    rw [map_pow, map_natCast]
  have h1 : A₁.map (f0 bk) * A₁'.map (f0 bk) =
      ((l : Per.Acris l) * w₀) ^ (2 * N) • (1 : Matrix (Fin d') (Fin d') (Per.Acris l)) := by
    rw [← hw₀, ← Matrix.map_mul, hA, map_smul_ringHom, map_pow, Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : ((l : Per.Acris l) * v) ^ N • (Q * A.map (f0 bk)) =
      ((l : Per.Acris l) * w₀) ^ N • (A.map (fA bk) * Q.map (phiA l)) := by
    rw [← hv', ← hw₀]; exact hS.frob
  have h3 : ((l : Per.Acris l) * v) ^ N • (Q₁ * A₁.map (f0 bk)) =
      ((l : Per.Acris l) * w₀) ^ N • (A₁.map (fA bk) * Q₁.map (phiA l)) := by
    rw [← hv', ← hw₀]; exact hS₁.frob
  have h4 : ∀ i j, (l : Per.Acris l) ^ n ∣
      (R.map (fA bk) * A₁.map (fA bk) - A.map (fA bk) * (R.map (fA bk)).map (phiA l)) i j := fun i j => by
    rw [← hlc (fA bk)]
    exact map_intertwine (fA bk) (frobS l bk.a) (phiA l) hφA _ A A₁ R hRel i j
  have h5 : ∀ i j, (l : Per.Acris l) ^ n ∣
      (R.map (f0 bk) * A₁.map (f0 bk) - A.map (f0 bk) * (R.map (f0 bk)).map (phiA l)) i j := fun i j => by
    rw [← hlc (f0 bk)]
    exact map_intertwine (f0 bk) (frobS l bk.a) (phiA l) hφ0 _ A A₁ R hRel i j
  obtain ⟨F, F', hF⟩ := hR (Per.Acris l) (phiA l) (l : Per.Acris l) ((l : Per.Acris l) ^ n) v w₀ N d d'
    (A.map (fA bk)) (A.map (f0 bk)) Q (A₁.map (fA bk)) (A₁.map (f0 bk)) (A₁'.map (f0 bk)) Q₁
    (R.map (fA bk)) (R.map (f0 bk)) h1 h2 h3 h4 h5
  refine hn d d' _ F F' ?_ hF
  intro i j
  have hD : R.map (fA bk) * Q₁ - Q * R.map (f0 bk) =
      R.map (fA bk) * (Q₁ - (l : Per.Acris l) ^ k • (1 : Matrix (Fin d') (Fin d') (Per.Acris l))) +
        (l : Per.Acris l) ^ k • (R.map (fA bk) - R.map (f0 bk)) -
        (Q - (l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) * R.map (f0 bk) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, smul_sub]
    abel
  rw [hD, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply, Matrix.map_apply]
  refine dvd_sub (dvd_add (dvd_mul_entries_left _ _ _ hS₁.mod i j) ?_) (dvd_mul_entries_right _ _ _ hS.mod i j)
  rw [smul_eq_mul]
  exact Dvd.dvd.mul_left (hdiff _) _
