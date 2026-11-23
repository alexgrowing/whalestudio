import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.BlockRank

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

section

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {N r : ℕ} [NeZero r] (D : BlockData N)

def qq (i : Fin (D.T.t + 1)) : MvPolynomial (BVar N r D.T.t) (KK O) :=
  Fin.lastCases (motive := fun _ => MvPolynomial (BVar N r D.T.t) (KK O))
    (∑ c, X (Sum.inl (Fin.castSucc D.uPos, c)) * X (xiVar N r D.T.t c))
    (fun i => ∑ c, X (Sum.inl (finPos N (D.T.pos i), c)) * X (Sum.inl (finPos N (D.T.pos i + 1), c))) i

def tauF (v : BVar N r D.T.t) : MvPolynomial (BVar N r D.T.t) (KK O) :=
  match v with
  | Sum.inl a => X (Sum.inl a)
  | Sum.inr (i, false) => X (Sum.inr (i, false))
  | Sum.inr (i, true) => X (Sum.inr (i, false)) * X (Sum.inr (i, true)) + qq (O := O) (r := r) D i

def tau : MvPolynomial (BVar N r D.T.t) (KK O) →ₐ[KK O] MvPolynomial (BVar N r D.T.t) (KK O) := aeval (tauF D)

def rhoF (v : BVar N r D.T.t) : FractionRing (MvPolynomial (BVar N r D.T.t) (KK O)) :=
  match v with
  | Sum.inl a => algebraMap _ _ (X (Sum.inl a) : MvPolynomial (BVar N r D.T.t) (KK O))
  | Sum.inr (i, false) => algebraMap _ _ (X (Sum.inr (i, false)) : MvPolynomial (BVar N r D.T.t) (KK O))
  | Sum.inr (i, true) => (algebraMap _ _ (X (Sum.inr (i, true)) : MvPolynomial (BVar N r D.T.t) (KK O)) -
      algebraMap _ _ (qq (O := O) (r := r) D i)) / algebraMap _ _ (X (Sum.inr (i, false)) : MvPolynomial (BVar N r D.T.t) (KK O))

def rho : MvPolynomial (BVar N r D.T.t) (KK O) →ₐ[KK O] FractionRing (MvPolynomial (BVar N r D.T.t) (KK O)) :=
  aeval (rhoF D)

theorem rho_inl (a : Fin (N + 1) × Fin r) : rho (O := O) (r := r) D (X (Sum.inl a)) = algebraMap _ _ (X (Sum.inl a) :
    MvPolynomial (BVar N r D.T.t) (KK O)) := by
  simp [rho, rhoF]

theorem rho_qq (i : Fin (D.T.t + 1)) : rho (O := O) (r := r) D (qq (O := O) (r := r) D i) = algebraMap _ _ (qq (O := O) (r := r) D i) := by
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp only [qq, Fin.lastCases_last, map_sum, map_mul, xiVar, rho_inl]
  · simp only [qq, Fin.lastCases_castSucc, map_sum, map_mul, rho_inl]

theorem rho_tau (f : MvPolynomial (BVar N r D.T.t) (KK O)) : rho D (tau D f) = algebraMap _ _ f := by
  have h : (rho (O := O) (r := r) D).comp (tau D) = IsScalarTower.toAlgHom (KK O) _
      (FractionRing (MvPolynomial (BVar N r D.T.t) (KK O))) := by
    apply MvPolynomial.algHom_ext
    intro v
    rcases v with a | ⟨i, _ | _⟩
    · simp [tau, tauF, rho_inl]
    · simp [tau, tauF, rho, rhoF]
    · have hz : algebraMap (MvPolynomial (BVar N r D.T.t) (KK O))
          (FractionRing (MvPolynomial (BVar N r D.T.t) (KK O))) (X (Sum.inr (i, false))) ≠ 0 :=
        (IsFractionRing.injective (MvPolynomial (BVar N r D.T.t) (KK O)) _).ne_iff.mpr (X_ne_zero _) |>.trans_eq (map_zero _)
      simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
      rw [tau, aeval_X]
      simp only [tauF]
      rw [map_add, map_mul, rho_qq]
      rw [rho, aeval_X, aeval_X]
      simp only [rhoF]
      field_simp
      ring
  exact AlgHom.congr_fun h f

theorem tau_inj : Function.Injective (tau (O := O) (r := r) D) := by
  intro f g h
  apply IsFractionRing.injective (MvPolynomial (BVar N r D.T.t) (KK O))
    (FractionRing (MvPolynomial (BVar N r D.T.t) (KK O)))
  rw [← rho_tau D f, ← rho_tau D g, h]

theorem xiMon_prod (K : Type) [CommRing K] (N r t : ℕ) (β : Fin r → ℕ) :
    xiMon K N r t β = ∏ c, X (xiVar N r t c) ^ β c := by
  simp only [xiMon, xiExp, monomial_sum_one, X_pow_eq_monomial]

def base (x : (Fin D.T.t → ℕ) × ℕ) (β : Fin r → ℕ) (y : MvPolynomial (Fin N × Fin r) (KK O)) :
    MvPolynomial (BVar N r D.T.t) (KK O) :=
  (∏ i, X (scalS N r D.T.t (Fin.castSucc i)) ^ x.1 i) * X (scalS N r D.T.t (Fin.last D.T.t)) ^ x.2 *
      (∏ i, X (scalZ N r D.T.t (Fin.castSucc i)) ^ D.T.z i) * X (scalZ N r D.T.t (Fin.last D.T.t)) ^ D.zPlus *
    (rename (chainEmb N r D.T.t) y * xiMon (KK O) N r D.T.t β)

theorem tau_rename (y : MvPolynomial (Fin N × Fin r) (KK O)) :
    tau D (rename (chainEmb N r D.T.t) y) = rename (chainEmb N r D.T.t) y := by
  have h : (tau (O := O) (r := r) D).comp (rename (chainEmb N r D.T.t)) = rename (chainEmb N r D.T.t) := by
    apply MvPolynomial.algHom_ext
    intro x
    simp [tau, tauF, chainEmb]
  exact AlgHom.congr_fun h y

theorem ell_eq_tau (x : (Fin D.T.t → ℕ) × ℕ) (β : Fin r → ℕ) (y : MvPolynomial (Fin N × Fin r) (KK O)) :
    ell D x β y = tau D (base D x β y) := by
  have h1 : ∀ i : Fin D.T.t, tau (O := O) (r := r) D (X (scalS N r D.T.t (Fin.castSucc i))) = D.Ehat O (r := r) i := by
    intro i
    simp [tau, tauF, scalS, scalZ, qq, BlockData.Ehat]
  have h2 : tau (O := O) (r := r) D (X (scalS N r D.T.t (Fin.last D.T.t))) = D.Eplus O (r := r) := by
    simp [tau, tauF, scalS, scalZ, qq, BlockData.Eplus]
  have h3 : ∀ i, tau (O := O) (r := r) D (X (scalZ N r D.T.t i)) = X (scalZ N r D.T.t i) := by
    intro i
    simp [tau, tauF, scalZ]
  have h4 : tau (O := O) (r := r) D (xiMon (KK O) N r D.T.t β) = xiMon (KK O) N r D.T.t β := by
    rw [xiMon_prod, map_prod]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [map_pow]
    simp [tau, tauF, xiVar]
  rw [ell_apply]
  unfold base pre
  simp only [map_mul, map_prod, map_pow, h1, h2, h3, h4, tau_rename]

def piF (v : BVar N r D.T.t) : MvPolynomial (Fin (D.T.t + 1) ⊕ Fin r) (MvPolynomial (Fin N × Fin r) (KK O)) :=
  match v with
  | Sum.inl (a, c) => Fin.lastCases
      (motive := fun _ => MvPolynomial (Fin (D.T.t + 1) ⊕ Fin r) (MvPolynomial (Fin N × Fin r) (KK O)))
      (X (Sum.inr c)) (fun a' => C (X (a', c))) a
  | Sum.inr (_, false) => 1
  | Sum.inr (i, true) => X (Sum.inl i)

def ppi : MvPolynomial (BVar N r D.T.t) (KK O) →ₐ[KK O]
    MvPolynomial (Fin (D.T.t + 1) ⊕ Fin r) (MvPolynomial (Fin N × Fin r) (KK O)) := aeval (piF D)

theorem ppi_rename (y : MvPolynomial (Fin N × Fin r) (KK O)) : ppi D (rename (chainEmb N r D.T.t) y) = C y := by
  induction y using MvPolynomial.induction_on
  next a =>
    simp [ppi]
  next p q hp hq =>
    rw [map_add, map_add, hp, hq, C_add]
  next p x hp =>
    rw [map_mul, rename_X, map_mul, hp, ppi, aeval_X, C_mul]
    simp [piF, chainEmb]

def eExp (x : (Fin D.T.t → ℕ) × ℕ) (β : Fin r → ℕ) : (Fin (D.T.t + 1) ⊕ Fin r) →₀ ℕ :=
  (∑ i, Finsupp.single (Sum.inl (Fin.castSucc i)) (x.1 i)) + Finsupp.single (Sum.inl (Fin.last D.T.t)) x.2 +
    ∑ c, Finsupp.single (Sum.inr c) (β c)

theorem ppi_base (x : (Fin D.T.t → ℕ) × ℕ) (β : Fin r → ℕ) (y : MvPolynomial (Fin N × Fin r) (KK O)) :
    ppi D (base D x β y) = monomial (eExp D x β) y := by
  have hS : ∀ i, ppi (O := O) D (X (scalS N r D.T.t i)) = X (Sum.inl i) := by
    intro i
    simp [ppi, piF, scalS]
  have hZ : ∀ i, ppi (O := O) D (X (scalZ N r D.T.t i)) = 1 := by
    intro i
    simp [ppi, piF, scalZ]
  have hXi : ppi (O := O) D (xiMon (KK O) N r D.T.t β) = ∏ c, X (Sum.inr c) ^ β c := by
    rw [xiMon_prod, map_prod]
    simp [ppi, piF, xiVar]
  rw [base]
  simp only [map_mul, map_prod, map_pow, hS, hZ, hXi, ppi_rename, one_pow, Finset.prod_const_one, mul_one]
  rw [eExp]
  simp only [X_pow_eq_monomial, ← monomial_sum_one, C_mul_monomial, monomial_mul, mul_one, one_mul]

theorem eExp_inj {x x' : (Fin D.T.t → ℕ) × ℕ} {β β' : Fin r → ℕ} (h : eExp D x β = eExp D x' β') :
    x = x' ∧ β = β' := by
  have hv : ∀ v, eExp D x β v = eExp D x' β' v := fun v => by rw [h]
  refine ⟨Prod.ext (funext fun i => ?_) ?_, funext fun c => ?_⟩
  · have hi := hv (Sum.inl (Fin.castSucc i))
    simpa [eExp, Finsupp.single_apply] using hi
  · have hi := hv (Sum.inl (Fin.last D.T.t))
    simpa [eExp, Finsupp.single_apply] using hi
  · have hi := hv (Sum.inr c)
    simpa [eExp, Finsupp.single_apply] using hi

theorem ltot_inj : Function.Injective (Ltot (O := O) (r := r) D) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro v hv
  rw [Ltot_apply] at hv
  simp only [ell_eq_tau] at hv
  rw [← map_sum] at hv
  have h0 : ∑ i : ↥(IF (r := r) D), base D i.1.1 i.1.2 (v i : MvPolynomial (Fin N × Fin r) (KK O)) = 0 :=
    tau_inj D (by rw [hv, map_zero])
  have h1 := congrArg (ppi D) h0
  rw [map_sum, map_zero] at h1
  simp only [ppi_base] at h1
  funext i0
  have h2 := congrArg (coeff (eExp D i0.1.1 i0.1.2)) h1
  rw [coeff_sum, coeff_zero, Finset.sum_eq_single i0] at h2
  · rw [coeff_monomial, if_pos rfl] at h2
    exact Subtype.ext h2
  · intro b _ hb
    rw [coeff_monomial, if_neg]
    intro he
    obtain ⟨e1, e2⟩ := eExp_inj D he
    exact hb (Subtype.ext (Sigma.ext e1 (heq_of_eq e2)))
  · intro h
    exact absurd (Finset.mem_univ _) h

end

theorem restInj : RestInj := fun _ _ _ _ _ _ _ D => ltot_inj D

theorem blockRankAt : BlockRankAt := blockRankAt_of restInj

end Formalism.MainNotions.ColumnSystems.Pf
