import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FderivEqOfJetOf
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open scoped ContDiff

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal.JetCorr

theorem jet_point_eq {K : Type} [Field K] {J : Type} {m : ℕ} (p : PrimeSpectrum (Jet K J m)) :
    p = IsLocalRing.closedPoint (Jet K J m) := by
  apply PrimeSpectrum.ext
  refine le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) fun a ha => ?_
  have hn : IsNilpotent a := by
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hn := jet_nilpotent_of_orig K J m (sub_const_mem_orig (R := K) q)
    have h0 : MvPolynomial.constantCoeff q = 0 := by
      by_contra hne
      refine (IsLocalRing.mem_maximalIdeal _).mp ha ?_
      have e : algebraMap K (Jet K J m) (MvPolynomial.constantCoeff q) =
          Ideal.Quotient.mk (orig K J ^ (m + 1)) (MvPolynomial.C (MvPolynomial.constantCoeff q)) := by
        rw [← MvPolynomial.algebraMap_eq]; rfl
      have hsplit : Ideal.Quotient.mk (orig K J ^ (m + 1)) q =
          algebraMap K (Jet K J m) (MvPolynomial.constantCoeff q) +
            Ideal.Quotient.mk (orig K J ^ (m + 1)) (q - MvPolynomial.C (MvPolynomial.constantCoeff q)) := by
        rw [map_sub, e, add_sub_cancel]
      rw [hsplit]
      exact IsNilpotent.isUnit_add_left_of_commute hn
        ((isUnit_iff_ne_zero.mpr hne).map (algebraMap K (Jet K J m))) (Commute.all _ _)
    rwa [h0, map_zero, sub_zero] at hn
  obtain ⟨n, hn⟩ := hn
  exact p.isPrime.mem_of_pow_mem n (hn ▸ p.asIdeal.zero_mem)

section JetOf

variable {N : ℕ} (m : ℕ)

theorem jetOf_one' : jetOf m (fun _ : Fin N → ℂ => (1 : ℂ)) = 1 := by
  rw [jetOf_const, map_one]

theorem jetOf_pow' {F : (Fin N → ℂ) → ℂ} (hF : AnalyticAt ℂ F 0) (k : ℕ) :
    jetOf m (fun v => F v ^ k) = jetOf m F ^ k := by
  induction k with
  | zero => simpa using jetOf_one' m
  | succ k ih =>
    rw [pow_succ, ← ih, ← jetOf_mul m (hF.fun_pow k).contDiffAt hF.contDiffAt]
    congr 1

theorem jetOf_mul_inv {F : (Fin N → ℂ) → ℂ} (hF : AnalyticAt ℂ F 0) (h0 : F 0 ≠ 0) :
    jetOf m F * jetOf m (fun v => (F v)⁻¹) = 1 := by
  rw [← jetOf_mul m hF.contDiffAt (hF.fun_inv h0).contDiffAt, ← jetOf_one' m]
  refine jetOf_congr m ((hF.continuousAt.eventually_ne h0).mono fun v hv => ?_)
  exact mul_inv_cancel₀ hv

theorem jetOf_zpow {F : (Fin N → ℂ) → ℂ} (hF : AnalyticAt ℂ F 0) (h0 : F 0 ≠ 0)
    (u : (Jet ℂ (Fin 1 × Fin N) m)ˣ) (hu : u.val = jetOf m F) (a : ℤ) :
    jetOf m (fun v => F v ^ a) = (u ^ a).val := by
  obtain ⟨k, rfl | rfl⟩ := a.eq_nat_or_neg
  · simp only [zpow_natCast, Units.val_pow_eq_pow_val, hu]
    exact jetOf_pow' m hF k
  · simp only [zpow_neg, zpow_natCast]
    symm
    apply Units.inv_eq_of_mul_eq_one_right
    rw [Units.val_pow_eq_pow_val, hu, ← jetOf_pow' m hF k]
    exact jetOf_mul_inv m (hF.fun_pow k) (pow_ne_zero _ h0)

theorem jetOf_prod {K : Type} (s : Finset K) {F : K → (Fin N → ℂ) → ℂ} (hF : ∀ k, AnalyticAt ℂ (F k) 0) :
    jetOf m (fun v => ∏ k ∈ s, F k v) = ∏ k ∈ s, jetOf m (F k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using jetOf_one' m
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, ← ih, ← jetOf_mul m (hF a).contDiffAt
      (Finset.analyticAt_fun_prod s fun k _ => hF k).contDiffAt]
    congr 1
    funext v
    simp [Finset.prod_insert ha]

end JetOf

theorem jetN_prod_zpow {n g : ℕ} (m : ℕ) {K : Type} [Fintype K] (f : K → (Fin g → ℂ) → ℂ)
    (hf : ∀ k, AnalyticAt ℂ (f k) 0) (h0 : ∀ k, f k 0 ≠ 0)
    (Λ : K → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (ε : K → ℤ) :
    ∃ u : K → (Jet ℂ (Fin n × Fin g) m)ˣ, (∀ k, (u k).val = jetN m fun w => f k (Λ k w)) ∧
      jetN m (fun w => ∏ k, f k (Λ k w) ^ ε k) = (∏ k, u k ^ ε k).val := by
  have hc : colsOf n g 0 = 0 := rfl
  have hA : ∀ k, AnalyticAt ℂ (fun v => f k (Λ k (colsOf n g v))) 0 := fun k => by
    have h1 : AnalyticAt ℂ (colsOf n g) 0 :=
      AnalyticAt.pi fun i => AnalyticAt.pi fun j =>
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n * g) => ℂ) (finProdFinEquiv (i, j))).analyticAt 0
    have h2 : AnalyticAt ℂ (fun v => Λ k (colsOf n g v)) 0 :=
      ((LinearMap.toContinuousLinearMap (Λ k)).analyticAt _).comp h1
    exact (hf k).comp_of_eq h2 (by rw [hc, map_zero])
  have hz : ∀ k, f k (Λ k (colsOf n g 0)) ≠ 0 := fun k => by rw [hc, map_zero]; exact h0 k
  let u0 : K → (Jet ℂ (Fin 1 × Fin (n * g)) m)ˣ := fun k =>
    Units.mkOfMulEqOne _ _ (jetOf_mul_inv m (hA k) (hz k))
  refine ⟨fun k => Units.map (renN n g m).toMonoidHom (u0 k), fun k => rfl, ?_⟩
  unfold jetN
  rw [jetOf_prod m Finset.univ (F := fun k v => f k (Λ k (colsOf n g v)) ^ ε k)
    fun k => (hA k).fun_zpow (hz k), map_prod, Units.coe_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [jetOf_zpow m (hA k) (hz k) (u0 k) rfl, ← map_zpow]
  rfl

open scoped Classical in
theorem prod_zpow_fiber {M T K : Type*} [CommGroup M] [Fintype K] (s : Finset T) (φ : K → T) (hs : ∀ k, φ k ∈ s)
    (ε : K → ℤ) (w : T → M) :
    ∏ k, w (φ k) ^ ε k = ∏ ψ ∈ s, w ψ ^ (∑ k, if φ k = ψ then ε k else 0) := by
  have h : ∀ ψ, w ψ ^ (∑ k, if φ k = ψ then ε k else 0) = ∏ k, if φ k = ψ then w ψ ^ ε k else 1 := fun ψ => by
    have hz : ∀ t : Finset K, ∀ a : K → ℤ, w ψ ^ (∑ k ∈ t, a k) = ∏ k ∈ t, w ψ ^ a k := fun t a => by
      induction t using Finset.induction_on with
      | empty => simp
      | insert b t hb ih => rw [Finset.sum_insert hb, Finset.prod_insert hb, zpow_add, ih]
    rw [hz]
    refine Finset.prod_congr rfl fun k _ => ?_
    split_ifs <;> simp
  simp only [h]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finset.prod_ite_eq, if_pos (hs k)]

open scoped Classical in

theorem prod_zpow_eq {M T K K' : Type*} [CommGroup M] [Fintype K] [Fintype K'] (φ : K → T) (ε : K → ℤ)
    (φ' : K' → T) (ε' : K' → ℤ) (u : K → M) (u' : K' → M)
    (h₁ : ∀ k l, φ k = φ l → u k = u l) (h₂ : ∀ k l, φ' k = φ' l → u' k = u' l)
    (h₃ : ∀ k l, φ k = φ' l → u k = u' l)
    (hs : ∀ ψ, (∑ k, if φ k = ψ then ε k else 0) = ∑ k', if φ' k' = ψ then ε' k' else 0) :
    ∏ k, u k ^ ε k = ∏ k, u' k ^ ε' k := by
  let w : T → M := fun ψ => if h : ∃ k, φ k = ψ then u h.choose else if h' : ∃ k, φ' k = ψ then u' h'.choose else 1
  have hw : ∀ k, u k = w (φ k) := fun k => by
    have h : ∃ l, φ l = φ k := ⟨k, rfl⟩
    simp only [w, dif_pos h]
    exact h₁ _ _ h.choose_spec.symm
  have hw' : ∀ k, u' k = w (φ' k) := fun k => by
    by_cases h : ∃ l, φ l = φ' k
    · simp only [w, dif_pos h]
      exact (h₃ _ _ h.choose_spec).symm
    · have h' : ∃ l, φ' l = φ' k := ⟨k, rfl⟩
      simp only [w, dif_neg h, dif_pos h']
      exact h₂ _ _ h'.choose_spec.symm
  simp only [hw, hw']
  rw [prod_zpow_fiber (Finset.univ.image φ ∪ Finset.univ.image φ') φ (fun k => by simp) ε w,
    prod_zpow_fiber (Finset.univ.image φ ∪ Finset.univ.image φ') φ' (fun k => by simp) ε' w]
  simp only [hs]

section Frame

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)

set_option backward.isDefEq.respectTransparency false in

theorem origin_mem {n m : ℕ} {ψ : Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left}
    {Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)} (h : Φ.JetMap m ψ Λ) {U : A.left.Opens}
    (p : Sp (Jet ℂ (Fin n × Fin g) m)) (hp : ψ p ∈ U) : ⊤ ≤ (Φ.e 0).left ⁻¹ᵁ U := by
  obtain ⟨hol, rfl⟩ := h
  rw [Scheme.Hom.comp_apply, jet_point_eq (K := ℂ) (J := Fin 1 × Fin (n * g)) (m := m)
      (spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) p),
    jetPt_closedPoint] at hp
  have hc : colsOf n g 0 = 0 := rfl
  rw [hc, map_zero] at hp
  exact top_le_of_mem hp

theorem fr_analyticAt (j : L.L.ι) (h : ⊤ ≤ (Φ.e 0).left ⁻¹ᵁ L.L.U j) : AnalyticAt ℂ (Φ.fr j) 0 :=
  GlobalTheory.SCV.analyticAt_of_differentiableOn (Φ.fr_hol j) ((Φ.hol (L.L.U j) 0).1.mem_nhds h)

end Frame

set_option backward.isDefEq.respectTransparency false in

theorem corr_of_jetRd : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), Φ.Imm → ∀ (n m : ℕ) (K K' : Type) [Fintype K] [Fintype K'] (φ : K → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)) (ε : K → ℤ) (τ : LB.Gen (LB.LinComb L.L φ ε)) (Λ : K → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (φ' : K' → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)) (ε' : K' → ℤ) (τ' : LB.Gen (LB.LinComb L.L φ' ε')) (Λ' : K' → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), Φ.JetRd m φ ε τ Λ → Φ.JetRd m φ' ε' τ' Λ' → LB.SameSum φ ε φ' ε' → LB.Gen.Corr L.L φ ε φ' ε' τ τ' := by
  intro S A _ _ L x0 g Φ hI n m K K' _ _ φ ε τ Λ φ' ε' τ' Λ' h h' hs j j' c c' cc
  by_cases hW : ∃ p, p ∈ LB.wchart L.L φ j ⊓ LB.wchart L.L φ' j'
  · obtain ⟨p, hp⟩ := hW
    have hT : ⊤ ≤ LB.wchart L.L φ j ⊓ LB.wchart L.L φ' j' := fun q _ => by
      have e1 := jet_point_eq (K := ℂ) (J := Fin n × Fin g) (m := m) p
      have e2 := jet_point_eq (K := ℂ) (J := Fin n × Fin g) (m := m) q
      rw [e2, ← e1]
      exact hp
    have o : ∀ k, ⊤ ≤ (Φ.e 0).left ⁻¹ᵁ L.L.U (j k) := fun k =>
      origin_mem Φ (h.1 k) p (LB.wchart_le L.L φ j k hp.1)
    have o' : ∀ k, ⊤ ≤ (Φ.e 0).left ⁻¹ᵁ L.L.U (j' k) := fun k =>
      origin_mem Φ (h'.1 k) p (LB.wchart_le L.L φ' j' k hp.2)
    obtain ⟨u, hu, hP⟩ := jetN_prod_zpow m (fun k => Φ.fr (j k)) (fun k => fr_analyticAt Φ _ (o k))
      (fun k => Φ.fr_ne _ _ (o k)) Λ ε
    obtain ⟨u', hu', hP'⟩ := jetN_prod_zpow m (fun k => Φ.fr (j' k)) (fun k => fr_analyticAt Φ _ (o' k))
      (fun k => Φ.fr_ne _ _ (o' k)) Λ' ε'
    have hE : ∏ k, u k ^ ε k = ∏ k, u' k ^ ε' k := by
      refine prod_zpow_eq φ ε φ' ε' u u' (fun k l e => Units.ext ?_) (fun k l e => Units.ext ?_)
        (fun k l e => Units.ext ?_) hs
      · rw [hu, hu, c k l e]
        exact GlobalTheory.AnVal.JetUniq.jet_uniq S A L x0 g Φ hI n m (φ l) _ _ (e ▸ h.1 k) (h.1 l) _
      · rw [hu', hu', c' k l e]
        exact GlobalTheory.AnVal.JetUniq.jet_uniq S A L x0 g Φ hI n m (φ' l) _ _ (e ▸ h'.1 k) (h'.1 l) _
      · rw [hu, hu', cc k l e]
        exact GlobalTheory.AnVal.JetUniq.jet_uniq S A L x0 g Φ hI n m (φ' l) _ _ (e ▸ h.1 k) (h'.1 l) _
    have r := h.2 j (hT.trans inf_le_left)
    have r' := h'.2 j' (hT.trans inf_le_right)
    rw [hP, hE, ← hP', ← r'] at r
    apply Units.ext
    have r2 := congrArg ((Sp (Jet ℂ (Fin n × Fin g) m)).presheaf.map
      (homOfLE (le_top : LB.wchart L.L φ j ⊓ LB.wchart L.L φ' j' ≤ ⊤)).op).hom r
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp] at r2
    exact r2
  · have hB : LB.wchart L.L φ j ⊓ LB.wchart L.L φ' j' = ⊥ := by
      rw [eq_bot_iff]
      exact fun p hp => (hW ⟨p, hp⟩).elim
    have : Subsingleton Γ(Sp (Jet ℂ (Fin n × Fin g) m), LB.wchart L.L φ j ⊓ LB.wchart L.L φ' j') := by
      rw [hB]; infer_instance
    exact Units.ext (Subsingleton.elim _ _)

end GlobalTheory.AnVal.JetCorr
