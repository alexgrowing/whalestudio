import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WachRingFactsUnramifiedLevelOneStatement
import Formalism.PieriBlockIdeals.PieriColumnMinors.HeckeLFunctionIdealEulerProduct

set_option autoImplicit false

noncomputable section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

namespace GlobalTheory.WachMap

section Gen

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {S : Submodule R M} {n : ℕ}

theorem coeff_unique (b : Module.Basis (Fin n) R S) {c d : Fin n → R}
    (h : ∑ j, c j • (b j : M) = ∑ j, d j • (b j : M)) : c = d := by
  have h' : ∑ j, c j • b j = ∑ j, d j • b j := Subtype.ext (by simpa using h)
  exact (b.repr_sum_self c).symm.trans ((congrArg (fun y => ⇑(b.repr y)) h').trans (b.repr_sum_self d))

theorem exists_coeff (b : Module.Basis (Fin n) R S) {x : M} (hx : x ∈ S) :
    ∃ c : Fin n → R, x = ∑ j, c j • (b j : M) := by
  refine ⟨fun j => b.repr ⟨x, hx⟩ j, ?_⟩
  have e := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at e
  exact e.symm

theorem sum_smul_sum {m : ℕ} (a : Fin m → R) (B : Fin m → Fin n → R) (e : Fin n → M) :
    ∑ k, a k • ∑ j, B k j • e j = ∑ j, (∑ k, a k * B k j) • e j := by
  simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

end Gen

def incHom (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] : O⟦X⟧ →+* O⟦X⟧ where
  toFun := inc l O
  map_one' := by simpa using (pi0Subst_laws_hold l O).2.2.1 1
  map_mul' := (pi0Subst_laws_hold l O).2.1
  map_zero' := by simpa using (pi0Subst_laws_hold l O).2.2.1 0
  map_add' := (pi0Subst_laws_hold l O).1

theorem incHom_apply (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] (y : O⟦X⟧) :
    incHom l O y = inc l O y := rfl

theorem map_one_add_X_smul {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {m : ℕ} (D : Mx R⟦X⟧ m m) :
    (1 + (X : R⟦X⟧) • D).map (PowerSeries.map f) = 1 + (X : S⟦X⟧) • D.map (PowerSeries.map f) := by
  ext i j
  by_cases hij : i = j <;> simp [hij]

end GlobalTheory.WachMap

namespace GlobalTheory.WachMap

theorem coeff_comm {R M M' : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    {S' : Submodule R M'} {n n' : ℕ} (e : Fin n → M) (b' : Module.Basis (Fin n') R S')
    (g : M →+ M') (u : M →+ M) (u' : M' →+ M') (σ : R → R) (hg : ∀ (a : R) x, g (a • x) = a • g x)
    (hu' : ∀ (a : R) x, u' (a • x) = σ a • u' x) (hc : ∀ x, g (u x) = u' (g x))
    (p : Fin n → Fin n → R) (p' : Fin n' → Fin n' → R) (A : Fin n' → Fin n → R)
    (hp : ∀ k, u (e k) = ∑ m, p m k • e m) (hp' : ∀ k, u' (b' k : M') = ∑ m, p' m k • (b' m : M'))
    (hA : ∀ k, g (e k) = ∑ m, A m k • (b' m : M')) (j : Fin n') (k : Fin n) :
    ∑ m, p m k * A j m = ∑ m, σ (A m k) * p' j m := by
  have h1 : g (u (e k)) = ∑ j, (∑ m, p m k * A j m) • (b' j : M') := by
    rw [hp k, map_sum]
    simp only [hg, hA]
    exact sum_smul_sum (fun m => p m k) (fun m j => A j m) (fun j => (b' j : M'))
  have h2 : u' (g (e k)) = ∑ j, (∑ m, σ (A m k) * p' j m) • (b' j : M') := by
    rw [hA k, map_sum]
    simp only [hu', hp']
    exact sum_smul_sum (fun m => σ (A m k)) (fun m j => p' j m) (fun j => (b' j : M'))
  have hc' := coeff_unique (c := fun j => ∑ m, p m k * A j m) (d := fun j => ∑ m, σ (A m k) * p' j m) b'
    ((h1.symm.trans (hc (e k))).trans h2)
  exact congrFun hc' j

theorem mul_eq_of_inc {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] (hl : l ≠ 2) {n n' : ℕ}
    (P : Mx O⟦X⟧ n n) (P' : Mx O⟦X⟧ n' n') (A A' : Mx O⟦X⟧ n' n)
    (h : ∀ j k, ∑ m, inc l O (P m k) * inc l O (A j m) = ∑ m, inc l O (A' m k) * inc l O (P' j m)) :
    P' * A' = A * P := by
  refine Matrix.ext fun j k => ?_
  apply (pi0Subst_laws_hold l O).2.2.2.2.2.2.2 hl
  simp only [Matrix.mul_apply]
  show incHom l O (∑ m, P' j m * A' m k) = incHom l O (∑ m, A j m * P m k)
  simp only [map_sum, map_mul, incHom_apply]
  rw [Finset.sum_congr rfl fun m _ => mul_comm (inc l O (P' j m)) (inc l O (A' m k)), ← h j k]
  exact Finset.sum_congr rfl fun m _ => mul_comm _ _

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {L O : Type} [Field L] [Algebra Qp L]
    [CommRing O] [Algebra O L] [TopologicalSpace L] {v : AddValuation L (WithTop ℚ)} {f : ℕ}
    (W : LocWach PD L O v f)

theorem phiD_smul (T : LocLat G Qp L O) (a : LetA O f) (x : W.DD T) :
    W.φD T (a • x) = letφ W.φ₀ a • W.φD T x := by
  rw [← algebraMap_smul W.EE a x, W.φD_smul, W.φE_ext, algebraMap_smul]

theorem gamD_smul (T : LocLat G Qp L O) (γ : W.Gam) (a : LetA O f) (x : W.DD T) :
    W.γD T γ (a • x) = letγ (W.γ₀ γ) a • W.γD T γ x := by
  rw [← algebraMap_smul W.EE a x, W.γD_smul, W.γE_ext, algebraMap_smul]

theorem map_smul_letA {T T' : LocLat G Qp L O} (g : LatHom T.L T'.L) (a : LetA O f)
    (x : W.DD T) : W.map g (a • x) = a • W.map g x := by
  rw [← algebraMap_smul W.EE a x, LinearMap.map_smul, algebraMap_smul]

variable {T T' : LocLat G Qp L O} {n n' : ℕ}
  (b : Module.Basis (Fin n) (LetA O f) ↥(W.N T)) (b' : Module.Basis (Fin n') (LetA O f) ↥(W.N T'))
  {l : ℕ} [Fact l.Prime] [Algebra ℤ_[l] O]

theorem exists_mapMat (RF : ∀ a : O⟦X⟧, (∀ δ ∈ W.DelF, W.γ₀ δ a = a) → ∃ y, inc l O y = a)
    (g : LatHom T.L T'.L) (hT : IsCrys PD T.ρ)
    (hT' : IsCrys PD T'.ρ) (hb : ∀ k, (b k : W.DD T) ∈ W.NΔ T) (hb' : ∀ k, (b' k : W.DD T') ∈ W.NΔ T') :
    ∃ A : ZMod f → Mx O⟦X⟧ n' n, ∀ k, W.map g (b k : W.DD T) =
      ∑ m, (fun i => inc l O (A i m k) : LetA O f) • (b' m : W.DD T') := by
  classical
  have key : ∀ k, ∃ c : Fin n' → LetA O f, W.map g (b k : W.DD T) = ∑ m, c m • (b' m : W.DD T') ∧
      ∀ m i, ∀ δ ∈ W.DelF, W.γ₀ δ (c m i) = c m i := by
    intro k
    have hk : (b k : W.DD T) ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ (b k : W.DD T) = b k := hb k
    have hy : W.map g (b k : W.DD T) ∈ W.N T' := W.map_N g hT hT' _ hk.1
    obtain ⟨c, hc⟩ := exists_coeff b' hy
    refine ⟨c, hc, fun m i δ hδ => ?_⟩
    have hb2 : ∀ m, W.γD T' δ (b' m : W.DD T') = b' m := fun m =>
      (show (b' m : W.DD T') ∈ W.N T' ∧ ∀ δ ∈ W.DelF, W.γD T' δ (b' m : W.DD T') = b' m from hb' m).2 δ hδ
    have e1 : W.γD T' δ (W.map g (b k : W.DD T)) = W.map g (b k : W.DD T) := by
      rw [← W.map_γ, hk.2 δ hδ]
    rw [hc, map_sum] at e1
    simp only [gamD_smul, hb2] at e1
    have e2 := coeff_unique (c := fun m => letγ (W.γ₀ δ) (c m)) (d := c) b' e1
    exact congrFun (congrFun e2 m) i
  choose c hc hinv using key
  refine ⟨fun i m k => Classical.choose (RF (c k m i) (fun δ hδ => hinv k m i δ hδ)), fun k => ?_⟩
  rw [hc k]
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  funext i
  exact (Classical.choose_spec (RF (c k m i) (fun δ hδ => hinv k m i δ hδ))).symm

variable {F : Type} [Field F] [Algebra ℤ_[l] F] [CharP F l] (red : O →+* F)

theorem red_frob (hl : l ≠ 2) (hred : ∀ z : ℤ_[l], red (algebraMap ℤ_[l] O z) = algebraMap ℤ_[l] F z)
    (hφ : ∀ a, W.φ₀ a = phi l O a) (g : LatHom T.L T'.L) (P : ZMod f → Mx O⟦X⟧ n n) (P' : ZMod f → Mx O⟦X⟧ n' n')
    (A : ZMod f → Mx O⟦X⟧ n' n)
    (hP : ∀ k, W.φD T (b k : W.DD T) = ∑ m, (fun i => inc l O (P i m k) : LetA O f) • (b m : W.DD T))
    (hP' : ∀ k, W.φD T' (b' k : W.DD T') = ∑ m, (fun i => inc l O (P' i m k) : LetA O f) • (b' m : W.DD T'))
    (hA : ∀ k, W.map g (b k : W.DD T) = ∑ m, (fun i => inc l O (A i m k) : LetA O f) • (b' m : W.DD T'))
    (i : ZMod f) :
    (P' i).map (PowerSeries.map red) * ((A (i - 1)).map (PowerSeries.map red)).map (frob0 l) =
      (A i).map (PowerSeries.map red) * (P i).map (PowerSeries.map red) := by
  classical
  have hc := fun j k => coeff_comm (fun k => (b k : W.DD T)) b'
    (W.map g).toAddMonoidHom (W.φD T).toAddMonoidHom (W.φD T').toAddMonoidHom (letφ W.φ₀)
    (fun a x => map_smul_letA W g a x) (fun a x => phiD_smul W T' a x) (fun x => W.map_φ g x)
    (fun m k => (fun i => inc l O (P i m k) : LetA O f)) (fun m k => (fun i => inc l O (P' i m k) : LetA O f))
    (fun m k => (fun i => inc l O (A i m k) : LetA O f)) hP hP' hA j k
  have hred' : ∀ y : O⟦X⟧, (∃ y', phi l O (inc l O y) = inc l O y') ∧
      ∀ y', phi l O (inc l O y) = inc l O y' → PowerSeries.map red y' = frob0 l (PowerSeries.map red y) :=
    frobenius_on_pi0Subst_holds l O F red hl hred
  let Y : Mx O⟦X⟧ n' n := fun m k => Classical.choose (hred' (A (i - 1) m k)).1
  have hY : ∀ m k, phi l O (inc l O (A (i - 1) m k)) = inc l O (Y m k) := fun m k =>
    Classical.choose_spec (hred' (A (i - 1) m k)).1
  have hi : ∀ j k, ∑ m, inc l O (P i m k) * inc l O (A i j m) = ∑ m, inc l O (Y m k) * inc l O (P' i j m) := by
    intro j k
    have e := congrFun (hc j k) i
    rw [Finset.sum_apply, Finset.sum_apply] at e
    refine e.trans (Finset.sum_congr rfl fun m _ => ?_)
    show W.φ₀ (inc l O (A (i - 1) m k)) * inc l O (P' i j m) = _
    rw [hφ, hY m k]
  have hM : P' i * Y = A i * P i := mul_eq_of_inc hl (P i) (P' i) (A i) Y hi
  have hYr : Y.map (PowerSeries.map red) = ((A (i - 1)).map (PowerSeries.map red)).map (frob0 l) := by
    refine Matrix.ext fun m k => ?_
    exact (hred' (A (i - 1) m k)).2 _ (hY m k)
  rw [← hYr, ← Matrix.map_mul, hM, Matrix.map_mul]

omit [Algebra ℤ_[l] F] in

theorem red_gam (hl : l ≠ 2) (γ : W.Gam) (u : ℤ_[l]) (un : O⟦X⟧) (hun : IsUn l O u un)
    (hγ : ∀ a, W.γ₀ γ a = act l O u a) (g : LatHom T.L T'.L) (D : ZMod f → Mx O⟦X⟧ n n)
    (D' : ZMod f → Mx O⟦X⟧ n' n') (A : ZMod f → Mx O⟦X⟧ n' n)
    (hD : ∀ k, W.γD T γ (b k : W.DD T) =
      ∑ m, (fun i => inc l O ((1 + (X : O⟦X⟧) • D i) m k) : LetA O f) • (b m : W.DD T))
    (hD' : ∀ k, W.γD T' γ (b' k : W.DD T') =
      ∑ m, (fun i => inc l O ((1 + (X : O⟦X⟧) • D' i) m k) : LetA O f) • (b' m : W.DD T'))
    (hA : ∀ k, W.map g (b k : W.DD T) = ∑ m, (fun i => inc l O (A i m k) : LetA O f) • (b' m : W.DD T'))
    (i : ZMod f) :
    (1 + (X : F⟦X⟧) • (D' i).map (PowerSeries.map red)) *
        ((A i).map (PowerSeries.map red)).map (gam0 0 (PowerSeries.map red un)) =
      (A i).map (PowerSeries.map red) * (1 + (X : F⟦X⟧) • (D i).map (PowerSeries.map red)) := by
  classical
  have hc := fun j k => coeff_comm (fun k => (b k : W.DD T)) b'
    (W.map g).toAddMonoidHom (W.γD T γ).toAddMonoidHom (W.γD T' γ).toAddMonoidHom (letγ (W.γ₀ γ))
    (fun a x => map_smul_letA W g a x) (fun a x => gamD_smul W T' γ a x) (fun x => W.map_γ g γ x)
    (fun m k => (fun i => inc l O ((1 + (X : O⟦X⟧) • D i) m k) : LetA O f))
    (fun m k => (fun i => inc l O ((1 + (X : O⟦X⟧) • D' i) m k) : LetA O f))
    (fun m k => (fun i => inc l O (A i m k) : LetA O f)) hD hD' hA j k
  have hi : ∀ j k, ∑ m, inc l O ((1 + (X : O⟦X⟧) • D i) m k) * inc l O (A i j m) =
      ∑ m, inc l O ((A i).map (gam0 (l : O) un) m k) * inc l O ((1 + (X : O⟦X⟧) • D' i) j m) := by
    intro j k
    have e := congrFun (hc j k) i
    rw [Finset.sum_apply, Finset.sum_apply] at e
    refine e.trans (Finset.sum_congr rfl fun m _ => ?_)
    show W.γ₀ γ (inc l O (A i m k)) * inc l O ((1 + (X : O⟦X⟧) • D' i) j m) = _
    rw [hγ, gamma_on_pi0Subst_holds l O u un hun]
    rfl
  have hM := mul_eq_of_inc hl (1 + (X : O⟦X⟧) • D i) (1 + (X : O⟦X⟧) • D' i) (A i) ((A i).map (gam0 (l : O) un)) hi
  have hG : ((A i).map (gam0 (l : O) un)).map (PowerSeries.map red) =
      ((A i).map (PowerSeries.map red)).map (gam0 0 (PowerSeries.map red un)) := by
    refine Matrix.ext fun m k => ?_
    simp only [Matrix.map_apply]
    rw [gamma_reduction_holds O F red (l : O) un (A i m k), map_natCast, CharP.cast_eq_zero]
  rw [← hG, ← map_one_add_X_smul red (D' i), ← map_one_add_X_smul red (D i), ← Matrix.map_mul, hM, Matrix.map_mul]

end Local

theorem charP_residueField_of_irreducible {l : ℕ} [Fact l.Prime] (LL : FinExt l) : CharP (ResidueField ↥(OL LL)) l := by
  have hl : l.Prime := Fact.out
  have : Algebra.IsIntegral ℤ_[l] ↥(OL LL) := ⟨fun x => integralClosure.isIntegral x⟩
  rw [CharP.charP_iff_prime_eq_zero hl, ← map_natCast (IsLocalRing.residue ↥(OL LL)), IsLocalRing.residue_eq_zero_iff]
  have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := ℤ_[l]) (IsLocalRing.maximalIdeal ↥(OL LL))
  have heq := IsLocalRing.eq_maximalIdeal hmax
  have hmem : (l : ℤ_[l]) ∈ (IsLocalRing.maximalIdeal ↥(OL LL)).comap (algebraMap ℤ_[l] ↥(OL LL)) := by
    rw [heq, PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _
  simpa using hmem

set_option maxHeartbeats 1000000 in

theorem exists_mapMat_redHom : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (K LL : FinExt l) (hA : CaseA K LL) (T T' : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (n n' : ℕ) (γ : (H.W K 1 LL hA.2.2).Gam) (b : Module.Basis (Fin n) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥((H.W K 1 LL hA.2.2).N T)) (b' : Module.Basis (Fin n') (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥((H.W K 1 LL hA.2.2).N T')) (N : Lat (ZMod (Module.finrank ℚ_[l] ↥(K0 K))) n ↥(OL LL)) (N' : Lat (ZMod (Module.finrank ℚ_[l] ↥(K0 K))) n' ↥(OL LL)) (u : ℤ_[l]) (un : PowerSeries ↥(OL LL)) (g : LatHom T.L T'.L), IsCrys (P.PD K) T.ρ → IsCrys (P.PD K) T'.ρ → IsFrame (H.W K 1 LL hA.2.2) T γ b N → IsFrame (H.W K 1 LL hA.2.2) T' γ b' N' → ((H.W K 1 LL hA.2.2).χΓ γ : ↥(OL LL)) = algebraMap ℤ_[l] ↥(OL LL) u → IsUn l ↥(OL LL) u un → ∃ A : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Mx (PowerSeries ↥(OL LL)) n' n, IsMapMat (H.W K 1 LL hA.2.2) g b b' A ∧ ∀ i, RedHom l ((PowerSeries.map (residue ↥(OL LL))) un) ((N.P i).map (PowerSeries.map (residue ↥(OL LL)))) ((N.D i).map (PowerSeries.map (residue ↥(OL LL)))) ((N'.P i).map (PowerSeries.map (residue ↥(OL LL)))) ((N'.D i).map (PowerSeries.map (residue ↥(OL LL)))) ((A i).map (PowerSeries.map (residue ↥(OL LL)))) ((A (i - 1)).map (PowerSeries.map (residue ↥(OL LL)))) := by
  intro l _ P H K LL hA T T' n n' γ b b' N N' u un g hT hT' hF hF' hχ hun
  have hl : l ≠ 2 := hA.2.1
  have := charP_residueField_of_irreducible LL
  obtain ⟨hφ, -, hγ, -, hRF, -⟩ := GlobalTheory.T.wachRingFacts_unramified_levelOne H K LL hA
  have RF : ∀ a : (↥(OL LL))⟦X⟧, (∀ δ ∈ (H.W K 1 LL hA.2.2).DelF, (H.W K 1 LL hA.2.2).γ₀ δ a = a) →
      ∃ y, inc l ↥(OL LL) y = a := fun a ha => (hRF a).mp ha
  obtain ⟨A, hAm⟩ := exists_mapMat (H.W K 1 LL hA.2.2) b b' RF g hT hT' hF.1 hF'.1
  refine ⟨A, hAm, fun i => ⟨?_, ?_⟩⟩
  · exact red_frob (H.W K 1 LL hA.2.2) b b' (residue ↥(OL LL)) hl (fun z => rfl) hφ g N.P N'.P A
      hF.2.1 hF'.2.1 hAm i
  · exact red_gam (H.W K 1 LL hA.2.2) b b' (residue ↥(OL LL)) hl γ u un hun (hγ γ u hχ) g N.D N'.D A
      hF.2.2.1 hF'.2.2.1 hAm i

end GlobalTheory.WachMap

end
