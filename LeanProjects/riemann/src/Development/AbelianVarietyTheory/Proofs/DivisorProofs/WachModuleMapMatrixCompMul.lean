import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
import Formalism.PieriBlockIdeals.PieriColumnMinors.HeckeLFunctionIdealEulerProduct

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WachPlace

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {f : ℕ}

theorem wachMap_comp_coeff (W : LocWach PD LL O v f) {T T' T'' : LocLat G Qp LL O} {n n' n'' : ℕ}
    (b : Module.Basis (Fin n) (LetA O f) ↥(W.N T)) (b' : Module.Basis (Fin n') (LetA O f) ↥(W.N T'))
    (b'' : Module.Basis (Fin n'') (LetA O f) ↥(W.N T''))
    (g : LatHom T.L T'.L) (g' : LatHom T'.L T''.L) (g'' : LatHom T.L T''.L)
    (a : Fin n → Fin n' → LetA O f) (a' : Fin n' → Fin n'' → LetA O f) (a'' : Fin n → Fin n'' → LetA O f)
    (h1 : ∀ k, W.map g (b k : W.DD T) = ∑ m, a k m • (b' m : W.DD T'))
    (h2 : ∀ k, W.map g' (b' k : W.DD T') = ∑ m, a' k m • (b'' m : W.DD T''))
    (h3 : ∀ k, W.map g'' (b k : W.DD T) = ∑ m, a'' k m • (b'' m : W.DD T''))
    (hc : ∀ x, g''.f x = g'.f (g.f x)) (k : Fin n) (p : Fin n'') :
    a'' k p = ∑ m, a k m * a' m p := by
  have hg : g'' = latComp g' g := by
    cases g''
    simp only [latComp]
    congr 1
    exact LinearMap.ext hc
  have hsm : ∀ {S S' : LocLat G Qp LL O} (u : LatHom S.L S'.L) (c : LetA O f) (x : W.DD S),
      W.map u (c • x) = c • W.map u x := fun u c x => (W.map u).map_smul_of_tower c x
  have key : W.map g'' (b k : W.DD T) = ∑ q, (∑ m, a k m * a' m q) • (b'' q : W.DD T'') := by
    rw [hg, W.map_comp, h1 k, map_sum]
    simp_rw [hsm, h2, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
  have e : ∑ q, a'' k q • b'' q = ∑ q, (∑ m, a k m * a' m q) • b'' q := by
    apply (W.N T'').subtype_injective
    simpa [map_sum] using (h3 k).symm.trans key
  have := congrArg (fun x => b''.repr x p) e
  simpa [Finset.sum_apply, map_sum, Finsupp.smul_apply, b''.repr_self, Finsupp.single_apply] using this

end Gen

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem isMapMat_comp_mul : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (K LL : FinExt l) (hA : CaseA K LL) (T T' T'' : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (n n' n'' : ℕ) (b : Module.Basis (Fin n) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥((H.W K 1 LL hA.2.2).N T)) (b' : Module.Basis (Fin n') (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥((H.W K 1 LL hA.2.2).N T')) (b'' : Module.Basis (Fin n'') (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥((H.W K 1 LL hA.2.2).N T'')) (g : LatHom T.L T'.L) (g' : LatHom T'.L T''.L) (g'' : LatHom T.L T''.L) (A : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Mx (PowerSeries ↥(OL LL)) n' n) (A' : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Mx (PowerSeries ↥(OL LL)) n'' n') (A'' : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Mx (PowerSeries ↥(OL LL)) n'' n), IsMapMat (H.W K 1 LL hA.2.2) g b b' A → IsMapMat (H.W K 1 LL hA.2.2) g' b' b'' A' → IsMapMat (H.W K 1 LL hA.2.2) g'' b b'' A'' → (∀ x, g''.f x = g'.f (g.f x)) → ∀ i, A'' i = A' i * A i := by
  intro l _ P H K LL hA T T' T'' n n' n'' b b' b'' g g' g'' A A' A'' h1 h2 h3 hc i
  obtain ⟨hadd, hmul, hC, -, -, -, -, hinj⟩ := Formalism.CohomologicalDescent.FrobeniusPeriodChange.pi0Subst_laws_hold l ↥(OL LL)
  let incR : (↥(OL LL))⟦X⟧ →+* (↥(OL LL))⟦X⟧ :=
    { toFun := inc l ↥(OL LL)
      map_one' := by simpa using hC 1
      map_mul' := hmul
      map_zero' := by simpa using hC 0
      map_add' := hadd }
  refine Matrix.ext fun p k => hinj hA.2.1 ?_
  have e := congrFun (wachMap_comp_coeff (H.W K 1 LL hA.2.2) b b' b'' g g' g''
    (fun k m i => inc l ↥(OL LL) (A i m k)) (fun k m i => inc l ↥(OL LL) (A' i m k))
    (fun k m i => inc l ↥(OL LL) (A'' i m k)) h1 h2 h3 hc k p) i
  rw [Finset.sum_apply] at e
  rw [Matrix.mul_apply]
  refine e.trans (Eq.trans ?_ (map_sum incR _ _).symm)
  exact Finset.sum_congr rfl fun m _ => (mul_comm _ _).trans (hmul _ _).symm

end GlobalTheory.WachPlace
