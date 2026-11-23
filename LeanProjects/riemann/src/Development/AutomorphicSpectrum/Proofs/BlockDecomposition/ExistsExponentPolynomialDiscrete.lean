import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UfamConst
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.CommonEigenvectors.KillPoly
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.CasimirOnParabolicInduction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieOneLMemZalg
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsStableBdSub
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductSubsetSumVanishesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorSumAnnihilatorStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutingHeckeCapelliOperatorsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasDerivAtTorusTranslateStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExponentialPolynomialSolutionSpaceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRecurrencePolynomialStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusElementLeviEmbeddingStatement
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

noncomputable section

namespace GlobalTheory.CompanionTheory.KillU

def polyOf {R : Type} [CommRing R] (n : ℕ) (c : ℕ → R) : R[X] := ∑ k ∈ Finset.range (n + 1), C (c k) * X ^ k

theorem polyOf_coeff {R : Type} [CommRing R] (n : ℕ) (c : ℕ → R) {j : ℕ} (hj : j ≤ n) : (polyOf n c).coeff j = c j := by
  classical
  simp only [polyOf, finset_sum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Nat.lt_succ_iff, hj]

theorem polyOf_natDegree_le {R : Type} [CommRing R] (n : ℕ) (c : ℕ → R) : (polyOf n c).natDegree ≤ n := by
  refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
  exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))

theorem polyOf_monic {R : Type} [CommRing R] (n : ℕ) (c : ℕ → R) (h : c n = 1) : (polyOf n c).Monic :=
  monic_of_natDegree_le_of_coeff_eq_one n (polyOf_natDegree_le n c) (by rw [polyOf_coeff n c le_rfl, h])

theorem polyOf_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (n : ℕ) (c : ℕ → R) :
    (polyOf n c).map f = polyOf n (fun k => f (c k)) := by
  simp [polyOf, Polynomial.map_sum]

theorem alg_kill {ι : Type} [Fintype ι] (r s : ℕ) (hr : 0 < r) (M : ι → Multiset ℂ) (l' : Multiset ℂ)
    (hl' : ∀ (R : Type) [CommRing R] [Algebra ℂ R] (h : ι → R),
      (∀ τ ∈ (Finset.univ : Finset ι), ((((M τ).powersetCard r).map Multiset.sum).map fun c => h τ - algebraMap ℂ R c).prod = 0) →
      (l'.map fun c => ∑ τ ∈ (Finset.univ : Finset ι), h τ - algebraMap ℂ R c).prod = 0)
    (R : Type) [CommRing R] [Algebra ℂ R] (I : Ideal R) (c d : ι → ℕ → R) (hc : ∀ τ, c τ r = 1) (hd : ∀ τ, d τ s = 1)
    (hI : ∀ τ j, (polyOf r (c τ) * polyOf s (d τ) - ((M τ).map fun x => X + C (algebraMap ℂ R x)).prod).coeff j ∈ I) :
    (l'.map fun z => ∑ τ, c τ (r - 1) - algebraMap ℂ R z).prod ∈ I := by
  by_cases hq : Nontrivial (R ⧸ I)
  swap
  · have : Subsingleton (R ⧸ I) := not_nontrivial_iff_subsingleton.1 hq
    exact Ideal.Quotient.eq_zero_iff_mem.1 (Subsingleton.elim _ _)
  let π : R →+* R ⧸ I := Ideal.Quotient.mk I
  have hπ : ∀ x : ℂ, π (algebraMap ℂ R x) = algebraMap ℂ (R ⧸ I) x := fun _ => rfl
  have key := hl' (R ⧸ I) (fun τ => π (c τ (r - 1))) fun τ _ => by
    have hA : (polyOf r fun k => π (c τ k)).Monic := polyOf_monic r _ (by simp [hc])
    have hB : (polyOf s fun k => π (d τ k)).Monic := polyOf_monic s _ (by simp [hd])
    have hdeg : (polyOf r fun k => π (c τ k)).natDegree = r :=
      le_antisymm (polyOf_natDegree_le r _) (le_natDegree_of_ne_zero (by
        rw [polyOf_coeff r _ le_rfl]; simp [hc]))
    have hAB : (polyOf r fun k => π (c τ k)) * (polyOf s fun k => π (d τ k)) =
        ((M τ).map fun x => X + C (algebraMap ℂ (R ⧸ I) x)).prod := by
      have h0 : (polyOf r (c τ) * polyOf s (d τ) - ((M τ).map fun x => X + C (algebraMap ℂ R x)).prod).map π = 0 := by
        ext j
        rw [coeff_map, coeff_zero]
        exact Ideal.Quotient.eq_zero_iff_mem.2 (hI τ j)
      rw [Polynomial.map_sub, Polynomial.map_mul, polyOf_map, polyOf_map, sub_eq_zero] at h0
      rw [h0, Polynomial.map_multiset_prod, Multiset.map_map]
      congr 1
      refine Multiset.map_congr rfl fun x _ => ?_
      simp [hπ]
    have := GlobalTheory.T.product_subset_sum_vanishes (R ⧸ I) r (M τ) _ _ hr hA hB hdeg hAB
    rw [polyOf_coeff r _ (Nat.sub_le r 1)] at this
    rw [Multiset.map_map]
    exact this
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change π _ = 0
  rw [map_multiset_prod, Multiset.map_map, ← key]
  congr 1
  refine Multiset.map_congr rfl fun z _ => ?_
  simp [hπ, map_sum]

theorem polyOf_eval {R : Type} [CommRing R] (n : ℕ) (c : ℕ → R) (x : R) :
    (polyOf n c).eval x = ∑ k ∈ Finset.range (n + 1), c k * x ^ k := by
  simp [polyOf, eval_finset_sum]

theorem coeff_zero_of_eval {R : Type} [CommRing R] [Algebra ℂ R] (P : R[X]) (Λ : R →ₗ[ℂ] ℂ)
    (h : ∀ u : ℂ, Λ (P.eval (algebraMap ℂ R u)) = 0) (j : ℕ) : Λ (P.coeff j) = 0 := by
  have hQ : polyOf P.natDegree (fun k => Λ (P.coeff k)) = 0 := Polynomial.funext fun u => by
    rw [polyOf_eval, eval_zero, ← h u, eval_eq_sum_range, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← map_pow, ← Algebra.commutes, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  by_cases hj : j ≤ P.natDegree
  · have := congrArg (fun q : ℂ[X] => q.coeff j) hQ
    simpa [polyOf_coeff _ _ hj] using this
  · rw [coeff_eq_zero_of_natDegree_lt (not_le.1 hj), map_zero]

theorem levi_kill : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (M : (E →+* ℂ) → Multiset ℂ), 0 < r → 0 < s →
  (∀ τ, Multiset.card (M τ) = r + s) →
  ∃ l : List ℂ, l.length = Nat.choose (r + s) r ^ Fintype.card (E →+* ℂ) ∧
    ∀ F : Sm E (r + s), (∀ (v : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip v * g) = F.1 g) →
      (∀ (τ : E →+* ℂ) (u : ℂ), cap (a := r + s) τ u F = ((M τ).map (u + ·)).prod • F) →
      ∀ p : GA E r × GA E s,
        ((l.map fun c => (∑ τ : E →+* ℂ, ∑ i : Fin r, Eop (a := r + s) τ (Fin.castAdd s i) (Fin.castAdd s i)) - c • (1 : Module.End ℂ (Sm E (r + s)))).prod F).1
          (GlobalTheory.CompanionTheory.CTFin.lev (Ad E) r s p) = 0 := by
  intro E _ _ _ r s M hr hs hcard
  classical
  obtain ⟨S, a, b, t, hcomm, hcapc, hleft, haS, hbS, ha1, hb1, htr, hA, hB⟩ := GlobalTheory.T.commuting_hecke_capelli_operators E r s hr hs
  obtain ⟨l', hcard', hl'⟩ := GlobalTheory.T.tensor_sum_annihilator (Finset.univ : Finset (E →+* ℂ)) (fun τ => ((M τ).powersetCard r).map Multiset.sum)
  refine ⟨l'.toList.map (· - ∑ τ, t τ), ?_, fun F hFN hFc p => ?_⟩
  · rw [List.length_map, Multiset.length_toList, hcard']
    simp [hcard, Multiset.card_powersetCard]
  letI Rr : CommRing S := { S.toRing with mul_comm := fun x y => Subtype.ext (hcomm x x.2 y y.2) }
  let Λ : S → (GA E r × GA E s) → (S →ₗ[ℂ] ℂ) := fun v p =>
    { toFun := fun w => ((w.1 * v.1) F).1 (GlobalTheory.CompanionTheory.CTFin.lev (Ad E) r s p)
      map_add' := fun x y => by
        change (((x.1 + y.1) * v.1) F).1 _ = _
        rw [add_mul]
        rfl
      map_smul' := fun c x => by
        change (((c • x.1) * v.1) F).1 _ = _
        rw [smul_mul_assoc]
        rfl }
  have hΛ : ∀ (x w v : S) q, Λ v q (x * w) = Λ (x * v) q w := fun x w v q => by
    change ((x.1 * w.1 * v.1) F).1 _ = ((w.1 * (x.1 * v.1)) F).1 _
    rw [hcomm x.1 x.2 w.1 w.2, mul_assoc]
  let I : Ideal S :=
    { carrier := {w | ∀ v q, Λ v q w = 0}
      add_mem' := fun {x y} hx hy v q => by rw [map_add, hx, hy, add_zero]
      zero_mem' := fun v q => map_zero _
      smul_mem' := fun x w hw v q => by
        rw [smul_eq_mul, hΛ]
        exact hw _ _ }
  let ca : (E →+* ℂ) → ℕ → S := fun τ k => ⟨a τ k, haS τ k⟩
  let cb : (E →+* ℂ) → ℕ → S := fun τ k => ⟨b τ k, hbS τ k⟩
  have hval : ∀ (u : ℂ) (n : ℕ) (c : ℕ → S) (e : ℕ → Module.End ℂ (Sm E (r + s))), (∀ k, (c k).1 = e k) →
      ((polyOf n c).eval (algebraMap ℂ S u)).1 = ∑ k ∈ Finset.range (n + 1), u ^ k • e k := fun u n c e he => by
    rw [polyOf_eval]
    change S.val _ = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, map_pow, AlgHom.commutes, ← map_pow, ← Algebra.commutes, ← Algebra.smul_def]
    exact congrArg _ (he k)
  have hI : ∀ τ j, (polyOf r (ca τ) * polyOf s (cb τ) - ((M τ).map fun x => X + C (algebraMap ℂ S x)).prod).coeff j ∈ I := by
    intro τ j v q
    refine coeff_zero_of_eval _ (Λ v q) (fun u => ?_) j
    have eA : ((polyOf r (ca τ)).eval (algebraMap ℂ S u)).1 = GlobalTheory.CompanionTheory.CTFin.capR r s τ (u - (s : ℂ) / 2) := by
      rw [hval u r _ (a τ) fun _ => rfl, hA]
    have eB : ((polyOf s (cb τ)).eval (algebraMap ℂ S u)).1 = GlobalTheory.CompanionTheory.CTFin.capS r s τ (u + (r : ℂ) / 2) := by
      rw [hval u s _ (b τ) fun _ => rfl, hB]
    have eP : (((M τ).map fun x => X + C (algebraMap ℂ S x)).prod).eval (algebraMap ℂ S u) =
        algebraMap ℂ S ((M τ).map (u + ·)).prod := by
      rw [eval_multiset_prod, Multiset.map_map, map_multiset_prod, Multiset.map_map]
      congr 1
      refine Multiset.map_congr rfl fun x _ => ?_
      simp
    rw [eval_sub, eval_mul, eP, map_sub, sub_eq_zero]
    have hG := hleft v.1 v.2 F hFN
    have h1 := GlobalTheory.CompanionTheory.CTFin.CapFactor.cap_levi E r s τ u (v.1 F) hG q
    have h2 : cap (a := r + s) τ u (v.1 F) = ((M τ).map (u + ·)).prod • v.1 F := by
      rw [← Module.End.mul_apply, (hcapc v.1 v.2 τ u).eq, Module.End.mul_apply, hFc, map_smul]
    change (((_ : S).1 * (_ : S).1 * v.1) F).1 _ = ((algebraMap ℂ (Module.End ℂ (Sm E (r + s))) _ * v.1) F).1 _
    rw [eA, eB, (GlobalTheory.CompanionTheory.CTFin.CapFactor.capR_commute_capS r s τ _ _).eq, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    change (GlobalTheory.CompanionTheory.CTFin.capS r s τ _ (GlobalTheory.CompanionTheory.CTFin.capR r s τ _ (v.1 F))).1 _ = (((M τ).map (u + ·)).prod • v.1 F).1 _
    rw [← h2]
    exact h1.symm
  have hmem := alg_kill r s hr M l' hl' S I ca cb (fun τ => Subtype.ext (ha1 τ)) (fun τ => Subtype.ext (hb1 τ)) hI
  have hw : (l'.map fun z => ∑ τ, ca τ (r - 1) - algebraMap ℂ S z).prod =
      (l'.toList.map fun z => ∑ τ, ca τ (r - 1) - algebraMap ℂ S z).prod := by
    conv_lhs => rw [← Multiset.coe_toList l']
    rw [Multiset.map_coe, Multiset.prod_coe]
  have e : ∀ z, S.val (∑ τ, ca τ (r - 1) - algebraMap ℂ S z) =
      (∑ τ : E →+* ℂ, ∑ i : Fin r, Eop (a := r + s) τ (Fin.castAdd s i) (Fin.castAdd s i)) -
        (z - ∑ τ, t τ) • (1 : Module.End ℂ (Sm E (r + s))) := fun z => by
    rw [map_sub, map_sum, AlgHom.commutes]
    have h3 : ∀ τ, S.val (ca τ (r - 1)) = a τ (r - 1) := fun _ => rfl
    simp only [h3, htr, Finset.sum_add_distrib, ← Finset.sum_smul, sub_smul, Algebra.algebraMap_eq_smul_one]
    abel
  have h4 := hmem 1 p
  rw [hw] at h4
  change (((S.val _) * 1) F).1 _ = 0 at h4
  rw [mul_one, map_list_prod, List.map_map] at h4
  rw [List.map_map]
  refine Eq.trans (congrArg (fun L' : List (Module.End ℂ (Sm E (r + s))) => (L'.prod F).1 (GlobalTheory.CompanionTheory.CTFin.lev (Ad E) r s p))
    (List.map_congr_left fun z _ => ?_)) h4
  exact (e z).symm

section Helpers
open GlobalTheory.CompanionTheory.CTFin PositivityTheory.Affgl GlobalTheory.PRep GlobalTheory.CuspRep.LocEx PositivityTheory.Rg.Rs.JFinTr

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem exists_iw (r s : ℕ) (x : GA E (r + s)) : ∃ (v : BlockIx (r + s) r → Ad E) (p : GA E r × GA E s)
    (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)),
    x = unip v * lev (Ad E) r s p * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g) := by
  have h : ∑ i, (![r, s] : Fin 2 → ℕ) i = r + s := CapFactor.two_sum _
  obtain ⟨v, hv, m, k, g, rfl⟩ := GlobalTheory.SpehInfChar.exists_iwasawa E (![r, s]) h x
  obtain ⟨xv, rfl⟩ := CapFactor.exists_unip_of_mem ![r, s] h hv
  refine ⟨xv, (m 0, m 1), k, g, ?_⟩
  have e := CapFactor.lev_eq_leviEmb (![r, s]) h (m 0, m 1)
  rw [PositivityTheory.Rg.Rs.PInfInd2A.levPair_eta] at e
  exact congrArg (fun z : GA E (r + s) => (show GA E (r + s) from unip xv) * z *
    (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g)) e.symm

theorem exists_ct (r s : ℕ) (hr : 0 < r) (hs : 0 < s) (φ : Sm E (r + s)) (hφ : IsAutForm φ) (c : (E →+* ℂ) → ℂ → ℂ)
    (hc : ∀ τ u, cap (a := r + s) τ u φ = c τ u • φ) :
    ∃ G : Sm E (r + s), (∀ (v : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), G.1 (unip v * g) = G.1 g) ∧
      (∀ τ u, cap (a := r + s) τ u G = c τ u • G) ∧ ∀ g, G.1 g = An.ctn r φ.1 g := by
  letI : MeasurableSpace (BlockIx (r + s) r → Ad E) := borel _
  haveI : BorelSpace (BlockIx (r + s) r → Ad E) := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, h𝓕, e⟩ := ((dict_holds E (r + s)).2.2.2 φ hφ r hr (by omega)).1
  haveI : FiniteDimensional ℂ (orbSpan φ) := hφ.kfin
  haveI := hφ.zfin
  let ρ := sub (cptRep E (r + s)) (orbSpan φ) (orbSpan_stable φ)
  let J : Set (Module.End ℂ (Sm E (r + s))) := {z | z ∈ Zalg E (r + s) ∧ z φ = 0}
  have hJ : Cofin J := cofin_ann φ
  have hφg : φ ∈ genSpace (stabFin φ) ρ J :=
    ⟨hφ, fun k hk => hk, fun g => GlobalTheory.Published.AutFinGL.type_of_map ρ (orbSpan φ).subtype (fun _ _ => rfl)
      ⟨φ, Submodule.subset_span ⟨1, by simp⟩⟩ g, fun z hz => hz.2⟩
  obtain ⟨G, hG, hGe⟩ := exists_mem_goodCT (stabFin φ) ρ J hJ φ hφg μ 𝓕 hμ h𝓕
  obtain ⟨a1, -, -, -, -, a6⟩ := hG
  refine ⟨G, a1, fun τ u => ?_, fun g => ?_⟩
  · have hz : cap (a := r + s) τ u - c τ u • (1 : Module.End ℂ (Sm E (r + s))) ∈ J :=
      ⟨sub_mem (cap_mem_Zalg τ u) (Subalgebra.smul_mem _ (one_mem _) _), by simp [hc]⟩
    have := a6 _ hz
    simpa [sub_eq_zero] using this
  · rw [hGe]
    exact (congrFun e g).symm

theorem orbit_mem (r s : ℕ) (hr : 0 < r) (hs : 0 < s) (φ : Sm E (r + s)) (hφ : IsAutForm φ) (M : (E →+* ℂ) → Multiset ℂ)
    (hc : ∀ τ u, cap (a := r + s) τ u φ = ((M τ).map (u + ·)).prod • φ) (l : List ℂ)
    (hk : ∀ F : Sm E (r + s), (∀ (v : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip v * g) = F.1 g) →
      (∀ (τ : E →+* ℂ) (u : ℂ), cap (a := r + s) τ u F = ((M τ).map (u + ·)).prod • F) →
      ∀ p : GA E r × GA E s,
        ((l.map fun c => (∑ τ : E →+* ℂ, ∑ i : Fin r, Eop (a := r + s) τ (Fin.castAdd s i) (Fin.castAdd s i)) - c • (1 : Module.End ℂ (Sm E (r + s)))).prod F).1
          (lev (Ad E) r s p) = 0)
    (S : Submodule ℂ (ℝ → ℂ))
    (hS : ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (D : Module.End ℂ X) (ev : X →ₗ[ℂ] (ℝ → ℂ)),
      (∀ x t, HasDerivAt (ev x) (ev (D x) t) t) → ∀ x, ev ((l.map fun c => D - c • (1 : Module.End ℂ X)).prod x) = 0 → ev x ∈ S)
    (g : GA E (r + s)) : (fun t => An.ctn r φ.1 (aT E (r + s) r t * g)) ∈ S := by
  obtain ⟨G, hN, hcap, hG⟩ := exists_ct r s hr hs φ hφ (fun τ u => ((M τ).map (u + ·)).prod) hc
  obtain ⟨v, p, k, f, rfl⟩ := exists_iw r s g
  set y := infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) f with hy
  set F := rt E (r + s) y G with hF
  have hFN : ∀ (v : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip v * g) = F.1 g := fun v g => by
    simp only [hF, rt_apply, mul_assoc]
    exact hN v _
  have hcomm : ∀ (τ : E →+* ℂ) (u : ℂ), Commute (cap (a := r + s) τ u) (rt E (r + s) y) := fun τ u => by
    rw [hy, map_mul]
    exact (GlobalTheory.CapAdInv.cap_commute_rt_infGL E _ τ u _).mul_right (commute_cap_finRep τ u f)
  have hFc : ∀ (τ : E →+* ℂ) (u : ℂ), cap (a := r + s) τ u F = ((M τ).map (u + ·)).prod • F := fun τ u => by
    rw [hF, ← Module.End.mul_apply, (hcomm τ u).eq, Module.End.mul_apply, hcap, map_smul]
  let ev : Sm E (r + s) →ₗ[ℂ] (ℝ → ℂ) :=
    { toFun := fun F t => F.1 (lev (Ad E) r s p * aT E (r + s) r t)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hmem := hS (Sm E (r + s)) (∑ τ : E →+* ℂ, ∑ i : Fin r, Eop (a := r + s) τ (Fin.castAdd s i) (Fin.castAdd s i)) ev
    (fun x t => GlobalTheory.T.hasDerivAt_torus_translate E r s x _ t) F (funext fun t => by
      change (_ : Sm E (r + s)).1 (lev (Ad E) r s p * aT E (r + s) r t) = 0
      rw [GlobalTheory.T.torus_element_levi_embedding E r s t, ← map_mul]
      exact hk F hFN hFc _)
  convert hmem using 1
  funext t
  obtain ⟨y', hy'⟩ := diag_mul_unip (aT E (r + s) r t) _ _ (aT_val (r + s) r t) (aT_inv_val (r + s) r t) v
  change _ = G.1 (lev (Ad E) r s p * aT E (r + s) r t * y)
  have e1 : aT E (r + s) r t * (unip v * lev (Ad E) r s p * y) = unip y' * (lev (Ad E) r s p * aT E (r + s) r t * y) := by
    calc aT E (r + s) r t * (unip v * lev (Ad E) r s p * y)
        = (aT E (r + s) r t * unip v) * lev (Ad E) r s p * y := by simp only [mul_assoc]
      _ = unip y' * aT E (r + s) r t * lev (Ad E) r s p * y := by rw [hy']
      _ = unip y' * (aT E (r + s) r t * lev (Ad E) r s p) * y := by simp only [mul_assoc]
      _ = unip y' * (lev (Ad E) r s p * aT E (r + s) r t * y) := by rw [aT_comm_lev]; simp only [mul_assoc]
  rw [← hG, e1, hN]

end Helpers

theorem killU : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N r : ℕ), 0 < r → r < N → ∃ D : ℕ, ∀ V : Submodule ℂ (Sm E N), IsDiscrete V →
  (∀ τ : E →+* ℂ, ∃ m, HasInfCharGL V τ m) → ∀ φ ∈ V, ∃ p : ℂ[X], p.Monic ∧ p.natDegree ≤ D ∧ An.Kill r φ.1 p ∧
    ∀ z, p.IsRoot z → ∃ c ∈ Exp r φ.1, z = Complex.exp c := by
  intro E _ _ _ N r hr hrN
  obtain ⟨s, rfl⟩ : ∃ s, N = r + s := ⟨N - r, by omega⟩
  have hs : 0 < s := by omega
  refine ⟨Nat.choose (r + s) r ^ Fintype.card (E →+* ℂ), fun V hV hinf φ hφ => ?_⟩
  choose M hM using hinf
  obtain ⟨l, hl, hk⟩ := levi_kill E r s M hr hs fun τ => (hM τ).1
  obtain ⟨S, hfin, hrank, hS⟩ := GlobalTheory.T.exponential_polynomial_solution_space l
  have haut := hV.aut φ hφ
  have hc : ∀ τ u, cap (a := r + s) τ u φ = ((M τ).map (u + ·)).prod • φ := fun τ u => (hM τ).2 u φ hφ
  have horb := orbit_mem r s hr hs φ haut M hc l hk S hS
  have hcont : ∀ g, Continuous fun t => An.ctn r φ.1 (aT E (r + s) r t * g) := by
    obtain ⟨G, -, -, hG⟩ := exists_ct r s hr hs φ haut (fun τ u => ((M τ).map (u + ·)).prod) hc
    intro g
    simp only [← hG]
    exact PDich.continuous_aT G r g
  obtain ⟨p, hp, hdeg, hkill, hroot⟩ := GlobalTheory.T.exists_recurrence_polynomial (GA E (r + s)) (aT E (r + s) r) (An.ctn r φ.1) S
    (fun u v => PExpFin.aT_add r u v) hcont hfin horb
  have hdict := dict_holds E (r + s)
  refine ⟨p, hp, hdeg.trans (hrank.trans hl.le), fun g => ?_, fun z hz => ?_⟩
  · have := hkill g
    simpa only [hdict.1] using this
  · obtain ⟨c, rfl, F, hF, hF0, hFe⟩ := hroot z hz
    exact ⟨c, ⟨_, (hdict.2.2.2 φ haut r hr (by omega)).1, F, hF, hF0, hFe⟩, rfl⟩

end GlobalTheory.CompanionTheory.KillU

end
