import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanDetSetIffAdelicLatticeValuationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNumeratorIdealOfAntiInvariantDivisorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelicCharacterEqProdUnramifiedValueZpowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceIdempotentComponentsConjValuationStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqProdLocalComponentsApproximating
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdentityClassLatticeEqSelfDualFrameLattice
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NotIsOfFinOrderUnitQuot

namespace GlobalTheory.ClassScalarValue

section Local

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR Formalism.IndefR.Links
  Formalism.L2.JoinChr Formalism.L2.Host Formalism.L2.Pj GlobalTheory.IdemSupport
open scoped TensorProduct Matrix nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem cP_cP (P : HeightOneSpectrum (𝓞 D.host.E)) : cP (cP P) = P :=
  HeightOneSpectrum.ext (Ideal.ext fun x => by rw [mem_cP, mem_cP, cO_cO])

theorem above_eq {P : HeightOneSpectrum (𝓞 D.host.E)} [DecidableEq (HeightOneSpectrum (𝓞 D.host.E))] :
    aboveF (L := D.host.E) D.host.F (P.under (𝓞 D.host.F)) = {P, cP P} := by
  ext Q
  rw [aboveF, Set.Finite.mem_toFinset, Finset.mem_insert, Finset.mem_singleton]
  exact ⟨eq_or_eq_cP, by rintro (rfl | rfl); exacts [rfl, under_cP P]⟩

set_option maxHeartbeats 1000000 in

theorem val_mul_val (hv : ∀ (k : D.host.E) (Q : HeightOneSpectrum (𝓞 D.host.E)),
      (cP Q).valuation D.host.E (star k) = Q.valuation D.host.E k)
    (χ : HChar D.host.E) {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : cP P ≠ P)
    (h : ∀ k, χ.resFin (P.under (𝓞 D.host.F)) k = 1) (h1 : χ.UnrAt P) (h2 : χ.UnrAt (cP P)) :
    χ.val P * χ.val (cP P) = 1 := by
  classical
  obtain ⟨π, hπ, hπ'⟩ : ∃ π : 𝓞 D.host.E, P.intValuation π = WithZero.exp (-1 : ℤ) ∧ π ∉ (cP P).asIdeal := by
    obtain ⟨π, hπ⟩ := P.intValuation_exists_uniformizer
    by_cases hm : π ∈ (cP P).asIdeal
    · have hn : ¬ P.asIdeal ≤ (cP P).asIdeal := fun hle => hP (eq_of_le hle).symm
      obtain ⟨b, hb, hb'⟩ := Set.not_subset.1 hn
      have hbb : P.intValuation (b ^ 2) < P.intValuation π := by
        have := (P.intValuation_le_pow_iff_mem (b ^ 2) 2).2 (Ideal.pow_mem_pow hb 2)
        refine this.trans_lt ?_
        rw [hπ, WithZero.exp_lt_exp]; norm_num
      refine ⟨π + b ^ 2, (Valuation.map_add_eq_of_lt_left _ hbb).trans hπ, fun hs => hb' ?_⟩
      exact (cP P).isPrime.mem_of_pow_mem 2 ((Ideal.add_mem_iff_right _ hm).1 hs)
    · exact ⟨π, hπ, hm⟩
  have a1 : P.valuation D.host.E (π : D.host.E) = WithZero.exp (-1 : ℤ) :=
    (P.valuation_of_algebraMap (K := D.host.E) π).trans hπ
  have a2 : (cP P).valuation D.host.E (π : D.host.E) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := D.host.E) (cP P)).2 hπ'
  have a3 : P.valuation D.host.E (star (π : D.host.E)) = 1 := by
    rw [← a2, ← hv _ (cP P), cP_cP]
  obtain ⟨t, ht⟩ := (D.sp.cm.fixed ((π : D.host.E) * star (π : D.host.E))).1 (by rw [star_mul, star_star])
  have b1 : P.valuation D.host.E (algebraMap D.host.F D.host.E t) = WithZero.exp (-1 : ℤ) := by
    rw [ht, map_mul, a1, a3, mul_one]
  have b2 : (cP P).valuation D.host.E (algebraMap D.host.F D.host.E t) = WithZero.exp (-1 : ℤ) := by
    rw [ht, map_mul, a2, hv, a1, one_mul]
  have t0 : t ≠ 0 := by
    rintro rfl
    rw [map_zero, map_zero] at b1
    exact WithZero.exp_ne_zero b1.symm
  have := h (Units.mk0 t t0)
  rw [HChar.resFin_apply, above_eq, Finset.prod_pair hP.symm] at this
  have key : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), χ.UnrAt Q → ∀ k : D.host.Eˣ,
      Q.valuation D.host.E (k : D.host.E) = WithZero.exp (-1 : ℤ) → χ.locK Q k = χ.val Q := fun Q hQ k hk =>
    χ.val_eq hQ (atFin Q k) ((GlobalTheory.CharLocProd.val_algebraMap Q (k : D.host.E)).trans hk)
  rwa [key P h1 _ b1, key _ h2 _ b2] at this

theorem mem_latHat_std {n : ℕ} (z : Fin n → Af D.host.F ⊗[D.host.F] D.host.E) :
    z ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (stdLat D.host.E n : Set (Fin n → D.host.E)) ↔ ∀ i, z i ∈ intAE D := by
  classical
  constructor
  · intro hz i
    induction hz using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      obtain ⟨o, ho⟩ := Submodule.mem_one.1 (hx i trivial)
      exact AddSubgroup.subset_closure ⟨a, ha, o, congrArg (fun w => a ⊗ₜ[D.host.F] w) ho.symm⟩
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | neg y _ hy => exact neg_mem hy
  · intro hz
    rw [← Finset.univ_sum_single z]
    refine sum_mem fun i _ => ?_
    have := hz i
    generalize z i = w at this
    induction this using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨a, ha, Pi.single i (x : D.host.E), fun j _ => ?_, funext fun j => ?_⟩
      · by_cases hj : j = i
        · subst hj; rw [Pi.single_eq_same]; exact Submodule.mem_one.2 ⟨x, rfl⟩
        · rw [Pi.single_eq_of_ne hj]; exact zero_mem _
      · by_cases hj : j = i
        · subst hj; rw [Pi.single_eq_same, Pi.single_eq_same]
        · rw [Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj, TensorProduct.tmul_zero]
    | zero => rw [Pi.single_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [Pi.single_add]; exact add_mem hy hz
    | neg y _ hy => rw [Pi.single_neg]; exact neg_mem hy

theorem mem_hLat (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (h1 : ∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E _ x)
    (h2 : ∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1)
    (V : HSp D) (hL : Bridge.hLat V 1 = stdLat D.host.E V.rank) (h : Bridge.Gf V) (x : Fin V.rank → D.host.E) :
    x ∈ Bridge.hLat V h ↔ ∀ i Q, Valued.v ((((Matrix.GeneralLinearGroup.map ι.toRingHom h.1)⁻¹).1.mulVec
      (fun j => algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) (x j)) i) Q) ≤ 1 := by
  let g := Matrix.GeneralLinearGroup.map ι.toRingHom h.1
  have key : ∀ x : Fin V.rank → D.host.E, ((h⁻¹ : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)).1.mulVec
      (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] x i) ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (Formalism.MainNotions.StandardLattice.L0c D V) ↔
      ∀ i Q, Valued.v (((g⁻¹).1.mulVec
      (fun j => algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) (x j)) i) Q) ≤ 1 := by
    intro x
    rw [← GlobalTheory.Equiv.StdSpace.identityClassLattice_eq_selfDualFrameLattice, hL, mem_latHat_std]
    refine forall_congr' fun i => (h2 _).trans ?_
    have e := RingHom.map_mulVec ι.toRingHom (h.1⁻¹).1 (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] x i) i
    have e2 : (ι.toRingHom ∘ fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] x i) =
      fun j => algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) (x j) := funext fun j => h1 _
    rw [e2] at e
    exact iff_of_eq (congrArg (fun w : FiniteAdeleRing (𝓞 D.host.E) D.host.E => ∀ Q, Valued.v (w Q) ≤ 1) e)
  refine ⟨fun hx => ?_, fun hx => Submodule.subset_span ((key x).2 hx)⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact (key x).1 hx
  | zero =>
    intro i Q
    simp only [Pi.zero_apply, map_zero]
    rw [show (fun _ : Fin V.rank => (0 : FiniteAdeleRing (𝓞 D.host.E) D.host.E)) = 0 from rfl, Matrix.mulVec_zero]
    exact (congrArg _ (GlobalTheory.PlaceIdem.zero_ap Q)).trans_le (by simp)
  | add x y _ _ hx hy =>
    intro i Q
    simp only [Pi.add_apply, map_add]
    rw [← Pi.add_def, Matrix.mulVec_add]
    exact Valuation.map_add_le _ (hx i Q) (hy i Q)
  | smul a x _ hx =>
    intro i Q
    have e : (fun j => algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) ((a • x) j)) =
        algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) a •
          fun j => algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) (x j) :=
      funext fun j => map_mul _ (a : D.host.E) (x j)
    rw [e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, GlobalTheory.PlaceIdem.mul_ap, map_mul]
    exact mul_le_one' ((GlobalTheory.CharLocProd.val_algebraMap Q (a : D.host.E)).trans_le (Q.valuation_le_one a)) (hx i Q)

theorem onId_eq (χ : HChar D.host.E) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
    (δ : HeightOneSpectrum (𝓞 D.host.E) → ℤ) (hI : ∀ Q, FractionalIdeal.count D.host.E Q I = max (δ Q) 0)
    (P : Finset (HeightOneSpectrum (𝓞 D.host.E))) (hP : ∀ Q ∈ P, cP Q ∉ P) (h0 : ∀ Q, Q ∉ P → cP Q ∉ P → δ Q = 0)
    (hδ : ∀ Q, δ (cP Q) = -δ Q) (hv : ∀ Q ∈ P, χ.val Q * χ.val (cP Q) = 1) :
    χ.onId I = ∏ Q ∈ P, χ.val Q ^ δ Q := by
  classical
  have hinj : Function.Injective (cP (D := D)) := Function.Involutive.injective cP_cP
  unfold HChar.onId
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := P ∪ P.image cP), Finset.prod_union,
    Finset.prod_image fun a _ b _ h => hinj h, ← Finset.prod_mul_distrib]
  · refine Finset.prod_congr rfl fun Q hQ => ?_
    rw [hI, hI, hδ, ← inv_eq_of_mul_eq_one_right (hv Q hQ), inv_zpow', ← zpow_add]
    congr 1
    omega
  · refine Finset.disjoint_left.2 fun Q h1 h2 => ?_
    obtain ⟨Q', h3, rfl⟩ := Finset.mem_image.1 h2
    exact hP Q' h3 h1
  · intro Q hQ
    by_contra hn
    rw [Finset.mem_coe, Finset.mem_union, not_or] at hn
    refine hQ ?_
    have := h0 Q hn.1 fun h => hn.2 (Finset.mem_image.2 ⟨_, h, cP_cP Q⟩)
    simp only [hI, this, max_self, zpow_zero]

theorem det_supp {R K : Type} [CommRing R] [CommRing K] {n : ℕ} (f : R →+* K) {u : R} {M : Matrix (Fin n) (Fin n) R}
    (h : ∀ i j, u * (M - 1) i j = (M - 1) i j) (hu : f u = 0) : f M.det = 1 := by
  have : f.mapMatrix (M - 1) = 0 := by
    ext i j
    change f ((M - 1) i j) = 0
    rw [← h, map_mul, hu, zero_mul]
  rw [map_sub, map_one, sub_eq_zero] at this
  rw [RingHom.map_det, this, Matrix.det_one]

theorem det_unitary (V : HSp D) (hg : V.gram = 1) (h : GA D V) :
    cA D (Formalism.L2.Theta.mt V h).det * (Formalism.L2.Theta.mt V h).det = 1 := by
  have h1 : Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt V h) * V.gram.map (incA D) * Formalism.L2.Theta.mt V h =
      V.gram.map (incA D) := (show HR (AF D.host.F) D.sp.cm.sig V.gram from h).2
  rw [hg, Matrix.map_one _ (map_zero _) (map_one _), mul_one] at h1
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, Matrix.det_one, Formalism.UG.cT, Matrix.det_transpose] at h2
  rw [RingHom.map_det]
  exact h2

set_option maxHeartbeats 800000 in

theorem exists_ideal (V : HSp D) (hg : V.gram = 1) (hL : Bridge.hLat V 1 = stdLat D.host.E V.rank) (h : GA D V)
    (e : AE D) (P : Finset (HeightOneSpectrum (𝓞 D.host.E))) (y : (AE D)ˣ) (he : Formalism.IndefR.Datum.IsIdemSum e P)
    (hs : SuppAt e V h) (hy : IsDetAt e V h y) (b : ℕ) (hb : ∀ Q ∈ P, (b : 𝓞 D.host.E) ∉ Q.asIdeal)
    (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E) (hc : ChrEq c χ)
    (hu : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), (b : 𝓞 D.host.E) ∉ Q.asIdeal → χ.UnrAt Q)
    (hr : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), cP Q ≠ Q → ∀ k, χ.resFin (Q.under (𝓞 D.host.F)) k = 1) :
    ∃ cc : Ideal (𝓞 D.host.E), cc ≠ ⊥ ∧ cc ⊔ cc.map (cO D : 𝓞 D.host.E →+* 𝓞 D.host.E) = ⊤ ∧
      cc ⊔ Ideal.span {(b : 𝓞 D.host.E)} = ⊤ ∧
      Submodule.span (𝓞 D.host.E) (detSet (Bridge.hLat V (FWT.fin V h))) *
        idlE (cc.map (cO D : 𝓞 D.host.E →+* 𝓞 D.host.E)) = idlE cc ∧
      ((c y : Circle) : ℂ) = ((χ.onId (cc : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : ℂˣ) : ℂ) := by
  classical
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  have h4 := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3
  obtain ⟨hid, hcj⟩ := GlobalTheory.T.placeIdempotent_components_conj_valuation D ι h1 h2 h4
  obtain ⟨ev, hev⟩ : ∃ ev : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), AE D →+* Q.adicCompletion D.host.E,
      ∀ Q z, ev Q z = ι (finPart D z) Q :=
    ⟨fun Q => ((GlobalTheory.CharLocProd.evalAt Q).comp ι.toRingHom).comp (finPart D), fun _ _ => rfl⟩
  simp only [← hev] at hid hcj
  obtain ⟨⟨es, hes, hsum⟩, horth⟩ := he
  have e0 : infPart D e = 0 := by
    rw [hsum, map_sum]
    exact Finset.sum_eq_zero fun Q hQ => (hid _ _ (hes Q hQ)).1
  have e1 : ∀ Q ∈ P, ev Q e = 1 := fun Q hQ => by
    rw [hsum, map_sum, Finset.sum_eq_single Q (fun Q' h' hne => (hid _ _ (hes Q' h')).2.2 Q hne.symm)
      (fun h' => absurd hQ h'), (hid _ _ (hes Q hQ)).2.1]
  have e2 : ∀ Q, Q ∉ P → ev Q e = 0 := fun Q hQ => by
    rw [hsum, map_sum]
    exact Finset.sum_eq_zero fun Q' h' => (hid _ _ (hes Q' h')).2.2 Q fun hh => hQ (hh ▸ h')
  have hP : ∀ Q ∈ P, cP Q ∉ P := fun Q hQ hQ' => by
    have a := congrArg (ev (cP Q)) horth
    rw [map_mul, e1 _ hQ', one_mul, map_zero] at a
    have a' := hcj e Q
    rw [a, e1 Q hQ, map_zero, map_one] at a'
    exact zero_ne_one a'
  obtain ⟨d, hd⟩ : ∃ d, d = (Formalism.L2.Theta.mt V h).det := ⟨_, rfl⟩
  have d1 : ∀ Q, Q ∉ P → cP Q ∉ P → ev Q d = 1 := fun Q hQ hQ' => by
    rw [hd]
    refine det_supp (ev Q) hs ?_
    have a := hcj e (cP Q)
    rw [e2 _ hQ', map_zero, cP_cP, map_eq_zero] at a
    rw [map_add, e2 Q hQ, a, add_zero]
  have d2 : ∀ Q, Valued.v (ev Q d) * Valued.v (ev (cP Q) d) = 1 := fun Q => by
    rw [← hcj, ← map_mul, ← map_mul, hd, det_unitary V hg h, map_one, map_one]
  have d3 : ∀ Q, Valued.v (ev Q d) ≠ 0 := fun Q => left_ne_zero_of_mul_eq_one (d2 Q)
  obtain ⟨δ, hδ⟩ : ∃ δ : HeightOneSpectrum (𝓞 D.host.E) → ℤ, ∀ Q, Valued.v (ev Q d) = WithZero.exp (-δ Q) :=
    ⟨fun Q => -WithZero.log (Valued.v (ev Q d)), fun Q => by rw [neg_neg, WithZero.exp_log (d3 Q)]⟩
  have δ0 : ∀ Q, Q ∉ P → cP Q ∉ P → δ Q = 0 := fun Q hQ hQ' => by
    have a := hδ Q
    rw [d1 Q hQ hQ', map_one, ← WithZero.exp_zero, WithZero.exp_inj] at a
    omega
  have δ1 : ∀ Q, δ (cP Q) = -δ Q := fun Q => by
    have a := d2 Q
    rw [hδ, hδ, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_inj] at a
    omega
  have hbc : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), (b : 𝓞 D.host.E) ∈ (cP Q).asIdeal ↔ (b : 𝓞 D.host.E) ∈ Q.asIdeal :=
    fun Q => by rw [mem_cP, map_natCast]
  have hfin : (Function.support δ).Finite := by
    refine (P ∪ P.image cP).finite_toSet.subset fun Q hQ => ?_
    by_contra hn
    rw [Finset.mem_coe, Finset.mem_union, not_or] at hn
    exact hQ (δ0 Q hn.1 fun h => hn.2 (Finset.mem_image.2 ⟨_, h, cP_cP Q⟩))
  obtain ⟨cc, c0, c1, c2, c3, c4⟩ := GlobalTheory.T.exists_numeratorIdeal_of_antiInvariant_divisor D.host.E (cO D) cP cO_cO mem_cP δ hfin δ1
  refine ⟨cc, c0, c1, c3 _ fun Q hQ hm => ?_, c4 _ fun x => ?_, ?_⟩
  · exact hQ (δ0 Q (fun h' => hb Q h' hm) fun h' => hb _ h' ((hbc Q).2 hm))
  · rw [GlobalTheory.T.mem_span_detSet_iff_adelicLattice_valuation D.host.E _ _ _ (mem_hLat ι h1 h2 V hL (FWT.fin V h)) x]
    refine forall_congr' fun Q => ?_
    rw [← hδ, hev, hd]
    have a : ι (finPart D (Formalism.L2.Theta.mt V h).det) =
        (Matrix.GeneralLinearGroup.map ι.toRingHom (FWT.fin V h).1).1.det :=
      RingHom.map_det (ι.toRingHom.comp (finPart D)) _
    rw [a]
  · have hv : ∀ (k : D.host.E) (Q : HeightOneSpectrum (𝓞 D.host.E)),
        (cP Q).valuation D.host.E (star k) = Q.valuation D.host.E k := fun k Q => by
      have a : ∀ (Q : HeightOneSpectrum (𝓞 D.host.E)) (k : D.host.E),
          Valued.v (ev Q (incA D k)) = Q.valuation D.host.E k := fun Q k => by
        rw [hev]
        exact (congrArg (fun w : FiniteAdeleRing (𝓞 D.host.E) D.host.E => Valued.v (w Q)) (h1 k)).trans
          (GlobalTheory.CharLocProd.val_algebraMap Q k)
      rw [← a, ← a Q, ← hcj _ Q, cA_incA]
    have hy' : (y : AE D) = e * d + (1 - e) := hd ▸ hy
    rw [onId_eq χ _ δ c2 P hP δ0 δ1 fun Q hQ => val_mul_val hv χ (fun a => hP Q hQ (a.symm ▸ hQ))
      (hr Q fun a => hP Q hQ (a.symm ▸ hQ)) (hu Q (hb Q hQ)) (hu _ fun a => hb Q hQ ((hbc Q).1 a))]
    refine GlobalTheory.T.idelicCharacter_eq_prod_unramifiedValue_zpow D ι h1 h2 h4 c χ hc y ?_ P δ (fun Q hQ => ⟨hu Q (hb Q hQ), ?_⟩) fun Q hQ => ?_
    · rw [hy', RingHom.map_add, RingHom.map_mul, RingHom.map_sub, e0, RingHom.map_one, zero_mul, zero_add, sub_zero]
    · rw [← hev, ← hδ, hy', RingHom.map_add, RingHom.map_mul, RingHom.map_sub, e1 Q hQ, RingHom.map_one, one_mul, sub_self,
        add_zero]
    · rw [← hev, hy', RingHom.map_add, RingHom.map_mul, RingHom.map_sub, e2 Q hQ, RingHom.map_one, zero_mul, zero_add,
        sub_zero]

theorem chrEq_mul_inv {a b c : (AE D)ˣ →* Circle} {α β γ : HChar D.host.E} (ha : ChrEq a α) (hb : ChrEq b β)
    (hc : ChrEq c γ) : ChrEq (a * b * c⁻¹) (α * β * γ⁻¹) := by
  refine ⟨⟨(ha.1.1.mul hb.1.1).mul hc.1.1.inv, fun x => ?_⟩, fun P e he k x hx => ?_⟩
  · rw [MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, ha.1.2, hb.1.2, hc.1.2, inv_one, one_mul, one_mul]
  · show ((a x * b x * (c x)⁻¹ : Circle) : ℂ) = ((α.locK P k * β.locK P k * (γ.locK P k)⁻¹ : ℂˣ) : ℂ)
    rw [Circle.coe_mul, Circle.coe_mul, Circle.coe_inv, ha.2 P e he k x hx, hb.2 P e he k x hx, hc.2 P e he k x hx,
      Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val]

theorem zCard_eq {E : Type} [Field E] [NumberField E] {n : ℕ} (Λ : GenLat E n) (N r : ℕ)
    (h : Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.Ln) :
    Λ.zCard N r = Λ.mIdx N r * (Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index ^ r := by
  rw [GenLat.zCard, GenLat.mIdx, ← mul_pow]
  congr 1
  exact (AddSubgroup.relIndex_mul_relIndex _ _ _ h (inf_le_left : Λ.Ln ≤ Λ.La)).symm

theorem mIdx_ne_zero {E : Type} [Field E] [NumberField E] {n : ℕ} (Λ : GenLat E n) {N : ℕ} (r : ℕ) (hN : N ≠ 0) :
    Λ.mIdx N r ≠ 0 := by
  refine pow_ne_zero _ ?_
  have hfg : (stdLat E n).FG := Submodule.fg_pi fun _ => by
    rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
  have : Module.Finite (𝓞 E) (stdLat E n) := Module.Finite.iff_fg.2 hfg
  have : Module.Finite ℤ (stdLat E n) := Module.Finite.trans (𝓞 E) _
  have : AddGroup.FG (stdLat E n).toAddSubgroup := Module.Finite.iff_addGroup_fg.1 this
  have h1 : (Ideal.span {(N : 𝓞 E)} • stdLat E n).toAddSubgroup.relIndex (stdLat E n).toAddSubgroup ≠ 0 := by
    have := AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg (stdLat E n).toAddSubgroup hN
    refine (AddSubgroup.finiteIndex_of_le (H := (nsmulAddMonoidHom N).range) ?_).index_ne_zero
    rintro _ ⟨x, rfl⟩
    change ((N • x : (stdLat E n).toAddSubgroup) : Fin n → E) ∈ Ideal.span {(N : 𝓞 E)} • stdLat E n
    rw [AddSubgroupClass.coe_nsmul, ← Nat.cast_smul_eq_nsmul (𝓞 E)]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) x.2
  exact fun h0 => h1 (AddSubgroup.relIndex_eq_zero_of_le_right (inf_le_right : Λ.Ln ≤ stdLat E n) h0)

theorem value_calc {x : ℂ} {q : ℚ} {a N m : ℕ} (hq : 0 < q) (ha : a ≠ 0) (hm : m ≠ 0) (h : q ^ 2 * (N : ℚ) = a) :
    (x * (Real.sqrt a : ℝ))⁻¹ * (q : ℂ) * (m : ℂ)⁻¹ * ((m * N : ℕ) : ℂ) = x⁻¹ * (Real.sqrt N : ℝ) := by
  have h1 : Real.sqrt a = q * Real.sqrt N := by
    have : (a : ℝ) = (q : ℝ) ^ 2 * N := by exact_mod_cast h.symm
    rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by exact_mod_cast hq.le)]
  have hN : N ≠ 0 := by
    rintro rfl
    rw [Nat.cast_zero, mul_zero] at h
    exact ha (by exact_mod_cast h.symm)
  have h2 : (N : ℂ) = (Real.sqrt N : ℝ) * (Real.sqrt N : ℝ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
  have h3 : ((Real.sqrt N : ℝ) : ℂ) ≠ 0 := fun h0 => hN (by rw [h0, mul_zero] at h2; exact_mod_cast h2)
  have h4 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have h5 : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  rw [h1, Nat.cast_mul, h2, Complex.ofReal_mul, Complex.ofReal_ratCast, mul_inv]
  generalize ((Real.sqrt N : ℝ) : ℂ) = s at *
  field_simp

end Local

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 800000 in

theorem class_scalar_value : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∀ (t : Tp) (k : O.Cl' t) (h : GA D (Vc D i)) (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (y : (AE D)ˣ), IsIdemSum e P → (∀ PP ∈ P, ((O.bad t : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → SuppAt e (Vc D i) h → IsDetAt e (Vc D i) h y → O.Lh t k = Bridge.hLat (Vc D i) (fin (Vc D i) h) → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q (tup t) → ((O.bad t : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → inC O.c' (O.ep t k * (((O.La t k).mIdx (O.Nc t k) D.R.r : O.c'.F))⁻¹ * ((O.La t k).zCard (O.Nc t k) D.R.r : O.c'.F)) = (((Lift.chrTh (R.toLevCh.mu (tup t)) R.eta ((i : ℕ) + 1)).2 y : Circle) : ℂ)⁻¹ * (Real.sqrt (((((O.La t k).La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf (O.La t k).La.toAddSubgroup).index : ℝ) ^ D.R.r) : ℂ) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC hT i Tp tup O hO t k h e P y he hP hs hy hLh hbad
  have hL := hC.lev
  obtain ⟨r1, r2, -, r4, -, r6⟩ := (hO.reps t).1 k
  have hcj := (GlobalTheory.ClassScalarCompare.latPin_iff_conjLat _ _).1 (hO.reps t).2 k
  have g := GlobalTheory.ClassScalarCompare.guard_conjLat (H := T.Q.H) (L := (O.La t k).La) ⟨r1, r2, r6⟩
  rw [hcj, GlobalTheory.ClassScalarCompare.conjLat_conjLat] at g
  have hpq : D.R.r = (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q :=
    (hT.laws.unf _ ⟨Nat.le_add_left _ _, i.2⟩ _ T.toCore.good_σ₀).1
  have hbar : (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = (GlobalTheory.IdemSupport.cO D : 𝓞 D.host.E →+* 𝓞 D.host.E) :=
    RingHom.ext fun a => RingOfIntegers.ext (T.Q.H.bar_eq a)
  obtain ⟨cc, c0, c1, c2, c3, c4⟩ := exists_ideal (Vc D i) hO.lift.std.1 hO.lift.std.2 h e P y he hs hy (O.bad t) hP _ _
    (chrEq_mul_inv (hL.mu0 i) (hL.xi (tup t)) hL.eta)
    (fun Q hQ x hx => by
      have a1 : (R.C.mu0 i).UnrAt Q := (R.C.isMu0 i).unr Q fun j hj => hQ (by
        obtain ⟨u, hu⟩ := (Finset.dvd_prod_of_mem D.host.g (Finset.mem_univ j)).trans
          ((Fin.prod_univ_two D.host.g).symm ▸ (hO.bad t).2.2.2.2)
        rw [hu, Nat.cast_mul]
        exact Ideal.mul_mem_right _ _ hj)
      have a2 : (R.xiH (tup t)).UnrAt Q := by
        by_contra hn
        rcases (hL.Q_ram (tup t) Q).1 hn with a | ⟨Q', a, a'⟩
        · exact hQ (hbad Q (Or.inr a))
        · rw [(GlobalTheory.IdemSupport.isConjPl_iff _ _).1 a', GlobalTheory.IdemSupport.mem_cP, map_natCast] at hQ
          exact hQ (hbad Q' (Or.inr a))
      rw [Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_inv, a1 x hx, a2 x hx,
        R.C.isEta.unr Q x hx, inv_one, one_mul, one_mul])
    (fun Q hQ x => by
      rw [Formalism.L2.Host.HChar.resFin_mul, Formalism.L2.Host.HChar.resFin_mul, Formalism.L2.Host.HChar.resFin_inv,
        (R.C.isMu0 i).triv.1, (hL.xi_triv (tup t)).1, R.C.isEta.res.1, Formalism.L2.Host.etaFin, above_eq,
        Finset.card_pair hQ.symm, if_neg (by norm_num), inv_one, one_mul, one_mul])
  rw [← hbar] at c1 c3
  rw [← hLh] at c3
  obtain ⟨q, q0, q1, q2⟩ := (hO.ep t).2 (O.Lh t k) cc g.1 g.2.1 g.2.2 c1 c3
  have hB := (hO.tuple t).B cc c0 c2
  have hi := GlobalTheory.ClassScalarCompare.stdIndex_conjLat (O.Lh t k)
  rw [← hcj] at hi
  rw [← hpq, ← Nat.cast_pow] at q1
  have := value_calc (x := (((Lift.chrTh (R.toLevCh.mu (tup t)) R.eta ((i : ℕ) + 1)).2 y : Circle) : ℂ)) q0
    (fun h0 => c0 (Ideal.absNorm_eq_zero_iff.1 h0))
    (mIdx_ne_zero (O.La t k) D.R.r (fun h0 : O.Nc t k = 0 => by simpa [h0] using r4.1)) q1
  rw [(hO.ep t).1 k, q2, zCard_eq _ _ _ r4.2.2, map_mul, map_mul, map_mul, map_inv₀, map_inv₀, hB, ← c4, map_ratCast,
    map_natCast, map_natCast, ← Nat.cast_pow]
  have hi' : ((O.La t k).Ln.toAddSubgroup.addSubgroupOf (O.La t k).La.toAddSubgroup).index =
      ((O.Lh t k ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf (O.Lh t k).toAddSubgroup).index := hi
  rw [← hi'] at this
  exact this

end GlobalTheory.ClassScalarValue
