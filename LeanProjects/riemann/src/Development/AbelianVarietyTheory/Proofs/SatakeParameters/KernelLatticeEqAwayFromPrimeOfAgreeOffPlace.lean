import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePtOne
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicLatticeSmulMemOfAgreeAwayFromPlaceStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

noncomputable section

namespace GlobalTheory.TwV.Xc

theorem sameOff_symm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (w : HeightOneSpectrum (𝓞 F)) {N : ℕ} {x y : GL (Fin N) (AfE F E)} (h : SameOff w x y) : SameOff w y x :=
  fun w' hw => (h w' hw).symm

set_option maxHeartbeats 1000000 in

theorem normConj_mem_pow : ∀ (D : D7) (n p : ℕ) (G : GAtP p) (A : LocAt D.host.F D.host.E n G), LocInt A → SplAlg A → ∀ v (P : HeightOneSpectrum (𝓞 D.host.E)), PrimeOf p (G.P.W v) (A.iw v) P → ∀ (m : ℕ) (a b : 𝓞 D.host.E), (b : D.host.E) = D.host.conj (a : D.host.E) → a ∈ P.asIdeal ^ m → ∃ c : 𝓞 D.host.F, c ∈ (A.pl v).1.asIdeal ^ m ∧ algebraMap D.host.F D.host.E (c : D.host.F) = ((a * b : 𝓞 D.host.E) : D.host.E) := by
  intro D n p G A hInt hSpl v P hP m a b hb ha

  let T : ℕ → Ideal (𝓞 D.host.E) := fun k =>
    { carrier := {x | ∃ y : G.P.W v, A.iw v (x : D.host.E) = algebraMap _ _ y ∧ (p : G.P.W v) ^ k ∣ y}
      add_mem' := by
        rintro x x' ⟨y, hy, hdy⟩ ⟨y', hy', hdy'⟩
        exact ⟨y + y', by simp [hy, hy'], dvd_add hdy hdy'⟩
      zero_mem' := ⟨0, by simp, dvd_zero _⟩
      smul_mem' := by
        rintro r x ⟨y, hy, hdy⟩
        obtain ⟨yr, hyr, -⟩ := hP r
        exact ⟨yr * y, by simp [hy, hyr], dvd_mul_of_dvd_right hdy _⟩ }
  have hT : ∀ k, P.asIdeal ^ k ≤ T k := by
    intro k
    induction k with
    | zero =>
      intro x _
      obtain ⟨y, hy, -⟩ := hP x
      exact ⟨y, hy, by simp⟩
    | succ k ih =>
      rw [pow_succ]
      refine Ideal.mul_le.2 fun x hx z hz => ?_
      obtain ⟨y, hy, hdy⟩ := ih hx
      obtain ⟨yz, hyz, hdz⟩ := hP z
      exact ⟨y * yz, by simp [hy, hyz], by rw [pow_succ]; exact mul_dvd_mul hdy (hdz.1 hz)⟩
  obtain ⟨ya, hya, hda⟩ := hT m ha
  obtain ⟨yb, hyb, -⟩ := hP b
  have hcc : ∀ x : D.host.E, D.host.φ₀ (D.host.conj x) = starRingEnd ℂ (D.host.φ₀ x) :=
    fun x => D.host.conjE_apply D.host.φ₀ x
  have hcc2 : ∀ x : D.host.E, D.host.conj (D.host.conj x) = x := fun x =>
    D.host.φ₀.injective (by rw [hcc, hcc, Complex.conj_conj])
  have hfix : D.host.conj (((a * b : 𝓞 D.host.E) : D.host.E)) = ((a * b : 𝓞 D.host.E) : D.host.E) := by
    show D.host.conj ((a : D.host.E) * (b : D.host.E)) = (a : D.host.E) * (b : D.host.E)
    rw [map_mul, hb, hcc2, mul_comm]
  have hF : ((a * b : 𝓞 D.host.E) : D.host.E) ∈ D.host.F :=
    (D.host.conjE_mem_hostF_iff _).2 hfix
  have hint : IsIntegral ℤ (⟨_, hF⟩ : D.host.F) :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ D.host.F D.host.E) (algebraMap D.host.F D.host.E).injective).1
      (a * b).isIntegral_coe
  let c : 𝓞 D.host.F := ⟨⟨_, hF⟩, hint⟩
  refine ⟨c, ?_, rfl⟩
  obtain ⟨t, ht⟩ := hda
  have hiw : A.iw v ((a * b : 𝓞 D.host.E) : D.host.E) = (p : G.P.Qq v) ^ m * algebraMap _ _ (t * yb) := by
    show A.iw v ((a : D.host.E) * (b : D.host.E)) = _
    rw [map_mul, hya, hyb, ht]
    simp only [map_mul, map_pow, map_natCast]
    ring
  have hph : A.phE v ((a * b : 𝓞 D.host.E) : D.host.E) =
      algebraMap D.host.F ((A.pl v).1.adicCompletion D.host.F) (c : D.host.F) := by
    have h1 : (inclE (F := D.host.F) ((A.pl v).1.adicCompletion D.host.F)) ((a * b : 𝓞 D.host.E) : D.host.E) =
        (1 : D.host.E) ⊗ₜ[D.host.F] algebraMap D.host.F ((A.pl v).1.adicCompletion D.host.F) (c : D.host.F) := by
      show (algebraMap D.host.F D.host.E (c : D.host.F)) ⊗ₜ[D.host.F] (1 : (A.pl v).1.adicCompletion D.host.F) = _
      rw [← Algebra.TensorProduct.algebraMap_apply (R := D.host.F) (S := D.host.F), Algebra.TensorProduct.algebraMap_apply']
    show ((A.spl v) ((inclE (F := D.host.F) ((A.pl v).1.adicCompletion D.host.F)) ((a * b : 𝓞 D.host.E) : D.host.E))).1 = _
    refine (congrArg (fun z => ((A.spl v) z).1) h1).trans ?_
    simp only [hSpl v]
  have heQ : A.eQ v (A.iw v ((a * b : 𝓞 D.host.E) : D.host.E)) = A.phE v ((a * b : 𝓞 D.host.E) : D.host.E) := by
    simp [LocAt.iw]
  have hu : A.eQ v (algebraMap _ _ (t * yb)) ∈ (A.pl v).1.adicCompletionIntegers D.host.F :=
    (hInt v _).1 ⟨_, rfl⟩
  rw [hiw, map_mul, map_pow, map_natCast, hph] at heQ
  have hval : ∀ k : D.host.F, Valued.v (algebraMap D.host.F ((A.pl v).1.adicCompletion D.host.F) k) =
      (A.pl v).1.valuation D.host.F k := by
    intro k
    rw [HeightOneSpectrum.algebraMap_adicCompletion]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (A.pl v).1 k
  have hp1 : Valued.v ((p : ℕ) : (A.pl v).1.adicCompletion D.host.F) ≤ WithZero.exp (-1 : ℤ) := by
    have h := (HeightOneSpectrum.intValuation_le_pow_iff_mem (A.pl v).1 ((p : ℕ) : 𝓞 D.host.F) 1).2
      (by simpa using (A.pl v).2)
    rw [← map_natCast (algebraMap D.host.F ((A.pl v).1.adicCompletion D.host.F)), hval,
      ← map_natCast (algebraMap (𝓞 D.host.F) D.host.F), HeightOneSpectrum.valuation_of_algebraMap]
    simpa using h
  have hu' : Valued.v (A.eQ v (algebraMap _ _ (t * yb))) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hu
  have hv : Valued.v (algebraMap D.host.F ((A.pl v).1.adicCompletion D.host.F) (c : D.host.F)) ≤
      WithZero.exp (-(m : ℤ)) := by
    rw [← heQ, map_mul, map_pow]
    calc _ ≤ WithZero.exp (-1 : ℤ) ^ m * 1 := mul_le_mul' (pow_le_pow_left' hp1 m) hu'
      _ = WithZero.exp (-(m : ℤ)) := by
        rw [mul_one, ← WithZero.exp_nsmul]
        congr 1
        simp
  rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem, ← HeightOneSpectrum.valuation_of_algebraMap (K := D.host.F),
    ← hval]
  exact hv

theorem smul_latK_of_smul_latAd : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E) (x x' : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (Lb : Submodule (𝓞 E) (Fin N → E)) (c : 𝓞 E), (c : E) ∈ (algebraMap F E).range → (∀ y ∈ latAd x Lb, c • y ∈ latAd x' Lb) → (∀ y ∈ latAd x' Lb, c • y ∈ latAd x Lb) → ∀ z ∈ latK sp J a x Lb, c • z ∈ latK sp J a x' Lb := by
  intro R F E _ _ _ _ _ _ sp N J a x x' Lb c hc h1 h2
  obtain ⟨c0, hc0⟩ := hc
  have hsig : (sp.cm.sig : E →+* E) (c : E) = c := by
    rw [← hc0]; exact (sp.cm.sig).commutes c0
  have hsm : ∀ y : Fin N → E, c • y = (c : E) • y := fun y => rfl
  have hd : ∀ y ∈ dualSet (sp.cm.sig : E →+* E) J (latAd x Lb),
      c • y ∈ dualSet (sp.cm.sig : E →+* E) J (latAd x' Lb) := by
    intro y hy z hz
    have key := hy _ (h2 z hz)
    have e1 : hform (sp.cm.sig : E →+* E) J z (c • y) = hform (sp.cm.sig : E →+* E) J (c • z) y := by
      rw [hsm, hsm]
      simp only [hform, Pi.smul_apply, smul_eq_mul, map_mul, hsig]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e1]; exact key
  have hc' : compan (sp := sp) J a (latAd x Lb) ≤
      (compan (sp := sp) J a (latAd x' Lb)).comap (DistribMulAction.toLinearMap (𝓞 E) (Fin N → E) c) := by
    unfold compan
    refine sup_le (fun y hy => ?_) (Submodule.smul_le.2 fun r hr n hn => ?_)
    · exact Submodule.mem_sup_left (h1 y hy)
    · have hn' : c • n ∈ Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) J (latAd x' Lb)) := by
        have : Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) J (latAd x Lb)) ≤
            (Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) J (latAd x' Lb))).comap
              (DistribMulAction.toLinearMap (𝓞 E) (Fin N → E) c) :=
          Submodule.span_le.2 fun y hy => Submodule.subset_span (hd y hy)
        exact this hn
      rw [Submodule.mem_comap]
      show c • (r • n) ∈ _
      rw [smul_comm]
      exact Submodule.mem_sup_right (Submodule.smul_mem_smul hr hn')
  intro z hz
  unfold latK toStd at hz ⊢
  obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hz
  refine Submodule.mem_map.2 ⟨c • w, hc' hw, ?_⟩
  rw [LinearMap.map_smul]

theorem eqOff_latK_of_sameOff : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (n p : ℕ) [Fact p.Prime] (G : GAtP p) (A : LocAt D.host.F D.host.E n G), LocInt A → SplAlg A → ∀ v (P : HeightOneSpectrum (𝓞 D.host.E)), PrimeOf p (G.P.W v) (A.iw v) P → ∀ (N : ℕ) (J : Matrix (Fin N) (Fin N) D.host.E) (a : 𝓞 D.host.E) (Lb : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), Module.Finite (𝓞 D.host.E) Lb → Submodule.span D.host.E (Lb : Set (Fin N → D.host.E)) = ⊤ → ∀ x x' : GL (Fin N) (AfE D.host.F D.host.E), SameOff (A.pl v).1 x x' → GL3Theta.EqOff D P (latK D.sp J a x Lb) (latK D.sp J a x' Lb) := by
  intro D n p _ G A hInt hSpl v P hP N J a Lb hfin hspan x x' hoff
  obtain ⟨m1, h1⟩ := GlobalTheory.T.adelicLattice_smul_mem_of_agree_away_from_place D.host.F D.host.E N Lb hfin hspan (A.pl v).1 x x' hoff
  obtain ⟨m2, h2⟩ := GlobalTheory.T.adelicLattice_smul_mem_of_agree_away_from_place D.host.F D.host.E N Lb hfin hspan (A.pl v).1 x' x (sameOff_symm _ hoff)
  refine ⟨max m1 m2, fun a' b hb ha => ?_⟩
  obtain ⟨c, hc, hcab⟩ := normConj_mem_pow D n p G A hInt hSpl v P hP (max m1 m2) a' b hb ha
  have hr : ((a' * b : 𝓞 D.host.E) : D.host.E) ∈ (algebraMap D.host.F D.host.E).range := ⟨_, hcab⟩
  have e1 : ∀ y ∈ latAd x Lb, (a' * b) • y ∈ latAd x' Lb := by
    intro y hy
    have := h1 c (Ideal.pow_le_pow_right (le_max_left _ _) hc) y hy
    rw [hcab] at this
    exact this
  have e2 : ∀ y ∈ latAd x' Lb, (a' * b) • y ∈ latAd x Lb := by
    intro y hy
    have := h2 c (Ideal.pow_le_pow_right (le_max_right _ _) hc) y hy
    rw [hcab] at this
    exact this
  exact ⟨smul_latK_of_smul_latAd D.sp J a x x' Lb _ hr e1 e2, smul_latK_of_smul_latAd D.sp J a x' x Lb _ hr e2 e1⟩

end GlobalTheory.TwV.Xc

end
