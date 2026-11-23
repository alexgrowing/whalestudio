import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleOfTheorem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SSAscent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularDefinite
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLatticeComplement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIotaOQOfData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCharpolyCoeffOfMatrix
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RootsCharpolySmulMatrix

noncomputable section

namespace GlobalTheory.ParamRep

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.LocalInv
open GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts

theorem charpoly_smul_eq_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (u : ℂ) :
    (u • M).charpoly = ((M.charpoly.roots.map (· * u)).map fun α => X - C α).prod := by
  have h := (IsAlgClosed.splits (u • M).charpoly).eq_prod_roots_of_monic (Matrix.charpoly_monic _)
  rw [GlobalTheory.RowTie.EigTwist.roots_charpoly_smul_matrix] at h
  exact h

theorem charpoly_smul_of_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (u : ℂ)
    (L : Multiset ℂ) (h : M.charpoly = (L.map fun α => X - C α).prod) :
    (u • M).charpoly = ((L.map (· * u)).map fun α => X - C α).prod := by
  rw [charpoly_smul_eq_prod, h, roots_multiset_prod_X_sub_C]

theorem prod_Icc_eq_fin {M : Type*} [CommMonoid M] (F : ℕ → M) (t : ℕ) :
    ∏ c ∈ Finset.Icc 1 t, F c = ∏ c : Fin t, F ((c : ℕ) + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel,
    Finset.prod_range]
  exact Finset.prod_congr rfl fun c _ => by rw [add_comm]

theorem charpoly_block {k : Type*} [CommRing k] {r t : ℕ} (M : Matrix (Fin r) (Fin r) k) (d : Fin t → k) :
    (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks M 0 0 (Matrix.diagonal d))).charpoly =
      M.charpoly * ∏ c, (X - C (d c)) := by
  rw [Matrix.charpoly_reindex, Matrix.charpoly_fromBlocks_zero₁₂]
  congr 1
  simp [Matrix.charpoly, Matrix.charmatrix, Matrix.det_diagonal]

theorem not_mem_placesOver_of_ne {E : Type} [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) {v : HeightOneSpectrum (𝓞 E)} (hv : v ∈ placesOver E q) : v ∉ placesOver E p := by
  intro hv'
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hne)
  have h1 : (1 : 𝓞 E) ∈ v.asIdeal := by
    have e : (1 : 𝓞 E) = (a : 𝓞 E) * (p : 𝓞 E) + (b : 𝓞 E) * (q : 𝓞 E) := by
      have := congrArg (Int.cast : ℤ → 𝓞 E) hab
      push_cast at this
      exact this.symm
    rw [e]
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hv') (v.asIdeal.mul_mem_left _ hv)
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem locG_tw_tw (hL : Formalism.MainNotions.SumRepresentations.At.TieLP N A) {a : ℕ} (π : A.CG a) (w : PlE H) :
    A.locG (A.tw (A.tw π A.etaTinv) A.etaT) w = A.locG π w := by
  obtain ⟨h1, h2⟩ := A.etaTinv_def w
  have d1 := A.locG_dim A.etaTinv w
  have d2 := A.locG_dim A.etaT w
  have hu2 := A.etaT_unr w
  obtain ⟨c, hc⟩ := Multiset.card_eq_one.mp ((A.frobEig_card _ hu2).trans d2)
  have hc0 : c ≠ 0 := by
    have := A.frobEig_ne_zero _ hu2
    rw [hc] at this
    simpa [eq_comm] using this
  have hu := A.unr_char _ _ d2 h1 hu2
  have hf : A.frobEig (A.lpChar (A.locG A.etaTinv w) (A.locG A.etaT w)) = {1} := by
    rw [A.frobEig_char _ _ c h1 hu2 d2 hc, h2, hc]
    simp [hc0]
  have he : A.lpChar (A.locG A.etaTinv w) (A.locG A.etaT w) = A.lpUnr w {1} := by
    rw [A.unr_eq_lpUnr _ hu, hf]
  obtain ⟨-, -, -, e1, e2, -⟩ := hL w (A.locG π w) (A.locG π w) (A.locG A.etaTinv w) (A.locG A.etaT w) 0 d1 d2
  rw [A.locG_tw, A.locG_tw, e1, he, e2]

theorem hecke_split (i : N.Loc) (x : N.X i) (π : A.CG R.r) (P : A.AV i) (hP : A.ptV i P = some x)
    (hB : IsBCV N A i P (twistIso N A ([⟨R.r, π, 1⟩] ++ [muPart N A i]) A.etaTinv))
    {w : PlE H} (hw : SplitOut N i w) (hu : A.unr (A.locG (A.tw π A.etaTinv) w))
    {B : ValuationSubring N.Om} {σ : G H.E N.Om} (hBw : IsPlaceOver (F := H.E) B w)
    (hσ : IsFrob (F := H.E) B (normV w) σ) :
    (heckePol N i x w).map (iotaO N A i) =
      galPol A (A.lpTw (A.locG (A.tw π A.etaTinv) w) ((1 - (R.nV : ℝ)) / 2)) *
        ∏ c ∈ Finset.Icc 1 R.t, (X - C ((N.chi i c σ : (N.O i)ˣ) : N.O i)).map (iotaO N A i) := by
  have e2 : (heckePol N i x w).map (iotaO N A i) =
      galPol A (A.lpTw (A.locV i P w) ((1 - (R.nV : ℝ)) / 2)) := A.pt_loc i P x hP w hw
  have e3 := hB.2.2.2.1 w hw.1
  have s1 := galPol_speh N A ⟨R.r, A.tw π A.etaTinv, 1⟩ w hu ((1 - (R.nV : ℝ)) / 2)
  have s2 := galPol_speh N A ⟨1, A.tw (A.muC i) A.etaTinv, R.t⟩ w (A.chi_mu i w hw).1
    ((1 - (R.nV : ℝ)) / 2)
  have e4 : isoLoc N A (twistIso N A ([⟨R.r, π, 1⟩] ++ [muPart N A i]) A.etaTinv) w =
      A.lpSum (spehLoc N A ⟨R.r, A.tw π A.etaTinv, 1⟩ w)
        (A.lpSum (spehLoc N A ⟨1, A.tw (A.muC i) A.etaTinv, R.t⟩ w) (A.lpZero w)) := rfl
  have e5 : ∏ c ∈ Finset.Icc 1 R.t,
        (X - C ((N.chi i c σ : (N.O i)ˣ) : N.O i)).map (iotaO N A i) =
      ∏ k ∈ Finset.range R.t, galPol A (A.lpTw (A.locG (A.tw (A.muC i) A.etaTinv) w)
        (((R.t : ℝ) - 1) / 2 - k + (1 - (R.nV : ℝ)) / 2)) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel]
    refine Finset.prod_congr rfl fun k hk => ?_
    have hx : ((R.t : ℝ) - 1) / 2 - k + (1 - (R.nV : ℝ)) / 2 =
        ((R.t : ℝ) - 1) / 2 + (1 - (R.nV : ℝ)) / 2 + (-(k : ℝ)) := by ring
    rw [hx, galPol_block N A i hw hBw hσ, add_comm 1 k, chi_apply N i k (Finset.mem_range.mp hk)]
    have hq := iota_eps N A i hw.2.1 hBw hσ
    have hinv : iotaO N A i ((((eps N i σ) ^ k)⁻¹ : (N.O i)ˣ) : N.O i) =
        ((normV w : ℕ) : ℂ) ^ (((-(k : ℝ) : ℝ)) : ℂ) := by
      rw [Complex.ofReal_neg, Complex.cpow_neg, Complex.ofReal_natCast, Complex.cpow_natCast, ← hq,
        map_units_inv, Units.val_pow_eq_pow_val, map_pow]
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Units.val_mul, map_mul, hinv]
  rw [e2, ← e3, e4, A.lpSum_zero, galPol_tw_sum N A _ _ s1.1 s2.1, s1.2, s2.2, e5]
  simp

theorem galPol_twist {w : PlE H} (π : A.CG R.r) (hu : A.unr (A.locG π w)) (u : ℂ)
    (hξ : A.frobEig (A.lpTw (A.locG A.etaTinv w) (-(R.t : ℝ) / 2)) = {u}) :
    galPol A (A.lpTw (A.locG (A.tw π A.etaTinv) w) ((1 - (R.nV : ℝ)) / 2)) =
      (((A.frobEig (A.lpTw (A.locG π w) ((1 - (R.r : ℝ)) / 2))).map (· * u)).map fun α => X - C α).prod := by
  obtain ⟨h1, -⟩ := A.etaTinv_def w
  have d1 := A.locG_dim A.etaTinv w
  obtain ⟨d, hd⟩ := Multiset.card_eq_one.mp ((A.frobEig_card _ h1).trans d1)
  rw [A.frobEig_tw _ _ h1, hd, Multiset.map_singleton, Multiset.singleton_inj] at hξ
  unfold galPol
  rw [A.locG_tw, A.frobEig_tw _ _ (A.unr_char _ _ d1 hu h1), A.frobEig_char _ _ d hu h1 d1 hd,
    A.frobEig_tw _ _ hu]
  simp only [Multiset.map_map]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun α _ => ?_)
  simp only [Function.comp]
  rw [← hξ]
  have hq : ((normV w : ℕ) : ℂ) ^ (((1 - (R.nV : ℝ)) / 2 : ℝ) : ℂ) =
      ((normV w : ℕ) : ℂ) ^ (((1 - (R.r : ℝ)) / 2 : ℝ) : ℂ) *
        ((normV w : ℕ) : ℂ) ^ ((-(R.t : ℝ) / 2 : ℝ) : ℂ) := by
    rw [← Complex.cpow_add _ _ (normV_ne_zero w)]
    congr 1
    rw [Ranks.nV]
    push_cast
    ring
  rw [hq]
  congr 2
  ring

theorem map_smul_matrix {k l : Type*} [CommRing k] [CommRing l] {n : Type*} (f : k →+* l) (c : k)
    (M : Matrix n n k) : (c • M).map f = f c • M.map f := by
  ext i j
  simp

section Twist

variable {Γ : Type} [Group Γ]

theorem coe_twGL {k : Type} [CommRing k] {n : ℕ} (ρ : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) (g : Γ) :
    ((Formalism.MainNotions.SumRepresentations.At.twGL ρ χ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      ((χ g : kˣ) : k) • ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  show algebraMap k (Matrix (Fin n) (Fin n) k) ((χ g : kˣ) : k) * _ = _
  rw [← Algebra.smul_def]

theorem twGL_twGL_inv {k : Type} [CommRing k] {n : ℕ} (ρ : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) :
    Formalism.MainNotions.SumRepresentations.At.twGL (Formalism.MainNotions.SumRepresentations.At.twGL ρ χ⁻¹) χ = ρ := by
  ext g : 2
  rw [coe_twGL, coe_twGL, smul_smul, MonoidHom.inv_apply, ← Units.val_mul, mul_inv_cancel]
  simp

theorem mapRep_twGL {k l : Type} [CommRing k] [CommRing l] {n : ℕ} (f : k →+* l) (ρ : Γ →* GL (Fin n) k)
    (χ : Γ →* kˣ) :
    mapRep f (Formalism.MainNotions.SumRepresentations.At.twGL ρ χ) =
      Formalism.MainNotions.SumRepresentations.At.twGL (mapRep f ρ) ((Units.map f.toMonoidHom).comp χ) := by
  ext g : 2
  rw [coe_twGL, mapRep_twGL_coe]
  rfl

theorem isSSRep_twGL {k : Type} [Field k] {n : ℕ} (ρ : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) (h : IsSSRep ρ) :
    IsSSRep (Formalism.MainNotions.SumRepresentations.At.twGL ρ χ) := by
  have key : ∀ W : Submodule k (Fin n → k), IsInv (Formalism.MainNotions.SumRepresentations.At.twGL ρ χ) W ↔ IsInv ρ W := by
    intro W
    refine ⟨fun hW g v hv => ?_, fun hW g v hv => ?_⟩
    · have h1 := hW g v hv
      rw [coe_twGL, Matrix.smul_mulVec] at h1
      exact (W.smul_mem_iff (χ g).ne_zero).1 h1
    · rw [coe_twGL, Matrix.smul_mulVec]
      exact W.smul_mem _ (hW g v hv)
  intro W hW
  obtain ⟨W', h1, h2⟩ := h W ((key W).1 hW)
  exact ⟨W', (key W').2 h1, h2⟩

end Twist

theorem rep_at_point (hLP : Formalism.MainNotions.SumRepresentations.At.TieLP N A) (hAut : Formalism.MainNotions.SumRepresentations.At.TieAut N A)
    (hW : WeightRegular N A) (hGal : Formalism.MainNotions.SumRepresentations.At.exists_galois_rep_local_global_compatible N A) (hAN : Formalism.MainNotions.SumRepresentations.At.JacquetShalikaStrongMultOne N A)
    (h41 : ∀ i, Formalism.MainNotions.SumRepresentations.At.Conclusion41 N A i) (hGC : GoodCuspidal N A) (hXi : GlobalTheory.SplitRead.XiOverO N A)
    (a : N.Loc) (x : N.X a) (Sig : List (Part A.CG)) (hSig : HasParamX N A a x Sig)
    (hgood : goodSig N A Sig) :
    ∃ (ρ : G H.E N.Om →* GL (Fin R.r) (N.O a)) (ξ : G H.E N.Om →* (N.O a)ˣ),
      IsRepOfSig N A a Sig ρ ∧
      (∀ k, N.l a ≠ H.g k → ∀ v ∈ placesOver H.E (H.g k), ∀ σ ∈ Ine (F := H.E) (N.plOm.1 v), ξ σ = 1) ∧
      IsRhoOf N a x (Formalism.MainNotions.SumRepresentations.At.twGL ρ ξ) := by
  obtain ⟨π, rfl⟩ := hGC a x Sig hSig hgood
  obtain ⟨P, hP, hB⟩ := hSig
  obtain ⟨ξ, hξc, hξ⟩ := hXi a
  have hη : EtaType N A := ⟨hAut.1.1, fun τ z hz => by
    rcases (hAut.2.1 τ).1 with h | h <;> rw [h, Multiset.mem_singleton] at hz <;> subst hz
    · exact ⟨0, by simp⟩
    · exact ⟨-1, by norm_num⟩⟩
  have al := part_alg N A hη hW a P _ hB ⟨R.r, A.tw π A.etaTinv, 1⟩ (by simp [twistIso]) (r_odd R) odd_one
  obtain ⟨ρ₀, hc0, -, haw, hab⟩ := (hGal a).1 R.r (r_odd R).pos _ al.1 al.2
  have hwd : ∀ w, A.wdOf a ρ₀ w = A.lpTw (A.locG π w) ((1 - (R.r : ℝ)) / 2) := by
    intro w
    by_cases hw : w ∈ placesOver H.E (N.l a)
    · rw [(hab w hw).2.2, locG_tw_tw N A hLP]
    · rw [(haw w hw).1, locG_tw_tw N A hLP]
  obtain ⟨⟨-, rf, hr⟩, -, -⟩ := h41 a
  obtain ⟨hrc, hrs, hrf⟩ := hr x
  have hιc : Continuous (iotaOQ N A a) := GlobalTheory.CoeffEmbedding.continuous_iotaOQ_of_data N A a
  have hcomp : iotaO N A a = (A.iotaQC a).toRingHom.comp (iotaOQ N A a) := rfl
  have hinj : Function.Injective (Polynomial.map (A.iotaQC a).toRingHom) :=
    Polynomial.map_injective _ (A.iotaQC a).injective

  have hfr : ∀ w, w ∉ placesOver H.E (N.l a) → A.unr (A.locG π w) → ∀ (B : ValuationSubring N.Om)
      (σ : G H.E N.Om), IsPlaceOver (F := H.E) B w → IsFrob (F := H.E) B (normV w) σ →
      (((ρ₀ σ : GL _ _) : Matrix (Fin R.r) (Fin R.r) (Qbar (N.l a))).map (A.iotaQC a).toRingHom).charpoly =
        galPol A (A.lpTw (A.locG π w) ((1 - (R.r : ℝ)) / 2)) := by
    intro w h1 h2 B σ hB hσ
    have hu : A.unr (A.wdOf a ρ₀ w) := by
      rw [hwd w]; exact (A.unr_tw _ _).2 h2
    have e := A.wdOf_frob a ρ₀ w h1 hc0 hu B σ hB hσ
    rw [hwd w] at e
    rw [Matrix.charpoly_map]
    exact e

  let R1 := Formalism.MainNotions.SumRepresentations.At.twGL ρ₀ ((Units.map (iotaOQ N A a).toMonoidHom).comp ξ)
  have hR1 : ∀ g, ((R1 g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (Qbar (N.l a))) =
      iotaOQ N A a ((ξ g : (N.O a)ˣ) : N.O a) • ((ρ₀ g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (Qbar (N.l a))) :=
    fun g => coe_twGL _ _ g
  have hR1c : Continuous fun g => ((R1 g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (Qbar (N.l a))) := by
    simp only [hR1]
    exact (hιc.comp hξc).smul hc0
  have hR1C : ∀ g, ((R1 g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (Qbar (N.l a))).map (A.iotaQC a).toRingHom =
      iotaO N A a ((ξ g : (N.O a)ˣ) : N.O a) •
        ((ρ₀ g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (Qbar (N.l a))).map (A.iotaQC a).toRingHom := by
    intro g
    rw [hR1, map_smul_matrix]
    rfl

  have hfin := placesOver_finite_joint_conditions_zpowers H.E (N.l a) (N.lPrime a).out.ne_zero
  have hall := (((hfin.eventually_cofinite_notMem.and (N.S a).finite_toSet.eventually_cofinite_notMem).and
    (N.Q a).finite_toSet.eventually_cofinite_notMem).and (A.locG_unr_ae π)).and
      (A.locG_unr_ae (A.tw π A.etaTinv))
  have hd := dense_iff_closure_eq.2 (hAN.2.2.1 _ (Filter.eventually_cofinite.1 hall))
  have hkey := GlobalTheory.TypeLeaf.charpoly_eq_of_dense (G H.E N.Om) (Qbar (N.l a)) (R.r + R.t)
    (fun g => ((rf x g : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O a)).map (iotaOQ N A a))
    (fun g => Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks
      ((R1 g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (Qbar (N.l a))) 0 0
      (Matrix.diagonal fun c : Fin R.t => iotaOQ N A a ((N.chi a ((c : ℕ) + 1) g : (N.O a)ˣ) : N.O a))))
    _ hd (hrc.matrix_map hιc)
    (by
      refine Continuous.matrix_reindex ?_ _ _
      refine Continuous.matrix_fromBlocks hR1c continuous_const continuous_const ?_
      exact Continuous.matrix_diagonal (continuous_pi fun c => hιc.comp (N.chi_cont a _)))
    (by
      rintro g ⟨v, hv, hsp, B, hBv, hg⟩
      obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := not_not.1 hv
      have hso : SplitOut N a v := ⟨hsp, h1, h2, h3⟩
      apply hinj
      have eL : (((rf x g : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O a)).map
          (iotaOQ N A a)).charpoly.map (A.iotaQC a).toRingHom = (heckePol N a x v).map (iotaO N A a) := by
        rw [Matrix.charpoly_map, Polynomial.map_map, ← hcomp, hrf v hso B g hBv hg]
      refine eL.trans ?_
      rw [charpoly_block, Polynomial.map_mul, ← Matrix.charpoly_map, hR1C g,
        hecke_split N A a x π P hP hB hso h5 hBv hg,
        galPol_twist N A π h4 _ ((hξ v h1).2 B g hBv hg),
        charpoly_smul_of_prod _ _ _ (hfr v h1 h4 B g hBv hg), prod_Icc_eq_fin, Polynomial.map_prod]
      congr 1
      refine Finset.prod_congr rfl fun c _ => ?_
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      rfl)

  haveI : CharZero (Qbar (N.l a)) := (RingHom.charZero_iff (A.iotaQC a).toRingHom.injective).2 inferInstance
  haveI : CharZero (Kf N a) := (RingHom.charZero_iff (A.iotaQ a).injective).2 inferInstance
  have hkey' : ∀ g, (((rf x g : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O a))).charpoly.map (iotaOQ N A a) =
      ((R1 g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (Qbar (N.l a))).charpoly *
        ∏ c : Fin R.t, (X - C (iotaOQ N A a ((N.chi a ((c : ℕ) + 1) g : (N.O a)ˣ) : N.O a))) :=
    fun g => (Matrix.charpoly_map _ _).symm.trans ((hkey g).trans (charpoly_block _ _))
  obtain ⟨ρ', hρc, hρs, hρp⟩ := GlobalTheory.LatticeComplement.exists_lattice_complement (G H.E N.Om) (N.O a) (Kf N a)
    R.r R.t (rf x) (fun c : Fin R.t => N.chi a ((c : ℕ) + 1)) hrc hrs
    ⟨Qbar (N.l a), inferInstance, A.iotaQ a, R1, hkey'⟩
  have hcan : ∀ g, ((ρ' g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (N.O a)).charpoly.map (iotaOQ N A a) =
      ((R1 g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (Qbar (N.l a))).charpoly := by
    intro g
    have e1 : (((rf x g : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O a))).charpoly.map (iotaOQ N A a) =
        ((ρ' g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (N.O a)).charpoly.map (iotaOQ N A a) *
          ∏ c : Fin R.t, (X - C (iotaOQ N A a ((N.chi a ((c : ℕ) + 1) g : (N.O a)ˣ) : N.O a))) := by
      have := congrArg (Polynomial.map (iotaOQ N A a)) (hρp g)
      rw [Polynomial.map_mul, Polynomial.map_prod] at this
      refine this.trans ?_
      congr 1
      refine Finset.prod_congr rfl fun c _ => ?_
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    have hne : (∏ c : Fin R.t, (X - C (iotaOQ N A a ((N.chi a ((c : ℕ) + 1) g : (N.O a)ˣ) : N.O a)))) ≠ 0 :=
      (monic_prod_of_monic _ _ fun c _ => monic_X_sub_C _).ne_zero
    exact mul_right_cancel₀ hne (e1.symm.trans (hkey' g))
  refine ⟨Formalism.MainNotions.SumRepresentations.At.twGL ρ' ξ⁻¹, ξ, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · have e : (fun g => ((Formalism.MainNotions.SumRepresentations.At.twGL ρ' ξ⁻¹ g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (N.O a))) =
        fun g => ((ξ g⁻¹ : (N.O a)ˣ) : N.O a) • ((ρ' g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (N.O a)) := by
      funext g
      rw [coe_twGL, MonoidHom.inv_apply, map_inv]
    rw [e]
    exact (hξc.comp continuous_inv).smul hρc
  · rw [mapRep_twGL]
    exact isSSRep_twGL _ _ hρs
  · filter_upwards [hfin.eventually_cofinite_notMem, A.locG_unr_ae π] with w h1 h2 B σ hBw hσ
    have iso : isoLoc N A [⟨R.r, π, 1⟩] w = A.locG π w := by
      simp [isoLoc, spehLoc, A.lpSum_zero, A.lpTw_zero]
    rw [iso]
    have h0 := hfr w h1 h2 B σ hBw hσ
    have c1 : (((ρ' σ : GL _ _) : Matrix (Fin R.r) (Fin R.r) (N.O a)).map (iotaO N A a)).charpoly =
        (((A.frobEig (A.lpTw (A.locG π w) ((1 - (R.r : ℝ)) / 2))).map
          (· * iotaO N A a ((ξ σ : (N.O a)ˣ) : N.O a))).map fun α => X - C α).prod := by
      rw [Matrix.charpoly_map, hcomp, ← Polynomial.map_map, hcan σ, ← Matrix.charpoly_map, hR1C σ]
      exact charpoly_smul_of_prod _ _ _ h0
    have c2 := charpoly_smul_of_prod _ (iotaO N A a (((ξ⁻¹ σ : (N.O a)ˣ)) : N.O a)) _ c1
    have huv : iotaO N A a ((ξ σ : (N.O a)ˣ) : N.O a) * iotaO N A a (((ξ⁻¹ σ : (N.O a)ˣ)) : N.O a) = 1 := by
      rw [← map_mul, MonoidHom.inv_apply, ← Units.val_mul, mul_inv_cancel]
      simp
    have hL : ((A.frobEig (A.lpTw (A.locG π w) ((1 - (R.r : ℝ)) / 2))).map
          (· * iotaO N A a ((ξ σ : (N.O a)ˣ) : N.O a))).map
          (· * iotaO N A a (((ξ⁻¹ σ : (N.O a)ˣ)) : N.O a)) =
        A.frobEig (A.lpTw (A.locG π w) ((1 - (R.r : ℝ)) / 2)) := by
      rw [Multiset.map_map]
      refine (Multiset.map_congr rfl fun α _ => ?_).trans (Multiset.map_id _)
      show α * _ * _ = α
      rw [mul_assoc, huv, mul_one]
    rw [← Matrix.charpoly_map, coe_twGL, map_smul_matrix, c2, hL]
    rfl
  · exact fun k hk v hv σ hσ =>
      (hξ v (not_mem_placesOver_of_ne (N.lPrime a).out (H.g_prime k) hk hv)).1 σ hσ
  · rw [twGL_twGL_inv]
    refine ⟨hρc, hρs, fun w hw B σ hB hσ => ?_⟩
    rw [prod_Icc_eq_fin (fun c => X - C ((N.chi a c σ : (N.O a)ˣ) : N.O a))]
    exact (hρp σ).symm.trans (hrf w hw B σ hB hσ)

end GlobalTheory.ParamRep

section Final

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

theorem GlobalTheory.ParamRep.jointCond_rho : ∀ D : D7, Formalism.MainNotions.SumRepresentations.tie0 D → Formalism.MainNotions.SumRepresentations.adm2 D → Formalism.MainNotions.SumRepresentations.ArchimedeanSignatureMatching D → Formalism.MainNotions.SumRepresentations.adm5 D → Formalism.MainNotions.SumRepresentations.Conclusion41 D → GlobalTheory.LocalInv.GoodCuspidal D.nd D.naut → XiOverO D.nd D.naut → Formalism.MainNotions.N.GlobalDatumResidualRepCondition D := by
  intro D h0 h2 _ h5 h41 hGC hXi a x _ Sig hSig hgood
  exact GlobalTheory.ParamRep.rep_at_point D.nd D.naut h0.1 h0.2.1 (GlobalTheory.LocalInv.weightRegular_definite D) h2 h5 h41 hGC hXi
    a x Sig hSig hgood

end Final
