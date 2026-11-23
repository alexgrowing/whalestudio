import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotMemPlacesOverOfNe
import Development.AutomorphicArithmetic.ThetaCorrespondence.CuspidalSupport.CuspOfCq
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AutomorphicGaloisAdmissible

noncomputable section

namespace GlobalTheory.ParamRep

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.LocalInv
open GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem rep_at_point_alt (hLP : Formalism.MainNotions.SumRepresentations.At.TieLP N A) (hAut : Formalism.MainNotions.SumRepresentations.At.TieAut N A)
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
  obtain ⟨ρ₀, hc0, -, haw, -⟩ := (UpperTheory.GalS.weakA hGal a).1 R.r (r_odd R).pos _ al.1 al.2
  have hwd : ∀ w, w ∉ placesOver H.E (N.l a) → A.unr (A.locG π w) →
      A.wdOf a ρ₀ w = A.lpTw (A.locG π w) ((1 - (R.r : ℝ)) / 2) := by
    intro w hw hu
    have k1 := haw w hw
    rw [locG_tw_tw N A hLP] at k1
    exact k1.eq_of_unr ((A.unr_tw _ _).2 hu)
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
      rw [hwd w h1 h2]; exact (A.unr_tw _ _).2 h2
    have e := A.wdOf_frob a ρ₀ w h1 hc0 hu B σ hB hσ
    rw [hwd w h1 h2] at e
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

example : type_of% @rep_at_point := @rep_at_point_alt

end GlobalTheory.ParamRep
