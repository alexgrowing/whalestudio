import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.ThetaOfCsdR
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.ResidualRigidity.AllPlaceRigidityResidual
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PInfAsc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatGLOfInvT
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfinitesimalCharacterConjugateStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvariantHermitianFormStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRightHaarMeasureStatement
import Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.LieInvariants.InvariantOfLieOneLEqZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryLocalPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfNodupSumMultisetOfEq

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Rig

namespace CuspidalConjugateSelfDual

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem hasInfChar_thetaSub {a : ℕ} (P : CuspSub E a) (τ : E →+* ℂ) (m : Multiset ℂ)
    (hm : P.HasInfChar (ComplexEmbedding.conjugate τ) m) :
    (GlobalTheory.ThetaPull.thetaSub P).HasInfChar τ (m.map Neg.neg) := by
  refine ⟨by rw [Multiset.card_map, hm.1], ?_⟩
  rintro u _ ⟨φ, hφ, rfl⟩
  change cap τ u (GlobalTheory.ThetaPull.pull E a φ) = _ • GlobalTheory.ThetaPull.pull E a φ
  rw [GlobalTheory.ThetaPull.cap_pull, LinearMap.smul_apply, hm.2 _ φ hφ, smul_smul, map_smul]
  congr 1
  have e : ((m.map Neg.neg).map (u + ·)) = (m.map (-u + ·)).map Neg.neg := by
    rw [Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl fun z _ => ?_
    simp only [Function.comp_apply]
    ring
  rw [e, Multiset.prod_map_neg, Multiset.card_map, hm.1]

theorem conj_of_mem_infOfWeight {n : ℕ} (lam : DomWeight n) {x : ℂ} (hx : x ∈ infOfWeight lam) :
    (starRingEnd ℂ) x = x := by
  obtain ⟨k, -, rfl⟩ := Multiset.mem_map.1 hx
  simp [map_div₀, map_ofNat]

theorem hasInfChar_of_sigma {a b : ℕ} {π : CuspSub E a} {π' : CuspSub E b}
    (h : (⟨a, CG.mk π⟩ : Σ c, CG E c) = ⟨b, CG.mk π'⟩) {τ : E →+* ℂ} {m : Multiset ℂ} (hm : π.HasInfChar τ m) :
    π'.HasInfChar τ m := by
  obtain ⟨rfl, he⟩ := Sigma.mk.inj_iff.mp h
  have hi : π.Iso π' := Quotient.exact (eq_of_heq he)
  exact hi.hasInfChar hm

theorem isCsd_of_sigma {a b : ℕ} {π : CuspSub E a} {π' : CuspSub E b}
    (h : (⟨a, π⟩ : Σ c, CuspSub E c) = ⟨b, π'⟩) (hc : π.IsCsd) : π'.IsCsd := by
  obtain ⟨rfl, he⟩ := Sigma.mk.inj_iff.mp h
  obtain rfl := eq_of_heq he
  exact hc

theorem isCsd_of_sigma_theta {a : ℕ} {π : CuspSub E a}
    (h : (⟨a, CG.mk (GlobalTheory.ThetaPull.thetaSub π)⟩ : Σ c, CG E c) = ⟨a, CG.mk π⟩) : π.IsCsd :=
  GlobalTheory.ThetaPull.isCsd_of_iso (Quotient.exact (eq_of_heq (Sigma.mk.inj h).2))

theorem conjPl_cw (w : HeightOneSpectrum (𝓞 E)) : ConjPl w (GlobalTheory.ThetaSatake.cw w) := by
  refine ⟨GlobalTheory.DefU.LocRet.under_conjSrc w, ?_⟩
  by_cases h : GlobalTheory.ThetaSatake.cw w = w
  · exact Or.inr ((GlobalTheory.ConjAtPlace.conjSrc_eq_iff w).1 h)
  · exact Or.inl h

theorem map_inv_sum {ι : Type} [Fintype ι] (f : ι → Multiset ℂˣ) :
    (∑ i, f i).map (·⁻¹) = ∑ i, (f i).map (·⁻¹) :=
  map_sum (Multiset.mapAddMonoidHom (·⁻¹)) f Finset.univ

theorem sum_rev_map {d : ℕ} (f : Fin d → Multiset ℂˣ) :
    ∑ k : Fin d, (f k.rev).map (·⁻¹) = (∑ k, f k).map (·⁻¹) := by
  rw [map_inv_sum]
  exact Fintype.sum_equiv Fin.revPerm _ _ fun k => by rw [Fin.revPerm_apply]

variable (E) in

def nuT (s : ℝ) : Formalism.L2.Host.HChar E := GlobalTheory.ThetaPull.thetaChar (GlobalTheory.HeckeGal.Model.absPow E (-s))

theorem isAbsPow_nuT (s : ℝ) : (nuT E s).IsAbsPow s := by
  have h := GlobalTheory.ThetaPull.isAbsPow_thetaChar (GlobalTheory.HeckeGal.Model.absPow_isAbsPow E (-s))
  rwa [neg_neg] at h

variable (E) in

def muT (d : ℕ) (k : Fin d) : Formalism.L2.Host.HChar E := GlobalTheory.HeckeGal.Model.absPow E (-spehExp d k.rev)

omit [IsCMField E] in
theorem isAbsPow_muT (d : ℕ) (k : Fin d) : (muT E d k).IsAbsPow (spehExp d k) := by
  have e : -spehExp d k.rev = spehExp d k := by rw [InfinitesimalCharacterAscent.spehExp_rev, neg_neg]
  show (GlobalTheory.HeckeGal.Model.absPow E (-spehExp d k.rev)).IsAbsPow (spehExp d k)
  rw [e]
  exact GlobalTheory.HeckeGal.Model.absPow_isAbsPow E _

end CuspidalConjugateSelfDual

open CuspidalConjugateSelfDual in

theorem rCuspCsd : RCuspCsd := by
  intro hJ hSS hStr E _ _ _ n D hr ht i a d P ha hd hu hn he
  have hx : ∀ j, ∃ (a' d' : ℕ) (P' : CuspSub E a'), 1 ≤ a' ∧ 1 ≤ d' ∧ P'.IsUnitary ∧ IsNormalised P' ∧
      AscEmb (D.V j) P' d' ∧ (j = i → (⟨a', P'⟩ : Σ b, CuspSub E b) = ⟨a, P⟩) := fun j => by
    by_cases h : j = i
    · subst h
      exact ⟨a, d, P, ha, hd, hu, hn, he, fun _ => rfl⟩
    · obtain ⟨a', d', P', h1, h2, h3, h4, h5⟩ := hStr E n D hr j
      exact ⟨a', d', P', h1, h2, h3, h4, h5 P' (Setoid.refl (α := CuspSub E a') P'), fun e => absurd e h⟩
  choose A Dd PP hA hDd hU hN hE hI using hx
  have hW : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ j, ∃ b : Fin (Dd j) → Multiset ℂˣ,
      (∀ k, (CG.mk ((PP j).twist (nuT E (spehExp (Dd j) k)))).HasSat w (b k)) ∧
      GlobalTheory.LGrp.IsSpherical (D.σ j w).ρ (GlobalTheory.LFun.KGL w (D.N j)) ∧ GlobalTheory.LFun.HasSatGL w (D.σ j w).ρ (∑ k, b k) :=
    Filter.eventually_all.2 fun j => hSS E (D.N j) (A j) (Dd j) (D.V j) (PP j) (D.σ j) (D.pos j) (D.discrete j)
      (hU j) (hN j) (hE j) (D.loc j) (fun k => nuT E (spehExp (Dd j) k)) (fun k => isAbsPow_nuT _)
  have hinj : Function.Injective (GlobalTheory.ThetaSatake.cw (E := E)) :=
    Function.LeftInverse.injective (g := GlobalTheory.ThetaSatake.cw) fun v => GlobalTheory.ThetaPull.conjSrc_conjSrc v
  have hC : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ j, ∃ c : Fin (Dd j) → Multiset ℂˣ,
      (∀ k, (CG.mk ((PP j).twist (muT E (Dd j) k))).HasSat (GlobalTheory.ThetaSatake.cw w) (c k)) ∧
      GlobalTheory.LGrp.IsSpherical (D.σ j (GlobalTheory.ThetaSatake.cw w)).ρ (GlobalTheory.LFun.KGL (GlobalTheory.ThetaSatake.cw w) (D.N j)) ∧
      GlobalTheory.LFun.HasSatGL (GlobalTheory.ThetaSatake.cw w) (D.σ j (GlobalTheory.ThetaSatake.cw w)).ρ (∑ k, c k) :=
    hinj.tendsto_cofinite.eventually (Filter.eventually_all.2 fun j => hSS E (D.N j) (A j) (Dd j) (D.V j) (PP j)
      (D.σ j) (D.pos j) (D.discrete j) (hU j) (hN j) (hE j) (D.loc j) (fun k => muT E (Dd j) k)
      (fun k => isAbsPow_muT _ _))
  obtain ⟨s, hs⟩ := hJ.unitary (ι := Σ j, Fin (Dd j)) (κ := Σ j, Fin (Dd j)) (m := fun x => A x.1)
    (m' := fun x => A x.1) (fun x => CG.mk (GlobalTheory.ThetaPull.thetaSub (PP x.1))) (fun x => CG.mk (PP x.1))
    (fun x => hA x.1) (fun x => hA x.1)
    (fun x => (CG.isUnitary_mk _).2 (GlobalTheory.SpehPair.isUnitary_of_isNormalised
      (GlobalTheory.ThetaPull.isNormalised_thetaSub (hN x.1))))
    (fun x => (CG.isUnitary_mk _).2 (hU x.1)) (nuT E) isAbsPow_nuT (fun x => spehExp (Dd x.1) x.2)
    (fun x => spehExp (Dd x.1) x.2) (by
      filter_upwards [hW, hC, ht] with w hw hc hθ
      choose b hb1 hb2 hb3 using hw
      choose c hc1 hc2 hc3 using hc
      obtain ⟨Bt, ⟨bw, hbw, hbsum⟩, hconj⟩ := hθ
      obtain ⟨bc, hbc, hbcsum⟩ := hconj _ (conjPl_cw w)
      have e1 : ∀ j, bw j = ∑ k, b j k := fun j => GlobalTheory.LFun.HasSatGL.unique (hbw j).2 (hb3 j)
      have e2 : ∀ j, bc j = ∑ k, c j k := fun j => GlobalTheory.LFun.HasSatGL.unique (hbc j).2 (hc3 j)
      refine ⟨fun x => (c x.1 x.2.rev).map (·⁻¹), fun x => b x.1 x.2, fun x => ?_, fun x => hb1 x.1 x.2, ?_⟩
      · have h := hc1 x.1 x.2.rev
        simp only [muT, Fin.rev_rev] at h
        show ((CG.mk (GlobalTheory.ThetaPull.thetaSub (PP x.1))).twist (GlobalTheory.ThetaPull.thetaChar
          (GlobalTheory.HeckeGal.Model.absPow E (-spehExp (Dd x.1) x.2)))).HasSat w ((c x.1 x.2.rev).map (·⁻¹))
        rw [CG.twist_mk, ← GlobalTheory.ThetaPull.thetaSub_twist]
        exact GlobalTheory.ThetaSatake.hasSat_thetaSub _ w _ h
      · rw [Fintype.sum_sigma, Fintype.sum_sigma, Finset.sum_congr rfl fun j _ => sum_rev_map (c j),
          ← map_inv_sum (fun j => ∑ k, c j k), ← Finset.sum_congr rfl fun j _ => e2 j,
          ← Finset.sum_congr rfl fun j _ => e1 j, hbcsum, hbsum, Multiset.map_map]
        simp)
  have hstr := GlobalTheory.Rigid.strings_eq_of_equiv
    (fun j => (⟨A j, CG.mk (GlobalTheory.ThetaPull.thetaSub (PP j))⟩ : Σ b, CG E b)) Dd
    (fun j => (⟨A j, CG.mk (PP j)⟩ : Σ b, CG E b)) Dd s fun x => hs x
  obtain ⟨s0, hs0⟩ := GlobalTheory.T.multiset_of_strings_determines_points_degrees _ Dd _ Dd hDd hDd hstr
  have hfix : s0 i = i := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    obtain ⟨lam, hlam⟩ := hr τ
    obtain ⟨m0, hm0, e0⟩ := infAsc_holds E (D.N i) (A i) (Dd i) (D.V i) (PP i) (D.discrete i) (hE i) τ _
      (D.inf i τ)
    obtain ⟨m1, hm1, -⟩ := infAsc_holds E (D.N i) (A i) (Dd i) (D.V i) (PP i) (D.discrete i) (hE i)
      (ComplexEmbedding.conjugate τ) _ (D.inf i _)
    obtain ⟨m2, hm2, e2⟩ := infAsc_holds E (D.N (s0 i)) (A (s0 i)) (Dd (s0 i)) (D.V (s0 i)) (PP (s0 i))
      (D.discrete _) (hE _) τ _ (D.inf _ τ)
    obtain ⟨μ, hμ1, hμ2⟩ := GlobalTheory.T.exists_right_haar_measure E (A i)
    have := hμ1
    have := hμ2
    obtain ⟨B, hB⟩ := GlobalTheory.T.exists_invariant_hermitian_form PositivityTheory.Rg.HF.GL.cuspFormsBoundedGL E (A i) μ (PP i) (hN i)
    have hconj := GlobalTheory.T.infinitesimal_character_conjugate E (A i) (PP i) B hB τ m0 m1 hm0 hm1
    have hθ := hasInfChar_of_sigma (hs0 i).1 (hasInfChar_thetaSub (PP i) τ m1 hm1)
    have hmem : ∀ z ∈ m0, z + (spehExp (Dd i) ⟨0, hDd i⟩ : ℂ) ∈ D.m i τ := fun z hz => by
      rw [e0]
      exact Multiset.mem_sum.2 ⟨⟨0, hDd i⟩, Finset.mem_univ _, Multiset.mem_map_of_mem _ hz⟩
    have hreal : ∀ z ∈ m0, (starRingEnd ℂ) z = z := fun z hz => by
      have h1 : z + (spehExp (Dd i) ⟨0, hDd i⟩ : ℂ) ∈ ∑ j, D.m j τ :=
        Multiset.mem_of_le (Finset.single_le_sum (f := fun j => D.m j τ) (fun _ _ => Multiset.zero_le _)
          (Finset.mem_univ i)) (hmem z hz)
      rw [hlam] at h1
      have h2 := conj_of_mem_infOfWeight lam h1
      rw [map_add, Complex.conj_ofReal] at h2
      exact add_right_cancel h2
    have h20 : m2 = m0 := by
      rw [hm2.unique hθ, hconj, Multiset.map_map]
      conv_rhs => rw [← Multiset.map_id m0]
      refine Multiset.map_congr rfl fun z hz => ?_
      simp [hreal z hz]
    have heq : D.m i τ = D.m (s0 i) τ := by
      rw [e0, e2, h20, (hs0 i).2]
    have hne : D.m i τ ≠ 0 := by
      obtain ⟨z, hz⟩ := Multiset.card_pos_iff_exists_mem.1 (by rw [hm0.1]; exact hA i)
      exact fun h0 => by simpa [h0] using hmem z hz
    exact (GlobalTheory.eq_of_nodup_sum_multiset_of_eq (Fin D.c) (fun j => D.m j τ)
      (by rw [hlam]; exact GlobalTheory.DefiniteBC.nodup_infOfWeight lam) i (s0 i) hne heq).symm
  have hcsd : (PP i).IsCsd := isCsd_of_sigma_theta (by have h := (hs0 i).1; rwa [hfix] at h)
  exact isCsd_of_sigma (hI i rfl) hcsd

end PositivityTheory.Rg.BcB.F.Rig

end
