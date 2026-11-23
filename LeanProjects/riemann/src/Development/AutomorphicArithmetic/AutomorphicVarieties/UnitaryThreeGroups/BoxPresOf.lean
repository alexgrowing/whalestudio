import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.IsLocPres
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BoxAbs
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BoxCount
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DatFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DatLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.FinrankKerAdRepComplexConjSubOneEqBoxDef
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.NotPrimeDvdRelIndexKerInducedUnitaryRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsGaloisCyclotomicNegOneTrivialOnEtaPsi
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsFinitePlaceSetFactoringThroughGS
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.InertiaLeNormalIffKerLeAndInertiaLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsDecompositionFieldFrobeniusData
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.GaloisGroupPhiCondition
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.KillLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ExistsLocallyConstantDOneEqCocycleOfTameInertia
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

section SlopeTestRemainingChoices

variable {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] (η : Γ →* ℤˣ) (Ψ : Γ →* Oˣ)

private theorem adBar_eq_one (j : ℤ) {g : Γ} (h : rbar O η Ψ g = 1) : adBar O η Ψ j g = 1 := by
  refine LinearMap.ext fun Y => Subtype.ext ?_
  show emb (rbar O η Ψ g) * Y.1 * emb (rbar O η Ψ g⁻¹) = Y.1
  rw [map_inv, h, inv_one, map_one, one_mul, mul_one]

variable [TopologicalSpace Γ] [IsTopologicalGroup Γ]

omit [IsTopologicalGroup Γ] in
private theorem rbar_open (hη : IsLocallyConstant η) (hΨ : IsLocallyConstant (barChar O Ψ)) :
    IsOpen ((rbar O η Ψ).ker : Set Γ) :=
  ((hη.prodMk hΨ).comp fun p => (⟨tor _ p.2, p.1⟩ : GG 3 (ResidueField O))).isOpen_fiber 1

private theorem adBar_open (hη : IsLocallyConstant η) (hΨ : IsLocallyConstant (barChar O Ψ)) (j : ℤ) :
    IsOpen ((adBar O η Ψ j).ker : Set Γ) :=
  Subgroup.isOpen_mono (fun _ hg => adBar_eq_one η Ψ j hg) (rbar_open η Ψ hη hΨ)

private theorem locCond (l : ℕ) [Fact l.Prime] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]
    [Finite (ResidueField O)] [CharP (ResidueField O) l] (h2 : IsUnit (2 : O)) [CompactSpace Γ]
    [TotallyDisconnectedSpace Γ] [T2Space Γ] (hη : IsLocallyConstant η) (hΨ : IsLocallyConstant (barChar O Ψ))
    (hΨ' : ∀ j : ℤ, AdicCont (maximalIdeal O) fun g => ((Ψ g ^ j : Oˣ) : O)) (I N : Subgroup Γ) [I.Normal] [N.Normal]
    (hI : IsClosed (I : Set Γ)) (hN : IsClosed (N : Set Γ)) (hNI : N ≤ I) (h0 : ∀ n ∈ N, r0 η Ψ n = 1)
    (hi : ¬ l ∣ N.relIndex I) (hf : ∃ fr : Γ, (I ⊔ Subgroup.zpowers fr).topologicalClosure = ⊤)
    (hU : ∀ n : ℕ, ∃ U : Subgroup Γ, IsOpen (U : Set Γ) ∧ I ≤ U ∧ U.index = l ^ n) :
    (form6 O).IsLocCond (emb.comp (r0 η Ψ)) N (killCond (emb.comp (rbar O η Ψ)) N) :=
  kill_loc O _ ℤ wt6 (form6 O) h2 Γ _ ((baseLift O η Ψ hΨ').toLift hη) (blockPairingForm_normalises_baseLift O η (barChar O Ψ))
    (blockPairingForm_normalises_baseLift O η Ψ) N (fun n hn => by
      show emb (r0 η Ψ n) = 1
      rw [h0 n hn, map_one])
    fun j => exists_locallyConstant_dOne_eq_cocycle_of_tame_inertia l _ Γ _ (adBar O η Ψ j) (adBar_open η Ψ hη hΨ j) I N hI hN hNI
      (fun n hn => adBar_eq_one η Ψ j (by rw [← baseLift_map_residue, h0 n hn, map_one])) hi hf hU

end SlopeTestRemainingChoices

private theorem lc_desc {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] {π : X → Y}
    (hq : Topology.IsQuotientMap π) {f : Y → Z} (h : IsLocallyConstant fun x => f (π x)) : IsLocallyConstant f :=
  fun s => hq.isOpen_preimage.1 (h s)

set_option maxHeartbeats 800000 in
private theorem aux (hI : CohInp) (hP : LemmaP) {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ)
    [hl : Fact l.Prime] (hl2 : l ≠ 2) {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [CharP (ResidueField O) l] (h2 : IsUnit (2 : O))
    (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (hη : IsLocallyConstant η) (hΨ : IsLocallyConstant (barChar O Ψ))
    (hΨc' : CharCont Ψ) (cc : G ℚ Ω) (hcc : ∃ φ : Ω →+* ℂ, ∀ x, φ (cc x) = starRingEnd ℂ (φ x)) (hηc : η cc = -1)
    (hΨc : Ψ cc = 1) (ι : GQ l →* G ℚ Ω) (hι : Continuous ι) (hinj : Function.Injective ι) (Kill : Set (G ℚ Ω))
    (hKi : ∀ g, g ∈ Kill ↔ ∃ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 ∧ g ∈ Ine (F := ℚ) A ∧
      g ∈ (rbar O η Ψ).ker) (hK : ∀ g ∈ Kill, r0 η Ψ g = 1)
    (hg : ∃ g, η g = 1 ∧ barChar O Ψ g = 1 ∧ cycMod ℚ Ω l 1 g = -1)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (A : S → ValuationSubring Ω) (v₀ : S)
    (η' : GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) →* ℤˣ) (Ψ' : GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) →* Oˣ)
    (hS : ContainsAbove S l) (hA : ∀ v, IsPlaceOver (A v) v.1) (hr : ι.range = Dec (F := ℚ) (A v₀))
    (hv : ∀ v : S, ((l : ℕ) : 𝓞 ℚ) ∈ v.1.asIdeal ↔ v = v₀) (e1 : η'.comp (toGS Ω _) = η)
    (e2 : Ψ'.comp (toGS Ω _) = Ψ) :
    ∀ (U : Univ (GCond.noCondition O (η.comp ι) (Ψ.comp ι))) (I : Ideal U.R) (B : Univ (BoxCond Kill ι hι U I))
      (WB : WPres O ℤ (U.R ⧸ I)), IsLocPres U I WB → BoxPres B WB := by
  classical
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  obtain ⟨hΦ, _, _, _⟩ := UpperTheory.galois_group_phi_condition hI.gf Ω l S hS
  have hq : Topology.IsQuotientMap (toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) := QuotientGroup.isQuotientMap_mk _
  have hπ := hq.continuous
  have e1' : ∀ g, η' (toGS Ω _ g) = η g := DFunLike.congr_fun e1
  have e2' : ∀ g, Ψ' (toGS Ω _ g) = Ψ g := DFunLike.congr_fun e2
  have e3 : ∀ g, barChar O Ψ' (toGS Ω _ g) = barChar O Ψ g := fun g =>
    congrArg (Units.map (residue O).toMonoidHom) (e2' g)
  have e4 : ∀ g, rbar O η' Ψ' (toGS Ω _ g) = rbar O η Ψ g := fun g =>
    SemidirectProduct.ext (congrArg (tor _) (e3 g)) (e1' g)
  have e5 : ∀ g, r0 η' Ψ' (toGS Ω _ g) = r0 η Ψ g := fun g =>
    SemidirectProduct.ext (congrArg (tor _) (e2' g)) (e1' g)
  have hη' : IsLocallyConstant η' := lc_desc hq (by simpa only [e1'] using hη)
  have hΨ' : IsLocallyConstant (barChar O Ψ') := lc_desc hq (by simpa only [e3] using hΨ)
  have hΨ'' : ∀ j : ℤ, AdicCont (maximalIdeal O) fun g => ((Ψ' g ^ j : Oˣ) : O) := fun j n =>
    lc_desc hq (by simpa only [e2'] using hΨc' j n)
  let H := (rbar O η Ψ).ker
  have hHc : IsClosed (H : Set (G ℚ Ω)) := H.isClosed_of_isOpen (rbar_open _ _ hη hΨ)
  let Nq : {v : S // v ≠ v₀} → Subgroup (G ℚ Ω) := fun q => Ine (F := ℚ) (A q.1) ⊓ H
  have hKill := UpperTheory.inertia_le_normal_iff_ker_le_and_inertia_le Ω l S A v₀ hS hA hv H fun g hg => by
    show rbar O η Ψ g = 1
    rw [← e4, show toGS Ω _ g = 1 from hg, map_one]
  have hN0 : ∀ q, ∀ n ∈ Nq q, r0 η' Ψ' (toGS Ω _ n) = 1 := fun q n hn => by
    rw [e5]
    refine hK n ((hKi n).2 ⟨A q.1, fun h => q.2 ((hv q.1).1 ?_), hn.1, hn.2⟩)
    have h' := hA q.1 ((l : ℕ) : 𝓞 ℚ)
    have e : algebraMap ℚ Ω (((l : ℕ) : 𝓞 ℚ) : ℚ) = (l : Ω) := by simp
    rw [e] at h'
    exact h'.1 h
  have hNn : ∀ q, ((Nq q).subgroupOf (Dec (F := ℚ) (A q.1))).Normal := fun q => by
    haveI := (UpperTheory.exists_decompositionField_frobenius_data Ω (A q.1) q.1.1 (hA q.1)).2.1
    exact inferInstanceAs ((Ine (F := ℚ) (A q.1)).subgroupOf (Dec (F := ℚ) (A q.1)) ⊓ H.subgroupOf _).Normal
  have hNc : ∀ q, IsClosed (Nq q : Set (G ℚ Ω)) := fun q =>
    (UpperTheory.exists_decompositionField_frobenius_data Ω (A q.1) q.1.1 (hA q.1)).2.2.1.inter hHc
  have hNi : ∀ q, ¬ l ∣ (Nq q).relIndex (Ine (F := ℚ) (A q.1)) := fun q =>
    UpperTheory.not_prime_dvd_relIndex_ker_inducedUnitaryRep l _ hl2 η (barChar O Ψ) _
  have key := boxPres_abs hP l hl2 (toGS Ω _) hq hΦ hη' hΨ'' (Kill := Kill) hι
    (fun q : {v : S // v ≠ v₀} => Dec (F := ℚ) (A q.1)) Nq (fun q => inf_le_left.trans (Ine_le_Dec _))
    (fun M _ hM => ((forall_congr' fun g => imp_congr_left (hKi g)).trans (hKill M hM)).trans (and_congr_right' Subtype.forall'))
    hN0
    (fun q => by
      obtain ⟨d1, d2, d3, d4, d5⟩ := UpperTheory.exists_decompositionField_frobenius_data Ω (A q.1) q.1.1 (hA q.1)
      haveI := hNn q
      have hφ : Continuous ((toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))).comp (Dec (F := ℚ) (A q.1)).subtype) :=
        hπ.comp continuous_subtype_val
      refine locCond (η'.comp ((toGS Ω _).comp (Dec (F := ℚ) (A q.1)).subtype))
        (Ψ'.comp ((toGS Ω _).comp (Dec (F := ℚ) (A q.1)).subtype)) l h2 (hη'.comp_continuous hφ)
        (hΨ'.comp_continuous hφ) (fun j n => (hΨ'' j n).comp_continuous hφ) _ _ (d3.preimage continuous_subtype_val)
        ((hNc q).preimage continuous_subtype_val) (fun x hx => hx.1) (fun n hn => hN0 q n hn) ?_ d4
        fun n => d5 _ (pow_pos hl.out.pos n)
      rw [Subgroup.relIndex_subgroupOf (Ine_le_Dec _)]
      exact hNi q)
    (fun j => by
      obtain ⟨g, g1, g2, g3⟩ := hg
      have h := box_count hI Ω l _ _ hl2 S A v₀ hS hA hv ι hι hinj hr (adBar O η' Ψ' j)
        (adBar_open _ _ hη' hΨ' j) Nq (fun q => inf_le_left) hNn hNc
        (fun q n hn => adBar_eq_one _ _ j ((e4 n).trans hn.2)) hNi
        ⟨g, g3, adBar_eq_one _ _ j ((e4 g).trans (SemidirectProduct.ext (by
          show tor _ (barChar O Ψ g) = 1
          rw [g2, map_one]) g1))⟩ cc hcc
      have h2' : (2 : ResidueField O) ≠ 0 := map_ofNat (residue O) 2 ▸ (h2.map (residue O)).ne_zero
      have h3 := UpperTheory.finrank_ker_adRep_complexConj_sub_one_eq_boxDef O _ h2' η' (barChar O Ψ') (toGS Ω _ cc) ((e1' _).trans hηc)
        ((e3 _).trans (by
          show Units.map (residue O).toMonoidHom (Ψ cc) = 1
          rw [hΨc, map_one])) j
      exact ⟨h.1, h.2.trans (congrArg _ h3)⟩)
  subst e1 e2
  exact key

theorem UpperTheory.V.U3.boxPres :
    CohInp → LemmaP → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) (U : D.ULoc) (B : Univ (BoxCond D.Kill D.ι D.ι_cont U (D.loc.It U))) (WB : WPres c.O ℤ (U.R ⧸ D.loc.It U)),
      IsLocPres U (D.loc.It U) WB → BoxPres B WB := by
  intro hI hP Ω _ _ _ K _ _ _ l hl c N hN e ψ D U B WB hW
  obtain ⟨hc, hf, hlm, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  haveI := hc
  haveI : Finite (ResidueField c.O) := hf
  haveI : CharP (ResidueField c.O) l := (CharP.charP_iff_prime_eq_zero hl.out).2 (by
    rw [← map_natCast (residue c.O), residue_eq_zero_iff]; exact hlm)
  haveI : IsNoetherianRing c.O := @PrincipalIdealRing.isNoetherianRing c.O _ c.dvr.toIsPrincipalIdealRing
  obtain ⟨-, hηc, hΨc, hη, hΨ, hK, h2, -⟩ := dat_facts D
  obtain ⟨-, -, -, -, hinj, -⟩ := dat_loc D
  obtain ⟨S, A, v₀, η', Ψ', hS, hA, hr, hv, e1, e2⟩ := UpperTheory.exists_finite_place_set_factoring_through_GS D
  exact aux hI hP l D.gd.l_odd h2 D.η D.Ψ hη hΨ D.Ψ_cont D.cc D.conj hηc hΨc D.ι D.ι_cont hinj D.Kill
    (fun _ => Iff.rfl) hK (UpperTheory.exists_galois_cyclotomic_neg_one_trivial_on_eta_psi D) S A v₀ η' Ψ' hS hA hr hv e1 e2 U _ B WB hW
