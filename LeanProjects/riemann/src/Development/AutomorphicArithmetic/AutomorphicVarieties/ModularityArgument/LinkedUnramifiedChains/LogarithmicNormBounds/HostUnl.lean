import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.LogarithmicNormBounds.LinkedUnlEOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostOk
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.CzBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IrrOpen
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.LevelAt
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.GaussianFieldRangeEqKerQuarticChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RestrictionToDecompositionGroup
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.LkHost
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.HostEx
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTerMore

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete
  UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Pr.IsCD.isLocalHom

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.Th UpperTheory.V.Z.J UpperTheory.V.U3 UpperTheory.V.UnitaryThreeInertia UpperTheory.V.Alg UpperTheory.V.Aut

section Local
open Matrix IsLocalRing
private theorem totDisc_quot {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    TotallyDisconnectedSpace (G ⧸ N) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_one]
  refine Set.eq_singleton_iff_unique_mem.2 ⟨mem_connectedComponent, fun y hy => ?_⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  by_contra hx
  have hx' : x ∉ N := fun h => hx ((QuotientGroup.eq_one_iff x).2 h)
  have ho : IsOpen {g : G | g * x ∉ N} := hN.isOpen_compl.preimage (continuous_mul_const x)
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho (by simpa using hx')
  let V : Subgroup (G ⧸ N) := U.toSubgroup.map (QuotientGroup.mk' N)
  have hVo : IsOpen (V : Set (G ⧸ N)) := QuotientGroup.isOpenMap_coe _ U.isOpen'
  have hV : IsClopen (V : Set (G ⧸ N)) := ⟨V.isClosed_of_isOpen hVo, hVo⟩
  obtain ⟨u, hu, hux⟩ := hV.connectedComponent_subset V.one_mem hy
  exact hU (U.toSubgroup.inv_mem hu) (QuotientGroup.eq.1 hux)
end Local

private theorem conj_left {G R : Type} [Group G] [CommRing R] (r : G →* GG 3 R) (h : GL (Fin 3) R) (g : G)
    (hg : (r g).right = 1) : (conjBy h r g).left = h * (r g).left * h⁻¹ := by
  have e : conjBy h r g = GG.ofGL h * r g * GG.ofGL h⁻¹ := by
    rw [map_inv]; rfl
  rw [e, SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.left_inl,
    SemidirectProduct.left_inl, SemidirectProduct.right_inl, sgnAct_one, SemidirectProduct.mul_right,
    SemidirectProduct.right_inl, hg, mul_one, sgnAct_one]

open Matrix in
private theorem matIrr_conj {G R : Type} [Group G] [CommRing R] {m : ℕ} {U : Subgroup G}
    {a a' : G → Matrix (Fin m) (Fin m) R} (h : GL (Fin m) R)
    (e : ∀ g ∈ U, a g = ((h⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) * a' g * h) (H : MatIrr U a) :
    MatIrr U a' :=
  _root_.UpperTheory.Reformulated.B.G5.matIrr_conj h e H

private theorem val_of_even {Ω : Type} [Field Ω] (B : ValuationSubring Ω) {M : ℕ} (hM : Even M)
    (h : B.valuation ((4 : ℕ) : Ω) < 1) : B.valuation (M : Ω) < 1 := by
  obtain ⟨m, rfl⟩ := hM.two_dvd
  have h2 : B.valuation ((2 : ℕ) : Ω) < 1 := by
    by_contra h2
    rw [not_lt] at h2
    rw [show (4 : ℕ) = 2 * 2 from rfl, Nat.cast_mul, map_mul] at h
    exact absurd h (not_lt.2 (one_le_mul h2 h2))
  have hm : B.valuation (m : Ω) ≤ 1 := (B.valuation_le_one_iff _).2 (natCast_mem B m)
  rw [Nat.cast_mul, map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_right' hm) h2

private theorem unl_of_iso {l : ℕ} [Fact l.Prime] {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {n : ℕ} {M : ℕ} {m : Fin n → ℤ} {r r' : Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Qbar l)}
    (H : Unl l M m r) (h : Af.RepIso r r') : Unl l M m r' := fun w hw => by
  obtain ⟨A, hA, κ, ⟨χ, h1, h2, h3⟩, h4⟩ := H w hw
  exact ⟨A, hA, κ, ⟨χ, h1, h2.of_iso h, h3⟩, h4⟩

theorem UpperTheory.V.Z.J.hostUnlE :
    Af.HypothesesH → UnlEndLogNorm → ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], IsQi K → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), HostData l e ψ o₁ → ∀ (S : Finset Pl) (A : S → ValuationSubring Ω) (F : Frame c.O (Formalism.ConjugateSelfDual.G ℚ Ω) (Gam Ω S) S), IsHostFrame Ω c e ψ S A F → ∀ (g₁ : Gam Ω S), F.Marked g₁ → ∀ r : Gam Ω S →* GG 3 (PadicAlgCl l), F.IsCharZeroPt g₁ r → U3.TypeI F.η r → ∀ ρ : G K Ω →* GL (Fin 3) (Qbar l), (∀ s : G K Ω, (ρ s).val = (r (toGS Ω _ (s.restrictScalars ℚ))).mat) → Unl l N ![(e : ℤ), 0, -(e : ℤ)] ρ := by
  intro hH hU K _ _ _ hK Ω _ _ _ _ _ l hl c N _ e ψ o₁ hd S A F hF g₁ hg r hr hI ρ hρ
  have hN := hH.litN
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  haveI hcl := isClosed_NS Ω (S : Set Pl)
  haveI : TotallyDisconnectedSpace (Gam Ω S) := totDisc_quot _ hcl
  have ok := hostFrame_ok Ω c e ψ o₁ hd S A F hF
  obtain ⟨hmu, -, -, -⟩ := isCharZeroPt_basic F ok g₁ hg r hr
  haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := by
    open Formalism.GaloisCohomology UpperTheory.V.Base in
    exact (dvrFacts l c.O).2.2.1
  haveI : CharP (ResidueField c.O) l := by
    rw [CharP.charP_iff_prime_eq_zero hl.out, ← map_natCast (residue c.O), residue_eq_zero_iff,
      mem_maximalIdeal, mem_nonunits_iff, ← map_natCast (algebraMap ℤ_[l] c.O)]
    intro hu
    exact PadicInt.prime_p.not_unit (isUnit_of_map_unit _ _ hu)
  obtain ⟨σ, hσ, hσc⟩ := hF.cc
  have hv : (A F.vl).valuation (l : Ω) < 1 := by simpa using (hF.isOver F.vl (l : 𝓞 ℚ)).2 hF.vl
  have hfr := Fr.host_ex ⟨⟨hN.coh.lf, hN.coh.lt, hN.coh.le, hN.coh.gf, hN.coh.ge, hN.coh.pt⟩, hN.coh.uo, hN.coh.gw⟩
    Ω l c N e ψ o₁ hd σ hσ _ hv
  have hσ' : IsConjOm σ.toRingEquiv := hσ
  have hΨ : Chr.Psi l e (Chr.dirG ℚ Ω ψ) σ = 1 := by
    have h1 : cycZ ℚ Ω l σ = -1 := hσ'.cyc (E := ℚ)
    have h2 : Base.chiO ℚ Ω l c.O σ = -1 := by
      show Units.map (algebraMap ℤ_[l] c.O).toMonoidHom (cycZ ℚ Ω l σ) = -1
      rw [h1]
      apply Units.ext
      simp
    have h3 : (Chr.dirG ℚ Ω ψ σ : c.O) = (-1) ^ e := by
      rw [Chr.dirG, MonoidHom.comp_apply, (Chr.clsFacts ℚ Ω N).2.2.2.1 σ hσ', MulChar.coe_toUnitHom]
      exact hd.par
    apply Units.ext
    show ((Base.chiO ℚ Ω l c.O σ ^ (e : ℤ) * Chr.dirG ℚ Ω ψ σ : c.Oˣ) : c.O) = 1
    rw [h2, zpow_natCast, Units.val_mul, h3, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, ← mul_pow]
    simp
  have hram : ∀ B' : ValuationSubring Ω, ¬ Ine (F := ℚ) B' ≤ (UnitaryThreeInertia.eta4 Ω).ker →
      B'.valuation ((l * N : ℕ) : Ω) < 1 := by
    intro B' h
    refine val_of_even B' (hd.N_even.mul_left l) ?_
    by_contra h4
    refine h fun s hs => ?_
    have h5 : Chr.cls ℚ Ω 4 s = 1 := (Chr.clsFacts ℚ Ω 4).2.2.2.2 B' h4 hs
    rw [MonoidHom.mem_ker, UnitaryThreeInertia.eta4, Chr.dirG, MonoidHom.comp_apply, h5, map_one]
  have hk : Pr.LinkHyp c N e (UnitaryThreeInertia.eta4 Ω) σ (A F.vl) (l * N) :=
    ⟨hd.e_pos, dvd_rfl, mul_ne_zero hl.out.ne_zero (NeZero.ne N), hram, hv, hσ⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hlev := UnitaryThreeInertia.levelAt_of_pt Ω c e ψ o₁ hd S A F hF K hK g₁ hg r hr ρ hρ
  have hopen := UnitaryThreeInertia.matIrr_open Ω c e ψ o₁ hd S A F hF g₁ hg r hr hI
  obtain ⟨B, _, _, t, r', hr', ht⟩ := hr
  obtain ⟨g, rfl⟩ : ∃ g, toGS Ω _ g = g₁ := QuotientGroup.mk_surjective g₁
  rw [hF.π] at hσc
  have ho := Pr.ordPt_of_isPt Ω c e ψ o₁ hd S A F hF σ g hσc r' hr'
  have hη : ∀ g, F.η (toGS Ω _ g) = UnitaryThreeInertia.eta4 Ω g := fun g => by rw [← hF.η, hF.π]; rfl
  have hm : ∀ s, (r (toGS Ω _ s)).right = UnitaryThreeInertia.eta4 Ω s := fun s => (hmu _).trans (hη s)
  have hle : ∀ s ∈ (UnitaryThreeInertia.eta4 Ω).ker, (UnitaryThreeInertia.push B.val (r'.comp (toGS Ω _)) s).left =
      tor _ t * (r (toGS Ω _ s)).left * (tor _ t)⁻¹ := fun s hs => by
    rw [← conj_left r _ _ ((hm s).trans hs), ← ht]
    rfl
  have hrg := (UnitaryThreeInertia.gaussian_field_range_eq_ker_quartic_char.2 Ω K hK).1
  have hker : ∀ s : G K Ω, Base.galEmb ℚ K Ω s ∈ (UnitaryThreeInertia.eta4 Ω).ker := fun s => by
    rw [← hrg]
    exact ⟨s, rfl⟩
  let j : G K Ω →* (UnitaryThreeInertia.eta4 Ω).ker := (Base.galEmb ℚ K Ω).codRestrict _ hker
  let ρ' : G K Ω →* GL (Fin 3) (Qbar l) :=
    (glPart (UnitaryThreeInertia.eta4 Ω) (UnitaryThreeInertia.push B.val (r'.comp (toGS Ω _))) ho.red.mult).comp j
  have hiso : Af.RepIso ρ ρ' := ⟨tor _ t, fun s => by
    rw [show ρ s = (r (toGS Ω _ (Base.galEmb ℚ K Ω s))).left from Units.ext (hρ s)]
    exact hle _ (hker s)⟩
  have key := hU Ω l c N e ψ (UnitaryThreeInertia.eta4 Ω) σ g (A F.vl) _ hk hd.N_even hΨ hfr B _ ho
    (fun V hV hVη => matIrr_conj (tor _ t) (fun s hs => by
      rw [mats, GG.mat, GG.mat, hle s (hVη hs), ← Units.val_mul, ← Units.val_mul]
      congr 1
      group) (hopen V hV hVη)) K hK.1 (by rw [← Base.range_galEmb]; exact hrg.symm) ρ' (fun s => rfl)
    N NeZero.one_le (hlev.of_iso hiso)
  exact unl_of_iso key (Af.RepIso.symm' hiso)
