import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.RegXInst
import Formalism.LocalToGlobal.ProjectiveLattices.CurveLocInst
import Formalism.LocalToGlobal.ProjectiveLattices.LocRingPf
import Formalism.LocalToGlobal.ProjectiveLattices.TieInst
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtPf
import Formalism.LocalToGlobal.ProjectiveLattices.HtXfer
import Formalism.LocalToGlobal.ProjectiveLattices.CompTie
import Formalism.LocalToGlobal.ProjectiveLattices.AxHInst
import Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg
import Formalism.LocalToGlobal.ProjectiveLattices.CombAlgOfCombBound
import Formalism.LocalToGlobal.ProjectiveLattices.CurveInj
import Formalism.LocalToGlobal.ProjectiveLattices.LocalUnitReduction.IsUnitMkOfForallPrime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAE
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CountQAtStGenericSectionPrimes
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsRatioFormsAtPoints
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RealisationValuesEqValuedPointOrdersStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsEquivCoverPointsPlacesBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsGaussRingMapToCompletionStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ComponentRingAwayGenericSectionQuotientStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

namespace GlobalTheory.NetOrders

theorem exists_quot_maps {K' Fr : Type} [Field K'] [CommRing Fr] [Algebra K' Fr] (J : Ideal Fr)
    {ι : Type} [Fintype ι] {R : ι → Type} [∀ c, CommRing (R c)] [∀ c, Algebra K' (R c)]
    (φ : ∀ c, Fr →ₐ[K'] R c) (hinj : ∀ f : Fr, (∀ c, φ c f = 0) → f = 0)
    (hone : ∀ Q : Ideal Fr, Q.IsPrime → J ≤ Q → ∀ c c', RingHom.ker (φ c) ≤ Q →
      RingHom.ker (φ c') ≤ Q → c = c')
    (hloc : ∀ c (r : R c), ∃ a p : Fr,
      (∀ Q : Ideal Fr, Q.IsPrime → J ≤ Q → RingHom.ker (φ c) ≤ Q → p ∉ Q) ∧ φ c p * r = φ c a)
    {S : ι → Type} [∀ c, CommRing (S c)] [∀ c, Algebra K' (S c)] (χ : ∀ c, R c →ₐ[K'] S c)
    (hs : ∀ c, Function.Surjective (χ c)) (hk : ∀ c, RingHom.ker (χ c) = Ideal.map (φ c) J) :
    ∃ Ψ : ∀ c, (Fr ⧸ J) →ₐ[K'] S c, (∀ c x, Ψ c (Ideal.Quotient.mk J x) = χ c (φ c x)) ∧
      (∀ c, Function.Surjective (Ψ c)) ∧ (∀ a, (∀ c, Ψ c a = 0) → a = 0) ∧
      ∀ c c', c ≠ c' → ∃ a, Ψ c a = 0 ∧ Ψ c' a = 1 := by
  have hJ : ∀ c, ∀ x ∈ J, χ c (φ c x) = 0 := fun c x hx => by
    rw [← RingHom.mem_ker, hk]; exact Ideal.mem_map_of_mem _ hx
  have hJK : ∀ c, ∀ x ∈ J ⊔ RingHom.ker (φ c), χ c (φ c x) = 0 := fun c x hx => by
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add, map_add, hJ c a ha, (RingHom.mem_ker).1 hb, map_zero, add_zero]
  refine ⟨fun c => Ideal.Quotient.liftₐ J ((χ c).comp (φ c)) (hJ c), fun c x => rfl, fun c s => ?_,
    fun a ha => ?_, fun c c' hne => ?_⟩
  · obtain ⟨r, rfl⟩ := hs c s
    obtain ⟨a, p, hp, e⟩ := hloc c r
    have hu := LocalUnitReduction.isUnit_mk_of_forall_prime (I := J ⊔ RingHom.ker (φ c)) (p := p)
      fun Q hQ hle => hp Q hQ (le_sup_left.trans hle) (le_sup_right.trans hle)
    obtain ⟨q, hq⟩ := hu.exists_right_inv
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective q
    have h1 : p * q - 1 ∈ J ⊔ RingHom.ker (φ c) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hq, map_one, sub_self]
    have h2 := hJK c _ h1
    refine ⟨Ideal.Quotient.mk J (q * a), ?_⟩
    show χ c (φ c (q * a)) = _
    simp only [map_sub, map_mul, map_one] at h2 ⊢
    rw [← e, map_mul]
    linear_combination (χ c r) * h2
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.Quotient.eq_zero_iff_mem]
    refine LocalUnitReduction.mem_of_forall_sup_ker J φ hinj hone fun c => LocalUnitReduction.mem_sup_ker J φ (hloc c) ?_
    rw [← hk]; exact ha c
  · have htop : (J ⊔ RingHom.ker (φ c')) ⊔ RingHom.ker (φ c) = ⊤ := by
      by_contra hne'
      obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal _ hne'
      exact hne (hone Q hQ.isPrime (le_sup_left.trans (le_sup_left.trans hle)) c c' (le_sup_right.trans hle)
        (le_sup_right.trans (le_sup_left.trans hle)))
    obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 htop)
    refine ⟨Ideal.Quotient.mk J b, ?_, ?_⟩
    · show χ c (φ c b) = 0
      rw [(RingHom.mem_ker).1 hb, map_zero]
    · show χ c' (φ c' b) = 1
      have := congrArg (fun z => χ c' (φ c' z)) e
      simpa only [map_add, hJK c' a ha, zero_add, map_one] using this

theorem addVal_mul_pow {S : Type} [CommRing S] (u : AddValuation S (WithTop ℤ)) (a b : S) (m : ℕ) :
    u (a * b ^ m) = u a + m • u b := by
  rw [u.map_mul, u.map_pow]

open ReciprocityTheory.ChartRestriction.G.T0 (Data KTf KTp OmS TVar algOpKT) in
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem exists_equiv_places {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j)
    (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)
    {ι : Type} [Fintype ι] (Ω : ι → Type) [∀ c, Field (Ω c)] [∀ c, Algebra B.KO (Ω c)]
    (gF : ∀ c, X.Forms →ₐ[B.KO] Ω c)
    (hinj : ∀ (u : WeightFamilies.Wt D j) (F : B.Cusp j u), (∀ c, gF c (X.inc u F) = 0) → F = 0)
    (hsplit : ∀ (c : ι) (k : Fin N), ∃ g : B.Cusp j wL, gF c (X.inc wL g) = gF c (X.inc wL (w k)) ∧
      ∀ c', c' ≠ c → gF c' (X.inc wL g) = 0)
    (hB : ∀ c, CurveLoc.BirAt X N w (gF c)) (hC : ∀ c, CurveLoc.CountQAt X la N w (gF c))
    [FiniteDimensional (Kp X la N) (OsK X la w)] [IsReduced (OsK X la w)]
    {WT : Type} [AddCommGroup WT] {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)]
    [∀ c, Algebra B.KO (A c)] [∀ c, Algebra (𝓞 B.KO) (A c)] {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
    (d : Data B.KO ι Ω WT A) (hd : d.AxH 𝒜) (hs : d.S1) (eN : Fin (d.N + 1) ≃ Fin N)
    (hD : d.D = WeightFamilies.dimY D j) (h0 : ∀ c, gF c (X.inc wL (w (eN (d.jc c)))) ≠ 0)
    (hx : ∀ c k, d.x c k * gF c (X.inc wL (w (eN (d.jc c)))) = gF c (X.inc wL (w (eN ((d.jc c).succAbove k))))) :
    ∃ e : Pts (Op X la N) (OsK X la w) ≃ Σ c, {v // v ∈ d.PlOver la c}, ∀ ζ,
      fdeg ζ = d.fze hs (e ζ).1 (e ζ).2.1 ∧ ∃ κ : WithTop ℤ, κ ≠ ⊤ ∧ ∀ (m : ℕ) (F : X.Forms)
        (hF : Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N F ∈ Vw X la N (addL (wt0 D j) wL m)),
        ord (unifO X la N) ζ (toOsK X la w (CurveLoc.fr0 X la N w m F hF)) =
          d.Wres (e ζ).1 (e ζ).2.1 (gF (e ζ).1 F) + m • κ := by
  have hD' : d.D + 1 = WeightFamilies.dimY D j + 1 := by rw [hD]
  obtain ⟨f, φ, hflat, hloc, hmax, hres, hφ, hφK, hφT⟩ :=
    GlobalTheory.T.exists_gaussRing_map_to_completion D B P j X la N d.D d.N (Equiv.prodCongr (finCongr hD') eN)
  letI : ∀ c, Algebra (KTf B.KO d.D d.N) (OmS (Ω c) d.D d.N) := fun c => (d.KTtoS hs c).toAlgebra
  letI : ∀ c, Algebra (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (OmS (Ω c) d.D d.N) := fun c => d.algOp hs la c
  letI := algOpKT (K := B.KO) d.D d.N la
  haveI := ReciprocityTheory.ChartRestriction.G.T0.isFractionRing_Op (K := B.KO) d.D d.N la
  haveI := ReciprocityTheory.ChartRestriction.G.T0.Op_isDVR (K := B.KO) d.D d.N la
  haveI := fun c => (d.comp_facts hd hs la c).2.1
  haveI := fun c => (d.comp_facts hd hs la c).2.2.1
  haveI := fun c => (d.comp_facts hd hs la c).2.2.2.1
  letI : Algebra (KTf B.KO d.D d.N) (Kp X la N) := φ.toAlgebra
  letI : Algebra (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (Op X la N) := f.toAlgebra
  letI : Algebra (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (Kp X la N) :=
    ((algebraMap (Op X la N) (Kp X la N)).comp f).toAlgebra
  haveI : IsScalarTower (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (Op X la N) (Kp X la N) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (KTf B.KO d.D d.N) (Kp X la N) :=
    IsScalarTower.of_algebraMap_eq fun o => (hφ o).symm
  haveI : Module.Flat (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (Op X la N) := hflat
  haveI : IsLocalHom (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (Op X la N)) := hloc
  have hres' : Function.Surjective (IsLocalRing.ResidueField.map
      (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (Op X la N))) := by
    intro z
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
    obtain ⟨a, ha⟩ := hres x
    refine ⟨IsLocalRing.residue _ a, ?_⟩
    rw [IsLocalRing.ResidueField.map_residue, eq_comm, ← sub_eq_zero, ← map_sub,
      IsLocalRing.residue_eq_zero_iff]
    exact ha
  choose χ hχs hχk hχψ using fun c => GlobalTheory.T.componentRing_away_genericSection_quotient D B P j X la N wL w (Ω c) (gF c) d.D d.N hD' eN (d.jc c) (d.x c)
    (fun p => IsFractionRing.lift_algebraMap (g := (d.sH c).toRingHom) (hs c) p) hφK hφT (h0 c) (hx c)
  obtain ⟨Ψ, hΨ, hΨs, hΨi, hΨsep⟩ := exists_quot_maps (Jid X la w) (fun c => phiZ X la N (Ω c) (gF c) w)
    (CurveInj.fraction_zero_injective X la N Ω gF w hinj)
    (fun Q hQ _ c c' => CurveLoc.one_of_split X la N w Ω gF hsplit Q hQ c c')
    (fun c => CurveLoc.loc_of_bir X la N w (gF c) (hB c) (hC c)) χ hχs hχk
  haveI : CharZero (Kp X la N) := by
    haveI : CharZero (X.Kl la) := charZero_of_injective_algebraMap (algebraMap B.KO (X.Kl la)).injective
    exact charZero_of_injective_algebraMap (algebraMap (X.Kl la) (Kp X la N)).injective
  haveI := (integralClosure_dvr' (Op X la N) (Kp X la N) (OsK X la w)).2
  have hU : IsUnif (OsK X la w) (unifO X la N) :=
    isUnif_of_field (Kp X la N) (Op.irreducible_map X la N
      (Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible (X.Ol la))))
  let Ψ' : ∀ c, OsK X la w →ₐ[Kp X la N] Kp X la N ⊗[KTf B.KO d.D d.N] OmS (Ω c) d.D d.N := Ψ
  have key : ∀ c (m : ℕ) (F : X.Forms)
      (hF : Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N F ∈ Vw X la N (addL (wt0 D j) wL m)),
      Ψ' c (toOsK X la w (CurveLoc.fr0 X la N w m F hF)) =
        ((1 : Kp X la N) ⊗ₜ[KTf B.KO d.D d.N] algebraMap (Ω c) (OmS (Ω c) d.D d.N) (gF c F)) *
          χ c (CurveLoc.invS X la N w (gF c)) ^ m := fun c m F hF => by
    refine (hΨ c _).trans ?_
    rw [CurveLoc.phiZ_fraction_base, map_mul, map_pow, hχψ c]
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_equiv_coverPoints_places_baseChange (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (Op X la N) (KTf B.KO d.D d.N) (Kp X la N)
    hmax hres' ι (fun c => OmS (Ω c) d.D d.N) (OsK X la w) (unifO X la N) hU
    (fun c => (Ψ' c).restrictScalars (Op X la N)) hΨs hΨi hΨsep
  refine ⟨e.trans (Equiv.sigmaCongrRight fun c => Equiv.subtypeEquivRight fun v => by
    rw [d.plOver_eq hs la c]), fun ζ => ?_⟩
  obtain ⟨h1, u, hu, hord⟩ := he ζ
  refine ⟨h1, u (χ _ (CurveLoc.invS X la N w (gF (e ζ).1))), ?_, fun m F hF => ?_⟩
  · intro ht
    have := congrArg (fun z => u (χ _ z)) (CurveLoc.weight_zero_section_mul_inv X la N w (gF (e ζ).1))
    simp only [map_mul, map_one, AddValuation.map_mul, ht, add_top, AddValuation.map_one] at this
    exact WithTop.top_ne_zero this
  · exact (hord _).trans ((congrArg u (key (e ζ).1 m F hF)).trans ((addVal_mul_pow u _ _ m).trans
      (congrArg (· + _) (hu _))))

theorem toE_eq_nval {T : CDVR} {a : WithTop ℤ} {x : T.Fr} (h : toE a = nval T.V 1 x) :
    (x = 0 → a = ⊤) ∧ (x ≠ 0 → a = (vV T.V x : ℤ)) := by
  constructor
  · rintro rfl
    rw [nval_zero] at h
    cases a with
    | top => rfl
    | coe n => exact absurd h (EReal.coe_ne_top _)
  · intro hx
    rw [nval_of_ne hx] at h
    cases a with
    | top => exact absurd h.symm (EReal.coe_ne_top _)
    | coe n =>
      have h' : ((n : ℝ) : EReal) = _ := h
      rw [EReal.coe_eq_coe_iff, Nat.cast_one, div_one] at h'
      exact_mod_cast h'

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem comp_val_eq {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X}
    {hM : IntAtExt X E} {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData (xplus X E hM) ka wL wF}
    {la : HeightOneSpectrum (𝓞 B.KO)} {ζ : PtsG G la} {y : E.Pt' la} (h : SecPt ζ y)
    {ι : Type} (Ω : ι → Type) [∀ c, Field (Ω c)] [∀ c, Algebra B.KO (Ω c)]
    (gF : ∀ c, (xplus X E hM).Forms →ₐ[B.KO] Ω c)
    (hsplit : ∀ (c : ι) (u : WeightFamilies.Wt D j) (F : B.Cusp j u), ∃ g : B.Cusp j u,
      gF c ((xplus X E hM).inc u g) = gF c ((xplus X E hM).inc u F) ∧
      ∀ c', c' ≠ c → gF c' ((xplus X E hM).inc u g) = 0)
    (c : ι) (hB : CurveLoc.BirAt (xplus X E hM) G.N G.w (gF c)) (k0 : Fin G.N)
    (hk0 : gF c ((xplus X E hM).inc wL (G.w k0)) ≠ 0)
    (W : AddValuation (Ω c) (WithTop ℤ)) (κ : WithTop ℤ) (hκ : κ ≠ ⊤)
    (hW : ∀ (m : ℕ) (F : (xplus X E hM).Forms)
      (hF : Formalism.MainNotions.Gaps.EtaleWeightGaps.emb (xplus X E hM) la G.N F ∈ Vw (xplus X E hM) la G.N (addL (wt0 D j) wL m)),
      ord (unifO (xplus X E hM) la G.N) ζ
        (toOsK (xplus X E hM) la G.w (CurveLoc.fr0 (xplus X E hM) la G.N G.w m F hF)) = W (gF c F) + m • κ)
    (Z : ι) (v : AddValuation (Ω Z) (WithTop ℤ)) (s : WeightFamilies.Wt D j → ℤ)
    (hv : ∀ (u : WeightFamilies.Wt D j) (F : B.Cusp j u),
      (gF Z ((xplus X E hM).inc u F) = 0 → h.ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb (xplus X E hM) la G.N (X.inc u F)) = 0) ∧
      (gF Z ((xplus X E hM).inc u F) ≠ 0 → h.ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb (xplus X E hM) la G.N (X.inc u F)) ≠ 0 ∧
        vV h.T.V (h.ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb (xplus X E hM) la G.N (X.inc u F))) =
          WithTop.untopD 0 (v (gF Z ((xplus X E hM).inc u F))) + s u)) :
    (⟨Z, v⟩ : Σ c, AddValuation (Ω c) (WithTop ℤ)) = ⟨c, W⟩ := by
  have hb : h.ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0) ≠ 0 := h.s0.ne_zero
  have key : ∀ (m : ℕ) (F : B.Cusp j (addL (wt0 D j) wL m)),
      toE (W (gF c ((xplus X E hM).inc _ F)) + m • κ) =
        nval h.T.V 1 (h.ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb (xplus X E hM) la G.N (X.inc _ F)) *
          (h.ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0))⁻¹ ^ m) := by
    intro m F
    rw [← hW m _ (emb_mem_Vw (xplus X E hM) la G.N _ F), h.ord]
    congr 1
    exact h.lift_frac m _
  have hWt : ∀ a : Ω c, a ≠ 0 → W a ≠ ⊤ := fun a ha ht => ha ((AddValuation.top_iff W).1 ht)
  obtain ⟨κ, rfl⟩ := WithTop.ne_top_iff_exists.1 hκ
  obtain rfl : Z = c := by
    by_contra hne
    obtain ⟨k, hk⟩ := GlobalTheory.ConstRatio.ratio_large (xplus X E hM) G.w (gF c) hB k0 hk0 1
    obtain ⟨-, d, hd, -⟩ := hk (k + 1) (Nat.lt_succ_self k)
    obtain ⟨g, hg1, hg2⟩ := hsplit c _ d
    have h1 := (toE_eq_nval (key _ g)).1 (by rw [(hv _ g).1 (hg2 Z hne), zero_mul])
    rw [← WithTop.coe_nsmul, WithTop.add_eq_top] at h1
    rcases h1 with h1 | h1
    · exact hWt _ (hg1 ▸ hd) h1
    · exact WithTop.coe_ne_top h1
  congr 1
  apply AddValuation.ext
  intro a
  by_cases ha : a = 0
  · rw [ha, v.map_zero, W.map_zero]
  have hvt : ∀ a : Ω Z, a ≠ 0 → v a ≠ ⊤ := fun a ha ht => ha ((AddValuation.top_iff v).1 ht)
  obtain ⟨k, hk⟩ := GlobalTheory.ConstRatio.ratio_large (xplus X E hM) G.w (gF Z) hB k0 hk0 a
  obtain ⟨n, d, hd, hn⟩ := hk (k + 1) (Nat.lt_succ_self k)
  have hn0 : gF Z ((xplus X E hM).inc _ n) ≠ 0 := hn ▸ mul_ne_zero ha hd
  have hp := pow_ne_zero (k + 1) (inv_ne_zero hb)
  obtain ⟨n1, n2⟩ := (hv _ n).2 hn0
  obtain ⟨d1, d2⟩ := (hv _ d).2 hd
  have n3 := (toE_eq_nval (key _ n)).2 (mul_ne_zero n1 hp)
  have d3 := (toE_eq_nval (key _ d)).2 (mul_ne_zero d1 hp)
  rw [vV_mul n1 hp, n2, hn, W.map_mul, v.map_mul] at n3
  rw [vV_mul d1 hp, d2] at d3
  obtain ⟨va, hva⟩ := WithTop.ne_top_iff_exists.1 (hvt a ha)
  obtain ⟨Wa, hWa⟩ := WithTop.ne_top_iff_exists.1 (hWt a ha)
  obtain ⟨vd, hvd⟩ := WithTop.ne_top_iff_exists.1 (hvt _ hd)
  obtain ⟨Wd, hWd⟩ := WithTop.ne_top_iff_exists.1 (hWt _ hd)
  rw [← hva, ← hWa, ← hvd, ← hWd] at n3
  rw [← hvd, ← hWd] at d3
  rw [← hva, ← hWa]
  simp only [← WithTop.coe_nsmul, ← WithTop.coe_add, WithTop.untopD_coe, WithTop.coe_inj] at n3 d3 ⊢
  omega

open ReciprocityTheory.ChartRestriction.G.T0 (Data) in
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem net_eq {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X}
    {hM : IntAtExt X E} {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (xplus X E hM) ka wL wF)
    {ι : Type} [Fintype ι] (Ω : ι → Type) [∀ c, Field (Ω c)] [∀ c, Algebra B.KO (Ω c)]
    (gF : ∀ c, (xplus X E hM).Forms →ₐ[B.KO] Ω c) (val : ∀ c (u : WeightFamilies.Wt D j), B.Cusp j u → Ω c)
    (hval : ∀ c u F, gF c ((xplus X E hM).inc u F) = val c u F)
    (hinj : ∀ (u : WeightFamilies.Wt D j) (F : B.Cusp j u), (∀ c, val c u F = 0) → F = 0)
    (hsplit : ∀ (c : ι) (u : WeightFamilies.Wt D j) (F : B.Cusp j u), ∃ g : B.Cusp j u,
      val c u g = val c u F ∧ ∀ c', c' ≠ c → val c' u g = 0)
    (hB : ∀ c, CurveLoc.BirAt (xplus X E hM) G.N G.w (gF c))
    (hC : ∀ la c, CurveLoc.CountQAt (xplus X E hM) la G.N G.w (gF c))
    (y : ∀ la, PtsG G la → E.Pt' la) (hw : ∀ la ζ, SecPt ζ (y la ζ)) (g0 : B.Cusp j wF)
    (hcur : ∀ la, (secQ (y la) (hw la) g0).InCurve)
    {WT : Type} [AddCommGroup WT] {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)]
    [∀ c, Algebra B.KO (A c)] [∀ c, Algebra (𝓞 B.KO) (A c)] {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
    (d : Data B.KO ι Ω WT A) (hd : d.AxH 𝒜) (hs : d.S1) (eN : Fin (d.N + 1) ≃ Fin G.N)
    (hD : d.D = WeightFamilies.dimY D j) (h0 : ∀ c, val c wL (G.w (eN (d.jc c))) ≠ 0)
    (hx : ∀ c k, d.x c k * val c wL (G.w (eN (d.jc c))) = val c wL (G.w (eN ((d.jc c).succAbove k))))
    (het : ∀ c, val c _ G.et ≠ 0)
    (s : ∀ c, AddValuation (Ω c) (WithTop ℤ) → WeightFamilies.Wt D j → ℤ)
    (hord : ∀ c v, d.ord c v (d.n1 • d.wde) (d.et c) = WithTop.untopD 0 (v (val c _ G.et)) + s c v (etWt D j G.iet))
    (hpt : ∀ la (ζ : PtsG G la), ∃ (Z : ι) (v : AddValuation (Ω Z) (WithTop ℤ)),
      ∀ (u : WeightFamilies.Wt D j) (F : B.Cusp j u),
      (val Z u F = 0 → (hw la ζ).ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb (xplus X E hM) la G.N (X.inc u F)) = 0) ∧
      (val Z u F ≠ 0 → (hw la ζ).ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb (xplus X E hM) la G.N (X.inc u F)) ≠ 0 ∧
        vV (hw la ζ).T.V ((hw la ζ).ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb (xplus X E hM) la G.N (X.inc u F))) =
          WithTop.untopD 0 (v (val Z u F)) + s Z v u)) (Gc PH Prw Pet : ℝ) :
    NetTie d hd hs G (fun la => secQ (y la) (hw la) g0) Gc PH Prw Pet := by
  intro la
  haveI := (hcur la).1
  haveI := (hcur la).2.1
  simp only [← hval] at hinj hsplit h0 hx het hord hpt
  obtain ⟨e, he⟩ := exists_equiv_places (xplus X E hM) la G.N G.w Ω gF hinj (fun c k => hsplit c wL (G.w k)) hB
    (hC la) d hd hs eN hD h0 hx
  refine finsum_eq_of_bijective e e.bijective fun ζ => ?_
  obtain ⟨h1, κ, hκ, hW⟩ := he ζ
  obtain ⟨Z, v, hv⟩ := hpt la ζ
  have hZ := comp_val_eq (hw la ζ) Ω gF hsplit (e ζ).1 (hB _) _ (h0 _) _ κ hκ hW Z v (s Z v) hv
  obtain ⟨e1, e2⟩ := (hv _ G.et).2 (het Z)
  rw [← hord] at e2
  have e3 : d.ord Z v (d.n1 • d.wde) (d.et Z) =
      d.ord (e ζ).1 (d.Wres (e ζ).1 (e ζ).2.1) (d.n1 • d.wde) (d.et (e ζ).1) :=
    congrArg (fun p : Σ c, AddValuation (Ω c) (WithTop ℤ) => d.ord p.1 p.2 (d.n1 • d.wde) (d.et p.1)) hZ
  have e4 := normalized_valuation_mul (hw la ζ).ep_pos _ e1
  rw [← (hw la ζ).hv, e2, e3] at e4
  show (ep (unifO (xplus X E hM) la G.N) ζ : ℝ) * (fdeg ζ : ℝ) * (E.vAt' la (y la ζ) (X.inc _ G.et)).toReal =
    ((1 : ℕ) : ℝ) * (d.fze hs (e ζ).1 (e ζ).2.1 : ℝ) *
      (d.ord (e ζ).1 (d.Wres (e ζ).1 (e ζ).2.1) (d.n1 • d.wde) (d.et (e ζ).1) : ℝ)
  rw [← e4, ← h1]
  push_cast
  ring

theorem ratio_single_mul {Ω M : Type} [Field Ω] (m : M) (a b : Ω) (hb : b ≠ 0) :
    ReciprocityTheory.ChartRestriction.G.T0.ratio (Ω := Ω) (AddMonoidAlgebra.single m a : AddMonoidAlgebra Ω M)
      (AddMonoidAlgebra.single m b) * b = a := by
  have hex : ∃ r : Ω, (AddMonoidAlgebra.single m a : AddMonoidAlgebra Ω M) = r • AddMonoidAlgebra.single m b :=
    ⟨a / b, by rw [AddMonoidAlgebra.smul_single', div_mul_cancel₀ _ hb]⟩
  unfold ReciprocityTheory.ChartRestriction.G.T0.ratio
  rw [dif_pos hex]
  have := hex.choose_spec
  rw [AddMonoidAlgebra.smul_single'] at this
  exact (AddMonoidAlgebra.single_right_injective this).symm

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem netTie_record : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) [Fintype (Comp (T.Q.Xo j) T.Q.c)] (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (g0 : (recB h.toLawsCore).Cusp j wF), CurveHyp h j hj hG ka wL wF G S g0 → GenValInjSt h j hG → CompSplitSt h j hG → BIRSt h j hj hG G → ∀ (y : ∀ la, PtsG G la → (extAll h j hj).Pt' la) (hw : ∀ la ζ, FromW (E := extAll h j hj) (hM := intAtExt_extAll h j hj) ζ (y la ζ)), (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InCurve) → (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InTie S) → j < D.R.m → ∀ (δ : ∀ Z : Comp (T.Q.Xo j) T.Q.c, AddValuation (Om Z) (WithTop ℤ) → Ix (T.Q.Dw j) → ℤ), OrdTie hG δ (trivialClassCondition (T.Q.Xo j) T.Q.c) (fun _ => Unit) (fun _ _ _ _ _ => True) → ∀ (d : ReciprocityTheory.ChartRestriction.G.T0.Data T.Q.c.F (Comp (T.Q.Xo j) T.Q.c) (fun Z => Om Z) (WTZ D.host.E) (fun Z => AC Z)) (hd : d.AxH (fun Z => AG Z)) (hs : d.S1) (eN : Fin (d.N + 1) ≃ Fin G.N), d.D = WeightFamilies.dimY D j → (∀ Z v, d.ord Z v = ordC (δ Z v) v) → d.wL = wtZ (wtA wL) wL.n → d.wF = wtZ (wtA wF) wF.n → (∀ k, d.w k = valC hG (wtA wL) wL.n (G.w (eN k)).1) → d.et = valC hG (wtA (wEt D j G.iet)) (wEt D j G.iet).n G.et.1 → d.n1 • d.wde = wtZ (wtA (wEt D j G.iet)) (wEt D j G.iet).n → ∀ (Gc PH Prw Pet : ℝ), NetTie (B := (recB h.toLawsCore)) d hd hs G (fun la => (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0)) Gc PH Prw Pet := by
  intro D T h j hj hG _ ka wL wF G S g0 hH hV hC hB y hw hcur htie _ δ hδ d hd hs eN hD hord _ _ hdw hdet hwt
    Gc PH Prw Pet
  have hT : GenFromTest (T.Q.Xo j) T.Q.c hG := fun Z => h.allTest j hj (Om Z) (genFr hG Z)
  have hpt := GlobalTheory.T.realisation_values_eq_valuedPoint_orders D T h j hj hG ka wL wF G S g0 hH hV hC hB y hw hcur htie δ hδ
  have hQ : CountQAtSt h j hj hG hT := GlobalTheory.SecCount.countQAtSt D T h j hj hG hT
  have hordC : ∀ (Z : Comp (T.Q.Xo j) T.Q.c) (v : AddValuation (Om Z) (WithTop ℤ)) a n f,
      ordC (δ Z v) v (wtZ a n) (valC hG a n f Z) =
        WithTop.untopD 0 (v (evC hG Z f)) + frW (δ Z v) (wtZ a n) := fun Z v a n f => by
    simp only [ordC, valC, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]
  have h0 : ∀ Z, evC hG Z (G.w (eN (d.jc Z))).1 ≠ 0 := fun Z h0 => hd.w_base Z (by
    rw [hdw]; simp only [valC, h0, AddMonoidAlgebra.single_zero])
  refine net_eq (X := recPJ h j hj) (E := extAll h j hj) (hM := intAtExt_extAll h j hj) G (fun Z => Om Z)
    (fun Z => formsEvR j hG hT Z) (fun Z u F => evC hG Z F.1) (fun Z u F => formsEvR_inc h j hj hG hT Z u F) hV hC
    (fun Z => birAt_of h j hj hG hT G hB Z) (fun la Z => hQ ka wL wF G S g0 la hH Z) y
    (fun la ζ => (hw la ζ).toSecPt) g0 hcur d hd hs eN hD h0 (fun Z k => ?_) (fun Z h0 => hd.et_ne Z ?_)
    (fun Z v u => frW (δ Z v) (wtZ (wtA u) u.n)) (fun Z v => ?_) (fun la ζ => ?_) Gc PH Prw Pet
  · unfold ReciprocityTheory.ChartRestriction.G.T0.Data.x
    rw [hdw, hdw]
    exact ratio_single_mul _ _ _ (h0 Z)
  · rw [hdet]
    have h0' : evC hG Z G.et.1 = 0 := h0
    simp only [valC, h0', AddMonoidAlgebra.single_zero]
  · rw [hord, hwt, hdet]
    exact hordC Z v _ _ _
  · obtain ⟨Z, v, -, -, hv⟩ := hpt la ζ
    exact ⟨Z, v, fun u F => ⟨(hv u F).1, fun hne => ⟨((hv u F).2 hne).1,
      ((hv u F).2 hne).2.trans (hordC Z v _ _ _)⟩⟩⟩

end GlobalTheory.NetOrders
