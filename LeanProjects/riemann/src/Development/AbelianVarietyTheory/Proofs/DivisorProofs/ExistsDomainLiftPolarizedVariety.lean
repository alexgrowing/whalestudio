import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRingHom
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsLevelOverIntegers
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsSiegPre
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsLiftPrincipallyPolarisedAbelianSquareZero

noncomputable section

namespace GlobalTheory.SiegPt

section Algebra

open Polynomial IsLocalRing

theorem exists_valuationSubring_extension {R L k : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Field L]
    [Algebra R L] [Algebra.IsAlgebraic R L] (hinj : Function.Injective (algebraMap R L)) [Field k] [IsAlgClosed k]
    (r : R →+* k) : ∃ (V : ValuationSubring L) (ψ : R →+* V) (r' : V →+* k),
      V.subtype.comp ψ = algebraMap R L ∧ r'.comp ψ = r := by
  classical
  let p := RingHom.ker r
  haveI hp : p.IsPrime := RingHom.ker_isPrime r
  have hu : ∀ y : p.primeCompl, IsUnit (algebraMap R L y) := fun y => by
    refine IsUnit.mk0 _ fun h => y.2 ?_
    rw [hinj (h.trans (map_zero _).symm)]
    exact p.zero_mem
  let f : Localization.AtPrime p →+* L := IsLocalization.lift hu
  obtain ⟨V, hV, hloc⟩ := IsLocalRing.exists_factor_valuationRing f
  let ψ : R →+* V := (f.codRestrict V.toSubring hV).comp (algebraMap R _)
  have hψ : V.subtype.comp ψ = algebraMap R L := RingHom.ext fun x => IsLocalization.lift_eq hu x
  let ρ : R →+* ResidueField V := (residue V).comp ψ
  have hρ : ∀ x, ρ x = 0 ↔ x ∈ p := fun x => by
    show residue V (f.codRestrict V.toSubring hV (algebraMap R _ x)) = 0 ↔ _
    rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff, ← mem_nonunits_iff,
      ← mem_maximalIdeal]
    exact IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p) p x
  let ρ' : R ⧸ p →+* ResidueField V := Ideal.Quotient.lift p ρ fun x hx => (hρ x).2 hx
  have hρ' : Function.Injective ρ' := (injective_iff_map_eq_zero _).2 fun x hx => by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.Quotient.eq_zero_iff_mem.2 ((hρ x).1 hx)
  letI : Algebra (R ⧸ p) (ResidueField V) := ρ'.toAlgebra
  letI : Algebra (R ⧸ p) k := (RingHom.kerLift r).toAlgebra
  haveI : FaithfulSMul (R ⧸ p) (ResidueField V) := (faithfulSMul_iff_algebraMap_injective _ _).2 hρ'
  haveI : FaithfulSMul (R ⧸ p) k := (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective r)
  haveI : Algebra.IsAlgebraic (R ⧸ p) (ResidueField V) := ⟨fun x => by
    obtain ⟨x, rfl⟩ := residue_surjective x
    obtain ⟨q, hq, hqx⟩ := Algebra.IsAlgebraic.isAlgebraic (R := R) (x : L)
    letI : NormalizedGCDMonoid R := Nonempty.some inferInstance
    have h1 : aeval (x : L) q.primPart = 0 := by
      rw [q.eq_C_content_mul_primPart, map_mul, aeval_C, mul_eq_zero] at hqx
      exact hqx.resolve_left fun h => hq (content_eq_zero_iff.1 (hinj (h.trans (map_zero _).symm)))
    have h2 : eval₂ ψ x q.primPart = 0 := by
      apply V.subtype_injective
      rw [hom_eval₂, hψ, map_zero]
      exact h1
    refine ⟨q.primPart.map (Ideal.Quotient.mk p), fun h => ?_, ?_⟩
    · obtain ⟨a, ha⟩ := (IsPrincipalIdealRing.principal p).principal
      have hd : C a ∣ q.primPart := (C_dvd_iff_dvd_coeff _ _).2 fun i => by
        rw [← Ideal.mem_span_singleton, ← Ideal.submodule_span_eq, ← ha, ← Ideal.Quotient.eq_zero_iff_mem, ← coeff_map, h, coeff_zero]
      refine hp.ne_top (Ideal.eq_top_of_isUnit_mem _ ?_ (q.isPrimitive_primPart a hd))
      rw [ha]
      exact Submodule.mem_span_singleton_self a
    · rw [aeval_def, eval₂_map]
      have := congrArg (residue V) h2
      rw [hom_eval₂, map_zero] at this
      exact this⟩
  let l : ResidueField V →ₐ[R ⧸ p] k := IsAlgClosed.lift
  refine ⟨V, ψ, l.toRingHom.comp (residue V), hψ, RingHom.ext fun x => ?_⟩
  exact l.commutes (Ideal.Quotient.mk p x)

end Algebra

section Level

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp unitOn omegaStd IsGrpPullback LBIso pushPt)

theorem sec_bijective {O C : Type} [CommRing O] [IsDomain O] [ValuationRing O] [Field C] [Algebra O C]
    [IsFractionRing O C] (X : Over (Sp O)) [IsProper X.hom]
    (e : Over.mk (Geo.Tor.spMap (algebraMap O C)) ⟶ 𝟙_ (Over (Sp O))) :
    Function.Bijective fun x : 𝟙_ (Over (Sp O)) ⟶ X => e ≫ x := by
  have he : e.left = Geo.Tor.spMap (algebraMap O C) := (Category.comp_id _).symm.trans (Over.w e)
  have hE : ValuativeCriterion.Existence X.hom := by
    have h : UniversallyClosed X.hom := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  have hU : ValuativeCriterion.Uniqueness X.hom := IsSeparated.valuativeCriterion X.hom
  let S : (Over.mk (Geo.Tor.spMap (algebraMap O C)) ⟶ X) → ValuativeCommSq X.hom := fun z =>
    { R := O, K := C, i₁ := z.left, i₂ := 𝟙 _, commSq := ⟨(Over.w z).trans (Category.comp_id _).symm⟩ }
  refine ⟨fun x y hxy => ?_, fun z => ?_⟩
  · have h₁ : Geo.Tor.spMap (algebraMap O C) ≫ x.left = (e ≫ x).left := congrArg (· ≫ x.left) he.symm
    have h₂ : Geo.Tor.spMap (algebraMap O C) ≫ y.left = (e ≫ x).left :=
      (congrArg (· ≫ y.left) he.symm).trans (congrArg Over.Hom.left hxy.symm)
    have := (hU (S (e ≫ x))).elim ⟨x.left, h₁, Over.w x⟩ ⟨y.left, h₂, Over.w y⟩
    exact Over.OverMorphism.ext (congrArg CommSq.LiftStruct.l this)
  · obtain ⟨⟨l, h1, h2⟩⟩ := hE (S z)
    refine ⟨Over.homMk l h2, Over.OverMorphism.ext ?_⟩
    show e.left ≫ l = z.left
    rw [he]
    exact h1

theorem exists_secHom {O C : Type} [CommRing O] [IsDomain O] [ValuationRing O] [Field C] [Algebra O C]
    [IsFractionRing O C] {Q : Out.PolAV (Sp O)}
    {Q' : Out.PolAV (Sp C)} {ψ : Q'.A.left ⟶ Q.A.left}
    (H : IsGrpPullback Q'.A Q.A (Geo.Tor.spMap (algebraMap O C)) ψ) (hw' : LBIso Q'.L (Q.L.pull ψ)) :
    ∃ ρ : (𝟙_ (Over (Sp O)) ⟶ Q.A) →* (𝟙_ (Over (Sp C)) ⟶ Q'.A), Function.Bijective ρ ∧
      ∀ (n : ℕ) x y (u : Oˣ), x ^ n = 1 → y ^ n = 1 →
        Out.WeilIs Q'.A Q'.L n (ρ x) (ρ y) (unitOn (Units.map (algebraMap O C).toMonoidHom u)) →
        Out.WeilIs Q.A Q.L n x y (unitOn u) := by
  have := Q.isAb.comm
  have := Q.isAb.proper
  have hG : Out.GlobalFnsSt := GlobalTheory.laws_without_cohomology.1
  let β := algebraMap O C
  obtain ⟨b, hb⟩ := UnifPoint.exists_pointEquiv H
  let e : Over.mk (Geo.Tor.spMap β) ⟶ 𝟙_ (Over (Sp O)) := Over.homMk (Geo.Tor.spMap β) (Category.comp_id _)
  let r : (𝟙_ (Over (Sp O)) ⟶ Q.A) →* (Over.mk (Geo.Tor.spMap β) ⟶ Q.A) :=
    MonoidHom.mk' (fun x => e ≫ x) fun x y => MonObj.comp_mul _ _ _
  have hρ : ∀ x, (b.symm (r x)).left ≫ ψ = Geo.Tor.spMap β ≫ x.left := fun x => by
    rw [← hb, b.apply_symm_apply]; rfl
  refine ⟨b.symm.toMonoidHom.comp r, b.symm.bijective.comp (sec_bijective Q.A e), fun n x y u hx hy hw => ?_⟩
  obtain ⟨c, hc, -⟩ := LevelCompare.weil_existsUnique Q n x y hx hy
  have h₁ := CommPairing.weilIs_pull hG Q.isAb Q.isLB e hc
  have h₂ := (weilIs_grpPullback_of_comm _ _ Q.A Q'.A _ ψ Q.L Q'.L Q.isLB Q'.isLB H hw' _ n _ _
    (pushPt H.1.w _) (pushPt H.1.w _) _ rfl rfl).1 hw
  have h₃ : Out.WeilIs Q.A Q.L n (e ≫ x) (e ≫ y) (unitOn (Units.map β.toMonoidHom u)) :=
    UnifPoint.weilIs_congr (Category.id_comp _) (hρ x) (hρ y) h₂
  have h₄ := CommutatorPairing.weilIs_unique hG Q.isAb Q.isLB h₁ h₃
  obtain ⟨w, rfl⟩ : ∃ w : Oˣ, unitOn w = c :=
    ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom.toMonoidHom c,
      Units.ext (CommRingCat.inv_hom_apply (Scheme.ΓSpecIso (CommRingCat.of O)) c.val)⟩
  have e' : Units.map e.left.appTop.hom.toMonoidHom (unitOn w) = unitOn (Units.map β.toMonoidHom w) :=
    Units.ext (congrArg (fun q => q.hom w.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm
  have inj : Function.Injective (unitOn (R := C)) :=
    Units.map_injective (Scheme.ΓSpecIso (CommRingCat.of C)).symm.commRingCatIsoToRingEquiv.injective
  have h₅ := congrArg Units.val (inj (e'.symm.trans h₄))
  obtain rfl : w = u := Units.ext (IsFractionRing.injective O C h₅)
  exact hc

theorem exists_level {O C : Type} [CommRing O] [IsDomain O] [ValuationRing O] [Field C] [IsAlgClosed C] [Algebra O C]
    [IsFractionRing O C] (P : Out.PolAV (Sp O)) (h M : ℕ) (ze : Oˣ) (hg : P.g = h) (hM : IsUnit (M : O))
    (hz : IsPrimitiveRoot (algebraMap O C ze) M) :
    ∃ lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Sp O)) ⟶ P.A), (∀ x y, lev (x + y) = lev x * lev y) ∧
      (∀ x, lev x ^ M = 1) ∧ ∀ x y, Out.WeilIs P.A P.L M (lev x) (lev y) (unitOn (ze ^ omegaStd x y)) := by
  subst hg
  have hM' : (M : C) ≠ 0 := by
    have := (hM.map (algebraMap O C)).ne_zero
    rwa [map_natCast] at this
  haveI : NeZero M := ⟨fun h0 => hM' (by rw [h0, Nat.cast_zero])⟩
  obtain ⟨P', g, hg, hgg, hmul, tw, htw⟩ :=
    GlobalTheory.laws_without_cohomology.2.2.1 _ _ (Geo.Tor.spMap (algebraMap O C)) P
  have hp : IsGrpPullback P'.A P.A (Geo.Tor.spMap (algebraMap O C)) g := ⟨hg, fun T x y x₀ y₀ hx hy => by
    rw [show x₀ = Out.toBase hg.w x from Over.OverMorphism.ext hx,
      show y₀ = Out.toBase hg.w y from Over.OverMorphism.ext hy, ← hmul]
    rfl⟩
  obtain ⟨ρ, hρ, hw⟩ := exists_secHom hp (Geo.Tor.LBIso.symm ⟨tw, htw⟩)
  obtain ⟨lev⟩ := nonempty_level_of_isAlgClosed C P' M (Units.map (algebraMap O C).toMonoidHom ze) hM'
    (IsPrimitiveRoot.coe_units_iff.1 hz)
  rw [← hgg]
  have := P'.isAb.comm
  choose t ht using fun a : Fin P'.g ⊕ Fin P'.g → ℤ =>
    hρ.2 (LevelCompare.homOfBasis lev (Multiplicative.ofAdd (fun j => (a j : ZMod M))))
  have tors : ∀ a, t a ^ M = 1 := fun a => hρ.1 (by rw [map_pow, ht, map_one, LevelCompare.hom_pow])
  refine ⟨t, fun a b => hρ.1 ?_, tors, fun a b => hw M _ _ _ (tors a) (tors b) ?_⟩
  · rw [map_mul, ht, ht, ht, ← map_mul, ← ofAdd_add]
    exact congrArg _ (congrArg _ (funext fun j => Int.cast_add _ _))
  · rw [ht, ht, map_zpow]
    have w := LevelCompare.pairing_of_basis lev a b
    unfold unitOn at w ⊢
    rw [map_zpow]
    exact w

end Level

section Main

open CategoryTheory AlgebraicGeometry Limits NumberField IsLocalRing
open MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.BdDim GlobalTheory.SiegelTor GlobalTheory.ZM GlobalTheory.CM GlobalTheory.Models
open scoped CategoryTheory.Obj

theorem exists_cycAway_hom {L : Type} [Field L] [IsAlgClosed L] (τ : L →+* ℂ) (V : ValuationSubring L) {n : ℕ}
    (hn : n ≠ 0) (hu : IsUnit (n : V)) :
    ∃ em : cycAway n →+* V, ∀ x, τ (em x) = x := by
  let σ : V →+* ℂ := τ.comp V.subtype
  have hσ : Function.Injective σ := τ.injective.comp V.subtype_injective
  haveI : CharZero L := τ.charZero
  haveI : NeZero n := ⟨hn⟩
  have hle : cycAway n ≤ σ.range := by
    refine Subring.closure_le.2 ?_
    rintro _ (rfl | rfl)
    · obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L n
      obtain ⟨i, -, hi⟩ := (hz.map_of_injective τ.injective).eq_pow_of_pow_eq_one
        (Complex.isPrimitiveRoot_exp n hn).pow_eq_one
      have hzV : z ∈ V := by
        rcases V.mem_or_inv_mem z with h | h
        · exact h
        · have e : z = z⁻¹ ^ (n - 1) := by
            rw [inv_pow]
            refine eq_inv_of_mul_eq_one_left ?_
            rw [← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hn), hz.pow_eq_one]
          rw [e]
          exact pow_mem h _
      exact ⟨⟨z, hzV⟩ ^ i, (map_pow σ _ _).trans hi⟩
    · obtain ⟨u, hu⟩ := hu
      refine ⟨↑u⁻¹, eq_inv_of_mul_eq_one_left ?_⟩
      rw [← map_natCast σ, ← hu, ← map_mul, Units.inv_mul, map_one]
  let e : V ≃+* σ.range := RingEquiv.ofBijective σ.rangeRestrict
    ⟨fun x y h => hσ (congrArg Subtype.val h), σ.rangeRestrict_surjective⟩
  exact ⟨e.symm.toRingHom.comp (Subring.inclusion hle), fun x =>
    congrArg Subtype.val (e.apply_symm_apply (Subring.inclusion hle x))⟩

theorem exists_siegel_point : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (T : Formalism.L2.Pj.CDVR) (P : Out.PolAV (Sp T.V)) (σ : T.V →+* ℂ) (k : Type) [Field k] [IsAlgClosed k] (r : T.V →+* k), 3 ≤ n → Odd n → IsUnit (n : T.V) → P.g = g → Function.Injective σ → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (ψ : T.V →+* V) (σ' : V →+* ℂ) (r' : V →+* k) (y : Sp V ⟶ F.X) (P' : Out.PolAV (Sp V)) (φ : P'.A.left ⟶ P.A.left) (α : P'.A.left ⟶ F.univ.A.left) (α₂ : (G2 P'.A).left ⟶ (G2 F.univ.A).left), Function.Injective σ' ∧ σ'.comp ψ = σ ∧ r'.comp ψ = r ∧ IsPolFibre ψ P P' φ ∧ IsGrpPullback P'.A F.univ.A y α ∧ IsSquare α α₂ ∧ LBIso (abelian₂ P'.A P'.L) (F.univ.P.pull α₂) := by
  intro g n F T P σ k _ _ r hn3 _ hu hg hσ
  have hn : n ≠ 0 := by omega
  let L := AlgebraicClosure (FractionRing T.V)
  have hinj : Function.Injective (algebraMap T.V L) := by
    rw [IsScalarTower.algebraMap_eq T.V (FractionRing T.V) L]
    exact (algebraMap (FractionRing T.V) L).injective.comp (IsFractionRing.injective _ _)
  haveI : FaithfulSMul T.V L := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  haveI : Algebra.IsAlgebraic T.V L := (IsFractionRing.comap_isAlgebraic_iff (K := FractionRing T.V)).2 inferInstance
  letI : Algebra T.V ℂ := σ.toAlgebra
  haveI : FaithfulSMul T.V ℂ := (faithfulSMul_iff_algebraMap_injective _ _).2 hσ
  let τ : L →ₐ[T.V] ℂ := IsAlgClosed.lift
  obtain ⟨V, ψ, r', hψ, hr⟩ := exists_valuationSubring_extension hinj r
  have hu' : IsUnit (n : V) := by simpa using hu.map ψ
  obtain ⟨em, hem⟩ := exists_cycAway_hom τ.toRingHom V hn hu'
  have hσ' : Function.Injective (τ.toRingHom.comp V.subtype) := τ.toRingHom.injective.comp V.subtype_injective
  have hemi : Function.Injective em := fun x y h => Subtype.ext (by rw [← hem, ← hem, h])
  have hz : IsPrimitiveRoot (em (zetaAway n)) n :=
    IsPrimitiveRoot.of_map_of_injective (f := τ.toRingHom.comp V.subtype)
      (by rw [show (τ.toRingHom.comp V.subtype) (em (zetaAway n)) = _ from hem _]; exact Complex.isPrimitiveRoot_exp n hn) hσ'
  obtain ⟨ze, hze⟩ := hz.isUnit hn
  have hprim : ∀ (K : Type) [Field K] (gk : V →+* K), IsPrimitiveRoot (gk ze) n := fun K _ gk => by
    haveI : NeZero (n : K) := ⟨by simpa using (hu'.map gk).ne_zero⟩
    rw [← Polynomial.isRoot_cyclotomic_iff, ← Polynomial.map_cyclotomic n gk, hze]
    exact (hz.isRoot_cyclotomic (Nat.pos_of_ne_zero hn)).map
  obtain ⟨P', φ, hφ⟩ := exists_isPolFibre GlobalTheory.laws_without_cohomology.2.2.1 ψ P
  obtain ⟨lev, hl₁, hl₂, hl₃⟩ := exists_level (C := L) P' g n ze (hφ.1.trans hg) hu' (hprim L _)
  obtain ⟨c, e, he, hc, hcP⟩ := GlobalTheory.SiegelOverLocal.exists_siegPre V T.V P ψ P' φ hφ.2.1 hφ.2.2.symm hφ.1 _ em g n
    (zetaAway n) ze lev (hφ.1.trans hg) hu' hze hprim hl₁ hl₂ hl₃
  have hd : Dense {x : Sp V | ((spMap em) x).asIdeal = ⊥} := by
    have h0 : Dense ({genericPoint (Sp V)} : Set (Sp V)) :=
      dense_iff_closure_eq.2 (genericPoint_closure _)
    refine h0.mono ?_
    rintro _ rfl
    rw [genericPoint_eq_bot_of_affine]
    exact Ideal.comap_bot_of_injective _ hemi
  obtain ⟨y, -, φ₁, φ₂, hpb, hsq, hiso, -⟩ := F.rep _ _ c inferInstance hd hc
  let κ : P'.A ⊗ P'.A ⟶ c.A ⊗ c.A := lift (fst P'.A P'.A ≫ e.inv) (snd P'.A P'.A ≫ e.inv)
  have hk : κ.left ≫ (lift (fst c.A c.A ≫ e.hom) (snd c.A c.A ≫ e.hom)).left = 𝟙 _ := by
    rw [← Over.comp_left, ← Over.id_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp [κ]
  have : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  refine ⟨V, inferInstance, inferInstance, ψ, τ.toRingHom.comp V.subtype, r', y, P', φ, e.inv.left ≫ φ₁, κ.left ≫ φ₂,
    hσ', ?_, hr, hφ, ?_, ⟨?_, ?_⟩, ?_⟩
  · rw [RingHom.comp_assoc, hψ]
    exact RingHom.ext fun x => τ.commutes x
  · exact ((isGrpPullback_of_iso e.symm).comp hpb).congr (Category.id_comp _) rfl
  · rw [Category.assoc, hsq.1, ← Category.assoc, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst]
  · rw [Category.assoc, hsq.2, ← Category.assoc, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_snd]
  · have hA : LBIso (abelian₂ P'.A P'.L) (c.P.pull κ.left) :=
      LBIso.chartPull (chartPullSec _ _ κ.left hk) (Geo.Tor.chartPullPull c.P κ.left κ.left rfl) hcP.symm
    have hB : LBIso (c.P.pull κ.left) (F.univ.P.pull (κ.left ≫ φ₂)) :=
      LBIso.chartPull (Geo.Tor.chartPullPull c.P κ.left κ.left rfl)
        (chartPullSame F.univ.P _ (fun _ => φ₂) _ κ.left fun _ => rfl) hiso
    exact LBIso.trans (DVR.linComb_isLB _ P'.isLB _ _) (pull_isLB c.isLB _) (pull_isLB F.univ.isLB _) hA hB

end Main

end GlobalTheory.SiegPt

end
