import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.IsConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.NotMem
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.Point
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.CohHomNatCastZero
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.NotLeSpanImage
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.KsCore
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.PullFrobIter
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.DualZeroOfSpan
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.RadicalStalk
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.OrdPull
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.Factor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorModuliObjectPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectPullbackCompDiagonalBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsDeRhamPairingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFiltrationLiftDeterminesModFilStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorRealiseKodairaSpencerDirectionStatement

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

namespace UpperTheory.Gal.Ord

private theorem asIdeal_spMap {B k : Type} [CommRing B] [Field k] (φ : B →+* k) (u : Sp k) :
    ((spMap φ).base u).asIdeal = RingHom.ker φ := by
  haveI := u.isPrime
  have hu : u.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  show Ideal.comap φ u.asIdeal = RingHom.ker φ
  rw [hu, RingHom.ker_eq_comap_bot]

private theorem charP_of_eq_closedPoint {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [IsLocalRing R]
    (hpR : (p : R) ∈ IsLocalRing.maximalIdeal R) {k : Type} [Field k] (β : R →+* k) (u : Sp k)
    (h : (spMap β).base u = IsLocalRing.closedPoint R) : CharP k p := by
  have hk : RingHom.ker β = IsLocalRing.maximalIdeal R := by
    rw [← asIdeal_spMap β u, h]
    rfl
  have h0 : (p : k) = 0 := by
    have hm : (p : R) ∈ RingHom.ker β := by
      rw [hk]
      exact hpR
    rw [RingHom.mem_ker, map_natCast] at hm
    exact hm
  exact (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr h0

private theorem exists_absNorm_eq {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [NumberField F] (w : Ideal (𝓞 F))
    (hw : w.IsPrime) (hp : (p : 𝓞 F) ∈ w) : w.IsMaximal ∧ ∃ f : ℕ, 0 < f ∧ Ideal.absNorm w = p ^ f := by
  have hne : w ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hp
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hp
  haveI : w.IsMaximal := hw.isMaximal hne
  refine ⟨inferInstance, ?_⟩
  obtain ⟨q, n, hn, hqw, hq, hN⟩ := Ideal.exists_prime_and_absNorm_eq_pow w
  have hqp : q = p := by
    by_contra hne'
    have hcop : Nat.Coprime p q := (Nat.coprime_primes Fact.out hq).mpr (Ne.symm hne')
    have h1 : (((Nat.gcd p q : ℕ) : ℤ) : 𝓞 F) ∈ w := by
      rw [Nat.gcd_eq_gcd_ab]
      push_cast
      exact w.add_mem (w.mul_mem_right _ hp) (w.mul_mem_right _ hqw)
    rw [hcop.gcd_eq_one, Nat.cast_one, Int.cast_one] at h1
    exact (Ideal.IsMaximal.ne_top inferInstance) ((Ideal.eq_top_iff_one w).mpr h1)
  exact ⟨n, hn, hqp ▸ hN⟩

end UpperTheory.Gal.Ord

theorem UpperTheory.Gal.Ord.ordGen :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → D.m = 1 → ∀ (i : Fin D.a) (w : Ideal (𝓞 D.F)), (IsLocalRing.maximalIdeal R).comap (b.t i) = w → ∀ (M : Model b N) (z : M.X), M.s.base z = IsLocalRing.closedPoint R → (∀ z' : M.X, M.s.base z' = IsLocalRing.closedPoint R → z' ⤳ z → z' = z) → ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ M.X), (∀ q, y.base q = z) → IsWOrd M.univ w y := by
  intro p _ D R _ _ _ _ b N hN hNp hpR hm i w hw M z hz hmin k _ _ y hy
  haveI : Smooth M.s := @SmoothOfRelativeDimension.smooth _ _ _ _ M.smooth
  set β : R →+* k := (Spec.preimage (y ≫ M.s)).hom with hβdef
  have hyβ : y ≫ M.s = spMap β := (Spec.map_preimage (y ≫ M.s)).symm
  have hβbase : (spMap β).base (IsLocalRing.closedPoint k) = IsLocalRing.closedPoint R := by
    rw [← hyβ]
    exact (congrArg M.s.base (hy _)).trans hz
  haveI hchar : CharP k p := charP_of_eq_closedPoint hpR β _ hβbase
  have hk : (p : k) = 0 := CharP.cast_eq_zero k p
  have hkerβ : RingHom.ker β = IsLocalRing.maximalIdeal R := by
    rw [← asIdeal_spMap β (IsLocalRing.closedPoint k), hβbase]
    rfl
  have hkerw : RingHom.ker (β.comp (b.t i)) = w := by
    rw [← RingHom.comap_ker, hkerβ, hw]
  have hwP : w.IsPrime := by
    rw [← hkerw]
    exact RingHom.ker_isPrime _
  have hpw : (p : 𝓞 D.F) ∈ w := by
    rw [← hkerw, RingHom.mem_ker, RingHom.comp_apply, map_natCast, map_natCast]
    exact hk
  obtain ⟨hwM, f, hf, hnorm⟩ := exists_absNorm_eq w hwP hpw
  obtain ⟨π⟩ := par p D.F w f hwM hpw hf
  obtain ⟨o₀, ⟨a₀⟩⟩ := GlobalTheory.T.exists_harrisTaylorModuliObject_pullback p D R b N M.X (Sp k) M.s (spMap β) y hyβ M.univ
  apply ordPull p D R b N M.X M.s M.univ w k y (spMap β) o₀ a₀
  rcases point p D R b N hN hNp hm k hk β o₀ i w f hkerw hnorm hf π with hW | hNO
  · exact hW
  exfalso
  have hLin := lin p D R b N hN hNp hm k hk β o₀ i w f hkerw hnorm hf π
  have hcard : Nat.card (𝓞 D.F ⧸ w) = p ^ f := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
    exact hnorm
  obtain ⟨x, hxε, hxg, y0, hy0, hxy0⟩ :=
    alg2 p k (𝓞 D.F) w f hf hcard π (β.comp (b.t i)) _ (coh o₀) (PrimitiveSubmodule o₀.A) _ hLin
  have hxFil : x ∈ Fil o₀.A := by
    rw [Fil, Submodule.mem_dualAnnihilator]
    intro c hc
    rw [← hxε c]
    have hle : Submodule.span k (Set.range fun c' => (coh o₀ π.g) ((⇑(frobDR p k hk o₀.A))^[f] c')) ≤
        LinearMap.ker x := by
      rw [Submodule.span_le]
      rintro _ ⟨c', rfl⟩
      exact hxg c'
    exact hle (hNO c hc)
  have hhom : hom o₀ π.ε x = x := by
    apply LinearMap.ext
    intro c
    exact hxε c
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.harrisTaylor_exists_deRham_pairing p D R b N hN hNp k (spMap β) o₀
  obtain ⟨g, hKS, hgx⟩ :=
    ks p D R b N hN hNp hm k hk β o₀ i w f hkerw hnorm hf π φ hφ x hxFil hhom ⟨y0, hy0, hxy0⟩
  obtain ⟨o', m', hlift⟩ := GlobalTheory.T.harrisTaylor_realise_kodairaSpencer_direction p D R b N hN hNp k (spMap β) o₀ β rfl φ hφ g hKS
  have hfst : (TrivSqZeroExt.fstHom k k k).toRingHom.comp (algebraMap k (DualNumber k)) = RingHom.id k := by
    ext a
    rfl
  have hcomp : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (algebraMap k (DualNumber k)) = 𝟙 _ := by
    rw [← GlobalTheory.Cris.spMap_comp, hfst]
    show Spec.map (CommRingCat.ofHom (RingHom.id k)) = _
    rw [CommRingCat.ofHom_id, Spec.map_id]
  obtain ⟨v, ⟨hv1, ⟨av⟩⟩, -⟩ := M.rep (Sp (DualNumber k)) _ o'
  have hcompv : Nonempty (ObjMap o₀ M.univ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v)) :=
    (GlobalTheory.T.harrisTaylorObjectPullback_comp_diagonalBundle p D R b N _ _ _ _ _ _ M.univ o' o₀ v _).1 ⟨m'⟩ ⟨av⟩
  have hyv : y = spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v := by
    apply (M.rep (Sp k) (spMap β) o₀).unique ⟨hyβ, ⟨a₀⟩⟩ ⟨?_, hcompv⟩
    rw [Category.assoc, hv1, ← Category.assoc, hcomp, Category.id_comp]
  have hcl : (spMap (TrivSqZeroExt.fstHom k k k).toRingHom).base (IsLocalRing.closedPoint k) =
      IsLocalRing.closedPoint (DualNumber k) := by
    apply PrimeSpectrum.ext
    refine (asIdeal_spMap (TrivSqZeroExt.fstHom k k k).toRingHom (IsLocalRing.closedPoint k)).trans ?_
    exact IsLocalRing.eq_maximalIdeal
      (RingHom.ker_isMaximal_of_surjective _ (fun a => ⟨TrivSqZeroExt.inl a, rfl⟩))
  have hvz : v.base (IsLocalRing.closedPoint (DualNumber k)) = z := by
    rw [← hcl]
    have h1 := hy (IsLocalRing.closedPoint k)
    rw [hyv] at h1
    exact h1
  obtain ⟨σ, hσ⟩ := gen R M.X M.s z hz hmin k y β (hy _) hyβ (fun r hr => by
    have hr' : r ∈ RingHom.ker β := hkerβ ▸ hr
    exact RingHom.mem_ker.mp hr')
  obtain ⟨τ, hτ⟩ := gen R M.X M.s z hz hmin (DualNumber k) v ((algebraMap k (DualNumber k)).comp β) hvz
    (hv1.trans (GlobalTheory.Cris.spMap_comp β _).symm) (fun r hr => by
      have hr' : r ∈ RingHom.ker β := hkerβ ▸ hr
      rw [RingHom.comp_apply, RingHom.mem_ker.mp hr', map_zero])
  obtain ⟨oκ, ⟨aκ⟩⟩ := GlobalTheory.T.exists_harrisTaylorModuliObject_pullback p D R b N M.X _ M.s (M.X.fromSpecResidueField z ≫ M.s)
    (M.X.fromSpecResidueField z) rfl M.univ
  have a₀' : ObjMap o₀ M.univ (spMap σ ≫ M.X.fromSpecResidueField z) := by
    rw [hσ]
    exact a₀
  have av' : ObjMap o' M.univ (spMap τ ≫ M.X.fromSpecResidueField z) := by
    rw [hτ]
    exact av
  obtain ⟨b₀⟩ := factor p D R b N hN hNp _ _ _ M.s _ _ M.univ oκ o₀ (M.X.fromSpecResidueField z) (spMap σ)
    rfl ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ M.s) hσ).trans hyβ)) aκ a₀'
  obtain ⟨b'⟩ := factor p D R b N hN hNp _ _ _ M.s _ _ M.univ oκ o' (M.X.fromSpecResidueField z) (spMap τ)
    rfl ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ M.s) hτ).trans hv1)) aκ av'
  have hκ : (p : M.X.residueField z) = 0 :=
    σ.injective (by rw [map_natCast, map_zero]; exact hk)
  have hT : (p : DualNumber k) = 0 := by
    rw [← map_natCast (algebraMap k (DualNumber k)), hk, map_zero]
  have hNO' := desc p D R b N w f π _ k (DualNumber k) hκ hk hT σ τ _ _ _ oκ o₀ o' b₀ b' hNO
  have h0 := estep p D R b N w f hf π k hk hT (spMap β) _ o₀ o' m' hNO' x hxg
  rw [hhom] at h0
  have hmem := (GlobalTheory.T.hodgeFiltration_lift_determines_mod_fil k o₀.A o'.A m'.φ m'.cart o'.ab x hxFil (g x) 0 (hlift x hxFil)).mp h0
  have hneg := (Fil o₀.A).neg_mem hmem
  rw [zero_sub, neg_neg] at hneg
  exact hgx hneg
