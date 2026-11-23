import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullTorsionIntegrallyClosed
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianSchemePointObjectStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.EqOfSpecializes
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.UnramifiedPrimeIdempotent
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.Orbit

section Ring

variable {Ω : Type} [Field Ω] {A : Type} [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω]
  {m : Ideal A} [m.IsPrime] {O : Type} [CommRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω]
  [IsScalarTower A O Ω]

include m in

theorem algebraMap_injective : Function.Injective (algebraMap O Ω) := by
  have hA : Function.Injective (algebraMap A Ω) := IsIntegralClosure.algebraMap_injective A ℤ Ω
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq m.primeCompl x
  have h1 : algebraMap O Ω (IsLocalization.mk' O a s) * algebraMap A Ω (s : A) = algebraMap A Ω a := by
    rw [IsScalarTower.algebraMap_apply A O Ω, IsScalarTower.algebraMap_apply A O Ω a, ← map_mul,
      IsLocalization.mk'_spec]
  rw [hx, zero_mul] at h1
  have h2 : a = 0 := hA (by rw [← h1, map_zero])
  rw [h2, IsLocalization.mk'_zero]

include m in

theorem exists_of_integral (x : Ω) (hx : IsIntegral ℤ x) : ∃ o : O, algebraMap O Ω o = x :=
  ⟨algebraMap A O (IsIntegralClosure.mk' A x hx), by
    rw [← IsScalarTower.algebraMap_apply, IsIntegralClosure.algebraMap_mk']⟩

include m in

theorem exists_hom {R : Type} [CommRing R] (f : R →+* Ω) (hf : ∀ a, IsIntegral ℤ (f a)) :
    ∃ g : R →+* O, ∀ a, algebraMap O Ω (g a) = f a := by
  have hi := algebraMap_injective (Ω := Ω) (A := A) (m := m) (O := O)
  choose g hg using fun a => exists_of_integral (Ω := Ω) (A := A) (m := m) (O := O) (f a) (hf a)
  exact ⟨{ toFun := g
           map_one' := hi (by rw [hg, map_one, map_one])
           map_mul' := fun a b => hi (by rw [hg, map_mul, map_mul, hg, hg])
           map_zero' := hi (by rw [hg, map_zero, map_zero])
           map_add' := fun a b => hi (by rw [hg, map_add, map_add, hg, hg]) }, hg⟩

end Ring

theorem sub_one_pow_eq {O : Type} [CommRing O] [IsDomain O] {p : ℕ} (hp : p.Prime) {ζ : O}
    (h : IsPrimitiveRoot ζ p) : ∃ u : O, IsUnit u ∧ (ζ - 1) ^ (p - 1) = u * (p : O) := by
  have h1 : IsPrimitiveRoot ζ ((p - 1) + 1) := by rwa [Nat.sub_add_cancel hp.one_le]
  have h2 := h1.prod_one_sub_pow_eq_order
  have h3 : Associated (∏ _k ∈ Finset.range (p - 1), (ζ - 1))
      (∏ k ∈ Finset.range (p - 1), (1 - ζ ^ (k + 1))) := by
    refine Associated.prod _ _ _ fun k hk => ?_
    have hk' : k + 1 < p := by have := Finset.mem_range.1 hk; have := hp.one_le; omega
    have hc : (k + 1).Coprime p := Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt (by omega) hk'))
    have := h.associated_sub_one_pow_sub_one_of_coprime hc
    have e : (1 - ζ ^ (k + 1)) = - (ζ ^ (k + 1) - 1) := by ring
    rw [e]
    exact this.trans (Associated.refl _).neg_right
  rw [h2, Finset.prod_const, Finset.card_range] at h3
  obtain ⟨u, hu⟩ := h3
  refine ⟨((u⁻¹ : Oˣ) : O), Units.isUnit _, ?_⟩
  have e1 : (((p - 1 : ℕ) : O) + 1) = (p : O) := by
    rw [← Nat.cast_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hp.one_le]
  have hu' : (ζ - 1) ^ (p - 1) * (u : O) = (p : O) := by
    rw [hu]; first | exact e1 | (push_cast; exact e1)
  rw [← hu', mul_comm]
  exact (Units.mul_inv_cancel_right _ _).symm

section Abstract

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open NumberField in

theorem orbit_abstract {p : ℕ} (hp : p.Prime) (hd : ¬ (p : ℤ) ∣ NumberField.discr E) {T : Type} [Finite T] (t₀ : T)
    (φ : Equiv.Perm T) {k : Type} [Field k] (r : T → 𝓞 E →+* k) (hpk : (p : k) = 0)
    (hF : ∀ s a, r (φ s) a = (r s a) ^ p) :
    ∃ (Sg : Type) (_ : Fintype Sg) (e : Sg → T) (φ' : Equiv.Perm Sg) (F : Type) (_ : Field F) (_ : Fintype F)
      (_ : CharP F p) (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}))
      (σ : Sg → F →+* k), t₀ ∈ Set.range e ∧ Function.Injective e ∧ (∀ τ, e (φ' τ) = φ (e τ)) ∧
        Function.Surjective pq ∧ (∀ τ a, r (e τ) a = σ τ (pq (Ideal.Quotient.mk _ a))) ∧
        (∀ t, (∀ a, r t a = 0 ↔ pq (Ideal.Quotient.mk _ a) = 0) → t ∈ Set.range e) ∧ IsSec pq sc := by
  classical
  set w₀ : Ideal (𝓞 E) := RingHom.ker (r t₀) with hw₀
  haveI hprime : w₀.IsPrime := RingHom.ker_isPrime _
  have hpw : (p : 𝓞 E) ∈ w₀ := by
    rw [hw₀, RingHom.mem_ker, map_natCast, hpk]
  have hp0 : (p : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hne : w₀ ≠ ⊥ := fun h => hp0 (by rwa [h, Ideal.mem_bot] at hpw)
  haveI hmax : w₀.IsMaximal := Ideal.IsPrime.isMaximal hprime hne
  letI fld : Field (𝓞 E ⧸ w₀) := Ideal.Quotient.field w₀
  haveI hfinq : Finite (𝓞 E ⧸ w₀) := Ideal.finiteQuotientOfFreeOfNeBot w₀ hne
  letI fin : Fintype (𝓞 E ⧸ w₀) := Fintype.ofFinite _
  have hle : Ideal.span {(p : 𝓞 E)} ≤ w₀ := (Ideal.span_singleton_le_iff_mem _).2 hpw
  have hchar : CharP (𝓞 E ⧸ w₀) p := by
    haveI : Fact p.Prime := ⟨hp⟩
    refine (CharP.charP_iff_prime_eq_zero hp).2 ?_
    have : ((p : 𝓞 E) : 𝓞 E ⧸ w₀) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hpw
    simpa using this
  have hker : ∀ s, RingHom.ker (r (φ s)) = RingHom.ker (r s) := fun s => by
    ext a
    rw [RingHom.mem_ker, RingHom.mem_ker, hF, pow_eq_zero_iff hp.ne_zero]
  obtain ⟨ε, h1, -, h3, -, -⟩ := unramified_prime_idempotent E p hp hd w₀ hpw
  have hsurj : Function.Surjective (Ideal.Quotient.mk w₀) := Ideal.Quotient.mk_surjective
  let lf : (𝓞 E ⧸ w₀) → 𝓞 E := Function.surjInv hsurj
  have hlf : ∀ a, Ideal.Quotient.mk w₀ (lf a) = a := Function.surjInv_eq hsurj
  let pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* (𝓞 E ⧸ w₀) := Ideal.Quotient.factor hle
  have hpq : ∀ a, pq (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk w₀ a := fun a => rfl
  have hz : ∀ a ∈ w₀, Ideal.Quotient.mk (Ideal.span {(p : 𝓞 E)}) (ε * a) = 0 := fun a ha =>
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 ((h3 a).2 ha))
  let sc : (𝓞 E ⧸ w₀) →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) :=
    AddMonoidHom.mk' (fun a => Ideal.Quotient.mk _ (ε * lf a)) fun a b => by
      have hm : lf (a + b) - (lf a + lf b) ∈ w₀ := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_add, hlf, hlf, hlf, sub_self]
      have := hz _ hm
      rw [mul_sub, map_sub, sub_eq_zero, mul_add, map_add] at this
      exact this
  have hsc : ∀ a, sc a = Ideal.Quotient.mk _ (ε * lf a) := fun a => rfl
  let Sg : Type := {t : T // RingHom.ker (r t) = w₀}
  let f : Sg → Sg := fun τ => ⟨φ τ.1, (hker τ.1).trans τ.2⟩
  have hfi : Function.Injective f := fun a b h =>
    Subtype.ext (φ.injective (congrArg Subtype.val h))
  haveI : Finite Sg := inferInstance
  let φ' : Equiv.Perm Sg := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hfi)
  let σ : Sg → (𝓞 E ⧸ w₀) →+* k := fun τ => Ideal.Quotient.lift w₀ (r τ.1) fun a ha => by
    have : a ∈ RingHom.ker (r τ.1) := by rw [τ.2]; exact ha
    exact this
  refine ⟨Sg, Fintype.ofFinite Sg, Subtype.val, φ', 𝓞 E ⧸ w₀, fld, fin, hchar, pq, sc, σ, ⟨⟨t₀, rfl⟩, rfl⟩,
    Subtype.val_injective, fun τ => rfl, Ideal.Quotient.factor_surjective hle, fun τ a => rfl, ?_, ?_, ?_⟩
  · intro t ht
    refine ⟨⟨t, ?_⟩, rfl⟩
    ext a
    rw [RingHom.mem_ker, ht a, hpq, Ideal.Quotient.eq_zero_iff_mem]
  · intro a
    rw [hsc, hpq, map_mul, hlf]
    have : Ideal.Quotient.mk w₀ ε = 1 := by
      rw [← map_one (Ideal.Quotient.mk w₀)]
      exact Ideal.Quotient.eq.2 h1
    rw [this, _root_.one_mul]
  · intro u a hu
    obtain ⟨u', rfl⟩ := Ideal.Quotient.mk_surjective u
    have hu' : u' ∈ w₀ := Ideal.Quotient.eq_zero_iff_mem.1 hu
    rw [hsc, ← map_mul]
    have := hz _ (w₀.mul_mem_right (lf a) hu')
    rw [show u' * (ε * lf a) = ε * (u' * lf a) by ring]
    exact this

end Abstract

section Root

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O₀ : Type} [CommRing O₀] {β : O₀ →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}

theorem exists_point (A : HodgeCpt Y S y) : ∃ x : Sp Ω ⟶ Xo.XF c, A.ξ ≫ A.f = x ≫ Y.j := by
  have : IsProper Y.s := projProper O₀ Y.X Y.s Y.proj
  have : IsLocallyNoetherian (pullback Y.s (spMap β)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd Y.s (spMap β))
  have : CompactSpace ↥(pullback Y.s (spMap β)) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd Y.s (spMap β))
  have : IsNoetherian (pullback Y.s (spMap β)) := {}
  have := Y.jQ_open
  let pt₀ : Sp Ω ⟶ pullback Y.s (spMap β) := pullback.lift (A.ξ ≫ A.f) (spMap A.cst) (by
    rw [Category.assoc, A.cst_over]; exact Spec.map_comp (CommRingCat.ofHom β) (CommRingCat.ofHom A.cst))
  have hpt₀ : pt₀ ≫ pullback.fst _ _ = A.ξ ≫ A.f := pullback.lift_fst _ _ _
  have hpt : pullback.fst Y.s (spMap β) (pt₀ (IsLocalRing.closedPoint Ω)) = genPt A.ξ₀ := by
    have : Subsingleton (Spec (CommRingCat.of A.Ω₀)) := inferInstanceAs (Subsingleton (PrimeSpectrum A.Ω₀))
    have h0 : pt₀ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom A.fn) ≫ A.ξ₀ := hpt₀.trans A.fn_over
    refine (Scheme.Hom.comp_apply _ _ _).symm.trans ?_
    rw [h0]
    exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg A.ξ₀ (Subsingleton.elim _ _))
  obtain ⟨q, hqU, hq⟩ := GlobalTheory.CompanionTheory.Ar.CmpHodgeDiag.exists_gen Y.jQ.isOpenEmbedding.isOpen_range Y.jQ_dense
    (pt₀ (IsLocalRing.closedPoint Ω))
  have h1 := hq.map (pullback.fst Y.s (spMap β)).continuous
  rw [hpt] at h1
  have h2 := GlobalTheory.CompanionTheory.Ar.CmpHodgeDiag.eq_of_specializes A.gen₀ h1
  have hr : Set.range pt₀ ⊆ Set.range Y.jQ := by
    rintro _ ⟨a, rfl⟩
    have : Subsingleton (Sp Ω) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
    rw [Subsingleton.elim a (IsLocalRing.closedPoint Ω), ← Y.ab_gen, Set.mem_preimage, hpt, ← h2]
    have h3 : q ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by rw [Y.ab_gen]; exact hqU
    exact h3
  refine ⟨IsOpenImmersion.lift Y.jQ pt₀ hr, ?_⟩
  rw [Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, hpt₀]

theorem exists_root (A : HodgeCpt Y S y) (hpq : 0 < D.p + D.q) {p : ℕ} (hp : p.Prime) (hpS : p ∈ S) :
    ∃ ζ : Ω, IsPrimitiveRoot ζ p := by
  haveI : CharZero Ω := charZero_of_injective_ringHom A.cst.injective
  obtain ⟨x, hx⟩ := exists_point A
  obtain ⟨s0, o, ⟨m0⟩⟩ := GlobalTheory.T.abelian_scheme_point_object E H D l Xo c O₀ β Y A.X A.f A.t A.m Ω A.ξ x hx
  have hN : 0 < p ^ A.R p := pow_pos hp.pos _
  obtain ⟨ζ, hζ⟩ := GlobalTheory.CompanionTheory.Ar.OmLink.root o A.t m0 (A.tors p hpS) hN hpq
  have hR : 1 ≤ A.R p := by have := A.R_ge p hpS; omega
  refine ⟨ζ ^ (p ^ (A.R p - 1)), hζ.pow hN ?_⟩
  rw [← pow_succ, Nat.sub_add_cancel hR]

end Root

theorem orbit_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ t₀ : CMType H ⊕ CMType H, ∃ (Sg : Type) (_ : Fintype Sg) (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) (_ : Field F) (_ : Fintype F) (_ : CharP F p) (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ ∧ IsSec pq sc := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d _ hpq p hfact hpS _ hp2 hdisc φ hφ A _ _ _ m _ hpm O _ _ _ _ _ _ _ t₀
  have hp : p.Prime := hfact.out
  have hinj := algebraMap_injective (Ω := Ω) (A := A) (m := m) (O := O)
  haveI : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective
  obtain ⟨ζ, hζ⟩ := exists_root 𝔐 hpq hp hpS
  have hζi : IsIntegral ℤ ζ := IsIntegral.of_pow hp.pos (by rw [hζ.pow_eq_one]; exact isIntegral_one)
  obtain ⟨z, hz⟩ := exists_of_integral (A := A) (m := m) (O := O) ζ hζi
  have hzp : IsPrimitiveRoot z p :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap O Ω) (by rwa [hz]) hinj
  obtain ⟨u, hu, huw⟩ := sub_one_pow_eq hp hzp
  choose g hg using fun t => exists_hom (A := A) (m := m) (O := O) (𝔐.emb t)
    (fun a => (Algebra.IsIntegral.isIntegral (R := ℤ) a).map (𝔐.emb t).toIntAlgHom)
  have hpm' : (p : O) ∈ IsLocalRing.maximalIdeal O := by
    have := (IsLocalization.AtPrime.to_map_mem_maximal_iff O m (p : A)).2 hpm
    simpa using this
  have hnu : ¬ IsUnit (p : O) := hpm'
  have hp0 : (p : O) ≠ 0 := fun h => by
    have h1 : algebraMap O Ω (p : O) = 0 := by rw [h, map_zero]
    rw [map_natCast] at h1
    exact hp.ne_zero (Nat.cast_eq_zero.1 h1)
  have hpk : ((p : ℕ) : IsLocalRing.ResidueField O) = 0 := by
    have := (IsLocalRing.residue_eq_zero_iff (p : O)).2 hpm'
    simpa using this
  obtain ⟨inc, hinc⟩ := exists_hom (A := A) (m := m) (O := O) (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F))
    (fun a => (Algebra.IsIntegral.isIntegral (R := ℤ) a).map (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)).toIntAlgHom)
  have hel : ∀ s (a : 𝓞 E), ∃ v : 𝓞 c.F, (v : c.F) = labelEmb c s a ∧ inc v = g s a := by
    intro s a
    have hi : IsIntegral ℤ (labelEmb c s a) :=
      (Algebra.IsIntegral.isIntegral (R := ℤ) a).map (labelEmb c s).toIntAlgHom
    refine ⟨IsIntegralClosure.mk' _ _ hi, IsIntegralClosure.algebraMap_mk' _ _ _, hinj ?_⟩
    rw [hinc, hg, RingHom.comp_apply, IsIntegralClosure.algebraMap_mk']
    rfl
  have hF : ∀ s (a : 𝓞 E), IsLocalRing.residue O (g (φ s) a) = (IsLocalRing.residue O (g s a)) ^ p := by
    intro s a
    obtain ⟨u', hu1, hu2⟩ := hel (φ s) a
    obtain ⟨v', hv1, hv2⟩ := hel s a
    have hn := hφ (Ideal.comap inc (IsLocalRing.maximalIdeal O)) inferInstance
      (by rw [Ideal.mem_comap, map_natCast]; exact hpm') s a u' v' hu1 hv1
    rw [Ideal.mem_comap, map_sub, map_pow, hu2, hv2] at hn
    have h2 := (IsLocalRing.residue_eq_zero_iff _).2 hn
    rw [map_sub, map_pow, sub_eq_zero] at h2
    exact h2
  obtain ⟨Sg, i1, e, φ', F, i2, i3, i4, pq, sc, σ, a1, a2, a3, a4, a5, a6, a7⟩ :=
    orbit_abstract hp hdisc t₀ φ (fun t => (IsLocalRing.residue O).comp (g t)) hpk hF
  refine ⟨Sg, i1, e, φ', F, i2, i3, i4, pq, sc, z - 1, σ, ⟨a1, a2, a3, a4, ?_, ?_, ⟨hp0, ⟨u, hu, huw⟩, hnu⟩, ?_⟩, a7⟩
  · intro τ a
    exact ⟨g (e τ) a, hg _ _, a5 τ a⟩
  · intro t ht
    exact a6 t fun a => ht a (g t a) (hg t a)
  · unfold HT.IsCp
    rw [if_neg hp2]
    exact ⟨ζ, hζ, by rw [map_sub, map_one, hz]⟩

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.Orbit
