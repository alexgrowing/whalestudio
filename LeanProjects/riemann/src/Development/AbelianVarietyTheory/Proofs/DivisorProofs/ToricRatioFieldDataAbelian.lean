import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NuHTwisted
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsHeckeLOfHasInf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConductorExponentAtPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightExceedsCenterBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCastMemBelow

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)
open GlobalTheory.CMVal GlobalTheory.HeckeGal

noncomputable section

namespace GlobalTheory.ThmAUpper.Read

theorem exists_pow_of_two_emb {L K : Type} [Field L] [Field K] (f g : L →+* K) {l : ℕ} (hl : l.Prime) (n : ℕ) :
    ∃ c : ℤ, IsCoprime c (l : ℤ) ∧ ∀ y : L, y ^ (l ^ n) = 1 → g y = f y ^ c := by
  have : NeZero (l ^ n) := ⟨pow_ne_zero _ hl.ne_zero⟩
  obtain ⟨z, hz⟩ := IsCyclic.exists_generator (α := rootsOfUnity (l ^ n) L)
  have key : ∀ c : ℤ, g ((z : Lˣ) : L) = f ((z : Lˣ) : L) ^ c → ∀ y : L, y ^ (l ^ n) = 1 → g y = f y ^ c := by
    intro c hc y hy
    obtain ⟨k, hk⟩ := hz (rootsOfUnity.mkOfPowEq y hy)
    have e : y = ((z : Lˣ) : L) ^ k := by
      have := congrArg (fun t : rootsOfUnity (l ^ n) L => ((t : Lˣ) : L)) hk
      simpa using this.symm
    rw [e, map_zpow₀, map_zpow₀, hc, ← zpow_mul, ← zpow_mul, mul_comm]
  have h1 : ((z : Lˣ) : L) ^ (l ^ n) = 1 := by
    have := z.2
    rw [mem_rootsOfUnity'] at this
    exact this
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hl).1 (orderOf_dvd_of_pow_eq_one h1)
  have hp : IsPrimitiveRoot ((z : Lˣ) : L) (l ^ m) := hm ▸ IsPrimitiveRoot.orderOf _
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · have e : ((z : Lˣ) : L) = 1 := by simpa using hp
    exact ⟨1, isCoprime_one_left, key 1 (by simp [e])⟩
  · have : NeZero (l ^ m) := ⟨pow_ne_zero _ hl.ne_zero⟩
    obtain ⟨i, -, hi, e⟩ := ((hp.map_of_injective f.injective).isPrimitiveRoot_iff).1 (hp.map_of_injective g.injective)
    refine ⟨i, Nat.isCoprime_iff_coprime.2 ((Nat.coprime_pow_right_iff hm0 _ _).1 hi), key i ?_⟩
    rw [zpow_natCast, e]

theorem exists_extend {A B K : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B]
    [Field K] [IsAlgClosed K] (hi : Function.Injective (algebraMap A B)) (f : A →+* K) (hf : Function.Injective f) :
    ∃ g : FractionRing B →+* K, ∀ a, g (algebraMap B _ (algebraMap A B a)) = f a := by
  letI := f.toAlgebra
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
  have : FaithfulSMul A K := (faithfulSMul_iff_algebraMap_injective _ _).2 hf
  let J0 : B →ₐ[A] K := IsAlgClosed.lift
  have hJ : Function.Injective J0.toRingHom := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := A) ?_
    rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    intro a b hab
    exact hf ((J0.commutes a).symm.trans (Eq.trans hab (J0.commutes b)))
  exact ⟨IsFractionRing.lift hJ, fun a => by rw [IsFractionRing.lift_algebraMap]; exact J0.commutes a⟩

theorem isClassTerm_reindex {E : Type} [Field E] [NumberField E] {I I' : Type} [Fintype I] [Fintype I'] (e : I' ≃ I)
    {φ : I → E →+* ℂ} {s : ℕ} {κ : I → ℕ} {c : Ideal (OF E)} {χ : HChar E} {y : (Af E)ˣ} {T : ℂ}
    (h : GlobalTheory.ToricDenom.IsClassTerm φ s κ c χ y T) : GlobalTheory.ToricDenom.IsClassTerm (φ ∘ e) s (κ ∘ e) c χ y T := by
  obtain ⟨S, hS, hT⟩ := h
  refine ⟨S, ⟨hS.1, fun σ hσ => ?_⟩, hT⟩
  have : ∀ x, term (φ ∘ e) (2 * s) (κ ∘ e) σ x = term φ (2 * s) κ σ x := fun x =>
    Fintype.prod_equiv e _ _ fun _ => rfl
  simp only [this]
  exact hS.2 σ hσ

open GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum GlobalTheory.ToricDenom in

theorem cond0_eq {D : D7} {T : Type} {Lc : Formalism.IndefR.Links.LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc)
    (hb : IsBaseCond (condF G.pl)) : GlobalTheory.LamTie.cond0 D.host (G.pl.w G.pl.v0) = condF G.pl := by
  classical
  have hw0 : below (G.pl.w G.pl.v0) = G.pl.v0 := G.pl.under_w (G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl))
  have hv0 := G.ch.basePlace_not_mem_chiGridBadPlaces
  rw [S1_mem_OmF] at hv0
  simp only [not_or] at hv0
  have hdvd : ∀ v ∈ G.pl.S0, v.asIdeal ∣ condF G.pl := fun v hv =>
    (dvd_pow_self _ (by unfold condExp; split_ifs <;> omega)).trans (Finset.dvd_prod_of_mem _ hv)
  have good : ∀ p : ℕ, p.Prime → ∀ v ∈ G.pl.S0, (p : 𝓞 D.host.F) ∈ v.asIdeal → p.Prime ∧ p ≠ 2 ∧ ¬ (p : ℤ) ∣ discr D.host.E ∧
      ∀ P : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ P.asIdeal → Ideal.absNorm P.asIdeal = p := by
    intro p hp v hv hpv
    obtain ⟨-, -, l, hl, h2, h3, h4, h5⟩ := hb.2.2 v (hdvd v hv)
    obtain rfl : l = p := prime_unique (K := D.host.F) hl hp h3 hpv
    exact ⟨hl, h2, h4, h5⟩
  have ex : ∀ p : ℕ, p.Prime → ∃ v : HeightOneSpectrum (𝓞 D.host.F), (p : 𝓞 D.host.F) ∈ v.asIdeal := by
    intro p hp
    have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
    obtain ⟨Q, hQ, hv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.F) (Ideal.span {(p : ℤ)})
    have hne : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot (p := Ideal.span {(p : ℤ)}) (by simpa using hp.ne_zero) Q
    refine ⟨⟨Q, hQ.isPrime, hne⟩, ?_⟩
    have h1 : (p : ℤ) ∈ Q.under ℤ := hv.over ▸ Ideal.mem_span_singleton_self _
    rw [Ideal.under_def, Ideal.mem_comap] at h1
    simpa using h1
  have hP : GlobalTheory.LamTie.PlacesOk D.host (q0 D) (G.pl.w G.pl.v0) := by
    refine ⟨?_, ?_, fun p hp => ?_⟩
    · refine (FieldDatPf.natCast_mem_below _ _).1 ?_
      rw [hw0]; exact G.pl.basePlace_over_qZero
    · have a1 := D.host.g_ne
      have a2 := D.host.pde_ne
      have a3 := D.host.pde_ne_g 0
      have a4 := D.host.pde_ne_g 1
      have a5 : q0 D ≠ D.host.g 0 := fun e => hv0.1 (e ▸ G.pl.basePlace_over_qZero)
      have a6 : q0 D ≠ D.host.g 1 := fun e => hv0.2.1 (e ▸ G.pl.basePlace_over_qZero)
      have a7 := leastSplitAuxiliaryPrime_ne_typePrimes D
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, not_false_eq_true,
        and_true]
      omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · obtain ⟨v, hv⟩ := ex _ (D.host.g_prime 0)
        exact good _ (D.host.g_prime 0) v (G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 (Or.inl hv)))) hv
      · obtain ⟨v, hv⟩ := ex _ (D.host.g_prime 1)
        exact good _ (D.host.g_prime 1) v (G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 (Or.inr (Or.inl hv))))) hv
      · obtain ⟨v, hv⟩ := ex _ D.host.pde_prime
        exact good _ D.host.pde_prime v (G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 (Or.inr (Or.inr (Or.inl hv)))))) hv
      · obtain ⟨v, hv⟩ := ex _ D.host.pde'_prime
        exact good _ D.host.pde'_prime v (G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 (Or.inr (Or.inr (Or.inr hv)))))) hv
      · exact good _ (leastSplitAuxiliaryPrimeThetaChain_spec D).1 _ (G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl)) G.pl.basePlace_over_qZero
  have hexp : ∀ v : HeightOneSpectrum (OF D.host.E),
      expIn (GlobalTheory.LamTie.cond0 D.host (G.pl.w G.pl.v0)) v = expIn (condF G.pl) v := by
    intro v
    obtain ⟨w, rfl⟩ := FieldDatPf.exists_above v
    obtain ⟨h2, h1, h0⟩ := GlobalTheory.LamTie.expIn_cond0 D.R D.host _ _ hP w
    have h4 : GlobalTheory.LamTie.Over4 D.host w ↔ below w ∈ S1 D := by
      rw [S1_mem_OmF, GlobalTheory.LamTie.Over4, Fin.exists_fin_two, or_assoc]
      exact or_congr (FieldDatPf.natCast_mem_below w _).symm (or_congr (FieldDatPf.natCast_mem_below w _).symm
        (or_congr (FieldDatPf.natCast_mem_below w _).symm (FieldDatPf.natCast_mem_below w _).symm))
    rw [hw0] at h1 h0
    refine Eq.trans ?_ (FieldDatPf.expIn_condF' G.pl (below w)).symm
    by_cases e : below w = G.pl.v0
    · rw [(h1 e).2, if_pos (G.pl.mem_S0_of_sum_eq.2 (Or.inl e)), condExp, if_pos e]
    · by_cases e' : below w ∈ S1 D
      · rw [h2 (h4.2 e'), if_pos (G.pl.mem_S0_of_sum_eq.2 (Or.inr e')), condExp, if_neg e]
      · rw [h0 (fun h => e' (h4.1 h)) e, if_neg fun h => (G.pl.mem_S0_of_sum_eq.1 h).elim e e']
  have hne : GlobalTheory.LamTie.cond0 D.host (G.pl.w G.pl.v0) ≠ ⊥ := by
    refine mul_ne_zero (pow_ne_zero _ ?_) (below _).ne_bot
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    have := (D.host.g_prime 0).pos
    have := (D.host.g_prime 1).pos
    have := D.host.pde_prime.pos
    have := D.host.pde'_prime.pos
    positivity
  rw [← Ideal.finprod_heightOneSpectrum_pow_multiplicity hne, ← Ideal.finprod_heightOneSpectrum_pow_multiplicity hb.1]
  exact finprod_congr fun v => congrArg _ (hexp v)

section Record

open GlobalTheory.ToricDenom GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {i : X.Tw}
  {Q : Finset (HeightOneSpectrum (𝓞 D.host.E))}

theorem thEval_eq_twisted {k : ℕ} {ψ : X.RCG i Q →* (X.Ok i k)ˣ} {ι : ℂ →+* Kbar X i}
    {J : FractionRing (X.Ok i k) →+* Kbar X i}
    (hJ : ∀ x, J (BlochKatoReduction.Gen.kMap X i k x) = algebraMap (FractionRing (X.O i)) (Kbar X i) x)
    {I : Type} [Fintype I] {φ : I → D.host.E →+* ℂ} {s : ℕ} {κ : I → ℕ} {c : Ideal (OF D.host.E)}
    {χ : HChar D.host.E} {lam : X.abelian₂ i} {u : Kbar X i} [Finite (PicO c)] {π : PicO c →* X.RCG i Q} {T : PicO c → ℂ}
    {θ : PicO c →* ℂˣ} (hθ : ∀ q, ι (θ q) = J (algebraMap (X.Ok i k) _ (ψ (π q) : X.Ok i k)))
    (hT : ∀ q, IsClassTerm φ s κ c χ q.out (T q))
    (hδ : ∀ δ, algebraMap (FractionRing (X.O i)) (Kbar X i) (X.th i Q lam δ) = u * ι (∑ᶠ q ∈ {q | π q⁻¹ = δ}, T q))
    {t : ℂ} (ht : IsTwistedSum φ s κ c χ θ t) : J (BlochKatoReduction.Gen.thEval X i Q lam k ψ) = u * ι t := by
  classical
  have := Fintype.ofFinite (PicO c)
  have e : t = ∑ q, T q * (θ q⁻¹ : ℂ) := by
    choose S hS hTq using hT
    refine ht.unique ⟨inferInstance, S, hS, ?_⟩
    rw [finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hTq, map_inv, Units.val_inv_eq_inv_val, lamF]
    ring
  rw [e, ← Finset.sum_fiberwise Finset.univ (fun q => π q⁻¹), map_sum, Finset.mul_sum, BlochKatoReduction.Gen.thEval, map_sum]
  refine Finset.sum_congr rfl fun δ _ => ?_
  rw [map_mul, hJ, hδ, show {q | π q⁻¹ = δ} = ↑(Finset.univ.filter fun q => π q⁻¹ = δ) by ext; simp,
    finsum_mem_coe_finset, map_sum, map_sum, mul_assoc, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun q hq => by rw [map_mul, hθ, (Finset.mem_filter.1 hq).2]

theorem sum_th_eq {ι : ℂ →+* Kbar X i}
    {I : Type} [Fintype I] {φ : I → D.host.E →+* ℂ} {s : ℕ} {κ : I → ℕ} {c : Ideal (OF D.host.E)}
    {χ : HChar D.host.E} {lam : X.abelian₂ i} {u : Kbar X i} [Finite (PicO c)] {π : PicO c →* X.RCG i Q} {T : PicO c → ℂ}
    (hT : ∀ q, IsClassTerm φ s κ c χ q.out (T q))
    (hδ : ∀ δ, algebraMap (FractionRing (X.O i)) (Kbar X i) (X.th i Q lam δ) = u * ι (∑ᶠ q ∈ {q | π q⁻¹ = δ}, T q))
    {t : ℂ} (ht : IsToricSum φ s κ c χ t) :
    algebraMap (FractionRing (X.O i)) (Kbar X i) (∑ δ, X.th i Q lam δ) = u * ι t := by
  obtain ⟨J, hJ⟩ := GlobalTheory.ToricDistribution.exists_emb X i 0
  have h := thEval_eq_twisted (ψ := 1) (θ := 1) hJ (fun q => by simp) hT hδ (t := t)
    (by simpa [IsTwistedSum, IsToricSum, lamF] using ht)
  rw [← h, ← hJ, BlochKatoReduction.Gen.thEval, map_sum]
  simp

end Record

open GlobalTheory.ToricDenom in

theorem exists_pow_char {D : D7} {C : Formalism.L2.Host.CharFrame D} {nch : NChoice D} {Tp : Formalism.L2.Host.TupTied D C nch}
    (hψ : Formalism.L2.Host.PsiChoiceCompatible D C nch Tp) {w : D.what₂.places.Pl} (hw : TwistedAt D w)
    (hval : (Tp.psi w).ValuesIn 0 D.what₂.embLL) (ι : ℂ →+* Kbar D.ntw (nch.twI w))
    (J : FractionRing (D.ntw.Ok (nch.twI w) (nch.k' w)) →+* Kbar D.ntw (nch.twI w)) :
    ∃ e : ℤ, IsCoprime e (D.ntw.l (nch.twI w) : ℤ) ∧ ∀ {c : Ideal (OF D.host.E)}, c ≠ ⊥ →
      ∀ π : PicO c →* D.ntw.RCG (nch.twI w) (nch.Q w), IsRecMap D.ntw (nch.twI w) (nch.Q w) π → ∀ y : (Af D.host.E)ˣ,
        ι ((finPart (Tp.psi w) y ^ e : ℂˣ) : ℂ) = J (algebraMap (D.ntw.Ok (nch.twI w) (nch.k' w)) _
          (nch.psi' w (π (QuotientGroup.mk y)) : D.ntw.Ok (nch.twI w) (nch.k' w))) := by
  classical
  have hl := (D.ntw.lPrime (nch.twI w)).out
  have := nch.Oe_fin w
  obtain ⟨g, hg⟩ := exists_extend (nch.Oe_inj w) (J.comp (algebraMap (D.ntw.Ok (nch.twI w) (nch.k' w)) _))
    (J.injective.comp (IsFractionRing.injective _ _))
  obtain ⟨n, hn⟩ := GlobalTheory.ToricDistribution.exists_exponent D.ntw (nch.twI w) (nch.Q w)
  obtain ⟨e, he, hpow⟩ := exists_pow_of_two_emb (ι.comp D.what₂.embLL) (g.comp (nch.embW w)) hl n
  obtain ⟨r, hr⟩ := GlobalTheory.ToricDistribution.exists_complex_char ι
    ((Units.map (J.comp (algebraMap (D.ntw.Ok (nch.twI w) (nch.k' w)) _)).toMonoidHom).comp (nch.psi' w))
    (pow_ne_zero n hl.ne_zero) fun x => by rw [← map_pow, hn, map_one]
  refine ⟨e, he, fun {c} hc π hπ y => ?_⟩
  have key := GlobalTheory.ToricDistribution.pic_char_eq_finPart hc (r.comp π) (Tp.psi w ^ e) (D.ntw.S0 (nch.twI w) ∪ nch.Q w)
    (fun P hP => ?_) y
  · have e1 : finPart (Tp.psi w ^ e) y = finPart (Tp.psi w) y ^ e := rfl
    rw [← e1, ← key]
    exact hr _
  rw [Finset.mem_union, not_or] at hP
  have hu : (Tp.psi w).UnrAt P := ((Tp.psi_is w hw).ram P).2 hP.2
  refine ⟨fun x hx => ?_, ?_⟩
  · show (Tp.psi w).loc P x ^ e = 1
    rw [hu x hx, one_zpow]
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob (D.nd.plOm.2 P)
  obtain ⟨y0, hy0⟩ := hval P hu
  have hy1 : D.what₂.embLL y0⁻¹ = (((Tp.psi w).val P)⁻¹ : ℂˣ).1 := by
    rw [map_inv₀, hy0, Units.val_inv_eq_inv_val]
    simp [Formalism.L2.Host.HChar.valTw]
  have h1 := hψ w hw P hP.2 (fun h => hP.1 (D.ntw.twistExcludedPlaces_contains_residueChar _ (by rw [nch.twI_l]; exact h))) _ σ (D.nd.plOm.2 P) hσ _ hy1
  have h2 : g (nch.embW w y0⁻¹) = ι (r (D.ntw.art (nch.twI w) (nch.Q w) σ)) := by
    rw [h1, hg, hr]; rfl
  have h3 : y0⁻¹ ^ (D.ntw.l (nch.twI w) ^ n) = 1 := by
    apply (g.comp (nch.embW w)).injective
    rw [map_pow, map_one, RingHom.comp_apply, h2, ← map_pow, ← Units.val_pow_eq_pow_val, ← map_pow, hn, map_one,
      Units.val_one, map_one]
  have h4 := hpow _ h3
  rw [RingHom.comp_apply, RingHom.comp_apply, h2, hy1, ← map_zpow₀, ← Units.val_zpow_eq_zpow_val] at h4
  have h5 := Units.ext (ι.injective h4)
  rw [MonoidHom.comp_apply, hπ P hP.1 hP.2 σ hσ, map_inv, h5, inv_zpow, inv_inv]
  rfl

end GlobalTheory.ThmAUpper.Read

namespace GlobalTheory.ThmAUpper

open Read GlobalTheory.ToricDenom GlobalTheory.FunObj.SqNum in

theorem read_twisted : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (CF : ℝ) (d : FunIn p CF), p.Rows → Fitted (@Comparison₂) p CF d → GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.ToricRatioConjugates → (∃ (_ : IsCMField D.host.E) (_ : IsAbelianGalois ℚ D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData D.host.d (GlobalTheory.FunObj.SqNum.cmPhi D) ∧
    GlobalTheory.CMVal.IsBaseCond (GlobalTheory.FunObj.SqNum.condF d.G.pl) ∧ ∃ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ) → ∀ w : D.what₂.places.Pl, TwistedAt D w → ∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j →
    ∀ (T₀ : ℂ) (ψc : PicO (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) →* ℂˣ) (T : (PicO (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) →* ℂˣ) → ℂ), IsValChar (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (GlobalTheory.FunObj.SqNum.condF d.G.pl) ∅ (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) →
      IsToricSum (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (GlobalTheory.FunObj.SqNum.condF d.G.pl) (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) T₀ → T₀ ≠ 0 →
      (∀ y, finPart (p.Tp.psi w) y = ψc (QuotientGroup.mk y)) →
      (∀ ψ, GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.IsTwistedSum (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) ψ (T ψ)) → (∃ ι : ℂ →+* GlobalTheory.ToricDenom.Kbar D.ntw (ex.nch.twI w),
        (∀ x : D.LL0, ι (D.what₂.embLL (x : D.what₂.LL)) = GlobalTheory.ToricDenom.toBar D.ntw (ex.nch.twI w) (D.ntw.emb0 (ex.nch.twI w) x)) ∧
        ∀ b : Bool, ∃ (lam : D.ntw.abelian₂ (ex.nch.twI w)) (jk : FractionRing (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)) →+* GlobalTheory.ToricDenom.Kbar D.ntw (ex.nch.twI w)) (c : ℤ),
            D.ntw.sideL (ex.nch.twI w) lam = b ∧ IsCoprime c (D.ntw.l (ex.nch.twI w) : ℤ) ∧
            jk.comp (BlochKatoReduction.Gen.kMap D.ntw (ex.nch.twI w) (ex.nch.k' w)) = algebraMap (FractionRing (D.ntw.O (ex.nch.twI w))) (GlobalTheory.ToricDenom.Kbar D.ntw (ex.nch.twI w)) ∧
            ∀ a : ℤ, jk (BlochKatoReduction.Gen.thEval D.ntw (ex.nch.twI w) (ex.nch.Q w) lam (ex.nch.k' w) (BlochKatoReduction.Gen.psiAt (D.ntw.sideL (ex.nch.twI w) lam) (ex.nch.psi' w ^ a))) *
                GlobalTheory.ToricDenom.atSide D.ntw b ι T₀ =
              jk (BlochKatoReduction.Gen.kMap D.ntw (ex.nch.twI w) (ex.nch.k' w) (∑ δ, D.ntw.th (ex.nch.twI w) ∅ lam δ)) * GlobalTheory.ToricDenom.atSide D.ntw b ι (T (ψc ^ (c * a)))) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p CF d hp hfit _ hF w hw i j s hs1 hs2 T₀ ψc T _ h0 _ hψ hT'
  obtain ⟨_, _, -, hb, -⟩ := hF
  obtain ⟨-, ι, hι, -, hall⟩ := hfit.1.list _ (hfit.1.setting.inW1 hw)
  refine ⟨ι, hι, fun b => ?_⟩
  have hi := i.2
  let a : Fin D.R.m := ⟨D.R.m - i - 1, by omega⟩
  have ha : a.1 + 1 = D.R.m - i := by simp only [a]; omega
  have hsN : s ≤ BlochKatoReduction.Gen.NFun D.R + 1 := by
    have h3 : halfRank D i j ≤ GlobalTheory.ChiGrid.bigN D := by
      have a : GlobalTheory.ChiGrid.rankV D (i + 1) (j + 1) ≤ GlobalTheory.ChiGrid.bigN D := by
        have h1 : (j + 1) * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ j.2
        have h2 : (i + 1) * GlobalTheory.ChiGrid.sLen D ≤ D.R.m * GlobalTheory.ChiGrid.sLen D := Nat.mul_le_mul_right _ i.2
        simp only [GlobalTheory.ChiGrid.rankV, GlobalTheory.ChiGrid.bigN, Ranks.r, mul_add] at *
        omega
      have e : GlobalTheory.ChiGrid.rankV D (i + 1) (j + 1) = GlobalTheory.ChiGrid.rankV D i j + D.R.t + GlobalTheory.ChiGrid.sLen D := by
        simp only [GlobalTheory.ChiGrid.rankV]; ring
      unfold halfRank; omega
    have h12 : BlochKatoReduction.Gen.NFun D.R = GlobalTheory.ChiGrid.bigN D := GlobalTheory.LamTie.nFun_eq_bigN D
    omega
  obtain ⟨lam, hlam, -, hth⟩ := hall j a s b hs1 hsN
  have e1 : GlobalTheory.LamTie.cond0 D.host (lamOf d.G).w0 = condF d.G.pl := cond0_eq d.G hb
  have e2 : (lamOf d.G).lam0 (D.ntw.l (ex.nch.twI w)) j a =
      nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w) := by
    rw [lambdaGrid_apply, ha, ex.nch.twI_l, nuH, xiH_base p, mul_one, div_mul_eq_mul_div]
  have e3 : GlobalTheory.LamTie.phi D.host ∘ D.eTau = cmPhi D := rfl
  have e4 : (lamOf d.G).kap j a s ∘ D.eTau = kap D 1 i j s := by
    funext τ
    simp only [Function.comp, GlobalTheory.LamTie.LamDat.kap, lamOf, kap, Formalism.L2.Host.eExp, Equiv.symm_apply_apply, ha]
    have : (GlobalTheory.ChiGrid.num D 1 τ).e (j + 1) = ⌊(D.hc τ).e j⌋ := by
      show GlobalTheory.SignedHC.GridData.extend 1 (D.hc τ).e (j + 1) = _
      simp [GlobalTheory.SignedHC.GridData.extend]
    rw [this]
  rw [e1, e2] at hth
  obtain ⟨u, -, hth⟩ := hth
  obtain ⟨_, π, t, hπ, ht, hδ⟩ := hth _ (hfit.1.cond w hw)
  obtain ⟨_, π0, t0, -, ht0, hδ0⟩ := hth ∅ ⟨by simp, by simp, by simp⟩
  replace ht := fun q => isClassTerm_reindex D.eTau (ht q)
  replace ht0 := fun q => isClassTerm_reindex D.eTau (ht0 q)
  rw [e3, e4] at ht ht0
  have e5 : condQ (condF d.G.pl) (belowSet (∅ : Finset (HeightOneSpectrum (𝓞 D.host.E)))) = condF d.G.pl := by
    simp [condQ, belowSet]
  have s0 := sum_th_eq ht0 hδ0 (t := T₀) (by rw [e5]; exact h0)
  obtain ⟨J, hJ⟩ := GlobalTheory.ToricDistribution.exists_emb D.ntw (ex.nch.twI w) (ex.nch.k' w)
  obtain ⟨e, he, hchar⟩ := exists_pow_char hfit.1.psi hw (hp.ties.psiVal w hw) (atSide D.ntw b ι) J
  have hc : condQ (condF d.G.pl) (belowSet (ex.nch.Q w)) ≠ ⊥ :=
    mul_ne_zero hb.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)
  have key : ∀ a : ℤ, J (BlochKatoReduction.Gen.thEval D.ntw (ex.nch.twI w) (ex.nch.Q w) lam (ex.nch.k' w) (ex.nch.psi' w ^ a)) =
      u * atSide D.ntw b ι (T (ψc ^ (e * a))) := fun a => by
    refine thEval_eq_twisted hJ (fun q => ?_) ht hδ (hT' _)
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 := hchar hc π hπ y
    have h2 : ∀ (x : (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w))ˣ), J (algebraMap (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)) _ (x ^ a : _ˣ)) =
        J (algebraMap (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)) _ x) ^ a := fun x => by
      have := congrArg Units.val (map_zpow (Units.map (J.comp
        (algebraMap (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)) _)).toMonoidHom) x a)
      rw [Units.val_zpow_eq_zpow_val] at this
      exact this
    rw [MonoidHom.zpow_apply, MonoidHom.zpow_apply, h2, ← h1, hψ, zpow_mul, Units.val_zpow_eq_zpow_val _ a, map_zpow₀]
  refine ⟨lam, J, if b then e else -e, hlam, by cases b <;> simp [he, he.neg_left], RingHom.ext hJ, fun a => ?_⟩
  rw [hJ, s0, hlam]
  cases b
  · have : BlochKatoReduction.Gen.psiAt false (ex.nch.psi' w ^ a) = ex.nch.psi' w ^ (-a) := by simp [BlochKatoReduction.Gen.psiAt]
    rw [this, key]
    simp only [Bool.false_eq_true, if_false, mul_neg, neg_mul]
    ring
  · have : BlochKatoReduction.Gen.psiAt true (ex.nch.psi' w ^ a) = ex.nch.psi' w ^ a := rfl
    rw [this, key]
    simp only [if_true]
    ring

end GlobalTheory.ThmAUpper
