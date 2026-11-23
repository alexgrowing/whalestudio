import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.ConjReal
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.JetSumTable
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StandardKernelAtTorus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemDivsOfMem

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.Proof.NarrowJetMoments

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke

section Notions

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

omit [NumberField E] in

theorem adj_eq (x : HomE E a b) : JetSumTable.adj x = StandardKernelAtTorus.adj x := by
  refine LinearMap.pi_ext' fun β => LinearMap.ext_ring ?_
  funext α
  have h1 := JetSumTable.adj_single x α β
  have h2 := StandardKernelAtTorus.adj_single x β α
  simpa using h1.trans h2.symm

variable {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))}

theorem suppBar_eq (d : Deco E a ST SG) (d' : Deco E b ST SG') : JetSumTable.suppBar d d' = StandardKernelAtTorus.suppPts d d' := rfl

theorem support_eq_dualPoints (d : Deco E a ST SG) (d' : Deco E b ST SG') : JetSumTable.suppP d d' = StandardKernelAtTorus.dualPts d d' := by
  ext x
  simp only [JetSumTable.suppP, StandardKernelAtTorus.dualPts, Set.mem_setOf_eq, adj_eq]

theorem stdAtT_iff {n : ℕ} (d : Deco E n ST SG) : JetSumTable.StdAtT d ↔ StandardKernelAtTorus.StdAtT d := Iff.rfl

end Notions

section Closure

variable {p : ℕ} [Fact p.Prime]

theorem closure_iff {H I : Type} (Z : Set H) (mom : H → I → ℂ_[p]) (G : Set I) (t : I → ℂ_[p]) (κ : ℂ_[p]) :
    JetSumTable.InIntClosure Z (fun x m => κ * mom x m) G t ↔ StandardKernelAtTorus.InMomClosure G t κ Z mom := by
  classical
  refine forall_congr' fun M => ?_
  refine imp_congr Iff.rfl (forall_congr' fun ε => imp_congr Iff.rfl ⟨?_, ?_⟩)
  · rintro ⟨c, hs, hc, hm⟩
    refine ⟨c.support.card, fun i => c (c.support.equivFin.symm i), fun i => c.support.equivFin.symm i, fun i => hc _,
      fun i => hs (c.support.equivFin.symm i).2, fun m hmM => ?_⟩
    have e : κ * ∑ i, c (c.support.equivFin.symm i) * mom (c.support.equivFin.symm i) m =
        c.sum fun x r => r * (κ * mom x m) := by
      rw [Equiv.sum_comp c.support.equivFin.symm fun x : c.support => c x * mom x m,
        Finset.sum_coe_sort c.support fun x => c x * mom x m, Finsupp.sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e]
    exact hm m hmM
  · rintro ⟨n, r, z, hr, hz, hm⟩
    refine ⟨∑ i, Finsupp.single (z i) (r i), ?_, ?_, fun m hmM => ?_⟩
    · intro x hx
      by_contra hn
      refine Finsupp.mem_support_iff.1 (Finset.mem_coe.1 hx) ?_
      rw [Finsupp.finset_sum_apply]
      refine Finset.sum_eq_zero fun i _ => Finsupp.single_eq_of_ne ?_
      intro h
      exact hn (h ▸ hz i)
    · intro x
      rw [Finsupp.finset_sum_apply]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
      rw [Finsupp.single_apply]
      split_ifs
      · exact hr i
      · simp
    · have e : ((∑ i, Finsupp.single (z i) (r i)).sum fun x r => r * (κ * mom x m)) = κ * ∑ i, r i * mom (z i) m := by
        rw [← Finsupp.sum_finset_sum_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _), Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finsupp.sum_single_index (zero_mul _)]
        ring
      rw [e]
      exact hm m hmM

variable {X : Fields} {a b : ℕ}

theorem induces_iff (ι : X.K →+* ℂ_[p]) (w : HeightOneSpectrum (𝓞 X.K)) : JetSumTable.Induces ι w ↔ StandardKernelAtTorus.Induces ι w :=
  forall_congr' fun _ => Iff.comm

theorem ptTab_eq (ι : X.K →+* ℂ_[p]) (u : X.Tau → ℂ_[p]) :
    (JetSumTable.ptTab ι u : HomE X.E a b → _) = StandardKernelAtTorus.diracMom ι u := by
  funext x m
  simp only [JetSumTable.ptTab, StandardKernelAtTorus.diracMom, adj_eq]

end Closure

section Data

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}
  {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)}

theorem homAt_anti {S S' : Finset (HeightOneSpectrum (𝓞 E))} (h : S ⊆ S') : homAt S' N N' ≤ homAt S N N' :=
  fun _ hx P hP => hx P (h hP)

theorem mulLat_mul {S : Finset (HeightOneSpectrum (𝓞 E))} {T : ℕ} (hT0 : T ≠ 0) (hT : ∀ P ∈ S, (T : 𝓞 E) ∉ P.asIdeal) (c : ℕ) :
    mulLat (T * c) (homAt S N N') = mulLat c (homAt S N N') := by
  have hTE : (T : E) ≠ 0 := Nat.cast_ne_zero.2 hT0
  have hs : ∀ y : HomE E a b, (T : 𝓞 E) • y = (T : E) • y := fun y => by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    refine ⟨(T : 𝓞 E) • y, Submodule.smul_mem _ _ hy, ?_⟩
    simp only [LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_mul]
    rw [mul_comm, mul_smul]
  · rintro _ ⟨y, hy, rfl⟩
    refine ⟨(T : E)⁻¹ • y, ?_, ?_⟩
    · intro P hP v hv
      obtain ⟨s, hs1, hs2⟩ := hy P hP v hv
      refine ⟨s * (T : 𝓞 E), P.asIdeal.primeCompl.mul_mem hs1 (hT P hP), ?_⟩
      have e : (T : 𝓞 E) • ((T : E)⁻¹ • y) v = y v := by
        rw [← LinearMap.smul_apply, hs, smul_inv_smul₀ hTE]
      rw [mul_smul, e]
      exact hs2
    · simp only [LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_mul]
      rw [mul_comm, mul_smul, hs, smul_inv_smul₀ hTE]

end Data

section Datum

variable {X : Fields} {a b : ℕ} {SB Sall : Finset (HeightOneSpectrum (𝓞 X.E))} {T cA cB' : ℕ}
  {N : Submodule (𝓞 X.E) (Sp X.E a)} {N' : Submodule (𝓞 X.E) (Sp X.E b)} {w : HeightOneSpectrum (𝓞 X.K)}

theorem datum_of_off (hS : SB ⊆ Sall) (hT0 : T ≠ 0) (hT : ∀ P ∈ SB, (T : 𝓞 X.E) ∉ P.asIdeal) {Ξ : HomE X.E a b → X.K}
    (h : JetSumTable.OffDatum cA (T * cB') N N' SB w Ξ) : StandardKernelAtTorus.DatumOffT SB Sall cA cB' N N' w Ξ := by
  have hm : divLat cA (homAt Sall N N') ≤ divLat cA (homAt SB N N') := Submodule.comap_mono (homAt_anti hS)
  refine ⟨fun x _ x' hx' hd => ?_, fun x hx => (h x (hm hx)).1⟩
  have := (h x' (hm hx')).2 (x - x') (by rwa [mulLat_mul hT0 hT])
  rwa [add_sub_cancel] at this

theorem off_of_datum (hT0 : T ≠ 0) (hT : ∀ P ∈ SB, (T : 𝓞 X.E) ∉ P.asIdeal) {Φ : HomE X.E a b → X.K}
    (h : StandardKernelAtTorus.DatumOffT SB Sall cA cB' N N' w Φ) :
    ∃ Ξ, JetSumTable.OffDatum cA (T * cB') N N' SB w Ξ ∧ ∀ x ∈ divLat cA (homAt Sall N N'), Ξ x = Φ x := by
  classical
  let R : HomE X.E a b → HomE X.E a b → Prop := fun x x' =>
    x' ∈ divLat cA (homAt Sall N N') ∧ x - x' ∈ mulLat cB' (homAt SB N N')
  refine ⟨fun x => if hx : ∃ x', R x x' then Φ hx.choose else 0, fun x _ => ⟨?_, fun y hy => ?_⟩, fun x hx => ?_⟩
  · beta_reduce
    split_ifs with hx
    · exact h.2 _ hx.choose_spec.1
    · simp
  · rw [mulLat_mul hT0 hT] at hy
    have e : R (x + y) = R x := by
      funext x'
      refine propext (and_congr Iff.rfl ?_)
      rw [add_sub_right_comm]
      exact Submodule.add_mem_iff_left _ hy
    simp only [e]
  · have hx' : ∃ x', R x x' := ⟨x, hx, by rw [sub_self]; exact zero_mem _⟩
    beta_reduce
    rw [dif_pos hx']
    exact (h.1 _ hx _ hx'.choose_spec.1 hx'.choose_spec.2).symm

variable (A : Amb X)

theorem jetSum_eq (cB : ℕ) (Ξ : HomE X.E a b → X.K) :
    JetSumTable.jetSum A Sall cA cB N N' Ξ = StandardKernelAtTorus.kerTable A Sall cA cB N N' Ξ := rfl

theorem ratIdx_eq (cB : ℕ) (Ξ : HomE X.E a b → X.K) :
    JetSumTable.RatIdx A Sall cA cB N N' Ξ = {m | StandardKernelAtTorus.RatAt A Sall cA cB N N' Ξ m} := rfl

theorem jetSum_congr (cB : ℕ) {Ξ Ξ' : HomE X.E a b → X.K} (h : ∀ x ∈ divLat cA (homAt Sall N N'), Ξ x = Ξ' x) :
    JetSumTable.jetSum A Sall cA cB N N' Ξ = JetSumTable.jetSum A Sall cA cB N N' Ξ' := by
  funext m
  unfold JetSumTable.jetSum latSum
  refine finsum_congr fun z => ?_
  beta_reduce
  rw [h _ (Subtype.property _)]

theorem ratIdx_congr (cB : ℕ) {Ξ Ξ' : HomE X.E a b → X.K} (h : ∀ x ∈ divLat cA (homAt Sall N N'), Ξ x = Ξ' x) :
    JetSumTable.RatIdx A Sall cA cB N N' Ξ = JetSumTable.RatIdx A Sall cA cB N N' Ξ' := by
  ext m
  refine forall₂_congr fun x hx => ?_
  rw [h x hx]

end Datum

section Clause

variable {X : Fields} (A : Amb X) (Pr : Primes X) (u : Pr.Word) {p : ℕ} [Fact p.Prime] (w : HeightOneSpectrum (𝓞 X.K))
  (ι : X.K →+* ℂ_[p]) (uu : X.Tau → ℂ_[p]) {a b : ℕ} (SB Sall : Finset (HeightOneSpectrum (𝓞 X.E)))
  {SG SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (d : DecoSet X.E a (Pr.vT u) SG) (d' : DecoSet X.E b (Pr.vT u) SG')

def ConclA (cA cB : ℕ) (Ξ₀ : HomE X.E a b → X.K) : Prop :=
  (seenBarC Pr u w →
    JetSumTable.InIntClosure (JetSumTable.suppBar d.1 d'.1) (JetSumTable.ptTab ι uu)
      (JetSumTable.RatIdx A Sall cA cB d.1.N d'.1.N fun x => phiT X.K d.1 d'.1 x * Ξ₀ x)
      fun m => ι (JetSumTable.jetSum A Sall cA cB d.1.N d'.1.N (fun x => phiT X.K d.1 d'.1 x * Ξ₀ x) m)) ∧
  (seenC Pr u w →
    JetSumTable.InIntClosure (JetSumTable.suppP d.1 d'.1) (fun x m => ((p : ℂ_[p]) ^ (X.f * a))⁻¹ * JetSumTable.ptTab ι uu x m)
      (JetSumTable.RatIdx A Sall cA cB d.1.N d'.1.N fun x => phiT X.K d.1 d'.1 x * Ξ₀ x)
      fun m => ι (JetSumTable.jetSum A Sall cA cB d.1.N d'.1.N (fun x => phiT X.K d.1 d'.1 x * Ξ₀ x) m))

def ConclB (cA cB : ℕ) (Φ : HomE X.E a b → X.K) : Prop :=
  (seenBarC Pr u w →
    StandardKernelAtTorus.InMomClosure {m | StandardKernelAtTorus.RatAt A Sall cA cB d.1.N d'.1.N (fun x => phiT X.K d.1 d'.1 x * Φ x) m}
      (fun m => ι (StandardKernelAtTorus.kerTable A Sall cA cB d.1.N d'.1.N (fun x => phiT X.K d.1 d'.1 x * Φ x) m))
      1 (StandardKernelAtTorus.suppPts d.1 d'.1) (StandardKernelAtTorus.diracMom ι uu)) ∧
  (seenC Pr u w →
    StandardKernelAtTorus.InMomClosure {m | StandardKernelAtTorus.RatAt A Sall cA cB d.1.N d'.1.N (fun x => phiT X.K d.1 d'.1 x * Φ x) m}
      (fun m => ι (StandardKernelAtTorus.kerTable A Sall cA cB d.1.N d'.1.N (fun x => phiT X.K d.1 d'.1 x * Φ x) m))
      (((p : ℂ_[p]) ^ (X.f * a))⁻¹) (StandardKernelAtTorus.dualPts d.1 d'.1) (StandardKernelAtTorus.diracMom ι uu))

theorem concl_iff (cA cB : ℕ) (Ξ : HomE X.E a b → X.K) :
    ConclA A Pr u w ι uu Sall d d' cA cB Ξ ↔ ConclB A Pr u w ι uu Sall d d' cA cB Ξ := by
  unfold ConclA ConclB
  rw [← closure_iff, ← closure_iff, ptTab_eq, support_eq_dualPoints]
  simp only [one_mul]
  rfl

theorem conclA_congr (cA cB : ℕ) {Ξ Ξ' : HomE X.E a b → X.K} (h : ∀ x ∈ divLat cA (homAt Sall d.1.N d'.1.N), Ξ x = Ξ' x) :
    ConclA A Pr u w ι uu Sall d d' cA cB Ξ ↔ ConclA A Pr u w ι uu Sall d d' cA cB Ξ' := by
  have h' : ∀ x ∈ divLat cA (homAt Sall d.1.N d'.1.N), phiT X.K d.1 d'.1 x * Ξ x = phiT X.K d.1 d'.1 x * Ξ' x :=
    fun x hx => by rw [h x hx]
  unfold ConclA
  rw [jetSum_congr A cB h', ratIdx_congr A cB h']

def ClauseA (cA cB' : ℕ) : Prop :=
  ∀ Ξ₀, JetSumTable.OffDatum cA (Pr.T u * cB') d.1.N d'.1.N SB w Ξ₀ → ConclA A Pr u w ι uu Sall d d' cA (Pr.T u * cB') Ξ₀

def ClauseB (cA cB' : ℕ) : Prop :=
  ∀ Φ, StandardKernelAtTorus.DatumOffT SB Sall cA cB' d.1.N d'.1.N w Φ → ConclB A Pr u w ι uu Sall d d' cA (Pr.T u * cB') Φ

theorem clause_iff (hS : SB ⊆ Sall) (hT0 : Pr.T u ≠ 0) (hT : ∀ P ∈ SB, (Pr.T u : 𝓞 X.E) ∉ P.asIdeal) (cA cB' : ℕ) :
    ClauseA A Pr u w ι uu SB Sall d d' cA cB' ↔ ClauseB A Pr u w ι uu SB Sall d d' cA cB' := by
  constructor
  · intro h Φ hΦ
    obtain ⟨Ξ, h1, h2⟩ := off_of_datum hT0 hT hΦ
    rw [← concl_iff, ← conclA_congr A Pr u w ι uu Sall d d' cA _ h2]
    exact h Ξ h1
  · intro h Ξ hΞ
    rw [concl_iff]
    exact h Ξ (datum_of_off hS hT0 hT hΞ)

end Clause

section Bad

variable {E : Type} [Field E] [NumberField E]

theorem notMem_of_coprime {m n : ℕ} (h : Nat.Coprime m n) (P : HeightOneSpectrum (𝓞 E)) (hn : (n : 𝓞 E) ∈ P.asIdeal) :
    (m : 𝓞 E) ∉ P.asIdeal := by
  intro hm
  obtain ⟨x, y, e⟩ := Nat.isCoprime_iff_coprime.2 h
  have e' : (x : 𝓞 E) * (m : 𝓞 E) + (y : 𝓞 E) * (n : 𝓞 E) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) e
  refine (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top ?_
  rw [← e']
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hm) (Ideal.mul_mem_left _ _ hn)

theorem coprime_qOf {T : ℕ} (hT : T.Prime) (P : HeightOneSpectrum (𝓞 E)) (h : (T : 𝓞 E) ∉ P.asIdeal) : Nat.Coprime (qOf P) T := by
  obtain ⟨q, n, hn, hq, hqp, hN⟩ := Ideal.exists_prime_and_absNorm_eq_pow P.asIdeal
  unfold qOf
  rw [hN]
  refine Nat.Coprime.pow_left _ ((Nat.coprime_primes hqp hT).2 ?_)
  rintro rfl
  exact h hq

variable {X : Fields}

theorem conjP_ne_self_of_split (hX : X.Ok) {v : HeightOneSpectrum (𝓞 X.F)} (hs : SplitAt X.E v) {P : HeightOneSpectrum (𝓞 X.E)}
    (hP : P.asIdeal.under (𝓞 X.F) = v.asIdeal) : conjPrime₂ P ≠ P := by
  intro hc
  have hne : GlobalTheory.MuConj.starAlg hX.star_F ≠ 1 := by
    intro h
    obtain ⟨τ⟩ : Nonempty X.Tau := Fintype.card_pos_iff.1 hX.f_pos
    refine hX.emb_ne τ τ (RingHom.ext fun x => ?_)
    have : star x = x := congrArg (fun σ : X.E ≃ₐ[X.F] X.E => σ x) h
    show X.emb τ x = X.emb τ (star x)
    rw [this]
  have key : ∀ Q : HeightOneSpectrum (𝓞 X.E), Ideal.map (algebraMap (𝓞 X.F) (𝓞 X.E)) v.asIdeal ≤ Q.asIdeal → Q = P := by
    intro Q hQ
    have hu : Q.under (𝓞 X.F) = P.under (𝓞 X.F) := by
      refine HeightOneSpectrum.ext ?_
      show Q.asIdeal.under (𝓞 X.F) = P.asIdeal.under (𝓞 X.F)
      rw [hP]
      exact (v.isMaximal.eq_of_le (Q.under (𝓞 X.F)).isPrime.ne_top (Ideal.map_le_iff_le_comap.1 hQ)).symm
    rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (GlobalTheory.MuConj.starAlg hX.star_F) hX.rankE hne P Q).1 hu with h | h
    · exact h
    · rw [GlobalTheory.Mem.Chr.conjPl_iff_mem] at h
      rw [← hc]
      ext y
      rw [mem_conjP]
      exact (h (cO X.E y) y (star_star (y : X.E)).symm).symm
  obtain ⟨Q, Q', hQ, hm⟩ := hs
  exact hQ ((key Q (hm ▸ Ideal.mul_le_left)).trans (key Q' (hm ▸ Ideal.mul_le_right)).symm)

variable {Pr : Primes X}

theorem sq_ne_neg_g (hX : X.Ok) (hPr : Pr.Ok) (i : Fin 2) (α : X.E) : α ^ 2 ≠ -(Pr.g i : X.E) := by
  classical
  intro hα
  have hint : IsIntegral ℤ α := by
    refine IsIntegral.of_pow two_pos ?_
    rw [hα]
    exact (isIntegral_natCast _).neg
  let a : 𝓞 X.E := ⟨α, hint⟩
  have ha : a ^ 2 = -(Pr.g i : 𝓞 X.E) := by
    apply RingOfIntegers.ext
    simp only [map_pow, map_neg, map_natCast]
    exact hα
  have hdvd : ∀ P ∈ Pr.vG i, P.asIdeal ^ 2 ∣ Ideal.span {X.conjO (Pr.piG i)} := by
    intro P hP
    have h1 : X.conjO (Pr.piG i) ∈ P.asIdeal := decoFin_mem_of_mem_divs hP
    have h2 : Pr.piG i ∉ P.asIdeal := by
      intro h
      obtain ⟨x, y, e⟩ := hPr.piG_cop i
      refine (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top ?_
      rw [← e]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_left _ _ h1)
    have h3 : a ∈ P.asIdeal := by
      refine P.isPrime.mem_of_pow_mem 2 ?_
      rw [ha, ← hPr.piG_norm i]
      exact neg_mem (Ideal.mul_mem_left _ _ h1)
    have h4 : P.asIdeal ^ 2 ∣ Ideal.span {Pr.piG i} * Ideal.span {X.conjO (Pr.piG i)} := by
      rw [Ideal.span_singleton_mul_span_singleton, hPr.piG_norm i, Ideal.dvd_span_singleton, ← neg_mem_iff, ← ha]
      exact Ideal.pow_mem_pow h3 2
    exact P.prime.pow_dvd_of_dvd_mul_left 2 (fun h => h2 (Ideal.dvd_span_singleton.1 h)) h4
  have hprod : (∏ P ∈ Pr.vG i, P.asIdeal ^ 2) ∣ Ideal.span {X.conjO (Pr.piG i)} :=
    Finset.prod_dvd_of_coprime (fun P _ Q _ h => HeightOneSpectrum.isCoprime_pow_of_ne P Q h 2 2) hdvd
  have hN1 : Pr.g i ^ (2 * X.f) ∣ Ideal.absNorm (Ideal.span {X.conjO (Pr.piG i)}) := by
    have := map_dvd Ideal.absNorm hprod
    rw [map_prod, Finset.prod_congr rfl (g := fun _ => Pr.g i ^ 2) (fun P hP => by rw [map_pow, hPr.vG_norm i P hP]),
      Finset.prod_const, hPr.vG_card i, ← pow_mul] at this
    exact this
  have hrk : Module.finrank ℚ X.E = 2 * X.f := by
    rw [← Module.finrank_mul_finrank ℚ X.F X.E, hX.rankE, ← hX.card_Tau, mul_comm]
    rfl
  have hN2 : Ideal.absNorm (Ideal.span {Pr.piG i}) * Ideal.absNorm (Ideal.span {X.conjO (Pr.piG i)}) = Pr.g i ^ (2 * X.f) := by
    rw [← map_mul, Ideal.span_singleton_mul_span_singleton, hPr.piG_norm i, Ideal.absNorm_span_natCast, RingOfIntegers.rank, hrk]
  obtain ⟨k, hk⟩ := hN1
  have hpos : 0 < Pr.g i ^ (2 * X.f) := pow_pos (hPr.g_prime i).pos _
  have h1 : Ideal.absNorm (Ideal.span {Pr.piG i}) = 1 := by
    rw [hk, mul_left_comm] at hN2
    exact Nat.eq_one_of_mul_eq_one_right ((Nat.mul_eq_left hpos.ne').1 hN2)
  have hu : IsUnit (X.conjO (Pr.piG i)) :=
    (Ideal.span_singleton_eq_top.1 (Ideal.absNorm_eq_one_iff.1 h1)).map _
  obtain ⟨P, hP⟩ : (Pr.vG i).Nonempty := Finset.card_pos.1 (hPr.vG_card i ▸ hX.f_pos)
  exact P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ (decoFin_mem_of_mem_divs hP) hu)

variable {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}

theorem good_of_mem_QE {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ QE sel (mu : Chr X.F X.E X.K)) :
    ∃ v, GoodPl X.E S v ∧ sel v = P := by
  classical
  unfold QE at h
  split_ifs at h with h2
  · obtain ⟨v, hv, e⟩ := Finset.mem_image.1 h
    have hv1 : v ∈ Qprime (mu : Chr X.F X.E X.K) := by simpa using hv
    refine ⟨v, ?_, e⟩
    by_contra hn
    have h4 := (Subgroup.mem_inf.1 mu.2).2
    exact hv1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h4 v) hn)
  · simp at h

theorem notMem_of_mem_QE (hsel : IsSel X sel) {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ QE sel (mu : Chr X.F X.E X.K))
    {l : ℕ} (hl : l.Prime) (hS : l ∈ S) : (l : 𝓞 X.E) ∉ P.asIdeal := by
  intro hm
  obtain ⟨v, hgood, e⟩ := good_of_mem_QE h
  have h5 : (l : 𝓞 X.F) ∈ v.asIdeal := by
    rw [← hsel v, e, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact hm
  apply hgood.2.2
  have h6 : ringChar (𝓞 X.F ⧸ v.asIdeal) ∣ l := by
    rw [← ringChar.spec, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact h5
  haveI := v.isPrime
  rcases (Nat.dvd_prime hl).1 h6 with h7 | h7
  · exact absurd h7 CharP.ringChar_ne_one
  · change ringChar (𝓞 X.F ⧸ v.asIdeal) ∈ S
    rw [h7]
    exact hS

theorem mem_vGs_iff {P : HeightOneSpectrum (𝓞 X.E)} : P ∈ Pr.vGs ↔ ∃ i, P ∈ Pr.vG i := by
  classical
  unfold Primes.vGs
  rw [Finset.mem_union, Fin.exists_fin_two]

theorem g_mem (hPr : Pr.Ok) {i : Fin 2} {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ Pr.vG i) : (Pr.g i : 𝓞 X.E) ∈ P.asIdeal := by
  rw [← hPr.piG_norm i]
  exact Ideal.mul_mem_left _ _ (decoFin_mem_of_mem_divs h)

theorem notMem_rowSG (hPr : Pr.Ok) (hsel : IsSel X sel) {l : ℕ} (hl : l.Prime) (hS : l ∈ S) (hg : ∀ i, l ≠ Pr.g i)
    {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ rowSG Pr sel mu) : (l : 𝓞 X.E) ∉ P.asIdeal := by
  classical
  rcases Finset.mem_union.1 hP with h | h
  · obtain ⟨i, hi⟩ := mem_vGs_iff.1 h
    exact notMem_of_coprime ((Nat.coprime_primes hl (hPr.g_prime i)).2 (hg i)) P (g_mem hPr hi)
  · exact notMem_of_mem_QE hsel h hl hS

theorem natCast_mem_conjP {P : HeightOneSpectrum (𝓞 X.E)} {n : ℕ} :
    (n : 𝓞 X.E) ∈ (conjPrime₂ P).asIdeal ↔ (n : 𝓞 X.E) ∈ P.asIdeal := by
  rw [mem_conjP, map_natCast]

theorem conjP_notMem_rowSG (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hS : ∀ i, Pr.g i ∈ S)
    {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ rowSG Pr sel mu) : conjPrime₂ P ∉ rowSG Pr sel mu := by
  classical
  intro hP'
  rcases Finset.mem_union.1 hP with h | h <;> rcases Finset.mem_union.1 hP' with h' | h'
  · obtain ⟨i, hi⟩ := mem_vGs_iff.1 h
    obtain ⟨j, hj⟩ := mem_vGs_iff.1 h'
    by_cases hij : i = j
    · subst hij
      have h1 : X.conjO (Pr.piG i) ∈ P.asIdeal := decoFin_mem_of_mem_divs hi
      have h2 : cO X.E (cO X.E (Pr.piG i)) ∈ P.asIdeal :=
        (decoFin_mem_of_mem_divs hj : X.conjO (Pr.piG i) ∈ (conjPrime₂ P).asIdeal)
      rw [cO_cO] at h2
      obtain ⟨x, y, e⟩ := hPr.piG_cop i
      refine (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top ?_
      rw [← e]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h2) (Ideal.mul_mem_left _ _ h1)
    · have hne : Pr.g i ≠ Pr.g j := by
        have := hPr.g_ne
        fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
      exact notMem_of_coprime ((Nat.coprime_primes (hPr.g_prime i) (hPr.g_prime j)).2 hne) P
        (natCast_mem_conjP.1 (g_mem hPr hj)) (g_mem hPr hi)
  · obtain ⟨i, hi⟩ := mem_vGs_iff.1 h
    exact notMem_of_mem_QE hsel h' (hPr.g_prime i) (hS i) (natCast_mem_conjP.2 (g_mem hPr hi))
  · obtain ⟨i, hi⟩ := mem_vGs_iff.1 h'
    exact notMem_of_mem_QE hsel h (hPr.g_prime i) (hS i) (natCast_mem_conjP.1 (g_mem hPr hi))
  · obtain ⟨v, hv, e⟩ := good_of_mem_QE h
    obtain ⟨v', -, e'⟩ := good_of_mem_QE h'
    have hvv : v' = v := by
      ext y
      rw [← hsel v, ← hsel v', e, e', Ideal.under_def, Ideal.under_def, Ideal.mem_comap, Ideal.mem_comap, mem_conjP]
      have : cO X.E (algebraMap (𝓞 X.F) (𝓞 X.E) y) = algebraMap (𝓞 X.F) (𝓞 X.E) y :=
        RingOfIntegers.ext (hX.star_F (y : X.F))
      rw [this]
    subst hvv
    exact conjP_ne_self_of_split hX hv.1 (e ▸ hsel v') (e'.symm.trans e)

theorem offT_rowSG {D : Dat} (hD : D.Ok) {H : D7} (s : Seam H D.X) (u : D.Pr.Word) (c : ℕ)
    {sel : HeightOneSpectrum (𝓞 D.X.F) → HeightOneSpectrum (𝓞 D.X.E)} {S : Set ℕ} {mu : Tup D.X.F D.X.E D.X.K S}
    (hsel : IsSel D.X sel) (hS : hostS H.host.q H.host.d (D.Pr.g 0) (D.Pr.g 1) (Set.range D.Pr.T) ⊆ S)
    (hc : ∀ P ∈ rowSG D.Pr sel mu, Nat.Coprime c (qOf P)) :
    StandardKernelAtTorus.OffT (rowSG D.Pr sel mu) H.host.q c (D.Pr.T u) := by
  intro P hP
  refine ⟨conjP_notMem_rowSG hD.fields hD.primes hsel (fun i => hS ?_) hP,
    notMem_rowSG hD.primes hsel Nat.prime_two (hS (by simp [hostS])) (fun i h => ?_) hP,
    notMem_rowSG hD.primes hsel H.host.hyp.1 (hS (by simp [hostS])) (fun i h => ?_) hP,
    notMem_of_coprime (hc P hP) P (Ideal.absNorm_mem _),
    notMem_rowSG hD.primes hsel (hD.primes.T_prime u) (hS (by simp [hostS])) (hD.primes.T_ne_g u) hP⟩
  · fin_cases i <;> simp [hostS]
  · have h1 := hD.sizes.g_big i
    have h2 := hD.fields.f_pos
    have h3 := D.R.m_add_three_le_k
    rw [← h] at h1
    have : 1 * 1 ≤ D.X.f * D.R.k := Nat.mul_le_mul h2 (by omega)
    rw [mul_assoc] at h1
    omega
  · refine sq_ne_neg_g hD.fields hD.primes i (s.iE.symm (H.host.sqq)) ?_
    rw [← map_pow, H.host.sqq_sq, map_neg, map_natCast, h]

end Bad

def NarrowB : Prop :=
  ∀ (D : Dat), D.Ok →
  ∀ (H : D7) (s : Seam H D.X) (cc : Ideal (𝓞 H.host.K)) (δ : ℂ) (B : Base H cc δ) (χ : TaylorLogMetric.IdE H → ℂ) (cD : H.what₂.Tau → ℂ),
    JetSumTable.AnaOk D s cc δ χ cD →
    ∀ (u : D.Pr.Word) [Fact (D.Pr.T u).Prime], Nat.Coprime (Ideal.absNorm cc) (D.Pr.T u) →
    ∀ (w : HeightOneSpectrum (𝓞 D.X.K)) (ι : D.X.K →+* ℂ_[D.Pr.T u]), StandardKernelAtTorus.Induces ι w →
      ∃ un : D.X.Tau → ℂ_[D.Pr.T u], (∀ τ, ‖un τ‖ = 1) ∧
        ∀ (sel : HeightOneSpectrum (𝓞 D.X.F) → HeightOneSpectrum (𝓞 D.X.E)) (S : Set ℕ) (mu : Tup D.X.F D.X.E D.X.K S)
          (cst : LocCst D.X (rowSG D.Pr sel mu)),
          IsSel D.X sel → hostS H.host.q H.host.d (D.Pr.g 0) (D.Pr.g 1) (Set.range D.Pr.T) ⊆ S →
          (∀ P ∈ rowSG D.Pr sel mu, Nat.Coprime (Ideal.absNorm cc) (qOf P)) →
          ∀ (i b : ℕ), i < D.R.m → b = D.R.N (i + 1) →
          ∀ (SG SG' : Finset (HeightOneSpectrum (𝓞 D.X.E)))
            (d : DecoSet D.X.E (D.R.N i) (D.Pr.vT u) SG) (d' : DecoSet D.X.E b (D.Pr.vT u) SG'),
            StandardKernelAtTorus.StdAtT d.1 → StandardKernelAtTorus.StdAtT d'.1 →
            ClauseB (ambOf s B χ cD) D.Pr u w ι un (rowSG D.Pr sel mu) (Sall sel mu u) d d' (cAof sel mu cst)
              ((∏ P : rowSG D.Pr sel mu, qOf P.1) ^ cst.B)

def WideA : Prop :=
  ∀ (D : D7) (X : Fields) (s : Seam D X), s.Ok → X.Ok →
  ∀ (Pr : Primes X), Pr.Ok → X.IsCond Pr.cond →
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
  ∀ (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ), TaylorLogMetric.IsChi D χ → IsDgen D cD →
  ∀ (u : Pr.Word), Nat.Coprime (Ideal.absNorm cc) (Pr.T u) →
  ∀ (p : ℕ) [Fact p.Prime], p = Pr.T u →
  ∀ (w : HeightOneSpectrum (𝓞 X.K)) (ι : X.K →+* ℂ_[p]), JetSumTable.Induces ι w →
    ∃ uu : X.Tau → ℂ_[p], (∀ τ, ‖uu τ‖ = 1) ∧
      ∀ (a b : ℕ), Even a → Even b →
      ∀ (SB Sall : Finset (HeightOneSpectrum (𝓞 X.E))), StandardKernelAtTorus.OffT SB D.host.q (Ideal.absNorm cc) (Pr.T u) →
        (∀ P, P ∈ Sall ↔ P ∈ Pr.vT u ∨ P ∈ SB) →
      ∀ (SG SG' : Finset (HeightOneSpectrum (𝓞 X.E))) (d : DecoSet X.E a (Pr.vT u) SG) (d' : DecoSet X.E b (Pr.vT u) SG'),
        JetSumTable.StdAtT d.1 → JetSumTable.StdAtT d'.1 →
      ∀ (cA cB' : ℕ), Nat.Coprime cA (Pr.T u) → Nat.Coprime cB' (Pr.T u) →
        ClauseA (ambOf s B χ cD) Pr u w ι uu SB Sall d d' cA cB'

theorem mem_Sall {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (u : Pr.Word) (P : HeightOneSpectrum (𝓞 X.E)) :
    P ∈ Sall sel mu u ↔ P ∈ Pr.vT u ∨ P ∈ rowSG Pr sel mu := by
  classical
  unfold Sall
  rw [Finset.mem_union]

theorem jetMoments_iff_narrowB : JetSumTable.JetMoments ↔ NarrowB := by
  refine forall_congr' fun D => forall_congr' fun hD => forall_congr' fun H => forall_congr' fun s => forall_congr' fun cc =>
    forall_congr' fun δ => forall_congr' fun B => forall_congr' fun χ => forall_congr' fun cD => forall_congr' fun _ =>
    forall_congr' fun u => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun w => forall_congr' fun ι =>
    imp_congr (induces_iff ι w) (exists_congr fun un => and_congr Iff.rfl ?_)
  refine forall_congr' fun sel => forall_congr' fun S => forall_congr' fun mu => forall_congr' fun cst =>
    forall_congr' fun hsel => forall_congr' fun hS => forall_congr' fun hc => forall_congr' fun i => forall_congr' fun b =>
    forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun SG => forall_congr' fun SG' => forall_congr' fun d =>
    forall_congr' fun d' => imp_congr Iff.rfl (imp_congr Iff.rfl ?_)
  exact clause_iff (ambOf s B χ cD) D.Pr u w ι un (rowSG D.Pr sel mu) (Sall sel mu u) d d'
    (fun P hP => (mem_Sall sel mu u P).2 (Or.inr hP)) (hD.primes.T_prime u).ne_zero
    (fun P hP => (offT_rowSG hD s u _ hsel hS hc P hP).2.2.2.2) (cAof sel mu cst) _

theorem momT_iff_wideA : StandardKernelAtTorus.MomT ↔ WideA := by
  refine forall_congr' fun D => forall_congr' fun X => forall_congr' fun s => forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun Pr => forall_congr' fun hPr => forall_congr' fun _ => forall_congr' fun cc => forall_congr' fun δ =>
    forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun B => forall_congr' fun χ => forall_congr' fun cD =>
    forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun u => forall_congr' fun _ => forall_congr' fun p =>
    forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun w => forall_congr' fun ι =>
    imp_congr (induces_iff ι w).symm (exists_congr fun uu => and_congr Iff.rfl ?_)
  refine forall_congr' fun a => forall_congr' fun b => forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun SB => forall_congr' fun Sall => forall_congr' fun hO => forall_congr' fun hS =>
    forall_congr' fun SG => forall_congr' fun SG' => forall_congr' fun d => forall_congr' fun d' =>
    imp_congr Iff.rfl (imp_congr Iff.rfl (forall_congr' fun cA => forall_congr' fun cB' =>
      imp_congr Iff.rfl (imp_congr Iff.rfl ?_)))
  exact (clause_iff (ambOf s B χ cD) Pr u w ι uu SB Sall d d' (fun P hP => (hS P).2 (Or.inr hP)) (hPr.T_prime u).ne_zero
    (fun P hP => (hO P hP).2.2.2.2) cA cB').symm

theorem narrowB_of_momT (h : StandardKernelAtTorus.MomT) : NarrowB := by
  intro D hD H s cc δ B χ cD ⟨hs, _, h1, h2, h3, h4⟩ u _ hcc w ι hι
  obtain ⟨un, hun, hM⟩ := h H D.X s hs hD.fields D.Pr hD.primes hD.cond cc δ h1 h2 B χ cD h3 h4 u hcc _ rfl w ι hι
  refine ⟨un, hun, fun sel S mu cst hsel hS hc i b _ hb SG SG' d d' hd hd' => ?_⟩
  have hev : ∀ j, Even (D.R.N j) := fun j => D.R.k_even.add ((D.R.t_odd.add_one).mul_left j)
  have hO := offT_rowSG hD s u _ hsel hS hc
  have hcop : Nat.Coprime (∏ P : rowSG D.Pr sel mu, qOf P.1) (D.Pr.T u) :=
    Nat.Coprime.prod_left fun P _ => coprime_qOf (hD.primes.T_prime u) P.1 (hO P.1 P.2).2.2.2.2
  exact hM _ b (hev i) (hb ▸ hev (i + 1)) _ _ hO (mem_Sall sel mu u) SG SG' d d' hd hd' _ _ (hcop.pow_left _) (hcop.pow_left _)

theorem jetMoments_of_momT (h : StandardKernelAtTorus.MomT) : JetSumTable.JetMoments := jetMoments_iff_narrowB.2 (narrowB_of_momT h)

theorem compare :
    (∀ {X : Fields} (A : Amb X) (Pr : Primes X) (u : Pr.Word) {p : ℕ} [Fact p.Prime] (w : HeightOneSpectrum (𝓞 X.K))
      (ι : X.K →+* ℂ_[p]) (uu : X.Tau → ℂ_[p]) {a b : ℕ} (SB Sall : Finset (HeightOneSpectrum (𝓞 X.E)))
      {SG SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (d : DecoSet X.E a (Pr.vT u) SG) (d' : DecoSet X.E b (Pr.vT u) SG'),
      SB ⊆ Sall → Pr.T u ≠ 0 → (∀ P ∈ SB, (Pr.T u : 𝓞 X.E) ∉ P.asIdeal) → ∀ cA cB' : ℕ,
        (ClauseA A Pr u w ι uu SB Sall d d' cA cB' ↔ ClauseB A Pr u w ι uu SB Sall d d' cA cB')) ∧
    (JetSumTable.JetMoments ↔ NarrowB) ∧ (StandardKernelAtTorus.MomT ↔ WideA) ∧ (StandardKernelAtTorus.MomT → JetSumTable.JetMoments) :=
  ⟨fun A Pr u _ _ w ι uu _ _ SB Sall _ _ d d' => clause_iff A Pr u w ι uu SB Sall d d',
    jetMoments_iff_narrowB, momT_iff_wideA, jetMoments_of_momT⟩

end GlobalTheory.Proof.NarrowJetMoments
