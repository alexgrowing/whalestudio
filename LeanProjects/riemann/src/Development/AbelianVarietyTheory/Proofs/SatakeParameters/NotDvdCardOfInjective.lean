import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.BadPrimesPeriodBound
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InterlacingEquivariance
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMulAddEqOneOfNotMem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TransportedWeylLatticeHermitianDuality
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActPMemLocPDelStdOfIsBasisAt

noncomputable section

namespace GlobalTheory.ColPeriod

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV Polynomial
open scoped Matrix

theorem not_dvd_card_of_injective {E : Type} [Field E] [NumberField E] {n : ℕ} {G : Type} [Group G] [Finite G]
    (f : G →* (Sp E n ≃ₗ[E] Sp E n)) (hf : Function.Injective f) {p : ℕ} (hp : p.Prime)
    (hb : Module.finrank ℚ E * n + 1 < p) : ¬ p ∣ Nat.card G := by
  intro hd
  haveI := Fact.mk hp
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hd
  let A : Module.End ℚ (Sp E n) := ((f g : Sp E n ≃ₗ[E] Sp E n) : Sp E n →ₗ[E] Sp E n).restrictScalars ℚ
  have hApow : ∀ (k : ℕ) (x : Sp E n), (A ^ k) x = (f (g ^ k)) x := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih => intro x; rw [pow_succ, pow_succ, map_mul, Module.End.mul_apply, ih]; rfl
  have hA : A ^ p = 1 := by
    refine LinearMap.ext fun x => ?_
    rw [hApow, ← hg, pow_orderOf_eq_one, map_one]; rfl
  have h1 : minpoly ℚ A ∣ cyclotomic p ℚ * (X - 1) := by
    rw [cyclotomic_prime_mul_X_sub_one]
    exact minpoly.dvd _ _ (by simp [hA])
  have hint : IsIntegral ℚ A := Algebra.IsIntegral.isIntegral A
  have hdeg : (minpoly ℚ A).natDegree ≤ Module.finrank ℚ E * n := by
    have h2 := natDegree_le_of_dvd (LinearMap.minpoly_dvd_charpoly A) (LinearMap.charpoly_monic A).ne_zero
    rw [LinearMap.charpoly_natDegree, ← Module.finrank_mul_finrank ℚ E (Sp E n)] at h2
    simpa using h2
  have hirr := cyclotomic.irreducible_rat hp.pos
  have hcop : IsCoprime (minpoly ℚ A) (cyclotomic p ℚ) := by
    refine (hirr.coprime_iff_not_dvd.2 fun h => ?_).symm
    have h2 := natDegree_le_of_dvd h (minpoly.ne_zero hint)
    rw [natDegree_cyclotomic, Nat.totient_prime hp] at h2
    omega
  obtain ⟨q, hq⟩ := hcop.dvd_of_dvd_mul_left h1
  have h3 : A = 1 := by
    have h4 := congrArg (aeval A) hq
    rw [map_mul, minpoly.aeval, zero_mul] at h4
    simpa [sub_eq_zero] using h4
  have h5 : f g = f 1 := by
    rw [map_one]
    refine LinearEquiv.ext fun x => ?_
    exact LinearMap.congr_fun h3 x
  rw [hf h5, orderOf_one] at hg
  exact hp.one_lt.ne hg

section Stab

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem glg_eq_one_of_fix (d : DecoSet X.E n ST SG) (h : GLG X.E n SG) (e : d.1.act 1 h = d.1) : h = 1 := by
  funext w
  apply Units.ext
  refine Matrix.mulVec_injective (funext fun c => ?_)
  obtain ⟨x, -, hx⟩ := d.2.be_surj w c
  have := congrFun (congrFun (congrArg Deco.be e) w) x
  change (h w).1.mulVec (d.1.be w x) = d.1.be w x at this
  rw [hx] at this
  simpa using this

theorem not_dvd_card_stab_form (Λ : LevFam X.E X.K n SG) (d : DecoSet X.E n ST SG)
    [Finite (MulAction.stabilizer (FormG Λ) d)] {p : ℕ} (hp : p.Prime) (hb : Module.finrank ℚ X.E * n + 1 < p) :
    ¬ p ∣ Nat.card (MulAction.stabilizer (FormG Λ) d) := by
  refine not_dvd_card_of_injective (((UF X.E n).subtype.comp (MonoidHom.fst _ _)).comp (Subgroup.subtype _)) ?_ hp hb
  rw [injective_iff_map_eq_one]
  rintro ⟨⟨γ, h⟩, hs⟩ h1
  have h2 : γ = 1 := Subtype.ext h1
  subst h2
  have h3 : h.1 = 1 := glg_eq_one_of_fix d h.1 (congrArg Subtype.val hs)
  exact Subtype.ext (Prod.ext rfl (Subtype.ext h3))

end Stab

section Pair

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}

theorem pairBK_mem_one (lam : ι → DomWeight n) (M : ι → Submodule (𝓞 K) (Fin n → K))
    (hM : ∀ τ, Submodule.IsLattice K (M τ)) {x y : VV K lam} (hx : x ∈ delK lam fun τ => dualFr (M τ))
    (hy : y ∈ nabK lam M) : pairBK lam x y ∈ (1 : Submodule (𝓞 K) K) := by
  let _ : StarRing K := starRingOfComm
  have h := (GlobalTheory.TransDual.nabDelDual K ι n lam (fun _ => 1) M (fun _ => by simp) (fun _ => by simp) hM).1
  have e : (fun τ => hdualFr (1 : Matrix (Fin n) (Fin n) K) (M τ)) = fun τ => dualFr (M τ) := by
    funext τ
    ext φ
    change (∀ y ∈ M τ, star y ⬝ᵥ ((1 : Matrix (Fin n) (Fin n) K) *ᵥ φ) ∈ _) ↔ ∀ x ∈ M τ, φ ⬝ᵥ x ∈ _
    refine forall₂_congr fun y _ => ?_
    rw [Matrix.one_mulVec, dotProduct_comm]
    rfl
  rw [e] at h
  rw [← h] at hx
  unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual at hx
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply] at hx
  have h2 := hx y hy
  rw [pairK_apply, pairP_trivial, pairingBSymm_holds] at h2
  rw [pairBK_apply]
  exact h2

omit [Fintype ι] in
theorem mem_dualFr_tauLat {E : Type} [Field E] [NumberField E] (emb : ι → E →+* K) (τ : ι)
    (L : Submodule (𝓞 E) (Fin n → E)) (φ : Fin n → K) :
    φ ∈ dualFr (tauLat emb τ L) ↔ ∀ y ∈ L, φ ⬝ᵥ (fun a => emb τ (y a)) ∈ (1 : Submodule (𝓞 K) K) := by
  constructor
  · intro h y hy
    exact h _ (Submodule.subset_span ⟨y, hy, rfl⟩)
  · intro h x hx
    induction hx using Submodule.span_induction with
    | mem z hz => obtain ⟨y, hy, rfl⟩ := hz; exact h y hy
    | zero => simp
    | add y z _ _ hy hz => rw [dotProduct_add]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [dotProduct_smul]; exact Submodule.smul_mem _ c hy

omit [Fintype ι] in

theorem dualFr_tauLat_tilN {E : Type} [Field E] [NumberField E] [StarRing E] (emb : ι → E →+* K) (τ : ι)
    (L : Submodule (𝓞 E) (Sp E n)) :
    dualFr (tauLat emb τ (tilN L)) = Br.sumLat rfl (dualFr (tauLat emb τ L)) 1 := by
  ext φ
  rw [mem_dualFr_tauLat]
  change _ ↔ (fun a : Fin n => φ a.castSucc) ∈ dualFr (tauLat emb τ L) ∧ ∃ c : 𝓞 K, φ (Fin.last n) = (c : K) * 1
  rw [mem_dualFr_tauLat]
  have e : ∀ y : Sp E (n + 1), φ ⬝ᵥ (fun a => emb τ (y a)) =
      (fun a : Fin n => φ a.castSucc) ⬝ᵥ (fun a => emb τ (initL E n y a)) + φ (Fin.last n) * emb τ (y (Fin.last n)) := by
    intro y
    simp only [dotProduct, Fin.sum_univ_castSucc]
    rfl
  constructor
  · intro h
    refine ⟨fun y hy => ?_, ?_⟩
    · have := h (incl E n y) ((mem_tilN _ _).2 ⟨by simpa using hy, 0, by simp⟩)
      rw [e] at this
      simpa using this
    · have := h (eLast E n) ((mem_tilN _ _).2 ⟨by simp, 1, by simp⟩)
      rw [e] at this
      simp only [initL_eLast, Pi.zero_apply, map_zero, eLast_last, map_one, mul_one] at this
      have h0 : (fun a : Fin n => φ a.castSucc) ⬝ᵥ (fun _ => (0 : K)) = 0 := dotProduct_zero _
      rw [h0, zero_add] at this
      obtain ⟨c, hc⟩ := Submodule.mem_one.1 this
      exact ⟨c, by rw [mul_one]; exact hc.symm⟩
  · rintro ⟨h1, c, hc⟩ y hy
    obtain ⟨h2, r, hr⟩ := (mem_tilN _ _).1 hy
    rw [e]
    refine Submodule.add_mem _ (h1 _ h2) ?_
    rw [hc, ← hr, mul_one]
    exact Submodule.mem_one.2 ⟨c * RingOfIntegers.mapRingHom (emb τ) r, by rw [map_mul]; rfl⟩

theorem valuation_le_one_of_smul (w : HeightOneSpectrum (𝓞 K)) {s : 𝓞 K} (hs : s ∉ w.asIdeal) {x : K}
    (h : s • x ∈ (1 : Submodule (𝓞 K) K)) : w.valuation K x ≤ 1 := by
  obtain ⟨c, hc⟩ := Submodule.mem_one.1 h
  have h1 : w.valuation K (s : K) = 1 := by
    have := (w.valuation_eq_one_iff_notMem (K := K) (r := s)).2 hs
    exact this
  have h2 : w.valuation K (algebraMap (𝓞 K) K c) ≤ 1 := w.valuation_le_one (K := K) c
  rw [hc, Algebra.smul_def, map_mul] at h2
  change w.valuation K (s : K) * _ ≤ 1 at h2
  rwa [h1, one_mul] at h2

end Pair

theorem valuation_pair_br_le_one {X : Fields} {N n : ℕ} (hN : N = n + 1) (lam : X.Tau → DomWeight N)
    (sg : X.Tau → DomWeight n) (hB : Br.BrIntegral X.K hN lam sg) (hI : ∀ τ, Br.Interlace hN (lam τ) (sg τ))
    (hS : ∀ τ, Br.SameShift (lam τ) (sg τ)) {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} {pi : 𝓞 X.E}
    (hT : ∀ P : ST, cO X.E pi ∉ P.1.asIdeal) (hG : ∀ v : SG, pi ∉ v.1.asIdeal) {p : ℕ}
    (hp : ∀ Q ∈ ST, ((p : ℕ) : 𝓞 X.E) ∉ Q.asIdeal) (w : HeightOneSpectrum (𝓞 X.K))
    (hw : ((p : ℕ) : 𝓞 X.K) ∈ w.asIdeal) (t : X.Tau → X.K) (ht : ∀ τ, w.valuation X.K (t τ) = 1)
    (d : DecoSet X.E n ∅ SG) {x : VV X.K lam}
    (hx : x ∈ localization₂ w.asIdeal (delAtr X.emb lam (DecoSet.tilH (ST := ST) hN pi d).1.Lsh)) {y : VV X.K sg}
    (hy : y ∈ nabAt X.emb sg d.1.N) : w.valuation X.K (pairBK sg (Br.brAt hN lam sg t x) y) ≤ 1 := by
  subst hN
  rw [(GlobalTheory.GO.use₃ lam hp _ w hw).2] at hx
  change x ∈ localization₂ w.asIdeal (delAtr X.emb lam (DecoSet.til (ST := ST) pi d).1.N) at hx
  rw [DecoSet.til_val d hT hG] at hx
  obtain ⟨s, hs, hsx⟩ := hx
  change s • x ∈ delK lam fun τ => dualFr (tauLat X.emb τ (tilN d.1.N)) at hsx
  simp only [dualFr_tauLat_tilN] at hsx
  have h1 := hB hI hS _ (fun _ => 1) (fun _ => one_ne_zero) _ hsx
  have h2 := pairBK_mem_one sg _ (fun τ => GlobalTheory.TauLat.tauLatLattice X.E X.K X.Tau n X.emb τ _ d.2.lat) h1 hy
  have h3 : Br.brAt rfl lam sg (fun _ => (1 : X.K)) = Br.brStd rfl lam sg := by simp [Br.brAt]
  rw [h3, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, LinearMap.smul_apply] at h2
  have h4 := valuation_le_one_of_smul w hs h2
  rw [Br.brAt, LinearMap.smul_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, map_mul, map_prod]
  simp only [map_zpow₀, ht, one_zpow, Finset.prod_const_one, one_mul]
  exact h4

section Period

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

theorem mem_divs {A : Type} [CommRing A] [IsDedekindDomain A] {a : A} {P : HeightOneSpectrum A} (h : P ∈ divs a) :
    a ∈ P.asIdeal := by
  unfold divs at h
  split_ifs at h with h1
  · simpa using h
  · simp at h

theorem natCast_notMem_of_ne {E : Type} [Field E] [NumberField E] {a p : ℕ} (ha : a.Prime) (hp : p.Prime) (h : a ≠ p)
    (w : HeightOneSpectrum (𝓞 E)) (hw : ((p : ℕ) : 𝓞 E) ∈ w.asIdeal) : ((a : ℕ) : 𝓞 E) ∉ w.asIdeal :=
  GlobalTheory.GO.natCast_notMem_of_coprime ((Nat.coprime_primes ha hp).2 h) w hw

theorem T_mem_of_piT_mem (hPr : Pr.Ok) (u : Pr.Word) {Q : HeightOneSpectrum (𝓞 X.E)} (h : Pr.piT u ∈ Q.asIdeal) :
    ((Pr.T u : ℕ) : 𝓞 X.E) ∈ Q.asIdeal := by
  rw [← hPr.piT_norm u]
  exact Q.asIdeal.mul_mem_right _ h

theorem piT_notMem_rowSG (hPr : Pr.Ok) (hsel : IsSel X sel) (u : Pr.Word) (hS : Pr.T u ∈ S) (v : rowSG Pr sel mu) :
    Pr.piT u ∉ v.1.asIdeal := by
  classical
  intro h
  have hT := T_mem_of_piT_mem hPr u h
  rcases Finset.mem_union.1 v.2 with h1 | h1
  · have h2 : ∃ i, v.1 ∈ Pr.vG i := by
      rcases Finset.mem_union.1 h1 with h2 | h2
      exacts [⟨0, h2⟩, ⟨1, h2⟩]
    obtain ⟨i, hi⟩ := h2
    have h3 : ((Pr.g i : ℕ) : 𝓞 X.E) ∈ v.1.asIdeal := by
      rw [← hPr.piG_norm i]
      exact v.1.asIdeal.mul_mem_left _ (mem_divs hi)
    exact natCast_notMem_of_ne (hPr.T_prime u) (hPr.g_prime i) (hPr.T_ne_g u i) v.1 h3 hT
  · unfold QE at h1
    split_ifs at h1 with h2
    · obtain ⟨v0, hv0, e⟩ := Finset.mem_image.1 h1
      have hv1 : v0 ∈ Qprime (mu : Chr X.F X.E X.K) := by simpa using hv0
      have hgood : GoodPl X.E S v0 := by
        by_contra hn
        have h4 := (Subgroup.mem_inf.1 mu.2).2
        exact hv1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h4 v0) hn)
      have h5 : ((Pr.T u : ℕ) : 𝓞 X.F) ∈ v0.asIdeal := by
        rw [← hsel v0, e, Ideal.under_def, Ideal.mem_comap, map_natCast]
        exact hT
      apply hgood.2.2
      have h6 : ringChar (𝓞 X.F ⧸ v0.asIdeal) ∣ Pr.T u := by
        rw [← ringChar.spec, ← map_natCast (Ideal.Quotient.mk v0.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
        exact h5
      haveI := v0.isPrime
      rcases (Nat.dvd_prime (hPr.T_prime u)).1 h6 with h7 | h7
      · exact absurd h7 CharP.ringChar_ne_one
      · change ringChar (𝓞 X.F ⧸ v0.asIdeal) ∈ S
        rw [h7]
        exact hS
    · simp at h1

theorem valuation_inv_natCast {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {p a : ℕ} (hp : p.Prime)
    (hw : ((p : ℕ) : 𝓞 K) ∈ w.asIdeal) (h : ¬ p ∣ a) : w.valuation K ((a : K))⁻¹ = 1 := by
  have h1 := GlobalTheory.GO.natCast_notMem_of_coprime ((Nat.Prime.coprime_iff_not_dvd hp).2 h).symm w hw
  have h2 : w.valuation K (algebraMap (𝓞 K) K (a : 𝓞 K)) = 1 := (w.valuation_eq_one_iff_notMem (K := K)).2 h1
  rw [map_natCast] at h2
  rw [map_inv₀, h2, inv_one]

theorem wt_eq_card {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K} (h : S.Ok) (s : S.Sec) (c : S.Cl) :
    (S.toCSDOf h s).wt c = Nat.card (MulAction.stabilizer S.G (s.rep c)) :=
  (@Nat.card_eq_fintype_card _ (h.fintypeStab _)).symm

theorem csOf_apply₂ {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K} (h : S.Ok) (s : S.Sec) {M M' : Type}
    [AddCommGroup M] [Module K M] [AddCommGroup M'] [Module K M'] (B : S.D → (M →ₗ[K] M' →ₗ[K] K)) (x : M) (y : M') :
    S.csOf h s B x y = letI := h.fintypeCl; ∑ c : S.Cl, (((S.toCSDOf h s).wt c : K))⁻¹ * B (s.rep c) x y := by
  simp only [GSD.csOf, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]

theorem valuation_PtilE_le_one (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (u : Pr.Word) (hS : Pr.T u ∈ S)
    (hB : Br.BrIntegral X.K (N_m_succ R) (W.lamTrue u R.m) W.sgTrue)
    (hI : ∀ τ, Br.Interlace (N_m_succ R) (W.lamTrue u R.m τ) (W.sgTrue τ))
    (hSh : ∀ τ, Br.SameShift (W.lamTrue u R.m τ) (W.sgTrue τ))
    (P : LevFam X.E X.K R.r Pr.vGs) (hP : (mtildeGSD W Ch sel mu P).Ok) {p : ℕ} (hp : p.Prime) (hpT : Pr.T u ≠ p)
    (hb : 2 * X.f * R.N R.m + 1 < p) (w : HeightOneSpectrum (𝓞 X.K)) (hw : ((p : ℕ) : 𝓞 X.K) ∈ w.asIdeal)
    (ψ : (evGSD W Ch sel mu P u).EqFun) (hψ : ∀ d, ψ.1 d ∈ localization₂ w.asIdeal ((evGSD W Ch sel mu P u).Del d))
    (F : MtildeV W Ch sel mu P) (hF : F ∈ MtildeL W Ch sel mu P) :
    w.valuation X.K (PtilE W Ch sel mu P hP u ψ F) ≤ 1 := by
  let _ := hP.fintypeCl
  have e : PtilE W Ch sel mu P hP u ψ F = ∑ c : (mtildeGSD W Ch sel mu P).Cl,
      ((((mtildeGSD W Ch sel mu P).toCSDOf hP (mtildeGSD W Ch sel mu P).outSec).wt c : X.K))⁻¹ *
        pairBK W.sgTrue (brC W u (ψ.1 ((mtildeGSD W Ch sel mu P).outSec.rep c)))
          (F.1 ((mtildeGSD W Ch sel mu P).outSec.rep c)) :=
    csOf_apply₂ hP (mtildeGSD W Ch sel mu P).outSec _ ψ.1 F.1
  rw [e]
  refine Valuation.map_sum_le _ fun c _ => ?_
  have hE : Module.finrank ℚ X.E = 2 * X.f := by
    rw [← Module.finrank_mul_finrank ℚ X.F X.E, hX.rankE, ← hX.card_Tau, mul_comm]
    rfl
  haveI := hP.fin_stab ((mtildeGSD W Ch sel mu P).outSec.rep c)
  have h1 := not_dvd_card_stab_form (rowTy Ch sel mu P).inv ((mtildeGSD W Ch sel mu P).outSec.rep c) hp
    (lt_of_le_of_lt (by rw [hE]; gcongr; omega) hb)
  rw [map_mul, valuation_inv_natCast w hp hw (by rw [wt_eq_card]; exact h1), one_mul]
  refine valuation_pair_br_le_one (N_m_succ R) _ _ hB hI hSh (ST := Pr.vT u) (pi := Pr.piT u) (fun Q hQ => ?_)
    (piT_notMem_rowSG sel mu hPr hsel u hS) (p := p) (fun Q hQ h => ?_) w hw _ (fun τ => ?_) _ (hψ _) (hF _)
  · obtain ⟨a, b, hab⟩ := hPr.piT_cop u
    exact Q.1.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hab ▸ Q.1.asIdeal.add_mem (Q.1.asIdeal.mul_mem_left _ (mem_divs Q.2)) (Q.1.asIdeal.mul_mem_left _ hQ)))
  · exact natCast_notMem_of_ne (hPr.T_prime u) hp hpT Q h (T_mem_of_piT_mem hPr u (mem_divs hQ))
  · have h2 : RingOfIntegers.mapRingHom (X.emb τ) (X.conjO (Pr.piT u)) ∉ w.asIdeal := by
      intro h
      refine natCast_notMem_of_ne (hPr.T_prime u) hp hpT w hw ?_
      have h3 := congrArg (RingOfIntegers.mapRingHom (X.emb τ)) (hPr.piT_norm u)
      rw [map_mul, map_natCast] at h3
      rw [← h3]
      exact w.asIdeal.mul_mem_left _ h
    exact (w.valuation_eq_one_iff_notMem (K := X.K)).2 h2

end Period

end GlobalTheory.ColPeriod
