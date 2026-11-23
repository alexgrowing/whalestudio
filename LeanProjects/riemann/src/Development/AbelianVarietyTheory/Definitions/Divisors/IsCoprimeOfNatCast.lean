import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GSplit
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActLevIffLevelActionOver
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardLatticeQuotientHalfLevel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevDesc

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)

section Ideals

theorem mem_sup_span_mul {O : Type} [CommRing O] {I : Ideal O} {a b x : O} (h : IsCoprime a b)
    (ha : x ∈ I ⊔ Ideal.span {a}) (hb : x ∈ I ⊔ Ideal.span {b}) : x ∈ I ⊔ Ideal.span {a * b} := by
  obtain ⟨u, v, huv⟩ := h
  obtain ⟨y, hy, _, hz, e⟩ := Submodule.mem_sup.1 ha
  obtain ⟨y', hy', _, hz', e'⟩ := Submodule.mem_sup.1 hb
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hz'
  refine Submodule.mem_sup.2 ⟨u * a * y' + v * b * y, add_mem (I.mul_mem_left _ hy') (I.mul_mem_left _ hy),
    (u * t + v * s) * (a * b), Ideal.mem_span_singleton'.2 ⟨_, rfl⟩, ?_⟩
  linear_combination (u * a) * e' + (v * b) * e + x * huv

theorem absNorm_eq_of_split {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime)
    (h : {v : HeightOneSpectrum (𝓞 E) | ((p : ℕ) : 𝓞 E) ∈ v.asIdeal}.ncard = Module.finrank ℚ E) {P : Ideal (𝓞 E)}
    (hP : P.IsPrime) (hw : (p : 𝓞 E) ∈ P) : Ideal.absNorm P = p := by
  classical
  obtain ⟨hc, -⟩ := Formalism.MainNotions.ModuliIntegralCharts.H1.GSplit.split_of_ncard hp h
  set I : Ideal (𝓞 E) := Ideal.span {((p : ℕ) : 𝓞 E)} with hI
  have hI0 : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  set M := UniqueFactorizationMonoid.normalizedFactors I with hM
  have hN : Ideal.absNorm I = p ^ Module.finrank ℚ E := by
    rw [hI, Ideal.absNorm_span_singleton]
    have : ((p : ℕ) : 𝓞 E) = algebraMap ℤ (𝓞 E) (p : ℤ) := by simp
    rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank]
    simp
  have hprod : M.prod = I := Ideal.prod_normalizedFactors_eq_self hI0
  have hge : ∀ P ∈ M, p ≤ Ideal.absNorm P := by
    intro P hP
    obtain ⟨hPp, hIP⟩ := (Ideal.mem_normalizedFactors_iff hI0).1 hP
    have hd : Ideal.absNorm P ∣ p ^ Module.finrank ℚ E := hN ▸ Ideal.absNorm_dvd_absNorm_of_le hIP
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 hd
    have h1 : Ideal.absNorm P ≠ 1 := by rw [Ne, Ideal.absNorm_eq_one_iff]; exact hPp.ne_top
    rw [hj] at h1 ⊢
    exact Nat.le_self_pow (by rintro rfl; simp at h1) p
  have hwM : P ∈ M := (Ideal.mem_normalizedFactors_iff hI0).2
    ⟨hP, by rw [hI, Ideal.span_singleton_le_iff_mem]; exact hw⟩
  refine le_antisymm ?_ (hge _ hwM)
  obtain ⟨M', hM'⟩ := Multiset.exists_cons_of_mem hwM
  have h2 : p ^ M'.card ≤ (M'.map Ideal.absNorm).prod := by
    have := Multiset.pow_card_le_prod (s := M'.map Ideal.absNorm) (a := p) (fun x hx => by
      obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.1 hx
      exact hge P (hM' ▸ Multiset.mem_cons_of_mem hP))
    simpa using this
  have h3 : Ideal.absNorm P * (M'.map Ideal.absNorm).prod = p * p ^ M'.card := by
    rw [← pow_succ', ← Multiset.card_cons P, ← hM', hc, ← hN, ← hprod, hM', Multiset.prod_cons, map_mul,
      map_multiset_prod]
  by_contra hlt
  have hlt' := not_le.1 hlt
  have hpos : 0 < p ^ M'.card := pow_pos hp.pos _
  nlinarith

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

def halfPrime (l : Level H) (v : Ideal (𝓞 (maximalRealSubfield E))) : Ideal (𝓞 E) :=
  l.Mb ⊔ v.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))

theorem natCast_M_mem (l : Level H) : (l.M : 𝓞 E) ∈ l.Mb := by
  have : Ideal.span {(l.M : 𝓞 E)} ≤ l.Mb := l.prod ▸ Ideal.mul_le_left
  exact this (Ideal.subset_span rfl)

theorem bar_bar' (a : 𝓞 E) : H.bar (H.bar a) = a :=
  Subtype.ext (by
    show ((H.bar (H.bar a) : 𝓞 E) : E) = (a : E)
    rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply])

theorem bar_algebraMap (a : 𝓞 (maximalRealSubfield E)) :
    H.bar (algebraMap _ (𝓞 E) a) = algebraMap _ (𝓞 E) a :=
  Subtype.ext (by
    show ((H.bar (algebraMap _ (𝓞 E) a) : 𝓞 E) : E) = _
    rw [H.bar_eq]
    exact (IsCMField.complexConj E).commutes (a : maximalRealSubfield E))

theorem exists_norm (y : 𝓞 E) : ∃ z : 𝓞 (maximalRealSubfield E), algebraMap _ (𝓞 E) z = y * H.bar y := by
  have h1 : ((y * H.bar y : 𝓞 E) : E) ∈ maximalRealSubfield E := by
    rw [← IsCMField.complexConj_eq_self_iff, ← H.bar_eq, map_mul, bar_bar', mul_comm]
  refine ⟨⟨⟨_, h1⟩, ?_⟩, rfl⟩
  exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ (maximalRealSubfield E) E) Subtype.val_injective).1
    (y * H.bar y).2

theorem halfPrime_eq (l : Level H) {v : Ideal (𝓞 (maximalRealSubfield E))} (hv : v.IsMaximal) {P : Ideal (𝓞 E)}
    (hP : P.IsPrime) (h : halfPrime l v ≤ P) : halfPrime l v = P := by
  refine le_antisymm h fun x hx => ?_
  have hc : v = P.comap (algebraMap _ (𝓞 E)) :=
    hv.eq_of_le (Ideal.comap_ne_top _ hP.ne_top) (Ideal.map_le_iff_le_comap.1 (le_sup_right.trans h))
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (l.coprime ▸ Submodule.mem_top :
    (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E))
  obtain ⟨b', hb', rfl⟩ := (Ideal.mem_map_iff_of_surjective (H.bar : 𝓞 E →+* 𝓞 E) H.bar.surjective).1 hb
  change a + H.bar b' = 1 at hab
  have hab' : H.bar a + b' = 1 := by simpa [bar_bar'] using congrArg H.bar hab
  obtain ⟨z, hz⟩ := exists_norm (H := H) (H.bar b' * x + a)
  have hzv : z ∈ v := by
    rw [hc, Ideal.mem_comap, hz]
    exact P.mul_mem_right _ (add_mem (P.mul_mem_left _ hx) (h (Ideal.mem_sup_left ha)))
  have h1 := Ideal.mem_map_of_mem (algebraMap _ (𝓞 E)) hzv
  rw [hz, map_add, map_mul, bar_bar'] at h1
  refine Submodule.mem_sup.2 ⟨a * (x - 1) + b' * ((1 - H.bar x) * (H.bar b' * x + a)),
    add_mem (l.Mb.mul_mem_right _ ha) (l.Mb.mul_mem_right _ hb'), _, h1, ?_⟩
  linear_combination x * hab + (H.bar b' * x + a) * hab'

theorem halfPrime_isPrime (l : Level H) {v : Ideal (𝓞 (maximalRealSubfield E))} (hv : v.IsMaximal)
    (hM : (l.M : 𝓞 (maximalRealSubfield E)) ∈ v) : (halfPrime l v).IsPrime := by
  obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E) v
    (by
      rw [(RingHom.injective_iff_ker_eq_bot (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))).1
        (FaithfulSMul.algebraMap_injective _ _)]
      exact bot_le)
  have hvQ : v.map (algebraMap _ (𝓞 E)) ≤ Q := Ideal.map_le_iff_le_comap.2 hQv.ge
  have hMQ : l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ Q := by
    rw [l.prod, Ideal.span_singleton_le_iff_mem]
    simpa using hvQ (Ideal.mem_map_of_mem _ hM)
  rcases hQ.isPrime.mul_le.1 hMQ with h | h
  · rw [halfPrime_eq l hv hQ.isPrime (sup_le h hvQ)]; exact hQ.isPrime
  · haveI := hQ.isPrime
    have hP : (Q.comap (H.bar : 𝓞 E →+* 𝓞 E)).IsPrime := inferInstance
    rw [halfPrime_eq l hv hP (sup_le (Ideal.map_le_iff_le_comap.1 h) (Ideal.map_le_iff_le_comap.2 fun a ha => ?_))]
    · exact hP
    · show H.bar (algebraMap _ (𝓞 E) a) ∈ Q
      rw [bar_algebraMap]; exact hvQ (Ideal.mem_map_of_mem _ ha)

end Ideals

section Generic

theorem superDiag_mul {r : ℕ} {k : Type} [Field k] {u u' : GL (Fin r) k} (hu : u ∈ unitri r k) (hu' : u' ∈ unitri r k) :
    superDiag ((u * u' : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) =
      superDiag (u : Matrix (Fin r) (Fin r) k) + superDiag (u' : Matrix (Fin r) (Fin r) k) := by
  simp only [superDiag, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · have hij : j ≠ i := fun e => by rw [e] at h; omega
    rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_add_of_mem j i (Finset.mem_univ _) (Finset.mem_univ _) hij,
      hu.2, hu'.2, one_mul, mul_one]
    intro c _ hc
    by_cases hci : c < i
    · rw [hu.1 (show id c < id i from hci), zero_mul]
    · have h1 : (c : ℕ) ≠ j := fun e => hc.1 (Fin.ext e)
      have h2 : (c : ℕ) ≠ i := fun e => hc.2 (Fin.ext e)
      have h3 : ¬ (c : ℕ) < i := hci
      rw [hu'.1 (show id j < id c from (by show (j : ℕ) < c; omega)), mul_zero]
  · simp

variable {R : Ranks} {Hs : Host R} {K : Type} [Field K]

def genChar (ψ : ∀ v : Sq Hs, AddChar (ZMod (Hs.g v.1)) K) : levelU Hs →* Kˣ :=
  MonoidHom.toHomUnits
    { toFun := fun u => psiU ψ (u : LevelGroup Hs)
      map_one' := by
        refine Finset.prod_eq_one fun v _ => ?_
        have : superDiag (((((1 : levelU Hs) : LevelGroup Hs) v : GL (Fin R.r) (ZMod (Hs.g v.1))) :
            Matrix (Fin R.r) (Fin R.r) (ZMod (Hs.g v.1)))) = 0 :=
          Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by
            split_ifs with h
            · exact Matrix.one_apply_ne fun e => by rw [e] at h; omega
            · rfl
        rw [this, AddChar.map_zero_eq_one]
      map_mul' := fun a b => by
        simp only [psiU, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun v _ => ?_
        rw [← AddChar.map_add_eq_mul, ← superDiag_mul (a.2 v trivial) (b.2 v trivial)]
        rfl }

theorem genChar_apply (ψ : ∀ v : Sq Hs, AddChar (ZMod (Hs.g v.1)) K) (u : levelU Hs) :
    ((genChar ψ u : Kˣ) : K) = psiU ψ (u : LevelGroup Hs) := rfl

variable (Hs)

def factorG (i : Fin 2) : Subgroup (LevelGroup Hs) := Subgroup.pi {v | v.1 ≠ i} fun _ => ⊥

def factorH (i : Fin 2) : Subgroup (LevelGroup Hs) := factorG Hs i ⊓ levelU Hs

def levelGU (i : Fin 2) : Subgroup (LevelGroup Hs) := Subgroup.pi {v | v.1 ≠ i} fun v => unitri R.r (ZMod (Hs.g v.1))

theorem exists_factor (a : LevelGroup Hs) : ∃ b ∈ factorG Hs 0, ∃ c ∈ factorG Hs 1, a = b * c ∧
    (∀ v, v.1 = 0 → b v = a v) ∧ ∀ v, v.1 = 1 → c v = a v := by
  refine ⟨fun v => if v.1 = 0 then a v else 1, fun v hv => if_neg hv, fun v => if v.1 = 1 then a v else 1,
    fun v hv => if_neg hv, funext fun v => ?_, fun v h => if_pos h, fun v h => if_pos h⟩
  obtain ⟨i, w⟩ := v
  fin_cases i <;> simp

end Generic

section Groups

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (Dw : Datum H) (l : Level H)

def typePrime (v : Sq D.host) : Ideal (𝓞 D.host.E) := halfPrime l v.2.1.asIdeal

def cofactor : ℕ := l.M / (D.host.g 0 * D.host.g 1)

def IsTypeLevel : Prop :=
  l.A = 1 ∧ l.M = D.host.g 0 * D.host.g 1 * cofactor l ∧ Nat.Coprime (D.host.g 0 * D.host.g 1) (cofactor l)

abbrev TypeFrame : Type :=
  ∀ v : Sq D.host, QMod Dw.La (typePrime l v) ≃+ (Fin D.R.r → ZMod (D.host.g v.1))

def grpR : Subgroup (LevelAut Dw l) :=
  trivMod Dw.La l.Mb (Ideal.span {((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E)})

def grpG : Subgroup (LevelAut Dw l) := trivMod Dw.La l.Mb (Ideal.span {((cofactor l : ℕ) : 𝓞 D.host.E)})

variable {Dw l}

theorem isTypeLevel_of_eq {m : ℕ} (hA : l.A = 1) (hM : l.M = D.host.g 0 * D.host.g 1 * m)
    (hm : Nat.Coprime (D.host.g 0 * D.host.g 1) m) : IsTypeLevel l ∧ cofactor l = m := by
  have h : cofactor l = m := by
    rw [cofactor, hM, Nat.mul_div_cancel_left _ (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos)]
  exact ⟨⟨hA, h ▸ hM, h ▸ hm⟩, h⟩

theorem isTypeLevel_of_pin {Q : Par D} (h : Q.PinLevel) : IsTypeLevel Q.l ∧ cofactor Q.l = 1 :=
  isTypeLevel_of_eq h.2 (by rw [mul_one]; exact h.1) (Nat.coprime_one_right _)

theorem g_mem_typePrime (v : Sq D.host) : ((D.host.g v.1 : ℕ) : 𝓞 D.host.E) ∈ typePrime l v :=
  Ideal.mem_sup_right (by simpa using Ideal.mem_map_of_mem (algebraMap _ (𝓞 D.host.E)) v.2.2)

theorem g_dvd (i : Fin 2) : D.host.g i ∣ D.host.g 0 * D.host.g 1 := by
  fin_cases i
  · exact dvd_mul_right _ _
  · exact dvd_mul_left _ _

theorem g_coprime {i j : Fin 2} (h : i ≠ j) : Nat.Coprime (D.host.g i) (D.host.g j) := by
  rw [Nat.coprime_primes (D.host.g_prime i) (D.host.g_prime j)]
  fin_cases i <;> fin_cases j
  · exact absurd rfl h
  · exact D.host.g_ne
  · exact D.host.g_ne.symm
  · exact absurd rfl h

theorem isCoprime_of_natCast {O : Type} [CommRing O] {I J : Ideal O} {a b : ℕ} (h : Nat.Coprime a b) (ha : (a : O) ∈ I)
    (hb : (b : O) ∈ J) : IsCoprime I J := by
  obtain ⟨u, v, huv⟩ := Nat.Coprime.cast (R := O) h
  exact Ideal.isCoprime_iff_exists.2 ⟨_, I.mul_mem_left u ha, _, J.mul_mem_left v hb, huv⟩

theorem typePrime_coprime : Pairwise (Function.onFun IsCoprime (typePrime l)) := by
  rintro ⟨i, v⟩ ⟨j, w⟩ hne
  by_cases h : i = j
  · subst h
    have hvw : v.1 ≠ w.1 := fun e => hne (congrArg _ (Subtype.ext e))
    obtain ⟨a, ha, b, hb, e⟩ := Ideal.isCoprime_iff_exists.1 (HeightOneSpectrum.isCoprime_of_ne _ _ hvw)
    exact Ideal.isCoprime_iff_exists.2 ⟨_, Ideal.mem_sup_right (Ideal.mem_map_of_mem _ ha), _,
      Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hb), by rw [← map_add, e, map_one]⟩
  · exact isCoprime_of_natCast (g_coprime h) (g_mem_typePrime ⟨i, v⟩) (g_mem_typePrime ⟨j, w⟩)

theorem iInf_typePrime_le :
    ⨅ v, typePrime l v ≤ l.Mb ⊔ Ideal.span {((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E)} := by
  intro x hx
  have key : ∀ i, x ∈ l.Mb ⊔ Ideal.span {((D.host.g i : ℕ) : 𝓞 D.host.E)} := by
    intro i
    have h0 : Ideal.span {((D.host.g i : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast (D.host.g_prime i).ne_zero
    have hsq : Squarefree (l.Mb ⊔ Ideal.span {((D.host.g i : ℕ) : 𝓞 D.host.E)}) :=
      ((UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors h0).2
        (Formalism.MainNotions.ModuliIntegralCharts.H1.GSplit.g_splits D i).2).squarefree_of_dvd (Ideal.dvd_iff_le.2 le_sup_right)
    have hx' : x ∈ (l.Mb ⊔ Ideal.span {((D.host.g i : ℕ) : 𝓞 D.host.E)}).radical := by
      rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
      rintro P ⟨hP, hPp⟩
      have hg : ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ Ideal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) P := by
        rw [Ideal.mem_comap, map_natCast]; exact hP (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
      let v : HeightOneSpectrum (𝓞 D.host.F) := ⟨Ideal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) P, inferInstance, fun e => by
        rw [e, Ideal.mem_bot] at hg
        exact (D.host.g_prime i).ne_zero (by exact_mod_cast hg)⟩
      have hle : typePrime l ⟨i, ⟨v, hg⟩⟩ ≤ P := sup_le (le_sup_left.trans hP) Ideal.map_comap_le
      exact hle (Ideal.mem_iInf.1 hx _)
    obtain ⟨n, hn⟩ := hx'
    refine Ideal.dvd_span_singleton.1 (hsq.isRadical n _ ?_)
    rw [Ideal.span_singleton_pow]
    exact Ideal.dvd_span_singleton.2 hn
  rw [Nat.cast_mul]
  exact mem_sup_span_mul (Nat.Coprime.cast (g_coprime (by decide))) (key 0) (key 1)

theorem IsTypeLevel.typePrime_spec (hl : IsTypeLevel l) (v : Sq D.host) :
    (typePrime l v).IsPrime ∧ Ideal.absNorm (typePrime l v) = D.host.g v.1 := by
  have hP : (typePrime l v).IsPrime := by
    refine halfPrime_isPrime l v.2.1.isMaximal ?_
    obtain ⟨k, hk⟩ := (g_dvd v.1).mul_right (cofactor l)
    rw [hl.2.1, hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ v.2.2
  exact ⟨hP, absNorm_eq_of_split (D.host.g_prime _) (D.nd.g_split _) hP (g_mem_typePrime v)⟩

theorem IsTypeLevel.smul_eq_zsmul (hl : IsTypeLevel l) (v : Sq D.host) (a : 𝓞 D.host.E) :
    ∃ n : ℤ, ∀ x : QMod Dw.La (typePrime l v), a • x = n • x := by
  have hc : Nat.card (𝓞 D.host.E ⧸ typePrime l v) = D.host.g v.1 := by
    rw [← (hl.typePrime_spec v).2, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 D.host.E ⧸ typePrime l v) := Nat.finite_of_card_ne_zero (hc ▸ (D.host.g_prime _).ne_zero)
  haveI := Fintype.ofFinite (𝓞 D.host.E ⧸ typePrime l v)
  obtain ⟨z, hz⟩ := (ZMod.ringEquivOfPrime (𝓞 D.host.E ⧸ typePrime l v) (D.host.g_prime v.1)
    (by rw [← Nat.card_eq_fintype_card, hc])).surjective (Ideal.Quotient.mk _ a)
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective z
  rw [map_intCast, ← map_intCast (Ideal.Quotient.mk (typePrime l v)), Ideal.Quotient.eq] at hz
  refine ⟨n, fun x => ?_⟩
  have h : ((n : 𝓞 D.host.E) - a) • x ∈ typePrime l v • (⊤ : Submodule _ (QMod Dw.La (typePrime l v))) :=
    Submodule.smul_mem_smul hz trivial
  rw [smul_top_qMod, Submodule.mem_bot, sub_smul, sub_eq_zero, Int.cast_smul_eq_zsmul] at h
  exact h.symm

theorem nonempty_addEquiv_pi {M : Type} [AddCommGroup M] {p r : ℕ} [hp : Fact p.Prime] (h : ∀ x : M, p • x = 0)
    (hN : Nat.card M = p ^ r) : Nonempty (M ≃+ (Fin r → ZMod p)) := by
  haveI : Finite M := Nat.finite_of_card_ne_zero (hN ▸ pow_ne_zero _ hp.out.ne_zero)
  obtain ⟨inst⟩ : Nonempty (Module (ZMod p) M) := ⟨AddCommGroup.zmodModule h⟩
  have hf : Module.finrank (ZMod p) M = Module.finrank (ZMod p) (Fin r → ZMod p) := by
    have := Module.natCard_eq_pow_finrank (K := ZMod p) (V := M)
    rw [hN, Nat.card_zmod] at this
    rw [Module.finrank_fin_fun]
    exact (Nat.pow_right_injective hp.out.two_le this).symm
  haveI : FiniteDimensional (ZMod p) M := Module.Finite.of_finite
  exact ⟨(LinearEquiv.ofFinrankEq (R := ZMod p) M (Fin r → ZMod p) hf).toAddEquiv⟩

theorem IsTypeLevel.nonempty_typeFrame (hl : IsTypeLevel l) (hr : Dw.p + Dw.q = D.R.r) : Nonempty (TypeFrame Dw l) := by
  refine ⟨fun v => Classical.choice ?_⟩
  have hc : Nat.card (𝓞 D.host.E ⧸ typePrime l v) = D.host.g v.1 := by
    rw [← (hl.typePrime_spec v).2, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 D.host.E ⧸ typePrime l v) := Nat.finite_of_card_ne_zero (hc ▸ (D.host.g_prime _).ne_zero)
  haveI := Dw.fin
  haveI := Dw.proj
  have hN : Nat.card (QMod Dw.La (typePrime l v)) = D.host.g v.1 ^ D.R.r := by
    rw [natCard_quot_smul_top_of_projective, hc, Dw.rank, hr]
  refine nonempty_addEquiv_pi (fun x => ?_) hN
  have h : ((D.host.g v.1 : ℕ) : 𝓞 D.host.E) • x ∈ typePrime l v • (⊤ : Submodule _ (QMod Dw.La (typePrime l v))) :=
    Submodule.smul_mem_smul (g_mem_typePrime v) trivial
  rwa [smul_top_qMod, Submodule.mem_bot, Nat.cast_smul_eq_nsmul] at h

def typeRed (fr : TypeFrame Dw l) : LevelAut Dw l →* LevelGroup D.host :=
  MonoidHom.pi fun v => (autMat (fr v)).comp (autRed (N := Dw.La) (J := typePrime l v) le_sup_left)

theorem typeRed_mulVec (fr : TypeFrame Dw l) (γ : LevelAut Dw l) (v : Sq D.host) (q : LaMod Dw l) :
    (typeRed fr γ v : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g v.1))).mulVec
      (fr v (qProj (J := typePrime l v) le_sup_left q)) = fr v (qProj (J := typePrime l v) le_sup_left (γ q)) :=
  (autMat_mulVec (fr v) _ _).trans (congrArg _ (autRed_qProj _ γ q))

theorem mem_grpR_iff {γ : LevelAut Dw l} : γ ∈ grpR Dw l ↔ ∀ v, γ ∈ trivMod Dw.La l.Mb (typePrime l v) := by
  refine ⟨fun h v => trivMod_mono ?_ h, fun h => ?_⟩
  · obtain ⟨k, hk⟩ := g_dvd (D := D) v.1
    rw [Ideal.span_singleton_le_iff_mem, hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (g_mem_typePrime v)
  · rw [grpR, ← trivMod_sup]
    exact trivMod_mono iInf_typePrime_le fun q => mem_iInf_smul_top typePrime_coprime fun v => h v q

theorem typeRed_eq_one (fr : TypeFrame Dw l) {γ : LevelAut Dw l} : typeRed fr γ = 1 ↔ γ ∈ grpR Dw l := by
  rw [mem_grpR_iff, funext_iff]
  refine forall_congr' fun v => Iff.trans ?_ (autRed_eq_one (J := typePrime l v) le_sup_left γ)
  exact map_eq_one_iff _ (autMat_injective (fr v))

def partIdeal (l : Level H) : Option (Sq D.host) → Ideal (𝓞 D.host.E)
  | none => l.Mb ⊔ Ideal.span {((cofactor l : ℕ) : 𝓞 D.host.E)}
  | some v => typePrime l v

theorem le_partIdeal : ∀ o, l.Mb ≤ partIdeal l o
  | none => le_sup_left
  | some _ => le_sup_left

theorem IsTypeLevel.partIdeal_coprime (hl : IsTypeLevel l) : Pairwise (Function.onFun IsCoprime (partIdeal l)) := by
  have key : ∀ v, IsCoprime (partIdeal l (some v)) (partIdeal l none) := fun v =>
    isCoprime_of_natCast (hl.2.2.coprime_dvd_left (g_dvd v.1)) (g_mem_typePrime v)
      (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  rintro (_ | v) (_ | w) h
  · exact absurd rfl h
  · exact (key w).symm
  · exact key v
  · exact typePrime_coprime fun e => h (congrArg _ e)

theorem IsTypeLevel.iInf_partIdeal_le (hl : IsTypeLevel l) : ⨅ o, partIdeal l o ≤ l.Mb := by
  intro x hx
  have h := mem_sup_span_mul (Nat.Coprime.cast hl.2.2)
    (iInf_typePrime_le (Ideal.mem_iInf.2 fun v => Ideal.mem_iInf.1 hx (some v))) (Ideal.mem_iInf.1 hx none)
  rw [← Nat.cast_mul, ← hl.2.1] at h
  exact sup_le le_rfl ((Ideal.span_singleton_le_iff_mem _).2 (natCast_M_mem l)) h

def IsTypeLevel.parts (hl : IsTypeLevel l) : LevelAut Dw l ≃* ∀ o, QAut Dw.La (partIdeal l o) :=
  crtAut le_partIdeal hl.partIdeal_coprime hl.iInf_partIdeal_le

theorem IsTypeLevel.grpG_inf_grpR (hl : IsTypeLevel l) : grpG Dw l ⊓ grpR Dw l = ⊥ := by
  refine eq_bot_iff.2 fun γ hγ => (map_eq_one_iff _ hl.parts.injective).1 (funext fun o => ?_)
  cases o with
  | none => exact (autRed_eq_one _ γ).2 (trivMod_mono le_sup_right hγ.1)
  | some v => exact (autRed_eq_one _ γ).2 (mem_grpR_iff.1 hγ.2 v)

theorem IsTypeLevel.typeRed_bijective (hl : IsTypeLevel l) (fr : TypeFrame Dw l) :
    Function.Bijective ((typeRed fr).comp (grpG Dw l).subtype) := by
  refine ⟨(injective_iff_map_eq_one _).2 fun γ hγ => Subtype.ext ?_, fun a => ?_⟩
  · exact Subgroup.mem_bot.1 (hl.grpG_inf_grpR ▸ ⟨γ.2, (typeRed_eq_one fr).1 hγ⟩)
  · choose b hb using fun v => autMat_surjective (fr v) (hl.smul_eq_zsmul v) (a v)
    obtain ⟨γ, hγ⟩ := (hl.parts (Dw := Dw)).surjective fun o => match o with
      | none => 1
      | some v => b v
    refine ⟨⟨γ, ?_⟩, funext fun v => ?_⟩
    · rw [grpG, ← trivMod_sup]
      exact (autRed_eq_one (le_partIdeal none) γ).1 (congrFun hγ none)
    · exact (congrArg (autMat (fr v)) (congrFun hγ (some v))).trans (hb v)

def typeEmb (hl : IsTypeLevel l) (fr : TypeFrame Dw l) : LevelGroup D.host →* LevelAut Dw l :=
  (grpG Dw l).subtype.comp (MulEquiv.ofBijective _ (hl.typeRed_bijective fr)).symm.toMonoidHom

theorem typeRed_typeEmb (hl : IsTypeLevel l) (fr : TypeFrame Dw l) (a : LevelGroup D.host) :
    typeRed fr (typeEmb hl fr a) = a :=
  (MulEquiv.ofBijective _ (hl.typeRed_bijective fr)).apply_symm_apply a

theorem typeEmb_mem (hl : IsTypeLevel l) (fr : TypeFrame Dw l) (a : LevelGroup D.host) : typeEmb hl fr a ∈ grpG Dw l :=
  Subtype.property _

theorem IsTypeLevel.commute (hl : IsTypeLevel l) {γ δ : LevelAut Dw l} (hγ : γ ∈ grpG Dw l) (hδ : δ ∈ grpR Dw l) :
    Commute γ δ := by
  refine hl.parts.injective ?_
  rw [map_mul, map_mul]
  funext o
  cases o with
  | none =>
    have : hl.parts γ none = 1 := (autRed_eq_one _ γ).2 (trivMod_mono le_sup_right hγ)
    simp [this]
  | some v =>
    have : hl.parts δ (some v) = 1 := (autRed_eq_one _ δ).2 (mem_grpR_iff.1 hδ v)
    simp [this]

def prodEquiv (hl : IsTypeLevel l) (fr : TypeFrame Dw l) : LevelGroup D.host × grpR Dw l ≃* LevelAut Dw l :=
  MulEquiv.ofBijective
    ((typeEmb hl fr).noncommCoprod (grpR Dw l).subtype fun a b => hl.commute (typeEmb_mem hl fr a) b.2) ⟨by
      rw [injective_iff_map_eq_one]
      rintro ⟨a, b⟩ h
      have h' : typeEmb hl fr a * b = 1 := h
      have h1 : a = 1 := by
        have := congrArg (typeRed fr) h'
        rwa [map_mul, typeRed_typeEmb, (typeRed_eq_one fr).2 b.2, mul_one, map_one] at this
      subst h1
      rw [map_one, one_mul] at h'
      exact Prod.ext rfl (Subtype.ext h'), fun γ =>
      ⟨(typeRed fr γ, ⟨(typeEmb hl fr (typeRed fr γ))⁻¹ * γ, (typeRed_eq_one fr).1 (by
        rw [map_mul, map_inv, typeRed_typeEmb, inv_mul_cancel])⟩), mul_inv_cancel_left _ _⟩⟩

theorem prodEquiv_apply (hl : IsTypeLevel l) (fr : TypeFrame Dw l) (a : LevelGroup D.host) (b : grpR Dw l) :
    prodEquiv hl fr (a, b) = typeEmb hl fr a * b := rfl

theorem typeRed_prodEquiv (hl : IsTypeLevel l) (fr : TypeFrame Dw l) (x : LevelGroup D.host × grpR Dw l) :
    typeRed fr (prodEquiv hl fr x) = x.1 := by
  rw [prodEquiv_apply, map_mul, typeRed_typeEmb, (typeRed_eq_one fr).2 x.2.2, mul_one]

def grpOf (fr : TypeFrame Dw l) (S : Subgroup (LevelGroup D.host)) : Subgroup (LevelAut Dw l) := S.comap (typeRed fr)

def grpHR (fr : TypeFrame Dw l) : Subgroup (LevelAut Dw l) := grpOf fr (levelU D.host)

def grpGHR (fr : TypeFrame Dw l) (i : Fin 2) : Subgroup (LevelAut Dw l) := grpOf fr (levelGU D.host i)

def grpOfEquiv (hl : IsTypeLevel l) (fr : TypeFrame Dw l) (S : Subgroup (LevelGroup D.host)) :
    S × grpR Dw l ≃* grpOf fr S where
  toFun x := ⟨prodEquiv hl fr (x.1, x.2), by
    show typeRed fr _ ∈ S
    rw [typeRed_prodEquiv]; exact x.1.2⟩
  invFun γ := (⟨((prodEquiv hl fr).symm γ).1, by
    rw [← typeRed_prodEquiv hl fr, MulEquiv.apply_symm_apply]; exact γ.2⟩, ((prodEquiv hl fr).symm γ).2)
  left_inv x := by simp
  right_inv γ := Subtype.ext ((prodEquiv hl fr).apply_symm_apply γ)
  map_mul' x y := Subtype.ext (map_mul (prodEquiv hl fr) ((x.1 : LevelGroup D.host), x.2) ((y.1 : LevelGroup D.host), y.2))

variable {K : Type} [Field K]

def chiHR (fr : TypeFrame Dw l) (ψ : ∀ v : Sq D.host, AddChar (ZMod (D.host.g v.1)) K) : grpHR fr →* Kˣ :=
  (genChar ψ).comp ((typeRed fr).subgroupComap (levelU D.host))

theorem chiHR_apply (fr : TypeFrame Dw l) (ψ : ∀ v : Sq D.host, AddChar (ZMod (D.host.g v.1)) K) (h : grpHR fr) :
    ((chiHR fr ψ h : Kˣ) : K) = psiU ψ (typeRed fr h) := rfl

instance fintypeSubgroup {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} (S : Subgroup (LevelAut Dw l)) : Fintype S := Fintype.ofFinite _

end Groups

end GlobalTheory.LevDesc
