import Mathlib
import Formalism.LocalToGlobal.Divisibility.DefGroup
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.LevelSubgroupFiniteAdelicStandard
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Stabstd
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsApprox
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsEasy
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsEquiv
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Stdform
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsScale
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsDual
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Formalism.LocalRingCardinality.MinkMEqMinkowskiNumber

noncomputable section

namespace GlobalTheory.latticeFrame

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.L2.Herm Formalism.L2.DIV
open scoped TensorProduct

section HatDualCopy

open Formalism.UG.P

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem levelafC_eq_inclE (D : 𝓞 F) :
    levelafC E D = inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) E D) := by
  have := csGlob_tmul_int (F := F) (E := E) (1 : E) D
  rw [mul_one] at this
  exact this

end HatDualCopy

section FrAlg

variable {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem modLI_li {S V V' V'' : Type} [CommRing S] [Algebra R S] [AddCommGroup V] [Module R V] [Module K V]
    [IsScalarTower R K V] [AddCommGroup V'] [Module R V'] [Module S V'] [IsScalarTower R S V'] [AddCommGroup V'']
    [Module R V''] (hRS : RingHom.ker (algebraMap R S) ≠ ⊤) (f : V'' →ₗ[R] V) (hf : Function.Injective f)
    (f' : V'' →ₗ[R] V') {ι : Type} {b : ι → V''} (hb' : LinearIndependent S (f' ∘ b)) :
    LinearIndependent K (f ∘ b) := by
  contrapose hb' with hb
  simp only [linearIndependent_iff', not_forall] at hb ⊢
  obtain ⟨s, g, eq, j', hj's, hj'g⟩ := hb
  use s
  obtain ⟨a, hag, j, hjs, hgI⟩ := Ideal.exist_integer_multiples_notMem hRS s g hj's hj'g
  choose g'' hg'' using hag
  let := Classical.propDecidable
  let g' i := if h : i ∈ s then g'' i h else 0
  have hg' : ∀ i ∈ s, algebraMap _ _ (g' i) = a * g i := by
    intro i hi; exact (congr_arg _ (dif_pos hi)).trans (hg'' i hi)
  have hgI : algebraMap R S (g' j) ≠ 0 := by
    simp only [FractionalIdeal.mem_coeIdeal, not_exists, not_and'] at hgI
    exact hgI _ (hg' j hjs)
  refine ⟨fun i => algebraMap R S (g' i), ?_, j, hjs, hgI⟩
  have eq : f (∑ i ∈ s, g' i • b i) = 0 := by
    rw [map_sum, ← smul_zero a, ← eq, Finset.smul_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [map_smul, ← IsScalarTower.algebraMap_smul K, hg' i hi, ← smul_assoc,
      smul_eq_mul, Function.comp_apply]
  simp only [IsScalarTower.algebraMap_smul, ← map_smul, ← map_sum,
    (f.map_eq_zero_iff hf).mp eq, map_zero, (· ∘ ·)]

theorem modLI_gen (P : Ideal R) [hP : P.IsMaximal] {n : ℕ} (L : Submodule R (Fin n → K)) (hfg : L.FG) :
    ∃ g : Fin n → (Fin n → K), (∀ i, g i ∈ L) ∧ L ≤ Submodule.span R (Set.range g) ⊔ P • L := by
  classical
  let _ : Field (R ⧸ P) := Ideal.Quotient.field P
  have : Module.Finite R ↥L := Module.Finite.iff_fg.2 hfg
  have : Module.Finite (R ⧸ P) (↥L ⧸ (P • (⊤ : Submodule R ↥L))) :=
    Module.Finite.of_restrictScalars_finite R (R ⧸ P) _
  let c := Module.finBasis (R ⧸ P) (↥L ⧸ (P • (⊤ : Submodule R ↥L)))
  choose lift hlift using Submodule.mkQ_surjective (P • (⊤ : Submodule R ↥L))
  let ct : Fin (Module.finrank (R ⧸ P) (↥L ⧸ (P • (⊤ : Submodule R ↥L)))) → ↥L := fun i => lift (c i)
  have hli : LinearIndependent K (L.subtype ∘ ct) := by
    refine modLI_li (S := R ⧸ P) ?_ L.subtype (Submodule.subtype_injective L)
      (Submodule.mkQ (P • (⊤ : Submodule R ↥L))) ?_
    · rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]; exact hP.ne_top
    · have : (Submodule.mkQ (P • (⊤ : Submodule R ↥L))) ∘ ct = c := funext fun i => hlift _
      rw [this]; exact c.linearIndependent
  have hmn : Module.finrank (R ⧸ P) (↥L ⧸ (P • (⊤ : Submodule R ↥L))) ≤ n := by
    have := hli.fintype_card_le_finrank
    simpa using this
  refine ⟨fun i => if h : i.val < Module.finrank (R ⧸ P) (↥L ⧸ (P • (⊤ : Submodule R ↥L))) then
    (ct ⟨i.val, h⟩ : Fin n → K) else 0, ?_, ?_⟩
  · intro i
    dsimp only
    split_ifs
    · exact (ct _).2
    · exact L.zero_mem
  · intro x hx
    choose r hr using fun j => Ideal.Quotient.mk_surjective
      (c.repr (Submodule.mkQ (P • (⊤ : Submodule R ↥L)) ⟨x, hx⟩) j)
    have hdiff : (⟨x, hx⟩ : ↥L) - ∑ j, r j • ct j ∈ P • (⊤ : Submodule R ↥L) := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, sub_eq_zero]
      have h1 := c.sum_repr (Submodule.mkQ (P • (⊤ : Submodule R ↥L)) ⟨x, hx⟩)
      show Submodule.mkQ (P • (⊤ : Submodule R ↥L)) ⟨x, hx⟩ =
        Submodule.mkQ (P • (⊤ : Submodule R ↥L)) (∑ j, r j • ct j)
      conv_lhs => rw [← h1]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hr j, map_smul, hlift]
      rfl
    have hdiff' : x - ∑ j, r j • (ct j : Fin n → K) ∈ P • L := by
      have h2 := Submodule.mem_map_of_mem (f := L.subtype) hdiff
      rw [Submodule.map_smul'', Submodule.map_subtype_top] at h2
      simpa using h2
    have hx2 : x = ∑ j, r j • (ct j : Fin n → K) + (x - ∑ j, r j • (ct j : Fin n → K)) := by abel
    rw [hx2]
    refine Submodule.add_mem_sup (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_) hdiff'
    refine Submodule.subset_span ⟨⟨j.val, lt_of_lt_of_le j.2 hmn⟩, ?_⟩
    dsimp only
    rw [dif_pos j.2]

end FrAlg

section FrNF

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem absNorm_coprime_of_sup (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) (D : ℕ) (h : I ⊔ Ideal.span {(D : 𝓞 E)} = ⊤) :
    Nat.Coprime (Ideal.absNorm I) D := by
  classical
  by_contra hc
  obtain ⟨p, hp, h1, h2⟩ := Nat.Prime.not_coprime_iff_dvd.1 hc
  have := Fact.mk hp
  have : Finite (𝓞 E ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  have := Fintype.ofFinite (𝓞 E ⧸ I)
  have hcard : p ∣ Fintype.card (𝓞 E ⧸ I) := by
    rw [← Nat.card_eq_fintype_card]; exact h1
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card p hcard
  have hpx : p • x = 0 := by rw [← hx]; exact addOrderOf_nsmul_eq_zero x
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [addOrderOf_zero] at hx
    exact hp.one_lt.ne hx
  obtain ⟨q, rfl⟩ := h2
  have h1' : (1 : 𝓞 E) ∈ I ⊔ Ideal.span {((p * q : ℕ) : 𝓞 E)} := by rw [h]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1'
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hb
  apply hx0
  have e1 : Ideal.Quotient.mk I (t * ((p * q : ℕ) : 𝓞 E)) = 1 := by
    rw [← map_one (Ideal.Quotient.mk I), ← hab, map_add, Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_add]
  calc x = Ideal.Quotient.mk I (t * ((p * q : ℕ) : 𝓞 E)) * x := by rw [e1, one_mul]
    _ = Ideal.Quotient.mk I t * (Ideal.Quotient.mk I (q : 𝓞 E)) * (p • x) := by
        rw [nsmul_eq_mul]; push_cast; simp only [map_mul, map_natCast]; ring
    _ = 0 := by rw [hpx, mul_zero]

theorem exists_good_basis (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG) (D : ℕ) (hD : D ≠ 0) (P0 : Pl E)
    (hP0 : (D : 𝓞 E) ∈ P0.asIdeal) :
    ∃ (b : Fin n → (Fin n → E)) (d : ℕ), (∀ i, b i ∈ L) ∧ d ≠ 0 ∧ Nat.Coprime d D ∧
      ∀ x ∈ L, (d : 𝓞 E) • x ∈ Submodule.span (𝓞 E) (Set.range b) := by
  classical
  have hD' : (D : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hD
  set Ps : Finset (Pl E) := primesOf (D : 𝓞 E) with hPs
  have hg : ∀ PP : Pl E, ∃ g : Fin n → (Fin n → E), (∀ i, g i ∈ L) ∧
      L ≤ Submodule.span (𝓞 E) (Set.range g) ⊔ PP.asIdeal • L := fun PP => by
    have := PP.isMaximal
    exact modLI_gen PP.asIdeal L hfg
  choose g hgL hgen using hg
  have hε : ∀ PP : Pl E, PP ∈ Ps → ∃ ε : 𝓞 E, ε - 1 ∈ PP.asIdeal ∧ ∀ QQ ∈ Ps, QQ ≠ PP → ε ∈ QQ.asIdeal := by
    intro PP hPP
    obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := Ps) (fun QQ : Pl E => QQ.asIdeal)
      (fun _ => 1) (fun QQ _ => QQ.prime) (fun i _ j _ hij h => hij (HeightOneSpectrum.ext h))
      (fun QQ => if QQ.1 = PP then 1 else 0)
    refine ⟨y, ?_, ?_⟩
    · have := hy PP hPP
      simpa using this
    · intro QQ hQ hne
      have := hy QQ hQ
      simpa [hne] using this
  choose! ε hε1 hε0 using hε
  let b : Fin n → (Fin n → E) := fun i => ∑ PP ∈ Ps, ε PP • g PP i
  set N := Submodule.span (𝓞 E) (Set.range b) with hN
  have hbL : ∀ i, b i ∈ L := fun i => Submodule.sum_mem _ fun PP _ => L.smul_mem _ (hgL PP i)
  have hsup : ∀ PP ∈ Ps, L ≤ N ⊔ PP.asIdeal • L := by
    intro PP hPP
    refine le_trans (hgen PP) (sup_le ?_ le_sup_right)
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have e : g PP i = b i - ((ε PP - 1) • g PP i + ∑ QQ ∈ Ps.erase PP, ε QQ • g QQ i) := by
      show _ = (∑ QQ ∈ Ps, ε QQ • g QQ i) - _
      rw [← Finset.add_sum_erase _ _ hPP, sub_smul, one_smul]; abel
    rw [SetLike.mem_coe, e]
    refine Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩))
      (Submodule.mem_sup_right ?_)
    refine Submodule.add_mem _ (Submodule.smul_mem_smul (hε1 PP hPP) (hgL PP i))
      (Submodule.sum_mem _ fun QQ hQ => ?_)
    exact Submodule.smul_mem_smul
      (hε0 QQ (Finset.mem_of_mem_erase hQ) PP hPP (Finset.ne_of_mem_erase hQ).symm) (hgL QQ i)
  have hr : ∀ PP ∈ Ps, ∃ r : 𝓞 E, r - 1 ∈ PP.asIdeal ∧ ∀ x ∈ L, r • x ∈ N := by
    intro PP hPP
    obtain ⟨r, hr1, hr2⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup hfg le_rfl (hsup PP hPP)
    exact ⟨r, hr1, fun x hx => hr2 (Submodule.smul_mem_pointwise_smul x r L hx)⟩
  let cI : Ideal (𝓞 E) :=
    { carrier := {r | ∀ x ∈ L, r • x ∈ N}
      add_mem' := fun {a b} ha hb x hx => by rw [add_smul]; exact N.add_mem (ha x hx) (hb x hx)
      zero_mem' := fun x _ => by rw [zero_smul]; exact N.zero_mem
      smul_mem' := fun c {a} ha x hx => by rw [smul_eq_mul, mul_smul]; exact N.smul_mem _ (ha x hx) }
  have hP0' : P0 ∈ Ps := mem_primesOf.2 ⟨hD', hP0⟩
  have hcI0 : cI ≠ ⊥ := by
    obtain ⟨r, hr1, hr2⟩ := hr P0 hP0'
    intro h0
    have h1 : r ∈ cI := hr2
    rw [h0, Ideal.mem_bot] at h1
    rw [h1, zero_sub, neg_mem_iff] at hr1
    exact P0.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hr1)
  have htop : cI ⊔ Ideal.span {(D : 𝓞 E)} = ⊤ := by
    by_contra hne
    obtain ⟨mI, hmax, hle⟩ := Ideal.exists_le_maximal _ hne
    have hDm : (D : 𝓞 E) ∈ mI := hle (Submodule.mem_sup_right (Ideal.mem_span_singleton_self _))
    let PP : Pl E := ⟨mI, hmax.isPrime, fun h => hD' (by rw [h] at hDm; exact hDm)⟩
    obtain ⟨r, hr1, hr2⟩ := hr PP (mem_primesOf.2 ⟨hD', hDm⟩)
    have h1 : r ∈ mI := hle (Submodule.mem_sup_left hr2)
    have h2 : (1 : 𝓞 E) ∈ mI := by
      have := mI.sub_mem h1 hr1
      simpa using this
    exact hmax.ne_top ((Ideal.eq_top_iff_one _).2 h2)
  exact ⟨b, Ideal.absNorm cI, hbL, fun h => hcI0 (Ideal.absNorm_eq_zero_iff.1 h), absNorm_coprime_of_sup cI hcI0 D htop,
    Ideal.absNorm_mem cI⟩

end FrNF

section FrAd

variable {F : Type} [Field F] [NumberField F]

theorem inv_algebraMap_int (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F) (hr : r ∉ v.asIdeal) :
    (algebraMap (𝓞 F) (v.adicCompletion F) r)⁻¹ ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, Formalism.UG.P.csApprox_val_int,
    HeightOneSpectrum.intValuation_eq_one_iff.2 hr, inv_one]

theorem exists_adele_idem (D d : 𝓞 F) (hD : D ≠ 0)
    (hcop : ∀ v : HeightOneSpectrum (𝓞 F), D ∈ v.asIdeal → d ∉ v.asIdeal) :
    ∃ e w w' : Af F, e ∈ intAd F ∧ w ∈ intAd F ∧ w' ∈ intAd F ∧ e * e = e ∧ e * w' = 0 ∧
      algebraMap (𝓞 F) (Af F) d * w = e ∧ algebraMap (𝓞 F) (Af F) D * w' = 1 - e := by
  classical
  have he : ∀ v : HeightOneSpectrum (𝓞 F),
      (if D ∈ v.asIdeal then (1 : v.adicCompletion F) else 0) ∈ v.adicCompletionIntegers F := by
    intro v
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hw : ∀ v : HeightOneSpectrum (𝓞 F),
      (if D ∈ v.asIdeal then (algebraMap (𝓞 F) (v.adicCompletion F) d)⁻¹ else 0) ∈
        v.adicCompletionIntegers F := by
    intro v
    split_ifs with h
    · exact inv_algebraMap_int v d (hcop v h)
    · exact zero_mem _
  have hw' : ∀ v : HeightOneSpectrum (𝓞 F),
      (if D ∈ v.asIdeal then 0 else (algebraMap (𝓞 F) (v.adicCompletion F) D)⁻¹) ∈
        v.adicCompletionIntegers F := by
    intro v
    split_ifs with h
    · exact zero_mem _
    · exact inv_algebraMap_int v D h
  refine ⟨⟨fun v => if D ∈ v.asIdeal then (1 : v.adicCompletion F) else 0, Filter.Eventually.of_forall he⟩,
    ⟨fun v => if D ∈ v.asIdeal then (algebraMap (𝓞 F) (v.adicCompletion F) d)⁻¹ else 0,
      Filter.Eventually.of_forall hw⟩,
    ⟨fun v => if D ∈ v.asIdeal then 0 else (algebraMap (𝓞 F) (v.adicCompletion F) D)⁻¹,
      Filter.Eventually.of_forall hw'⟩, he, hw, hw', ?_, ?_, ?_, ?_⟩
  · ext1 v
    show (if D ∈ v.asIdeal then (1 : v.adicCompletion F) else 0) * (if D ∈ v.asIdeal then 1 else 0) =
      if D ∈ v.asIdeal then 1 else 0
    split_ifs <;> simp
  · ext1 v
    show (if D ∈ v.asIdeal then (1 : v.adicCompletion F) else 0) *
      (if D ∈ v.asIdeal then 0 else (algebraMap (𝓞 F) (v.adicCompletion F) D)⁻¹) = 0
    split_ifs <;> simp
  · ext1 v
    show algebraMap (𝓞 F) (v.adicCompletion F) d *
      (if D ∈ v.asIdeal then (algebraMap (𝓞 F) (v.adicCompletion F) d)⁻¹ else 0) =
      if D ∈ v.asIdeal then 1 else 0
    split_ifs with h
    · refine mul_inv_cancel₀ (Formalism.UG.P.levelaf_algebraMap_ne_zero v d ?_)
      rintro rfl
      exact hcop v h (Ideal.zero_mem _)
    · rw [mul_zero]
  · ext1 v
    show algebraMap (𝓞 F) (v.adicCompletion F) D *
      (if D ∈ v.asIdeal then 0 else (algebraMap (𝓞 F) (v.adicCompletion F) D)⁻¹) =
      1 - if D ∈ v.asIdeal then 1 else 0
    split_ifs with h
    · rw [mul_zero, sub_self]
    · rw [sub_zero]
      exact mul_inv_cancel₀ (Formalism.UG.P.levelaf_algebraMap_ne_zero v D hD)

end FrAd

section FrGlue

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

local notation "𝒜" => E ⊗[F] Af F
local notation "ιA" => inclE (F := F) (E := E) (Af F)

theorem mem_hatL_incl {L : Submodule (𝓞 E) (Fin n → E)} {l : Fin n → E} (hl : l ∈ L) :
    (fun i => ιA (l i)) ∈ hatL (F := F) L :=
  Submodule.subset_span ⟨l, hl, rfl⟩

theorem frame_of_glue (L : Submodule (𝓞 E) (Fin n → E)) (B C : Matrix (Fin n) (Fin n) E) (hBC : B * C = 1)
    (hB : ∀ j, (fun i => B i j) ∈ L) (ε ω κ γ : 𝒜) (hε : ε ∈ intAf F E) (hω : ω ∈ intAf F E)
    (hidem : ε * ε = ε) (hεκ : ε * κ = 0) (hκγ : κ * γ = 1 - ε) (d : 𝓞 E)
    (hdω : ιA (algebraMap (𝓞 E) E d) * ω = ε)
    (hdL : ∀ x ∈ L, ∃ a : Fin n → 𝓞 E, d • x = B *ᵥ (fun j => algebraMap (𝓞 E) E (a j)))
    (hlow : ∀ v : Fin n → 𝒜, (∀ i, v i ∈ intAf F E) → (fun i => γ * v i) ∈ hatL (F := F) L)
    (hup : ∀ v ∈ hatL (F := F) L, ∀ i, κ * v i ∈ intAf F E) :

    ∃ β : GL (Fin n) 𝒜, IsFrame β L := by
  have hCB : C * B = 1 := mul_eq_one_comm.1 hBC
  set B' : Matrix (Fin n) (Fin n) 𝒜 := B.map ιA with hB'
  set C' : Matrix (Fin n) (Fin n) 𝒜 := C.map ιA with hC'
  have hBC' : B' * C' = 1 := by
    rw [hB', hC', ← Matrix.map_mul, hBC, Matrix.map_one _ (map_zero _) (map_one _)]
  have hs3 : (1 - ε) * γ * ε = 0 := by
    have : (1 - ε) * γ * ε = γ * (ε - ε * ε) := by ring
    rw [this, hidem, sub_self, mul_zero]
  have hs4 : (1 - ε) * γ * κ = 1 - ε := by
    have : (1 - ε) * γ * κ = (1 - ε) * (κ * γ) := by ring
    rw [this, hκγ]
    linear_combination hidem
  have h1 : (ε • B' + ((1 - ε) * γ) • (1 : Matrix (Fin n) (Fin n) 𝒜)) *
      (ε • C' + κ • (1 : Matrix (Fin n) (Fin n) 𝒜)) = 1 := by
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_one, Matrix.one_mul]
    rw [hidem, mul_comm ε ((1 - ε) * γ), hs3, mul_comm κ ε, hεκ, mul_comm κ ((1 - ε) * γ), hs4, hBC', zero_smul,
      zero_smul, add_zero, zero_add, ← add_smul, add_sub_cancel, one_smul]
  have h2 := mul_eq_one_comm.1 h1
  have hinv : ∀ (x : Fin n → 𝒜) (i : Fin n),
      ((ε • C' + κ • (1 : Matrix (Fin n) (Fin n) 𝒜)) *ᵥ x) i = ε * (C' *ᵥ x) i + κ * x i := by
    intro x i
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    rfl
  have key1 : ∀ x ∈ hatL (F := F) L, ∀ i, ε * (C' *ᵥ x) i ∈ intAf F E := by
    intro x hx
    unfold hatL latS at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      intro i
      obtain ⟨a, ha⟩ := hdL l hl
      have e1 : (C' *ᵥ fun i => ιA (l i)) i = ιA ((C *ᵥ l) i) := by
        simp only [Matrix.mulVec, dotProduct, hC', Matrix.map_apply, map_sum, map_mul]
      have e2 : algebraMap (𝓞 E) E d * (C *ᵥ l) i = algebraMap (𝓞 E) E (a i) := by
        have h3 : C *ᵥ (d • l) = fun j => algebraMap (𝓞 E) E (a j) := by
          rw [ha, Matrix.mulVec_mulVec, hCB, Matrix.one_mulVec]
        have h4 := congrFun h3 i
        rw [Matrix.mulVec_smul, Pi.smul_apply, Algebra.smul_def] at h4
        exact h4
      rw [e1, ← hdω, mul_right_comm, ← map_mul, e2]
      exact mul_mem (Formalism.UG.CS.incl_int (a i)) hω
    | zero =>
      intro i
      rw [Matrix.mulVec_zero, Pi.zero_apply, mul_zero]
      exact zero_mem _
    | add x y _ _ hx hy =>
      intro i
      rw [Matrix.mulVec_add, Pi.add_apply, mul_add]
      exact add_mem (hx i) (hy i)
    | smul s x _ hx =>
      intro i
      have e : (C' *ᵥ (s • x)) i = (s : 𝒜) * (C' *ᵥ x) i := by
        rw [Matrix.mulVec_smul]; rfl
      rw [e, mul_left_comm]
      exact mul_mem s.2 (hx i)
  refine ⟨⟨_, _, h1, h2⟩, fun x => ?_⟩
  show x ∈ hatL (F := F) L ↔ ∀ i, ((ε • C' + κ • (1 : Matrix (Fin n) (Fin n) 𝒜)) *ᵥ x) i ∈ intAf F E
  constructor
  · intro hx i
    rw [hinv]
    exact add_mem (key1 x hx i) (hup x hx i)
  · intro hy
    set y := (ε • C' + κ • (1 : Matrix (Fin n) (Fin n) 𝒜)) *ᵥ x with hydef
    have hxy : x = (ε • B' + ((1 - ε) * γ) • (1 : Matrix (Fin n) (Fin n) 𝒜)) *ᵥ y := by
      rw [hydef, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
    have e3 : (ε • B' + ((1 - ε) * γ) • (1 : Matrix (Fin n) (Fin n) 𝒜)) *ᵥ y =
        (⟨ε, hε⟩ : intAf F E) • (∑ j, (⟨y j, hy j⟩ : intAf F E) • (fun i => ιA (B i j))) +
          (⟨1 - ε, sub_mem (one_mem _) hε⟩ : intAf F E) • (fun i => γ * y i) := by
      funext i
      rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
      simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, Subring.smul_def, smul_eq_mul, Matrix.mulVec,
        dotProduct, hB', Matrix.map_apply]
      congr 1
      · congr 1
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _
      · ring
    rw [hxy, e3]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (mem_hatL_incl (hB j)))) (Submodule.smul_mem _ _ (hlow y hy))

end FrGlue

theorem exists_frame (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsLattice E L) :
    ∃ β : GL (Fin n) (E ⊗[F] Af F), IsFrame β L := by
  classical
  have hfin : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hL.fg
  have hspan := hL.span_eq_top
  obtain ⟨c, hc0, hc⟩ := Formalism.UG.P.adelstabL_lower (F := F) L hspan
  obtain ⟨d0, hd00, hd0⟩ := Formalism.UG.P.adelstabL_upper (F := F) L hfin
  obtain ⟨p, hp0, hp⟩ := Ring.not_isField_iff_exists_prime.1 (RingOfIntegers.not_isField E)
  let P0 : Pl E := ⟨p, hp, hp0⟩
  set D1 : ℕ := Ideal.absNorm (Ideal.span {c * d0} : Ideal (𝓞 F)) with hD1
  set D2 : ℕ := Ideal.absNorm P0.asIdeal with hD2
  have hD1' : D1 ≠ 0 := by
    rw [hD1, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact mul_ne_zero hc0 hd00
  have hD2' : D2 ≠ 0 := by
    rw [hD2, Ne, Ideal.absNorm_eq_zero_iff]
    exact hp0
  obtain ⟨t, ht⟩ : ∃ t : 𝓞 F, t * (c * d0) = (D1 : 𝓞 F) :=
    Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem _)
  have hP0 : ((D1 * D2 : ℕ) : 𝓞 E) ∈ P0.asIdeal := by
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.absNorm_mem _)
  obtain ⟨b, d, hbL, hd, hcop, hdL⟩ := exists_good_basis L hL.fg (D1 * D2) (mul_ne_zero hD1' hD2') P0 hP0
  have hcopF : ∀ v : HeightOneSpectrum (𝓞 F), ((D1 * D2 : ℕ) : 𝓞 F) ∈ v.asIdeal →
      ((d : ℕ) : 𝓞 F) ∉ v.asIdeal := by
    intro v h1 h2
    obtain ⟨x, y, hxy⟩ := Nat.isCoprime_iff_coprime.2 hcop
    have h3 : (1 : 𝓞 F) ∈ v.asIdeal := by
      have e : (1 : 𝓞 F) = (x : 𝓞 F) * ((d : ℕ) : 𝓞 F) + (y : 𝓞 F) * ((D1 * D2 : ℕ) : 𝓞 F) := by
        have := congrArg (Int.cast : ℤ → 𝓞 F) hxy
        push_cast at this ⊢
        exact this.symm
      rw [e]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h2) (Ideal.mul_mem_left _ _ h1)
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h3)
  obtain ⟨e, w, w', he, hw, hw', hee, hew', hdw, hDw'⟩ := exists_adele_idem ((D1 * D2 : ℕ) : 𝓞 F) ((d : ℕ) : 𝓞 F)
    (Nat.cast_ne_zero.2 (mul_ne_zero hD1' hD2')) hcopF
  have hdE : (d : E) ≠ 0 := Nat.cast_ne_zero.2 hd
  have hspanb : Submodule.span E (Set.range b) = ⊤ := by
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    intro x hx
    have h2 : ((d : ℕ) : 𝓞 E) • x ∈ Submodule.span E (Set.range b) :=
      Submodule.span_subset_span (𝓞 E) E _ (hdL x hx)
    have h3 : x = ((d : E))⁻¹ • (((d : ℕ) : 𝓞 E) • x) := by
      rw [← algebraMap_smul E (((d : ℕ) : 𝓞 E)) x, map_natCast, inv_smul_smul₀ hdE]
    rw [SetLike.mem_coe, h3]
    exact Submodule.smul_mem _ _ h2
  choose Cc hCc using fun k : Fin n => (Submodule.mem_span_range_iff_exists_fun E).1
    (hspanb ▸ Submodule.mem_top : (Pi.single k 1 : Fin n → E) ∈ Submodule.span E (Set.range b))
  have hBC : (Matrix.of fun i j => b j i : Matrix (Fin n) (Fin n) E) * (Matrix.of fun j k => Cc k j) = 1 := by
    ext i k
    have h1 := congrFun (hCc k) i
    rw [Finset.sum_apply] at h1
    rw [Matrix.mul_apply, Matrix.one_apply, ← Pi.single_apply, ← h1]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hmem : ∀ {a : Af F}, a ∈ intAd F → ((1 : E) ⊗ₜ[F] a : E ⊗[F] Af F) ∈ intAf F E :=
    fun {a} ha => Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
  have hDeq : t * d0 * (D2 : 𝓞 F) * c = ((D1 * D2 : ℕ) : 𝓞 F) := by
    rw [Nat.cast_mul, ← ht]; ring
  refine frame_of_glue L _ _ hBC (fun j => hbL j) ((1 : E) ⊗ₜ[F] e) ((1 : E) ⊗ₜ[F] w)
    (((1 : E) ⊗ₜ[F] w') * Formalism.UG.P.levelafC E (t * d0 * (D2 : 𝓞 F))) (Formalism.UG.P.levelafC E c) (hmem he) (hmem hw)
    ?_ ?_ ?_ ((d : ℕ) : 𝓞 E) ?_ ?_ hc ?_
  · rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hee]
  · rw [← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, hew', TensorProduct.tmul_zero, zero_mul]
  · rw [mul_assoc, ← Formalism.UG.P.levelafC_mul, hDeq]
    unfold Formalism.UG.P.levelafC
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm w', hDw', TensorProduct.tmul_sub]
    rfl
  · have h1 : inclE (F := F) (E := E) (Af F) (algebraMap (𝓞 E) E ((d : ℕ) : 𝓞 E)) =
        Formalism.UG.P.levelafC E ((d : ℕ) : 𝓞 F) := by
      rw [levelafC_eq_inclE]
      simp only [map_natCast]
    rw [h1]
    unfold Formalism.UG.P.levelafC
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hdw]
  · intro x hx
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 (hdL x hx)
    refine ⟨a, ?_⟩
    rw [← ha]
    funext i
    rw [Finset.sum_apply]
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, Algebra.smul_def]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  · intro v hv i
    have e1 : ((1 : E) ⊗ₜ[F] w') * Formalism.UG.P.levelafC E (t * d0 * (D2 : 𝓞 F)) * v i =
        ((1 : E) ⊗ₜ[F] w') * Formalism.UG.P.levelafC E (t * (D2 : 𝓞 F)) * (Formalism.UG.P.levelafC E d0 * v i) := by
      rw [show t * d0 * (D2 : 𝓞 F) = t * (D2 : 𝓞 F) * d0 by ring, Formalism.UG.P.levelafC_mul]
      ring
    rw [e1]
    exact mul_mem (mul_mem (hmem hw') (Formalism.UG.P.levelafC_mem _)) (hd0 v hv i)

end GlobalTheory.latticeFrame

end
