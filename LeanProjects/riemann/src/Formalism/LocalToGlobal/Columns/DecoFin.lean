import Mathlib
import Formalism.LocalToGlobal.Columns.StdLatUnimodular
import Formalism.LocalToGlobal.Columns.BaseLemmas
import Formalism.HermitianLattices.FinalNeighbourConstruct
import Formalism.SatakeDualWeyl.KpqSubgroupCompact

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.HermitianLatticesTheory

section Fin

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

variable (E) in

def PosStar : Prop := ∀ a : E, a ≠ 0 → 0 < Algebra.trace ℚ E (star a * a)

theorem posStar_of_conj (h : ∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) :
    PosStar E := by
  intro a ha
  have h1 : ((Algebra.trace ℚ E (star a * a) : ℚ) : ℂ) =
      ((∑ τ : E →ₐ[ℚ] ℂ, Complex.normSq (τ a) : ℝ) : ℂ) := by
    have := trace_eq_sum_embeddings (K := ℚ) (L := E) ℂ (x := star a * a)
    rw [eq_ratCast] at this
    rw [this, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [map_mul, show τ (star a) = starRingEnd ℂ (τ a) from h τ.toRingHom a, mul_comm,
      Complex.mul_conj]
  have h2 : (0 : ℝ) < ∑ τ : E →ₐ[ℚ] ℂ, Complex.normSq (τ a) := by
    apply Finset.sum_pos
    · intro τ _
      exact Complex.normSq_pos.2 (by simpa using ha)
    · have : Nonempty (E →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩
      exact Finset.univ_nonempty
  have h3 : ((Algebra.trace ℚ E (star a * a) : ℚ) : ℝ) = ∑ τ : E →ₐ[ℚ] ℂ, Complex.normSq (τ a) := by
    exact_mod_cast h1
  rw [← h3] at h2
  exact_mod_cast h2

theorem hStd_pos (hE : PosStar E) (x : Sp E n) (hx : x ≠ 0) :
    0 < Algebra.trace ℚ E (hStd E n x x) := by
  simp only [hStd, LinearMap.mk₂'ₛₗ_apply, map_sum]
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  refine lt_of_lt_of_le (hE (x i) hi) ?_
  refine Finset.single_le_sum (f := fun j => Algebra.trace ℚ E (star (x j) * x j)) ?_ (Finset.mem_univ i)
  intro j _
  by_cases hj : x j = 0
  · simp [hj]
  · exact (hE (x j) hj).le

theorem star_range (r : 𝓞 E) : star (algebraMap (𝓞 E) E r) ∈ Set.range (algebraMap (𝓞 E) E) := ⟨RingOfIntegers.mapRingHom (starRingEnd E) r, rfl⟩

theorem unimod_finite (hE : PosStar E) (n : ℕ) :
    ∃ s : Finset (Submodule (𝓞 E) (Sp E n)),
      (∀ N ∈ s, Submodule.IsLattice E N ∧ IsUnimodular (hStd E n) N) ∧
      ∀ M, Submodule.IsLattice E M → IsUnimodular (hStd E n) M →
        ∃ N ∈ s, ∃ g ∈ UF E n, gmap g N = M := by
  have hpos := hStd_pos hE (n := n)
  obtain ⟨m, ι, hι, hmul, hlat⟩ := final_traceReal E (Sp E n) (hStd E n) hStd_isSymm hpos
  set h := hStd E n with hh
  set e : ℤ := NumberField.discr E with he
  have he0 : e ≠ 0 := NumberField.discr_ne_zero E
  have ecast : ((e.natAbs ^ 2 : ℕ) : E) = ((e : E)) * (e : E) := by
    have h0 : ((e.natAbs ^ 2 : ℕ) : ℤ) = e * e := by rw [Nat.cast_pow, Int.natAbs_sq, sq]
    rw [← Int.cast_natCast, h0, Int.cast_mul]
  obtain ⟨s, hs1, hs2⟩ := classSetFinite_core final_shortVectors final_finIntermediate
    final_isomOfTrace h hpos m ι hι hmul 1 one_pos (Real.sqrt (((e.natAbs ^ 2 : ℕ) : ℝ) ^ m))
    {M | Submodule.IsLattice E M ∧ IsUnimodular h M}
    (by
      rintro M ⟨-, hM⟩ x hx y hy
      rw [Nat.cast_one, one_mul]
      rw [← hM] at hy
      exact (mem_dual M y).1 hy x hx)
    (fun M hM => hlat M hM.1)
    (by
      rintro M ⟨-, hM⟩ _ _
      apply genusCovolBound_covol_le h m ι hι M (e.natAbs ^ 2)
        (pow_pos (Int.natAbs_pos.mpr he0) 2)
      have hdualmem : ∀ y, (∀ x ∈ M, ∃ z : ℤ, Algebra.trace ℚ E (h x y) = z) →
          ((e : E) • y) ∈ dual h M := by
        intro y hy
        rw [mem_dual]
        intro x hx
        rw [LinearMap.map_smul, smul_eq_mul]
        apply genusCovolBound_discr
        intro r
        obtain ⟨s, hs'⟩ := star_range r
        obtain ⟨z, hz⟩ := hy (s • x) (M.smul_mem s hx)
        refine ⟨z, ?_⟩
        rw [← hz]
        congr 1
        rw [← algebraMap_smul E s x, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
          starRingEnd_apply, hs', star_star, mul_comm]
      intro y y' hy hy'
      have h1 := hdualmem y hy
      rw [hM] at h1
      have hm := (mem_dual M _).1 (hdualmem y' hy') _ h1
      have key : h ((e : E) • y) ((e : E) • y') =
          algebraMap ℚ E ((e.natAbs ^ 2 : ℕ) : ℚ) * h y y' := by
        rw [map_natCast, ecast]
        simp only [LinearMap.map_smulₛₗ₂, LinearMap.map_smul, starRingEnd_apply, star_intCast,
          smul_eq_mul]
        ring
      rw [key] at hm
      obtain ⟨r, hr⟩ := Submodule.mem_one.mp hm
      obtain ⟨z, hz⟩ := genusCovolBound_trace_int r
      refine ⟨z, ?_⟩
      rw [← hz, hr, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul])
  exact ⟨s, hs1, fun M h1 h2 => hs2 M ⟨h1, h2⟩⟩

end Fin

section Orbits

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

instance finite_quot (P : HeightOneSpectrum (𝓞 E)) : Finite (𝓞 E ⧸ P.asIdeal) :=
  Ideal.finiteQuotientOfFreeOfNeBot P.asIdeal P.ne_bot

private theorem mem_localized_of_mem (Q : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n))
    {x : Sp E n} (hx : x ∈ N) : x ∈ localization₂ Q.asIdeal N :=
  show ∃ s ∈ Q.asIdeal.primeCompl, s • x ∈ N from ⟨1, Q.asIdeal.primeCompl.one_mem, by rwa [one_smul]⟩

theorem Deco.Ok.f_eq_of_span {d d' : Deco E n ST SG} (hd : d.Ok) (hd' : d'.Ok) (hN : d.N = d'.N)
    {S : Set (Sp E n)} (hS : Submodule.span (𝓞 E) S = d.N) (P : ST)
    (h : ∀ b ∈ S, d.f P b = d'.f P b) : ∀ x ∈ d.N, d.f P x = d'.f P x := by
  have hm : ∀ y ∈ Submodule.span (𝓞 E) S, y ∈ d.at P.1 ∧ y ∈ d'.at P.1 := fun y hy =>
    ⟨mem_localized_of_mem P.1 d.N (hS ▸ hy), mem_localized_of_mem P.1 d'.N (hN ▸ hS ▸ hy)⟩
  have z0 : ∀ e : Deco E n ST SG, e.Ok → e.f P 0 = 0 := fun e he => by
    have h0 := he.f_smul P 0 0 (Submodule.zero_mem _)
    simpa using h0
  intro x hx
  rw [← hS] at hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact h y hy
  | zero => rw [z0 d hd, z0 d' hd']
  | add y z hy hz ihy ihz =>
    rw [hd.f_add P y (hm y hy).1 z (hm z hz).1, hd'.f_add P y (hm y hy).2 z (hm z hz).2, ihy, ihz]
  | smul a y hy ih =>
    rw [hd.f_smul P a y (hm y hy).1, hd'.f_smul P a y (hm y hy).2, ih]

theorem Deco.Ok.be_eq_of_span {d d' : Deco E n ST SG} (hd : d.Ok) (hd' : d'.Ok) (hN : d.N = d'.N)
    {S : Set (Sp E n)} (hS : Submodule.span (𝓞 E) S = d.N) (w : SG)
    (h : ∀ b ∈ S, d.be w b = d'.be w b) : ∀ x ∈ d.N, d.be w x = d'.be w x := by
  have hm : ∀ y ∈ Submodule.span (𝓞 E) S, y ∈ d.at w.1 ∧ y ∈ d'.at w.1 := fun y hy =>
    ⟨mem_localized_of_mem w.1 d.N (hS ▸ hy), mem_localized_of_mem w.1 d'.N (hN ▸ hS ▸ hy)⟩
  have z0 : ∀ e : Deco E n ST SG, e.Ok → e.be w 0 = 0 := fun e he => by
    have h0 := he.be_smul w 0 0 (Submodule.zero_mem _)
    simpa using h0
  intro x hx
  rw [← hS] at hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact h y hy
  | zero => rw [z0 d hd, z0 d' hd']
  | add y z hy hz ihy ihz =>
    rw [hd.be_add w y (hm y hy).1 z (hm z hz).1, hd'.be_add w y (hm y hy).2 z (hm z hz).2, ihy, ihz]
  | smul a y hy ih =>
    rw [hd.be_smul w a y (hm y hy).1, hd'.be_smul w a y (hm y hy).2, ih]

theorem DecoSet.finite_fibre (N : Submodule (𝓞 E) (Sp E n)) (hN : N.FG) :
    {d : DecoSet E n ST SG | d.1.N = N}.Finite := by
  obtain ⟨S, hS⟩ := hN
  let Φ : {d : DecoSet E n ST SG | d.1.N = N} →
      (∀ P : ST, S → 𝓞 E ⧸ P.1.asIdeal) × (∀ w : SG, S → Fin n → 𝓞 E ⧸ w.1.asIdeal) :=
    fun d => (fun P b => d.1.1.f P b.1, fun w b => d.1.1.be w b.1)
  have hΦ : Function.Injective Φ := by
    rintro ⟨d, hd⟩ ⟨d', hd'⟩ hdd
    have hd0 : d.1.N = N := hd
    have hd0' : d'.1.N = N := hd'
    apply Subtype.ext
    apply Subtype.ext
    have e1 := congrArg Prod.fst hdd
    have e2 := congrArg Prod.snd hdd
    refine Deco.Ok.ext_on d.2 d'.2 (hd0.trans hd0'.symm) (fun P => ?_) (fun w => ?_)
    · exact Deco.Ok.f_eq_of_span d.2 d'.2 (hd0.trans hd0'.symm) (hS.trans hd0.symm) P
        fun b hb => congrFun (congrFun e1 P) ⟨b, hb⟩
    · exact Deco.Ok.be_eq_of_span d.2 d'.2 (hd0.trans hd0'.symm) (hS.trans hd0.symm) w
        fun b hb => congrFun (congrFun e2 w) ⟨b, hb⟩
  exact Set.finite_coe_iff.1 (Finite.of_injective Φ hΦ)

theorem DecoSet.finite_reps (hE : PosStar E) :
    ∃ s : Set (DecoSet E n ST SG), s.Finite ∧
      ∀ d, ∃ d0 ∈ s, ∃ g : UF E n, d = (g, (1 : GLG E n SG)) • d0 := by
  classical
  obtain ⟨S, hS, hrep⟩ := unimod_finite hE n
  have key : ∀ (h : Sp E n ≃ₗ[E] Sp E n) (L : Submodule (𝓞 E) (Sp E n)), gmap h.symm (gmap h L) = L := by
    intro h L
    ext x
    simp only [gmap, Submodule.mem_map, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      simpa using hz
    · intro hx
      exact ⟨h x, ⟨x, hx, rfl⟩, by simp⟩
  refine ⟨⋃ N ∈ (S : Set (Submodule (𝓞 E) (Sp E n))), {d : DecoSet E n ST SG | d.1.N = N}, ?_, ?_⟩
  · exact S.finite_toSet.biUnion fun N hN => DecoSet.finite_fibre N (hS N hN).1.fg
  · intro d
    obtain ⟨N, hN, g, hg, hgN⟩ := hrep d.1.N d.2.lat d.2.uni
    refine ⟨((⟨g, hg⟩ : UF E n), (1 : GLG E n SG))⁻¹ • d,
      Set.mem_biUnion (Finset.mem_coe.mpr hN) ?_, ⟨g, hg⟩, (smul_inv_smul _ d).symm⟩
    show (((⟨g, hg⟩ : UF E n), (1 : GLG E n SG))⁻¹ • d).1.N = N
    rw [DecoSet.smul_val]
    show gmap g.symm d.1.N = N
    rw [← hgN]
    exact key g N

theorem DecoSet.finite_orbits (hE : PosStar E) (Γ : Subgroup (UF E n × GLG E n SG))
    (hΓ : ∀ g : UF E n, (g, (1 : GLG E n SG)) ∈ Γ) :
    Finite (MulAction.orbitRel.Quotient Γ (DecoSet E n ST SG)) := by
  obtain ⟨s, hs, hrep⟩ := DecoSet.finite_reps (E := E) (n := n) (ST := ST) (SG := SG) hE
  haveI : Finite s := hs.to_subtype
  refine Finite.of_surjective
    (fun x : s => (Quotient.mk _ x.1 : MulAction.orbitRel.Quotient Γ (DecoSet E n ST SG))) ?_
  intro z
  induction z using Quotient.inductionOn with
  | h d =>
    obtain ⟨d0, hd0, g, rfl⟩ := hrep d
    refine ⟨⟨d0, hd0⟩, ?_⟩
    have hmem : (g, (1 : GLG E n SG)) • d0 ∈ MulAction.orbit Γ d0 := ⟨⟨(g, 1), hΓ g⟩, rfl⟩
    exact (Quotient.sound (s := MulAction.orbitRel Γ (DecoSet E n ST SG)) hmem).symm

theorem DecoSet.stab_fst_injective (d : DecoSet E n ST SG) {a b : UF E n × GLG E n SG}
    (ha : a • d = d) (hb : b • d = d) (hab : a.1 = b.1) : a = b := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  simp only at hab
  subst hab
  congr 1
  funext w
  apply Units.ext
  have hA : ∀ x, (a2 w).1.mulVec (d.1.be w (a1.1.symm x)) = d.1.be w x := fun x => by
    have h1 := congrArg (fun e : DecoSet E n ST SG => e.1.be w x) ha
    simpa [DecoSet.smul_val, Deco.act] using h1
  have hB : ∀ x, (b2 w).1.mulVec (d.1.be w (a1.1.symm x)) = d.1.be w x := fun x => by
    have h1 := congrArg (fun e : DecoSet E n ST SG => e.1.be w x) hb
    simpa [DecoSet.smul_val, Deco.act] using h1
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro c
  obtain ⟨x, hx, hxc⟩ := d.2.be_surj w c
  simp only [Matrix.toLin'_apply]
  rw [← hxc, ← LinearEquiv.symm_apply_apply a1.1 x, hA, hB]

theorem DecoSet.finite_stabilizer (hE : PosStar E) (d : DecoSet E n ST SG) :
    Finite (MulAction.stabilizer (UF E n × GLG E n SG) d) := by
  have hA := final_autFinite E (Sp E n) (hStd E n) hStd_isSymm (hStd_pos hE) d.1.N d.2.lat
  have : Finite {g : Sp E n ≃ₗ[E] Sp E n | g ∈ isom (hStd E n) ∧ gmap g d.1.N = d.1.N} := hA
  let Φ : MulAction.stabilizer (UF E n × GLG E n SG) d →
      {g : Sp E n ≃ₗ[E] Sp E n | g ∈ isom (hStd E n) ∧ gmap g d.1.N = d.1.N} :=
    fun a => ⟨a.1.1.1, a.1.1.2, congrArg (fun d : DecoSet E n ST SG => d.1.N) a.2⟩
  refine Finite.of_injective Φ ?_
  intro a b hab
  apply Subtype.ext
  exact DecoSet.stab_fst_injective d a.2 b.2 (Subtype.ext (show a.1.1.1 = b.1.1.1 from
    congrArg (fun g : {g : Sp E n ≃ₗ[E] Sp E n | g ∈ isom (hStd E n) ∧ gmap g d.1.N = d.1.N} => g.1) hab))

end Orbits

section Glue

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

variable (E) in

def cO : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (starRingEnd E)

theorem algebraMap_cO (r : 𝓞 E) : algebraMap (𝓞 E) E (cO E r) = star (algebraMap (𝓞 E) E r) := rfl

theorem cO_cO (r : 𝓞 E) : cO E (cO E r) = r := by
  apply IsFractionRing.injective (𝓞 E) E
  rw [algebraMap_cO, algebraMap_cO, star_star]

theorem conjIdeal_eq (P : Ideal (𝓞 E)) : conjIdeal (K := E) P = P.comap (cO E) := by
  have hset : {r : 𝓞 E | ∃ s ∈ P, algebraMap (𝓞 E) E r = star (algebraMap (𝓞 E) E s)} =
      (P.comap (cO E) : Set (𝓞 E)) := by
    ext r
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, Ideal.mem_comap]
    constructor
    · rintro ⟨s, hs, h⟩
      have hrs : cO E r = s := by
        apply IsFractionRing.injective (𝓞 E) E
        rw [algebraMap_cO, h, star_star]
      rw [hrs]
      exact hs
    · intro h
      exact ⟨cO E r, h, by rw [algebraMap_cO, star_star]⟩
  show Ideal.span {r : 𝓞 E | ∃ s ∈ P, algebraMap (𝓞 E) E r = star (algebraMap (𝓞 E) E s)} = _
  rw [hset, Ideal.span_eq]

theorem mem_conjIdeal (P : Ideal (𝓞 E)) (r : 𝓞 E) : r ∈ conjIdeal (K := E) P ↔ cO E r ∈ P := by
  rw [conjIdeal_eq, Ideal.mem_comap]

theorem hStd_nondeg : (hStd E n).Nondegenerate := by
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · funext i
    have h1 := hx (Pi.single i 1)
    simpa [hStd, Pi.single_apply] using h1
  · funext i
    have h1 := hy (Pi.single i 1)
    simp only [hStd, LinearMap.mk₂'ₛₗ_apply] at h1
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, star_zero, zero_mul])
      (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, star_one, one_mul] at h1
    exact h1

theorem hStd_osmul_left (r : 𝓞 E) (x y : Sp E n) : hStd E n (r • x) y = hStd E n x (cO E r • y) := by
  simp only [hStd, LinearMap.mk₂'ₛₗ_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, Algebra.smul_def, star_mul', algebraMap_cO]
  ring

theorem hStd_mem_one_symm {x y : Sp E n} (h : hStd E n x y ∈ (1 : Submodule (𝓞 E) E)) :
    hStd E n y x ∈ (1 : Submodule (𝓞 E) E) := by
  have hs : hStd E n y x = star (hStd E n x y) := by
    simp only [hStd, LinearMap.mk₂'ₛₗ_apply, star_sum, star_mul', star_star]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  obtain ⟨r, hr⟩ := Submodule.mem_one.mp h
  exact Submodule.mem_one.mpr ⟨cO E r, by rw [hs, ← hr, algebraMap_cO]⟩

private theorem mem_dual_lemma_2 (L : Submodule (𝓞 E) (Sp E n)) (y : Sp E n) :
    y ∈ dual (hStd E n) L ↔ ∀ x ∈ L, hStd E n x y ∈ (1 : Submodule (𝓞 E) E) := by
  simp only [dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply]

theorem dual_anti {L M : Submodule (𝓞 E) (Sp E n)} (h : L ≤ M) :
    dual (hStd E n) M ≤ dual (hStd E n) L := by
  intro y hy
  rw [mem_dual_lemma_2] at hy ⊢
  exact fun x hx => hy x (h hx)

private theorem hStd_symm_lemma_8 : (hStd E n).IsSymm := by
  first
  | exact fun x y => by
      simp only [hStd, LinearMap.mk₂'ₛₗ_apply, map_sum, map_mul, starRingEnd_apply, star_star]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  | exact ⟨fun x y => by
      simp only [hStd, LinearMap.mk₂'ₛₗ_apply, map_sum, map_mul, starRingEnd_apply, star_star]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _⟩

theorem dual_dual {L : Submodule (𝓞 E) (Sp E n)} (hL : Submodule.IsLattice E L) :
    dual (hStd E n) (dual (hStd E n) L) = L := by
  exact (dualLattice (𝓞 E) E (Sp E n) (hStd E n) hStd_symm_lemma_8 hStd_nondeg star_range L hL).2.1

theorem dual_lattice {L : Submodule (𝓞 E) (Sp E n)} (hL : Submodule.IsLattice E L) :
    Submodule.IsLattice E (dual (hStd E n) L) := by
  exact (dualLattice (𝓞 E) E (Sp E n) (hStd E n) hStd_symm_lemma_8 hStd_nondeg star_range L hL).1

theorem mem_dual_sup (L M : Submodule (𝓞 E) (Sp E n)) (y : Sp E n) :
    y ∈ dual (hStd E n) (L ⊔ M) ↔ y ∈ dual (hStd E n) L ∧ y ∈ dual (hStd E n) M := by
  rw [mem_dual_lemma_2, mem_dual_lemma_2, mem_dual_lemma_2]
  constructor
  · intro h
    exact ⟨fun x hx => h x (Submodule.mem_sup_left hx), fun x hx => h x (Submodule.mem_sup_right hx)⟩
  · rintro ⟨h1, h2⟩ x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add, LinearMap.add_apply]
    exact Submodule.add_mem _ (h1 a ha) (h2 b hb)

theorem mem_dual_smul (I : Ideal (𝓞 E)) (D : Submodule (𝓞 E) (Sp E n)) (y : Sp E n) :
    y ∈ dual (hStd E n) (I • D) ↔ ∀ p ∈ I, cO E p • y ∈ dual (hStd E n) D := by
  rw [mem_dual_lemma_2]
  constructor
  · intro h p hp
    rw [mem_dual_lemma_2]
    intro x hx
    rw [← hStd_osmul_left]
    exact h _ (Submodule.smul_mem_smul hp hx)
  · intro h z hz
    refine Submodule.smul_induction_on hz ?_ ?_
    · intro p hp x hx
      rw [hStd_osmul_left]
      exact (mem_dual_lemma_2 D _).mp (h p hp) x hx
    · intro a b ha hb
      rw [map_add, LinearMap.add_apply]
      exact Submodule.add_mem _ ha hb

theorem lattice_between {B M D : Submodule (𝓞 E) (Sp E n)} (hB : Submodule.IsLattice E B)
    (hD : Submodule.IsLattice E D) (h1 : B ≤ M) (h2 : M ≤ D) : Submodule.IsLattice E M :=
  ⟨Submodule.FG.of_le hD.fg h2, by
    rw [eq_top_iff, ← hB.span_eq_top]
    exact Submodule.span_mono h1⟩

theorem glue_unimodular {I J : Ideal (𝓞 E)} (hIJ : ∀ p ∈ I, cO E p ∈ J) (hJI : ∀ p ∈ J, cO E p ∈ I)
    (hcop : ∃ e ∈ I, ∃ e' ∈ J, e + e' = 1) {N B : Submodule (𝓞 E) (Sp E n)}
    (hN : IsUnimodular (hStd E n) N) (hB : Submodule.IsLattice E B) (hBN : B ≤ N)
    (hIN : I • N ≤ B) :
    Submodule.IsLattice E (B ⊔ I • dual (hStd E n) B) ∧
      IsUnimodular (hStd E n) (B ⊔ I • dual (hStd E n) B) := by
  set D := dual (hStd E n) B with hD
  have hND : N ≤ D := by
    have := dual_anti hBN
    rwa [show dual (hStd E n) N = N from hN] at this
  have hJD : ∀ p ∈ J, ∀ u ∈ D, p • u ∈ N := by
    intro p hp u hu
    rw [← show dual (hStd E n) N = N from hN, mem_dual]
    intro y hy
    have e : hStd E n y (p • u) = hStd E n (cO E p • y) u := by
      rw [hStd_osmul_left, cO_cO]
    rw [e]
    exact (mem_dual B u).1 hu _ (hIN (Submodule.smul_mem_smul (hJI p hp) hy))
  have hDD : dual (hStd E n) D = B := dual_dual hB
  have hID : I • D ≤ D := Submodule.smul_le.2 fun r _ u hu => D.smul_mem r hu
  refine ⟨lattice_between hB (dual_lattice hB) le_sup_left (sup_le (hBN.trans hND) hID), ?_⟩
  change dual (hStd E n) (B ⊔ I • D) = B ⊔ I • D
  apply le_antisymm
  · intro y hy
    obtain ⟨hy1, hy2⟩ := (mem_dual_sup _ _ y).1 hy
    rw [mem_dual_smul, hDD] at hy2
    obtain ⟨e, he, e', he', hee⟩ := hcop
    have : y = e' • y + e • y := by rw [← add_smul, add_comm e' e, hee, one_smul]
    rw [this]
    refine Submodule.add_mem_sup ?_ (Submodule.smul_mem_smul he hy1)
    have := hy2 (cO E e') (hJI e' he')
    rwa [cO_cO] at this
  · refine sup_le ?_ (Submodule.smul_le.2 ?_)
    · intro y hy
      rw [mem_dual_sup, mem_dual_smul, hDD]
      exact ⟨hND (hBN hy), fun p _ => B.smul_mem _ hy⟩
    · intro p' hp' u hu
      rw [mem_dual_sup, mem_dual_smul, hDD]
      refine ⟨D.smul_mem _ hu, fun p hp => ?_⟩
      rw [smul_comm]
      exact hIN (Submodule.smul_mem_smul hp' (hJD _ (hIJ p hp) u hu))

end Glue

section Moves2

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

def conjPrime₂ (P : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 E) where
  asIdeal := P.asIdeal.comap (cO E)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    intro h
    have h1 : cO E p ∈ P.asIdeal.comap (cO E) := by
      rw [Ideal.mem_comap, cO_cO]; exact hp
    rw [h, Ideal.mem_bot] at h1
    apply hp0
    rw [← cO_cO p, h1, map_zero]

theorem mem_conjP (P : HeightOneSpectrum (𝓞 E)) (r : 𝓞 E) :
    r ∈ (conjPrime₂ P).asIdeal ↔ cO E r ∈ P.asIdeal := Iff.rfl

theorem conjIdeal_asIdeal (P : HeightOneSpectrum (𝓞 E)) :
    conjIdeal (K := E) P.asIdeal = (conjPrime₂ P).asIdeal := conjIdeal_eq P.asIdeal

theorem exists_mem_notMem {P Q : HeightOneSpectrum (𝓞 E)} (h : P ≠ Q) :
    ∃ s ∈ P.asIdeal, s ∉ Q.asIdeal := by
  by_contra hc
  push_neg at hc
  apply h
  exact HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top hc)

theorem exists_coprime {P Q : HeightOneSpectrum (𝓞 E)} (h : P ≠ Q) :
    ∃ e ∈ P.asIdeal, ∃ e' ∈ Q.asIdeal, e + e' = 1 := by
  have hne : P.asIdeal ≠ Q.asIdeal := fun e => h (HeightOneSpectrum.ext e)
  have h1 : P.asIdeal ⊔ Q.asIdeal = ⊤ := Ideal.IsMaximal.coprime_of_ne P.isMaximal Q.isMaximal hne
  have h2 : (1 : 𝓞 E) ∈ P.asIdeal ⊔ Q.asIdeal := by
    rw [h1]
    exact Submodule.mem_top
  obtain ⟨e, he, e', he', hsum⟩ := Submodule.mem_sup.mp h2
  exact ⟨e, he, e', he', hsum⟩

def SameAt (Q : HeightOneSpectrum (𝓞 E)) (N N' : Submodule (𝓞 E) (Sp E n)) : Prop :=
  ∃ a ∉ Q.asIdeal, ∃ a' ∉ Q.asIdeal, (∀ x ∈ N', a • x ∈ N) ∧ ∀ x ∈ N, a' • x ∈ N'

theorem localization_le_of_smul_mem {Q : HeightOneSpectrum (𝓞 E)} {M N : Submodule (𝓞 E) (Sp E n)} {a : 𝓞 E}
    (ha : a ∉ Q.asIdeal) (h : ∀ x ∈ M, a • x ∈ N) : localization₂ Q.asIdeal M ≤ localization₂ Q.asIdeal N := by
  intro x hx
  obtain ⟨s, hs, hsx⟩ := (show ∃ s ∈ Q.asIdeal.primeCompl, s • x ∈ M from hx)
  show ∃ s ∈ Q.asIdeal.primeCompl, s • x ∈ N
  refine ⟨a * s, Q.asIdeal.primeCompl.mul_mem (Ideal.mem_primeCompl_iff.mpr ha) hs, ?_⟩
  rw [mul_smul]
  exact h _ hsx

theorem SameAt.localization_eq {Q : HeightOneSpectrum (𝓞 E)} {N N' : Submodule (𝓞 E) (Sp E n)}
    (h : SameAt Q N N') : localization₂ Q.asIdeal N' = localization₂ Q.asIdeal N := by
  obtain ⟨a, ha, a', ha', h1, h2⟩ := h
  exact le_antisymm (localization_le_of_smul_mem ha h1) (localization_le_of_smul_mem ha' h2)

theorem mem_smul_of_loc {Q : HeightOneSpectrum (𝓞 E)} {M : Submodule (𝓞 E) (Sp E n)} {x : Sp E n}
    (hx : x ∈ M) {s : 𝓞 E} (hs : s ∉ Q.asIdeal) (h : s • x ∈ Q.asIdeal • M) : x ∈ Q.asIdeal • M := by
  obtain ⟨t, q, hq, hst⟩ := Q.isMaximal.exists_inv hs
  have hx' : x = t • (s • x) + q • x := by
    rw [← mul_smul, ← add_smul, hst, one_smul]
  rw [hx']
  exact Submodule.add_mem _ (Submodule.smul_mem _ t h) (Submodule.smul_mem_smul hq hx)

theorem lattice_of_smul {N B D : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsLattice E N)
    (hD : Submodule.IsLattice E D) (hBD : B ≤ D) {p : 𝓞 E} (hp : p ≠ 0) (h : ∀ x ∈ N, p • x ∈ B) :
    Submodule.IsLattice E B := by
  refine ⟨Submodule.FG.of_le hD.fg hBD, ?_⟩
  rw [eq_top_iff, ← hN.span_eq_top, Submodule.span_le]
  intro x hx
  have hp' : algebraMap (𝓞 E) E p ≠ 0 := by
    rwa [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
  have : x = (algebraMap (𝓞 E) E p)⁻¹ • (p • x) := by
    rw [← algebraMap_smul E p x, smul_smul, inv_mul_cancel₀ hp', one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (h x hx))

theorem conj_smul_dual_mem {I : Ideal (𝓞 E)} {N B : Submodule (𝓞 E) (Sp E n)}
    (hN : IsUnimodular (hStd E n) N) (hIN : I • N ≤ B) {p : 𝓞 E} (hp : cO E p ∈ I) {u : Sp E n}
    (hu : u ∈ dual (hStd E n) B) : p • u ∈ N := by
  have hN' : dual (hStd E n) N = N := hN
  rw [← hN', mem_dual_lemma_2]
  intro x hx
  have e : hStd E n x (p • u) = hStd E n (cO E p • x) u := by
    rw [hStd_osmul_left, cO_cO]
  rw [e]
  exact (mem_dual_lemma_2 B u).mp hu _ (hIN (Submodule.smul_mem_smul hp hx))

def Deco.repl (d : Deco E n ST SG) (P : ST) (N' : Submodule (𝓞 E) (Sp E n))
    (f' : Sp E n → 𝓞 E ⧸ P.1.asIdeal) : Deco E n ST SG where
  N := N'
  f := open Classical in Function.update d.f P f'
  be := d.be

theorem Deco.Ok.f_zero {d : Deco E n ST SG} (hd : d.Ok) (P : ST) : d.f P 0 = 0 := by
  have h0 := hd.f_smul P 0 0 (Submodule.zero_mem _)
  simpa using h0

theorem Deco.Ok.repl {d : Deco E n ST SG} (hd : d.Ok) (P : ST) {N' : Submodule (𝓞 E) (Sp E n)}
    {f' : Sp E n → 𝓞 E ⧸ P.1.asIdeal} (hlat : Submodule.IsLattice E N')
    (huni : IsUnimodular (hStd E n) N') (hST : ∀ Q : ST, Q ≠ P → SameAt Q.1 d.N N')
    (hSG : ∀ w : SG, SameAt w.1 d.N N')
    (f_add : ∀ x ∈ localization₂ P.1.asIdeal N', ∀ y ∈ localization₂ P.1.asIdeal N', f' (x + y) = f' x + f' y)
    (f_smul : ∀ (a : 𝓞 E), ∀ x ∈ localization₂ P.1.asIdeal N',
      f' (a • x) = Ideal.Quotient.mk P.1.asIdeal a * f' x)
    (f_off : ∀ x, x ∉ localization₂ P.1.asIdeal N' → f' x = 0) (f_ne : ∃ x ∈ N', f' x ≠ 0) :
    (d.repl P N' f').Ok := by
  have hfne : ∀ Q : ST, Q ≠ P → (d.repl P N' f').f Q = d.f Q := fun Q hQ => by
    simp [Deco.repl, hQ]
  have hfP : (d.repl P N' f').f P = f' := by
    simp [Deco.repl]
  have hloc : ∀ Q : ST, Q ≠ P → localization₂ Q.1.asIdeal N' = localization₂ Q.1.asIdeal d.N := fun Q hQ =>
    (hST Q hQ).localization_eq
  refine ⟨hlat, huni, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Q x hx y hy
    by_cases hQ : Q = P
    · subst hQ
      rw [hfP]
      exact f_add x hx y hy
    · have hx' : x ∈ localization₂ Q.1.asIdeal d.N := by rw [← hloc Q hQ]; exact hx
      have hy' : y ∈ localization₂ Q.1.asIdeal d.N := by rw [← hloc Q hQ]; exact hy
      rw [hfne Q hQ]
      exact hd.f_add Q x hx' y hy'
  · intro Q c x hx
    by_cases hQ : Q = P
    · subst hQ
      rw [hfP]
      exact f_smul c x hx
    · have hx' : x ∈ localization₂ Q.1.asIdeal d.N := by rw [← hloc Q hQ]; exact hx
      rw [hfne Q hQ]
      exact hd.f_smul Q c x hx'
  · intro Q x hx
    by_cases hQ : Q = P
    · subst hQ
      rw [hfP]
      exact f_off x hx
    · rw [hfne Q hQ]
      refine hd.f_off Q x fun hx' => hx ?_
      show x ∈ localization₂ Q.1.asIdeal N'
      rw [hloc Q hQ]
      exact hx'
  · intro Q
    by_cases hQ : Q = P
    · subst hQ
      rw [hfP]
      exact f_ne
    · obtain ⟨a, ha, a', ha', h1, h2⟩ := hST Q hQ
      obtain ⟨x, hx, hfx⟩ := hd.f_ne Q
      refine ⟨a' • x, h2 x hx, ?_⟩
      rw [hfne Q hQ, hd.f_smul Q a' x (mem_localized_of_mem _ _ hx)]
      exact mul_ne_zero (fun h0 => ha' (Ideal.Quotient.eq_zero_iff_mem.mp h0)) hfx
  · intro w x hx y hy
    have hl := (hSG w).localization_eq
    have hx' : x ∈ localization₂ w.1.asIdeal d.N := by rw [← hl]; exact hx
    have hy' : y ∈ localization₂ w.1.asIdeal d.N := by rw [← hl]; exact hy
    exact hd.be_add w x hx' y hy'
  · intro w c x hx
    have hl := (hSG w).localization_eq
    have hx' : x ∈ localization₂ w.1.asIdeal d.N := by rw [← hl]; exact hx
    exact hd.be_smul w c x hx'
  · intro w x hx
    have hl := (hSG w).localization_eq
    refine hd.be_off w x fun hx' => hx ?_
    show x ∈ localization₂ w.1.asIdeal N'
    rw [hl]
    exact hx'
  · intro w c
    obtain ⟨a, ha, a', ha', h1, h2⟩ := hSG w
    haveI := w.1.isMaximal
    letI := Ideal.Quotient.field w.1.asIdeal
    have hne : Ideal.Quotient.mk w.1.asIdeal a' ≠ 0 := fun h0 =>
      ha' (Ideal.Quotient.eq_zero_iff_mem.mp h0)
    obtain ⟨x, hx, hbx⟩ := hd.be_surj w ((Ideal.Quotient.mk w.1.asIdeal a')⁻¹ • c)
    refine ⟨a' • x, h2 x hx, ?_⟩
    show d.be w (a' • x) = c
    rw [hd.be_smul w a' x (mem_localized_of_mem _ _ hx), hbx, smul_smul, mul_inv_cancel₀ hne, one_smul]
  · intro w x hx hbx
    obtain ⟨a, ha, a', ha', h1, h2⟩ := hSG w
    have hl := (hSG w).localization_eq
    have hxl : x ∈ localization₂ w.1.asIdeal d.N := by rw [← hl]; exact mem_localized_of_mem _ _ hx
    have hb : d.be w (a • x) = 0 := by
      have hbx' : d.be w x = 0 := hbx
      rw [hd.be_smul w a x hxl, hbx', smul_zero]
    have hax : a • x ∈ w.1.asIdeal • d.N := hd.be_ker w _ (h1 x hx) hb
    have key : (a' * a) • x ∈ w.1.asIdeal • N' := by
      rw [mul_smul]
      refine Submodule.smul_induction_on hax ?_ ?_
      · intro p hp y hy
        rw [smul_comm]
        exact Submodule.smul_mem_smul hp (h2 y hy)
      · intro u v hu hv
        rw [smul_add]
        exact Submodule.add_mem _ hu hv
    exact mem_smul_of_loc hx (fun hm => (w.1.isPrime.mem_or_mem hm).elim ha' ha) key

theorem Deco.Ok.mem_kerAt {d : Deco E n ST SG} (hd : d.Ok) (P : ST) (x : Sp E n) :
    x ∈ d.kerAt P ↔ x ∈ d.N ∧ d.f P x = 0 := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact hy
    | zero => exact ⟨Submodule.zero_mem _, hd.f_zero P⟩
    | add y z _ _ hy hz =>
      refine ⟨Submodule.add_mem _ hy.1 hz.1, ?_⟩
      rw [hd.f_add P y (mem_localized_of_mem P.1 d.N hy.1) z (mem_localized_of_mem P.1 d.N hz.1), hy.2, hz.2, add_zero]
    | smul a y _ hy =>
      refine ⟨Submodule.smul_mem _ a hy.1, ?_⟩
      rw [hd.f_smul P a y (mem_localized_of_mem P.1 d.N hy.1), hy.2, mul_zero]
  · intro hx
    exact Submodule.subset_span hx

structure MoveHyp (ST SG : Finset (HeightOneSpectrum (𝓞 E))) (P : ST) : Prop where
  ne : conjPrime₂ P.1 ≠ P.1
  st : ∀ Q : ST, Q.1 ≠ conjPrime₂ P.1
  sg : ∀ w : SG, w.1 ≠ P.1 ∧ w.1 ≠ conjPrime₂ P.1

theorem Deco.Ok.dnN_spec {d : Deco E n ST SG} (hd : d.Ok) (P : ST) (hne : conjPrime₂ P.1 ≠ P.1) :
    Submodule.IsLattice E (d.dnN P) ∧ IsUnimodular (hStd E n) (d.dnN P) ∧
      (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P.1 → Q ≠ conjPrime₂ P.1 → SameAt Q d.N (d.dnN P)) ∧
      localization₂ P.1.asIdeal (d.dnN P) = localization₂ P.1.asIdeal (d.kerAt P) := by
  have hBN : d.kerAt P ≤ d.N := fun x hx => ((hd.mem_kerAt P x).1 hx).1
  have hIN : P.1.asIdeal • d.N ≤ d.kerAt P := by
    rw [Submodule.smul_le]
    intro r hr y hy
    rw [hd.mem_kerAt]
    refine ⟨Submodule.smul_mem _ r hy, ?_⟩
    rw [hd.f_smul P r y (le_locP _ _ hy), Ideal.Quotient.eq_zero_iff_mem.2 hr, zero_mul]
  obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.1.ne_bot
  have hB : Submodule.IsLattice E (d.kerAt P) :=
    lattice_of_smul hd.lat hd.lat hBN hp0 fun x hx => hIN (Submodule.smul_mem_smul hp hx)
  obtain ⟨e, he, e', he', hee⟩ := exists_coprime hne.symm
  obtain ⟨h1, h2⟩ := glue_unimodular (I := P.1.asIdeal) (J := (conjPrime₂ P.1).asIdeal)
    (fun p hp => by rw [mem_conjP, cO_cO]; exact hp) (fun p hp => hp) ⟨e, he, e', he', hee⟩
    hd.uni hB hBN hIN
  have hbar : ∀ a ∈ (conjPrime₂ P.1).asIdeal, ∀ x ∈ d.dnN P, a • x ∈ d.kerAt P := by
    intro a ha x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [smul_add]
    refine Submodule.add_mem _ (Submodule.smul_mem _ a hy) ?_
    refine Submodule.smul_induction_on hz (fun r hr u hu => ?_) (fun u v hu hv => ?_)
    · rw [smul_comm]
      exact hIN (Submodule.smul_mem_smul hr (conj_smul_dual_mem hd.uni hIN ha hu))
    · rw [smul_add]
      exact Submodule.add_mem _ hu hv
  refine ⟨h1, h2, ?_, ?_⟩
  · intro Q hQ hQ'
    obtain ⟨a, ha, haQ⟩ := exists_mem_notMem (Ne.symm hQ')
    obtain ⟨a', ha', haQ'⟩ := exists_mem_notMem (Ne.symm hQ)
    exact ⟨a, haQ, a', haQ', fun x hx => hBN (hbar a ha x hx), fun x hx =>
      (le_sup_left : d.kerAt P ≤ d.dnN P) (hIN (Submodule.smul_mem_smul ha' hx))⟩
  · obtain ⟨a, ha, haP⟩ := exists_mem_notMem hne
    exact le_antisymm (localization_le_of_smul_mem haP (hbar a ha))
      (localization_le_of_smul_mem (one_notMem P.1) fun x hx => by
        rw [one_smul]; exact (le_sup_left : d.kerAt P ≤ d.dnN P) hx)

theorem Deco.Ok.dn {d : Deco E n ST SG} (hd : d.Ok) (P : ST) (hP : MoveHyp ST SG P)
    {f' : Sp E n → 𝓞 E ⧸ P.1.asIdeal}
    (f_add : ∀ x ∈ localization₂ P.1.asIdeal (d.dnN P), ∀ y ∈ localization₂ P.1.asIdeal (d.dnN P),
      f' (x + y) = f' x + f' y)
    (f_smul : ∀ (a : 𝓞 E), ∀ x ∈ localization₂ P.1.asIdeal (d.dnN P),
      f' (a • x) = Ideal.Quotient.mk P.1.asIdeal a * f' x)
    (f_off : ∀ x, x ∉ localization₂ P.1.asIdeal (d.dnN P) → f' x = 0) (f_ne : ∃ x ∈ d.dnN P, f' x ≠ 0) :
    (d.dn P f').Ok := by
  have hs := hd.dnN_spec P hP.ne
  exact hd.repl P hs.1 hs.2.1 (fun Q hQ => hs.2.2.1 Q.1 (fun h => hQ (Subtype.ext h)) (hP.st Q))
    (fun w => hs.2.2.1 w.1 (hP.sg w).1 (hP.sg w).2) f_add f_smul f_off f_ne

end Moves2

section Up

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem smul_upA_mem {P : Ideal (𝓞 E)} {N : Submodule (𝓞 E) (Sp E n)} {x : Sp E n} (hx : x ∈ N)
    {p : 𝓞 E} (hp : p ∈ P) {z : Sp E n} (hz : z ∈ upA P N x) : p • z ∈ N := by
  unfold upA at hz
  obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.mp hz
  rw [smul_add]
  refine Submodule.add_mem _ (Submodule.smul_mem _ p hy) ?_
  clear hz
  induction hw using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨a, ha, rfl⟩ := hv
    obtain ⟨r, hr⟩ := (neighbourConstruct_mem_inv.mp ha) p hp
    have e : p • a • x = r • x := by
      rw [← algebraMap_smul E r x, hr, ← algebraMap_smul E p (a • x), smul_smul]
    rw [e]
    exact Submodule.smul_mem _ r hx
  | zero =>
    rw [smul_zero]
    exact Submodule.zero_mem _
  | add v v' _ _ hv hv' =>
    rw [smul_add]
    exact Submodule.add_mem _ hv hv'
  | smul c v _ hv =>
    rw [smul_comm]
    exact Submodule.smul_mem _ c hv

theorem upN_spec {N : Submodule (𝓞 E) (Sp E n)} (hlat : Submodule.IsLattice E N)
    (huni : IsUnimodular (hStd E n) N) (P : HeightOneSpectrum (𝓞 E)) (hne : conjPrime₂ P ≠ P)
    {x : Sp E n} (hx : x ∈ N) :
    Submodule.IsLattice E (upN P.asIdeal N x) ∧ IsUnimodular (hStd E n) (upN P.asIdeal N x) ∧
      (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → Q ≠ conjPrime₂ P → SameAt Q N (upN P.asIdeal N x)) ∧
      upN P.asIdeal N x ≤ upA P.asIdeal N x ∧
      (conjPrime₂ P).asIdeal • upA P.asIdeal N x ≤ upN P.asIdeal N x := by
  set A := upA P.asIdeal N x with hA
  have hNA : N ≤ A := le_sup_left
  have hdN : dual (hStd E n) N = N := huni
  obtain ⟨pb, hpb, hpb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (conjPrime₂ P).ne_bot
  have hPN : Submodule.IsLattice E ((conjPrime₂ P).asIdeal • N) :=
    lattice_of_smul hlat hlat (Submodule.smul_le.2 fun r _ y hy => N.smul_mem r hy) hpb0
      fun y hy => Submodule.smul_mem_smul hpb hy
  have hAle : A ≤ dual (hStd E n) ((conjPrime₂ P).asIdeal • N) := by
    intro z hz
    rw [mem_dual_smul, hdN]
    intro p hp
    exact smul_upA_mem hx ((mem_conjP P p).1 hp) hz
  have hAlat : Submodule.IsLattice E A := lattice_between hlat (dual_lattice hPN) hNA hAle
  have hBN : dual (hStd E n) A ≤ N := by
    have := dual_anti hNA
    rwa [hdN] at this
  have hIN : (conjPrime₂ P).asIdeal • N ≤ dual (hStd E n) A := by
    have := dual_anti hAle
    rwa [dual_dual hPN] at this
  obtain ⟨e, he, e', he', hee⟩ := exists_coprime hne
  obtain ⟨h1, h2⟩ := glue_unimodular (I := (conjPrime₂ P).asIdeal) (J := P.asIdeal)
    (fun p hp => hp) (fun p hp => by rw [mem_conjP, cO_cO]; exact hp) ⟨e, he, e', he', hee⟩
    huni (dual_lattice hAlat) hBN hIN
  rw [dual_dual hAlat] at h1 h2
  have hN' : upN P.asIdeal N x = dual (hStd E n) A ⊔ (conjPrime₂ P).asIdeal • A := by
    rw [upN, conjIdeal_asIdeal]
  rw [hN']
  have hle : dual (hStd E n) A ⊔ (conjPrime₂ P).asIdeal • A ≤ A :=
    sup_le (hBN.trans hNA) (Submodule.smul_le.2 fun r _ y hy => A.smul_mem r hy)
  refine ⟨h1, h2, ?_, hle, le_sup_right⟩
  intro Q hQ hQ'
  obtain ⟨a, ha, haQ⟩ := exists_mem_notMem (Ne.symm hQ)
  obtain ⟨a', ha', haQ'⟩ := exists_mem_notMem (Ne.symm hQ')
  exact ⟨a, haQ, a', haQ', fun y hy => smul_upA_mem hx ha (hle hy), fun y hy =>
    (le_sup_right : (conjPrime₂ P).asIdeal • A ≤ _) (Submodule.smul_mem_smul ha' (hNA hy))⟩

theorem exists_inv_unif (P : HeightOneSpectrum (𝓞 E)) {q : 𝓞 E} (hq : q ∈ P.asIdeal)
    (hq2 : q ∉ P.asIdeal ^ 2) :
    ∃ a ∈ invIdeal (K := E) P.asIdeal, ∃ r : 𝓞 E, r ∉ P.asIdeal ∧
      algebraMap (𝓞 E) E q * a = algebraMap (𝓞 E) E r := by
  by_contra H
  push Not at H
  apply hq2
  have hkey := neighbourConstruct_key (K := E) (V := E) P.asIdeal P.ne_bot
    (Submodule.map (Algebra.linearMap (𝓞 E) E) P.asIdeal) (algebraMap (𝓞 E) E q) (by
      intro a ha
      obtain ⟨r, hr⟩ := neighbourConstruct_mem_inv.1 ha q hq
      have hr' := H a ha r
      refine ⟨r, ?_, ?_⟩
      · by_contra hrP
        exact hr' hrP hr.symm
      · rw [Algebra.linearMap_apply, hr, smul_eq_mul, mul_comm])
  rw [← Submodule.map_smul''] at hkey
  obtain ⟨r, hr, hrq⟩ := hkey
  have : r = q := by
    apply RingOfIntegers.ext
    exact hrq
  rw [← this, sq]
  simpa using hr

theorem Deco.Ok.up {d : Deco E n ST SG} (hd : d.Ok) (P : ST) (hP : MoveHyp ST SG P) {q : 𝓞 E}
    (hq : q ∈ P.1.asIdeal) (hq2 : q ∉ P.1.asIdeal ^ 2) {x : Sp E n} (hx : x ∈ d.N)
    (hfx : d.f P x = 1) : (d.up P q x).Ok := by
  classical
  obtain ⟨h1, h2, h3, h4, h5⟩ := upN_spec hd.lat hd.uni P.1 hP.ne hx
  have hloc : ∀ y ∈ localization₂ P.1.asIdeal (upN P.1.asIdeal d.N x), q • y ∈ d.at P.1 := by
    intro y hy
    obtain ⟨s, hs, hsy⟩ := (mem_locP _ _ _).1 hy
    refine (mem_locP _ _ _).2 ⟨s, hs, ?_⟩
    rw [smul_comm]
    exact smul_upA_mem hx hq (h4 hsy)
  refine hd.repl P h1 h2 (fun Q hQ => h3 Q.1 (fun h => hQ (Subtype.ext h)) (hP.st Q))
    (fun w => h3 w.1 (hP.sg w).1 (hP.sg w).2) ?_ ?_ ?_ ?_
  · intro y hy z hz
    rw [if_pos hy, if_pos hz, if_pos (Submodule.add_mem _ hy hz), smul_add]
    exact hd.f_add P _ (hloc y hy) _ (hloc z hz)
  · intro a y hy
    rw [if_pos hy, if_pos (Submodule.smul_mem _ a hy), smul_comm]
    exact hd.f_smul P a _ (hloc y hy)
  · intro y hy
    rw [if_neg hy]
  · obtain ⟨a, ha, r, hr, har⟩ := exists_inv_unif P.1 hq hq2
    obtain ⟨e, he, e', he', hee⟩ := exists_coprime hP.ne
    have hax : a • x ∈ upA P.1.asIdeal d.N x :=
      (le_sup_right : _ ≤ upA P.1.asIdeal d.N x) (Submodule.subset_span ⟨a, ha, rfl⟩)
    have hy : e • (a • x) ∈ upN P.1.asIdeal d.N x := h5 (Submodule.smul_mem_smul he hax)
    refine ⟨e • (a • x), hy, ?_⟩
    rw [if_pos (le_locP _ _ hy)]
    have e1 : q • e • a • x = (e * r) • x := by
      rw [smul_comm q e, ← algebraMap_smul E q (a • x), smul_smul, har, algebraMap_smul, mul_smul]
    rw [e1, hd.f_smul P _ x (le_locP _ _ hx), hfx, mul_one]
    apply mk_ne_zero
    intro hm
    rcases P.1.isPrime.mem_or_mem hm with h | h
    · apply one_notMem P.1
      rw [← hee]
      exact Ideal.add_mem _ h he'
    · exact hr h

theorem DecoSet.up_val (d : DecoSet E n ST SG) (P : ST) (hP : MoveHyp ST SG P) {q : 𝓞 E}
    (hq : q ∈ P.1.asIdeal) (hq2 : q ∉ P.1.asIdeal ^ 2) {x : Sp E n} (hx : x ∈ d.1.N)
    (hfx : d.1.f P x = 1) : (d.up P q x).1 = d.1.up P q x := by
  have hok : (d.1.up P q x).Ok := Deco.Ok.up d.2 P hP hq hq2 hx hfx
  unfold DecoSet.up
  rw [dif_pos hok]

theorem DecoSet.upSet_nonempty (d : DecoSet E n ST SG) (P : ST) (hP : MoveHyp ST SG P) {q : 𝓞 E}
    (hq : q ∈ P.1.asIdeal) (hq2 : q ∉ P.1.asIdeal ^ 2) : (d.upSet P q).Nonempty := by
  obtain ⟨x, hx, hfx⟩ := d.2.f_ne P
  haveI := P.1.isMaximal
  letI := Ideal.Quotient.field P.1.asIdeal
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective ((d.1.f P x)⁻¹)
  have hx1 : d.1.f P (c • x) = 1 := by
    rw [d.2.f_smul P c x (mem_localized_of_mem _ _ hx), hc, inv_mul_cancel₀ hfx]
  exact ⟨⟨d.1.up P q (c • x), d.2.up P hP hq hq2 (Submodule.smul_mem _ c hx) hx1⟩,
    c • x, Submodule.smul_mem _ c hx, hx1, rfl⟩

end Up

section Til

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

@[simp] theorem incl_castSucc (y : Sp E n) (i : Fin n) : incl E n y i.castSucc = y i := by
  simp [incl]

@[simp] theorem incl_last (y : Sp E n) : incl E n y (Fin.last n) = 0 := by
  simp [incl]

@[simp] theorem initL_apply (x : Sp E (n + 1)) (i : Fin n) : initL E n x i = x i.castSucc := rfl

@[simp] theorem initL_incl (y : Sp E n) : initL E n (incl E n y) = y := by
  funext i
  rw [initL_apply, incl_castSucc]

@[simp] theorem eLast_last : eLast E n (Fin.last n) = 1 := by
  simp [eLast]

@[simp] theorem eLast_castSucc (i : Fin n) : eLast E n i.castSucc = 0 := by
  simp [eLast, Pi.single_apply, Fin.castSucc_ne_last]

@[simp] theorem initL_eLast : initL E n (eLast E n) = 0 := by
  funext i
  simp

theorem sp_decomp (x : Sp E (n + 1)) :
    x = incl E n (initL E n x) + x (Fin.last n) • eLast E n := by
  funext i
  induction i using Fin.lastCases <;> simp

theorem initL_osmul (s : 𝓞 E) (x : Sp E (n + 1)) : initL E n (s • x) = s • initL E n x := rfl

theorem hStd_succ (x y : Sp E (n + 1)) : hStd E (n + 1) x y =
    hStd E n (initL E n x) (initL E n y) + star (x (Fin.last n)) * y (Fin.last n) := by
  simp [hStd, Fin.sum_univ_castSucc]

theorem hermStd_lastVector_apply (pi : 𝓞 E) (x : Sp E (n + 1)) :
    hStd E (n + 1) (z0 E n (algebraMap (𝓞 E) E pi)) x =
      algebraMap (𝓞 E) E (cO E pi) * x (Fin.last n) := by
  simp [hStd, z0, Fin.sum_univ_castSucc, algebraMap_cO, Algebra.smul_def]

theorem mem_tilN (N : Submodule (𝓞 E) (Sp E n)) (x : Sp E (n + 1)) :
    x ∈ tilN N ↔ initL E n x ∈ N ∧ ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = x (Fin.last n) := by
  unfold tilN
  constructor
  · intro hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨y', hy', rfl⟩ := Submodule.mem_map.mp hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
    refine ⟨?_, c, ?_⟩
    · simpa [initL_osmul] using hy'
    · simp [Algebra.smul_def]
  · rintro ⟨hN, r, hr⟩
    rw [sp_decomp x, ← hr, algebraMap_smul]
    exact Submodule.add_mem_sup (Submodule.mem_map_of_mem hN)
      (Submodule.mem_span_singleton.mpr ⟨r, rfl⟩)

theorem mem_localization_tilN (Q : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n))
    (x : Sp E (n + 1)) :
    x ∈ localization₂ Q.asIdeal (tilN N) ↔ initL E n x ∈ localization₂ Q.asIdeal N ∧ IntAt Q (x (Fin.last n)) := by
  constructor
  · intro hx
    obtain ⟨s, hs, hsx⟩ := (show ∃ s ∈ Q.asIdeal.primeCompl, s • x ∈ tilN N from hx)
    rw [mem_tilN] at hsx
    obtain ⟨h1, r, hr⟩ := hsx
    refine ⟨show ∃ s ∈ Q.asIdeal.primeCompl, s • initL E n x ∈ N from ⟨s, hs, by rwa [← initL_osmul]⟩,
      r, s, Ideal.mem_primeCompl_iff.mp hs, ?_⟩
    rw [hr, Pi.smul_apply, Algebra.smul_def]
  · rintro ⟨hx1, r, t, ht, hr⟩
    obtain ⟨s, hs, hsx⟩ := (show ∃ s ∈ Q.asIdeal.primeCompl, s • initL E n x ∈ N from hx1)
    show ∃ s ∈ Q.asIdeal.primeCompl, s • x ∈ tilN N
    refine ⟨s * t, Q.asIdeal.primeCompl.mul_mem hs (Ideal.mem_primeCompl_iff.mpr ht), ?_⟩
    rw [mem_tilN]
    refine ⟨?_, s * r, ?_⟩
    · rw [initL_osmul, mul_comm, mul_smul]
      exact Submodule.smul_mem _ t hsx
    · rw [Pi.smul_apply, Algebra.smul_def, map_mul, map_mul, mul_assoc, hr]

theorem tilN_lattice {N : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsLattice E N) :
    Submodule.IsLattice E (tilN N) := by
  refine ⟨(hN.fg.map _).sup (Submodule.fg_span_singleton _), ?_⟩
  rw [eq_top_iff]
  intro x _
  rw [sp_decomp x]
  refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (Submodule.subset_span
    ((le_sup_right : _ ≤ tilN N) (Submodule.mem_span_singleton_self _))))
  have h1 : Submodule.map (incl E n) ⊤ ≤ Submodule.span E (tilN N : Set (Sp E (n + 1))) := by
    rw [← hN.span_eq_top, Submodule.map_span]
    apply Submodule.span_mono
    rintro _ ⟨y, hy, rfl⟩
    exact (le_sup_left : _ ≤ tilN N) (Submodule.mem_map_of_mem hy)
  exact h1 (Submodule.mem_map_of_mem Submodule.mem_top)

theorem tilN_unimodular {N : Submodule (𝓞 E) (Sp E n)} (hN : IsUnimodular (hStd E n) N) :
    IsUnimodular (hStd E (n + 1)) (tilN N) := by
  have hN' : dual (hStd E n) N = N := hN
  show dual (hStd E (n + 1)) (tilN N) = tilN N
  ext y
  rw [mem_dual_lemma_2 (tilN N) y, mem_tilN N y]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [← hN', mem_dual_lemma_2]
      intro u hu
      have h1 := h (incl E n u) ((mem_tilN N _).mpr
        ⟨by rwa [initL_incl], 0, by rw [incl_last, map_zero]⟩)
      rwa [hStd_succ, initL_incl, incl_last, star_zero, zero_mul, add_zero] at h1
    · have h1 := h (eLast E n) ((mem_tilN N _).mpr
        ⟨by rw [initL_eLast]; exact Submodule.zero_mem _, 1, by rw [eLast_last, map_one]⟩)
      rw [hStd_succ, initL_eLast, map_zero, LinearMap.zero_apply, zero_add, eLast_last, star_one,
        one_mul] at h1
      exact Submodule.mem_one.mp h1
  · rintro ⟨h1, r, hr⟩ x hx
    rw [← hN'] at h1
    obtain ⟨hx1, c, hc⟩ := (mem_tilN N x).mp hx
    rw [hStd_succ, ← hr, ← hc]
    refine Submodule.add_mem _ ((mem_dual_lemma_2 N _).mp h1 _ hx1) ?_
    exact Submodule.mem_one.mpr ⟨cO E c * r, by rw [map_mul, algebraMap_cO]⟩

theorem IntAt.div_of_notMem {Q : HeightOneSpectrum (𝓞 E)} {a : E} (ha : IntAt Q a) {pi : 𝓞 E}
    (hpi : pi ∉ Q.asIdeal) : IntAt Q (a / algebraMap (𝓞 E) E pi) := by
  obtain ⟨r, s, hs, h⟩ := ha
  have hpi0 : algebraMap (𝓞 E) E pi ≠ 0 := by
    intro h0
    apply hpi
    have hz : pi = 0 := by
      apply IsFractionRing.injective (𝓞 E) E
      rw [h0, map_zero]
    rw [hz]
    exact Submodule.zero_mem _
  refine ⟨r, s * pi, ?_, ?_⟩
  · exact fun hmem => (Q.isPrime.mem_or_mem hmem).elim hs hpi
  · have e : algebraMap (𝓞 E) E pi * (a / algebraMap (𝓞 E) E pi) = a := by
      field_simp
    rw [map_mul, mul_assoc, e, h]

theorem Deco.Ok.til {d : Deco E n ∅ SG} (hd : d.Ok) {pi : 𝓞 E}
    (hT : ∀ P : ST, cO E pi ∉ P.1.asIdeal) (hG : ∀ w : SG, pi ∉ w.1.asIdeal) :
    (d.til (ST := ST) pi).Ok where
  lat := tilN_lattice hd.lat
  uni := tilN_unimodular hd.uni
  f_add P x hx y hy := by
    replace hx : x ∈ localization₂ P.1.asIdeal (tilN d.N) := hx
    replace hy : y ∈ localization₂ P.1.asIdeal (tilN d.N) := hy
    simp only [Deco.til]
    rw [if_pos hx, if_pos hy, if_pos (Submodule.add_mem _ hx hy), map_add]
    rw [hermStd_lastVector_apply, hermStd_lastVector_apply]
    exact reduction_add ((IntAt.coe _ _).mul ((mem_localization_tilN _ _ _).1 hx).2)
      ((IntAt.coe _ _).mul ((mem_localization_tilN _ _ _).1 hy).2)
  f_smul P a x hx := by
    replace hx : x ∈ localization₂ P.1.asIdeal (tilN d.N) := hx
    simp only [Deco.til]
    rw [if_pos hx, if_pos (Submodule.smul_mem _ a hx), LinearMap.map_smul_of_tower, hermStd_lastVector_apply]
    exact redP_osmul a ((IntAt.coe _ _).mul ((mem_localization_tilN _ _ _).1 hx).2)
  f_off P x hx := by
    replace hx : x ∉ localization₂ P.1.asIdeal (tilN d.N) := hx
    simp only [Deco.til]
    rw [if_neg hx]
  f_ne P := by
    have h1 : eLast E n ∈ tilN d.N := (mem_tilN _ _).2 ⟨by simp, 1, by simp⟩
    refine ⟨_, h1, ?_⟩
    simp only [Deco.til]
    rw [if_pos (le_locP _ _ h1), hermStd_lastVector_apply, eLast_last, mul_one, reduction_coe]
    exact mk_ne_zero (hT P)
  be_add w x hx y hy := by
    replace hx : x ∈ localization₂ w.1.asIdeal (tilN d.N) := hx
    replace hy : y ∈ localization₂ w.1.asIdeal (tilN d.N) := hy
    simp only [Deco.til]
    rw [if_pos hx, if_pos hy, if_pos (Submodule.add_mem _ hx hy)]
    obtain ⟨hx1, hx2⟩ := (mem_localization_tilN _ _ _).1 hx
    obtain ⟨hy1, hy2⟩ := (mem_localization_tilN _ _ _).1 hy
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last, Pi.add_apply, add_div]
      exact reduction_add (hx2.div_of_notMem (hG w)) (hy2.div_of_notMem (hG w))
    · simp only [Fin.snoc_castSucc, Pi.add_apply, map_add]
      rw [hd.be_add w _ hx1 _ hy1]
      rfl
  be_smul w a x hx := by
    replace hx : x ∈ localization₂ w.1.asIdeal (tilN d.N) := hx
    simp only [Deco.til]
    rw [if_pos hx, if_pos (Submodule.smul_mem _ a hx)]
    obtain ⟨hx1, hx2⟩ := (mem_localization_tilN _ _ _).1 hx
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last, Pi.smul_apply, smul_eq_mul]
      rw [smul_div_assoc]
      exact redP_osmul a (hx2.div_of_notMem (hG w))
    · simp only [Fin.snoc_castSucc, Pi.smul_apply, smul_eq_mul]
      rw [initL_osmul, hd.be_smul w a _ hx1]
      rfl
  be_off w x hx := by
    replace hx : x ∉ localization₂ w.1.asIdeal (tilN d.N) := hx
    simp only [Deco.til]
    rw [if_neg hx]
  be_surj w c := by
    obtain ⟨y, hy, hc⟩ := hd.be_surj w (fun i => c i.castSucc)
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (c (Fin.last n))
    have h0 : algebraMap (𝓞 E) E pi ≠ 0 := by
      rw [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
      rintro rfl
      exact hG w (Ideal.zero_mem _)
    have h1 : incl E n y + (r * pi) • eLast E n ∈ tilN d.N :=
      (mem_tilN _ _).2 ⟨by rw [map_add, initL_osmul]; simpa using hy, r * pi, by
        simp [Algebra.smul_def]⟩
    refine ⟨_, h1, ?_⟩
    simp only [Deco.til]
    rw [if_pos (le_locP _ _ h1)]
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last]
      have e : (incl E n y + (r * pi) • eLast E n) (Fin.last n) / algebraMap (𝓞 E) E pi =
          algebraMap (𝓞 E) E r := by
        simp [Algebra.smul_def, h0]
      rw [e, reduction_coe, hr]
    · simp only [Fin.snoc_castSucc]
      have e : initL E n (incl E n y + (r * pi) • eLast E n) = y := by
        rw [map_add, initL_osmul]; simp
      rw [e, hc]
  be_ker w x hx h0 := by
    replace hx : x ∈ tilN d.N := hx
    simp only [Deco.til] at h0
    rw [if_pos (le_locP _ _ hx)] at h0
    obtain ⟨h1, r, hr⟩ := (mem_tilN _ _).1 hx
    have hpi0 : algebraMap (𝓞 E) E pi ≠ 0 := by
      rw [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
      rintro rfl
      exact hG w (Ideal.zero_mem _)
    have e1 : d.be w (initL E n x) = 0 := by
      funext j
      have := congrFun h0 j.castSucc
      simpa only [Fin.snoc_castSucc, Pi.zero_apply] using this
    have e2 : redP w.1 (x (Fin.last n) / algebraMap (𝓞 E) E pi) = 0 := by
      have := congrFun h0 (Fin.last n)
      simpa only [Fin.snoc_last, Pi.zero_apply] using this
    have hr' : r ∈ w.1.asIdeal := by
      have := reduction_spec w.1 (a := x (Fin.last n) / algebraMap (𝓞 E) E pi) (r := r) (hG w) (by
        rw [hr]; field_simp)
      rw [e2, mul_zero] at this
      exact Ideal.Quotient.eq_zero_iff_mem.1 this.symm
    have h2 := hd.be_ker w _ h1 e1
    change x ∈ w.1.asIdeal • tilN d.N
    rw [sp_decomp x, ← hr, algebraMap_smul]
    refine Submodule.add_mem _ ?_ (Submodule.smul_mem_smul hr'
      ((le_sup_right : _ ≤ tilN d.N) (Submodule.mem_span_singleton_self _)))
    have h3 : (w.1.asIdeal • d.N).map ((incl E n).restrictScalars (𝓞 E)) ≤
        w.1.asIdeal • tilN d.N := by
      rw [Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_sup_left
    exact h3 (Submodule.mem_map_of_mem h2)

theorem DecoSet.til_val (d : DecoSet E n ∅ SG) {pi : 𝓞 E}
    (hT : ∀ P : ST, cO E pi ∉ P.1.asIdeal) (hG : ∀ w : SG, pi ∉ w.1.asIdeal) :
    (DecoSet.til (ST := ST) pi d).1 = d.1.til pi := by
  have hok : (d.1.til (ST := ST) pi).Ok := Deco.Ok.til d.2 hT hG
  unfold DecoSet.til
  rw [dif_pos hok]

end Til

section LLsh

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem Deco.Ok.mem_L {d : Deco E n ST SG} (hd : d.Ok) (x : Sp E n) :
    x ∈ d.L ↔ x ∈ d.N ∧ ∀ P : ST, d.f P x = 0 := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact hy
    | zero => exact ⟨Submodule.zero_mem _, fun P => hd.f_zero P⟩
    | add y z _ _ hy hz =>
      refine ⟨Submodule.add_mem _ hy.1 hz.1, fun P => ?_⟩
      rw [hd.f_add P y (mem_localized_of_mem P.1 d.N hy.1) z (mem_localized_of_mem P.1 d.N hz.1), hy.2 P, hz.2 P,
        add_zero]
    | smul a y _ hy =>
      refine ⟨Submodule.smul_mem _ a hy.1, fun P => ?_⟩
      rw [hd.f_smul P a y (mem_localized_of_mem P.1 d.N hy.1), hy.2 P, mul_zero]
  · intro hx
    exact Submodule.subset_span hx

theorem Deco.Ok.L_le_N {d : Deco E n ST SG} (hd : d.Ok) : d.L ≤ d.N := Submodule.span_le.mpr fun x hx => hx.1

theorem Deco.Ok.N_le_Lsh {d : Deco E n ST SG} (hd : d.Ok) : d.N ≤ d.Lsh := by
  have hu : dual (hStd E n) d.N = d.N := hd.uni
  have h1 : dual (hStd E n) d.N ≤ dual (hStd E n) d.L := dual_anti hd.L_le_N
  rw [hu] at h1
  exact h1

theorem Deco.Ok.L_le_Lsh {d : Deco E n ST SG} (hd : d.Ok) : d.L ≤ d.Lsh := le_trans hd.L_le_N hd.N_le_Lsh

theorem Deco.Ok.smul_N_mem_L {d : Deco E n ST SG} (hd : d.Ok) {a : 𝓞 E}
    (ha : ∀ P : ST, a ∈ P.1.asIdeal) {x : Sp E n} (hx : x ∈ d.N) : a • x ∈ d.L := by
  refine Submodule.subset_span ⟨Submodule.smul_mem _ a hx, fun P => ?_⟩
  rw [hd.f_smul P a x (mem_localized_of_mem P.1 d.N hx), Ideal.Quotient.eq_zero_iff_mem.mpr (ha P), zero_mul]

theorem Deco.Ok.smul_Lsh_mem_N {d : Deco E n ST SG} (hd : d.Ok) {a : 𝓞 E}
    (ha : ∀ P : ST, cO E a ∈ P.1.asIdeal) {x : Sp E n} (hx : x ∈ d.Lsh) : a • x ∈ d.N := by
  have hu : dual (hStd E n) d.N = d.N := hd.uni
  rw [← hu, mem_dual_lemma_2]
  intro y hy
  have e : hStd E n y (a • x) = hStd E n (cO E a • y) x := by
    rw [hStd_osmul_left, cO_cO]
  rw [e]
  exact (mem_dual_lemma_2 d.L x).mp hx _ (hd.smul_N_mem_L ha hy)

theorem Deco.Ok.smul_Lsh_mem_L {d : Deco E n ST SG} (hd : d.Ok) {pi : 𝓞 E}
    (ha : ∀ P : ST, pi ∈ P.1.asIdeal) {x : Sp E n} (hx : x ∈ d.Lsh) :
    (pi * cO E pi) • x ∈ d.L := by
  rw [mul_smul]
  refine hd.smul_N_mem_L ha ?_
  exact hd.smul_Lsh_mem_N (fun P => by rw [cO_cO]; exact ha P) hx

theorem Deco.Ok.L_lattice {d : Deco E n ST SG} (hd : d.Ok) : Submodule.IsLattice E d.L := by
  classical
  have hex : ∀ P : ST, ∃ p ∈ P.1.asIdeal, p ≠ 0 := fun P =>
    Submodule.exists_mem_ne_zero_of_ne_bot P.1.ne_bot
  choose g hg hg0 using hex
  refine lattice_of_smul hd.lat hd.lat hd.L_le_N (p := ∏ P, g P) ?_ ?_
  · exact Finset.prod_ne_zero_iff.mpr fun P _ => hg0 P
  · intro x hx
    refine hd.smul_N_mem_L (fun P => ?_) hx
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ P)]
    exact Ideal.mul_mem_right _ _ (hg P)

theorem Deco.Ok.Lsh_lattice {d : Deco E n ST SG} (hd : d.Ok) : Submodule.IsLattice E d.Lsh := dual_lattice hd.L_lattice

theorem Deco.Ok.mem_locP_L {d : Deco E n ST SG} (hd : d.Ok) (P : ST) (x : Sp E n) :
    x ∈ localization₂ P.1.asIdeal d.L ↔ x ∈ d.at P.1 ∧ d.f P x = 0 := by
  classical
  constructor
  · intro hx
    obtain ⟨s, hs, hsx⟩ := (show ∃ s ∈ P.1.asIdeal.primeCompl, s • x ∈ d.L from hx)
    have hxN : x ∈ d.at P.1 :=
      show ∃ s ∈ P.1.asIdeal.primeCompl, s • x ∈ d.N from ⟨s, hs, hd.L_le_N hsx⟩
    refine ⟨hxN, ?_⟩
    have h0 : d.f P (s • x) = 0 := ((hd.mem_L _).mp hsx).2 P
    rw [hd.f_smul P s x hxN] at h0
    exact (mul_eq_zero.mp h0).resolve_left
      (fun h => Ideal.mem_primeCompl_iff.mp hs (Ideal.Quotient.eq_zero_iff_mem.mp h))
  · rintro ⟨hxN, hfx⟩
    obtain ⟨s, hs, hsx⟩ := (show ∃ s ∈ P.1.asIdeal.primeCompl, s • x ∈ d.N from hxN)
    have hu : ∀ Q : ST, ∃ s : 𝓞 E, (Q ≠ P → s ∈ Q.1.asIdeal) ∧ s ∉ P.1.asIdeal := by
      intro Q
      by_cases hQ : Q = P
      · exact ⟨1, fun h => absurd hQ h, fun h1 => P.1.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)⟩
      · obtain ⟨s, hs1, hs2⟩ := exists_mem_notMem (P := Q.1) (Q := P.1) (fun h => hQ (Subtype.ext h))
        exact ⟨s, fun _ => hs1, hs2⟩
    choose u huQ huP using hu
    have htP : (∏ Q, u Q) ∉ P.1.asIdeal := by
      have hm : (∏ Q, u Q) ∈ P.1.asIdeal.primeCompl :=
        Submonoid.prod_mem _ fun Q _ => Ideal.mem_primeCompl_iff.mpr (huP Q)
      exact Ideal.mem_primeCompl_iff.mp hm
    have htQ : ∀ Q : ST, Q ≠ P → (∏ Q', u Q') ∈ Q.1.asIdeal := fun Q hQ => by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ Q)]
      exact Ideal.mul_mem_right _ _ (huQ Q hQ)
    show ∃ s ∈ P.1.asIdeal.primeCompl, s • x ∈ d.L
    refine ⟨(∏ Q, u Q) * s, P.1.asIdeal.primeCompl.mul_mem (Ideal.mem_primeCompl_iff.mpr htP) hs, ?_⟩
    rw [mul_smul]
    refine (hd.mem_L _).mpr ⟨Submodule.smul_mem _ _ hsx, fun Q => ?_⟩
    rw [hd.f_smul Q _ _ (mem_localized_of_mem _ _ hsx)]
    by_cases hQ : Q = P
    · subst hQ
      rw [hd.f_smul Q s x hxN, hfx, mul_zero, mul_zero]
    · rw [Ideal.Quotient.eq_zero_iff_mem.mpr (htQ Q hQ), zero_mul]

end LLsh

section Equivariance

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem gmap_sup (g : Sp E n ≃ₗ[E] Sp E n) (A B : Submodule (𝓞 E) (Sp E n)) :
    gmap g (A ⊔ B) = gmap g A ⊔ gmap g B := Submodule.map_sup A B _

theorem gmap_smul (g : Sp E n ≃ₗ[E] Sp E n) (I : Ideal (𝓞 E)) (A : Submodule (𝓞 E) (Sp E n)) :
    gmap g (I • A) = I • gmap g A := by
  simp only [gmap, Submodule.map_smul'']

theorem upA_gmap (g : Sp E n ≃ₗ[E] Sp E n) (P : Ideal (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n))
    (x : Sp E n) : upA P (gmap g N) (g x) = gmap g (upA P N x) := by
  unfold upA
  rw [gmap_sup]
  congr 1
  unfold gmap
  rw [Submodule.map_span]
  congr 1
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_image, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a • x, ⟨a, ha, rfl⟩, map_smul g a x⟩
  · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, map_smul g a x⟩

private theorem dual_gmap_lemma_3 {g : Sp E n ≃ₗ[E] Sp E n} (hg : g ∈ UF E n)
    (L : Submodule (𝓞 E) (Sp E n)) :
    dual (hStd E n) (gmap g L) = gmap g (dual (hStd E n) L) := by
  have hg' : ∀ x y, hStd E n (g x) (g y) = hStd E n x y := hg
  ext y
  rw [mem_dual_lemma_2]
  simp only [gmap, Submodule.mem_map, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
  constructor
  · intro h
    refine ⟨g.symm y, ?_, by simp⟩
    rw [mem_dual_lemma_2]
    intro x hx
    have h1 := h (g x) ⟨x, hx, rfl⟩
    rwa [← hg' x (g.symm y), LinearEquiv.apply_symm_apply]
  · rintro ⟨z, hz, rfl⟩ x ⟨x', hx', rfl⟩
    rw [hg']
    exact (mem_dual_lemma_2 L z).mp hz x' hx'

theorem upN_gmap {g : Sp E n ≃ₗ[E] Sp E n} (hg : g ∈ UF E n) (P : Ideal (𝓞 E))
    (N : Submodule (𝓞 E) (Sp E n)) (x : Sp E n) :
    upN P (gmap g N) (g x) = gmap g (upN P N x) := by
  unfold upN
  rw [upA_gmap, dual_gmap_lemma_3 hg, gmap_sup, gmap_smul]

private theorem localization_gmap_eq_gmap_localization (g : Sp E n ≃ₗ[E] Sp E n) (Q : HeightOneSpectrum (𝓞 E))
    (L : Submodule (𝓞 E) (Sp E n)) :
    localization₂ Q.asIdeal (gmap g L) = gmap g (localization₂ Q.asIdeal L) := by
  have hsm : ∀ (s : 𝓞 E) (v : Sp E n), g.symm (s • v) = s • g.symm v := fun s v =>
    ((g.symm : Sp E n →ₗ[E] Sp E n).restrictScalars (𝓞 E)).map_smul s v
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, hsx⟩ := (show ∃ s ∈ Q.asIdeal.primeCompl, s • x ∈ gmap g L from hx)
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp hsx
    refine Submodule.mem_map.mpr ⟨g.symm x,
      show ∃ s ∈ Q.asIdeal.primeCompl, s • g.symm x ∈ L from ⟨s, hs, ?_⟩, by simp⟩
    rw [← hsm, ← hyx]
    simpa using hy
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨s, hs, hsy⟩ := (show ∃ s ∈ Q.asIdeal.primeCompl, s • y ∈ L from hy)
    show ∃ s ∈ Q.asIdeal.primeCompl, s • ((g : Sp E n →ₗ[E] Sp E n).restrictScalars (𝓞 E)) y ∈ gmap g L
    exact ⟨s, hs, Submodule.mem_map.mpr ⟨s • y, hsy,
      ((g : Sp E n →ₗ[E] Sp E n).restrictScalars (𝓞 E)).map_smul s y⟩⟩

private theorem up_f_lemma_5 (d : Deco E n ST SG) (P : ST) (q : 𝓞 E) (x y : Sp E n) :
    (d.up P q x).f P y = open Classical in
      if y ∈ localization₂ P.1.asIdeal (upN P.1.asIdeal d.N x) then d.f P (q • y) else 0 := by
  simp [Deco.up]

private theorem up_f_ne_lemma_6 (d : Deco E n ST SG) (P : ST) (q : 𝓞 E) (x : Sp E n) {Q : ST}
    (hQ : Q ≠ P) : (d.up P q x).f Q = d.f Q := by
  simp [Deco.up, hQ]

theorem Deco.up_act (d : Deco E n ST SG) {g : Sp E n ≃ₗ[E] Sp E n} (hg : g ∈ UF E n)
    (h : GLG E n SG) (P : ST) (q : 𝓞 E) (x : Sp E n) :
    (d.act g h).up P q (g x) = (d.up P q x).act g h := by
  have hsm : ∀ (s : 𝓞 E) (v : Sp E n), g.symm (s • v) = s • g.symm v := fun s v =>
    ((g.symm : Sp E n →ₗ[E] Sp E n).restrictScalars (𝓞 E)).map_smul s v
  have mg : ∀ (L : Submodule (𝓞 E) (Sp E n)) (v : Sp E n), v ∈ gmap g L ↔ g.symm v ∈ L := by
    intro L v
    simp only [gmap, Submodule.mem_map, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
    · intro hv
      exact ⟨g.symm v, hv, by simp⟩
  have e1 : (d.act g h).N = gmap g d.N := rfl
  apply Deco.ext
  · show upN P.1.asIdeal (gmap g d.N) (g x) = gmap g (upN P.1.asIdeal d.N x)
    exact upN_gmap hg _ _ _
  · funext Q y
    by_cases hQ : Q = P
    · subst hQ
      change _ = (d.up Q q x).f Q (g.symm y)
      rw [up_f_lemma_5, up_f_lemma_5]
      have hm' : y ∈ localization₂ Q.1.asIdeal (upN Q.1.asIdeal (d.act g h).N (g x)) ↔
          g.symm y ∈ localization₂ Q.1.asIdeal (upN Q.1.asIdeal d.N x) := by
        rw [e1, upN_gmap hg, localization_gmap_eq_gmap_localization, mg]
      by_cases hm : g.symm y ∈ localization₂ Q.1.asIdeal (upN Q.1.asIdeal d.N x)
      · rw [if_pos (hm'.mpr hm), if_pos hm]
        change d.f Q (g.symm (q • y)) = _
        rw [hsm]
      · rw [if_neg (fun h' => hm (hm'.mp h')), if_neg hm]
    · change _ = (d.up P q x).f Q (g.symm y)
      rw [up_f_ne_lemma_6 _ _ _ _ hQ, up_f_ne_lemma_6 _ _ _ _ hQ]
      rfl
  · rfl

theorem Deco.IsUp.act {P : ST} {q : 𝓞 E} {d d' : Deco E n ST SG} (hdd : Deco.IsUp P q d d')
    {g : Sp E n ≃ₗ[E] Sp E n} (hg : g ∈ UF E n) (h : GLG E n SG) :
    Deco.IsUp P q (d.act g h) (d'.act g h) := by
  obtain ⟨x, hx, hfx, rfl⟩ := hdd
  refine ⟨g x, Submodule.mem_map.mpr ⟨x, hx, rfl⟩, ?_, (Deco.up_act d hg h P q x).symm⟩
  show d.f P (g.symm (g x)) = 1
  rw [LinearEquiv.symm_apply_apply, hfx]

theorem Deco.kerAt_act (d : Deco E n ST SG) (g : Sp E n ≃ₗ[E] Sp E n) (h : GLG E n SG) (P : ST) :
    (d.act g h).kerAt P = gmap g (d.kerAt P) := by
  show Submodule.span (𝓞 E) {x | x ∈ gmap g d.N ∧ d.f P (g.symm x) = 0} =
    (Submodule.span (𝓞 E) {x | x ∈ d.N ∧ d.f P x = 0}).map
      ((g : Sp E n →ₗ[E] Sp E n).restrictScalars (𝓞 E))
  rw [Submodule.map_span]
  congr 1
  ext x
  simp only [gmap, Submodule.mem_map, Set.mem_setOf_eq, Set.mem_image,
    LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hf⟩
    exact ⟨y, ⟨hy, by simpa using hf⟩, rfl⟩
  · rintro ⟨y, ⟨hy, hf⟩, rfl⟩
    exact ⟨⟨y, hy, rfl⟩, by simpa using hf⟩

theorem Deco.dnN_act (d : Deco E n ST SG) {g : Sp E n ≃ₗ[E] Sp E n} (hg : g ∈ UF E n)
    (h : GLG E n SG) (P : ST) : (d.act g h).dnN P = gmap g (d.dnN P) := by
  unfold Deco.dnN
  rw [Deco.kerAt_act, gmap_sup, gmap_smul, dual_gmap_lemma_3 hg]

theorem Deco.dn_act (d : Deco E n ST SG) {g : Sp E n ≃ₗ[E] Sp E n} (hg : g ∈ UF E n)
    (h : GLG E n SG) (P : ST) (f' : Sp E n → 𝓞 E ⧸ P.1.asIdeal) :
    (d.act g h).dn P (fun y => f' (g.symm y)) = (d.dn P f').act g h := by
  apply Deco.ext
  · exact Deco.dnN_act d hg h P
  · funext Q y
    by_cases hQ : Q = P
    · subst hQ
      simp [Deco.dn, Deco.act]
    · simp [Deco.dn, Deco.act, hQ]
  · rfl

theorem Deco.IsDn.act {P : ST} {q : 𝓞 E} {d d' : Deco E n ST SG} (hdd : Deco.IsDn P q d d')
    {g : Sp E n ≃ₗ[E] Sp E n} (hg : g ∈ UF E n) (h : GLG E n SG) :
    Deco.IsDn P q (d.act g h) (d'.act g h) := by
  have hsm : ∀ (s : 𝓞 E) (v : Sp E n), g.symm (s • v) = s • g.symm v := fun s v =>
    ((g.symm : Sp E n →ₗ[E] Sp E n).restrictScalars (𝓞 E)).map_smul s v
  obtain ⟨h1, h2⟩ := hdd
  refine ⟨?_, ?_⟩
  · conv_lhs => rw [h1]
    exact (Deco.dn_act d hg h P (d'.f P)).symm
  · intro e he hfe
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp he
    have hfe' : d.f P y = 1 := by
      have h3 := hfe
      simp only [Deco.act, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply] at h3
      exact h3
    show d'.f P (g.symm (q • g y)) = 1
    rw [hsm, LinearEquiv.symm_apply_apply]
    exact h2 y hy hfe'

theorem DecoSet.smul_mem_upSet (a : UF E n × GLG E n SG) (P : ST) (q : 𝓞 E)
    (d d' : DecoSet E n ST SG) : a • d' ∈ (a • d).upSet P q ↔ d' ∈ d.upSet P q := by
  have key : ∀ (b : UF E n × GLG E n SG) (e e' : DecoSet E n ST SG), Deco.IsUp P q e.1 e'.1 →
      Deco.IsUp P q (b • e).1 (b • e').1 := by
    intro b e e' h
    rw [DecoSet.smul_val, DecoSet.smul_val]
    exact h.act b.1.2 b.2
  constructor
  · intro h
    have h2 := key a⁻¹ _ _ h
    rwa [inv_smul_smul, inv_smul_smul] at h2
  · intro h
    exact key a _ _ h

theorem DecoSet.smul_mem_dnSet (a : UF E n × GLG E n SG) (P : ST) (q : 𝓞 E)
    (d d' : DecoSet E n ST SG) : a • d' ∈ (a • d).dnSet P q ↔ d' ∈ d.dnSet P q := by
  have key : ∀ (b : UF E n × GLG E n SG) (e e' : DecoSet E n ST SG), Deco.IsDn P q e.1 e'.1 →
      Deco.IsDn P q (b • e).1 (b • e').1 := by
    intro b e e' h
    rw [DecoSet.smul_val, DecoSet.smul_val]
    exact h.act b.1.2 b.2
  constructor
  · intro h
    have h2 := key a⁻¹ _ _ h
    rwa [inv_smul_smul, inv_smul_smul] at h2
  · intro h
    exact key a _ _ h

theorem DecoSet.dnSet_finite (d : DecoSet E n ST SG) (P : ST) (hne : conjPrime₂ P.1 ≠ P.1) (q : 𝓞 E) :
    (d.dnSet P q).Finite := by
  have hs := d.2.dnN_spec P hne
  refine (DecoSet.finite_fibre (d.1.dnN P) hs.1.fg).subset ?_
  rintro d' ⟨h1, _⟩
  show d'.1.N = d.1.dnN P
  rw [h1]
  rfl

end Equivariance

section Adjoint

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem unimodular_eq_of_le {M N : Submodule (𝓞 E) (Sp E n)} (hM : IsUnimodular (hStd E n) M)
    (hN : IsUnimodular (hStd E n) N) (h : M ≤ N) : M = N := by
  have hM' : dual (hStd E n) M = M := hM
  have hN' : dual (hStd E n) N = N := hN
  have h2 := dual_anti (E := E) (n := n) h
  rw [hM', hN'] at h2
  exact le_antisymm h h2

theorem Deco.up_f (d : Deco E n ST SG) (P : ST) (q : 𝓞 E) (x y : Sp E n) :
    (d.up P q x).f P y = open Classical in
      if y ∈ localization₂ P.1.asIdeal (upN P.1.asIdeal d.N x) then d.f P (q • y) else 0 := by
  simp [Deco.up]

theorem Deco.up_f_of_mem (d : Deco E n ST SG) (P : ST) (q : 𝓞 E) (x : Sp E n) {y : Sp E n}
    (hy : y ∈ upN P.1.asIdeal d.N x) : (d.up P q x).f P y = d.f P (q • y) := by
  rw [Deco.up_f, if_pos (mem_localized_of_mem _ _ hy)]

theorem Deco.up_f_ne (d : Deco E n ST SG) (P : ST) (q : 𝓞 E) (x : Sp E n) {Q : ST} (hQ : Q ≠ P) :
    (d.up P q x).f Q = d.f Q := by
  simp [Deco.up, hQ]

theorem inv_integral (P : HeightOneSpectrum (𝓞 E)) {q : 𝓞 E} (hq : q ∈ P.asIdeal)
    (hq2 : q ∉ P.asIdeal ^ 2) {b : E} (hb : b ∈ invIdeal (K := E) P.asIdeal) {β : 𝓞 E}
    (hβ : β ∈ P.asIdeal) (h : algebraMap (𝓞 E) E q * b = algebraMap (𝓞 E) E β) :
    ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = b := by
  obtain ⟨a, ha, r, hr, har⟩ := exists_inv_unif P hq hq2
  obtain ⟨t, p, hp, e⟩ := P.isMaximal.exists_inv hr
  obtain ⟨c1, hc1⟩ := neighbourConstruct_mem_inv.1 hb p hp
  obtain ⟨c2, hc2⟩ := neighbourConstruct_mem_inv.1 ha β hβ
  refine ⟨t * c2 + c1, ?_⟩
  have e' : algebraMap (𝓞 E) E t * algebraMap (𝓞 E) E r + algebraMap (𝓞 E) E p = 1 := by
    rw [← map_mul, ← map_add, e, map_one]
  rw [map_add, map_mul, hc1, hc2, ← h]
  calc algebraMap (𝓞 E) E t * (algebraMap (𝓞 E) E q * b * a) + algebraMap (𝓞 E) E p * b
      = (algebraMap (𝓞 E) E t * (algebraMap (𝓞 E) E q * a) + algebraMap (𝓞 E) E p) * b := by ring
    _ = b := by rw [har, e', one_mul]

theorem Deco.Ok.smul_mem_kerAt {d : Deco E n ST SG} (hd : d.Ok) (P : ST) {p : 𝓞 E}
    (hp : p ∈ P.1.asIdeal) {y : Sp E n} (hy : y ∈ d.N) : p • y ∈ d.kerAt P := by
  refine Submodule.subset_span ⟨Submodule.smul_mem _ p hy, ?_⟩
  rw [hd.f_smul P p y (mem_localized_of_mem P.1 d.N hy), Ideal.Quotient.eq_zero_iff_mem.mpr hp, zero_mul]

theorem Deco.Ok.conj_smul_dnN_mem {d : Deco E n ST SG} (hd : d.Ok) (P : ST) {a : 𝓞 E}
    (ha : a ∈ (conjPrime₂ P.1).asIdeal) {x : Sp E n} (hx : x ∈ d.dnN P) : a • x ∈ d.kerAt P := by
  have hIN : P.1.asIdeal • d.N ≤ d.kerAt P :=
    Submodule.smul_le.2 fun r hr y hy => hd.smul_mem_kerAt P hr hy
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  rw [smul_add]
  refine Submodule.add_mem _ (Submodule.smul_mem _ a hy) ?_
  refine Submodule.smul_induction_on hz (fun r hr u hu => ?_) (fun u v hu hv => ?_)
  · rw [smul_comm]
    exact hIN (Submodule.smul_mem_smul hr (conj_smul_dual_mem hd.uni hIN ha hu))
  · rw [smul_add]
    exact Submodule.add_mem _ hu hv

theorem Deco.Ok.dnN_up {d : Deco E n ST SG} (hd : d.Ok) (P : ST) (hP : MoveHyp ST SG P) {q : 𝓞 E}
    (hq : q ∈ P.1.asIdeal) (hq2 : q ∉ P.1.asIdeal ^ 2) {x : Sp E n} (hx : x ∈ d.N)
    (hfx : d.f P x = 1) : (d.up P q x).dnN P = d.N := by
  have hd' := hd.up P hP hq hq2 hx hfx
  obtain ⟨-, -, -, h4, h5⟩ := upN_spec hd.lat hd.uni P.1 hP.ne hx
  refine unimodular_eq_of_le (hd'.dnN_spec P hP.ne).2.1 hd.uni (sup_le ?_ ?_)
  · intro y hy
    obtain ⟨hy1, hy2⟩ := (hd'.mem_kerAt P y).1 hy
    replace hy1 : y ∈ upN P.1.asIdeal d.N x := hy1
    rw [d.up_f_of_mem P q x hy1] at hy2
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 (h4 hy1)
    obtain ⟨b, hb, rfl⟩ := neighbourConstruct_mem_span.1 hv
    obtain ⟨β, hβ⟩ := neighbourConstruct_mem_inv.1 hb q hq
    have e1 : q • (b • x) = β • x := by
      rw [← algebraMap_smul E q (b • x), smul_smul, ← hβ, algebraMap_smul]
    rw [smul_add, e1, hd.f_add P _ (le_locP _ _ (d.N.smul_mem q hu)) _
      (le_locP _ _ (d.N.smul_mem β hx)), hd.f_smul P q u (le_locP _ _ hu),
      hd.f_smul P β x (le_locP _ _ hx), hfx, Ideal.Quotient.eq_zero_iff_mem.2 hq, zero_mul,
      zero_add, mul_one] at hy2
    obtain ⟨r, hr⟩ := inv_integral P.1 hq hq2 hb (Ideal.Quotient.eq_zero_iff_mem.1 hy2) hβ.symm
    rw [← hr, algebraMap_smul]
    exact Submodule.add_mem _ hu (Submodule.smul_mem _ r hx)
  · have hIN : (conjPrime₂ P.1).asIdeal • d.N ≤ (d.up P q x).kerAt P := by
      rw [Submodule.smul_le]
      intro r hr y hy
      have h1 : r • y ∈ upN P.1.asIdeal d.N x :=
        h5 (Submodule.smul_mem_smul hr ((le_sup_left : d.N ≤ upA P.1.asIdeal d.N x) hy))
      rw [hd'.mem_kerAt]
      refine ⟨h1, ?_⟩
      rw [d.up_f_of_mem P q x h1, hd.f_smul P q _ (le_locP _ _ (d.N.smul_mem r hy)),
        Ideal.Quotient.eq_zero_iff_mem.2 hq, zero_mul]
    rw [Submodule.smul_le]
    intro p hp u hu
    exact conj_smul_dual_mem hd.uni hIN (by rw [mem_conjP, cO_cO]; exact hp) hu

theorem Deco.IsUp.isDn {d d' : Deco E n ST SG} (hd : d.Ok) {P : ST} (hP : MoveHyp ST SG P)
    {q : 𝓞 E} (hq : q ∈ P.1.asIdeal) (hq2 : q ∉ P.1.asIdeal ^ 2) (h : Deco.IsUp P q d d') :
    Deco.IsDn P q d' d := by
  classical
  obtain ⟨x, hx, hfx, rfl⟩ := h
  refine ⟨?_, fun e he h1 => ?_⟩
  · ext1
    · exact (hd.dnN_up P hP hq hq2 hx hfx).symm
    · simp [Deco.dn, Deco.up]
    · rfl
  · rwa [d.up_f_of_mem P q x he] at h1

theorem Deco.IsDn.isUp {d d' : Deco E n ST SG} (hd : d.Ok) (hd' : d'.Ok) {P : ST}
    (hP : MoveHyp ST SG P) {q : 𝓞 E} (hq : q ∈ P.1.asIdeal) (hq2 : q ∉ P.1.asIdeal ^ 2)
    (h : Deco.IsDn P q d' d) : Deco.IsUp P q d d' := by
  classical
  obtain ⟨h1, h2⟩ := h
  have hN : d.N = d'.dnN P := congrArg Deco.N h1
  have hf : ∀ Q : ST, Q ≠ P → d.f Q = d'.f Q := fun Q hQ =>
    (congrFun (congrArg Deco.f h1) Q).trans (Function.update_of_ne hQ _ _)
  have hbe : d.be = d'.be := by
    have := congrArg Deco.be h1
    exact this
  have hBN : d'.kerAt P ≤ d.N := by
    rw [hN]; exact le_sup_left

  obtain ⟨e0, he0, hne⟩ := hd'.f_ne P
  have := P.1.isMaximal
  obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv hne
  obtain ⟨t0, rfl⟩ := Ideal.Quotient.mk_surjective b
  set e := t0 • e0 with hedef
  have he : e ∈ d'.N := Submodule.smul_mem _ t0 he0
  have hfe : d'.f P e = 1 := by
    rw [hd'.f_smul P t0 e0 (le_locP _ _ he0), mul_comm, hb]
  have hx : q • e ∈ d.N := hBN (hd'.smul_mem_kerAt P hq he)
  have hfx : d.f P (q • e) = 1 := h2 e he hfe
  have hup := hd.up P hP hq hq2 hx hfx
  obtain ⟨-, huni, -, h4, h5⟩ := upN_spec hd.lat hd.uni P.1 hP.ne hx

  have hdec : ∀ y ∈ d'.N, ∃ c : 𝓞 E, Ideal.Quotient.mk P.1.asIdeal c = d'.f P y ∧
      y - c • e ∈ d'.kerAt P := by
    intro y hy
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (d'.f P y)
    refine ⟨c, hc, ?_⟩
    rw [hd'.mem_kerAt]
    refine ⟨Submodule.sub_mem _ hy (Submodule.smul_mem _ c he), ?_⟩
    have e1 : y - c • e = y + (-c) • e := by rw [neg_smul, sub_eq_add_neg]
    rw [e1, hd'.f_add P y (le_locP _ _ hy) _ (le_locP _ _ (Submodule.smul_mem _ _ he)),
      hd'.f_smul P (-c) e (le_locP _ _ he), hfe, mul_one, map_neg, hc, add_neg_cancel]
  have heA : e ∈ upA P.1.asIdeal d.N (q • e) := by
    obtain ⟨a, ha, r, hr, har⟩ := exists_inv_unif P.1 hq hq2
    obtain ⟨t, p, hp, etp⟩ := P.1.isMaximal.exists_inv hr
    have e1 : e = p • e + (t • a) • (q • e) := by
      have : (t • a) • (q • e) = (t * r) • e := by
        rw [← algebraMap_smul E q e, smul_smul, smul_mul_assoc, mul_comm a, har, ← algebraMap_smul E t,
          smul_eq_mul, ← map_mul, algebraMap_smul]
      rw [this, ← add_smul, add_comm, etp, one_smul]
    have h3 : p • e + (t • a) • (q • e) ∈ upA P.1.asIdeal d.N (q • e) :=
      Submodule.add_mem_sup (hBN (hd'.smul_mem_kerAt P hp he))
        (Submodule.subset_span ⟨t • a, Submodule.smul_mem _ t ha, rfl⟩)
    rwa [← e1] at h3
  have hN'A : d'.N ≤ upA P.1.asIdeal d.N (q • e) := by
    intro y hy
    obtain ⟨c, -, hc⟩ := hdec y hy
    have : y = (y - c • e) + c • e := by abel
    rw [this]
    exact Submodule.add_mem _ ((le_sup_left : d.N ≤ upA P.1.asIdeal d.N (q • e)) (hBN hc))
      (Submodule.smul_mem _ c heA)
  have hNeq : upN P.1.asIdeal d.N (q • e) = d'.N := by
    refine unimodular_eq_of_le huni hd'.uni (sup_le ?_ ?_)
    · have := dual_anti hN'A
      rwa [show dual (hStd E n) d'.N = d'.N from hd'.uni] at this
    · rw [conjIdeal_asIdeal, Submodule.smul_le]
      intro r hr z hz
      obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hz
      obtain ⟨b, hb, rfl⟩ := neighbourConstruct_mem_span.1 hv
      obtain ⟨β, hβ⟩ := neighbourConstruct_mem_inv.1 hb q hq
      have e1 : b • (q • e) = β • e := by
        rw [← algebraMap_smul E q e, smul_smul, mul_comm, ← hβ, algebraMap_smul]
      rw [smul_add, e1]
      rw [hN] at hu
      exact Submodule.add_mem _ ((hd'.mem_kerAt P _).1 (hd'.conj_smul_dnN_mem P hr hu)).1
        (Submodule.smul_mem _ r (Submodule.smul_mem _ β he))
  refine ⟨q • e, hx, hfx, ?_⟩
  refine Deco.Ok.ext_on hd' hup hNeq.symm (fun Q y hy => ?_) (fun w y _ => ?_)
  · by_cases hQ : Q = P
    · subst hQ
      rw [d.up_f_of_mem Q q _ (hNeq.symm ▸ hy)]
      obtain ⟨c, hc1, hc2⟩ := hdec y hy
      have e1 : q • y = q • (y - c • e) + c • (q • e) := by
        rw [smul_comm c q e, ← smul_add]
        congr 1
        abel
      rw [e1, hd.f_add Q _ (le_locP _ _ (d.N.smul_mem q (hBN hc2))) _
        (le_locP _ _ (d.N.smul_mem c hx)), hd.f_smul Q q _ (le_locP _ _ (hBN hc2)),
        hd.f_smul Q c _ (le_locP _ _ hx), hfx, Ideal.Quotient.eq_zero_iff_mem.2 hq, zero_mul,
        zero_add, mul_one, hc1]
    · rw [d.up_f_ne P q _ hQ, hf Q hQ]
  · change d'.be w y = d.be w y
    rw [hbe]

theorem DecoSet.mem_upSet_iff_mem_dnSet {P : ST} (hP : MoveHyp ST SG P) {q : 𝓞 E}
    (hq : q ∈ P.1.asIdeal) (hq2 : q ∉ P.1.asIdeal ^ 2) (d d' : DecoSet E n ST SG) :
    d' ∈ d.upSet P q ↔ d ∈ d'.dnSet P q := ⟨fun h => Deco.IsUp.isDn d.2 hP hq hq2 h, fun h => Deco.IsDn.isUp d.2 d'.2 hP hq hq2 h⟩

end Adjoint

section UpIndex

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem inv_smul_mem {P : Ideal (𝓞 E)} {N : Submodule (𝓞 E) (Sp E n)} {a : E}
    (ha : a ∈ invIdeal (K := E) P) {z : Sp E n} (hz : z ∈ P • N) : a • z ∈ N := by
  have ha' := neighbourConstruct_mem_inv.mp ha
  refine Submodule.smul_induction_on hz ?_ ?_
  · intro p hp y hy
    obtain ⟨r, hr⟩ := ha' p hp
    have e : a • p • y = r • y := by
      rw [← algebraMap_smul E r y, hr, ← algebraMap_smul E p y, smul_smul, mul_comm]
    rw [e]
    exact Submodule.smul_mem _ r hy
  · intro y y' hy hy'
    rw [smul_add]
    exact Submodule.add_mem _ hy hy'

theorem upA_le_of_sub {P : Ideal (𝓞 E)} {N : Submodule (𝓞 E) (Sp E n)} {x x' : Sp E n}
    (h : x - x' ∈ P • N) : upA P N x ≤ upA P N x' := by
  unfold upA
  apply sup_le le_sup_left
  rw [Submodule.span_le]
  rintro z ⟨a, ha, rfl⟩
  have e : a • x = a • x' + a • (x - x') := by
    rw [smul_sub]
    abel
  rw [e]
  exact Submodule.add_mem _ (Submodule.mem_sup_right (Submodule.subset_span ⟨a, ha, rfl⟩))
    (Submodule.mem_sup_left (inv_smul_mem ha h))

theorem upA_congr {P : Ideal (𝓞 E)} {N : Submodule (𝓞 E) (Sp E n)} {x x' : Sp E n}
    (h : x - x' ∈ P • N) : upA P N x = upA P N x' := le_antisymm (upA_le_of_sub h) (upA_le_of_sub (by rw [← neg_sub]; exact Submodule.neg_mem _ h))

theorem Deco.up_congr (d : Deco E n ST SG) (P : ST) (q : 𝓞 E) {x x' : Sp E n}
    (h : x - x' ∈ P.1.asIdeal • d.N) : d.up P q x = d.up P q x' := by
  have h' : upN P.1.asIdeal d.N x = upN P.1.asIdeal d.N x' := by
    unfold upN
    rw [upA_congr h]
  unfold Deco.up
  rw [h']

theorem Deco.Ok.up_inj {d : Deco E n ST SG} (hd : d.Ok) (P : ST) (hP : MoveHyp ST SG P) {q : 𝓞 E}
    (hq : q ∈ P.1.asIdeal) (hq2 : q ∉ P.1.asIdeal ^ 2) {x x' : Sp E n} (hx : x ∈ d.N)
    (hx' : x' ∈ d.N) (hfx : d.f P x = 1) (hfx' : d.f P x' = 1) (h : d.up P q x = d.up P q x') :
    x - x' ∈ P.1.asIdeal • d.N := by
  have hN : upN P.1.asIdeal d.N x = upN P.1.asIdeal d.N x' := congrArg Deco.N h
  obtain ⟨-, -, -, h4, -⟩ := upN_spec hd.lat hd.uni P.1 hP.ne hx'
  obtain ⟨-, -, -, -, h5⟩ := upN_spec hd.lat hd.uni P.1 hP.ne hx
  obtain ⟨a, ha, r, hr, har⟩ := exists_inv_unif P.1 hq hq2
  obtain ⟨e, he, e', he', hee⟩ := exists_coprime hP.ne
  have heP : e ∉ P.1.asIdeal := by
    intro h'
    apply one_notMem P.1
    rw [← hee]
    exact Ideal.add_mem _ h' he'
  have h1 : e • (a • x) ∈ upA P.1.asIdeal d.N x' := by
    apply h4
    rw [← hN]
    exact h5 (Submodule.smul_mem_smul he ((le_sup_right : _ ≤ upA P.1.asIdeal d.N x)
      (Submodule.subset_span ⟨a, ha, rfl⟩)))
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 h1
  obtain ⟨b, hb, rfl⟩ := neighbourConstruct_mem_span.1 hv
  obtain ⟨β, hβ⟩ := neighbourConstruct_mem_inv.1 hb q hq
  have e1 : q • (e • (a • x)) = (e * r) • x := by
    rw [smul_comm q e, ← algebraMap_smul E q (a • x), smul_smul, har, algebraMap_smul, mul_smul]
  have e2 : q • (b • x') = β • x' := by
    rw [← algebraMap_smul E q (b • x'), smul_smul, ← hβ, algebraMap_smul]
  have e3 : (e * r) • x = q • u + β • x' := by
    rw [← e1, ← huv, smul_add, e2]
  have e4 : Ideal.Quotient.mk P.1.asIdeal (e * r) = Ideal.Quotient.mk P.1.asIdeal β := by
    have := congrArg (d.f P) e3
    rwa [hd.f_smul P _ x (le_locP _ _ hx), hfx, mul_one,
      hd.f_add P _ (le_locP _ _ (d.N.smul_mem q hu)) _ (le_locP _ _ (d.N.smul_mem β hx')),
      hd.f_smul P q u (le_locP _ _ hu), hd.f_smul P β x' (le_locP _ _ hx'), hfx',
      Ideal.Quotient.eq_zero_iff_mem.2 hq, zero_mul, zero_add, mul_one] at this
  have e5 : β - e * r ∈ P.1.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, e4, sub_self]
  refine mem_smul_of_loc (Submodule.sub_mem _ hx hx') (s := e * r)
    (fun hm => (P.1.isPrime.mem_or_mem hm).elim heP hr) ?_
  have e6 : (e * r) • (x - x') = q • u + (β - e * r) • x' := by
    rw [smul_sub, e3, sub_smul]
    abel
  rw [e6]
  exact Submodule.add_mem _ (Submodule.smul_mem_smul hq hu) (Submodule.smul_mem_smul e5 hx')

theorem Deco.Ok.up_f_inv {d : Deco E n ST SG} (hd : d.Ok) (P : ST) (hP : MoveHyp ST SG P) {q : 𝓞 E}
    (hq : q ∈ P.1.asIdeal) (hq2 : q ∉ P.1.asIdeal ^ 2) {x : Sp E n} (hx : x ∈ d.N)
    (hfx : d.f P x = 1) : (d.up P q x).f P ((algebraMap (𝓞 E) E q)⁻¹ • x) = 1 := by
  obtain ⟨-, -, -, -, h5⟩ := upN_spec hd.lat hd.uni P.1 hP.ne hx
  obtain ⟨a, ha, r, hr, har⟩ := exists_inv_unif P.1 hq hq2
  obtain ⟨e, he, e', he', hee⟩ := exists_coprime hP.ne
  have heP : e ∉ P.1.asIdeal := by
    intro h'
    apply one_notMem P.1
    rw [← hee]
    exact Ideal.add_mem _ h' he'
  have hq0 : algebraMap (𝓞 E) E q ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at har
    apply hr
    rw [(FaithfulSMul.algebraMap_eq_zero_iff (𝓞 E) E).1 har.symm]
    exact Ideal.zero_mem _
  have hmem : (algebraMap (𝓞 E) E q)⁻¹ • x ∈ localization₂ P.1.asIdeal (upN P.1.asIdeal d.N x) := by
    refine (mem_locP _ _ _).2 ⟨e * r, fun hm => (P.1.isPrime.mem_or_mem hm).elim heP hr, ?_⟩
    have : (e * r) • ((algebraMap (𝓞 E) E q)⁻¹ • x) = e • (a • x) := by
      rw [mul_smul, ← algebraMap_smul E r, smul_smul, ← har, mul_comm (algebraMap (𝓞 E) E q) a,
        mul_assoc, mul_inv_cancel₀ hq0, mul_one]
    rw [this]
    exact h5 (Submodule.smul_mem_smul he ((le_sup_right : _ ≤ upA P.1.asIdeal d.N x)
      (Submodule.subset_span ⟨a, ha, rfl⟩)))
  rw [Deco.up_f, if_pos hmem, ← algebraMap_smul E q, smul_smul, mul_inv_cancel₀ hq0, one_smul, hfx]

theorem exists_finite_reps {N : Submodule (𝓞 E) (Sp E n)} (hN : N.FG)
    (P : HeightOneSpectrum (𝓞 E)) :
    ∃ R : Set (Sp E n), R.Finite ∧ ∀ x ∈ N, ∃ r ∈ R, x - r ∈ P.asIdeal • N := by
  classical
  obtain ⟨S, hS⟩ := hN
  refine ⟨Set.range fun φ : S → 𝓞 E ⧸ P.asIdeal => ∑ b : S, (Quotient.out (φ b) : 𝓞 E) • b.1,
    Set.finite_range _, ?_⟩
  intro x hx
  rw [← hS] at hx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_finset'.1 hx
  refine ⟨_, ⟨fun b => Ideal.Quotient.mk P.asIdeal (c b), rfl⟩, ?_⟩
  rw [← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun b _ => ?_
  rw [← sub_smul]
  refine Submodule.smul_mem_smul ?_ (hS ▸ Submodule.subset_span b.2)
  rw [← Ideal.Quotient.eq]
  exact (Quotient.out_eq' _).symm

theorem DecoSet.upSet_finite (d : DecoSet E n ST SG) (P : ST) (q : 𝓞 E) : (d.upSet P q).Finite := by
  obtain ⟨R, hR, hrep⟩ := exists_finite_reps d.2.lat.fg P.1
  have hfin : ((fun r => d.1.up P q r) '' R).Finite := hR.image _
  refine (hfin.preimage Subtype.val_injective.injOn).subset ?_
  rintro d' ⟨x, hx, _, hd'⟩
  obtain ⟨r, hr, hxr⟩ := hrep x hx
  show ∃ r, r ∈ R ∧ d.1.up P q r = d'.1
  exact ⟨r, hr, by rw [hd', Deco.up_congr d.1 P q hxr]⟩

end UpIndex

section TilL

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem Deco.Ok.til_L {d : Deco E n ∅ SG} (hd : d.Ok) {pi : 𝓞 E}
    (hT : ∀ P : ST, cO E pi ∉ P.1.asIdeal) (hG : ∀ w : SG, pi ∉ w.1.asIdeal)
    (hpi : ∀ P : ST, pi ∈ P.1.asIdeal)
    (hdvd : ∀ r : 𝓞 E, (∀ P : ST, r ∈ P.1.asIdeal) → pi ∣ r) :
    (d.til (ST := ST) pi).L = d.N.map ((incl E n).restrictScalars (𝓞 E)) ⊔
      Submodule.span (𝓞 E) {z0 E n (algebraMap (𝓞 E) E pi)} := by
  have hok := hd.til (ST := ST) hT hG
  have hf : ∀ (P : ST) (x : Sp E (n + 1)) (r : 𝓞 E), x ∈ tilN d.N →
      algebraMap (𝓞 E) E r = x (Fin.last n) →
      (d.til (ST := ST) pi).f P x = Ideal.Quotient.mk P.1.asIdeal (cO E pi * r) := by
    intro P x r hx hr
    have : (d.til (ST := ST) pi).f P x =
        redP P.1 (hStd E (n + 1) (z0 E n (algebraMap (𝓞 E) E pi)) x) := if_pos (le_locP _ _ hx)
    rw [this, hermStd_lastVector_apply, ← hr, ← map_mul, reduction_coe]
  ext x
  rw [hok.mem_L]
  constructor
  · rintro ⟨hx, h0⟩
    replace hx : x ∈ tilN d.N := hx
    obtain ⟨h1, r, hr⟩ := (mem_tilN _ _).1 hx
    obtain ⟨c, rfl⟩ := hdvd r fun P => by
      have := h0 P
      rw [hf P x r hx hr, Ideal.Quotient.eq_zero_iff_mem] at this
      exact (P.1.isPrime.mem_or_mem this).resolve_left (hT P)
    rw [sp_decomp x, ← hr]
    refine Submodule.add_mem_sup (Submodule.mem_map_of_mem h1) ?_
    have : algebraMap (𝓞 E) E (pi * c) • eLast E n = c • z0 E n (algebraMap (𝓞 E) E pi) := by
      rw [z0, ← algebraMap_smul E c, smul_smul, map_mul, mul_comm]
    rw [this]
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)
  · intro hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨y0, hy0, rfl⟩ := Submodule.mem_map.1 hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
    have hlast : algebraMap (𝓞 E) E (c * pi) =
        ((incl E n).restrictScalars (𝓞 E) y0 + c • z0 E n (algebraMap (𝓞 E) E pi)) (Fin.last n) := by
      simp [z0, Algebra.smul_def]
    have hmem : (incl E n).restrictScalars (𝓞 E) y0 + c • z0 E n (algebraMap (𝓞 E) E pi) ∈
        tilN d.N := by
      rw [mem_tilN]
      refine ⟨?_, c * pi, hlast⟩
      rw [map_add, initL_osmul]
      simpa [z0] using hy0
    refine ⟨hmem, fun P => ?_⟩
    rw [hf P _ _ hmem hlast, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (hpi P))

end TilL

section AtBase

variable {X : Fields} {Pr : Primes X}

theorem decoFin_mem_of_mem_divs {A : Type} [CommRing A] [IsDedekindDomain A] {a : A}
    {P : HeightOneSpectrum A} (h : P ∈ divs a) : a ∈ P.asIdeal := by
  unfold divs at h
  split_ifs at h with hf
  · exact (Set.Finite.mem_toFinset hf).mp h
  · simp at h

theorem conj_piT_notMem (hPr : Pr.Ok) (u : Pr.Word) (P : Pr.vT u) :
    cO X.E (Pr.piT u) ∉ P.1.asIdeal := by
  intro h
  obtain ⟨a, b, hab⟩ := hPr.piT_cop u
  have h1 : Pr.piT u ∈ P.1.asIdeal := decoFin_mem_of_mem_divs P.2
  apply P.1.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h)

theorem exists_g_mem (hPr : Pr.Ok) (w : Pr.vGs) : ∃ i, (Pr.g i : 𝓞 X.E) ∈ w.1.asIdeal := by
  classical
  have h2 : w.1 ∈ Pr.vG 0 ∨ w.1 ∈ Pr.vG 1 := by
    have h3 := w.2
    simp only [Primes.vGs, Finset.mem_union] at h3
    exact h3
  rcases h2 with h | h
  · refine ⟨0, ?_⟩
    rw [← hPr.piG_norm 0]
    exact Ideal.mul_mem_left _ _ (decoFin_mem_of_mem_divs h)
  · refine ⟨1, ?_⟩
    rw [← hPr.piG_norm 1]
    exact Ideal.mul_mem_left _ _ (decoFin_mem_of_mem_divs h)

private theorem natCast_coprime_lemma_7 {R : Type} [CommRing R] {I : Ideal R} (hI : I ≠ ⊤) {a b : ℕ}
    (hab : Nat.Coprime a b) (ha : (a : R) ∈ I) (hb : (b : R) ∈ I) : False := by
  apply hI
  rw [Ideal.eq_top_iff_one]
  have h1 : (((Nat.gcd a b : ℕ) : ℤ) : R) ∈ I := by
    rw [Nat.gcd_eq_gcd_ab]
    push_cast
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ ha) (Ideal.mul_mem_right _ _ hb)
  rwa [Nat.Coprime.gcd_eq_one hab, Nat.cast_one, Int.cast_one] at h1

theorem piT_notMem_vGs (hPr : Pr.Ok) (u : Pr.Word) (w : Pr.vGs) : Pr.piT u ∉ w.1.asIdeal := by
  intro h
  obtain ⟨i, hi⟩ := exists_g_mem hPr w
  have hT : (Pr.T u : 𝓞 X.E) ∈ w.1.asIdeal := by
    rw [← hPr.piT_norm u]
    exact Ideal.mul_mem_right _ _ h
  exact natCast_coprime_lemma_7 w.1.isPrime.ne_top
    ((Nat.coprime_primes (hPr.T_prime u) (hPr.g_prime i)).mpr (hPr.T_ne_g u i)) hT hi

theorem T_mem (hPr : Pr.Ok) (u : Pr.Word) (P : Pr.vT u) : (Pr.T u : 𝓞 X.E) ∈ P.1.asIdeal := by
  have h := decoFin_mem_of_mem_divs P.2
  rw [← hPr.piT_norm u]
  exact Ideal.mul_mem_right _ _ h

theorem T_notMem_vGs (hPr : Pr.Ok) (u : Pr.Word) (w : Pr.vGs) : (Pr.T u : 𝓞 X.E) ∉ w.1.asIdeal := by
  intro hT
  obtain ⟨i, hi⟩ := exists_g_mem hPr w
  exact natCast_coprime_lemma_7 w.1.isPrime.ne_top
    ((Nat.coprime_primes (hPr.T_prime u) (hPr.g_prime i)).mpr (hPr.T_ne_g u i)) hT hi

theorem moveHyp_of_ok (hPr : Pr.Ok) (u : Pr.Word) (P : Pr.vT u) : MoveHyp (Pr.vT u) Pr.vGs P := by
  have hpi : Pr.piT u ∈ P.1.asIdeal := decoFin_mem_of_mem_divs P.2
  have hc := conj_piT_notMem hPr u P
  have hTP := T_mem hPr u P
  have hTc : (Pr.T u : 𝓞 X.E) ∈ (conjPrime₂ P.1).asIdeal := by
    rw [mem_conjP, map_natCast]
    exact hTP
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply hc
    rw [← mem_conjP, h]
    exact hpi
  · intro Q h
    apply hc
    rw [← mem_conjP, ← h]
    exact decoFin_mem_of_mem_divs Q.2
  · intro w
    exact ⟨fun h => T_notMem_vGs hPr u w (by rw [h]; exact hTP),
      fun h => T_notMem_vGs hPr u w (by rw [h]; exact hTc)⟩

theorem T_notMem_sq (hPr : Pr.Ok) (u : Pr.Word) (P : Pr.vT u)
    (h : Pr.piT u ∉ P.1.asIdeal ^ 2) : (Pr.T u : 𝓞 X.E) ∉ P.1.asIdeal ^ 2 := by
  intro hT
  apply h
  have hpi : Pr.piT u ∈ P.1.asIdeal := decoFin_mem_of_mem_divs P.2
  have hc := conj_piT_notMem hPr u P
  obtain ⟨t, p, hp, htp⟩ := P.1.isMaximal.exists_inv hc
  have htp' : t * X.conjO (Pr.piT u) + p = 1 := htp
  have e : Pr.piT u = t * (Pr.T u : 𝓞 X.E) + p * Pr.piT u := by
    rw [← hPr.piT_norm u]
    linear_combination (-Pr.piT u) * htp'
  rw [e]
  refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ hT) ?_
  rw [sq]
  exact Ideal.mul_mem_mul hp hpi

end AtBase

section TilEquiv

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem sp_ext {x y : Sp E (n + 1)} (h1 : initL E n x = initL E n y)
    (h2 : x (Fin.last n) = y (Fin.last n)) : x = y := by
  funext i
  induction i using Fin.lastCases with
  | last => exact h2
  | cast j => exact congrFun h1 j

def extL (g : Sp E n →ₗ[E] Sp E n) : Sp E (n + 1) →ₗ[E] Sp E (n + 1) :=
  (incl E n).comp (g.comp (initL E n)) + (LinearMap.proj (Fin.last n)).smulRight (eLast E n)

@[simp] theorem initL_extL (g : Sp E n →ₗ[E] Sp E n) (x : Sp E (n + 1)) :
    initL E n (extL g x) = g (initL E n x) := by
  simp [extL]

@[simp] theorem extL_last (g : Sp E n →ₗ[E] Sp E n) (x : Sp E (n + 1)) :
    extL g x (Fin.last n) = x (Fin.last n) := by
  simp [extL]

def extE (g : Sp E n ≃ₗ[E] Sp E n) : Sp E (n + 1) ≃ₗ[E] Sp E (n + 1) :=
  LinearEquiv.ofLinearMap (extL (g : Sp E n →ₗ[E] Sp E n)) (extL (g.symm : Sp E n →ₗ[E] Sp E n))
    (by ext1 i; apply LinearMap.ext; intro c; apply sp_ext <;> simp)
    (by ext1 i; apply LinearMap.ext; intro c; apply sp_ext <;> simp)

@[simp] theorem initL_extE (g : Sp E n ≃ₗ[E] Sp E n) (x : Sp E (n + 1)) :
    initL E n (extE g x) = g (initL E n x) := initL_extL (g : Sp E n →ₗ[E] Sp E n) x

@[simp] theorem extE_last (g : Sp E n ≃ₗ[E] Sp E n) (x : Sp E (n + 1)) :
    extE g x (Fin.last n) = x (Fin.last n) := extL_last (g : Sp E n →ₗ[E] Sp E n) x

@[simp] theorem initL_extE_symm (g : Sp E n ≃ₗ[E] Sp E n) (x : Sp E (n + 1)) :
    initL E n ((extE g).symm x) = g.symm (initL E n x) := initL_extL (g.symm : Sp E n →ₗ[E] Sp E n) x

@[simp] theorem extE_symm_last (g : Sp E n ≃ₗ[E] Sp E n) (x : Sp E (n + 1)) :
    (extE g).symm x (Fin.last n) = x (Fin.last n) := extL_last (g.symm : Sp E n →ₗ[E] Sp E n) x

theorem extE_mem_UF {g : Sp E n ≃ₗ[E] Sp E n} (hg : g ∈ UF E n) : extE g ∈ UF E (n + 1) := by
  show ∀ x y, hStd E (n + 1) (extE g x) (extE g y) = hStd E (n + 1) x y
  intro x y
  rw [hStd_succ, hStd_succ, initL_extE, initL_extE, extE_last, extE_last,
    show hStd E n (g (initL E n x)) (g (initL E n y)) = hStd E n (initL E n x) (initL E n y) from hg _ _]

def extU : UF E n →* UF E (n + 1) where
  toFun g := ⟨extE g.1, extE_mem_UF g.2⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    apply sp_ext
    · exact initL_extE _ x
    · exact extE_last _ x
  map_mul' a b := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    apply sp_ext
    · change initL E n (extE (a.1 * b.1) x) = initL E n (extE a.1 (extE b.1 x))
      simp only [initL_extE]
      rfl
    · change extE (a.1 * b.1) x (Fin.last n) = extE a.1 (extE b.1 x) (Fin.last n)
      simp only [extE_last]

def padM (R : Type) [CommRing R] (n : ℕ) :
    Matrix (Fin n) (Fin n) R →* Matrix (Fin (n + 1)) (Fin (n + 1)) R where
  toFun A := Matrix.of fun i j =>
    Fin.lastCases (motive := fun _ => R) (Fin.lastCases (motive := fun _ => R) 1 (fun _ => 0) j)
      (fun i' => Fin.lastCases (motive := fun _ => R) 0 (fun j' => A i' j') j) i
  map_one' := by
    ext i j
    refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;>
      simp [Matrix.one_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]
  map_mul' A B := by
    ext i j
    refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_castSucc]

theorem padM_mulVec_snoc {R : Type} [CommRing R] (A : Matrix (Fin n) (Fin n) R) (v : Fin n → R)
    (c : R) : (padM R n A).mulVec (Fin.snoc (α := fun _ => R) v c) =
      Fin.snoc (α := fun _ => R) (A.mulVec v) c := by
  funext i
  induction i using Fin.lastCases with
  | last => simp [padM, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]
  | cast j => simp [padM, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]

def extG : GLG E n SG →* GLG E (n + 1) SG :=
  MonoidHom.pi fun w => (Units.map (padM (𝓞 E ⧸ w.1.asIdeal) n)).comp (Pi.evalMonoidHom _ w)

theorem extG_apply (h : GLG E n SG) (w : SG) :
    ((extG h w : GL (Fin (n + 1)) (𝓞 E ⧸ w.1.asIdeal)) : Matrix _ _ _) =
      padM (𝓞 E ⧸ w.1.asIdeal) n (h w).1 := rfl

theorem tilN_gmap (g : Sp E n ≃ₗ[E] Sp E n) (N : Submodule (𝓞 E) (Sp E n)) :
    tilN (gmap g N) = gmap (extE g) (tilN N) := by
  have h1 : ∀ y, extE g (incl E n y) = incl E n (g y) := fun y =>
    sp_ext (by rw [initL_extE, initL_incl, initL_incl]) (by rw [extE_last, incl_last, incl_last])
  have h2 : extE g (eLast E n) = eLast E n :=
    sp_ext (by rw [initL_extE, initL_eLast, map_zero]) (by rw [extE_last])
  unfold tilN
  rw [gmap_sup]
  congr 1
  · ext z
    simp only [gmap, Submodule.mem_map, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨incl E n y, ⟨y, hy, rfl⟩, h1 y⟩
    · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨g y, ⟨y, hy, rfl⟩, (h1 y).symm⟩
  · unfold gmap
    rw [Submodule.map_span, Set.image_singleton]
    simp only [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, h2]

theorem Deco.til_act (d : Deco E n ∅ SG) (g : Sp E n ≃ₗ[E] Sp E n) (h : GLG E n SG) (pi : 𝓞 E) :
    (d.act g h).til (ST := ST) pi = (d.til (ST := ST) pi).act (extE g) (extG h) := by
  have mg : ∀ (L : Submodule (𝓞 E) (Sp E (n + 1))) (v : Sp E (n + 1)),
      v ∈ gmap (extE g) L ↔ (extE g).symm v ∈ L := by
    intro L v
    simp only [gmap, Submodule.mem_map, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
    · intro hv
      exact ⟨(extE g).symm v, hv, by simp⟩
  have hloc : ∀ (Q : HeightOneSpectrum (𝓞 E)) (x : Sp E (n + 1)),
      x ∈ localization₂ Q.asIdeal (tilN (gmap g d.N)) ↔ (extE g).symm x ∈ localization₂ Q.asIdeal (tilN d.N) := by
    intro Q x
    rw [tilN_gmap, localization_gmap_eq_gmap_localization, mg]
  apply Deco.ext
  · exact tilN_gmap g d.N
  · funext P x
    change (open Classical in if x ∈ localization₂ P.1.asIdeal (tilN (gmap g d.N))
        then redP P.1 (hStd E (n + 1) (z0 E n (algebraMap (𝓞 E) E pi)) x) else 0) =
      (open Classical in if (extE g).symm x ∈ localization₂ P.1.asIdeal (tilN d.N)
        then redP P.1 (hStd E (n + 1) (z0 E n (algebraMap (𝓞 E) E pi)) ((extE g).symm x)) else 0)
    rw [hermStd_lastVector_apply, hermStd_lastVector_apply, extE_symm_last]
    by_cases hm : (extE g).symm x ∈ localization₂ P.1.asIdeal (tilN d.N)
    · rw [if_pos ((hloc P.1 x).mpr hm), if_pos hm]
    · rw [if_neg (fun h' => hm ((hloc P.1 x).mp h')), if_neg hm]
  · funext w x
    change (open Classical in if x ∈ localization₂ w.1.asIdeal (tilN (gmap g d.N))
        then Fin.snoc (α := fun _ => 𝓞 E ⧸ w.1.asIdeal) ((h w).1.mulVec (d.be w (g.symm (initL E n x))))
          (redP w.1 (x (Fin.last n) / algebraMap (𝓞 E) E pi)) else 0) =
      (padM (𝓞 E ⧸ w.1.asIdeal) n (h w).1).mulVec (open Classical in
        if (extE g).symm x ∈ localization₂ w.1.asIdeal (tilN d.N)
        then Fin.snoc (α := fun _ => 𝓞 E ⧸ w.1.asIdeal) (d.be w (initL E n ((extE g).symm x)))
          (redP w.1 ((extE g).symm x (Fin.last n) / algebraMap (𝓞 E) E pi)) else 0)
    by_cases hm : (extE g).symm x ∈ localization₂ w.1.asIdeal (tilN d.N)
    · rw [if_pos ((hloc w.1 x).mpr hm), if_pos hm, padM_mulVec_snoc, initL_extE_symm, extE_symm_last]
    · rw [if_neg (fun h' => hm ((hloc w.1 x).mp h')), if_neg hm, Matrix.mulVec_zero]

theorem DecoSet.til_smul (a : UF E n × GLG E n SG) (d : DecoSet E n ∅ SG) {pi : 𝓞 E}
    (hT : ∀ P : ST, cO E pi ∉ P.1.asIdeal) (hG : ∀ w : SG, pi ∉ w.1.asIdeal) :
    DecoSet.til (ST := ST) pi (a • d) = (extU a.1, extG a.2) • DecoSet.til (ST := ST) pi d := by
  apply Subtype.ext
  rw [DecoSet.smul_val, DecoSet.til_val (a • d) hT hG, DecoSet.til_val d hT hG, DecoSet.smul_val,
    Deco.til_act]
  rfl

end TilEquiv

section Index

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem quot_smul_def (P : HeightOneSpectrum (𝓞 E)) (a : 𝓞 E) (c : 𝓞 E ⧸ P.asIdeal) :
    a • c = Ideal.Quotient.mk P.asIdeal a * c := by
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq]

def Deco.Ok.fLin {d : Deco E n ST SG} (hd : d.Ok) (P : ST) (M : Submodule (𝓞 E) (Sp E n))
    (hM : M ≤ d.at P.1) : M →ₗ[𝓞 E] (𝓞 E ⧸ P.1.asIdeal) where
  toFun y := d.f P y.1
  map_add' y z := hd.f_add P _ (hM y.2) _ (hM z.2)
  map_smul' a y := by
    rw [RingHom.id_apply, quot_smul_def]
    exact hd.f_smul P a _ (hM y.2)

theorem Deco.Ok.exists_dualBasis {d : Deco E n ST SG} (hd : d.Ok) :
    ∃ e : ST → Sp E n, (∀ P, e P ∈ d.N) ∧ (∀ P, d.f P (e P) = 1) ∧
      ∀ P Q, Q ≠ P → d.f Q (e P) = 0 := by
  classical
  have hex : ∀ P : ST, ∃ e ∈ d.N, d.f P e = 1 ∧ ∀ Q : ST, Q ≠ P → d.f Q e = 0 := by
    intro P
    have hu : ∀ Q : ST, ∃ s : 𝓞 E, (Q ≠ P → s ∈ Q.1.asIdeal) ∧ s ∉ P.1.asIdeal := by
      intro Q
      by_cases hQ : Q = P
      · exact ⟨1, fun h => absurd hQ h, fun h1 => P.1.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)⟩
      · obtain ⟨s, hs1, hs2⟩ := exists_mem_notMem (P := Q.1) (Q := P.1) (fun h => hQ (Subtype.ext h))
        exact ⟨s, fun _ => hs1, hs2⟩
    choose s huQ huP using hu
    have htP : (∏ Q, s Q) ∉ P.1.asIdeal := by
      have hm : (∏ Q, s Q) ∈ P.1.asIdeal.primeCompl :=
        Submonoid.prod_mem _ fun Q _ => Ideal.mem_primeCompl_iff.mpr (huP Q)
      exact Ideal.mem_primeCompl_iff.mp hm
    have htQ : ∀ Q : ST, Q ≠ P → (∏ Q', s Q') ∈ Q.1.asIdeal := fun Q hQ => by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ Q)]
      exact Ideal.mul_mem_right _ _ (huQ Q hQ)
    obtain ⟨x, hx, hfx⟩ := hd.f_ne P
    haveI := P.1.isMaximal
    letI := Ideal.Quotient.field P.1.asIdeal
    have hy : d.f P ((∏ Q, s Q) • x) ≠ 0 := by
      rw [hd.f_smul P _ x (mem_localized_of_mem _ _ hx)]
      exact mul_ne_zero (fun h0 => htP (Ideal.Quotient.eq_zero_iff_mem.mp h0)) hfx
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective ((d.f P ((∏ Q, s Q) • x))⁻¹)
    have hyN : (∏ Q, s Q) • x ∈ d.N := Submodule.smul_mem _ _ hx
    refine ⟨c • (∏ Q, s Q) • x, Submodule.smul_mem _ c hyN, ?_, fun Q hQ => ?_⟩
    · rw [hd.f_smul P c _ (mem_localized_of_mem _ _ hyN), hc, inv_mul_cancel₀ hy]
    · rw [hd.f_smul Q c _ (mem_localized_of_mem _ _ hyN), hd.f_smul Q _ x (mem_localized_of_mem _ _ hx),
        Ideal.Quotient.eq_zero_iff_mem.mpr (htQ Q hQ), zero_mul, mul_zero]
  choose e he1 he2 he3 using hex
  exact ⟨e, he1, he2, fun P Q hQP => he3 P Q hQP⟩

theorem Deco.Ok.f_sum_dualBasis {d : Deco E n ST SG} (hd : d.Ok) {e : ST → Sp E n}
    (h1 : ∀ P, e P ∈ d.N) (h2 : ∀ P, d.f P (e P) = 1) (h3 : ∀ P Q, Q ≠ P → d.f Q (e P) = 0)
    (c : ST → 𝓞 E) (Q : ST) :
    d.f Q (∑ P, c P • e P) = Ideal.Quotient.mk Q.1.asIdeal (c Q) := by
  classical
  have hle : ∀ y ∈ d.N, y ∈ d.at Q.1 := fun y hy => mem_localized_of_mem Q.1 d.N hy
  have hsum : ∀ s : Finset ST, (∑ P ∈ s, c P • e P) ∈ d.N := fun s =>
    Submodule.sum_mem _ fun P _ => Submodule.smul_mem _ _ (h1 P)
  have key : ∀ s : Finset ST, d.f Q (∑ P ∈ s, c P • e P) =
      ∑ P ∈ s, Ideal.Quotient.mk Q.1.asIdeal (c P) * d.f Q (e P) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [hd.f_zero Q]
    | @insert P s hP ih =>
      rw [Finset.sum_insert hP, Finset.sum_insert hP,
        hd.f_add Q _ (hle _ (Submodule.smul_mem _ _ (h1 P))) _ (hle _ (hsum s)),
        hd.f_smul Q _ _ (hle _ (h1 P)), ih]
  rw [key, Finset.sum_eq_single Q]
  · rw [h2, mul_one]
  · intro P _ hPQ
    rw [h3 P Q (Ne.symm hPQ), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ Q) h

theorem card_quot_conjP (P : HeightOneSpectrum (𝓞 E)) :
    Nat.card (𝓞 E ⧸ (conjPrime₂ P).asIdeal) = Nat.card (𝓞 E ⧸ P.asIdeal) := by
  have surj : Function.Surjective (cO E) := fun r => ⟨cO E r, cO_cO r⟩
  have inj : Function.Injective (cO E) := fun a b h => by
    rw [← cO_cO a, h, cO_cO]
  exact Nat.card_congr (Ideal.quotientEquiv (conjPrime₂ P).asIdeal P.asIdeal
    (RingEquiv.ofBijective (cO E) ⟨inj, surj⟩)
    (Ideal.map_comap_of_surjective (cO E) surj P.asIdeal).symm).toEquiv

theorem Deco.Ok.Lsh_quot_L {d : Deco E n ST SG} (hd : d.Ok) (hc : ∀ P Q : ST, Q.1 ≠ conjPrime₂ P.1) :
    Nonempty ((d.Lsh ⧸ d.L.submoduleOf d.Lsh) ≃ₗ[𝓞 E]
      ((∀ P : ST, 𝓞 E ⧸ P.1.asIdeal) × (∀ P : ST, 𝓞 E ⧸ (conjPrime₂ P.1).asIdeal))) := by
  classical
  obtain ⟨e, h1, h2, h3⟩ := hd.exists_dualBasis
  have hdN : dual (hStd E n) d.N = d.N := hd.uni

  have hle : ∀ P : ST, d.Lsh ≤ d.at P.1 := by
    intro P
    have hex : ∀ Q : ST, ∃ a : 𝓞 E, a ∉ P.1.asIdeal ∧ a ∈ (conjPrime₂ Q.1).asIdeal := by
      intro Q
      obtain ⟨a, ha, ha'⟩ := exists_mem_notMem (P := conjPrime₂ Q.1) (Q := P.1) (hc Q P).symm
      exact ⟨a, ha', ha⟩
    choose a ha ha' using hex
    intro y hy
    refine (mem_locP _ _ _).2 ⟨∏ Q : ST, a Q, fun h' => ?_, hd.smul_Lsh_mem_N (fun Q => ?_) hy⟩
    · obtain ⟨Q, -, hQ⟩ := (Ideal.IsPrime.prod_mem_iff (hp := P.1.isPrime)).1 h'
      exact ha Q hQ
    · have : (∏ Q : ST, a Q) ∈ (conjPrime₂ Q.1).asIdeal :=
        Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem a (Finset.mem_univ Q)) (ha' Q)
      exact this

  have hunif : ∀ P : ST, ∃ t ∈ (conjPrime₂ P.1).asIdeal, t ∉ (conjPrime₂ P.1).asIdeal ^ 2 := by
    intro P
    obtain ⟨t, ht, ht'⟩ := Ideal.exists_mem_pow_notMem_pow_succ (conjPrime₂ P.1).asIdeal (conjPrime₂ P.1).ne_bot
      (conjPrime₂ P.1).isPrime.ne_top 1
    exact ⟨t, by simpa using ht, ht'⟩
  choose t ht ht2 using hunif

  have hpe : ∀ (P : ST) (p : 𝓞 E), p ∈ P.1.asIdeal → p • e P ∈ d.L := by
    intro P p hp
    rw [hd.mem_L]
    refine ⟨Submodule.smul_mem _ p (h1 P), fun Q => ?_⟩
    rw [hd.f_smul Q p _ (le_locP _ _ (h1 P))]
    by_cases hQ : Q = P
    · subst hQ
      rw [Ideal.Quotient.eq_zero_iff_mem.2 hp, zero_mul]
    · rw [h3 P Q hQ, mul_zero]
  have hinv : ∀ (P : ST), ∀ y ∈ d.Lsh, hStd E n (e P) y ∈ invIdeal (K := E) (conjPrime₂ P.1).asIdeal := by
    intro P y hy
    rw [neighbourConstruct_mem_inv]
    intro p hp
    have e1 : algebraMap (𝓞 E) E p * hStd E n (e P) y = hStd E n (cO E p • e P) y := by
      rw [hStd_osmul_left, cO_cO, ← algebraMap_smul E p y, LinearMap.map_smul, smul_eq_mul]
    rw [e1]
    exact Submodule.mem_one.1 ((mem_dual _ y).1 hy _ (hpe P _ hp))
  have hint : ∀ (P : ST), ∀ y ∈ d.Lsh, ∃ r : 𝓞 E,
      algebraMap (𝓞 E) E r = algebraMap (𝓞 E) E (t P) * hStd E n (e P) y := fun P y hy =>
    neighbourConstruct_mem_inv.1 (hinv P y hy) (t P) (ht P)

  let ψ : d.Lsh →ₗ[𝓞 E] (∀ P : ST, 𝓞 E ⧸ (conjPrime₂ P.1).asIdeal) :=
    { toFun := fun y P => redP (conjPrime₂ P.1) (algebraMap (𝓞 E) E (t P) * hStd E n (e P) y.1)
      map_add' := by
        intro y z
        funext P
        obtain ⟨r, hr⟩ := hint P y.1 y.2
        obtain ⟨r', hr'⟩ := hint P z.1 z.2
        change redP _ (_ * hStd E n (e P) (y.1 + z.1)) = redP _ _ + redP _ _
        rw [map_add, mul_add, ← hr, ← hr']
        exact reduction_add (IntAt.coe _ _) (IntAt.coe _ _)
      map_smul' := by
        intro a y
        funext P
        obtain ⟨r, hr⟩ := hint P y.1 y.2
        change redP _ (_ * hStd E n (e P) (a • y.1)) = a • redP _ _
        rw [LinearMap.map_smul_of_tower, mul_smul_comm, ← hr, quot_smul_def]
        exact redP_osmul a (IntAt.coe _ _) }
  have hψ : ∀ (y : d.Lsh) (P : ST),
      ψ y P = redP (conjPrime₂ P.1) (algebraMap (𝓞 E) E (t P) * hStd E n (e P) y.1) := fun _ _ => rfl

  have hdec : ∀ x ∈ d.N, ∃ c : ST → 𝓞 E, x - ∑ P, c P • e P ∈ d.L := by
    intro x hx
    choose c hcx using fun P : ST => Ideal.Quotient.mk_surjective (d.f P x)
    refine ⟨c, ?_⟩
    have hs : ∑ P, c P • e P ∈ d.N := Submodule.sum_mem _ fun P _ => Submodule.smul_mem _ _ (h1 P)
    rw [hd.mem_L]
    refine ⟨Submodule.sub_mem _ hx hs, fun Q => ?_⟩
    have e1 : x - ∑ P, c P • e P = x + (-1 : 𝓞 E) • ∑ P, c P • e P := by
      rw [neg_smul, one_smul, sub_eq_add_neg]
    rw [e1, hd.f_add Q x (le_locP _ _ hx) _ (le_locP _ _ (Submodule.smul_mem _ _ hs)),
      hd.f_smul Q _ _ (le_locP _ _ hs), hd.f_sum_dualBasis h1 h2 h3, hcx]
    simp

  have hmemN : ∀ y ∈ d.Lsh, (∀ P : ST, hStd E n (e P) y ∈ (1 : Submodule (𝓞 E) E)) → y ∈ d.N := by
    intro y hy H
    rw [← hdN, mem_dual]
    intro x hx
    obtain ⟨c, hcx⟩ := hdec x hx
    have e1 : x = (x - ∑ P, c P • e P) + ∑ P, c P • e P := by abel
    rw [e1, map_add, LinearMap.add_apply, map_sum, LinearMap.sum_apply]
    refine Submodule.add_mem _ ((mem_dual _ y).1 hy _ hcx) (Submodule.sum_mem _ fun P _ => ?_)
    rw [hStd_osmul_left, LinearMap.map_smul_of_tower]
    exact Submodule.smul_mem _ _ (H P)
  have hker1 : ∀ (y : d.Lsh) (P : ST), ψ y P = 0 → hStd E n (e P) y.1 ∈ (1 : Submodule (𝓞 E) E) := by
    intro y P h0
    obtain ⟨r, hr⟩ := hint P y.1 y.2
    rw [hψ, ← hr, reduction_coe, Ideal.Quotient.eq_zero_iff_mem] at h0
    exact Submodule.mem_one.2 (inv_integral (conjPrime₂ P.1) (ht P) (ht2 P) (hinv P y.1 y.2) h0 hr.symm)
  have hψN : ∀ (y : d.Lsh), y.1 ∈ d.N → ψ y = 0 := by
    intro y hy
    funext P
    have h4 : hStd E n (e P) y.1 ∈ (1 : Submodule (𝓞 E) E) := by
      rw [← hdN] at hy
      exact (mem_dual _ _).1 hy _ (h1 P)
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 h4
    rw [hψ, ← hr, ← map_mul, reduction_coe]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_right _ _ (ht P))

  have hψbasis : ∀ P : ST, ∃ y : d.Lsh, ψ y P = 1 ∧ ∀ Q, Q ≠ P → ψ y Q = 0 := by
    intro P
    have hBlat : Submodule.IsLattice E (d.kerAt P) := by
      obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.1.ne_bot
      exact lattice_of_smul hd.lat hd.lat (fun x hx => ((hd.mem_kerAt P x).1 hx).1) hp0
        fun x hx => hd.smul_mem_kerAt P hp hx
    have hnot : ¬ dual (hStd E n) (d.kerAt P) ≤ d.N := by
      intro hle'
      have := dual_anti hle'
      rw [hdN, dual_dual hBlat] at this
      have h5 := ((hd.mem_kerAt P _).1 (this (h1 P))).2
      rw [h2] at h5
      exact one_ne_zero h5
    obtain ⟨y, hy, hyN⟩ := SetLike.not_le_iff_exists.1 hnot
    have hLB : d.L ≤ d.kerAt P := fun x hx =>
      (hd.mem_kerAt P x).2 ⟨((hd.mem_L x).1 hx).1, ((hd.mem_L x).1 hx).2 P⟩
    have hyL : y ∈ d.Lsh := dual_anti hLB hy
    have hQ0 : ∀ Q, Q ≠ P → hStd E n (e Q) y ∈ (1 : Submodule (𝓞 E) E) := fun Q hQ =>
      (mem_dual _ y).1 hy _ ((hd.mem_kerAt P _).2 ⟨h1 Q, h3 Q P (Ne.symm hQ)⟩)
    have hP0 : ψ ⟨y, hyL⟩ P ≠ 0 := by
      intro h0
      apply hyN
      refine hmemN y hyL fun Q => ?_
      by_cases hQ : Q = P
      · subst hQ
        exact hker1 ⟨y, hyL⟩ Q h0
      · exact hQ0 Q hQ
    have := (conjPrime₂ P.1).isMaximal
    obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv hP0
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective b
    refine ⟨s • ⟨y, hyL⟩, ?_, fun Q hQ => ?_⟩
    · rw [map_smul, Pi.smul_apply, quot_smul_def, mul_comm, hb]
    · obtain ⟨r, hr⟩ := Submodule.mem_one.1 (hQ0 Q hQ)
      rw [map_smul, Pi.smul_apply, hψ]
      change s • redP _ (_ * hStd E n (e Q) y) = 0
      rw [← hr, ← map_mul, reduction_coe, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_right _ _ (ht Q)),
        smul_zero]
  choose yb hyb1 hyb2 using hψbasis
  have hψsurj : Function.Surjective ψ := by
    intro c
    choose r hr using fun P : ST => Ideal.Quotient.mk_surjective (c P)
    refine ⟨∑ P, r P • yb P, ?_⟩
    funext Q
    rw [map_sum, Finset.sum_apply, Finset.sum_eq_single Q]
    · rw [map_smul, Pi.smul_apply, hyb1, quot_smul_def, mul_one, hr]
    · intro P _ hP
      rw [map_smul, Pi.smul_apply, hyb2 P Q hP.symm, smul_zero]
    · intro h
      exact absurd (Finset.mem_univ Q) h

  let φ : d.Lsh →ₗ[𝓞 E] (∀ P : ST, 𝓞 E ⧸ P.1.asIdeal) :=
    LinearMap.pi fun P => hd.fLin P d.Lsh (hle P)
  have hφ : ∀ (y : d.Lsh) (P : ST), φ y P = d.f P y.1 := fun _ _ => rfl
  let Θ := φ.prod ψ
  have hΘker : LinearMap.ker Θ = d.L.submoduleOf d.Lsh := by
    ext y
    rw [LinearMap.mem_ker]
    change Θ y = 0 ↔ y.1 ∈ d.L
    constructor
    · intro h0
      have h01 : φ y = 0 := congrArg Prod.fst h0
      have h02 : ψ y = 0 := congrArg Prod.snd h0
      rw [hd.mem_L]
      refine ⟨hmemN y.1 y.2 fun P => hker1 y P (congrFun h02 P), fun P => ?_⟩
      rw [← hφ, h01]
      rfl
    · intro hy
      obtain ⟨hy1, hy2⟩ := (hd.mem_L _).1 hy
      refine Prod.ext ?_ (hψN y hy1)
      funext P
      exact hy2 P
  have hΘsurj : Function.Surjective Θ := by
    rintro ⟨c, c'⟩
    obtain ⟨y1, hy1⟩ := hψsurj c'
    choose r hr using fun P : ST => Ideal.Quotient.mk_surjective (c P - φ y1 P)
    have hs : ∑ P, r P • e P ∈ d.N := Submodule.sum_mem _ fun P _ => Submodule.smul_mem _ _ (h1 P)
    let y2 : d.Lsh := ⟨∑ P, r P • e P, hd.N_le_Lsh hs⟩
    have hφ2 : ∀ Q, φ y2 Q = Ideal.Quotient.mk Q.1.asIdeal (r Q) := fun Q =>
      (hφ y2 Q).trans (hd.f_sum_dualBasis h1 h2 h3 r Q)
    have hψ2 : ψ y2 = 0 := hψN y2 hs
    refine ⟨y1 + y2, Prod.ext ?_ ?_⟩
    · funext Q
      change φ (y1 + y2) Q = c Q
      rw [map_add, Pi.add_apply, hφ2, hr]
      abel
    · change ψ (y1 + y2) = c'
      rw [map_add, hψ2, add_zero, hy1]
  exact ⟨(Submodule.quotEquivOfEq _ _ hΘker.symm).trans (Θ.quotKerEquivOfSurjective hΘsurj)⟩

theorem Deco.Ok.card_Lsh_quot_L {d : Deco E n ST SG} (hd : d.Ok)
    (hc : ∀ P Q : ST, Q.1 ≠ conjPrime₂ P.1) :
    Nat.card (d.Lsh ⧸ d.L.submoduleOf d.Lsh) = ∏ P : ST, Nat.card (𝓞 E ⧸ P.1.asIdeal) ^ 2 := by
  obtain ⟨ε⟩ := hd.Lsh_quot_L hc
  rw [Nat.card_congr ε.toEquiv, Nat.card_prod, Nat.card_pi, Nat.card_pi, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun P _ => ?_
  rw [card_quot_conjP, sq]

theorem card_Lsh_quot_L_of_ok {X : Fields} {Pr : Primes X} (hPr : Pr.Ok) (u : Pr.Word) {n : ℕ}
    (d : ColDeco X Pr u n) :
    Nat.card (d.1.Lsh ⧸ d.1.L.submoduleOf d.1.Lsh) = Pr.T u ^ (2 * X.f) := by
  rw [Deco.Ok.card_Lsh_quot_L d.2 (fun P Q => (moveHyp_of_ok hPr u P).st Q)]
  have h1 : ∀ P : Pr.vT u, Nat.card (𝓞 X.E ⧸ P.1.asIdeal) = Pr.T u := fun P => by
    rw [← hPr.vT_norm u P.1 P.2, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  simp only [h1, Finset.prod_const, Finset.card_univ, Fintype.card_coe, hPr.vT_card u, ← pow_mul]

end Index

section Misc

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

def DecoSet.forgetT (d : DecoSet E n ST SG) : DecoSet E n ∅ SG :=
  ⟨{ N := d.1.N, f := fun P => absurd P.2 (Finset.notMem_empty _), be := d.1.be },
    { lat := d.2.lat
      uni := d.2.uni
      f_add := fun P => absurd P.2 (Finset.notMem_empty _)
      f_smul := fun P => absurd P.2 (Finset.notMem_empty _)
      f_off := fun P => absurd P.2 (Finset.notMem_empty _)
      f_ne := fun P => absurd P.2 (Finset.notMem_empty _)
      be_add := d.2.be_add
      be_smul := d.2.be_smul
      be_off := d.2.be_off
      be_surj := d.2.be_surj
      be_ker := d.2.be_ker }⟩

end Misc

section AtBase2

variable {X : Fields} {Pr : Primes X}

theorem posStar_of_ok (hX : X.Ok) : PosStar X.E := posStar_of_conj hX.conjE

theorem T_unif (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) (P : Pr.vT u) :
    (Pr.T u : 𝓞 X.E) ∈ P.1.asIdeal ∧ (Pr.T u : 𝓞 X.E) ∉ P.1.asIdeal ^ 2 :=
  ⟨T_mem hPr u P, T_notMem_sq hPr u P (hPr.piT_notMem_sq hX u P.2)⟩

theorem upD_finite_nonempty (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) {n : ℕ} (P : Pr.vT u)
    (d : ColDeco X Pr u n) : (upD u P d).Finite ∧ (upD u P d).Nonempty := ⟨DecoSet.upSet_finite d P _, DecoSet.upSet_nonempty d P (moveHyp_of_ok hPr u P) (T_unif hX hPr u P).1 (T_unif hX hPr u P).2⟩

theorem piT_dvd_of_mem (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) (r : 𝓞 X.E)
    (hr : ∀ P : Pr.vT u, r ∈ P.1.asIdeal) : Pr.piT u ∣ r := by
  classical
  have hbase : (↑(Pr.vT u) : Set (HeightOneSpectrum (𝓞 X.E))).Pairwise
      (Function.onFun IsCoprime fun Q => Q.asIdeal) := by
    intro Q _ Q' _ hne
    change IsCoprime Q.asIdeal Q'.asIdeal
    rw [Ideal.isCoprime_iff_sup_eq]
    exact Ideal.IsMaximal.coprime_of_ne Q.isMaximal Q'.isMaximal
      fun h => hne (HeightOneSpectrum.ext h)
  have h1 : ∏ Q ∈ Pr.vT u, Q.asIdeal ∣ Ideal.span {Pr.piT u} :=
    Finset.prod_dvd_of_coprime hbase fun Q hQ => by
      rw [Ideal.dvd_span_singleton]
      exact decoFin_mem_of_mem_divs hQ
  have h2 : ∏ Q ∈ Pr.vT u, Q.asIdeal ∣ Ideal.span {r} :=
    Finset.prod_dvd_of_coprime hbase fun Q hQ => by
      rw [Ideal.dvd_span_singleton]
      exact hr ⟨Q, hQ⟩
  have hN : Ideal.absNorm (∏ Q ∈ Pr.vT u, Q.asIdeal) = Pr.T u ^ X.f := by
    rw [map_prod, Finset.prod_congr rfl fun Q hQ => hPr.vT_norm u Q hQ, Finset.prod_const,
      hPr.vT_card]
  obtain ⟨J, hJ⟩ := h1
  have hJ1 : Ideal.absNorm J = 1 := by
    have := congrArg Ideal.absNorm hJ
    rw [map_mul, hN, hPr.absNorm_piT hX u] at this
    exact (Nat.eq_of_mul_eq_mul_left (pow_pos (hPr.T_prime u).pos _) (by rw [mul_one]; exact this)).symm
  rw [Ideal.absNorm_eq_one_iff.1 hJ1, Ideal.mul_top] at hJ
  rw [← hJ] at h2
  rw [Ideal.dvd_span_singleton, Ideal.mem_span_singleton] at h2
  exact h2

end AtBase2

section Bridge

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem decoFin_gram_hStd : Formalism.UG.gram (hStd E n) = 1 := by
  ext i j
  simp only [Formalism.UG.gram, hStd, LinearMap.mk₂'ₛₗ_apply]
  rw [Finset.sum_eq_single i (fun k _ hk => by rw [Pi.single_eq_of_ne hk, star_zero, zero_mul])
    (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, star_one, one_mul, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · rw [Pi.single_eq_of_ne hij, if_neg hij]

theorem mem_UJ_iff (g : GL (Fin n) E) :
    g ∈ Formalism.UG.UJ (starRingEnd E) (1 : Matrix (Fin n) (Fin n) E) ↔ Formalism.UG.glEquiv g ∈ UF E n := by
  rw [← decoFin_gram_hStd]
  exact Formalism.UG.Final.HermBridge E (Fin n) (hStd E n) g

end Bridge

section TilClasses

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem int_eq_one_of_small {c : 𝓞 E}
    (hc : ∀ σ : E →ₐ[ℚ] ℂ, ‖σ (algebraMap (𝓞 E) E c)‖ ≤ 1)
    (hP : ∀ P ∈ ST, c - 1 ∈ P.asIdeal)
    (hbig : 2 ^ Module.finrank ℚ E < ∏ P ∈ ST, Ideal.absNorm P.asIdeal) : c = 1 := by
  classical
  by_contra hne
  have hr : c - 1 ≠ 0 := sub_ne_zero.2 hne
  have hbase : (↑ST : Set (HeightOneSpectrum (𝓞 E))).Pairwise
      (Function.onFun IsCoprime fun Q => Q.asIdeal) := by
    intro Q _ Q' _ hne
    change IsCoprime Q.asIdeal Q'.asIdeal
    rw [Ideal.isCoprime_iff_sup_eq]
    exact Ideal.IsMaximal.coprime_of_ne Q.isMaximal Q'.isMaximal
      fun h => hne (HeightOneSpectrum.ext h)
  have h1 : ∏ Q ∈ ST, Q.asIdeal ∣ Ideal.span {c - 1} :=
    Finset.prod_dvd_of_coprime hbase fun Q hQ => by
      rw [Ideal.dvd_span_singleton]
      exact hP Q hQ
  have h2 := map_dvd Ideal.absNorm h1
  rw [map_prod] at h2
  have h3 : Ideal.absNorm (Ideal.span {c - 1}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hr
  have h4 := Nat.le_of_dvd (Nat.pos_of_ne_zero h3) h2
  have h5 : (Ideal.absNorm (Ideal.span {c - 1}) : ℝ) ≤ 2 ^ Module.finrank ℚ E := by
    rw [Ideal.absNorm_span_singleton]
    have e1 : ((Algebra.norm ℤ (c - 1)).natAbs : ℝ) =
        ‖algebraMap ℚ ℂ (Algebra.norm ℚ (algebraMap (𝓞 E) E (c - 1)))‖ := by
      have e0 : Algebra.norm ℚ (algebraMap (𝓞 E) E (c - 1)) = ((Algebra.norm ℤ (c - 1) : ℤ) : ℚ) :=
        (Algebra.coe_norm_int (c - 1)).symm
      rw [e0, Nat.cast_natAbs]
      simp
    rw [e1, Algebra.norm_eq_prod_embeddings, norm_prod, ← AlgHom.card ℚ E ℂ, ← Finset.card_univ,
      ← Finset.prod_const]
    refine Finset.prod_le_prod (fun σ _ => norm_nonneg _) fun σ _ => ?_
    rw [map_sub, map_sub, map_one, map_one]
    calc ‖σ (algebraMap (𝓞 E) E c) - 1‖ ≤ ‖σ (algebraMap (𝓞 E) E c)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by rw [norm_one]; linarith [hc σ]
      _ = 2 := by norm_num
  have h6 : (Ideal.absNorm (Ideal.span {c - 1})) ≤ 2 ^ Module.finrank ℚ E := by exact_mod_cast h5
  omega

theorem til_fix_eLast (hconj : ∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a))
    (hbig : 2 ^ Module.finrank ℚ E < ∏ P ∈ ST, Ideal.absNorm P.asIdeal)
    {d₁ d₂ : Deco E n ∅ SG} {pi : 𝓞 E} (hT : ∀ P : ST, cO E pi ∉ P.1.asIdeal)
    {γ : Sp E (n + 1) ≃ₗ[E] Sp E (n + 1)} (hγ : γ ∈ UF E (n + 1)) {h : GLG E (n + 1) SG}
    (H : (d₁.til (ST := ST) pi).act γ h = d₂.til (ST := ST) pi) : γ (eLast E n) = eLast E n := by
  have he : eLast E n ∈ tilN d₁.N := (mem_tilN _ _).2 ⟨by simp, 1, by simp⟩
  have hN : gmap γ (tilN d₁.N) = tilN d₂.N := congrArg Deco.N H
  have hy : γ (eLast E n) ∈ tilN d₂.N := by
    rw [← hN, mem_gmap]
    simpa using he
  obtain ⟨-, c, hcl⟩ := (mem_tilN _ _).1 hy

  have hcP : ∀ P ∈ ST, c - 1 ∈ P.asIdeal := by
    intro P hP
    have h1 : (d₁.til (ST := ST) pi).f ⟨P, hP⟩ (γ.symm (γ (eLast E n))) =
        (d₂.til (ST := ST) pi).f ⟨P, hP⟩ (γ (eLast E n)) :=
      congrFun (congrFun (congrArg Deco.f H) ⟨P, hP⟩) (γ (eLast E n))
    rw [LinearEquiv.symm_apply_apply] at h1
    have h2 : (d₁.til (ST := ST) pi).f ⟨P, hP⟩ (eLast E n) =
        redP P (hStd E (n + 1) (z0 E n (algebraMap (𝓞 E) E pi)) (eLast E n)) :=
      if_pos (le_locP _ _ he)
    have h3 : (d₂.til (ST := ST) pi).f ⟨P, hP⟩ (γ (eLast E n)) =
        redP P (hStd E (n + 1) (z0 E n (algebraMap (𝓞 E) E pi)) (γ (eLast E n))) :=
      if_pos (le_locP _ _ hy)
    rw [h2, h3, hermStd_lastVector_apply, hermStd_lastVector_apply, eLast_last, mul_one, ← hcl, ← map_mul, reduction_coe, reduction_coe] at h1
    have h4 : cO E pi * (c - 1) ∈ P.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, mul_sub, mul_one, map_sub, ← h1, sub_self]
    exact (P.isPrime.mem_or_mem h4).resolve_left (hT ⟨P, hP⟩)

  have hnorm : hStd E n (initL E n (γ (eLast E n))) (initL E n (γ (eLast E n))) +
      star (algebraMap (𝓞 E) E c) * algebraMap (𝓞 E) E c = 1 := by
    have h1 := hγ (eLast E n) (eLast E n)
    rw [hStd_succ, hStd_succ, ← hcl] at h1
    rw [h1]
    simp
  have hcσ : ∀ σ : E →ₐ[ℚ] ℂ, ‖σ (algebraMap (𝓞 E) E c)‖ ≤ 1 := by
    intro σ
    have h1 := congrArg σ hnorm
    rw [map_add, map_mul, map_one, hStd_apply, map_sum,
      show σ (star (algebraMap (𝓞 E) E c)) = starRingEnd ℂ (σ (algebraMap (𝓞 E) E c)) from
        hconj σ.toRingHom _, mul_comm (starRingEnd ℂ _), Complex.mul_conj] at h1
    have h2 : ∀ i, σ (star (initL E n (γ (eLast E n)) i) * initL E n (γ (eLast E n)) i) =
        ((Complex.normSq (σ (initL E n (γ (eLast E n)) i)) : ℝ) : ℂ) := by
      intro i
      rw [map_mul, show σ (star (initL E n (γ (eLast E n)) i)) =
        starRingEnd ℂ (σ (initL E n (γ (eLast E n)) i)) from hconj σ.toRingHom _, mul_comm,
        Complex.mul_conj]
    rw [Finset.sum_congr rfl fun i _ => h2 i, ← Complex.ofReal_sum, ← Complex.ofReal_add] at h1
    have h3 : (∑ i, Complex.normSq (σ (initL E n (γ (eLast E n)) i))) +
        Complex.normSq (σ (algebraMap (𝓞 E) E c)) = 1 := by exact_mod_cast h1
    have h4 : 0 ≤ ∑ i, Complex.normSq (σ (initL E n (γ (eLast E n)) i)) :=
      Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
    have h5 : Complex.normSq (σ (algebraMap (𝓞 E) E c)) ≤ 1 := by linarith
    rw [Complex.normSq_eq_norm_sq] at h5
    exact (sq_le_one_iff₀ (norm_nonneg _)).1 h5
  have hc1 : c = 1 := int_eq_one_of_small hcσ hcP hbig
  rw [hc1, map_one, star_one, one_mul] at hnorm
  have h0 : hStd E n (initL E n (γ (eLast E n))) (initL E n (γ (eLast E n))) = 0 := by
    have := hnorm
    rwa [add_eq_right] at this
  have hl : initL E n (γ (eLast E n)) = 0 := by
    by_contra hne
    have := hStd_pos (posStar_of_conj hconj) _ hne
    rw [h0, map_zero] at this
    exact lt_irrefl _ this
  apply sp_ext
  · rw [hl, initL_eLast]
  · rw [← hcl, hc1, map_one, eLast_last]

theorem exists_extU_of_fix (γ : UF E (n + 1)) (h : γ.1 (eLast E n) = eLast E n) :
    ∃ γ' : UF E n, γ = extU γ' := by
  have hlast : ∀ (g : UF E (n + 1)), g.1 (eLast E n) = eLast E n → ∀ x : Sp E n,
      g.1 (incl E n x) (Fin.last n) = 0 := by
    intro g hg x
    have h1 := g.2 (eLast E n) (incl E n x)
    rw [hg, hStd_succ, hStd_succ] at h1
    simpa using h1
  have hinv : γ⁻¹.1 (eLast E n) = eLast E n := by
    change γ.1.symm (eLast E n) = eLast E n
    rw [LinearEquiv.symm_apply_eq, h]
  have hincl : ∀ (g : UF E (n + 1)), g.1 (eLast E n) = eLast E n → ∀ x : Sp E n,
      g.1 (incl E n x) = incl E n (initL E n (g.1 (incl E n x))) := by
    intro g hg x
    apply sp_ext
    · simp
    · rw [hlast g hg x, incl_last]
  let A : Sp E n →ₗ[E] Sp E n := (initL E n).comp ((γ.1 : Sp E (n + 1) →ₗ[E] _).comp (incl E n))
  let B : Sp E n →ₗ[E] Sp E n :=
    (initL E n).comp ((γ⁻¹.1 : Sp E (n + 1) →ₗ[E] _).comp (incl E n))
  have hA : ∀ x, A x = initL E n (γ.1 (incl E n x)) := fun _ => rfl
  have hB : ∀ x, B x = initL E n (γ⁻¹.1 (incl E n x)) := fun _ => rfl
  have hAB : A.comp B = LinearMap.id := by
    apply LinearMap.ext
    intro x
    rw [LinearMap.comp_apply, hA, hB, ← hincl γ⁻¹ hinv x]
    change initL E n (γ.1 (γ.1.symm (incl E n x))) = x
    simp
  have hBA : B.comp A = LinearMap.id := by
    apply LinearMap.ext
    intro x
    rw [LinearMap.comp_apply, hA, hB, ← hincl γ h x]
    change initL E n (γ.1.symm (γ.1 (incl E n x))) = x
    simp
  let g' : Sp E n ≃ₗ[E] Sp E n := LinearEquiv.ofLinearMap A B hAB hBA
  have hg' : ∀ x, g' x = initL E n (γ.1 (incl E n x)) := fun _ => rfl
  have hU : g' ∈ UF E n := by
    intro x y
    have h1 := γ.2 (incl E n x) (incl E n y)
    rw [hStd_succ, hStd_succ, hlast γ h x, hlast γ h y] at h1
    simpa [hg'] using h1
  refine ⟨⟨g', hU⟩, ?_⟩
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change γ.1 x = extE g' x
  conv_lhs => rw [sp_decomp x, map_add, map_smul, h, hincl γ h]
  apply sp_ext
  · rw [initL_extE, hg', map_add, map_smul]
    simp
  · rw [extE_last]
    simp

theorem Deco.til_injective {d₁ d₂ : Deco E n ∅ SG} (h₁ : d₁.Ok) (h₂ : d₂.Ok) {pi : 𝓞 E}
    (H : d₁.til (ST := ST) pi = d₂.til (ST := ST) pi) : d₁ = d₂ := by
  have hN : d₁.N = d₂.N := by
    have hT : tilN d₁.N = tilN d₂.N := congrArg Deco.N H
    ext x
    have key : ∀ M : Submodule (𝓞 E) (Sp E n), x ∈ M ↔ incl E n x ∈ tilN M := fun M => by
      rw [mem_tilN, initL_incl, incl_last]
      exact ⟨fun h => ⟨h, 0, map_zero _⟩, fun h => h.1⟩
    rw [key, key, hT]
  apply Deco.ext
  · exact hN
  · funext P
    exact absurd P.2 (Finset.notMem_empty _)
  · funext w y
    by_cases hy : y ∈ localization₂ w.1.asIdeal d₁.N
    · have hbe := congrArg (fun e : Deco E (n + 1) ST SG => e.be w (incl E n y)) H
      have hy' : incl E n y ∈ localization₂ w.1.asIdeal (tilN d₁.N) := by
        rw [mem_localization_tilN, initL_incl, incl_last]
        exact ⟨hy, 0, 1, fun h1 => w.1.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1), by simp⟩
      have hy'' : incl E n y ∈ localization₂ w.1.asIdeal (tilN d₂.N) := by
        rw [← hN]
        exact hy'
      simp only [Deco.til, if_pos hy', if_pos hy'', initL_incl] at hbe
      have h2 := congrArg Fin.init hbe
      simp only [Fin.init_snoc] at h2
      exact h2
    · have hy2 : y ∉ localization₂ w.1.asIdeal d₂.N := by
        rw [← hN]
        exact hy
      rw [h₁.be_off w y hy, h₂.be_off w y hy2]

theorem DecoSet.til_class_inj (hconj : ∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a))
    (hbig : 2 ^ Module.finrank ℚ E < ∏ P ∈ ST, Ideal.absNorm P.asIdeal) {pi : 𝓞 E}
    (hT : ∀ P : ST, cO E pi ∉ P.1.asIdeal) (hG : ∀ w : SG, pi ∉ w.1.asIdeal)
    (d₁ d₂ : DecoSet E n ∅ SG) (γ : UF E (n + 1)) (h : GLG E n SG)
    (H : (γ, extG h) • DecoSet.til (ST := ST) pi d₁ = DecoSet.til (ST := ST) pi d₂) :
    ∃ γ' : UF E n, γ = extU γ' ∧ (γ', h) • d₁ = d₂ := by
  have H1 : (d₁.1.til (ST := ST) pi).act γ.1 (extG h) = d₂.1.til (ST := ST) pi := by
    have := congrArg Subtype.val H
    rwa [DecoSet.smul_val, DecoSet.til_val _ hT hG, DecoSet.til_val _ hT hG] at this
  obtain ⟨γ', rfl⟩ := exists_extU_of_fix γ (til_fix_eLast hconj hbig hT γ.2 H1)
  refine ⟨γ', rfl, ?_⟩
  rw [← DecoSet.til_smul (γ', h) d₁ hT hG] at H
  apply Subtype.ext
  have H2 := congrArg Subtype.val H
  rw [DecoSet.til_val _ hT hG, DecoSet.til_val _ hT hG] at H2
  exact Deco.til_injective ((γ', h) • d₁).2 d₂.2 H2

end TilClasses

section AtBase3

variable {X : Fields} {Pr : Primes X}

end AtBase3

section DnNonempty

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem DecoSet.dnSet_nonempty (d : DecoSet E n ST SG) (P : ST) (hP : MoveHyp ST SG P) {q : 𝓞 E}
    (hq : q ∈ P.1.asIdeal) (hq2 : q ∉ P.1.asIdeal ^ 2) : (d.dnSet P q).Nonempty := by
  classical
  have hd := d.2
  have hmax := P.1.isMaximal

  obtain ⟨x0, hx0, hne⟩ := hd.f_ne P
  obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv hne
  obtain ⟨t0, rfl⟩ := Ideal.Quotient.mk_surjective b
  set e1 := t0 • x0 with he1def
  have he1 : e1 ∈ d.1.N := Submodule.smul_mem _ t0 hx0
  have hfe1 : d.1.f P e1 = 1 := by
    rw [hd.f_smul P t0 x0 (le_locP _ _ hx0), mul_comm, hb]
  have hBlat : Submodule.IsLattice E (d.1.kerAt P) := by
    obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.1.ne_bot
    exact lattice_of_smul hd.lat hd.lat (fun x hx => ((hd.mem_kerAt P x).1 hx).1) hp0
      fun x hx => hd.smul_mem_kerAt P hp hx
  have hqe : q • e1 ∈ d.1.kerAt P := hd.smul_mem_kerAt P hq he1
  have hpair : ∀ w ∈ dual (hStd E n) (d.1.kerAt P), ∀ y ∈ d.1.kerAt P,
      hStd E n w y ∈ (1 : Submodule (𝓞 E) E) := fun w hw y hy =>
    hStd_mem_one_symm ((mem_dual _ w).1 hw y hy)

  have hex : ∃ w ∈ dual (hStd E n) (d.1.kerAt P), ∃ r : 𝓞 E, r ∉ P.1.asIdeal ∧
      algebraMap (𝓞 E) E r = hStd E n w (q • e1) := by
    by_contra H
    push Not at H
    have hkey : q • e1 ∈ P.1.asIdeal • d.1.kerAt P := by
      refine neighbourConstruct_key (K := E) P.1.asIdeal P.1.ne_bot _ _ fun a ha => ?_
      rw [← dual_dual hBlat, mem_dual]
      intro w hw
      obtain ⟨r, hr⟩ := Submodule.mem_one.1 (hpair w hw _ hqe)
      have hrP : r ∈ P.1.asIdeal := by
        by_contra hrP
        exact H w hw r hrP hr
      rw [LinearMap.map_smul, smul_eq_mul, ← hr, mul_comm]
      exact Submodule.mem_one.2 (neighbourConstruct_mem_inv.1 ha r hrP)
    obtain ⟨a, ha, r, hr, har⟩ := exists_inv_unif P.1 hq hq2
    have h1 := inv_smul_mem ha hkey
    have e2 : a • (q • e1) = r • e1 := by
      rw [← algebraMap_smul E q e1, smul_smul, mul_comm, har, algebraMap_smul]
    rw [e2] at h1
    have h2 := ((hd.mem_kerAt P _).1 h1).2
    rw [hd.f_smul P r e1 (le_locP _ _ he1), hfe1, mul_one] at h2
    exact hr (Ideal.Quotient.eq_zero_iff_mem.1 h2)
  obtain ⟨w0, hw0, r, hr, hrw⟩ := hex
  obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv (mk_ne_zero hr)
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective b
  set w := cO E t • w0 with hwdef
  have hw : w ∈ dual (hStd E n) (d.1.kerAt P) := Submodule.smul_mem _ _ hw0
  have hwq : hStd E n w (q • e1) = algebraMap (𝓞 E) E (t * r) := by
    rw [hwdef, hStd_osmul_left, cO_cO, LinearMap.map_smul_of_tower, ← hrw, Algebra.smul_def, map_mul]
  obtain ⟨-, -, -, hloc⟩ := hd.dnN_spec P hP.ne
  have hint : ∀ y ∈ localization₂ P.1.asIdeal (d.1.dnN P), IntAt P.1 (hStd E n w y) := by
    intro y hy
    rw [hloc] at hy
    obtain ⟨s, hs, hsy⟩ := (mem_locP _ _ _).1 hy
    obtain ⟨r', hr'⟩ := Submodule.mem_one.1 (hpair w hw _ hsy)
    exact ⟨r', s, hs, by rw [hr', LinearMap.map_smul_of_tower, Algebra.smul_def]⟩
  let f' : Sp E n → 𝓞 E ⧸ P.1.asIdeal := fun y =>
    if y ∈ localization₂ P.1.asIdeal (d.1.dnN P) then redP P.1 (hStd E n w y) else 0
  have hf' : ∀ y ∈ localization₂ P.1.asIdeal (d.1.dnN P), f' y = redP P.1 (hStd E n w y) := fun y hy =>
    if_pos hy
  have hBle : d.1.kerAt P ≤ localization₂ P.1.asIdeal (d.1.dnN P) := fun y hy =>
    le_locP _ _ ((le_sup_left : d.1.kerAt P ≤ d.1.dnN P) hy)
  have hf'q : f' (q • e1) = 1 := by
    rw [hf' _ (hBle hqe), hwq, reduction_coe, map_mul, mul_comm, hb]
  have f_add : ∀ x ∈ localization₂ P.1.asIdeal (d.1.dnN P), ∀ y ∈ localization₂ P.1.asIdeal (d.1.dnN P),
      f' (x + y) = f' x + f' y := by
    intro x hx y hy
    rw [hf' _ hx, hf' _ hy, hf' _ (Submodule.add_mem _ hx hy), map_add]
    exact reduction_add (hint x hx) (hint y hy)
  have f_smul : ∀ (a : 𝓞 E), ∀ x ∈ localization₂ P.1.asIdeal (d.1.dnN P),
      f' (a • x) = Ideal.Quotient.mk P.1.asIdeal a * f' x := by
    intro a x hx
    rw [hf' _ hx, hf' _ (Submodule.smul_mem _ a hx), LinearMap.map_smul_of_tower]
    exact redP_osmul a (hint x hx)
  have hok : (d.1.dn P f').Ok := hd.dn P hP f_add f_smul (fun x hx => if_neg hx)
    ⟨q • e1, (le_sup_left : d.1.kerAt P ≤ d.1.dnN P) hqe, by rw [hf'q]; exact one_ne_zero⟩
  have hfP : (d.1.dn P f').f P = f' := by simp [Deco.dn]
  refine ⟨⟨d.1.dn P f', hok⟩, ?_, ?_⟩
  · change d.1.dn P f' = d.1.dn P ((d.1.dn P f').f P)
    rw [hfP]
  · intro e he hfe
    change (d.1.dn P f').f P (q • e) = 1
    rw [hfP]
    have hb' : e - e1 ∈ d.1.kerAt P := by
      rw [hd.mem_kerAt]
      refine ⟨Submodule.sub_mem _ he he1, ?_⟩
      have e3 : e - e1 = e + (-1 : 𝓞 E) • e1 := by rw [neg_smul, one_smul, sub_eq_add_neg]
      rw [e3, hd.f_add P e (le_locP _ _ he) _ (le_locP _ _ (Submodule.smul_mem _ _ he1)),
        hd.f_smul P _ e1 (le_locP _ _ he1), hfe, hfe1]
      simp
    have e4 : q • e = q • (e - e1) + q • e1 := by rw [← smul_add, sub_add_cancel]
    rw [e4, f_add _ (Submodule.smul_mem _ q (hBle hb')) _ (hBle hqe), f_smul q _ (hBle hb'), hf'q,
      Ideal.Quotient.eq_zero_iff_mem.2 hq, zero_mul, zero_add]

end DnNonempty

end Formalism.L2.Col
