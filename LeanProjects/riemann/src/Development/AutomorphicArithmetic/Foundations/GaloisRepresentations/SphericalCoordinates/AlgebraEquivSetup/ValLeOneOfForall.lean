import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.ApartOfNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMaxCompactGLOfCommuteEtaleCharpolyBounded

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.LKRes
open GlobalTheory.SplitPts (conjE)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap)
open GlobalTheory.LFun (KGL)
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct

namespace UpperTheory.Gal.W2.Seed

private theorem den_of_norm {p : ℕ} [Fact p.Prime] {c : ℚ} (h : ‖(c : ℚ_[p])‖ ≤ 1) : ¬ p ∣ c.den := by
  intro hd
  have h1 : ‖((c.den : ℕ) : ℚ_[p])‖ < 1 := Padic.norm_natCast_lt_one_iff.2 hd
  have hn : ¬ p ∣ c.num.natAbs := fun hn =>
    (Fact.out : p.Prime).one_lt.ne' (Nat.eq_one_of_dvd_coprimes c.reduced hn hd)
  have hn1 : ‖((c.num.natAbs : ℕ) : ℚ_[p])‖ = 1 := by
    have h0 : ‖((c.num.natAbs : ℕ) : ℤ_[p])‖ = 1 :=
      PadicInt.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hn)
    rw [← PadicInt.coe_natCast]
    exact h0
  have h2 : ‖(c.num : ℚ_[p])‖ = 1 := by
    rcases Int.natAbs_eq c.num with e | e <;> rw [e] <;> simpa using hn1
  have h3 : (c : ℚ_[p]) * (c.den : ℚ_[p]) = c.num := by exact_mod_cast Rat.mul_den_eq_num c
  have h4 := congrArg norm h3
  rw [norm_mul, h2] at h4
  nlinarith [norm_nonneg (c : ℚ_[p]), norm_nonneg ((c.den : ℕ) : ℚ_[p])]

private theorem val_rat_le {p : ℕ} [Fact p.Prime] {E : Type} [Field E] [NumberField E] (w : Plc E)
    (hw : (p : 𝓞 E) ∈ w.asIdeal) {c : ℚ} (h : ‖(c : ℚ_[p])‖ ≤ 1) : w.valuation E (algebraMap ℚ E c) ≤ 1 := by
  have hd := den_of_norm h
  have hc : algebraMap ℚ E c = algebraMap (𝓞 E) E (c.num : 𝓞 E) / algebraMap (𝓞 E) E (c.den : 𝓞 E) := by
    simp only [eq_ratCast, map_intCast, map_natCast]
    exact Rat.cast_def c
  have hden : (c.den : 𝓞 E) ∉ w.asIdeal := by
    intro hm
    have hcop : Nat.Coprime p c.den := ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hd)
    obtain ⟨a, b, hab⟩ : IsCoprime (p : ℤ) (c.den : ℤ) := Nat.isCoprime_iff_coprime.2 hcop
    have : (1 : 𝓞 E) ∈ w.asIdeal := by
      have e : (1 : 𝓞 E) = (a : 𝓞 E) * p + (b : 𝓞 E) * c.den := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) hab.symm
      rw [e]
      exact add_mem (Ideal.mul_mem_left _ _ hw) (Ideal.mul_mem_left _ _ hm)
    exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)
  have h1 : w.valuation E (algebraMap (𝓞 E) E (c.den : 𝓞 E)) = 1 :=
    le_antisymm (w.valuation_le_one _) (not_lt.1 fun hlt => hden ((w.valuation_lt_one_iff_mem _).1 hlt))
  rw [hc, map_div₀, h1, div_one]
  exact w.valuation_le_one _

private theorem mem_v_iff {p : ℕ} [Fact p.Prime] (x : PadicAlgCl p) :
    x ∈ (PadicAlgCl.valued p).v.valuationSubring ↔ ‖x‖ ≤ 1 := by
  rw [Valuation.mem_valuationSubring_iff]
  show ‖x‖₊ ≤ 1 ↔ _
  exact Iff.rfl

private theorem val_le_one_of_forall {p : ℕ} [Fact p.Prime] {E : Type} [Field E] [NumberField E] (w : Plc E)
    (hw : (p : 𝓞 E) ∈ w.asIdeal) {x : E} (h : ∀ τ : E →+* PadicAlgCl p, ‖τ x‖ ≤ 1) : w.valuation E x ≤ 1 := by
  classical
  have hroots : ∀ r ∈ ((minpoly ℚ x).map (algebraMap ℚ (PadicAlgCl p))).roots, ‖r‖ ≤ 1 := by
    intro r hr
    have h0 : Polynomial.aeval r (minpoly ℚ x) = 0 := by
      have := (Polynomial.mem_roots'.1 hr).2
      simpa [Polynomial.IsRoot, Polynomial.eval_map_algebraMap] using this
    obtain ⟨φ, hφ⟩ := IntermediateField.exists_algHom_of_splits_of_aeval
      (fun s => ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩) h0
    rw [← hφ]
    exact h φ.toRingHom
  have hlift : (minpoly ℚ x).map (algebraMap ℚ (PadicAlgCl p)) ∈
      Polynomial.lifts ((PadicAlgCl.valued p).v.valuationSubring.subtype) := by
    have hm : ((minpoly ℚ x).map (algebraMap ℚ (PadicAlgCl p))).Monic :=
      (minpoly.monic (Algebra.IsIntegral.isIntegral x)).map _
    rw [(IsAlgClosed.splits _).eq_prod_roots_of_monic hm]
    refine Subsemiring.multiset_prod_mem _ _ ?_
    intro f hf
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hf
    exact Polynomial.mem_lifts _ |>.2 ⟨Polynomial.X - Polynomial.C ⟨r, (mem_v_iff r).2 (hroots r hr)⟩, by simp⟩
  have hco : ∀ n, ‖(((minpoly ℚ x).coeff n : ℚ) : ℚ_[p])‖ ≤ 1 := by
    intro n
    obtain ⟨a, ha⟩ := (Polynomial.lifts_iff_coeff_lifts _).1 hlift n
    have h1 := (mem_v_iff _).1 a.2
    have h2 : (a : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) (((minpoly ℚ x).coeff n : ℚ) : ℚ_[p]) := by
      have : (a : PadicAlgCl p) = _ := ha
      rw [this, Polynomial.coeff_map]
      simp
    rw [h2, PadicAlgCl.norm_extends] at h1
    exact h1
  have hlift2 : (minpoly ℚ x).map (algebraMap ℚ E) ∈ Polynomial.lifts ((w.valuation E).valuationSubring.subtype) := by
    refine (Polynomial.lifts_iff_coeff_lifts _).2 fun n => ?_
    rw [Polynomial.coeff_map]
    exact ⟨⟨_, (Valuation.mem_valuationSubring_iff _ _).2 (val_rat_le w hw (hco n))⟩, rfl⟩
  obtain ⟨q, hq, -, hmon⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift2
    ((minpoly.monic (Algebra.IsIntegral.isIntegral x)).map _)
  have hi : IsIntegral (w.valuation E).valuationSubring x := by
    refine ⟨q, hmon, ?_⟩
    have : Polynomial.eval₂ (algebraMap (w.valuation E).valuationSubring E) x q =
        Polynomial.eval x (q.map ((w.valuation E).valuationSubring.subtype)) := by
      rw [Polynomial.eval_map]; rfl
    rw [this, hq, Polynomial.eval_map_algebraMap, minpoly.aeval]
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  rw [← hy]
  exact (Valuation.mem_valuationSubring_iff _ _).1 y.2

private theorem omega_root {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) :
    (A.ω : E) ^ 2 - (A.tr : E) * (A.ω : E) + (A.nm : E) = 0 := by
  have h1 : (A.ω : E) + IsCMField.complexConj E (A.ω : E) = (A.tr : E) := by
    have h := congrArg (fun z : 𝓞 E => (z : E)) A.tr_eq
    simpa [A.bar_eq] using h
  have h2 : (A.ω : E) * IsCMField.complexConj E (A.ω : E) = (A.nm : E) := by
    have h := congrArg (fun z : 𝓞 E => (z : E)) A.nm_eq
    simpa [A.bar_eq] using h
  linear_combination (A.ω : E) * h1 - h2

private theorem omega_not_rat {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (q : ℚ) :
    (A.ω : E) ≠ algebraMap ℚ E q := by
  intro h
  have h0 := omega_root A
  rw [h] at h0
  have h1 : q ^ 2 - (A.tr : ℚ) * q + (A.nm : ℚ) = 0 := by
    apply (algebraMap ℚ E).injective
    simpa using h0
  have hd : ((A.tr : ℚ)) ^ 2 - 4 * (A.nm : ℚ) < 0 := by exact_mod_cast A.disc_neg
  nlinarith [sq_nonneg (2 * q - (A.tr : ℚ))]

private theorem span_omega {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (K : Subfield E)
    (hK : Module.finrank ℚ K = 2) (h : (A.ω : E) ∈ K) (x : K) :
    ∃ a b : ℚ, x = algebraMap ℚ K a + algebraMap ℚ K b * ⟨A.ω, h⟩ := by
  have hli : LinearIndependent ℚ ![(1 : K), ⟨A.ω, h⟩] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have hE : algebraMap ℚ E a + algebraMap ℚ E b * (A.ω : E) = 0 := by
      have := congrArg (fun z : K => (z : E)) hab
      simpa [Algebra.smul_def] using this
    have hb : b = 0 := by
      by_contra hb
      apply omega_not_rat A (-a / b)
      have hb' : algebraMap ℚ E b ≠ 0 := by simpa using hb
      rw [map_div₀, map_neg]
      field_simp
      linear_combination hE
    subst hb
    refine ⟨?_, rfl⟩
    have : algebraMap ℚ E a = 0 := by simpa using hE
    simpa using this
  have hspan : Submodule.span ℚ (Set.range ![(1 : K), ⟨A.ω, h⟩]) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simp [hK])
  have hx : x ∈ Submodule.span ℚ (Set.range ![(1 : K), ⟨A.ω, h⟩]) := hspan ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).1 hx
  refine ⟨c 0, c 1, ?_⟩
  rw [← hc]
  simp [Fin.sum_univ_two, Algebra.smul_def]

private theorem lies_or {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) {p : ℕ} [Fact p.Prime]
    (P : A.AtP p) (τ : E →+* PadicAlgCl p) :
    LiesOver P.Kq P.u τ ∨ LiesOver P.Kq P.u (τ.comp (cj E)) := by
  obtain ⟨h, -⟩ := P.ρp_eq
  have key : ∀ f : E →+* PadicAlgCl p, f (A.ω : E) = algebraMap ℚ_[p] (PadicAlgCl p) (P.u ⟨A.ω, h⟩) →
      LiesOver P.Kq P.u f := by
    intro f hf x
    obtain ⟨a, b, rfl⟩ := span_omega A P.Kq P.hKq.1 h x
    simp only [map_add, map_mul, Subfield.coe_add, Subfield.coe_mul, hf]
    simp
  have hr : (algebraMap ℚ_[p] (PadicAlgCl p) (P.u ⟨A.ω, h⟩)) ^ 2 -
      (A.tr : PadicAlgCl p) * algebraMap ℚ_[p] (PadicAlgCl p) (P.u ⟨A.ω, h⟩) + (A.nm : PadicAlgCl p) = 0 := by
    have h0 : (⟨A.ω, h⟩ : P.Kq) ^ 2 - (A.tr : P.Kq) * ⟨A.ω, h⟩ + (A.nm : P.Kq) = 0 := by
      apply Subtype.ext
      simpa using omega_root A
    have h1 := congrArg ((algebraMap ℚ_[p] (PadicAlgCl p)).comp P.u) h0
    simp only [map_add, map_sub, map_mul, map_pow, map_intCast, map_zero] at h1
    exact h1
  have ht : (τ (A.ω : E)) ^ 2 - (A.tr : PadicAlgCl p) * τ (A.ω : E) + (A.nm : PadicAlgCl p) = 0 := by
    have h1 := congrArg τ (omega_root A)
    simpa using h1
  have hfac : (τ (A.ω : E) - algebraMap ℚ_[p] (PadicAlgCl p) (P.u ⟨A.ω, h⟩)) *
      (τ (A.ω : E) + algebraMap ℚ_[p] (PadicAlgCl p) (P.u ⟨A.ω, h⟩) - (A.tr : PadicAlgCl p)) = 0 := by
    linear_combination ht - hr
  rcases mul_eq_zero.1 hfac with e | e
  · exact Or.inl (key τ (sub_eq_zero.1 e))
  · refine Or.inr (key _ ?_)
    have h1 : (A.ω : E) + cj E (A.ω : E) = (A.tr : E) := by
      have h := congrArg (fun z : 𝓞 E => (z : E)) A.tr_eq
      simpa [A.bar_eq] using h
    have h2 := congrArg τ h1
    simp only [map_add, map_intCast] at h2
    simp only [RingHom.comp_apply]
    linear_combination h2 - e

private theorem mulKQ_inclK {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (a : K) :
    (mulKQ K 1) (inclK p K 1 a) = (a : PadicAlgCl p) := by
  show Algebra.TensorProduct.lift K.val (Qr p 1).val _ (a ⊗ₜ[ℚ_[p]] (1 : Qr p 1)) = _
  rw [Algebra.TensorProduct.lift_tmul]
  simp

private theorem norm_of_mem_intKQ {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    {z : KQ p K 1} (hz : z ∈ intKQ p K 1) : ‖mulKQ K 1 z‖ ≤ 1 := by
  have hle : intKQ p K 1 ≤ ((PadicAlgCl.valued p).v.valuationSubring.toSubring).comap (mulKQ K 1).toRingHom := by
    refine (Subring.closure_le).2 ?_
    rintro _ (⟨a, rfl⟩ | ⟨b, rfl⟩)
    · have h : (mulKQ K 1) (inclK p K 1 a) = ((a : K) : PadicAlgCl p) := by
        show Algebra.TensorProduct.lift K.val (Qr p 1).val _ ((a : K) ⊗ₜ[ℚ_[p]] (1 : Qr p 1)) = _
        rw [Algebra.TensorProduct.lift_tmul]
        simp
      show (mulKQ K 1) (inclK p K 1 a) ∈ (PadicAlgCl.valued p).v.valuationSubring
      rw [h]
      exact a.2
    · have h : (mulKQ K 1) (inclQ p K 1 b) = ((b : Qr p 1) : PadicAlgCl p) := by
        show Algebra.TensorProduct.lift K.val (Qr p 1).val _ ((1 : K) ⊗ₜ[ℚ_[p]] (b : Qr p 1)) = _
        rw [Algebra.TensorProduct.lift_tmul]
        simp
      show (mulKQ K 1) (inclQ p K 1 b) ∈ (PadicAlgCl.valued p).v.valuationSubring
      rw [h]
      exact b.2
  exact (mem_v_iff _).1 (hle hz)

private theorem norm_galois {p : ℕ} [Fact p.Prime] (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (z : PadicAlgCl p) :
    ‖σ z‖ = ‖z‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm, minpoly.algEquiv_eq]

private theorem norm_of_Kint {p : ℕ} [Fact p.Prime] (t : ℚ_[p]ˣ)
    (h : (GeneralLinearGroup.scalar (Fin 1)) (Units.map (algebraMap ℚ_[p] (Qr p 1)).toMonoidHom t) ∈
      GlobalTheory.LKLoc.Kint p (Q0 p) 1 1) : ‖(t : ℚ_[p])‖ ≤ 1 := by
  obtain ⟨k, hk⟩ := h
  have e : (((k.val 0 0 : GlobalTheory.LKLoc.intR p (Q0 p) 1) : Qr p 1)) = algebraMap ℚ_[p] (Qr p 1) (t : ℚ_[p]) := by
    have := congrArg (fun g : GL (Fin 1) (Qr p 1) => g.val 0 0) hk
    simpa using this
  have h1 : ((((k.val 0 0 : GlobalTheory.LKLoc.intR p (Q0 p) 1) : Qr p 1)) : PadicAlgCl p) ∈
      (PadicAlgCl.valued p).v.valuationSubring := (k.val 0 0).2
  rw [e, mem_v_iff] at h1
  have h2 : (((algebraMap ℚ_[p] (Qr p 1) (t : ℚ_[p])) : Qr p 1) : PadicAlgCl p) =
      algebraMap ℚ_[p] (PadicAlgCl p) (t : ℚ_[p]) := rfl
  rw [h2, PadicAlgCl.norm_extends] at h1
  exact h1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime]

private theorem inv_hyp (S : Setup A n p) (y : Gam0 E n)
    (hy : inclG S.G 1 (locC S.G (y : GL (Fin n) E × ℚˣ)) ∈ LocalSmoothExtension.Kp S.G) :
    inclG S.G 1 (locC S.G ((y⁻¹ : Gam0 E n) : GL (Fin n) E × ℚˣ)) ∈ LocalSmoothExtension.Kp S.G := by
  have e : locC S.G ((y⁻¹ : Gam0 E n) : GL (Fin n) E × ℚˣ) = (locC S.G (y : GL (Fin n) E × ℚˣ))⁻¹ :=
    map_inv (locC S.G) (y.1 : S.G.Cˣ × ℚˣ)
  rw [e, map_inv]
  exact (LocalSmoothExtension.Kp S.G).inv_mem hy

private theorem sim_norm (S : Setup A n p) (y : Gam0 E n)
    (hy : inclG S.G 1 (locC S.G (y : GL (Fin n) E × ℚˣ)) ∈ LocalSmoothExtension.Kp S.G) :
    ‖(((y.1.2 : ℚˣ) : ℚ) : ℚ_[p])‖ ≤ 1 := by
  have a1 := norm_of_Kint (Units.map (algebraMap ℚ ℚ_[p]).toMonoidHom y.1.2) hy.1
  simpa using a1

private theorem entry_norm (S : Setup A n p) (y : Gam0 E n)
    (hy : inclG S.G 1 (locC S.G (y : GL (Fin n) E × ℚˣ)) ∈ LocalSmoothExtension.Kp S.G) (i : Fin S.P.m) (j l : Fin n) :
    ‖S.P.emb i (y.1.1.val j l)‖ ≤ 1 := by
  let i' : Fin S.G.m := i
  obtain ⟨k, hk⟩ := hy.2 i' (Set.mem_univ i')
  let j' : Fin S.G.n := j
  let l' : Fin S.G.n := l
  have e := congrArg (fun g : GL (Fin S.G.n) (KQ p (S.G.Fw i') 1) => g.val j' l') hk
  have h1 := norm_of_mem_intKQ (S.G.Fw i') (k.val j' l').2
  let a : S.G.Fw i' := embOf (S.P.emb i) (y.1.1.val j l)
  have e' : ((k.val j' l' : intKQ p (S.G.Fw i') 1) : KQ p (S.G.Fw i') 1) = inclK p (S.G.Fw i') 1 a := e
  rw [e', mulKQ_inclK] at h1
  exact h1

private theorem conj_entry (y : Gam0 E n) (j l : Fin n) :
    cj E (y.1.1.val j l) = algebraMap ℚ E (y.1.2 : ℚ) * (y.1.1)⁻¹.val l j := by
  have h : (y.1.1.val.map (conjE E).toRingHom)ᵀ * y.1.1.val =
      algebraMap ℚ E (y.1.2 : ℚ) • (1 : Matrix (Fin n) (Fin n) E) := y.2.1
  have h3 : (y.1.1.val.map (conjE E).toRingHom)ᵀ = algebraMap ℚ E (y.1.2 : ℚ) • (y.1.1)⁻¹.val := by
    calc (y.1.1.val.map (conjE E).toRingHom)ᵀ
        = (y.1.1.val.map (conjE E).toRingHom)ᵀ * (y.1.1.val * (y.1.1)⁻¹.val) := by
          rw [Units.mul_inv, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, h, smul_mul_assoc, Matrix.one_mul]
  have := congrFun (congrFun h3 l) j
  simpa using this

private theorem over_norm (S : Setup A n p) (y : Gam0 E n)
    (hy : inclG S.G 1 (locC S.G (y : GL (Fin n) E × ℚˣ)) ∈ LocalSmoothExtension.Kp S.G) (τ : E →+* PadicAlgCl p)
    (hτ : LiesOver S.P.Kq S.P.u τ) (j l : Fin n) : ‖τ (y.1.1.val j l)‖ ≤ 1 := by
  obtain ⟨i, σ, rfl⟩ := S.P.emb_all τ hτ
  show ‖σ (S.P.emb i (y.1.1.val j l))‖ ≤ 1
  rw [norm_galois]
  exact entry_norm S y hy i j l

private theorem rat_norm {E : Type} [Field E] {p : ℕ} [Fact p.Prime] (τ : E →+* PadicAlgCl p) [Algebra ℚ E] (c : ℚ) :
    ‖τ (algebraMap ℚ E c)‖ = ‖(c : ℚ_[p])‖ := by
  have : τ (algebraMap ℚ E c) = algebraMap ℚ_[p] (PadicAlgCl p) (c : ℚ_[p]) := by simp
  rw [this, PadicAlgCl.norm_extends]

private theorem all_norm (S : Setup A n p) (y : Gam0 E n)
    (hy : inclG S.G 1 (locC S.G (y : GL (Fin n) E × ℚˣ)) ∈ LocalSmoothExtension.Kp S.G) (τ : E →+* PadicAlgCl p) (j l : Fin n) :
    ‖τ (y.1.1.val j l)‖ ≤ 1 := by
  rcases lies_or A S.P τ with h | h
  · exact over_norm S y hy τ h j l
  · have hy' := inv_hyp S y hy
    have e : y.1.1.val j l = cj E (cj E (y.1.1.val j l)) := by
      simp [IsCMField.complexConj_apply_apply]
    have h1 := over_norm S _ hy' _ h l j
    have h2 : τ (y.1.1.val j l) = τ (algebraMap ℚ E (y.1.2 : ℚ)) * (τ.comp (cj E)) ((y⁻¹ : Gam0 E n).1.1.val l j) := by
      rw [e, conj_entry y j l, map_mul, map_mul]
      simp only [RingHom.comp_apply]
      rw [show cj E (algebraMap ℚ E (y.1.2 : ℚ)) = algebraMap ℚ E (y.1.2 : ℚ) by simp]
      rfl
    rw [h2, norm_mul, rat_norm]
    exact mul_le_one₀ (sim_norm S y hy) (norm_nonneg _) h1

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in
private theorem mem_KGL_of_entries {w : Plc E} {g : GL (Fin n) (w.adicCompletion E)}
    (h1 : ∀ i j, Valued.v (g.val i j) ≤ 1) (h2 : ∀ i j, Valued.v (g⁻¹.val i j) ≤ 1) : g ∈ KGL w n :=
  GlobalTheory.StabInt.mem_KGL_of_mem_integralGL ((GroundTheory.Automorphic.GLnLocal.mem_integralGL_iff _ _).2
    ⟨fun i j => (GlobalTheory.StabInt.mem_O_iff _).2 (h1 i j), fun i j => (GlobalTheory.StabInt.mem_O_iff _).2 (h2 i j)⟩)

private theorem val_coe {K : Type} [Field K] [NumberField K] (w : Plc K) (x : K) :
    Valued.v (algebraMap K (w.adicCompletion K) x) = w.valuation K x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x

private def toC {K : Type} [Field K] [NumberField K] (w : Plc K) : K →+* w.adicCompletion K :=
  algebraMap K (w.adicCompletion K)

private theorem val_toC {K : Type} [Field K] [NumberField K] (w : Plc K) (x : K) :
    Valued.v (toC w x) = w.valuation K x := val_coe w x

theorem pPInt : PInt := by
  intro E _ _ _ A n p _ S y hy
  refine ⟨fun w hw => ?_, fun v hv => ?_⟩
  · refine mem_KGL_of_entries (fun j l => ?_) (fun j l => ?_)
    · have e : (comp w (rat y)).val j l = algebraMap E (w.adicCompletion E) (y.1.1.val j l) := rfl
      rw [e, val_coe]
      exact val_le_one_of_forall w hw fun τ => all_norm S y hy τ j l
    · have e : (comp w (rat y))⁻¹.val j l = algebraMap E (w.adicCompletion E) ((y⁻¹ : Gam0 E n).1.1.val j l) := by
        rw [← map_inv, ← map_inv]
        rfl
      rw [e, val_coe]
      exact val_le_one_of_forall w hw fun τ => all_norm S _ (inv_hyp S y hy) τ j l
  · have e0 : ((sim (rat y) : AfQˣ) : AfQ) = algebraMap ℚ AfQ (y.1.2 : ℚ) := rfl
    have e : ((sim (rat y) : AfQˣ) : AfQ) v = toC v (y.1.2 : ℚ) := by
      rw [e0]
      exact RingHom.congr_fun (Subsingleton.elim ((pLoc ℚ v).comp (algebraMap ℚ AfQ)) (toC v)) _
    rw [e, val_toC]
    have a1 : v.valuation ℚ (y.1.2 : ℚ) ≤ 1 := by
      simpa using val_rat_le v hv (sim_norm S y hy)
    have a2 : v.valuation ℚ ((y.1.2 : ℚ))⁻¹ ≤ 1 := by
      have := val_rat_le v hv (sim_norm S _ (inv_hyp S y hy))
      simpa using this
    rw [map_inv₀] at a2
    refine le_antisymm a1 ?_
    exact (inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (Units.ne_zero _)))).1 a2

end UpperTheory.Gal.W2.Seed
