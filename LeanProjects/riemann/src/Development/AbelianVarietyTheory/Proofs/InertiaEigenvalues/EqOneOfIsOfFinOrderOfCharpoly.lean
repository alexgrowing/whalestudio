import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharpolySmulOfProd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffProdOneSubCMulX
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ForallFieldIffForallSubgroup

noncomputable section

namespace GlobalTheory.Triple

open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction.Gen
open Formalism.L2.Host (HChar CharFrame)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
open GlobalTheory.GalChar (IsGal toQ)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE)
open GlobalTheory.TripleGal (UnrRho HkFrob)

theorem eq_one_of_isOfFinOrder_of_charpoly {K : Type} [Field K] [CharZero K] {n : ℕ} {A : GL (Fin n) K}
    (hA : IsOfFinOrder A) (hc : (A : Matrix (Fin n) (Fin n) K).charpoly = (X - 1) ^ n) : A = 1 := by
  obtain ⟨m, hm, h⟩ := isOfFinOrder_iff_pow_eq_one.1 hA
  have h1 : minpoly K (A : Matrix (Fin n) (Fin n) K) ∣ X ^ m - C 1 := minpoly.dvd _ _ (by
    rw [map_sub, map_pow, aeval_X, map_one, map_one, ← Units.val_pow_eq_pow_val, h, Units.val_one, sub_self])
  have h2 := ((separable_X_pow_sub_C (1 : K) (Nat.cast_ne_zero.2 hm.ne') one_ne_zero).squarefree.squarefree_of_dvd
    h1).isRadical n _ (hc ▸ Matrix.minpoly_dvd_charpoly _)
  have h3 := aeval_eq_zero_of_dvd_aeval_eq_zero h2 (minpoly.aeval K _)
  rw [map_sub, aeval_X, map_one, sub_eq_zero] at h3
  exact Units.ext h3

theorem charpolyRev_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ} (M : Matrix (Fin n) (Fin n) R) :
    M.charpolyRev.map f = (M.map f).charpolyRev := by
  rw [Matrix.charpolyRev, Matrix.charpolyRev, ← coe_mapRingHom, RingHom.map_det]
  congr 1
  ext a b : 2
  by_cases h : a = b <;> simp [h]

theorem eval_charpolyRev {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (z : R) :
    M.charpolyRev.eval z = (1 - z • M).det := by
  rw [Matrix.charpolyRev, ← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext a b : 2
  by_cases h : a = b <;> simp [h, mul_comm z]

theorem charpolyRev_of_inv {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ} (h : A * B = 1) {m : Multiset ℂ}
    (hB : B.charpoly = (m.map fun a => X - C a).prod) : A.charpolyRev = (m.map fun a => 1 - C a⁻¹ * X).prod := by
  have e : ∀ z : ℂ, (Matrix.scalar (Fin n) z - B).det = (m.map fun a => z - a).prod := fun z => by
    rw [← Matrix.eval_charpoly, hB, eval_multiset_prod, Multiset.map_map]
    simp
  have h0 : (Matrix.scalar (Fin n) 0 - B).det ≠ 0 := by
    rw [map_zero, zero_sub, Matrix.det_neg]
    exact mul_ne_zero (by simp) (Matrix.isUnit_det_of_left_inverse h).ne_zero
  apply Polynomial.funext
  intro z
  refine mul_right_cancel₀ h0 ?_
  have e1 : (1 - z • A) * (Matrix.scalar (Fin n) 0 - B) = Matrix.scalar (Fin n) z - B := by
    rw [map_zero, zero_sub, mul_neg, sub_mul, one_mul, smul_mul_assoc, h, neg_sub, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]
  rw [eval_charpolyRev, ← Matrix.det_mul, e1, e, e, eval_multiset_prod, Multiset.map_map, ← Multiset.prod_map_mul]
  refine congrArg _ (Multiset.map_congr rfl fun a ha => ?_)
  have ha0 : a ≠ 0 := fun h1 => h0 (by
    rw [e]
    exact Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨a, ha, by rw [h1, sub_self]⟩))
  simp only [Function.comp_apply, eval_sub, eval_one, eval_mul, eval_C, eval_X]
  field_simp
  ring

theorem sum_coeff_charpolyRev {R : Type} [CommRing R] [Nontrivial R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) :
    ∑ k ∈ Finset.range (n + 1), M.charpolyRev.coeff k = (1 - M).det := by
  have h : M.charpolyRev.natDegree < n + 1 := by
    rw [← Matrix.reverse_charpoly, Nat.lt_succ_iff]
    exact (reverse_natDegree_le _).trans (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin])
  have := eval_eq_sum_range' h 1
  simp only [one_pow, mul_one, eval_charpolyRev, one_smul] at this
  exact this.symm

variable {D : D7} {X : NTw D.R D.host D.what₂ D.LL0 D.nd} {i : X.Tw}

theorem unramified_of_isGaloisRepOf {a : ℕ} {π : D.naut.CG a} {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ}
    {r : GalE D →* GL (Fin a) (Qbar l)} (h : IsGaloisRepOf D π l ι r) {w : PlE D.host} (hl : w ∉ placesOver D.host.E l)
    (hu : D.naut.unr (D.naut.locG π w)) {A : ValuationSubring D.nd.Om} (hA : IsPlaceOver (F := D.host.E) A w)
    {σ : GalE D} (hσ : σ ∈ Ine (F := D.host.E) A) : r σ = 1 := by
  refine GlobalTheory.PointIrredCompare.Ine_le_of_normal (D.nd.plOm.2 w) hA r.ker (fun τ hτ => ?_) hσ
  obtain ⟨h1, h2, -⟩ := h.2.2 w hl
  obtain ⟨h3, h4⟩ := (D.naut.unr_iff_ine _).1 ((D.naut.unr_tw _ ((1 - (a : ℝ)) / 2)).2 hu)
  refine eq_one_of_isOfFinOrder_of_charpoly (finite_zpowers.1 ((h2.1 h3).subset ?_)) ?_
  · rintro _ ⟨n, rfl⟩
    exact ⟨τ ^ n, zpow_mem hτ n, map_zpow r τ n⟩
  · apply Polynomial.map_injective ι.toRingHom ι.injective
    rw [h1 τ hτ, h4 τ hτ, D.naut.lpDim_tw, D.naut.locG_dim]
    simp

theorem cyclotomicEps_eq_one_on_inertia {v : PlE D.host} (hv : v ∉ placesOver D.host.E (X.l i)) {A : ValuationSubring D.nd.Om}
    (hA : IsPlaceOver (F := D.host.E) A v) {σ : GalE D} (hσ : σ ∈ Ine (F := D.host.E) A) : eps0 X i σ = 1 := by
  have h1 : cycZ D.host.E D.nd.Om (X.l i) σ = 1 := by
    refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
    rw [cycZ_toZModPow_eq hv hA (q := 1) (fun x hx => by simpa using hσ.2 x hx) n]
    simp
  rw [eps0, MonoidHom.comp_apply, h1, map_one]

theorem cyclotomicEps_frobenius_eq_norm {v : PlE D.host} (hv : v ∉ placesOver D.host.E (X.l i)) {A : ValuationSubring D.nd.Om}
    (hA : IsPlaceOver (F := D.host.E) A v) {σ : GalE D} (hσ : IsFrob (F := D.host.E) A (normV v) σ) :
    ((eps0 X i σ : (X.O0 i)ˣ) : X.O0 i) = (normV v : ℕ) := by
  show algebraMap ℤ_[X.l i] (X.O0 i) ((cycZ D.host.E D.nd.Om (X.l i) σ : ℤ_[X.l i]ˣ) : ℤ_[X.l i]) = _
  rw [cycZ_of_isFrob hv hA hσ, map_natCast]

def twistW (s : X.Sig i) : GalE D →* (X.O0 i)ˣ := eps0 X i ^ D.R.t * (chiS i s)⁻¹

def matW (s : X.Sig i) (g : GalE D) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i) :=
  ((twistW s g : (X.O0 i)ˣ) : X.O0 i) • ((X.rhoS i s g : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i))

theorem matW_eq (s : X.Sig i) (g : GalE D) :
    matW s g = (((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) ^ D.R.t) • Tmat i s g := by
  rw [matW, Tmat, smul_smul, twistW, MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.inv_apply, Units.val_mul,
    Units.val_pow_eq_pow_val]

theorem matW_mul_inv (s : X.Sig i) (g : GalE D) : matW s g * matW s g⁻¹ = 1 := by
  rw [matW, matW, smul_mul_smul_comm, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, mul_inv_cancel, map_one,
    map_one, Units.val_one, Units.val_one, one_smul]

variable {C : CharFrame D} {art : Ideles D.host.E →* Gab D.host.E D.nd.Om} {s : X.Sig i}

section With

variable {σ : D.what₂.FT} {π : D.naut.CG D.R.r} {r : GalE D →* GL (Fin D.R.r) (Qbar (X.l i))} {ν : GalE D →* (X.O0 i)ˣ}
  {w : D.what₂.places.Pl} {red : Zbar (X.l i) →+* FbAt D w}

theorem IsTripleWith.unrRho {b : Bool} {ρ : Reading X i b} (ha : IsGlobalArtin art)
    (h : IsTripleWith C art ρ s σ π r ν w red) : UnrRho i s := by
  intro v hl hg A hA g hgI
  obtain ⟨n, hn⟩ := h.shift
  have e := h.rho g
  rw [unramified_of_isGaloisRepOf h.gal hl (h.param.unr v hg) hA hgI,
    (hn.unr_iff ha (Or.inl hl) hA).2 (shiftChar_unr C v) g hgI, Units.val_one, map_one, one_smul, Units.val_one] at e
  refine Units.ext (Matrix.map_injective (GlobalTheory.GalChar.toQ_injective ρ.κ) ?_)
  simpa using e

theorem IsTripleWith.charpolyRev_matW {ρ : Reading X i (X.side i s)} (ha : IsGlobalArtin art) (hC : IsChars C art ρ)
    (h : IsTripleWith C art ρ s σ π r ν w red) {P : PlE D.host} (hS : P ∉ X.S0 i) {B : ValuationSubring D.nd.Om}
    (hB : IsPlaceOver (F := D.host.E) B P) {g : GalE D} (hF : IsFrob (F := D.host.E) B (normV P) g⁻¹) :
    (matW s g).charpolyRev.map ρ.toC = ((satake (muBase C (X.l i) (jIdx s)) π P).map fun α =>
      1 - Polynomial.C (((normV P : ℕ) : ℂ) ^ ((D.R.r - 1) / 2) * α) * Polynomial.X).prod := by
  have hl : P ∉ placesOver D.host.E (X.l i) := fun hk => hS (X.twistExcludedPlaces_contains_residueChar i hk)
  have hg : ∀ k, P ∉ placesOver D.host.E (D.host.g k) := fun k hk => hS (X.placesOver_subset_exceptional i k hk)
  obtain ⟨n, hn⟩ := hC.chiS
  have hu := (hn.unr_iff ha (Or.inl hl) hB).1 (X.twistCharacterFamily_unramified i _ _ P hl hg (fun hk => hS (X.primes_subset_exceptional i hk)) B hB)
  have e1 := h.charpoly_frob ha hl hg hB hF
  have e2 : ρ.toC ((twistW s g⁻¹ : (X.O0 i)ˣ) : X.O0 i) =
      (((blockChar C (X.l i) (jIdx s)).val P : ℂˣ) : ℂ) * ((normV P : ℕ) : ℂ) ^ D.R.t := by
    rw [twistW, MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_pow_eq_pow_val,
      cyclotomicEps_frobenius_eq_norm hl hB hF, map_mul, map_pow, map_natCast, map_units_inv, ρ.toC_apply,
      hn.frob ha (Or.inl hl) hu hB hF, inv_inv, mul_comm]
  rw [← Matrix.charpoly_map, ← Function.comp_def (fun a => Polynomial.X - Polynomial.C a), ← Multiset.map_map] at e1
  have e3 := charpoly_smul_of_prod _ _ (ρ.toC ((twistW s g⁻¹ : (X.O0 i)ˣ) : X.O0 i)) e1
  have e4 : (matW s g⁻¹).map ρ.toC = ρ.toC ((twistW s g⁻¹ : (X.O0 i)ˣ) : X.O0 i) •
      ((X.rhoS i s g⁻¹ : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map ρ.toC := by
    ext x y
    simp [matW]
  rw [← e4, ← Function.comp_def (fun a => Polynomial.X - Polynomial.C a), ← Multiset.map_map] at e3
  have e5 : (matW s g).map ρ.toC * (matW s g⁻¹).map ρ.toC = 1 := by
    rw [← Matrix.map_mul, matW_mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [charpolyRev_map, charpolyRev_of_inv e5 e3, satake, Multiset.map_map, Multiset.map_map, Multiset.map_map]
  refine congrArg _ (Multiset.map_congr rfl fun a _ => ?_)
  simp only [Function.comp_apply]
  rw [← geometric_eigenvalue, e2, ← mul_assoc]

theorem IsTripleWith.hkFrob {ρ : Reading X i (X.side i s)} (ha : IsGlobalArtin art) (hC : IsChars C art ρ)
    (h : IsTripleWith C art ρ s σ π r ν w red) : HkFrob i s := by
  intro P hS hP g hF k hk
  obtain ⟨x, h1, h2⟩ := h.hecke k P hk hP hS
  have e := congrArg (fun p => coeff p k) (h.charpolyRev_matW ha hC hS (D.nd.plOm.2 P) hF)
  simp only [coeff_map, GlobalTheory.coeff_prod_one_sub_C_mul_X] at e
  have e2 : ((normV P : ℕ) : ℂ) ^ (k * (k - 1) / 2) * heckeVal (muBase C (X.l i) (jIdx s)) π k P =
      (((normV P : ℕ) : ℂ) ^ ((D.R.r - 1) / 2)) ^ k * (satake (muBase C (X.l i) (jIdx s)) π P).esymm k :=
    (pow_mul_heckeVal _ π P hk).trans
      (Multiset.pow_smul_esymm (((normV P : ℕ) : ℂ) ^ ((D.R.r - 1) / 2)) k (satake (muBase C (X.l i) (jIdx s)) π P)).symm
  have e3 : (-1) ^ k * ((normV P : ℕ) : X.O0 i) ^ (k * (k - 1) / 2) * x = (matW s g).charpolyRev.coeff k := by
    apply ρ.toC_injective
    rw [e, map_mul, map_mul, map_pow, map_pow, map_neg, map_one, map_natCast, h2, mul_assoc, e2, mul_assoc]
  rw [← matW_eq, ← e3, ← h1, map_mul, map_mul, map_pow, map_pow, map_neg, map_one, map_natCast]

end With

theorem notMem_of_mem_pD {v : PlE D.host} (hv : v ∈ X.pD i) :
    v ∉ placesOver D.host.E (X.l i) ∧ ∀ k, v ∉ placesOver D.host.E (D.host.g k) := by
  have h : v ∈ placesOver D.host.E (if X.l i = D.host.pde then D.host.pde' else D.host.pde) :=
    X.pD_eq i ▸ Finset.mem_coe.2 hv
  have hl : (X.l i).Prime := (X.lPrime i).out
  split_ifs at h with e
  · exact ⟨GlobalTheory.GalChar.notMem_of_ne D.host.pde'_prime hl (e ▸ D.host.pde_ne.symm) h,
      fun k => GlobalTheory.GalChar.notMem_of_ne D.host.pde'_prime (D.host.g_prime k) (D.host.pde_ne_g k).2 h⟩
  · exact ⟨GlobalTheory.GalChar.notMem_of_ne D.host.pde_prime hl (Ne.symm e) h,
      fun k => GlobalTheory.GalChar.notMem_of_ne D.host.pde_prime (D.host.g_prime k) (D.host.pde_ne_g k).1 h⟩

theorem matW_of_mem_Ine (hu : UnrRho i s) {v : PlE D.host} (hl : v ∉ placesOver D.host.E (X.l i))
    (hg : ∀ k, v ∉ placesOver D.host.E (D.host.g k)) {A : ValuationSubring D.nd.Om}
    (hA : IsPlaceOver (F := D.host.E) A v) {g : GalE D} (hI : g ∈ Ine (F := D.host.E) A) :
    matW s g = (((chiS i s g)⁻¹ : (X.O0 i)ˣ) : X.O0 i) • (1 : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) := by
  rw [matW_eq, Tmat, cyclotomicEps_eq_one_on_inertia hl hA hI, hu v hl hg A hA g hI, Units.val_one, Units.val_one, one_pow, one_smul]

variable {Y : NExp D.R D.host D.what₂ D.LL0 D.nd X}

theorem IsTripleOf.unrRho (h : IsTripleOf Y) (hi : X.NonzeroIndexPlace i) (s : X.Sig i) : UnrRho i s :=
  let ⟨_, _, h⟩ := h
  let ⟨_, _, _, _, _, _, _, _, h2⟩ := h.triple hi s
  h2.unrRho h.artin

theorem IsTripleOf.hkFrob (h : IsTripleOf Y) (hi : X.NonzeroIndexPlace i) (s : X.Sig i) : HkFrob i s :=
  let ⟨_, _, h⟩ := h
  let ⟨_, h1, _, _, _, _, _, _, h2⟩ := h.triple hi s
  h2.hkFrob h.artin h1

theorem IsTripleOf.hecke_polynomial (h : IsTripleOf Y) (hi : X.NonzeroIndexPlace i) (s : X.Sig i) {P : PlE D.host} (hS : P ∉ X.S0 i)
    (hP : IsSplitPl D.host P) {g : GalE D} (hF : IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) g⁻¹) :
    ∑ k ∈ Finset.range (D.R.r + 1), monomial k ((-1 : X.O i) ^ k * ((normV P : ℕ) : X.O i) ^ (k * (k - 1) / 2) *
      X.hEig i s k P) = (matW s g).charpolyRev.map (algebraMap (X.O0 i) (X.O i)) := by
  have hd : ((matW s g).charpolyRev.map (algebraMap (X.O0 i) (X.O i))).natDegree < D.R.r + 1 := by
    rw [← Matrix.reverse_charpoly, Nat.lt_succ_iff]
    exact natDegree_map_le.trans ((reverse_natDegree_le _).trans
      (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]))
  rw [as_sum_range' _ _ hd]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [h.hkFrob hi s P hS hP g hF k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)), coeff_map, matW_eq]

theorem IsTripleOf.adm8 (h : IsTripleOf Y) : adm8 X Y := by
  intro i hi s _
  have hu := h.unrRho hi s
  refine ⟨twistW s, ?_, fun P hS _ A hA g hI => ?_, fun v hv A hA => ?_, fun P hS hP g hF => ?_⟩
  · obtain ⟨ρ⟩ := Reading.nonempty i true
    exact Units.continuous_val.comp
      (((GlobalTheory.GalChar.continuous_units _ (GlobalTheory.GalChar.continuous_cyc (X.twistBaseCoefficientRing_isAdic i) ρ.κ_alg)).pow D.R.t).mul
        (GlobalTheory.GalChar.continuous_units _ (X.twistCharacterFamily_continuous i _ _)).inv)
  · have hl : P ∉ placesOver D.host.E (X.l i) := fun hk => hS (X.twistExcludedPlaces_contains_residueChar i hk)
    have hg : ∀ k, P ∉ placesOver D.host.E (D.host.g k) := fun k hk => hS (X.placesOver_subset_exceptional i k hk)
    refine (matW_of_mem_Ine hu hl hg hA hI).trans ?_
    rw [chiS, X.twistCharacterFamily_unramified i _ _ P hl hg (fun hk => hS (X.primes_subset_exceptional i hk)) A hA g hI, inv_one, Units.val_one, one_smul]
  · obtain ⟨hl, hg⟩ := notMem_of_mem_pD hv
    cases hb : X.side i s
    · refine Or.inl fun g hI => (matW_of_mem_Ine hu hl hg hA hI).trans ?_
      rw [chiS, X.twistCharacterFamily_at_auxiliaryPlaces i _ _ v hv A hA g hI, hb, if_neg Bool.false_ne_true, inv_inv]
    · refine Or.inr fun g hI => (matW_of_mem_Ine hu hl hg hA hI).trans ?_
      rw [chiS, X.twistCharacterFamily_at_auxiliaryPlaces i _ _ v hv A hA g hI, hb, if_pos rfl]
  · change _ = algebraMap (X.O0 i) (X.O i) (1 - matW s g).det
    rw [← sum_coeff_charpolyRev, map_sum, matW_eq]
    exact Finset.sum_congr rfl fun k hk => h.hkFrob hi s P hS hP g hF k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))

theorem satake_identity_of_isTriple (D : D7) (h : IsTriple D) :
    Formalism.MainNotions.BlochKatoReduction.Gen.adm8 D.ntw D.nexp ∧ GlobalTheory.TwSys.AllGood D.nexp ∧ D.nexp.sig_all :=
  ⟨IsTripleOf.adm8 h, IsTripleOf.allGood h, IsTripleOf.sig_all h⟩

end GlobalTheory.Triple

end
