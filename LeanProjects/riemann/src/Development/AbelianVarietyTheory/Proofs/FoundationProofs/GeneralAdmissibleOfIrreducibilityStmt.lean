import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaTypePrimesOfAdmissible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRepMatrixEqTopOfAbsIrreducible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntSubMem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjPlMemPlacesOver
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCompatibleConjugationRepresentation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapPrimeToPartFbar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanEqTopOfTraceEq

noncomputable section

namespace GlobalTheory.TripleResidual

open NumberField IsDedekindDomain Polynomial Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.TameLabels GlobalTheory.AntiRamConj GlobalTheory.TwistDet
open GlobalTheory.TypeLeaf (WildOne FrobDense)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (OnW IsBaseChange IsGaloisRepOf IsReduction Zbar GaloisReps GalE toFb)
open scoped Pointwise

theorem span_eq_top_of_trace_eq {Γ K : Type} [Monoid Γ] [Field K] {n : ℕ}
    (M N : Γ →* Matrix (Fin n) (Fin n) K) (h : ∀ g, (M g).trace = (N g).trace)
    (hN : Submodule.span K (Set.range N) = ⊤) : Submodule.span K (Set.range M) = ⊤ := by
  first
  | exact @_root_.GlobalTheory.TraceFormNondegenerate.span_eq_top_of_trace_eq
  | exact _root_.GlobalTheory.TraceFormNondegenerate.span_eq_top_of_trace_eq
  | (apply _root_.GlobalTheory.TraceFormNondegenerate.span_eq_top_of_trace_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.TraceFormNondegenerate.span_eq_top_of_trace_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TraceFormNondegenerate.span_eq_top_of_trace_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TraceFormNondegenerate.span_eq_top_of_trace_eq ..)

theorem trace_eq_of_charpoly_eq {K : Type} [Field K] {n : ℕ} {A B : Matrix (Fin n) (Fin n) K}
    (h : A.charpoly = B.charpoly) : A.trace = B.trace := by
  rcases n with _ | n
  · simp [Matrix.trace]
  · rw [Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff, h]

theorem det_ne_zero_of_not_isRoot {k K : Type} [Field k] [Field K] (κ : k →+* K) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) k) (c : k) (h : ¬ (A.map κ).charpoly.IsRoot (κ c)) :
    (A - c • (1 : Matrix _ _ k)).det ≠ 0 := by
  intro h0
  apply h
  rw [Matrix.charpoly_map, IsRoot, eval_map, eval₂_hom, Matrix.eval_charpoly, Matrix.scalar_apply,
    ← Matrix.smul_one_eq_diagonal, ← neg_sub, Matrix.det_neg, h0, mul_zero, map_zero]

theorem charpoly_conj_GL {Γ K : Type} [Group Γ] [Field K] {n : ℕ} (ρ : Γ →* GL (Fin n) K) (g s : Γ) :
    ((ρ (g * s * g⁻¹) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).charpoly =
      ((ρ s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).charpoly := by
  rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

section Wild

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

def WildAt (A : ValuationSubring Ω) (u : G E Ω) : Prop := ∀ y : Ω, y ≠ 0 → A.valuation (u y / y - 1) < 1

omit [NumberField E] in
theorem wildAt_conj (c : Ω ≃+* Ω) {A : ValuationSubring Ω} {u u' : G E Ω} (h : ∀ y, u' y = c (u (c.symm y)))
    (hu : WildAt (moveVal c A) u') : WildAt A u := fun y hy => by
  have := hu (c y) ((map_ne_zero_iff _ c.injective).2 hy)
  rw [moveVal_lt_one, map_sub, map_div₀, map_one, h] at this
  simpa using this

theorem wildAt_of_isWild {A : ValuationSubring Ω} {u : G E Ω} (h : BlochKatoReduction.IsWild A u) : WildAt A u := fun y hy => by
  have e : u y / y - 1 = (u y - y) / y := by field_simp
  have h0 : 0 < A.valuation y := zero_lt_iff.mpr (by simpa using hy)
  rw [e, map_div₀, div_lt_one₀ h0]
  exact h.2 y hy

theorem mem_ine_of_wildAt {A : ValuationSubring Ω} {u : G E Ω} (h : WildAt A u) : u ∈ Ine (F := E) A :=
  (GlobalTheory.InertiaTypePrimes.isWild_of_isWildAt A u h).1

theorem eq_one_of_wildAt [IsAlgClosure E Ω] {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 E)}
    (hA : IsPlaceOver A v) {l : ℕ} [Fact l.Prime] (hv : v ∉ placesOver E l) {K : Type} [Field K] [CharP K l] {n : ℕ}
    (ρ : G E Ω →* GL (Fin n) K) (ho : IsOpen (ρ.ker : Set (G E Ω))) {u : G E Ω} (hu : WildAt A u)
    (hc : ((ρ u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).charpoly = (X - 1) ^ n) : ρ u = 1 := by
  refine GlobalTheory.mem_of_wild_of_pow_mem_open_normal _ _ A v hA ρ.ker inferInstance ho u (l ^ n) (fun hm => hv ?_) hu ?_
  · rw [Nat.cast_pow] at hm
    exact v.isPrime.mem_of_pow_mem _ hm
  · rw [MonoidHom.mem_ker, map_pow, Units.ext_iff, Units.val_pow_eq_pow_val]
    exact pow_eq_one_of_charpoly _ hc

def TameOff {K : Type} [Field K] {n : ℕ} (ρ : G E Ω →* GL (Fin n) K) (χ : G E Ω →* Kˣ) (A : ValuationSubring Ω) :
    Prop :=
  (∀ u, WildAt A u → ρ u = 1) ∧ ∃ s ∈ Ine (F := E) A,
    ¬ ((ρ s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).charpoly.IsRoot ((χ s : Kˣ) : K)

theorem TameOff.move [IsAlgClosure E Ω] {K : Type} [Field K] {n : ℕ} {ρ : G E Ω →* GL (Fin n) K} {χ : G E Ω →* Kˣ}
    {A A' : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 E)} (hA : IsPlaceOver A v) (hA' : IsPlaceOver A' v)
    (h : TameOff ρ χ A) : TameOff ρ χ A' := by
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := E) hA hA'
  have e : moveVal g.toRingEquiv A = A' := by
    rw [← hg]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  subst e
  obtain ⟨h1, s, hs, h2⟩ := h
  refine ⟨fun u hu => ?_, g * s * g⁻¹,
    conjAut_mem_ine g.toRingEquiv (fun x => ⟨x, g.symm.commutes x⟩) hs, ?_⟩
  · have h3 := h1 (g⁻¹ * u * g) (wildAt_conj g.toRingEquiv (fun y => ?_) hu)
    · have e : u = g * (g⁻¹ * u * g) * g⁻¹ := by group
      rw [e, map_mul, map_mul, h3, mul_one, ← map_mul, mul_inv_cancel, map_one]
    · change u y = (g * (g⁻¹ * u * g) * g⁻¹) y
      congr 1
      group
  · rwa [charpoly_conj_GL, map_mul, map_mul, map_inv, mul_inv_cancel_comm]

end Wild

section Row

variable {D : D7} (Y : NTw D.R D.host D.what₂ D.LL0 D.nd)

theorem charpoly_cConj (hD : FrobDense D) {n : ℕ} {π : D.naut.CG n} (hπ : D.naut.csd π) {l : ℕ} [Fact l.Prime]
    {ι : Qbar l ≃+* ℂ} {r : GalE D →* GL (Fin n) (Qbar l)} (hr : IsGaloisRepOf D π l ι r) (g : GalE D) :
    ((r (cConj Y g) : GL _ _) : Matrix (Fin n) (Fin n) (Qbar l)).charpoly =
      ((((cyc D.host.E D.nd.Om l g : (Qbar l)ˣ) : Qbar l) ^ (1 - (n : ℤ))) •
        ((r g⁻¹ : GL _ _) : Matrix (Fin n) (Fin n) (Qbar l))).charpoly := by
  have : Algebra.IsAlgebraic D.host.E D.nd.Om := IsAlgClosure.isAlgebraic
  obtain ⟨bar, hinj, hbar⟩ := GlobalTheory.ConjPoly.exists_conj D
  obtain ⟨hcont, -, hfr⟩ := hr
  have hl := (GlobalTheory.ConjPoly.finite_placesOver D.host.E l (Fact.out : l.Prime).ne_zero).compl_mem_cofinite
  have hall := (D.naut.locG_unr_ae π).and hl
  have hcc : Continuous (cConj Y) := GlobalTheory.AntiLAdic.continuous_conjHom Y.cc (cc_symm_mem Y)
  refine GlobalTheory.TypeLeaf.charpoly_eq_of_dense (GalE D) (Qbar l) n
    (fun g => ((r (cConj Y g) : GL _ _) : Matrix (Fin n) (Fin n) (Qbar l)))
    (fun g => (((cyc D.host.E D.nd.Om l g : (Qbar l)ˣ) : Qbar l) ^ (1 - (n : ℤ))) •
        ((r g⁻¹ : GL _ _) : Matrix (Fin n) (Fin n) (Qbar l))) _ (hD _ (Filter.eventually_cofinite.1 hall))
    (hcont.comp hcc)
    (((GlobalTheory.ConjPoly.continuous_cyc_val D.host.E D.nd.Om l).zpow₀ (1 - (n : ℤ))
      fun g => Or.inl (Units.ne_zero _)).fun_smul (hcont.comp continuous_inv)) ?_ g
  rintro σ ⟨w, hw, -, B, hB, hσ⟩
  obtain ⟨hu, hwl⟩ := not_not.1 hw
  obtain ⟨hcj, hn, -⟩ := hbar w
  obtain ⟨hu', he⟩ := D.naut.csd_unr π w (bar w) hπ hcj hu
  have e1 := (hfr w hwl).2.2 hu B σ hB hσ
  have e2 := (hfr (bar w) fun h => hwl (mem_placesOver_conj (isConjPl_symm hcj) h)).2.2 hu' _ _
    (isPlaceOver_moveVal_cc Y hcj hB) (by rw [hn]; exact isFrob_cConj Y hσ)
  rw [galPol, D.naut.frobEig_tw _ _ hu, ← Matrix.charpoly_map] at e1
  rw [galPol, D.naut.frobEig_tw _ _ hu', he, hn, ← Matrix.charpoly_map] at e2
  have hq : ((normV w : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (GlobalTheory.ConjPoly.normV_ne_zero w)
  have e3 := GlobalTheory.ConjPoly.charpoly_smul_inv _
    (((r σ⁻¹ : GL _ _) : Matrix (Fin n) (Fin n) (Qbar l)).map ι.toRingHom)
    (by rw [← Matrix.map_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _)]) _ (((normV w : ℕ) : ℂ) ^ (1 - (n : ℤ))) e1
  apply Polynomial.map_injective ι.toRingHom ι.injective
  rw [← Matrix.charpoly_map, ← Matrix.charpoly_map, GlobalTheory.ConjPoly.cyc_val_frob hwl hB hσ]
  refine e2.trans (Eq.trans ?_ (e3.symm.trans ?_))
  · rw [Multiset.map_map, Multiset.map_map, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun a _ => ?_
    simp only [Function.comp_apply]
    rw [GlobalTheory.ConjPoly.cpow_sq hq ((1 - (n : ℝ)) / 2) _ (by push_cast; ring)]
    have : ((normV w : ℕ) : ℂ) ^ (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) ≠ 0 := by
      simp [hq]
    rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel_right₀ this, mul_comm a⁻¹]
  · congr 1
    ext a b
    simp

theorem charpoly_cConj_red (hD : FrobDense D) {n : ℕ} {π : D.naut.CG n} (hπ : D.naut.csd π) {l : ℕ} [Fact l.Prime]
    {ι : Qbar l ≃+* ℂ} {red : Zbar l →+* Formalism.CyclotomicNorms.Fbar l} {r : GalE D →* GL (Fin n) (Qbar l)}
    {ρ : GalE D →* GL (Fin n) (Formalism.CyclotomicNorms.Fbar l)} (hr : IsGaloisRepOf D π l ι r) (hρ : IsReduction D red r ρ)
    {v : PlE D.host} (hv : v ∉ placesOver D.host.E l) {A : ValuationSubring D.nd.Om} (hA : IsPlaceOver A v)
    {s : GalE D} (hs : s ∈ Ine (F := D.host.E) A) :
    ((ρ (cConj Y s) : GL _ _) : Matrix (Fin n) (Fin n) (Formalism.CyclotomicNorms.Fbar l)).charpoly =
      ((ρ s⁻¹ : GL _ _) : Matrix (Fin n) (Fin n) (Formalism.CyclotomicNorms.Fbar l)).charpoly := by
  have h := charpoly_cConj Y hD hπ hr s
  rw [cyc_eq_one_of_mem_Ine hv hA hs, Units.val_one, one_zpow, one_smul] at h
  obtain ⟨p, p1, p2⟩ := hρ.2.2 (cConj Y s)
  obtain ⟨q, q1, q2⟩ := hρ.2.2 s⁻¹
  rw [← p2, ← q2, Polynomial.map_injective _ Subtype.val_injective (p1.trans (h.trans q1.symm))]

theorem wild_fixed (hW : WildOne D) {k : Fin 2} {v : D.nd.PlG k} {π : D.naut.CG D.R.r}
    (hf : (D.naut.items₂ k _ (D.naut.locG π (D.naut.plGw k v))).natDegree = D.R.r)
    {l : ℕ} [Fact l.Prime] (hl : l ≠ D.host.g k) {ι : Qbar l ≃+* ℂ} {red : Zbar l →+* Formalism.CyclotomicNorms.Fbar l}
    {r : GalE D →* GL (Fin D.R.r) (Qbar l)} {ρ : GalE D →* GL (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar l)}
    (hr : IsGaloisRepOf D π l ι r) (hρ : IsReduction D red r ρ) {u : GalE D}
    (hu : WildAt (D.nd.plOm.1 (D.naut.plGw k v)) u) : ρ u = 1 := by
  have hw := not_mem_of_ne (v := v) (Fact.out : l.Prime) hl
  have huI := mem_ine_of_wildAt hu
  have h1 := (hr.2.2 _ hw).1 u huI
  rw [D.naut.inePol_tw _ _ _ huI, hW k v _ (by rw [hf, D.naut.locG_dim]) u huI hu, D.naut.locG_dim] at h1
  obtain ⟨p, hp1, hp2⟩ := hρ.2.2 u
  have hp : p = (X - 1) ^ D.R.r := by
    apply Polynomial.map_injective (ι.toRingHom.comp (Zbar l).subtype) (ι.injective.comp Subtype.val_injective)
    rw [← Polynomial.map_map, hp1, h1]
    simp
  refine eq_one_of_wildAt (D.nd.plOm.2 _) hw ρ hρ.1 hu ?_
  rw [← hp2, hp]
  simp

theorem tameOff_all {l : ℕ} [Fact l.Prime] {k : Fin 2} (hl : l ≠ D.host.g k)
    {ρ : GalE D →* GL (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar l)} {χ : GalE D →* (Formalism.CyclotomicNorms.Fbar l)ˣ}
    (ho : IsOpen (ρ.ker : Set (GalE D)))
    (hρ : ∀ v, ∀ s ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)),
      ((ρ (cConj Y s) : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar l)).charpoly =
        ((ρ s⁻¹ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar l)).charpoly)
    (hχ : ∀ v, ∀ s ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)), χ (cConj Y s) = (χ s)⁻¹)
    (h : ∀ v, TameOff ρ χ (D.nd.plOm.1 (D.naut.plGw k v)))
    {w : PlE D.host} (hw : w ∈ placesOver D.host.E (D.host.g k)) {A : ValuationSubring D.nd.Om}
    (hA : IsPlaceOver A w) : TameOff ρ χ A := by
  obtain ⟨v, rfl | hv⟩ := GlobalTheory.TypePlaceCover.place_cover D k w hw
  · exact (h v).move (D.nd.plOm.2 _) hA
  have hB := isPlaceOver_moveVal_cc Y hv (D.nd.plOm.2 _)
  refine TameOff.move hB hA ?_
  obtain ⟨h1, s, hs, h2⟩ := h v
  refine ⟨fun u hu => ?_, cConj Y s⁻¹, cConj_mem_ine Y (Subgroup.inv_mem _ hs), ?_⟩
  · have h3 : WildAt (D.nd.plOm.1 (D.naut.plGw k v)) (cConj Y u) :=
      wildAt_conj Y.cc (fun y => by rw [← cConj_apply, cConj_cConj]) hu
    have h4 := hρ v _ (mem_ine_of_wildAt h3)
    rw [cConj_cConj, map_inv, h1 _ h3, inv_one, Units.val_one, Matrix.charpoly_one, Fintype.card_fin] at h4
    exact eq_one_of_wildAt hB (fun hm => not_mem_of_ne (v := v) (Fact.out : l.Prime) hl
      (mem_placesOver_conj (isConjPl_symm hv) hm)) ρ ho hu h4
  · rwa [hρ v _ (Subgroup.inv_mem _ hs), hχ v _ (Subgroup.inv_mem _ hs), inv_inv, map_inv, inv_inv]

end Row

section Triples

variable {D : D7} (Y : NTw D.R D.host D.what₂ D.LL0 D.nd)

abbrev FbAt (D : D7) (w : D.what₂.places.Pl) : Type :=
  Fb (D.what₂.places.resChar w) (D.what₂.places.resChar_prime w)

def IsRowOfTriple (i : Y.Tw) (s : Y.Sig i) (σ : D.what₂.FT) (w : D.what₂.places.Pl)
    (κ : IsLocalRing.ResidueField (Y.O0 i) →+* FbAt D w) : Prop :=
  D.nd.goodRow σ ∧ D.what₂.isot (Y.jS i s) σ ≠ ⊥ ∧ D.what₂.places.resChar w = Y.l i ∧
  (∀ x : 𝓞 ↥D.LL0, (∃ y ∈ IsLocalRing.maximalIdeal (Y.O0 i), algebraMap (Y.O0 i) (FractionRing (Y.O0 i)) y =
      (if Y.side i s then Y.emb0 i else Y.emb0b i) (x : ↥D.LL0)) ↔
    0 < D.what₂.places.val w ((x : ↥D.LL0) : D.what₂.LL)) ∧
  (∃ η : GalE D →* (FbAt D w)ˣ,
    (∀ v, v ∉ placesOver D.host.E (Y.l i) → ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v →
      ∀ t ∈ Ine (F := D.host.E) A, η t = 1) ∧
    ∀ g, ((BlochKatoReduction.Gen.rbar Y i s g).map κ).charpoly =
      (((η g : (FbAt D w)ˣ) : FbAt D w) •
        ((D.ntypes.rbar σ w g : GL (Fin D.R.r) (FbAt D w)) : Matrix (Fin D.R.r) (Fin D.R.r) (FbAt D w))).charpoly) ∧
  ∀ k, D.host.g k ≠ Y.l i → ∀ v : D.nd.PlG k, ∃ u : (ZMod (D.host.g k))ˣ,
    (u = D.nd.chiT k v ⟨Y.jS i s - 1, by have := Y.jS_range i s; omega⟩ ∨
      u = (D.nd.chiT k v ⟨Y.jS i s - 1, by have := Y.jS_range i s; omega⟩)⁻¹) ∧
    κ (IsLocalRing.residue (Y.O0 i) ((BlochKatoReduction.Gen.chiS i s (D.ntypes.tg k v) : (Y.O0 i)ˣ) : Y.O0 i)) =
      D.ntypes.iota k v w (toFb D k u)

def TriplesAreRows : Prop :=
  ∀ i, Y.NonzeroIndexPlace i → ∀ s : Y.Sig i, ∃ σ w κ, IsRowOfTriple Y i s σ w κ

def BlockCharConj : Prop :=
  ∀ i, Y.NonzeroIndexPlace i → ∀ j b, 1 ≤ j → j ≤ D.R.m → ∀ k, D.host.g k ≠ Y.l i → ∀ v ∈ placesOver D.host.E (D.host.g k),
    ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v → ∀ t ∈ Ine (F := D.host.E) A, ∀ t' : GalE D,
      (∀ x, t' x = Y.cc (t (Y.cc.symm x))) → Y.chi1 i j b t' = (Y.chi1 i j b t)⁻¹

variable {Y}

theorem admissible_at_of_irreducible_tame {i : Y.Tw} {s : Y.Sig i} {σ : D.what₂.FT} {w : D.what₂.places.Pl}
    {κ : IsLocalRing.ResidueField (Y.O0 i) →+* FbAt D w} (h : IsRowOfTriple Y i s σ w κ)
    (hirr : @Formalism.CyclotomicNorms.IrredOn _ _ ⟨D.what₂.places.resChar_prime w⟩ _ _ (D.ntypes.rbar σ w) ⊤)
    (htame : ∀ k, D.host.g k ≠ Y.l i → ∀ v ∈ placesOver D.host.E (D.host.g k), ∀ A : ValuationSubring D.nd.Om,
      IsPlaceOver A v → TameOff (D.ntypes.rbar σ w)
        ((Units.map (κ.comp (IsLocalRing.residue (Y.O0 i))).toMonoidHom).comp (BlochKatoReduction.Gen.chiS i s)) A) :
    BlochKatoReduction.Gen.ValuationStabilityAtRing Y i s := by
  have : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
  obtain ⟨-, -, hl, -, ⟨η, hη, hcp⟩, -⟩ := h
  let ρ := mapRep (κ.comp (IsLocalRing.residue (Y.O0 i))) (Y.rhoS i s)
  have hρ : ∀ g, ((ρ g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (FbAt D w)) = (BlochKatoReduction.Gen.rbar Y i s g).map κ :=
    fun _ => rfl
  refine ⟨?_, fun k hk v hv A hA => ?_⟩
  · have hr : Nonempty (Fin D.R.r) := ⟨⟨0, (odd_r D.R).pos⟩⟩
    have h1 := GlobalTheory.BurnsideField.span_mat_eq_top_of_isIrrSub (D.ntypes.rbar σ w)
      ⟨top_ne_bot, fun _ _ _ => trivial, fun W _ hW => hirr W fun g _ => hW g⟩
    have h2 := span_eq_top_of_trace_eq ((Units.coeHom _).comp ρ)
      (twistM ((Units.coeHom _).comp (D.ntypes.rbar σ w)) η) (fun g => trace_eq_of_charpoly_eq (hcp g)) (by
        rw [eq_top_iff, ← h1, Submodule.span_le]
        rintro _ ⟨g, rfl⟩
        have := Submodule.smul_mem _ (((η g)⁻¹ : (FbAt D w)ˣ) : FbAt D w) (Submodule.subset_span (R := FbAt D w)
          (Set.mem_range_self (f := twistM ((Units.coeHom _).comp (D.ntypes.rbar σ w)) η) g))
        change (((η g)⁻¹ : (FbAt D w)ˣ) : FbAt D w) • ((η g : (FbAt D w)ˣ) : FbAt D w) •
          ((D.ntypes.rbar σ w g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (FbAt D w)) ∈ _ at this
        rwa [smul_smul, Units.inv_mul, one_smul] at this)
    let := κ.toAlgebra
    exact GlobalTheory.BurnsideField.span_eq_top_of_span_map (K := FbAt D w) _ h2
  · have hvl : v ∉ placesOver D.host.E (Y.l i) := fun hm => by
      obtain ⟨a, b, hab⟩ : IsCoprime ((Y.l i : ℕ) : 𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.E) :=
        Nat.Coprime.cast ((Nat.coprime_primes (Y.lPrime i).out (D.host.g_prime k)).2 hk.symm)
      refine v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
      rw [← hab]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hm) (Ideal.mul_mem_left _ _ hv)
    obtain ⟨h1, t, ht, h2⟩ := htame k hk v hv A hA
    refine ⟨fun u hu => ?_, t, ht, det_ne_zero_of_not_isRoot κ _ _ ?_⟩
    · have hm : IsOpen (IsLocalRing.maximalIdeal (Y.O0 i) : Set (Y.O0 i)) := by
        simpa using (isAdic_iff.mp (Y.twistBaseCoefficientRing_isAdic i)).1 1
      have ho : IsOpen (ρ.ker : Set (GalE D)) := by
        refine Subgroup.isOpen_mono (fun g hg => ?_)
          (GlobalTheory.InertiaTypePrimes.isOpen_ker_mapRep _ hm _ (Y.rhoS_cont i s))
        have h3 : BlochKatoReduction.Gen.rbar Y i s g = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hg)
        rw [MonoidHom.mem_ker, Units.ext_iff, hρ, h3, Matrix.map_one _ (map_zero _) (map_one _), Units.val_one]
      have h3 := eq_one_of_wildAt hA (hl ▸ hvl) ρ ho (wildAt_of_isWild hu) (by
        rw [hρ, hcp, hη v hvl A hA u hu.1, h1 u (wildAt_of_isWild hu), Units.val_one, Units.val_one, one_smul,
          Matrix.charpoly_one, Fintype.card_fin])
      apply Matrix.map_injective κ.injective
      change (BlochKatoReduction.Gen.rbar Y i s u).map κ = Matrix.map 1 κ
      rw [← hρ, h3, Matrix.map_one _ (map_zero _) (map_one _), Units.val_one]
    · rw [hcp, hη v hvl A hA t ht, Units.val_one, one_smul]
      exact h2

end Triples

end GlobalTheory.TripleResidual

end
