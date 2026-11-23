import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ScalarCharacterTwist
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.CharacterValuation
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StandardRankOneLatticeOfLocal
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LiesOverSpanOfNatCastMemHeightOne
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExpNegOneLtOne

open NumberField IsDedekindDomain nonZeroDivisors

noncomputable section

namespace GlobalTheory.CharValCompare

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions GlobalTheory.IndefiniteRowSideFullHecke

section Pull

variable {E E' : Type} [Field E] [Field E'] (e : E ≃+* E')

theorem map_osmul (c : 𝓞 E) (a : E) : e (c • a) = RingOfIntegers.mapRingEquiv e c • e a := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  rfl

def pull (I : Submodule (𝓞 E') E') : Submodule (𝓞 E) E where
  carrier := {x | e x ∈ I}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    show e (a + b) ∈ I
    rw [map_add]; exact add_mem ha hb
  smul_mem' := fun c a ha => by
    show e (c • a) ∈ I
    rw [map_osmul]
    exact I.smul_mem _ ha

theorem mem_pull (I : Submodule (𝓞 E') E') (x : E) : x ∈ pull e I ↔ e x ∈ I := Iff.rfl

theorem pull_pull (I : Submodule (𝓞 E') E') : pull e.symm (pull e I) = I := by
  ext x
  rw [mem_pull, mem_pull, e.apply_symm_apply]

theorem pull_one : pull e 1 = 1 := by
  ext x
  rw [mem_pull, Submodule.mem_one, Submodule.mem_one]
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨RingOfIntegers.mapRingEquiv e.symm r, by rw [← e.symm_apply_apply x, ← hr]; rfl⟩
  · rintro ⟨r, rfl⟩
    exact ⟨RingOfIntegers.mapRingEquiv e r, rfl⟩

theorem pull_norm (c : E → E) (c' : E' → E') (h : ∀ x, e (c x) = c' (e x)) {I : Submodule (𝓞 E') E'}
    (hI : ∃ J : Submodule (𝓞 E') E', (∀ x, x ∈ J ↔ c' x ∈ I) ∧ I * J = 1) :
    ∃ J : Submodule (𝓞 E) E, (∀ x, x ∈ J ↔ c x ∈ pull e I) ∧ pull e I * J = 1 := by
  obtain ⟨J, hJ, hIJ⟩ := hI
  refine ⟨pull e J, fun x => by rw [mem_pull, mem_pull, hJ, h], le_antisymm ?_ ?_⟩
  · rw [Submodule.mul_le]
    intro x hx y hy
    rw [← pull_one e, mem_pull, map_mul, ← hIJ]
    exact Submodule.mul_mem_mul hx hy
  · rw [Submodule.one_le]
    have h1 : ∀ z ∈ I * J, e.symm z ∈ pull e I * pull e J := by
      intro z hz
      refine Submodule.mul_induction_on hz (fun a ha b hb => ?_) fun a b ha hb => by rw [map_add]; exact add_mem ha hb
      rw [map_mul]
      exact Submodule.mul_mem_mul (by simpa [mem_pull] using ha) (by simpa [mem_pull] using hb)
    simpa using h1 1 (hIJ ▸ Submodule.mem_one.2 ⟨1, map_one _⟩)

def pushP (P : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 E') :=
  HeightOneSpectrum.comap (RingOfIntegers.mapRingEquiv e.symm : 𝓞 E' →+* 𝓞 E) (RingOfIntegers.mapRingEquiv e.symm).surjective P

theorem mem_pushP (P : HeightOneSpectrum (𝓞 E)) (r : 𝓞 E') :
    r ∈ (pushP e P).asIdeal ↔ RingOfIntegers.mapRingEquiv e.symm r ∈ P.asIdeal := Iff.rfl

theorem mem_localization_pullback (P : HeightOneSpectrum (𝓞 E)) (I : Submodule (𝓞 E') E') (x : E) :
    x ∈ localization₂ P.asIdeal (pull e I) ↔ e x ∈ localization₂ (pushP e P).asIdeal I := by
  constructor
  · rintro ⟨s, hs, h⟩
    refine ⟨RingOfIntegers.mapRingEquiv e s, ?_, by rwa [mem_pull, map_osmul] at h⟩
    intro hm
    have h2 : RingOfIntegers.mapRingEquiv e.symm (RingOfIntegers.mapRingEquiv e s) = s :=
      RingOfIntegers.ext (e.symm_apply_apply _)
    exact hs (h2 ▸ (mem_pushP e P _).1 hm)
  · rintro ⟨s, hs, h⟩
    refine ⟨RingOfIntegers.mapRingEquiv e.symm s, hs, ?_⟩
    have := map_osmul e.symm s (e x)
    rw [e.symm_apply_apply] at this
    rwa [mem_pull, ← this, e.apply_symm_apply]

end Pull

section Vp

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem mem_vpIdeal (P : HeightOneSpectrum (𝓞 E)) (x : E) : x ∈ CharacterValuation.vpIdeal P ↔
    ∀ y ∈ (conjPrime₂ P).asIdeal, ∃ z ∈ P.asIdeal, algebraMap (𝓞 E) E z = algebraMap (𝓞 E) E y * x := by
  have h0 : (((conjPrime₂ P).asIdeal : FractionalIdeal (𝓞 E)⁰ E)) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 (conjPrime₂ P).ne_bot
  unfold CharacterValuation.vpIdeal
  rw [FractionalIdeal.mem_coe, ← div_eq_mul_inv, FractionalIdeal.mem_div_iff_of_ne_zero h0]
  constructor
  · intro h y hy
    have := h _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨y, hy, rfl⟩)
    rw [mul_comm] at this
    exact (FractionalIdeal.mem_coeIdeal _).1 this
  · intro h y hy
    obtain ⟨z, hz, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    rw [mul_comm]
    exact (FractionalIdeal.mem_coeIdeal _).2 (h z hz)

theorem vpLat_eq (P : HeightOneSpectrum (𝓞 E)) : ScalarCharacterTwist.vpLat P = CharacterValuation.vpLat P := by
  ext x
  exact (mem_vpIdeal P (x 0)).symm

theorem star_mem_vpIdeal {P : HeightOneSpectrum (𝓞 E)} {x : E} (h : x ∈ CharacterValuation.vpIdeal P) : star x ∈ CharacterValuation.vpIdeal (conjPrime₂ P) := by
  rw [mem_vpIdeal] at h ⊢
  intro y hy
  rw [conjP_conjP] at hy
  obtain ⟨z, hz, e⟩ := h (cO E y) (by rwa [mem_conjP, cO_cO])
  refine ⟨cO E z, by rwa [mem_conjP, cO_cO], ?_⟩
  rw [algebraMap_cO, e, star_mul', algebraMap_cO, star_star]

theorem normOne_vpIdeal (P : HeightOneSpectrum (𝓞 E)) : NormOne (CharacterValuation.vpIdeal P) := by
  refine ⟨CharacterValuation.vpIdeal (conjPrime₂ P), fun x => ⟨fun h => ?_, fun h => ?_⟩, ?_⟩
  · have := star_mem_vpIdeal h
    rwa [conjP_conjP] at this
  · have := star_mem_vpIdeal h
    rwa [star_star] at this
  · have h0 : (((conjPrime₂ P).asIdeal : FractionalIdeal (𝓞 E)⁰ E)) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 (conjPrime₂ P).ne_bot
    have h1 : ((P.asIdeal : FractionalIdeal (𝓞 E)⁰ E)) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 P.ne_bot
    unfold CharacterValuation.vpIdeal
    rw [conjP_conjP, ← FractionalIdeal.coe_mul, mul_mul_mul_comm, ← mul_inv, mul_comm ((conjPrime₂ P).asIdeal : FractionalIdeal (𝓞 E)⁰ E),
      mul_inv_cancel₀ (mul_ne_zero h1 h0), FractionalIdeal.coe_one]

theorem isSdLat_vpLat (P : HeightOneSpectrum (𝓞 E)) : IsSdLat (CharacterValuation.vpLat P) := self_dual_rank_one_lattice (normOne_vpIdeal P)

omit [StarRing E] in

theorem isFrames_iff {n : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 E))} (N : Submodule (𝓞 E) (Sp E n)) (fr : Frs E n SB) :
    CharacterValuation.IsFrames N fr ↔ ScalarCharacterTwist.FrOf N fr := Iff.rfl

end Vp

section Val

variable {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ)

omit [NumberField K] in
theorem sig_desc {z : ℂ} (h : ∃ k, σ k = z) : σ (desc σ z) = z := by
  unfold desc
  rw [dif_pos h]
  exact h.choose_spec

omit [NumberField K] in
theorem desc_sig (k : K) : desc σ (σ k) = k := σ.injective (sig_desc σ ⟨k, rfl⟩)

theorem hasVal_iff [StarRing K] (w : HeightOneSpectrum (𝓞 K)) {p : ℕ} (hp : p.Prime) (h : ((p : ℕ) : 𝓞 K) ∈ w.asIdeal) (k : K) (r : ℚ) :
    ScalarCharacterTwist.HasVal_vp σ w (σ k) r ↔ k ≠ 0 ∧ CharacterValuation.val_vp w p k = r := by
  have h0 : (eW w : ℚ) ≠ 0 := by exact_mod_cast (eW_pos w).ne'
  rw [ScalarCharacterTwist.hasVal_vp_iff, CharacterValuation.val_vp, ordE_prime w hp h, Int.cast_natCast, div_eq_iff h0]

theorem unit_iff (w : HeightOneSpectrum (𝓞 K)) (k : K) : ScalarCharacterTwist.UnitAtW σ w (σ k) ↔ CharacterValuation.UnitAt w k :=
  ScalarCharacterTwist.unitAtW_iff σ w k

end Val

section Chi

variable {D : D7} {X : Fields} (s : Seam D X) {χ : TaylorLogMetric.IdE D → ℂ}

theorem idTo_eq (I : Submodule (𝓞 X.E) X.E) : CharacterValuation.idTo s I = pull s.iE.symm I := by
  have : s.iE '' (I : Set X.E) = (pull s.iE.symm I : Set D.host.E) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [mem_pull] using hx
    · intro hy
      exact ⟨_, hy, s.iE.apply_symm_apply y⟩
  rw [CharacterValuation.idTo, this, Submodule.span_eq]

theorem mem_lat {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) (y : Fin n → D.host.E) :
    y ∈ s.lat N ↔ (fun i => s.iE.symm (y i)) ∈ N := by
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      simpa using hx
    | zero =>
      convert N.zero_mem using 1
      funext i
      exact map_zero _
    | add a b _ _ ha hb =>
      convert N.add_mem ha hb using 1
      funext i
      exact map_add _ _ _
    | smul c a _ ha =>
      convert N.smul_mem (RingOfIntegers.mapRingEquiv s.iE.symm c) ha using 1
      funext i
      exact map_osmul s.iE.symm c (a i)
  · intro hy
    exact Submodule.subset_span ⟨_, hy, funext fun i => s.iE.apply_symm_apply _⟩

theorem detId_lat {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) :
    TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat N) = pull s.iE.symm (detI N) := by
  apply le_antisymm
  · rw [TaylorLogMetric.detId, Submodule.span_le]
    rintro _ ⟨A, hA, rfl⟩
    refine Submodule.subset_span ⟨A.map s.iE.symm, fun v hv => ?_, (s.iE.symm : D.host.E →+* X.E).map_det A⟩
    have h1 := (mem_lat s N _).1 (hA (fun i => s.iE (v i)) fun i _ => by
      have := hv i (Set.mem_univ _)
      rw [← pull_one s.iE] at this
      exact this)
    convert h1 using 1
    funext i
    simp [Matrix.mulVec, dotProduct]
  · have : detI N ≤ pull s.iE (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat N)) := by
      rw [detI, Submodule.span_le]
      rintro _ ⟨A, hA, rfl⟩
      refine Submodule.subset_span ⟨A.map s.iE, fun v hv => (mem_lat s N _).2 ?_, (s.iE : X.E →+* D.host.E).map_det A⟩
      have h1 := hA (fun i => s.iE.symm (v i)) fun i _ => by
        have := hv i (Set.mem_univ _)
        rw [← pull_one s.iE.symm] at this
        exact this
      convert h1 using 1
      funext i
      simp [Matrix.mulVec, dotProduct]
    intro y hy
    simpa [mem_pull] using this hy

variable {s}

theorem normOne_idealPreimageUnderRingEquiv (hs : s.Ok) {I : Submodule (𝓞 X.E) X.E} (h : NormOne I) : TaylorLogMetric.N1 D (pull s.iE.symm I) :=
  pull_norm s.iE.symm D.host.conj star (fun x => by rw [RingEquiv.symm_apply_eq, hs.2, s.iE.apply_symm_apply]) h

theorem normOne_pull (hs : s.Ok) {I : TaylorLogMetric.IdE D} (h : TaylorLogMetric.N1 D I) : NormOne (pull s.iE I) :=
  pull_norm s.iE star D.host.conj hs.2 h

theorem normOne_detIdeal_transportedLattice (hs : s.Ok) {n : ℕ} {N : Submodule (𝓞 X.E) (Sp X.E n)} (hN : IsSdLat N) :
    TaylorLogMetric.N1 D (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat N)) := by
  rw [detId_lat]
  exact normOne_idealPreimageUnderRingEquiv hs (normOne_detI hN)

theorem chi_ne_zero (hs : s.Ok) (hχ : TaylorLogMetric.IsChi D χ) {I : TaylorLogMetric.IdE D} (h : TaylorLogMetric.N1 D I) : χ I ≠ 0 := by
  have h' := h
  obtain ⟨J, hJ, hIJ⟩ := h
  have hc : ∀ x, D.host.conj (D.host.conj x) = x := fun x => by
    obtain ⟨y, rfl⟩ := s.iE.surjective x
    rw [← hs.2, ← hs.2, star_star]
  have h1 := hχ.1 I J h' ⟨I, fun x => by rw [hJ, hc], by rw [mul_comm, hIJ]⟩
  have h2 := hχ.2 (letI := D.host.cmStar; 1)
  intro h0
  rw [hIJ, h0, zero_mul, Submodule.one_eq_span] at h1
  have h3 := h1.symm.trans h2
  simp at h3

theorem sig_chiDet (hs : s.Ok) (hK : CharacterValuation.ChiInK s χ) {n : ℕ} {N : Submodule (𝓞 X.E) (Sp X.E n)} (hN : IsSdLat N) :
    s.σ₀ (CharacterValuation.chiDet s χ N) = χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat N)) :=
  sig_desc _ (hK _ (normOne_detIdeal_transportedLattice hs hN))

theorem chiDet_ne_zero (hs : s.Ok) (hχ : TaylorLogMetric.IsChi D χ) (hK : CharacterValuation.ChiInK s χ) {n : ℕ} {N : Submodule (𝓞 X.E) (Sp X.E n)}
    (hN : IsSdLat N) : CharacterValuation.chiDet s χ N ≠ 0 := fun h =>
  chi_ne_zero hs hχ (normOne_detIdeal_transportedLattice hs hN) (by rw [← sig_chiDet hs hK hN, h, map_zero])

theorem char_det_rank_one_lattice (I : Submodule (𝓞 X.E) X.E) : CharacterValuation.chiDet s χ (lat1 I) = CharacterValuation.chiK s χ (pull s.iE.symm I) := by
  rw [CharacterValuation.chiDet, detId_lat, det_ideal_rank_one_lattice]

theorem chiVp_eq (P : HeightOneSpectrum (𝓞 X.E)) : CharacterValuation.chiVp s χ P = CharacterValuation.chiDet s χ (CharacterValuation.vpLat P) := by
  rw [CharacterValuation.chiVp, idTo_eq]
  exact (char_det_rank_one_lattice _).symm

theorem chiFac_eq (hs : s.Ok) (hK : CharacterValuation.ChiInK s χ) {a b : ℕ} {N : Submodule (𝓞 X.E) (Sp X.E a)} {N' : Submodule (𝓞 X.E) (Sp X.E b)}
    (hN : IsSdLat N) (hN' : IsSdLat N') : Base.chiFac χ a b (s.lat N) (s.lat N') =
      s.σ₀ (CharacterValuation.chiDet s χ N ^ ((b / 2 : ℕ) : ℤ) * CharacterValuation.chiDet s χ N' ^ (-((a / 2 : ℕ) : ℤ))) := by
  rw [map_mul, map_zpow₀, map_zpow₀, sig_chiDet hs hK hN, sig_chiDet hs hK hN']
  rfl

end Chi

section Parts

variable {D : D7} {Z : Dat} {s : Seam D Z.X} {χ : TaylorLogMetric.IdE D → ℂ}
  {sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)} {S : Set ℕ}
  {mu : Tup Z.X.F Z.X.E Z.X.K S} {cst : LocCst Z.X (rowSG Z.Pr sel mu)}

theorem sig_chiDet' (hs : s.Ok) (hK : CharacterValuation.ChiInK s χ) {n : ℕ} {N : Submodule (𝓞 Z.X.E) (Sp Z.X.E n)} (hN : IsSdLat N) :
    ScalarCharacterTwist.chiDet s χ N = s.σ₀ (CharacterValuation.chiDet s χ N) := (sig_chiDet hs hK hN).symm

theorem rhoJ_eq (hs : s.Ok) (hK : CharacterValuation.ChiInK s χ) (i : ℕ) {n : ℕ} {N : Submodule (𝓞 Z.X.E) (Sp Z.X.E n)} (hN : IsSdLat N)
    (fr : Frs Z.X.E n (rowSG Z.Pr sel mu)) :
    ScalarCharacterTwist.rhoJ s χ sel mu cst i N fr = s.σ₀ (CharacterValuation.rho Z s χ sel mu cst i N fr) := by
  rw [ScalarCharacterTwist.rhoJ, CharacterValuation.rho, map_mul, map_zpow₀, sig_chiDet' hs hK hN]
  rfl

theorem rhoJ'_eq (hs : s.Ok) (hK : CharacterValuation.ChiInK s χ) (i : ℕ) {n : ℕ} {N : Submodule (𝓞 Z.X.E) (Sp Z.X.E n)} (hN : IsSdLat N)
    (fr : Frs Z.X.E n (rowSG Z.Pr sel mu)) :
    ScalarCharacterTwist.rhoJ' s χ sel mu cst i N fr = s.σ₀ (CharacterValuation.rho' Z s χ sel mu cst i N fr) := by
  rw [ScalarCharacterTwist.rhoJ', CharacterValuation.rho', map_mul, map_zpow₀, map_inv₀, sig_chiDet' hs hK hN]
  rfl

theorem chiDet_vp (hs : s.Ok) (hK : CharacterValuation.ChiInK s χ) (P : HeightOneSpectrum (𝓞 Z.X.E)) :
    ScalarCharacterTwist.chiDet s χ (ScalarCharacterTwist.vpLat P) = s.σ₀ (CharacterValuation.chiVp s χ P) := by
  rw [vpLat_eq, chiVp_eq, sig_chiDet' hs hK (isSdLat_vpLat P)]

theorem piT_ne_zero (hZ : Z.Ok) (u : Z.Pr.Word) : Z.Pr.piT u ≠ 0 := by
  intro h
  have h1 := hZ.primes.piT_norm u
  rw [h, zero_mul] at h1
  exact (hZ.primes.T_prime u).ne_zero (by exact_mod_cast h1.symm)

theorem T_mem (hZ : Z.Ok) {u : Z.Pr.Word} {P : HeightOneSpectrum (𝓞 Z.X.E)} (hP : P ∈ Z.Pr.vT u) :
    ((Z.Pr.T u : ℕ) : 𝓞 Z.X.E) ∈ P.asIdeal := by
  rw [← hZ.primes.piT_norm u]
  exact Ideal.mul_mem_right _ _ (decoFin_mem_of_mem_divs hP)

theorem T_eq (hZ : Z.Ok) (u : Z.Pr.Word) (τ : Z.X.Tau) :
    ((Z.Pr.T u : ℕ) : 𝓞 Z.X.K) = Z.X.embO τ (Z.Pr.piT u) * Z.X.embO τ (Z.X.conjO (Z.Pr.piT u)) := by
  rw [← map_mul, hZ.primes.piT_norm u, map_natCast]

theorem seenC_iff (hZ : Z.Ok) {u : Z.Pr.Word} {P : HeightOneSpectrum (𝓞 Z.X.E)} (hP : P ∈ Z.Pr.vT u) (w : HeightOneSpectrum (𝓞 Z.X.K)) :
    seenC Z.Pr u w ↔ ((Z.Pr.T u : ℕ) : 𝓞 Z.X.K) ∈ w.asIdeal ∧ ∃ τ, SeesP w τ P := by
  constructor
  · intro h
    obtain ⟨τ₀⟩ : Nonempty Z.X.Tau := Fintype.card_pos_iff.1 hZ.fields.f_pos
    have hT : ((Z.Pr.T u : ℕ) : 𝓞 Z.X.K) ∈ w.asIdeal := by
      rw [T_eq hZ u τ₀]
      exact Ideal.mul_mem_right _ _ (h τ₀)
    obtain ⟨τ, h1 | h1⟩ := GlobalTheory.exists_comap_eq_or_eq_conj Z.X hZ.fieldsConditions _ (hZ.primes.T_prime u) w P hT (T_mem hZ hP)
    · exact ⟨hT, τ, h1⟩
    · have h2 : Z.Pr.piT u ∈ (pullW τ w).asIdeal := h τ
      rw [show pullW τ w = conjPrime₂ P from h1] at h2
      exact absurd h2 (conj_piT_notMem hZ.primes u ⟨P, hP⟩)
  · rintro ⟨_, τ, h⟩ τ'
    have h2 : Z.Pr.piT u ∈ (pullW τ w).asIdeal := by
      rw [show pullW τ w = P from h]
      exact decoFin_mem_of_mem_divs hP
    have h3 : Z.X.embO τ' (Z.Pr.piT u) = Z.X.embO τ (Z.Pr.piT u) := RingOfIntegers.ext (hZ.primes.piT_Kq u τ' τ)
    rw [h3]
    exact h2

theorem seenBarC_iff (hZ : Z.Ok) {u : Z.Pr.Word} {P : HeightOneSpectrum (𝓞 Z.X.E)} (hP : P ∈ Z.Pr.vT u) (w : HeightOneSpectrum (𝓞 Z.X.K)) :
    seenBarC Z.Pr u w ↔ ((Z.Pr.T u : ℕ) : 𝓞 Z.X.K) ∈ w.asIdeal ∧ ∃ τ, SeesPbar w τ P := by
  constructor
  · intro h
    obtain ⟨τ₀⟩ : Nonempty Z.X.Tau := Fintype.card_pos_iff.1 hZ.fields.f_pos
    have hT : ((Z.Pr.T u : ℕ) : 𝓞 Z.X.K) ∈ w.asIdeal := by
      rw [T_eq hZ u τ₀]
      exact Ideal.mul_mem_left _ _ (h τ₀)
    obtain ⟨τ, h1 | h1⟩ := GlobalTheory.exists_comap_eq_or_eq_conj Z.X hZ.fieldsConditions _ (hZ.primes.T_prime u) w P hT (T_mem hZ hP)
    · have h2 : Z.X.conjO (Z.Pr.piT u) ∈ (pullW τ w).asIdeal := h τ
      rw [show pullW τ w = P from h1] at h2
      exact absurd h2 (conj_piT_notMem hZ.primes u ⟨P, hP⟩)
    · exact ⟨hT, τ, h1⟩
  · rintro ⟨_, τ, h⟩ τ'
    have h2 : cO Z.X.E (Z.Pr.piT u) ∈ (pullW τ w).asIdeal := by
      rw [show pullW τ w = conjPrime₂ P from h, mem_conjP, cO_cO]
      exact decoFin_mem_of_mem_divs hP
    have h3 : Z.X.embO τ' (Z.X.conjO (Z.Pr.piT u)) = Z.X.embO τ (Z.X.conjO (Z.Pr.piT u)) := by
      apply RingOfIntegers.ext
      change Z.X.emb τ' (star (Z.Pr.piT u : Z.X.E)) = Z.X.emb τ (star (Z.Pr.piT u : Z.X.E))
      rw [hZ.fields.emb_star, hZ.fields.emb_star, hZ.primes.piT_Kq u τ' τ]
    rw [h3]
    exact h2

theorem partA_iff (hZ : Z.Ok) (hs : s.Ok) (hχ : TaylorLogMetric.IsChi D χ) (hK : CharacterValuation.ChiInK s χ) (u : Z.Pr.Word) :
    CharacterValuation.PartA Z s χ u ↔ ScalarCharacterTwist.PartA s χ u := by
  refine forall₂_congr fun P hP => ?_
  have h0 : CharacterValuation.chiVp s χ P ≠ 0 := by
    rw [chiVp_eq]
    exact chiDet_ne_zero hs hχ hK (isSdLat_vpLat P)
  have hT := hZ.primes.T_prime u
  rw [chiDet_vp hs hK, ScalarCharacterTwist.modOne_iff]
  refine and_congr Iff.rfl (and_congr (forall₂_congr fun w _ => (unit_iff _ w _).symm) ⟨fun h => ⟨fun w hw => ?_, fun w hw => ?_⟩, ?_⟩)
  · obtain ⟨h1, τ, h2⟩ := (seenC_iff hZ hP w).1 hw
    exact (hasVal_iff _ w hT h1 _ _).2 ⟨h0, (h w h1 τ).1 h2⟩
  · obtain ⟨h1, τ, h2⟩ := (seenBarC_iff hZ hP w).1 hw
    exact (hasVal_iff _ w hT h1 _ _).2 ⟨h0, (h w h1 τ).2 h2⟩
  · rintro ⟨h1, h2⟩ w hw τ
    exact ⟨fun h => ((hasVal_iff _ w hT hw _ _).1 (h1 w ((seenC_iff hZ hP w).2 ⟨hw, τ, h⟩))).2,
      fun h => ((hasVal_iff _ w hT hw _ _).1 (h2 w ((seenBarC_iff hZ hP w).2 ⟨hw, τ, h⟩))).2⟩

theorem detUnit_of_stdOver (hZ : Z.Ok) {u : Z.Pr.Word} {n : ℕ} {N : Submodule (𝓞 Z.X.E) (Sp Z.X.E n)}
    (h : CharacterValuation.StdOver (Z.Pr.T u) N) : ScalarCharacterTwist.DetUnitAt (Z.Pr.vT u) N :=
  fun P hP => ordDet_of_std (h P (T_mem hZ hP))

theorem stdOver_of_detUnit (hZ : Z.Ok) {u : Z.Pr.Word} {n : ℕ} {N : Submodule (𝓞 Z.X.E) (Sp Z.X.E n)} (hN : IsSdLat N)
    (h : ScalarCharacterTwist.DetUnitAt (Z.Pr.vT u) N) : CharacterValuation.StdOver (Z.Pr.T u) (lat1 (detI N)) := by
  intro P hP
  apply standard_rank_one_lattice_of_det hN.1
  rw [← hZ.primes.piT_norm u] at hP
  rcases P.isPrime.mem_or_mem hP with h1 | h1
  · exact h P ((mem_divs (piT_ne_zero hZ u) P).2 h1)
  · have := ordDet_conj hN (h (conjPrime₂ P) ((mem_divs (piT_ne_zero hZ u) _).2 h1))
    rwa [conjP_conjP] at this

theorem mu_offset_rank_one_lattice (SB : Finset (HeightOneSpectrum (𝓞 Z.X.E))) (mU : HeightOneSpectrum (𝓞 Z.X.E) → Z.X.Kˣ) {n : ℕ}
    {N : Submodule (𝓞 Z.X.E) (Sp Z.X.E n)} (hN : IsSdLat N) : muOff sel SB mU (lat1 (detI N)) = muOff sel SB mU N := by
  unfold muOff
  simp only [order_det_rank_one_lattice _ hN.1]

theorem mu_inverse_rank_one_lattice (i : ℕ) {n : ℕ} {N : Submodule (𝓞 Z.X.E) (Sp Z.X.E n)} (hN : IsSdLat N) (fr : Frs Z.X.E n (rowSG Z.Pr sel mu)) :
    CharacterValuation.muInv Z sel mu cst i (lat1 (detI N)) (fun P => detFr (fr P)) = CharacterValuation.muInv Z sel mu cst i N fr := by
  unfold CharacterValuation.muInv muInvDet
  simp only [mu_offset_rank_one_lattice _ _ hN, det_detFr]

theorem chiDet_detI {n : ℕ} (N : Submodule (𝓞 Z.X.E) (Sp Z.X.E n)) :
    CharacterValuation.chiDet s χ (lat1 (detI N)) = CharacterValuation.chiDet s χ N := by
  rw [char_det_rank_one_lattice, CharacterValuation.chiDet, detId_lat]

theorem unit_chiF {w : HeightOneSpectrum (𝓞 Z.X.K)} {x y : Z.X.K} (hx : CharacterValuation.UnitAt w x) (hy : CharacterValuation.UnitAt w y) (a b : ℤ) :
    CharacterValuation.UnitAt w (x ^ a * y ^ b) := by
  unfold CharacterValuation.UnitAt at *
  rw [map_mul, map_zpow₀, map_zpow₀, hx, hy, one_zpow, one_zpow, one_mul]

theorem unit_scal {w : HeightOneSpectrum (𝓞 Z.X.K)} {x y : Z.X.K} (hx : w.valuation Z.X.K x = 1) (hy : w.valuation Z.X.K y = 1) :
    w.valuation Z.X.K (x * y⁻¹) = 1 := by
  rw [map_mul, map_inv₀, hx, hy, inv_one, one_mul]

theorem exists_frames (SB : Finset (HeightOneSpectrum (𝓞 Z.X.E))) {n : ℕ} {N : Submodule (𝓞 Z.X.E) (Sp Z.X.E n)} (hN : IsSdLat N) :
    ∃ fr : Frs Z.X.E n SB, ScalarCharacterTwist.FrOf N fr := by
  choose f hf using fun P : SB => exists_isFr P.1 hN.1
  exact ⟨f, hf⟩

theorem partBStd_of_partB (hs : s.Ok) (hK : CharacterValuation.ChiInK s χ) {u : Z.Pr.Word} (h : ScalarCharacterTwist.PartB s χ sel mu cst u) :
    ScalarCharacterTwist.PartBStd s χ sel mu cst u := by
  intro w hw i N fr N' fr' hN hN' hf hf' h1 h1'
  obtain ⟨a1, -, -, a4, a5⟩ := h w hw i _ N fr hN hf fun P hP => ordDet_of_std (h1 P hP)
  obtain ⟨b1, -, -, b4, b5⟩ := h w hw i _ N' fr' hN' hf' fun P hP => ordDet_of_std (h1' P hP)
  refine ⟨?_, a4, b4, a5, b5, unit_scal a5 b5⟩
  rw [sig_chiDet' hs hK hN, unit_iff] at a1
  rw [sig_chiDet' hs hK hN', unit_iff] at b1
  rw [ScalarCharacterTwist.chiFJ, chiFac_eq hs hK hN hN', unit_iff]
  exact unit_chiF a1 b1 _ _

theorem partBChi_of_partB (hZ : Z.Ok) (hs : s.Ok) (hK : CharacterValuation.ChiInK s χ) {u : Z.Pr.Word} (h : ScalarCharacterTwist.PartB s χ sel mu cst u)
    (w : HeightOneSpectrum (𝓞 Z.X.K)) (hw : ((Z.Pr.T u : ℕ) : 𝓞 Z.X.K) ∈ w.asIdeal) : CharacterValuation.PartBChi Z s χ u w := by
  have core : ∀ (n : ℕ) (N : Submodule (𝓞 Z.X.E) (Sp Z.X.E n)), IsSdLat N → ScalarCharacterTwist.DetUnitAt (Z.Pr.vT u) N →
      CharacterValuation.UnitAt w (CharacterValuation.chiDet s χ N) := fun n N hN hd => by
    obtain ⟨fr, hf⟩ := exists_frames (rowSG Z.Pr sel mu) hN
    have := (h w hw ⟨0, lt_of_lt_of_le two_pos Z.R.two_le_m⟩ n N fr hN hf hd).1
    rwa [sig_chiDet' hs hK hN, unit_iff] at this
  refine ⟨fun I hI hT => ?_, fun n N hN hd => core n N hN (detUnit_of_stdOver hZ hd), fun a b N N' _ _ hN hN' hd hd' => ?_⟩
  · have := core 1 _ (self_dual_rank_one_lattice (normOne_pull hs hI)) fun P hP => ordDet_of_std (standard_rank_one_lattice_of_local (by
      ext x
      rw [mem_localization_pullback, hT _ (by rw [mem_pushP, map_natCast]; exact T_mem hZ hP), ← mem_localization_pullback, pull_one]))
    rwa [char_det_rank_one_lattice, pull_pull] at this
  · rw [CharacterValuation.chiFK, chiFac_eq hs hK hN hN', desc_sig]
    exact unit_chiF (core a N hN (detUnit_of_stdOver hZ hd)) (core b N' hN' (detUnit_of_stdOver hZ hd')) _ _

theorem partB_iff (hZ : Z.Ok) (hs : s.Ok) (hK : CharacterValuation.ChiInK s χ) (u : Z.Pr.Word) :
    (∀ w : HeightOneSpectrum (𝓞 Z.X.K), ((Z.Pr.T u : ℕ) : 𝓞 Z.X.K) ∈ w.asIdeal →
      CharacterValuation.PartBChi Z s χ u w ∧ ∀ i : Fin Z.R.m, CharacterValuation.PartBMu Z s χ sel mu cst u w i.1) ↔
    ScalarCharacterTwist.PartB s χ sel mu cst u ∧ ScalarCharacterTwist.PartBStd s χ sel mu cst u := by
  constructor
  · intro h
    have hB : ScalarCharacterTwist.PartB s χ sel mu cst u := by
      intro w hw i n N fr hN hf hd
      have hN1 := self_dual_rank_one_lattice (normOne_detI hN)
      have hd1 := stdOver_of_detUnit hZ hN hd
      have a1 := (h w hw).1.2.1 1 _ hN1 hd1
      obtain ⟨a2, a3⟩ := ((h w hw).2 i).1 1 _ hN1 hd1
      obtain ⟨a3, a4, a5⟩ := a3 (fun P => detFr (fr P)) fun P => isFr_detFr (hf P)
      rw [CharacterValuation.rho, mu_inverse_rank_one_lattice _ hN, chiDet_detI] at a4
      rw [CharacterValuation.rho', mu_inverse_rank_one_lattice _ hN, chiDet_detI] at a5
      rw [chiDet_detI] at a1
      rw [mu_offset_rank_one_lattice _ _ hN] at a2
      rw [mu_inverse_rank_one_lattice _ hN] at a3
      rw [sig_chiDet' hs hK hN, rhoJ_eq hs hK _ hN, rhoJ'_eq hs hK _ hN, unit_iff, unit_iff, unit_iff]
      exact ⟨a1, a4, a5, a2, a3⟩
    exact ⟨hB, partBStd_of_partB hs hK hB⟩
  · rintro ⟨h, -⟩ w hw
    refine ⟨partBChi_of_partB hZ hs hK h w hw, fun i => ⟨fun n N hN hd => ⟨?_, fun fr hf => ?_⟩, ?_⟩⟩
    · obtain ⟨fr, hf⟩ := exists_frames (rowSG Z.Pr sel mu) hN
      exact (h w hw i n N fr hN hf (detUnit_of_stdOver hZ hd)).2.2.2.1
    · obtain ⟨-, a2, a3, -, a5⟩ := h w hw i n N fr hN hf (detUnit_of_stdOver hZ hd)
      rw [rhoJ_eq hs hK _ hN, unit_iff] at a2
      rw [rhoJ'_eq hs hK _ hN, unit_iff] at a3
      exact ⟨a5, a2, a3⟩
    · intro a b N fr N' fr' hN hN' hd hd' hf hf'
      exact unit_scal (h w hw i a N fr hN hf (detUnit_of_stdOver hZ hd)).2.2.2.2
        (h w hw i b N' fr' hN' hf' (detUnit_of_stdOver hZ hd')).2.2.2.2

theorem partC_iff (hZ : Z.Ok) (hs : s.Ok) (hχ : TaylorLogMetric.IsChi D χ) (hK : CharacterValuation.ChiInK s χ) (u : Z.Pr.Word) :
    (∀ w : HeightOneSpectrum (𝓞 Z.X.K), ((Z.Pr.T u : ℕ) : 𝓞 Z.X.K) ∈ w.asIdeal → ∀ i : Fin Z.R.m, CharacterValuation.PartC Z s χ sel mu cst u w i) ↔
    ScalarCharacterTwist.PartC s χ sel mu cst u := by
  refine forall₂_congr fun w hw => forall_congr' fun i => forall₂_congr fun P _ => forall₂_congr fun τ _ => ?_
  have hT := hZ.primes.T_prime u
  have h0 : CharacterValuation.chiVp s χ P ≠ 0 := by
    rw [chiVp_eq]
    exact chiDet_ne_zero hs hχ hK (isSdLat_vpLat P)
  have e1 : ScalarCharacterTwist.sPrime Z i τ = CharacterValuation.sPrime Z i τ := rfl
  have e2 : ScalarCharacterTwist.sExp Z i τ = CharacterValuation.sPlain Z i τ := rfl
  rw [chiDet_vp hs hK, vpLat_eq, rhoJ_eq hs hK _ (isSdLat_vpLat P), rhoJ'_eq hs hK _ (isSdLat_vpLat P), e1, e2]
  simp only [hasVal_iff _ w hT hw]
  constructor
  · rintro ⟨a1, a2, a3, a4⟩ r ⟨-, rfl⟩
    exact ⟨⟨a1, a3⟩, a2, a4⟩
  · intro h
    obtain ⟨⟨a1, a3⟩, a2, a4⟩ := h _ ⟨h0, rfl⟩
    exact ⟨a1, a2, a3, a4⟩

theorem partD_iff (hs : s.Ok) (hχ : TaylorLogMetric.IsChi D χ) (hK : CharacterValuation.ChiInK s χ) :
    (∀ i : Fin Z.R.m, CharacterValuation.PartD Z s χ sel mu cst i.1) ↔ ScalarCharacterTwist.PartD s χ sel mu cst := by
  refine forall_congr' fun i => forall₃_congr fun n N fr => forall₂_congr fun hN _ => ?_
  rw [rhoJ_eq hs hK _ hN, rhoJ'_eq hs hK _ hN, sig_chiDet' hs hK hN, ← map_mul, ← map_zpow₀, s.σ₀.injective.eq_iff]
  exact and_iff_right (chiDet_ne_zero hs hχ hK hN)

theorem unram_iff (u : Z.Pr.Word) :
    (CharacterValuation.UnramOver (mu : Chr Z.X.F Z.X.E Z.X.K) (Z.Pr.T u) ∧ ∀ k, CharacterValuation.UnramOver (mu : Chr Z.X.F Z.X.E Z.X.K) (Z.Pr.g k)) ↔
      ScalarCharacterTwist.UnrTG mu u :=
  ⟨fun h v hv => ⟨fun h1 => h.1 v h1 hv, fun k h1 => h.2 k v h1 hv⟩,
    fun h => ⟨fun v h1 hv => (h v hv).1 h1, fun k v h1 hv => (h v hv).2 k h1⟩⟩

theorem exists_isSel (X : Fields) : ∃ sel, IsSel X sel := by
  have : ∀ v : HeightOneSpectrum (𝓞 X.F), ∃ P : HeightOneSpectrum (𝓞 X.E), P.asIdeal.under (𝓞 X.F) = v.asIdeal := by
    intro v
    have := v.isMaximal
    obtain ⟨Q, hQ, h⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 X.E) v.asIdeal (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (FaithfulSMul.algebraMap_injective (𝓞 X.F) (𝓞 X.E))]
      exact bot_le)
    exact ⟨⟨Q, hQ.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hQ (RingOfIntegers.not_isField _)⟩, h⟩
  choose f hf using this
  exact ⟨f, hf⟩

theorem unrTG_one (u : Z.Pr.Word) : ScalarCharacterTwist.UnrTG (1 : Tup Z.X.F Z.X.E Z.X.K S) u :=
  fun _ hv => absurd (fun _ _ => rfl) hv

theorem exists_cst (hZ : Z.Ok) {m0 : Fin Z.R.m → Formalism.L2.Host.HChar Z.X.E} {eta : Formalism.L2.Host.HChar Z.X.E}
    (h : Z.Ch.Tied Z.sig0 (fun j τ => (Z.W.row τ).e j) m0 eta)
    (sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)) (mu : Tup Z.X.F Z.X.E Z.X.K S) :
    ∃ cst : LocCst Z.X (rowSG Z.Pr sel mu), MuqTieG (Pr := Z.Pr) (R := Z.R) sel mu cst Z.sig0 m0 := by
  choose f hf using GlobalTheory.TameVal.locK_mem_coeff Z hZ m0 eta h
  have hq : ∀ P : HeightOneSpectrum (𝓞 Z.X.E), ((Formalism.L2.Col.qOf P : ℕ) : Z.X.E) ≠ 0 := fun P => by
    have : Ideal.absNorm P.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact P.ne_bot
    exact_mod_cast this
  refine ⟨⟨fun _ _ => 1, fun _ => 1, fun _ => 1, fun j P => if h : j - 1 < Z.R.m then
    (f ⟨j - 1, h⟩ P.1 (Units.mk0 _ (hq P.1)))⁻¹ * (((qVal (mu : Chr Z.X.F Z.X.E Z.X.K) P.1)⁻¹ : Z.X.Kˣ) : Z.X.K) else 0,
    0, 0, 0, false⟩, fun i hi P _ qu hqu => ?_⟩
  obtain rfl : qu = Units.mk0 _ (hq P.1) := Units.ext hqu
  have hi' : i + 1 - 1 < Z.R.m := hi
  simp only [dif_pos hi']
  rw [map_mul, map_inv₀, hf]
  rfl

end Parts

def CharValuationsInK : Prop :=
  ∀ (D : Dat), D.Ok → ∀ (H : D7) (s : Seam H D.X), s.Ok → s.σ₀ = D.sig0 → ∀ χ : TaylorLogMetric.IdE H → ℂ, TaylorLogMetric.IsChi H χ → CharacterValuation.ChiInK s χ →
  ∀ u : D.Pr.Word,
    ScalarCharacterTwist.PartA s χ u ∧
    ∀ (sel : HeightOneSpectrum (𝓞 D.X.F) → HeightOneSpectrum (𝓞 D.X.E)), IsSel D.X sel →
    ∀ (S : Set ℕ) (mu : Tup D.X.F D.X.E D.X.K S), ScalarCharacterTwist.UnrTG mu u →
    ∀ (m0 : Fin D.R.m → Formalism.L2.Host.HChar D.X.E) (eta : Formalism.L2.Host.HChar D.X.E),
      D.Ch.Tied D.sig0 (fun j τ => (D.W.row τ).e j) m0 eta →
    ∀ cst : LocCst D.X (rowSG D.Pr sel mu), MuqTieG sel mu cst D.sig0 m0 →
      ScalarCharacterTwist.PartB s χ sel mu cst u ∧ ScalarCharacterTwist.PartBStd s χ sel mu cst u ∧ ScalarCharacterTwist.PartC s χ sel mu cst u ∧ ScalarCharacterTwist.PartD s χ sel mu cst

theorem charValAtT_iff : CharacterValuation.CharValAtT ↔ CharValuationsInK := by
  constructor
  · intro h Z hZ D s hs hσ χ hχ hK u
    obtain ⟨h1, h2, h3⟩ := h Z D s χ u hZ hs hσ hχ hK
    refine ⟨(partA_iff hZ hs hχ hK u).1 h1, fun sel hsel S mu hmu m0 eta ht cst hc => ?_⟩
    have h4 := h3 m0 eta ht sel hsel S mu ((unram_iff u).2 hmu).1 ((unram_iff u).2 hmu).2 cst hc
    have h5 := (partB_iff hZ hs hK u).1 fun w hw => ⟨h2 w hw, fun i => ((h4 i).1 w hw).1⟩
    exact ⟨h5.1, h5.2, (partC_iff hZ hs hχ hK u).1 fun w hw i => ((h4 i).1 w hw).2, (partD_iff hs hχ hK).1 fun i => (h4 i).2⟩
  · intro h Z D s χ u hZ hs hσ hχ hK
    obtain ⟨h1, h2⟩ := h Z hZ D s hs hσ χ hχ hK u
    refine ⟨(partA_iff hZ hs hχ hK u).2 h1, ?_, fun m0 eta ht sel hsel S mu hT hg cst hc i => ?_⟩
    · obtain ⟨m0, eta, ht⟩ := hZ.hecke
      obtain ⟨sel, hsel⟩ := exists_isSel Z.X
      obtain ⟨cst, hc⟩ := exists_cst hZ ht sel (1 : Tup Z.X.F Z.X.E Z.X.K ∅)
      exact partBChi_of_partB hZ hs hK (h2 sel hsel ∅ 1 (unrTG_one u) m0 eta ht cst hc).1
    · obtain ⟨b1, b2, b3, b4⟩ := h2 sel hsel S mu ((unram_iff u).1 ⟨hT, hg⟩) m0 eta ht cst hc
      exact ⟨fun w hw => ⟨((partB_iff hZ hs hK u).2 ⟨b1, b2⟩ w hw).2 i, (partC_iff hZ hs hχ hK u).2 b3 w hw i⟩,
        (partD_iff hs hχ hK).2 b4 i⟩

theorem typings_agree :
    (∀ (Z : Dat) (D : D7) (s : Seam D Z.X) (χ : TaylorLogMetric.IdE D → ℂ) (u : Z.Pr.Word), Z.Ok → s.Ok → TaylorLogMetric.IsChi D χ → CharacterValuation.ChiInK s χ →
      (CharacterValuation.PartA Z s χ u ↔ ScalarCharacterTwist.PartA s χ u) ∧
      ∀ (sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)) (S : Set ℕ) (mu : Tup Z.X.F Z.X.E Z.X.K S)
        (cst : LocCst Z.X (rowSG Z.Pr sel mu)),
        ((CharacterValuation.UnramOver (mu : Chr Z.X.F Z.X.E Z.X.K) (Z.Pr.T u) ∧ ∀ k, CharacterValuation.UnramOver (mu : Chr Z.X.F Z.X.E Z.X.K) (Z.Pr.g k)) ↔
          ScalarCharacterTwist.UnrTG mu u) ∧
        ((∀ w : HeightOneSpectrum (𝓞 Z.X.K), ((Z.Pr.T u : ℕ) : 𝓞 Z.X.K) ∈ w.asIdeal →
          CharacterValuation.PartBChi Z s χ u w ∧ ∀ i : Fin Z.R.m, CharacterValuation.PartBMu Z s χ sel mu cst u w i.1) ↔
          ScalarCharacterTwist.PartB s χ sel mu cst u ∧ ScalarCharacterTwist.PartBStd s χ sel mu cst u) ∧
        ((∀ w : HeightOneSpectrum (𝓞 Z.X.K), ((Z.Pr.T u : ℕ) : 𝓞 Z.X.K) ∈ w.asIdeal →
          ∀ i : Fin Z.R.m, CharacterValuation.PartC Z s χ sel mu cst u w i) ↔ ScalarCharacterTwist.PartC s χ sel mu cst u) ∧
        ((∀ i : Fin Z.R.m, CharacterValuation.PartD Z s χ sel mu cst i.1) ↔ ScalarCharacterTwist.PartD s χ sel mu cst)) ∧
    (CharacterValuation.CharValAtT ↔ CharValuationsInK) ∧ (ScalarCharacterTwist.CharValuations → CharacterValuation.CharValAtT) :=
  ⟨fun _ _ _ _ u hZ hs hχ hK => ⟨partA_iff hZ hs hχ hK u, fun _ _ _ _ =>
      ⟨unram_iff u, partB_iff hZ hs hK u, partC_iff hZ hs hχ hK u, partD_iff hs hχ hK⟩⟩,
    charValAtT_iff, fun h => charValAtT_iff.2 fun Z hZ D s hs hσ χ hχ _ => h Z hZ D s hs hσ χ hχ⟩

end GlobalTheory.CharValCompare
