import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocInd
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocGen
import Formalism.LocalToGlobal.GlobalTheory.CoefficientMapSurjective

noncomputable section

open NumberField Matrix

namespace Formalism.L2.GlobalTheoryTheory.ColValS

section Dual

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem hform_eq (σ : K →+* K) (J : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    Formalism.UG.hform σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_mulVec (σ : K →+* K) (J M : Matrix (Fin n) (Fin n) K) (v y : Fin n → K) :
    Formalism.UG.hform σ J (M *ᵥ v) y = ∑ a, σ (v a) * ((Formalism.UG.cT σ M * J) *ᵥ y) a := by
  rw [hform_eq]
  have e1 : (fun i => σ ((M *ᵥ v) i)) = M.map σ *ᵥ fun a => σ (v a) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
  rw [e1, dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec]
  rfl

variable (l : ℕ) [hl : Fact l.Prime]

theorem col_mem_of_isLocBasis {L : Set (Fin n → K)} {Y : GL (Fin n) K} (hY : Formalism.L2.Forms.IsLocBasis l L Y) (a : Fin n) :
    ∃ t : ℕ, ¬ l ∣ t ∧ (t : K) • (fun r => (Y : Matrix (Fin n) (Fin n) K) r a) ∈ L := by
  refine (hY _).2 ⟨1, hl.out.not_dvd_one, fun b => ?_⟩
  have e : (((Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ fun r => (Y : Matrix (Fin n) (Fin n) K) r a) b =
      (((Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (Y : Matrix (Fin n) (Fin n) K)) b a := rfl
  rw [Nat.cast_one, one_mul, e, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply]
  split_ifs
  · exact ⟨1, map_one _⟩
  · exact ⟨0, map_zero _⟩

theorem den_of_isLocBasis {L : Submodule (𝓞 K) (Fin n → K)} (hfg : L.FG) {Y : GL (Fin n) K}
    (hY : Formalism.L2.Forms.IsLocBasis l (L : Set (Fin n → K)) Y) :
    ∃ d : ℕ, ¬ l ∣ d ∧ ∀ x ∈ L, ∀ a, (d : K) * ((((Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) a) ∈
      (algebraMap (𝓞 K) K).range := by
  classical
  obtain ⟨S, hS⟩ := hfg
  have ht : ∀ g ∈ S, ∃ t : ℕ, ¬ l ∣ t ∧ ∀ a, (t : K) * ((((Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ g) a) ∈
      (algebraMap (𝓞 K) K).range := fun g hg =>
    (hY g).1 ⟨1, hl.out.not_dvd_one, by
      rw [Nat.cast_one, one_smul, SetLike.mem_coe, ← hS]; exact Submodule.subset_span hg⟩
  let t : (Fin n → K) → ℕ := fun g => if h : g ∈ S then (ht g h).choose else 1
  have htS : ∀ g ∈ S, ¬ l ∣ t g ∧ ∀ a, (t g : K) * ((((Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ g) a) ∈
      (algebraMap (𝓞 K) K).range := fun g hg => by
    simp only [t, dif_pos hg]; exact (ht g hg).choose_spec
  refine ⟨∏ g ∈ S, t g, ?_, fun x hx => ?_⟩
  · rw [Prime.dvd_finsetProd_iff hl.out.prime]
    rintro ⟨g, hg, hdvd⟩
    exact (htS g hg).1 hdvd
  · rw [← hS] at hx
    induction hx using Submodule.span_induction with
    | mem g hg =>
      intro a
      rw [← Finset.mul_prod_erase S t hg, Nat.cast_mul, mul_comm ((t g : ℕ) : K), mul_assoc]
      exact Subring.mul_mem _ ⟨(∏ g' ∈ S.erase g, t g' : ℕ), map_natCast _ _⟩ ((htS g hg).2 a)
    | zero =>
      intro a
      rw [Matrix.mulVec_zero, Pi.zero_apply, mul_zero]
      exact Subring.zero_mem _
    | add x y _ _ hx hy =>
      intro a
      rw [Matrix.mulVec_add, Pi.add_apply, mul_add]
      exact Subring.add_mem _ (hx a) (hy a)
    | smul r x _ hx =>
      intro a
      rw [← algebraMap_smul K r x, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm]
      exact Subring.mul_mem _ ⟨r, rfl⟩ (hx a)

theorem sig_range (σ : K →+* K) {y : K} (hy : y ∈ (algebraMap (𝓞 K) K).range) : σ y ∈ (algebraMap (𝓞 K) K).range := by
  obtain ⟨r, rfl⟩ := hy
  obtain ⟨r', hr'⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.sig_int σ r
  exact ⟨r', hr'⟩

theorem isLocBasis_dual (σ : K →+* K) (J : Matrix (Fin n) (Fin n) K) {L : Submodule (𝓞 K) (Fin n → K)} (hfg : L.FG)
    {Y : GL (Fin n) K} (hY : Formalism.L2.Forms.IsLocBasis l (L : Set (Fin n → K)) Y) (B0 : GL (Fin n) K)
    (hB0 : ((B0⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Formalism.UG.cT σ (Y : Matrix (Fin n) (Fin n) K) * J) :
    Formalism.L2.Forms.IsLocBasis l (Formalism.BasicNotions.dualSet σ J L) B0 := by
  intro x
  rw [hB0]
  constructor
  · rintro ⟨s, hs, hx⟩
    choose t ht htL using col_mem_of_isLocBasis l hY
    refine ⟨s * ∏ b, t b, ?_, fun a => ?_⟩
    · rw [Nat.Prime.dvd_mul hl.out, not_or]
      refine ⟨hs, ?_⟩
      rw [Prime.dvd_finsetProd_iff hl.out.prime]
      rintro ⟨b, -, hb⟩
      exact ht b hb
    · have h1 := hx _ (htL a)
      have e1 : (t a : K) • (fun r => (Y : Matrix (Fin n) (Fin n) K) r a) =
          (Y : Matrix (Fin n) (Fin n) K) *ᵥ ((t a : K) • Pi.single a (1 : K)) := by
        rw [Matrix.mulVec_smul, Matrix.mulVec_single_one]
        rfl
      rw [e1, hform_mulVec, Finset.sum_eq_single a (fun b _ hb => by simp [hb])
        (fun h => absurd (Finset.mem_univ a) h)] at h1
      simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, map_natCast, Matrix.mulVec_smul] at h1
      rw [← Finset.mul_prod_erase Finset.univ t (Finset.mem_univ a)]
      have e2 : ((s * (t a * ∏ b ∈ Finset.univ.erase a, t b) : ℕ) : K) *
          ((Formalism.UG.cT σ (Y : Matrix (Fin n) (Fin n) K) * J) *ᵥ x) a =
          ((∏ b ∈ Finset.univ.erase a, t b : ℕ) : K) *
            ((t a : K) * ((s : K) * ((Formalism.UG.cT σ (Y : Matrix (Fin n) (Fin n) K) * J) *ᵥ x) a)) := by
        push_cast; ring
      rw [e2]
      exact Subring.mul_mem _ ⟨_, map_natCast _ _⟩ h1
  · rintro ⟨s', hs', h'⟩
    obtain ⟨d, hd, hdL⟩ := den_of_isLocBasis l hfg hY
    refine ⟨d * s', ?_, ?_⟩
    · rw [Nat.Prime.dvd_mul hl.out, not_or]; exact ⟨hd, hs'⟩
    · intro z hz
      have hz' : z = (Y : Matrix (Fin n) (Fin n) K) *ᵥ ((((Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *ᵥ z) := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
      rw [hz', hform_mulVec]
      refine Subring.sum_mem _ fun b _ => ?_
      rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
      have e : σ (((((Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *ᵥ z) b) *
          (((d * s' : ℕ) : K) * ((Formalism.UG.cT σ (Y : Matrix (Fin n) (Fin n) K) * J) *ᵥ x) b) =
          σ ((d : K) * ((((Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *ᵥ z) b) *
            ((s' : K) * ((Formalism.UG.cT σ (Y : Matrix (Fin n) (Fin n) K) * J) *ᵥ x) b) := by
        rw [map_mul, map_natCast]; push_cast; ring
      rw [e]
      exact Subring.mul_mem _ (sig_range σ (hdL z hz b)) (h' b)

end Dual

section Ten

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem ten_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (f : ι → MvPolynomial (Fin n × Fin n) R) :
    Formalism.MainNotions.flipTwoThree.ten (fun τ => MvPolynomial.map φ (f τ)) = MvPolynomial.map φ (Formalism.MainNotions.flipTwoThree.ten f) := by
  unfold Formalism.MainNotions.flipTwoThree.ten
  rw [map_prod]
  exact Finset.prod_congr rfl fun τ _ => (MvPolynomial.map_rename _ _ _).symm

end Ten

variable (D : Formalism.BasicNotions.D7)

theorem map_gen {n : ℕ} (r : D.what₂.LL) (f : D.what₂.Tau → MvPolynomial (Fin n × Fin n) ℤ) :
    MvPolynomial.map D.what₂.embLL (r • Formalism.MainNotions.flipTwoThree.ten (fun τ => MvPolynomial.map (Int.castRingHom D.what₂.LL) (f τ))) =
      D.what₂.embLL r • Formalism.MainNotions.flipTwoThree.ten (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ)) := by
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul, ten_map, ten_map,
    MvPolynomial.map_map, RingHom.ext_int (D.what₂.embLL.comp (Int.castRingHom D.what₂.LL)) (Int.castRingHom ℂ)]

theorem mem_intSpanAt_iff_map (w : D.what₂.places.Pl) {n : ℕ} (lam : D.what₂.Tau → Formalism.BasicNotions.DomWeight n)
    (p : MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL) :
    p ∈ Formalism.MainNotions.flipTwoThree.IntSpanAt D w lam ↔ MvPolynomial.map D.what₂.embLL p ∈ Formalism.L2.Forms.IntSpan D w lam := by
  constructor
  · intro hp
    induction hp using AddSubgroup.closure_induction with
    | mem q hq =>
      obtain ⟨r, f, hr, hf, rfl⟩ := hq
      exact AddSubgroup.subset_closure ⟨r, f, hr, hf, map_gen D r f⟩
    | zero => rw [map_zero]; exact AddSubgroup.zero_mem _
    | add q q' _ _ h1 h2 => rw [map_add]; exact AddSubgroup.add_mem _ h1 h2
    | neg q _ h1 => rw [map_neg]; exact AddSubgroup.neg_mem _ h1
  · intro hp
    have hle : Formalism.L2.Forms.IntSpan D w lam ≤
        (Formalism.MainNotions.flipTwoThree.IntSpanAt D w lam).map (MvPolynomial.map D.what₂.embLL).toAddMonoidHom := by
      unfold Formalism.L2.Forms.IntSpan
      rw [AddSubgroup.closure_le]
      rintro _ ⟨r, f, hr, hf, rfl⟩
      exact ⟨_, AddSubgroup.subset_closure ⟨r, f, hr, hf, rfl⟩, map_gen D r f⟩
    obtain ⟨q, hq, hqe⟩ := hle hp
    have : q = p := MvPolynomial.map_injective _ D.what₂.embLL.injective hqe
    rwa [← this]

theorem embT_mem_Ow (w : D.what₂.places.Pl) (τ : D.what₂.Tau) (y : D.host.E) (s : ℕ)
    (hs : ¬ D.what₂.places.resChar w ∣ s) (hy : (s : D.host.E) * y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) :
    Formalism.L2.Forms.embT D τ y ∈ Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_Ow D w := by
  rw [Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_embT_eq]
  exact Subring.mem_map.2 ⟨_, Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_val_locInt D w
    ((D.host.sigmaOf (D.eTau τ : D.R.GG) : D.host.E →+* D.host.E)) y s hs hy, rfl⟩

theorem change_mem (w : D.what₂.places.Pl) (τ : D.what₂.Tau) {n : ℕ} {L : Set (Fin n → D.host.E)}
    {B B₂ : GL (Fin n) D.host.E} (hB : Formalism.L2.Forms.IsLocBasis (D.what₂.places.resChar w) L B)
    (hB₂ : Formalism.L2.Forms.IsLocBasis (D.what₂.places.resChar w) L B₂) (a b : Fin n) :
    Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) ((B₂⁻¹ * B : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) τ a b ∈
      Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_Ow D w := by
  have : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
  obtain ⟨s, hs, hx⟩ := col_mem_of_isLocBasis (D.what₂.places.resChar w) hB b
  obtain ⟨s', hs', h⟩ := (hB₂ _).1 ⟨s, hs, hx⟩
  have e : (((B₂⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) *ᵥ
      fun r => (B : Matrix (Fin n) (Fin n) D.host.E) r b) a =
      ((B₂⁻¹ * B : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) a b := by
    rw [Units.val_mul]; rfl
  have h2 := embT_mem_Ow D w τ _ s' hs' (h a)
  rw [e] at h2
  exact h2

theorem basis_change (w : D.what₂.places.Pl) {n : ℕ} (lam : D.what₂.Tau → Formalism.BasicNotions.DomWeight n)
    (G : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (s : D.what₂.Tau → ℤ) {L : Set (Fin n → D.host.E)}
    {B B₂ : GL (Fin n) D.host.E} (hB : Formalism.L2.Forms.IsLocBasis (D.what₂.places.resChar w) L B)
    (hB₂ : Formalism.L2.Forms.IsLocBasis (D.what₂.places.resChar w) L B₂)
    (Q : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ) (hQ : Q ∈ Formalism.L2.Forms.IntSpan D w lam) :
    ∃ Q₂ ∈ Formalism.L2.Forms.IntSpan D w lam,
      Formalism.L2.Forms.fnOf G s (Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) ((B⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)) Q =
        Formalism.L2.Forms.fnOf G s (Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) ((B₂⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)) Q₂ := by
  set N : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ :=
    fun τ => Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) ((B⁻¹ * B₂ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) τ with hN
  set N' : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ :=
    fun τ => Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) ((B₂⁻¹ * B : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) τ with hN'
  have hNN' : ∀ τ, N τ * N' τ = 1 := fun τ => by
    simp only [hN, hN', Formalism.L2.Forms.atInf]
    rw [← Matrix.map_mul, ← Units.val_mul]
    have : (B⁻¹ * B₂ * (B₂⁻¹ * B) : GL (Fin n) D.host.E) = 1 := by group
    rw [this, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨MvPolynomial.C (∏ τ, (N τ).det ^ s τ) * Formalism.L2.Forms.subP N Q,
    Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwG_intSpan_allSubP D w _ N _ (fun τ g hg => Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.local_GL_stabilises_lattice D w _ _ _ (N τ) (N' τ) (hNN' τ)
      (change_mem D w τ hB₂ hB) (change_mem D w τ hB hB₂) g hg) Q hQ, ?_⟩
  rw [← Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.fnOf_mul]
  have hM : Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) ((B⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) =
      fun τ => N τ * Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) ((B₂⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) τ := by
    funext τ
    simp only [hN, Formalism.L2.Forms.atInf]
    rw [← Matrix.map_mul, ← Units.val_mul]
    congr 2
    group
  rw [hM]

end Formalism.L2.GlobalTheoryTheory.ColValS
