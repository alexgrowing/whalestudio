import Formalism.HermitianCurvature.StatementTL
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameCompletion
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.BlockMinorAbsoluteOfExplicit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HomogeneityNaturalDegree
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WCellMemOmPlus
import Formalism.FormalDegreeBessel.FormalDegreeRatio.BFCell
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OmpCofLPd

namespace Formalism.FourierDecayAlt.P.TLC

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TL
open scoped ComplexConjugate

noncomputable section

variable {k r : ℕ}

lemma om_herm_add (H : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (v w u : Fin (2 * r + k + 1) → ℂ) :
    herm H (v + w) u = herm H v u + herm H w u := by
  simp only [herm, Matrix.mulVec_add, dotProduct_add]

lemma om_herm_smul (H : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (c : ℂ) (v u : Fin (2 * r + k + 1) → ℂ) :
    herm H (c • v) u = c * herm H v u := by
  simp only [herm, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

lemma om_herm_sum {ι : Type*} (s : Finset ι) (H : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (v : ι → Fin (2 * r + k + 1) → ℂ) (u : Fin (2 * r + k + 1) → ℂ) :
    herm H (∑ i ∈ s, v i) u = ∑ i ∈ s, herm H (v i) u := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [herm]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, om_herm_add, ih]

lemma om_herm_smul_right (H : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (c : ℂ) (v u : Fin (2 * r + k + 1) → ℂ) :
    herm H v (c • u) = conj c * herm H v u := by
  simp only [herm, star_smul, smul_dotProduct, smul_eq_mul, Complex.star_def]

lemma om_herm_sum_right {ι : Type*} (s : Finset ι) (H : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (v : Fin (2 * r + k + 1) → ℂ) (u : ι → Fin (2 * r + k + 1) → ℂ) :
    herm H v (∑ i ∈ s, u i) = ∑ i ∈ s, herm H v (u i) := by
  simp only [herm, star_sum, sum_dotProduct]

lemma om_inv_eq {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    Hpk k r * gᴴ * Hpk k r = g⁻¹ := by
  have hH : Hpk k r * Hpk k r = 1 := (hpkFacts k r).2.1
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  symm
  apply Matrix.inv_eq_left_inv
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', hH]

private lemma herm_swap_eq_zero_of_eq_zero (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) w v = conj (herm (Hpk k r) v w) := by
  have hH : (Hpk k r)ᴴ = Hpk k r := (hpkFacts k r).1
  unfold herm
  rw [← Complex.star_def, ← star_dotProduct_star, star_star, Matrix.star_mulVec, hH,
    ← Matrix.dotProduct_mulVec]

lemma om_N3xM_eq {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) : HermitianLatticeCounting.ExpansionTerms.formalDeterminantVectorOnGroup k r Bs.z Bs.z' g = g⁻¹ *ᵥ D.cofL Bs g := by
  have hd : IsUnit g.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg
  have hZ : ∀ a b, herm (Hpk k r) (g⁻¹ *ᵥ fvec k r Bs.z a) (fvec k r Bs.z' b) =
      starRingEnd ℂ (Zhat k r Bs.z Bs.z' g a b) := by
    intro a b
    rw [← Formalism.FourierDecayAlt.P.Qx2.herm_uh hg, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hd, Matrix.one_mulVec,
      herm_swap_eq_zero_of_eq_zero]
    rfl
  have hM : (Matrix.of fun a b => herm (Hpk k r) (g⁻¹ *ᵥ fvec k r Bs.z a) (fvec k r Bs.z' b)) =
      (Zhat k r Bs.z Bs.z' g).map (starRingEnd ℂ) := by
    ext a b
    simp [hZ]
  unfold HermitianLatticeCounting.ExpansionTerms.formalDeterminantVectorOnGroup D.cofL
  rw [hM, show ((Zhat k r Bs.z Bs.z' g).map (starRingEnd ℂ)).adjugate =
      (Zhat k r Bs.z Bs.z' g).adjugate.map (starRingEnd ℂ) from
      (RingHom.map_adjugate (starRingEnd ℂ) _).symm, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.mulVec_smul]
  rfl

lemma om_herm_wb_zero {v w : Fin (2 * r + k + 1) → ℂ} (hw : inWb k r w)
    (hv : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → i.val ≤ r + k → v i = 0) : herm (Hpk k r) v w = 0 := by
  unfold herm
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
  · have : (Hpk k r *ᵥ v) i = 0 := by
      simp only [Matrix.mulVec, dotProduct]
      apply Finset.sum_eq_zero
      intro j _
      by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
      · simp [hv j hj.1 hj.2]
      · have : Hpk k r i j = 0 := by
          unfold Hpk
          have hij : i ≠ j := fun h => hj (h ▸ hi)
          split_ifs <;> first | rfl | omega | exact absurd ‹_› (by tauto)
        simp [this]
    simp [this]
  · have : w i = 0 := hw i (by omega)
    simp [this]

lemma om_fvec_wb_zero (z' : Fin (2 * r + k + 1) → ℂ) {w : Fin (2 * r + k + 1) → ℂ} (hw : inWb k r w)
    (hz'w : herm (Hpk k r) w z' = 0) (b : Fin (r + 1)) : herm (Hpk k r) (fvec k r z' b) w = 0 := by
  unfold fvec
  split_ifs with hb
  · apply om_herm_wb_zero hw
    intro i hi1 _
    simp only [bvec, eI, Pi.single_apply]
    rw [if_neg]
    intro h
    rw [h] at hi1
    simp at hi1
    omega
  · rw [herm_swap_eq_zero_of_eq_zero, hz'w, map_zero]

lemma om_eq {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) {B0 : Fin k → Fin (2 * r + k + 1) → ℂ}
    (hB : Q.IsFrameOf k r [Bs.z'] B0) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) (j : Fin k) :
    omC Bs B0 g j = herm (Hpk k r) (HermitianLatticeCounting.ExpansionTerms.N3om k r Bs.z Bs.z' g) (B0 j) := by
  show herm (Hpk k r) ((Hpk k r * gᴴ * Hpk k r) *ᵥ D.cofL Bs g) (B0 j) = _
  rw [om_inv_eq hg, ← om_N3xM_eq Bs hg]
  obtain ⟨-, -, co, hco⟩ := HermitianLatticeCounting.P.omega_decomposition k r Bs.z Bs.z' Bs.z_mem Bs.z'_mem
    Bs.T'_pos.ne' g hg
  have h0 : ∀ b, herm (Hpk k r) (co b • fvec k r Bs.z' b) (B0 j) = 0 := fun b => by
    rw [om_herm_smul, om_fvec_wb_zero Bs.z' (hB.1 j) (hB.2.2 j Bs.z' (by simp)) b, mul_zero]
  rw [hco, om_herm_add, om_herm_sum]
  simp [h0]

lemma om_complete {z' : Fin (2 * r + k + 1) → ℂ} (hz' : inWb k r z') (hT' : 0 < Tz k r z')
    {B0 : Fin k → Fin (2 * r + k + 1) → ℂ} (hB : Q.IsFrameOf k r [z'] B0) {v : Fin (2 * r + k + 1) → ℂ}
    (hv : inWb k r v) (hvz : herm (Hpk k r) v z' = 0) : ∑ j, herm (Hpk k r) v (B0 j) • B0 j = v := by
  classical
  let e : Fin (k + 1) → Fin (2 * r + k + 1) → ℂ := fun i => if h : i.val < k then B0 ⟨i.val, h⟩ else z'
  have he_wb : ∀ i, inWb k r (e i) := by
    intro i
    simp only [e]
    split_ifs
    exacts [hB.1 _, hz']
  have hzz : herm (Hpk k r) z' z' ≠ 0 := by
    intro h0
    simp [Tz, h0] at hT'
  have horth : ∀ i j, i ≠ j → herm (Hpk k r) (e i) (e j) = 0 := by
    intro i j hij
    simp only [e]
    split_ifs with hi hj hj
    · rw [hB.2.1, if_neg]
      intro h
      exact hij (Fin.ext (by simpa using congrArg Fin.val h))
    · exact hB.2.2 _ z' (by simp)
    · rw [herm_swap_eq_zero_of_eq_zero, hB.2.2 _ z' (by simp), map_zero]
    · have := i.isLt
      have := j.isLt
      exact absurd (Fin.ext (by omega)) hij
  have hn : ∀ i, herm (Hpk k r) (e i) (e i) ≠ 0 := by
    intro i
    simp only [e]
    split_ifs
    · rw [hB.2.1, if_pos rfl]
      exact one_ne_zero
    · exact hzz
  have key : ∀ (b : Fin (k + 1) → ℂ) (j : Fin (k + 1)),
      herm (Hpk k r) (∑ i, b i • e i) (e j) = b j * herm (Hpk k r) (e j) (e j) := by
    intro b j
    rw [om_herm_sum, Finset.sum_eq_single j]
    · rw [om_herm_smul]
    · intro i _ hij
      rw [om_herm_smul, horth i j hij, mul_zero]
    · simp
  have mid : ∀ u : Fin (2 * r + k + 1) → ℂ, inWb k r u →
      (∀ t : Fin (k + 1), u ⟨r + t.val, by omega⟩ = 0) → u = 0 := by
    intro u hu ht
    funext i
    show u i = 0
    by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
    · have h1 : u ⟨r + (i.val - r), by omega⟩ = 0 := ht ⟨i.val - r, by omega⟩
      have e1 : (⟨r + (i.val - r), by omega⟩ : Fin (2 * r + k + 1)) = i := Fin.ext (by simp; omega)
      rwa [e1] at h1
    · exact hu i (by omega)
  have sum_wb : ∀ b : Fin (k + 1) → ℂ, inWb k r (∑ i, b i • e i) := by
    intro b i hi
    simp [Finset.sum_apply, he_wb _ i hi]
  let A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ := Matrix.of fun t i => e i ⟨r + t.val, by omega⟩
  have hA : ∀ b t, (A *ᵥ b) t = (∑ i, b i • e i) ⟨r + t.val, by omega⟩ := by
    intro b t
    simp [A, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hinj : Function.Injective A.mulVec := by
    intro b1 b2 h12
    have h0 : A *ᵥ (b1 - b2) = 0 := by rw [Matrix.mulVec_sub, h12, sub_self]
    have hu : ∑ i, (b1 - b2) i • e i = 0 :=
      mid _ (sum_wb _) (fun t => by rw [← hA, h0]; rfl)
    funext j
    have h1 := key (b1 - b2) j
    have h00 : herm (Hpk k r) 0 (e j) = 0 := by simp [herm]
    rw [hu, h00] at h1
    have h2 := (mul_eq_zero.mp h1.symm).resolve_right (hn j)
    simpa [sub_eq_zero] using h2
  have hsurj : Function.Surjective A.mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr (Matrix.mulVec_injective_iff_isUnit.mp hinj)
  have hsub : ∀ x y u, herm (Hpk k r) (x - y) u = herm (Hpk k r) x u - herm (Hpk k r) y u := by
    intro x y u
    simp only [herm, Matrix.mulVec_sub, dotProduct_sub]
  set w := v - ∑ j, herm (Hpk k r) v (B0 j) • B0 j with hw
  have hwwb : inWb k r w := by
    intro i hi
    simp [hw, Finset.sum_apply, hv i hi, (hB.1 _) i hi]
  have hwe : ∀ j, herm (Hpk k r) w (e j) = 0 := by
    intro j
    rw [hw, hsub, om_herm_sum]
    simp only [om_herm_smul]
    simp only [e]
    split_ifs with hj
    · simp [hB.2.1]
    · simp [hB.2.2 _ z' (by simp), hvz]
  obtain ⟨b, hb⟩ := hsurj (fun t => w ⟨r + t.val, by omega⟩)
  have huw : ∑ i, b i • e i = w := by
    have h1 := mid (∑ i, b i • e i - w)
      (fun i hi => by rw [Pi.sub_apply, sum_wb b i hi, hwwb i hi, sub_zero])
      (fun t => by
        have h2 := hA b t
        rw [hb] at h2
        rw [Pi.sub_apply, ← h2, sub_self])
    exact sub_eq_zero.mp h1
  have hb0 : ∀ j, b j = 0 := by
    intro j
    have h1 := key b j
    rw [huw, hwe] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_right (hn j)
  have hw0 : w = 0 := by
    rw [← huw]
    simp [hb0]
  rw [hw, sub_eq_zero] at hw0
  exact hw0.symm

lemma om_N3om_mem {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) :
    inWb k r (HermitianLatticeCounting.ExpansionTerms.N3om k r Bs.z Bs.z' g) ∧ herm (Hpk k r) (HermitianLatticeCounting.ExpansionTerms.N3om k r Bs.z Bs.z' g) Bs.z' = 0 := by
  obtain ⟨h1, h2, -⟩ := HermitianLatticeCounting.P.omega_decomposition k r Bs.z Bs.z' Bs.z_mem Bs.z'_mem
    Bs.T'_pos.ne' g hg
  refine ⟨h1, ?_⟩
  simpa [fvec] using h2 (Fin.last r)

lemma om_expand {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) {B0 : Fin k → Fin (2 * r + k + 1) → ℂ}
    (hB : Q.IsFrameOf k r [Bs.z'] B0) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) : ∑ j, omC Bs B0 g j • B0 j = HermitianLatticeCounting.ExpansionTerms.N3om k r Bs.z Bs.z' g := by
  simp_rw [om_eq Bs hB hg]
  exact om_complete Bs.z'_mem Bs.T'_pos hB (om_N3om_mem Bs hg).1 (om_N3om_mem Bs hg).2

theorem om_norm {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) {B0 : Fin k → Fin (2 * r + k + 1) → ℂ}
    (hB : Q.IsFrameOf k r [Bs.z'] B0) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) : C6.sq2 (omC Bs B0 g) = Gf k r Bs.z Bs.z' g / Tz k r Bs.z' := by
  have hm := (HermitianLatticeCounting.P.dual_vector_norm_on_group k r Bs.z Bs.z' Bs.z_mem Bs.z'_mem Bs.T'_pos g hg).1
  rw [← om_expand Bs hB hg] at hm
  simp only [om_herm_sum, om_herm_smul, om_herm_sum_right, om_herm_smul_right, hB.2.1,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at hm
  simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true] at hm
  apply Complex.ofReal_injective
  rw [← hm]
  simp only [C6.sq2, Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self]

theorem om_equiv {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) {B0 : Fin k → Fin (2 * r + k + 1) → ℂ}
    (hB : Q.IsFrameOf k r [Bs.z'] B0) (p : B.SS k r) (hp : Bs.inSS p)
    {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    ∑ j, omC Bs B0 (B.sgs p g) j • B0 j = (Matrix.of p.2.1)⁻¹ *ᵥ ∑ j, omC Bs B0 g j • B0 j := by
  obtain ⟨hA, hN1, hD, hN2⟩ := hp
  have hA' := Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hA
  have hN1' := Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv hN1
  have hsg : B.sgs p g = (Matrix.of p.1.1)⁻¹ * ((Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2) *
      Matrix.of p.2.1 := by
    simp only [B.sgs, Matrix.mul_assoc]
  have hm : (Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2 ∈ UH (Hpk k r) :=
    Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hN1'.1 hg) hN2.1
  have hsU : B.sgs p g ∈ UH (Hpk k r) := by
    rw [hsg]
    exact Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hA'.1 hm) hD.1
  rw [om_expand Bs hB hsU, om_expand Bs hB hg, hsg,
    HermitianLatticeCounting.P.dual_vector_equivariant k r Bs.z Bs.z' Bs.z_mem Bs.z'_mem _ hm _ hA' _ hD,
    HermitianLatticeCounting.P.dual_vector_unipotent_invariant k r Bs.z Bs.z' Bs.z_mem Bs.z'_mem g hg _ hN1' _ hN2]

def OmPolyP : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (B0 : Fin k → Fin (2 * r + k + 1) → ℂ),
    Q.IsFrameOf k r [Bs.z'] B0 → ∀ j, U.IsPolyDeg (r + 1) fun g => omC Bs B0 g j

def OmCellP : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (B0 : Fin k → Fin (2 * r + k + 1) → ℂ),
    Q.IsFrameOf k r [Bs.z'] B0 → ∀ x ∈ Q.DomR k r Bs.z Bs.z', ∀ j, omC Bs B0 (Q.wCell k r (Fin.last r) x.1 * x.2) j =
      conj (∏ a, x.1 a) * herm (Hpk k r) (x.2⁻¹ *ᵥ Bs.z) (B0 j)

theorem om_facts_of (h1 : OmPolyP) (h4 : OmCellP) : OmFacts := by
  intro k r Wp Wq _ _ _ _ _ Bs B0 hB
  exact ⟨h1 k r Wp Wq Bs B0 hB, fun g hg => om_norm Bs hB hg,
    fun p hp g hg => om_equiv Bs hB p hp hg.1, h4 k r Wp Wq Bs B0 hB⟩

lemma om_prod_erase (r : ℕ) (c : Fin r → ℂ) (ζ : ℂ) :
    ∏ j ∈ Finset.univ.erase (Fin.last r), (if h : j.val < r then c ⟨j.val, h⟩ else ζ) = ∏ a, c a := by
  rw [← Finset.compl_singleton, ← Fin.image_castSucc, Finset.prod_image (fun a _ b _ h => Fin.castSucc_injective _ h)]
  simp

lemma inv_mulVec_of_fixed_vector {n : ℕ} (W M : Matrix (Fin n) (Fin n) ℂ) (z : Fin n → ℂ) (hM : IsUnit M.det)
    (hG : IsUnit (W * M).det) (hW : W *ᵥ z = z) : (W * M)⁻¹ *ᵥ z = M⁻¹ *ᵥ z := by
  have hWd : IsUnit W.det := by
    rw [Matrix.det_mul] at hG
    exact isUnit_of_mul_isUnit_left hG
  rw [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec]
  congr 1
  conv_lhs => rw [← hW]
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hWd, Matrix.one_mulVec]

theorem om_cell {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) {B0 : Fin k → Fin (2 * r + k + 1) → ℂ}
    (x : (Fin r → ℂ) × Q.Mx k r) (hx : x ∈ Q.DomR k r Bs.z Bs.z') (j : Fin k) :
    omC Bs B0 (Q.wCell k r (Fin.last r) x.1 * x.2) j = conj (∏ a, x.1 a) * herm (Hpk k r) (x.2⁻¹ *ᵥ Bs.z) (B0 j) := by
  obtain ⟨hc, hM, -⟩ := hx
  have hWU : bigCell k r x.1 1 ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.big_cell_mem_holds k r x.1 1 hc (by simp)
  have hgU : bigCell k r x.1 1 * x.2 ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hWU hM.1
  have hfix : ∀ b, (bigCell k r x.1 1 * x.2) *ᵥ fvec k r Bs.z' b =
      bigCell k r x.1 1 *ᵥ fvec k r (x.2 *ᵥ Bs.z') b := by
    intro b
    rw [← Matrix.mulVec_mulVec]
    congr 1
    unfold fvec
    split_ifs with hb
    · exact (hM.2 ⟨b.val, hb⟩ (by simp only [Fin.val_last]; exact hb)).1
    · rfl
  have hZ : Zhat k r Bs.z Bs.z' (bigCell k r x.1 1 * x.2) = Zhat k r Bs.z (x.2 *ᵥ Bs.z') (bigCell k r x.1 1) := by
    ext a b
    simp only [Zhat, hfix]
  have hMz' := (Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.glev_inWb hM Bs.z'_mem).1
  rw [Formalism.QuantumDeterminants.big_cell_coordinate_holds k r _ _ x.1 1 Bs.z_mem hMz'] at hZ
  have hcof : D.cofL Bs (bigCell k r x.1 1 * x.2) = conj (∏ a, x.1 a) • Bs.z := by
    unfold D.cofL
    rw [hZ, Matrix.adjugate_diagonal, Finset.sum_eq_single (Fin.last r)]
    · rw [Matrix.diagonal_apply_eq, om_prod_erase]
      congr 1
      simp [fvec]
    · intro b _ hb
      rw [Matrix.diagonal_apply_ne _ (Ne.symm hb), map_zero, zero_smul]
    · simp
  have hWz : bigCell k r x.1 1 *ᵥ Bs.z = Bs.z := by
    rw [← Formalism.FourierDecayAlt.P.TwoByOneBlock.jV_wbPart Bs.z_mem, Formalism.FourierDecayAlt.P.BigCellHermitian.bigCell_mulVec_jV, Matrix.one_mulVec]
  rw [Formalism.FourierDecayAlt.P5.Rad.wCell_last_eq]
  show herm (Hpk k r) ((Hpk k r * (bigCell k r x.1 1 * x.2)ᴴ * Hpk k r) *ᵥ
    D.cofL Bs (bigCell k r x.1 1 * x.2)) (B0 j) = _
  rw [om_inv_eq hgU, hcof, Matrix.mulVec_smul, om_herm_smul,
    inv_mulVec_of_fixed_vector _ _ _ (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hM.1) (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hgU) hWz]

end

end Formalism.FourierDecayAlt.P.TLC

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.P.TLC

theorem omega_polynomial_facts : TL.OmFacts := by
  exact om_facts_of (fun k r Wp Wq _ _ _ _ _ Bs B0 _ j => omp_poly Bs B0 j)
    (fun k r Wp Wq _ _ _ _ _ Bs B0 _ x hx j => om_cell Bs x hx j)

end Formalism.FourierDecayAlt.P
