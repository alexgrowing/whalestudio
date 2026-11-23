import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGeneratorCmDifferentIdealScaled
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeImageRationalHomLattice

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.TriangleColumns

def IL (D : D7) (cc : Ideal (𝓞 D.host.K)) {n : ℕ} (L : Lat D n) : Lat D n :=
  Submodule.span (𝓞 D.host.E) {v | ∃ t ∈ Iid D cc, ∃ y ∈ L, v = t • y}

theorem smul_mem_IL {D : D7} {cc : Ideal (𝓞 D.host.K)} {n : ℕ} {L : Lat D n} {t : D.host.E}
    (ht : t ∈ Iid D cc) {y : Fin n → D.host.E} (hy : y ∈ L) : t • y ∈ IL D cc L :=
  Submodule.subset_span ⟨t, ht, y, hy, rfl⟩

theorem IL_mono {D : D7} {cc : Ideal (𝓞 D.host.K)} {n : ℕ} {L L' : Lat D n} (h : L ≤ L') :
    IL D cc L ≤ IL D cc L' :=
  Submodule.span_mono fun _ ⟨t, ht, y, hy, e⟩ => ⟨t, ht, y, h hy, e⟩

theorem hE_osmul_left (D : D7) {n : ℕ} (a : 𝓞 D.host.E) (x y : Fin n → D.host.E) :
    hE D (a • x) y = a • hE D x y := by
  rw [← algebraMap_smul D.host.E a x, hE_smul_left, Algebra.smul_def]

theorem pair_mem {D : D7} {cc : Ideal (𝓞 D.host.K)} {n : ℕ} {L : Lat D n} {v w : Fin n → D.host.E}
    (hw : ∀ y ∈ L, IntE D (hE D y w)) (hv : v ∈ IL D cc L) : hE D v w ∈ Iid D cc := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨t, ht, y, hy, rfl⟩ := hv
    obtain ⟨o, ho⟩ := hw y hy
    rw [hE_smul_left, ← ho, mul_comm, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ ht
  | zero => simp [hE]
  | add u v _ _ hu hv => rw [hE_add_left]; exact add_mem hu hv
  | smul a v _ hv => rw [hE_osmul_left]; exact Submodule.smul_mem _ _ hv

theorem sd_int {D : D7} {n : ℕ} {L : Lat D n} (h : SD D L) {y w : Fin n → D.host.E} (hy : y ∈ L) (hw : w ∈ L) :
    IntE D (hE D y w) := (((sd_iff D L).1 h).2.2 y).1 hy w hw

theorem smul_mem_IL_of_P {D : D7} {cc : Ideal (𝓞 D.host.K)} {n : ℕ} {M : Lat D n} {P : Ideal (𝓞 D.host.E)}
    {b : Fin n → D.host.E} (hb : ∀ p ∈ P, p • b ∈ M) {t : D.host.E} (ht : t ∈ P • Iid D cc) :
    t • b ∈ IL D cc M := by
  refine Submodule.smul_induction_on ht (fun p hp s hs => ?_) (fun u v hu hv => ?_)
  · have : (p • s) • b = s • (p • b) := by rw [smul_assoc, smul_comm]
    rw [this]; exact smul_mem_IL hs (hb p hp)
  · rw [add_smul]; exact add_mem hu hv

theorem decomp {D : D7} {cc : Ideal (𝓞 D.host.K)} {n : ℕ} {M : Lat D n} {P : Ideal (𝓞 D.host.E)}
    {b : Fin n → D.host.E} (hb : ∀ p ∈ P, p • b ∈ M) {t₀ : D.host.E}
    (hg : ∀ t ∈ Iid D cc, ∃ a : 𝓞 D.host.E, t - a • t₀ ∈ P • Iid D cc) {v : Fin n → D.host.E}
    (hv : v ∈ IL D cc (M ⊔ Submodule.span (𝓞 D.host.E) {b})) :
    ∃ a : 𝓞 D.host.E, v - (a • t₀) • b ∈ IL D cc M := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨t, ht, y, hy, rfl⟩ := hv
    obtain ⟨m, hm, z, hz, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 hz
    obtain ⟨a, ha⟩ := hg (o • t) (Submodule.smul_mem _ _ ht)
    refine ⟨a, ?_⟩
    have : t • (m + o • b) - (a • t₀) • b = t • m + (o • t - a • t₀) • b := by
      rw [smul_add, sub_smul, smul_assoc o t b, smul_comm o t b]; abel
    rw [this]
    exact add_mem (smul_mem_IL ht hm) (smul_mem_IL_of_P hb ha)
  | zero => exact ⟨0, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨a, ha⟩ := hu
    obtain ⟨a', ha'⟩ := hv
    refine ⟨a + a', ?_⟩
    have : u + v - ((a + a') • t₀) • b = (u - (a • t₀) • b) + (v - (a' • t₀) • b) := by
      rw [add_smul, add_smul]; abel
    rw [this]; exact add_mem ha ha'
  | smul c v _ hv =>
    obtain ⟨a, ha⟩ := hv
    refine ⟨c * a, ?_⟩
    have : c • v - ((c * a) • t₀) • b = c • (v - (a • t₀) • b) := by
      rw [smul_sub, mul_smul, smul_assoc c]
    rw [this]; exact Submodule.smul_mem _ _ ha

def mat (D : D7) {N N' : ℕ} (t₀ : D.host.E) (b : Fin N' → D.host.E) (a : Fin N → 𝓞 D.host.E) :
    Matrix (Fin N') (Fin N) D.host.E := fun i j => (a j • t₀) * b i

theorem pt_apply (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (z : Matrix (Fin N') (Fin N) D.host.E)
    (τ : D.what₂.Tau) (i : Fin N') (j : Fin N) : pt D (tor0 D cc δ) δ z τ i j = δ * embT D τ (z i j) := rfl

theorem pt_sub (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (z w : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ z - pt D (tor0 D cc δ) δ w = pt D (tor0 D cc δ) δ (z - w) := by
  funext τ i j
  simp only [Pi.sub_apply, pt_apply, Matrix.sub_apply, map_sub, mul_sub]

theorem pt_add (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (z w : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ z + pt D (tor0 D cc δ) δ w = pt D (tor0 D cc δ) δ (z + w) := by
  funext τ i j
  simp only [Pi.add_apply, pt_apply, Matrix.add_apply, map_add, mul_add]

def ptH (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N : ℕ) {N' : ℕ} (t₀ : D.host.E) (b : Fin N' → D.host.E) :
    (Fin N → 𝓞 D.host.E) →+ VC D N N' :=
  AddMonoidHom.mk' (fun a => pt D (tor0 D cc δ) δ (mat D t₀ b a)) fun a a' => by
    rw [pt_add]; congr 1; funext i j
    simp only [mat, Pi.add_apply, Matrix.add_apply, add_smul, add_mul]

theorem ptH_apply (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N : ℕ) {N' : ℕ} (t₀ : D.host.E)
    (b : Fin N' → D.host.E) (a : Fin N → 𝓞 D.host.E) :
    ptH D cc δ N t₀ b a = pt D (tor0 D cc δ) δ (mat D t₀ b a) := rfl

def phiH (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N' : ℕ} (t₀ : D.host.E) (b x : Fin N' → D.host.E) :
    𝓞 D.host.E →+ ℂ :=
  AddMonoidHom.mk' (fun s => (∑ τ, ∑ i, embT D τ (s : D.host.E) *
      (δ * embT D τ (t₀ * x i) * (starRingEnd ℂ) (δ * embT D τ (t₀ * b i)))) / (area (tor0 D cc δ).abelian₂ : ℂ))
    fun s s' => by
      simp only [RingOfIntegers.coe_eq_algebraMap, map_add, add_mul, Finset.sum_add_distrib, add_div]

theorem Hf_ptH (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N : ℕ) {N' : ℕ} (t₀ : D.host.E)
    (b x : Fin N' → D.host.E) (c c' : Fin N → 𝓞 D.host.E) :
    Hf D (tor0 D cc δ) (ptH D cc δ N t₀ x c') (ptH D cc δ N t₀ b c) =
      phiH D cc δ t₀ b x (∑ k, c' k * sgO D (c k)) := by
  have h1 : ∀ s : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E (sgO D s) =
      D.host.conj (algebraMap (𝓞 D.host.E) D.host.E s) := fun s => rfl
  rw [phiH, AddMonoidHom.mk'_apply]
  simp only [Hf, ptH_apply, pt_apply, mat, Algebra.smul_def,
    RingOfIntegers.coe_eq_algebraMap, map_sum, map_mul, h1, embT_conj, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem pt_mem {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hδ : δ ≠ 0) {N N' : ℕ} (L : Lat D N')
    (z : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ z ∈ La D (tor0 D cc δ) (stdL D N) L ↔ ∀ j, (fun i => z i j) ∈ IL D cc L := by
  obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.ThetaLatImage.theta_lattice_image D cc δ hδ N N'
  rw [h2]
  constructor
  · rintro ⟨w, hw, e⟩
    rw [h1 e]; exact (h3 L w).1 hw
  · intro h
    exact ⟨z, (h3 L z).2 h, rfl⟩

theorem ptH_mem {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hδ : δ ≠ 0) {N N' : ℕ} (L : Lat D N')
    (t₀ : D.host.E) (b : Fin N' → D.host.E) (a : Fin N → 𝓞 D.host.E) :
    ptH D cc δ N t₀ b a ∈ La D (tor0 D cc δ) (stdL D N) L ↔ ∀ j, (a j • t₀) • b ∈ IL D cc L :=
  pt_mem hδ L _

theorem ptH_add (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N : ℕ) {N' : ℕ} (t₀ : D.host.E)
    (b x : Fin N' → D.host.E) (a : Fin N → 𝓞 D.host.E) :
    ptH D cc δ N t₀ b a + ptH D cc δ N t₀ x a = ptH D cc δ N t₀ (b + x) a := by
  rw [ptH_apply, ptH_apply, ptH_apply, pt_add]; congr 1; funext i j
  simp only [mat, Pi.add_apply, Matrix.add_apply, mul_add]

theorem exists_sub_ptH {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hδ : δ ≠ 0) {N N' : ℕ} {M : Lat D N'}
    {P : Ideal (𝓞 D.host.E)} {b : Fin N' → D.host.E} (hb : ∀ p ∈ P, p • b ∈ M) {t₀ : D.host.E}
    (hg : ∀ t ∈ Iid D cc, ∃ a : 𝓞 D.host.E, t - a • t₀ ∈ P • Iid D cc) {z : VC D N N'}
    (hz : z ∈ La D (tor0 D cc δ) (stdL D N) (M ⊔ Submodule.span (𝓞 D.host.E) {b})) :
    ∃ a : Fin N → 𝓞 D.host.E, ∀ L : Lat D N', M ≤ L →
      z - ptH D cc δ N t₀ b a ∈ La D (tor0 D cc δ) (stdL D N) L := by
  obtain ⟨w, -, rfl⟩ := ((GlobalTheory.ThetaLatImage.theta_lattice_image D cc δ hδ N N').2.1 _ _ z).1 hz
  choose a ha using fun j => decomp hb hg ((pt_mem hδ _ w).1 hz j)
  refine ⟨a, fun L hL => ?_⟩
  rw [ptH_apply, pt_sub, pt_mem hδ]
  exact fun j => IL_mono hL (ha j)

theorem triDat_of_tri : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → δ ≠ 0 → ∀ (N N' : ℕ) (P : Ideal (𝓞 D.host.E)), P.IsMaximal → ∀ A B C : Lat D N', Tri D P A B C → TriDat D (tor0 D cc δ) (La D (tor0 D cc δ) (stdL D N) A) (La D (tor0 D cc δ) (stdL D N) B) (La D (tor0 D cc δ) (stdL D N) C) P N := by
  intro D cc δ hcc hδ N N' P hP A B C ⟨hA, hB, hC, M, b, x, eA, eB, eC, hp, hbx⟩
  obtain ⟨t₀, ht₀, hg, hθ⟩ := GlobalTheory.IdealGenerator.exists_generator_Iid D cc hcc P hP
  have MA : M ≤ A := eA ▸ le_sup_left
  have MB : M ≤ B := eB ▸ le_sup_left
  have MC : M ≤ C := eC ▸ le_sup_left
  have bxA : b + x ∈ A := eA ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have bB : b ∈ B := eB ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have xC : x ∈ C := eC ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hsum : ∀ (y : Fin N' → D.host.E) (a : Fin N → 𝓞 D.host.E),
      ∑ i, ((ptH D cc δ N t₀ y).comp (AddMonoidHom.single (fun _ : Fin N => 𝓞 D.host.E) i)) (a i) =
        ptH D cc δ N t₀ y a := by
    intro y a
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.single_apply]
    rw [← map_sum, Finset.univ_sum_single]
  have hin : ∀ (L : Lat D N') (y : Fin N' → D.host.E), y ∈ L → ∀ a : Fin N → 𝓞 D.host.E,
      ptH D cc δ N t₀ y a ∈ La D (tor0 D cc δ) (stdL D N) L := fun L y hy a =>
    (ptH_mem hδ L t₀ y a).2 fun j => smul_mem_IL (Submodule.smul_mem _ _ ht₀) hy
  have hinP : ∀ (L : Lat D N') (y : Fin N' → D.host.E), M ≤ L → (∀ p ∈ P, p • y ∈ M) → ∀ i, ∀ p ∈ P,
      ptH D cc δ N t₀ y (Pi.single i p) ∈ La D (tor0 D cc δ) (stdL D N) L := fun L y hL hy i p hp =>
    (ptH_mem hδ L t₀ y _).2 fun j => IL_mono hL <| smul_mem_IL_of_P hy <| Submodule.smul_mem_smul (by
      by_cases h : j = i
      · subst h; simpa using hp
      · simp [Pi.single_eq_of_ne h]) ht₀
  refine ⟨fun i => (ptH D cc δ N t₀ b).comp (AddMonoidHom.single (fun _ : Fin N => 𝓞 D.host.E) i),
    fun i => (ptH D cc δ N t₀ x).comp (AddMonoidHom.single (fun _ : Fin N => 𝓞 D.host.E) i),
    fun _ => phiH D cc δ t₀ b x, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j a a'
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.single_apply]
    rw [Hf_ptH, Finset.sum_eq_single i (fun k _ hk => by rw [Pi.single_eq_of_ne hk, zero_mul]) (by simp)]
    split_ifs with h
    · subst h; simp only [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne h, map_zero, mul_zero, map_zero]
  · intro i a
    refine ⟨hin B b bB _, hin C x xC _, ?_⟩
    simp only [AddMonoidHom.comp_apply]
    rw [ptH_add]; exact hin A _ bxA _
  · intro i p hpP
    exact ⟨⟨hinP A b MA (fun p h => (hp p h).1) i p hpP, hinP C b MC (fun p h => (hp p h).1) i p hpP⟩,
      ⟨hinP A x MA (fun p h => (hp p h).2) i p hpP, hinP B x MB (fun p h => (hp p h).2) i p hpP⟩⟩
  · intro z hz
    rw [eB] at hz
    obtain ⟨a, ha⟩ := exists_sub_ptH hδ (fun p h => (hp p h).1) hg hz
    exact ⟨a, by rw [hsum]; exact ⟨ha A MA, ha C MC⟩⟩
  · intro z hz
    rw [eC] at hz
    obtain ⟨a, ha⟩ := exists_sub_ptH hδ (fun p h => (hp p h).2) hg hz
    exact ⟨a, by rw [hsum]; exact ⟨ha A MA, ha B MB⟩⟩
  · intro a ha i
    rw [hsum, ptH_mem hδ] at ha
    have h1 := pair_mem (fun y hy => sd_int hA hy bxA) (ha i)
    obtain ⟨o, ho⟩ := sd_int hB bB bB
    refine hθ (hE D b x) hbx (fun p h => ?_) (a i) ?_
    · rw [← hE_osmul_left]; exact sd_int hC (MC (hp p h).1) xC
    · have : a i • (t₀ * hE D b x) = hE D ((a i • t₀) • b) (b + x) - (a i * o) • t₀ := by
        rw [hE_smul_left, hE_add_right, ← ho]
        simp only [Algebra.smul_def, map_mul]; ring
      rw [this]; exact sub_mem h1 (Submodule.smul_mem _ _ ht₀)
  · intro a ha i
    rw [hsum, ptH_mem hδ] at ha
    have h1 := pair_mem (fun y hy => sd_int hB hy bB) (ha i)
    refine hθ (hE D x b) (fun h => hbx (conj_hE D x b ▸ h.conj)) (fun p h => ?_) (a i) ?_
    · rw [← hE_osmul_left]; exact sd_int hB (MB (hp p h).2) bB
    · rwa [hE_smul_left, smul_mul_assoc] at h1

end GlobalTheory.TriangleColumns
