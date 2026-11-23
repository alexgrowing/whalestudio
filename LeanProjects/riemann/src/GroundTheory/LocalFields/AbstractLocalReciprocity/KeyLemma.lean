import Mathlib
import GroundTheory.LocalFields.AbstractLocalReciprocity.CoeNormEqProdSmulNorm

namespace GroundTheory.LocalField.Abstract

open ProfiniteInteger

namespace ClassFieldData

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  {D : ClassFieldData G A} {K L : OpenSubgroup G}

section SlopeTestRemainingChoices

omit [TotallyDisconnectedSpace G] in

def powLift {φ : G} (hφK : φ ∈ (K : Subgroup G))
    (hdφ : D.deg φ = Multiplicative.ofAdd (inertiaDegree D.deg K : ℤ̂)) (m : ℕ) (hm : 0 < m) :
    D.FrobeniusLift K where
  elt := φ ^ m
  mem := K.pow_mem hφK m
  deg := m
  deg_pos := hm
  deg_eq := by
    rw [map_pow, hdφ, ← ofAdd_nsmul]
    congr 1
    push_cast
    rw [nsmul_eq_mul]

omit [TotallyDisconnectedSpace G] in

theorem mem_fixedModule_of_smul_eq [IsDiscreteModule G A] (K : OpenSubgroup G) {φ : G}
    (hφK : φ ∈ (K : Subgroup G)) (hdφ : D.deg φ = Multiplicative.ofAdd (inertiaDegree D.deg K : ℤ̂))
    {w : A} (hw : w ∈ fixedModule A ((K : Subgroup G) ⊓ D.deg.ker)) (hφw : φ • w = w) :
    w ∈ fixedModule A (K : Subgroup G) := by
  let S : OpenSubgroup G := ⟨MulAction.stabilizer G w, IsDiscreteModule.isOpen_stabilizer w⟩
  let M : OpenSubgroup G := S ⊓ K
  have hMK : M ≤ K := inf_le_right
  have hu : (K : Subgroup G) ⊓ D.deg.ker ≤ M := fun g hg => ⟨hw g hg, hg.1⟩
  have hrel : D.relDeg K ⟨φ, hφK⟩ = Multiplicative.ofAdd 1 := by
    refine (ProfiniteInteger.pow_left_inj (D.inertiaDegree_ne_zero K)).1 ?_
    rw [D.relDeg_pow, ← ofAdd_nsmul, nsmul_one]
    exact hdφ
  intro τ hτ
  obtain ⟨m, hm⟩ := D.exists_pow_mul_mem_of_unramified hMK hu hrel ⟨τ, hτ⟩
  have h1 : ∀ j : ℕ, (φ ^ j) • w = w := by
    intro j
    induction j with
    | zero => simp
    | succ k ih => rw [pow_succ, mul_smul, hφw, ih]
  have h2 : ((φ ^ m)⁻¹ * τ) • w = w := by
    have h3 : (φ ^ m)⁻¹ * τ ∈ S := by simpa using hm.1
    exact MulAction.mem_stabilizer_iff.1 h3
  calc τ • w = (φ ^ m * ((φ ^ m)⁻¹ * τ)) • w := by group
    _ = w := by rw [mul_smul, h2, h1]

omit [TotallyDisconnectedSpace G] in

theorem map_conj_inf_ker (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal] {g : G}
    (hg : g ∈ (K : Subgroup G)) :
    ((L : Subgroup G) ⊓ D.deg.ker).map (MulAut.conj g).toMonoidHom = (L : Subgroup G) ⊓ D.deg.ker :=
  Subgroup.mem_normalizer_iff_map_conj_eq.1 (FrobeniusLift.mem_normalizer hLK hg)

omit [TotallyDisconnectedSpace G] in

theorem map_conj_inf_ker_self {g : G} (hg : g ∈ (K : Subgroup G)) :
    ((K : Subgroup G) ⊓ D.deg.ker).map (MulAut.conj g).toMonoidHom =
      (K : Subgroup G) ⊓ D.deg.ker := by
  have : ((K : Subgroup G).subgroupOf K).Normal := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  exact map_conj_inf_ker le_rfl hg

omit [TotallyDisconnectedSpace G] in

theorem smul_mem_fixedModule_inf_ker (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal] {g : G}
    (hg : g ∈ (K : Subgroup G)) {y : A} (hy : y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) :
    g • y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) := by
  have := smul_mem_fixedModule hy g
  rwa [map_conj_inf_ker hLK hg] at this

omit [TotallyDisconnectedSpace G] in

theorem smul_norm_inf_ker (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal] {g : G}
    (hg : g ∈ (K : Subgroup G)) (y : fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) :
    g • (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) y : A) =
      norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
        ⟨g • (y : A), smul_mem_fixedModule_inf_ker hLK hg y.2⟩ :=
  smul_norm_of_map_eq g (map_conj_inf_ker_self hg) (map_conj_inf_ker hLK hg) y

omit [TotallyDisconnectedSpace G] in

theorem smul_smul_comm (hLK : L ≤ K) [hN : ((L : Subgroup G).subgroupOf K).Normal] {δ ψ : G}
    (hδ : δ ∈ (K : Subgroup G) ⊓ D.deg.ker) (hψ : ψ ∈ (L : Subgroup G)) {y : A}
    (hy : y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) : δ • ψ • y = ψ • δ • y := by
  have hconj : ∀ g ∈ (K : Subgroup G), ∀ x ∈ (L : Subgroup G), g * x * g⁻¹ ∈ (L : Subgroup G) := by
    intro g hg x hx
    have := hN.conj_mem ⟨x, hLK hx⟩ (by simpa [Subgroup.mem_subgroupOf] using hx) ⟨g, hg⟩
    simpa [Subgroup.mem_subgroupOf] using this
  have hc : δ⁻¹ * ψ⁻¹ * δ * ψ ∈ (L : Subgroup G) ⊓ D.deg.ker := by
    refine ⟨?_, ?_⟩
    · have h1 : δ⁻¹ * ψ⁻¹ * δ⁻¹⁻¹ ∈ (L : Subgroup G) :=
        hconj δ⁻¹ (K.inv_mem hδ.1) _ (L.inv_mem hψ)
      rw [inv_inv] at h1
      exact L.mul_mem h1 hψ
    · have hdδ : D.deg δ = 1 := hδ.2
      show D.deg (δ⁻¹ * ψ⁻¹ * δ * ψ) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hdδ]
      simp
  calc δ • ψ • y = (ψ * δ * (δ⁻¹ * ψ⁻¹ * δ * ψ)) • y := by rw [← mul_smul]; group
    _ = ψ • δ • y := by rw [mul_smul, hy _ hc, mul_smul]

theorem smul_mem_field [IsDiscreteModule G A] (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
    (s : D.FrobeniusLift K) {g : G}
    (hgJ : ∀ y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker),
      g • y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker))
    (hcomm : ∀ y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker), s.elt • g • y = g • s.elt • y)
    {y : A} (hy : y ∈ fixedModule A ((s.field L hLK : OpenSubgroup G) : Subgroup G)) :
    g • y ∈ fixedModule A ((s.field L hLK : OpenSubgroup G) : Subgroup G) := by
  rw [FrobeniusLift.coe_field, mem_fixedModule_frobeniusClosure] at hy ⊢
  exact ⟨hgJ y hy.1, by rw [hcomm y hy.1, hy.2]⟩

end SlopeTestRemainingChoices

section Helpers

omit [TotallyDisconnectedSpace G] in

theorem normal_inf_ker (hLK : L ≤ K) [hN : ((L : Subgroup G).subgroupOf K).Normal] :
    (((L : Subgroup G) ⊓ D.deg.ker).subgroupOf ((K : Subgroup G) ⊓ D.deg.ker)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have h := (Subgroup.mem_normalizer_iff.1 (FrobeniusLift.mem_normalizer (D := D) hLK g.2.1) n).1 hn
  simpa using h

omit [TotallyDisconnectedSpace G] in

theorem prod_range_prod_range_eq {M : Type*} [CommMonoid M] (f : ℕ → M) (g D0 : ℕ) :
    ∏ i ∈ Finset.range g, ∏ j ∈ Finset.range D0, f (D0 * i + j) =
      ∏ m ∈ Finset.range (g * D0), f m := by
  induction g with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, ih, Nat.succ_mul, Finset.prod_range_add, mul_comm D0 k]

variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]

theorem field_le_field_of_pow (s1 s2 : D.FrobeniusLift K) (k : ℕ) (h2 : s2.elt = s1.elt ^ k) :
    s2.field L hLK ≤ s1.field L hLK := by
  intro x hx
  refine frobeniusClosure_le (s1.field L hLK).isClosed ?_ le_frobeniusClosure hx
  rw [h2]
  exact Subgroup.pow_mem _ (s1.elt_mem_field hLK) k

theorem coe_norm_field_field (s1 s2 : D.FrobeniusLift K) (k : ℕ) (hk : 0 < k)
    (h2 : s2.elt = s1.elt ^ k) (hdeg : s2.deg = k * s1.deg)
    (z : fixedModule A ((s2.field L hLK : OpenSubgroup G) : Subgroup G)) :
    (norm A ((s1.field L hLK : OpenSubgroup G) : Subgroup G)
      ((s2.field L hLK : OpenSubgroup G) : Subgroup G) z : A) =
      ∏ i : Fin k, s1.elt ^ (i : ℕ) • (z : A) := by
  have hmap1 := map_frobeniusClosure D.continuous_deg (FrobeniusLift.mem_normalizer hLK s1.mem)
    s1.deg_eq (L := (L : Subgroup G))
  have hmap2 := map_frobeniusClosure D.continuous_deg (FrobeniusLift.mem_normalizer hLK s2.mem)
    s2.deg_eq (L := (L : Subgroup G))
  rw [hdeg, mul_assoc] at hmap2
  have hf : 0 < s1.deg * inertiaDegree D.deg K :=
    Nat.mul_pos s1.deg_pos (Nat.pos_of_ne_zero (D.inertiaDegree_ne_zero K))
  have key := coe_norm_eq_prod_smul_norm D.deg (K := ((s1.field L hLK : OpenSubgroup G) : Subgroup G))
    (S := ((s2.field L hLK : OpenSubgroup G) : Subgroup G)) (J := (L : Subgroup G) ⊓ D.deg.ker)
    (f := s1.deg * inertiaDegree D.deg K) (n := k) hk hf
    (fun x hx => field_le_field_of_pow hLK s1 s2 k h2 hx) ?_ ?_ ?_ ?_
    (s1.elt_mem_field hLK) s1.deg_eq z (fixedModule_anti le_frobeniusClosure z.2)
  · rw [key]
    refine Finset.prod_congr rfl fun i _ => ?_
    congr 1
    exact coe_norm_of_le (fun x hx => (s1.field_inf_ker hLK).le hx) _
  · intro x hx
    have : D.deg x ∈ (frobeniusClosure D.deg L s2.elt).map D.deg := ⟨x, hx, rfl⟩
    rw [hmap2] at this
    exact this
  · intro x _ hx
    have : D.deg x ∈ AddSubgroup.toSubgroup (multiples (k * (s1.deg * inertiaDegree D.deg K))) := hx
    rw [← hmap2] at this
    obtain ⟨y, hy, hyx⟩ := this
    exact ⟨y, hy, hyx⟩
  · intro x hx
    have : D.deg x ∈ (frobeniusClosure D.deg L s1.elt).map D.deg := ⟨x, hx, rfl⟩
    rw [hmap1] at this
    exact this
  · intro q hq
    have hqJ : q ∈ (L : Subgroup G) ⊓ D.deg.ker := (s1.field_inf_ker hLK).le hq
    exact ⟨fun _ => hqJ, fun h => le_frobeniusClosure h⟩

omit [TotallyDisconnectedSpace G] [((L : Subgroup G).subgroupOf K).Normal] in

theorem coe_norm_inf_ker_prod {ι : Type*} (s : Finset ι) (f : ι → A)
    (hf : ∀ i, f i ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) :
    (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
      ⟨∏ i ∈ s, f i, Subgroup.prod_mem _ fun i _ => hf i⟩ : A) =
      ∏ i ∈ s, (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
        ⟨f i, hf i⟩ : A) := by
  have h : (⟨∏ i ∈ s, f i, Subgroup.prod_mem _ fun i _ => hf i⟩ :
      fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) = ∏ i ∈ s, ⟨f i, hf i⟩ := by
    ext
    simp
  rw [h, map_prod]
  simp

omit [TotallyDisconnectedSpace G] [((L : Subgroup G).subgroupOf K).Normal] in

theorem coe_norm_inf_ker_mul {y z : A} (hy : y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker))
    (hz : z ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) :
    (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
      ⟨y * z, Subgroup.mul_mem _ hy hz⟩ : A) =
      (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) ⟨y, hy⟩ : A) *
        norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) ⟨z, hz⟩ := by
  have h : (⟨y * z, Subgroup.mul_mem _ hy hz⟩ : fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) =
      ⟨y, hy⟩ * ⟨z, hz⟩ := rfl
  rw [h, map_mul]
  rfl

end Helpers

section Key

variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]

theorem exists_norm_eq_norm_inf_ker (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]
    {φ : G} (hφK : φ ∈ (K : Subgroup G))
    (hdφ : D.deg φ = Multiplicative.ofAdd (inertiaDegree D.deg K : ℤ̂))
    (s1 s2 : D.FrobeniusLift K) (h1 : s1.elt = φ ^ s1.deg) (hψL : s1.elt ∈ (L : Subgroup G))
    (h2 : s2.elt = s1.elt ^ ((L : Subgroup G).relIndex K))
    (hdeg : s2.deg = (L : Subgroup G).relIndex K * s1.deg)
    {x a : A} (hx : x ∈ fixedModule A ((s1.field L hLK : OpenSubgroup G) : Subgroup G))
    (ha : a ∈ fixedModule A ((s1.field L hLK : OpenSubgroup G) : Subgroup G))
    (hxu : D.valuation (s1.field L hLK) ⟨x, hx⟩ = 1)
    (hau : D.valuation (s1.field L hLK) ⟨a, ha⟩ = 1)
    {δ : G} (hδ : δ ∈ (K : Subgroup G) ⊓ D.deg.ker) (hrel : φ • x / x = δ • a / a) :
    ∃ b : fixedModule A (L : Subgroup G),
      (norm A (K : Subgroup G) (L : Subgroup G) b : A) =
        norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
          ⟨x, fixedModule_anti le_frobeniusClosure hx⟩ := by
  classical
  set g := (L : Subgroup G).relIndex K with hgdef
  have hg : 0 < g := Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero
    (H := (L : Subgroup G).subgroupOf K))
  have hP'P : s2.field L hLK ≤ s1.field L hLK := field_le_field_of_pow hLK s1 s2 g h2
  have hP'L : s2.field L hLK ≤ L := fun y hy =>
    frobeniusClosure_le L.isClosed (by rw [h2]; exact L.pow_mem hψL g) inf_le_left hy
  have hu : ((s1.field L hLK : OpenSubgroup G) : Subgroup G) ⊓ D.deg.ker ≤ s2.field L hLK :=
    fun y hy => le_frobeniusClosure ((s1.field_inf_ker hLK).le hy)
  have hT := coe_norm_field_field hLK s1 s2 g hg h2 hdeg
  have hrelψ := s1.relDeg_field hLK

  have hφJ : ∀ y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker),
      φ • y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) :=
    fun y hy => smul_mem_fixedModule_inf_ker hLK hφK hy
  have hφjJ : ∀ (j : ℕ), ∀ y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker),
      φ ^ j • y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) :=
    fun j y hy => smul_mem_fixedModule_inf_ker hLK (K.pow_mem hφK j) hy
  have hδJ : ∀ y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker),
      δ • y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) :=
    fun y hy => smul_mem_fixedModule_inf_ker hLK hδ.1 hy
  have hcommφ : ∀ (i j : ℕ) (y : A), s1.elt ^ i • φ ^ j • y = φ ^ j • s1.elt ^ i • y := by
    intro i j y
    have hc : Commute (s1.elt ^ i) (φ ^ j) := by
      rw [h1]
      exact (((Commute.refl φ).pow_left _).pow_left _).pow_right _
    rw [smul_smul, smul_smul, hc.eq]
  have hcommδ : ∀ (i : ℕ), ∀ y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker),
      s1.elt ^ i • δ • y = δ • s1.elt ^ i • y :=
    fun i y hy => (smul_smul_comm hLK hδ (L.pow_mem hψL i) hy).symm
  have hφP' : ∀ (j : ℕ), ∀ y ∈ fixedModule A ((s2.field L hLK : OpenSubgroup G) : Subgroup G),
      φ ^ j • y ∈ fixedModule A ((s2.field L hLK : OpenSubgroup G) : Subgroup G) := by
    intro j y hy
    refine smul_mem_field hLK s2 (hφjJ j) (fun z _ => ?_) hy
    rw [h2]
    exact hcommφ g j z
  have hδP' : ∀ y ∈ fixedModule A ((s2.field L hLK : OpenSubgroup G) : Subgroup G),
      δ • y ∈ fixedModule A ((s2.field L hLK : OpenSubgroup G) : Subgroup G) := by
    intro y hy
    refine smul_mem_field hLK s2 hδJ (fun z hz => ?_) hy
    rw [h2]
    exact hcommδ g z hz
  have hP'J : ∀ y ∈ fixedModule A ((s2.field L hLK : OpenSubgroup G) : Subgroup G),
      y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) :=
    fun y hy => fixedModule_anti le_frobeniusClosure hy

  have hxU : (⟨x, hx⟩ : fixedModule A ((s1.field L hLK : OpenSubgroup G) : Subgroup G)) ∈
      D.units (s1.field L hLK) := hxu
  rw [D.units_eq_map_norm hax hP'P hu] at hxU
  obtain ⟨x'', -, hx''⟩ := hxU
  have haU : (⟨a, ha⟩ : fixedModule A ((s1.field L hLK : OpenSubgroup G) : Subgroup G)) ∈
      D.units (s1.field L hLK) := hau
  rw [D.units_eq_map_norm hax hP'P hu] at haU
  obtain ⟨c, -, hc⟩ := haU
  have hxN : x = ∏ i : Fin g, s1.elt ^ (i : ℕ) • (x'' : A) := by
    rw [← hT, hx'']
  have haN : a = ∏ i : Fin g, s1.elt ^ (i : ℕ) • (c : A) := by
    rw [← hT, hc]

  have hφx'' : φ • (x'' : A) ∈ fixedModule A ((s2.field L hLK : OpenSubgroup G) : Subgroup G) := by
    simpa using hφP' 1 _ x''.2
  have hδc : δ • (c : A) ∈ fixedModule A ((s2.field L hLK : OpenSubgroup G) : Subgroup G) :=
    hδP' _ c.2
  set y' : fixedModule A ((s2.field L hLK : OpenSubgroup G) : Subgroup G) :=
    ⟨φ • (x'' : A), hφx''⟩ / x'' / (⟨δ • (c : A), hδc⟩ / c) with hy'def
  have hNy' : norm A ((s1.field L hLK : OpenSubgroup G) : Subgroup G)
      ((s2.field L hLK : OpenSubgroup G) : Subgroup G) y' = 1 := by
    apply Subtype.ext
    rw [hT]
    simp only [hy'def, Subgroup.coe_div, OneMemClass.coe_one, smul_div', Finset.prod_div_distrib]
    have e1 : ∏ i : Fin g, s1.elt ^ (i : ℕ) • φ • (x'' : A) = φ • x := by
      rw [hxN, Finset.smul_prod']
      refine Finset.prod_congr rfl fun i _ => ?_
      simpa using hcommφ i 1 (x'' : A)
    have e2 : ∏ i : Fin g, s1.elt ^ (i : ℕ) • δ • (c : A) = δ • a := by
      rw [haN, Finset.smul_prod']
      exact Finset.prod_congr rfl fun i _ => hcommδ i _ (hP'J _ c.2)
    rw [e1, e2, ← hxN, ← haN, hrel, div_self']
  obtain ⟨b, -, hb⟩ := D.exists_units_eq_smul_div hax hP'P hu hrelψ hNy'

  set Tb : A := ∏ j : Fin s1.deg, φ ^ (j : ℕ) • (b : A) with hTbdef
  have hTbP' : Tb ∈ fixedModule A ((s2.field L hLK : OpenSubgroup G) : Subgroup G) :=
    Subgroup.prod_mem _ fun j _ => hφP' j _ b.2
  have htele : φ • Tb / Tb = s1.elt • (b : A) / b := by
    rw [hTbdef, Finset.smul_prod', h1]
    simp only [Fin.prod_univ_eq_prod_range (fun j => φ • φ ^ j • (b : A)),
      Fin.prod_univ_eq_prod_range (fun j => φ ^ j • (b : A))]
    have hs := Finset.prod_range_succ (fun j => φ ^ j • (b : A)) s1.deg
    have hs' := Finset.prod_range_succ' (fun j => φ ^ j • (b : A)) s1.deg
    simp only [pow_zero, one_smul] at hs'
    have : ∏ j ∈ Finset.range s1.deg, φ • φ ^ j • (b : A) =
        ∏ j ∈ Finset.range s1.deg, φ ^ (j + 1) • (b : A) := by
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [smul_smul, ← pow_succ']
    rw [this, div_eq_div_iff_mul_eq_mul, ← hs', hs, mul_comm]
  set x' : A := (x'' : A) / Tb with hx'def
  have hx'P' : x' ∈ fixedModule A ((s2.field L hLK : OpenSubgroup G) : Subgroup G) :=
    Subgroup.div_mem _ x''.2 hTbP'
  have hx'J := hP'J _ hx'P'
  have hrel' : φ • x' = x' * (δ • (c : A) / c) := by
    have hy'v : (y' : A) = φ • (x'' : A) / x'' / (δ • (c : A) / c) := by
      simp [hy'def]
    have e : φ • (x'' : A) / x'' = (s1.elt • (b : A) / b) * (δ • (c : A) / c) := by
      rw [← hb, hy'v, div_mul_cancel]
    have e2 : φ • Tb = Tb * (s1.elt • (b : A) / b) := by
      rw [← htele, mul_div_cancel]
    rw [hx'def, smul_div', e2]
    have e3 : φ • (x'' : A) = x'' * ((s1.elt • (b : A) / b) * (δ • (c : A) / c)) := by
      rw [← e, mul_div_cancel]
    rw [e3, mul_div_mul_comm, mul_div_cancel_left]

  set w : A := (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) ⟨x', hx'J⟩ : A)
    with hwdef
  have := normal_inf_ker (D := D) hLK
  have hcJ := hP'J _ c.2
  have hwφ : φ • w = w := by
    rw [hwdef, smul_norm_inf_ker hLK hφK]
    have e : (⟨φ • x', smul_mem_fixedModule_inf_ker hLK hφK hx'J⟩ :
        fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) =
        ⟨x', hx'J⟩ * (⟨δ • (c : A), hδJ _ hcJ⟩ / ⟨c, hcJ⟩) := by
      ext
      simp [hrel']
    rw [e, map_mul, map_div, norm_smul (K := (K : Subgroup G) ⊓ D.deg.ker)
      (L := (L : Subgroup G) ⊓ D.deg.ker) ⟨δ, hδ⟩ ⟨(c : A), hcJ⟩ (hδJ _ hcJ), div_self', mul_one]
  have hwK : w ∈ fixedModule A (K : Subgroup G) :=
    mem_fixedModule_of_smul_eq K hφK hdφ (norm _ _ _ _).2 hwφ

  have hbJ := hP'J _ b.2
  have hNb := coe_norm_field_eq hLK s2 hφK hdφ b
  refine ⟨⟨w, fixedModule_anti hLK hwK⟩ * norm A (L : Subgroup G)
    ((s2.field L hLK : OpenSubgroup G) : Subgroup G) b, ?_⟩
  have hψK : ∀ i : ℕ, s1.elt ^ i ∈ (K : Subgroup G) := fun i => K.pow_mem s1.mem i
  have hx''eq : (x'' : A) = x' * Tb := by rw [hx'def, div_mul_cancel]
  have hTbJ := hP'J _ hTbP'
  have hNTb : (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) ⟨Tb, hTbJ⟩ : A) =
      ∏ j : Fin s1.deg, φ ^ (j : ℕ) •
        (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) ⟨b, hbJ⟩ : A) := by
    have hmemj : ∀ j : Fin s1.deg, φ ^ (j : ℕ) • (b : A) ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) :=
      fun j => hφjJ j _ hbJ
    rw [show (⟨Tb, hTbJ⟩ : fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) =
        ⟨∏ j : Fin s1.deg, φ ^ (j : ℕ) • (b : A), Subgroup.prod_mem _ fun j _ => hmemj j⟩ from rfl,
      coe_norm_inf_ker_prod Finset.univ _ hmemj]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [smul_norm_inf_ker hLK (K.pow_mem hφK j)]
  have hNx : (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
      ⟨x, fixedModule_anti le_frobeniusClosure hx⟩ : A) =
      w ^ g * ∏ i : Fin g, s1.elt ^ (i : ℕ) •
        (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) ⟨Tb, hTbJ⟩ : A) := by
    have hmemi : ∀ i : Fin g, s1.elt ^ (i : ℕ) • (x'' : A) ∈
        fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) :=
      fun i => smul_mem_fixedModule_inf_ker hLK (hψK i) (hP'J _ x''.2)
    have e1 : (⟨x, fixedModule_anti le_frobeniusClosure hx⟩ :
        fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) =
        ⟨∏ i : Fin g, s1.elt ^ (i : ℕ) • (x'' : A), Subgroup.prod_mem _ fun i _ => hmemi i⟩ :=
      Subtype.ext hxN
    rw [e1, coe_norm_inf_ker_prod Finset.univ _ hmemi]
    have e2 : ∀ i : Fin g, (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
        ⟨s1.elt ^ (i : ℕ) • (x'' : A), hmemi i⟩ : A) =
        w * s1.elt ^ (i : ℕ) •
          (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) ⟨Tb, hTbJ⟩ : A) := by
      intro i
      have h3 := smul_norm_inf_ker hLK (hψK i) ⟨(x'' : A), hP'J _ x''.2⟩
      rw [← h3]
      have e4 : (⟨(x'' : A), hP'J _ x''.2⟩ : fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) =
          ⟨x' * Tb, Subgroup.mul_mem _ hx'J hTbJ⟩ := Subtype.ext hx''eq
      rw [e4, coe_norm_inf_ker_mul hx'J hTbJ, smul_mul', ← hwdef, hwK _ (hψK i)]
    rw [Finset.prod_congr rfl fun i _ => e2 i, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  rw [map_mul, Subgroup.coe_mul, coe_norm_of_mem hLK hwK,
    norm_norm (fun y hy => hP'L hy) (fun y hy => hLK hy) b, hNb, hNx, hNTb]
  congr 1
  simp_rw [Finset.smul_prod', smul_smul, h1, ← pow_mul, ← pow_add]
  rw [Fin.prod_univ_eq_prod_range (fun m => φ ^ m • _) s2.deg, hdeg,
    ← prod_range_prod_range_eq _ g s1.deg]
  simp only [Finset.prod_range]

end Key

end ClassFieldData

end GroundTheory.LocalField.Abstract
