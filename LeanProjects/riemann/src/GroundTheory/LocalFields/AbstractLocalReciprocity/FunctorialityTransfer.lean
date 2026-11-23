import Mathlib
import GroundTheory.LocalFields.AbstractLocalReciprocity.FunctorialityNorm

namespace GroundTheory.LocalField.Abstract

open ProfiniteInteger MulAction

section Transfer

theorem map_transfer {Γ : Type*} [Group Γ] {H : Subgroup Γ} [H.FiniteIndex] {B C : Type*} [CommGroup B]
    [CommGroup C] (φ : H →* B) (f : B →* C) (g : Γ) : f (φ.transfer g) = (f.comp φ).transfer g := by
  classical
  let _ : Fintype (Quotient (orbitRel (Subgroup.zpowers g) (Γ ⧸ H))) := Fintype.ofFinite _
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot,
    MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot, map_prod]
  rfl

end Transfer

section FixedField

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {d : G →* Multiplicative ℤ̂} {L : Subgroup G} {σ : G}

theorem exists_eq_zpow_mul_of_mem_frobeniusClosure (hL : IsOpen (L : Set G))
    (hσ : σ ∈ Subgroup.normalizer ((L ⊓ d.ker : Subgroup G) : Set G)) {y : G}
    (hy : y ∈ frobeniusClosure d L σ) : ∃ m : ℤ, ∃ l ∈ L, y = σ ^ m * l := by
  have hy' : y ∈ closure ((Subgroup.zpowers σ ⊔ (L ⊓ d.ker) : Subgroup G) : Set G) := by
    rw [← Subgroup.topologicalClosure_coe]
    exact hy
  have hO : IsOpen ((fun z => y⁻¹ * z) ⁻¹' (L : Set G)) :=
    hL.preimage (continuous_const.mul continuous_id)
  have hyO : y ∈ (fun z => y⁻¹ * z) ⁻¹' (L : Set G) := by
    show y⁻¹ * y ∈ L
    rw [inv_mul_cancel]
    exact L.one_mem
  obtain ⟨h, hhO, hhS⟩ := mem_closure_iff.1 hy' _ hO hyO
  obtain ⟨m, j, hj, rfl⟩ := (mem_zpowers_sup_iff hσ).1 hhS
  refine ⟨m, j * (y⁻¹ * (σ ^ m * j))⁻¹, L.mul_mem hj.1 (L.inv_mem hhO), by group⟩

variable [CompactSpace G] [TotallyDisconnectedSpace G]

theorem frobeniusClosure_pow_eq_inf (hd : Continuous d) (hL : IsOpen (L : Set G)) {K' : Subgroup G}
    (hK' : IsOpen (K' : Set G)) (hLK' : L ≤ K') {ρ : G}
    (hρ : ρ ∈ Subgroup.normalizer ((L ⊓ d.ker : Subgroup G) : Set G)) {N : ℕ} (hN : N ≠ 0)
    (hdρ : d ρ = Multiplicative.ofAdd (N : ℤ̂)) {f : ℕ} (hf : 0 < f) (hρf : ρ ^ f ∈ K')
    (hdiv : ∀ k : ℤ, ρ ^ k ∈ K' → (f : ℤ) ∣ k) :
    frobeniusClosure d L (ρ ^ f) = K' ⊓ frobeniusClosure d L ρ := by
  have hρf' : ρ ^ f ∈ Subgroup.normalizer ((L ⊓ d.ker : Subgroup G) : Set G) := Subgroup.pow_mem _ hρ f
  have hdρf : d (ρ ^ f) = Multiplicative.ofAdd ((f * N : ℕ) : ℤ̂) := by
    rw [map_pow, hdρ, ← ofAdd_nsmul, nsmul_eq_mul, Nat.cast_mul]
  have hle : frobeniusClosure d L (ρ ^ f) ≤ frobeniusClosure d L ρ :=
    frobeniusClosure_le isClosed_frobeniusClosure (Subgroup.pow_mem _ mem_frobeniusClosure_self f)
      le_frobeniusClosure
  apply le_antisymm
  · refine frobeniusClosure_le ((OpenSubgroup.isClosed ⟨K', hK'⟩).inter isClosed_frobeniusClosure)
      ⟨hρf, Subgroup.pow_mem _ mem_frobeniusClosure_self f⟩ ?_
    exact le_inf (inf_le_left.trans hLK') le_frobeniusClosure
  · intro y hy
    obtain ⟨hyK', hyS⟩ := Subgroup.mem_inf.1 hy
    set M : ℕ+ := ⟨f * N, Nat.mul_pos hf (Nat.pos_of_ne_zero hN)⟩ with hMdef
    set V : Set G := (L : Set G) ∩ d ⁻¹' (Multiplicative.toAdd ⁻¹' (multiples M : Set ℤ̂)) with hVdef
    have hV : IsOpen V := hL.inter ((isOpen_multiples M).preimage (continuous_toAdd.comp hd))
    have hO : IsOpen ((fun z => y⁻¹ * z) ⁻¹' V) := hV.preimage (continuous_const.mul continuous_id)
    have hyO : y ∈ (fun z => y⁻¹ * z) ⁻¹' V := by
      simp only [Set.mem_preimage, inv_mul_cancel, hVdef, Set.mem_inter_iff, map_one, toAdd_one]
      exact ⟨L.one_mem, (multiples M).zero_mem⟩
    have hy' : y ∈ closure ((Subgroup.zpowers ρ ⊔ (L ⊓ d.ker) : Subgroup G) : Set G) := by
      rw [← Subgroup.topologicalClosure_coe]
      exact hyS
    obtain ⟨h, hhO, hhS⟩ := mem_closure_iff.1 hy' _ hO hyO
    have hhS' : h ∈ frobeniusClosure d L ρ := Subgroup.le_topologicalClosure _ hhS
    obtain ⟨k, j, hj, rfl⟩ := (mem_zpowers_sup_iff hρ).1 hhS
    obtain ⟨huL, huM⟩ := hhO
    set u := y⁻¹ * (ρ ^ k * j) with hudef

    have hρk : ρ ^ k ∈ K' := by
      have : ρ ^ k = y * u * j⁻¹ := by rw [hudef]; group
      rw [this]
      exact K'.mul_mem (K'.mul_mem hyK' (hLK' huL)) (K'.inv_mem (hLK' hj.1))
    obtain ⟨k', rfl⟩ := hdiv k hρk
    have hhf : ρ ^ ((f : ℤ) * k') * j ∈ frobeniusClosure d L (ρ ^ f) := by
      refine Subgroup.mul_mem _ ?_ (le_frobeniusClosure hj)
      rw [zpow_mul, zpow_natCast]
      exact Subgroup.zpow_mem _ mem_frobeniusClosure_self k'

    have huS : u ∈ frobeniusClosure d L ρ :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hyS) hhS'
    have hmap := map_frobeniusClosure hd hρf' hdρf
    have hdu : d u ∈ (frobeniusClosure d L (ρ ^ f)).map d := by
      rw [hmap]
      exact huM
    obtain ⟨z, hz, hzu⟩ := hdu
    have hzu' : z⁻¹ * u ∈ frobeniusClosure d L ρ ⊓ d.ker := by
      refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (hle hz)) huS, ?_⟩
      exact (MonoidHom.mem_ker).2 (by rw [map_mul, map_inv, hzu, inv_mul_cancel])
    rw [frobeniusClosure_inf_ker hd hL hρ hN hdρ] at hzu'
    have hu : u ∈ frobeniusClosure d L (ρ ^ f) := by
      have : u = z * (z⁻¹ * u) := by group
      rw [this]
      exact Subgroup.mul_mem _ hz (le_frobeniusClosure hzu')
    have : y = ρ ^ ((f : ℤ) * k') * j * u⁻¹ := by rw [hudef]; group
    rw [this]
    exact Subgroup.mul_mem _ hhf (Subgroup.inv_mem _ hu)

end FixedField

section Ver

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] in

theorem map_conj_eq_of_normal {K L : Subgroup G} [(L.subgroupOf K).Normal] (hLK : L ≤ K) {τ : G}
    (hτ : τ ∈ K) : L.map (MulAut.conj τ).toMonoidHom = L := by
  ext y
  rw [mem_map_conj]
  constructor
  · intro h
    have := conj_mem_of_normal hτ (hLK h) h
    simpa [mul_assoc] using this
  · intro h
    have := conj_mem_of_normal (K.inv_mem hτ) (hLK h) h
    simpa using this

variable {K K' L : OpenSubgroup G} [((L : Subgroup G).subgroupOf K).Normal]
  [((L : Subgroup G).subgroupOf K').Normal]

omit [IsTopologicalGroup G] [CompactSpace G] in

theorem galRestrict_injective (hK'K : K' ≤ K) :
    Function.Injective (galRestrict (K := K) (L := L) (K' := K') (L' := L) hK'K le_rfl) := by
  rw [injective_iff_map_eq_one]
  intro q hq
  induction q using QuotientGroup.induction_on with
  | H k =>
    rw [galRestrict_mk, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hq
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hq

omit [IsTopologicalGroup G] [CompactSpace G] in

theorem mk_mem_range_galRestrict_iff (hLK' : L ≤ K') (hK'K : K' ≤ K) (k : (K : Subgroup G)) :
    (k : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ∈
      (galRestrict (K := K) (L := L) (K' := K') (L' := L) hK'K le_rfl).range ↔
      (k : G) ∈ (K' : Subgroup G) := by
  constructor
  · rintro ⟨q, hq⟩
    induction q using QuotientGroup.induction_on with
    | H k' =>
      rw [galRestrict_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hq
      have h := (K' : Subgroup G).mul_mem k'.2 (hLK' hq)
      simpa using h
  · intro hk
    exact ⟨((⟨k, hk⟩ : (K' : Subgroup G)) : _ ⧸ _), rfl⟩

omit [IsTopologicalGroup G] [CompactSpace G] in
theorem mk_mk_eq_iff (hLK' : L ≤ K') (hK'K : K' ≤ K) (a b : (K : Subgroup G)) :
    ((a : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :
        _ ⧸ (galRestrict (K := K) (L := L) (K' := K') (L' := L) hK'K le_rfl).range) =
      ((b : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) : _ ⧸ _) ↔
      (a : G)⁻¹ * b ∈ (K' : Subgroup G) := by
  rw [QuotientGroup.eq, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    mk_mem_range_galRestrict_iff hLK' hK'K]
  simp

omit [IsTopologicalGroup G] [CompactSpace G] in
theorem zpow_smul_mk_mk_eq_iff (hLK' : L ≤ K') (hK'K : K' ≤ K) (σ x : (K : Subgroup G)) (k : ℤ) :
    ((σ : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ^ k) •
        ((x : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :
          _ ⧸ (galRestrict (K := K) (L := L) (K' := K') (L' := L) hK'K le_rfl).range) =
      ((x : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) : _ ⧸ _) ↔
      (x : G)⁻¹ * (σ : G) ^ k * x ∈ (K' : Subgroup G) := by
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, ← QuotientGroup.mk_zpow, ← QuotientGroup.mk_mul,
    mk_mk_eq_iff hLK' hK'K]
  have e : (((σ ^ k * x : (K : Subgroup G)) : G))⁻¹ * x = ((x : G)⁻¹ * (σ : G) ^ k * x)⁻¹ := by
    simp only [Subgroup.coe_mul, SubgroupClass.coe_zpow]
    group
  rw [e, Subgroup.inv_mem_iff]

noncomputable def verlagerung (hK'K : K' ≤ K) :
    (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K →*
      Abelianization ((K' : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K') :=
  ((Abelianization.of).comp
    (MonoidHom.ofInjective (galRestrict_injective (L := L) hK'K)).symm.toMonoidHom).transfer

end Ver

namespace ClassFieldData

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  {D : ClassFieldData G A}

omit [TotallyDisconnectedSpace G] in

theorem exists_frobeniusLift_of_deg {K : OpenSubgroup G} {x : G} (hx : x ∈ (K : Subgroup G)) {N : ℕ}
    (hN : 0 < N) (hd : D.deg x = Multiplicative.ofAdd (N : ℤ̂)) :
    ∃ s : D.FrobeniusLift K, s.elt = x := by
  have hm := toAdd_deg_mem_multiples (D := D) K hx
  rw [hd, toAdd_ofAdd, ← Int.cast_natCast,
    intCast_mem_multiples_iff (Nat.pos_of_ne_zero (D.inertiaDegree_ne_zero K))] at hm
  obtain ⟨m, rfl⟩ := Int.natCast_dvd_natCast.1 hm
  have hm0 : 0 < m := Nat.pos_of_mul_pos_left hN
  exact ⟨⟨x, hx, m, hm0, by rw [hd, Nat.mul_comm]⟩, rfl⟩

section Ver

variable {K K' L : OpenSubgroup G} [((L : Subgroup G).subgroupOf K).Normal]
  [((L : Subgroup G).subgroupOf K').Normal]

theorem reciprocity_mk_conj_pow (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]
    (hLK' : L ≤ K') (hK'K : K' ≤ K) (s : D.FrobeniusLift K) (x : (K : Subgroup G)) {f : ℕ}
    (hf0 : 0 < f) (hf : ∀ k : ℤ, (x : G)⁻¹ * s.elt ^ k * x ∈ (K' : Subgroup G) ↔ (f : ℤ) ∣ k)
    (hmem : (x : G)⁻¹ * s.elt ^ f * x ∈ (K' : Subgroup G))
    {π : fixedModule A ((s.field L (hLK'.trans hK'K) : OpenSubgroup G) : Subgroup G)}
    (hπ : D.valuation (s.field L (hLK'.trans hK'K)) π = Multiplicative.ofAdd 1) :
    D.reciprocity hLK' hax ((⟨_, hmem⟩ : (K' : Subgroup G)) :
      (K' : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K') =
      (QuotientGroup.mk (norm A (K' : Subgroup G)
        ((K' ⊓ conjOpen (x : G)⁻¹ (s.field L (hLK'.trans hK'K)) : OpenSubgroup G) : Subgroup G)
        ⟨(x : G)⁻¹ • (π : A), fixedModule_anti (inf_le_right (a := K'))
          (smul_mem_fixedModule π.2 _)⟩) : tateZero A (K' : Subgroup G) (L : Subgroup G)) := by
  have hLK : L ≤ K := hLK'.trans hK'K
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : G, ρ = (x : G)⁻¹ * s.elt * x := ⟨_, rfl⟩
  have hρK : ρ ∈ (K : Subgroup G) := by
    rw [hρdef]
    exact (K : Subgroup G).mul_mem ((K : Subgroup G).mul_mem ((K : Subgroup G).inv_mem x.2) s.mem) x.2
  have hρn := FrobeniusLift.mem_normalizer (D := D) hLK hρK
  have hdρ : D.deg ρ = Multiplicative.ofAdd ((s.deg * inertiaDegree D.deg K : ℕ) : ℤ̂) := by
    rw [hρdef, map_mul, map_mul, map_inv, mul_comm _ (D.deg s.elt), mul_assoc, inv_mul_cancel,
      mul_one, s.deg_eq]
  have hN : s.deg * inertiaDegree D.deg K ≠ 0 := s.degree_ne_zero
  have hρz : ∀ k : ℤ, ρ ^ k = (x : G)⁻¹ * s.elt ^ k * x := fun k => by
    have := conj_zpow (i := k) (a := (x : G)⁻¹) (b := s.elt)
    simpa [hρdef] using this
  have hρn' : ∀ k : ℕ, ρ ^ k = (x : G)⁻¹ * s.elt ^ k * x := fun k => by
    have := conj_pow (i := k) (a := (x : G)⁻¹) (b := s.elt)
    simpa [hρdef] using this
  have hmemρ : ρ ^ f ∈ (K' : Subgroup G) := by
    rw [hρn']
    exact hmem
  have hdivρ : ∀ k : ℤ, ρ ^ k ∈ (K' : Subgroup G) → (f : ℤ) ∣ k := fun k hk =>
    (hf k).1 (by rwa [hρz] at hk)
  obtain ⟨t, ht⟩ := exists_frobeniusLift_of_deg (D := D) (K := K') hmemρ
    (N := f * (s.deg * inertiaDegree D.deg K)) (Nat.mul_pos hf0 (Nat.pos_of_ne_zero hN))
    (by rw [map_pow, hdρ, ← ofAdd_nsmul, nsmul_eq_mul]; norm_cast)
  have hconjS : ((conjOpen (x : G)⁻¹ (s.field L hLK) : OpenSubgroup G) : Subgroup G) =
      frobeniusClosure D.deg L ρ := by
    rw [coe_conjOpen, s.coe_field hLK, map_conj_frobeniusClosure,
      map_conj_eq_of_normal hLK ((K : Subgroup G).inv_mem x.2), inv_inv, hρdef]
  have hkey := frobeniusClosure_pow_eq_inf D.continuous_deg L.isOpen K'.isOpen hLK' hρn hN hdρ hf0
    hmemρ hdivρ
  have htfield : ((t.field L hLK' : OpenSubgroup G) : Subgroup G) =
      ((K' ⊓ conjOpen (x : G)⁻¹ (s.field L hLK) : OpenSubgroup G) : Subgroup G) := by
    rw [t.coe_field hLK', ht, hkey, ← hconjS]
    rfl
  have hle : t.field L hLK' ≤ conjOpen (x : G)⁻¹ (s.field L hLK) := by
    intro y hy
    have : y ∈ ((t.field L hLK' : OpenSubgroup G) : Subgroup G) := hy
    rw [htfield] at this
    exact (Subgroup.mem_inf.1 this).2
  have ha : (x : G)⁻¹ • (π : A) ∈
      fixedModule A ((conjOpen (x : G)⁻¹ (s.field L hLK) : OpenSubgroup G) : Subgroup G) :=
    smul_mem_fixedModule π.2 _
  have hv1 : D.valuation (conjOpen (x : G)⁻¹ (s.field L hLK)) ⟨_, ha⟩ = Multiplicative.ofAdd 1 := by
    rw [valuation_conj (x : G)⁻¹ rfl π ⟨_, ha⟩ rfl, hπ]
  have hram : relRamificationIndex D.deg (conjOpen (x : G)⁻¹ (s.field L hLK)) (t.field L hLK') = 1 := by
    rw [relRamificationIndex, Subgroup.relIndex_eq_one]
    intro y hy
    obtain ⟨hyk, hyS⟩ := Subgroup.mem_inf.1 hy
    have hy' : y ∈ frobeniusClosure D.deg L ρ ⊓ D.deg.ker := by
      refine ⟨?_, hyk⟩
      rw [← hconjS]
      exact hyS
    rw [frobeniusClosure_inf_ker D.continuous_deg L.isOpen hρn hN hdρ] at hy'
    show y ∈ frobeniusClosure D.deg L t.elt
    rw [ht]
    exact le_frobeniusClosure hy'
  have hπ' : D.valuation (t.field L hLK') ⟨(x : G)⁻¹ • (π : A), fixedModule_anti hle ha⟩ =
      Multiplicative.ofAdd 1 := by
    rw [D.valuation_of_mem hle ha, hv1, hram, pow_one]
  have he : ((⟨_, hmem⟩ : (K' : Subgroup G)) : (K' : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K') =
      ((⟨t.elt, t.mem⟩ : (K' : Subgroup G)) : _ ⧸ _) := by
    congr 1
    apply Subtype.ext
    show _ = t.elt
    rw [ht, hρn']
  rw [he, D.reciprocity_mk_eq_norm hLK' hax t hπ']
  congr 1
  apply Subtype.ext
  exact coe_norm_congr rfl htfield _

theorem reciprocity_verlagerung (hax : ClassFieldAxiom G A) [IsDiscreteModule G A] (hLK' : L ≤ K')
    (hK'K : K' ≤ K) (g : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :
    Abelianization.lift (D.reciprocity hLK' hax) (verlagerung hK'K g) =
      tateZeroIncl hLK' hK'K (D.reciprocity (hLK'.trans hK'K) hax g) := by
  classical
  have hLK : L ≤ K := hLK'.trans hK'K
  obtain ⟨s, rfl⟩ := exists_frobeniusLift_mk (D := D) hLK g
  obtain ⟨π, hπ⟩ := D.exists_prime (s.field L hLK)
  rw [D.reciprocity_mk_eq_norm hLK hax s hπ, tateZeroIncl_mk, verlagerung, map_transfer]
  set H := (galRestrict (K := K) (L := L) (K' := K') (L' := L) hK'K le_rfl).range with hH
  set γ : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K :=
    ((⟨s.elt, s.mem⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) with hγ
  let _ : Fintype (Quotient (orbitRel (Subgroup.zpowers γ)
    (((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ⧸ H))) := Fintype.ofFinite _
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
  let τ : Quotient (orbitRel (Subgroup.zpowers γ)
      (((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ⧸ H)) → (K : Subgroup G) :=
    fun q => q.out.out.out
  have hqτ : ∀ q, q.out = (((τ q : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :
      _ ⧸ H) := fun q => by
    simp only [τ, QuotientGroup.out_eq']
  have hper : ∀ q (k : ℤ), ((τ q : G))⁻¹ * s.elt ^ k * τ q ∈ (K' : Subgroup G) ↔
      (Function.minimalPeriod (γ • ·) q.out : ℤ) ∣ k := fun q k => by
    rw [← zpow_smul_eq_iff_minimalPeriod_dvd, hqτ q, hγ, zpow_smul_mk_mk_eq_iff hLK' hK'K]
  have hpos : ∀ q : Quotient (orbitRel (Subgroup.zpowers γ) (((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ⧸ H)), 0 < Function.minimalPeriod (γ • ·) q.out := fun q =>
    Nat.pos_of_dvd_of_pos (pow_smul_eq_iff_minimalPeriod_dvd.1 (by rw [pow_orderOf_eq_one, one_smul]))
      (orderOf_pos γ)
  have hmemf : ∀ q : Quotient (orbitRel (Subgroup.zpowers γ) (((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ⧸ H)), ((τ q : G))⁻¹ * s.elt ^ Function.minimalPeriod (γ • ·) q.out * τ q ∈
      (K' : Subgroup G) := fun q => by
    have := (hper q (Function.minimalPeriod (γ • ·) q.out)).2 dvd_rfl
    rwa [zpow_natCast] at this
  have hfac : ∀ q : Quotient (orbitRel (Subgroup.zpowers γ) (((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ⧸ H)), ((Abelianization.lift (D.reciprocity hLK' hax)).comp
      ((Abelianization.of).comp
        (MonoidHom.ofInjective (galRestrict_injective (L := L) hK'K)).symm.toMonoidHom))
        ⟨(q.out.out)⁻¹ * γ ^ Function.minimalPeriod (γ • ·) q.out * q.out.out,
          QuotientGroup.out_conj_pow_minimalPeriod_mem H γ q.out⟩ =
      (QuotientGroup.mk (norm A (K' : Subgroup G)
        ((K' ⊓ conjOpen ((τ q : G))⁻¹ (s.field L hLK) : OpenSubgroup G) : Subgroup G)
        ⟨((τ q : G))⁻¹ • (π : A), fixedModule_anti (inf_le_right (a := K'))
          (smul_mem_fixedModule π.2 _)⟩) : tateZero A (K' : Subgroup G) (L : Subgroup G)) := by
    intro q
    refine Eq.trans ?_ (reciprocity_mk_conj_pow hax hLK' hK'K s (τ q) (hpos q) (hper q) (hmemf q) hπ)
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, Abelianization.lift_apply_of]
    congr 1
    rw [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [MonoidHom.ofInjective_apply, galRestrict_mk]
    show (Quotient.out q.out)⁻¹ * γ ^ Function.minimalPeriod (γ • ·) q.out * Quotient.out q.out = _
    have hL : (Quotient.out q.out)⁻¹ * γ ^ Function.minimalPeriod (γ • ·) q.out * Quotient.out q.out =
        ((((τ q)⁻¹ * ⟨s.elt, s.mem⟩ ^ Function.minimalPeriod (γ • ·) q.out * τ q : (K : Subgroup G))) :
          (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow]
      simp only [τ, QuotientGroup.out_eq']
      rfl
    rw [hL]
    congr 1
  rw [Finset.prod_congr rfl fun q _ => hfac q, ← QuotientGroup.mk_prod]
  congr 1
  apply Subtype.ext
  rw [SubmonoidClass.coe_finsetProd]
  refine (coe_norm_eq_prod_norm_inf hK'K (fun q => (τ q : G)) (fun q => (τ q).2)
    (fun q => ((K' ⊓ conjOpen ((τ q : G))⁻¹ (s.field L hLK) : OpenSubgroup G) : Subgroup G))
    ?_ ?_ ?_ π (fun q => fixedModule_anti (inf_le_right (a := K'))
      (smul_mem_fixedModule π.2 _))).symm
  · intro q k hk
    show k ∈ (K' : Subgroup G) ⊓ ((conjOpen ((τ q : G))⁻¹ (s.field L hLK) : OpenSubgroup G) :
      Subgroup G) ↔ _
    rw [Subgroup.mem_inf, mem_conjOpen, inv_inv]
    exact ⟨fun h => h.2, fun h => ⟨hk, h⟩⟩
  · intro c hc
    let p : ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ⧸ H :=
      (((⟨c⁻¹, (K : Subgroup G).inv_mem hc⟩ : (K : Subgroup G)) :
        (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) : _ ⧸ H)
    let q : Quotient (orbitRel (Subgroup.zpowers γ) (((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ⧸ H)) := Quotient.mk'' p
    obtain ⟨⟨z, hz⟩, hzp⟩ := orbitRel_apply.1 (Quotient.mk_out' p : orbitRel _ _ q.out p)
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    have hzp' : γ ^ m • p = q.out := hzp
    rw [hqτ q, hγ, ← QuotientGroup.mk_zpow, MulAction.Quotient.smul_mk, smul_eq_mul,
      ← QuotientGroup.mk_mul, mk_mk_eq_iff hLK' hK'K] at hzp'
    refine ⟨q, _, hzp', ?_⟩
    have e : (τ q : G) * ((((⟨s.elt, s.mem⟩ : (K : Subgroup G)) ^ m *
        ⟨c⁻¹, (K : Subgroup G).inv_mem hc⟩ : (K : Subgroup G)) : G)⁻¹ * τ q)⁻¹ * c = s.elt ^ m := by
      simp only [Subgroup.coe_mul, SubgroupClass.coe_zpow]
      group
    rw [e]
    exact Subgroup.zpow_mem _ (s.elt_mem_field hLK) m
  · intro q q' k hk k' hk' hy
    obtain ⟨m, l, hl, hyeq⟩ := exists_eq_zpow_mul_of_mem_frobeniusClosure L.isOpen
      (FrobeniusLift.mem_normalizer (D := D) hLK s.mem) hy
    rw [← Quotient.out_eq q, ← Quotient.out_eq q']
    apply Quotient.sound
    refine (orbitRel_apply (G := Subgroup.zpowers γ)).2 ⟨⟨γ ^ m, Subgroup.zpow_mem_zpowers γ m⟩, ?_⟩
    show γ ^ m • q'.out = q.out
    rw [hqτ q, hqτ q', hγ, ← QuotientGroup.mk_zpow, MulAction.Quotient.smul_mk, smul_eq_mul,
      ← QuotientGroup.mk_mul, mk_mk_eq_iff hLK' hK'K]
    have hl1 : s.elt ^ m * l * (s.elt ^ m)⁻¹ ∈ (L : Subgroup G) :=
      conj_mem_of_normal ((K : Subgroup G).zpow_mem s.mem m) (hLK hl) hl
    have hl2 := conj_mem_of_normal ((K : Subgroup G).inv_mem (τ q).2) (hLK hl1) hl1
    have hτ' : (τ q' : G) = (s.elt ^ m * l)⁻¹ * ((τ q : G) * k⁻¹ * k') := by
      rw [← hyeq]
      group
    have e : ((((⟨s.elt, s.mem⟩ : (K : Subgroup G)) ^ m * τ q' : (K : Subgroup G)) : G))⁻¹ * τ q =
        k'⁻¹ * k * (((τ q : G))⁻¹ * (s.elt ^ m * l * (s.elt ^ m)⁻¹) * ((τ q : G))⁻¹⁻¹) := by
      simp only [Subgroup.coe_mul, SubgroupClass.coe_zpow]
      rw [hτ']
      group
    rw [e]
    exact (K' : Subgroup G).mul_mem
      ((K' : Subgroup G).mul_mem ((K' : Subgroup G).inv_mem hk') hk) (hLK' hl2)

end Ver

end ClassFieldData

end GroundTheory.LocalField.Abstract
