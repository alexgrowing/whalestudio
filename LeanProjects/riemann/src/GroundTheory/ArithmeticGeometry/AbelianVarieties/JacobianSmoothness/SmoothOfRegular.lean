import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularLocalDomain
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Jacobian

open IsLocalRing TensorProduct

universe u

noncomputable section

section Presentation

variable {k : Type u} [Field k] {P S : Type u} [CommRing P] [CommRing S] [Algebra k P]
  [Algebra k S] [Algebra P S] [IsScalarTower k P S] [IsLocalRing P] [IsLocalRing S]

def residueAlgEquivOfSurjective (hres : Function.Surjective (algebraMap k (ResidueField S))) :
    k ≃ₐ[k] ResidueField S :=
  AlgEquiv.ofBijective (Algebra.ofId k (ResidueField S))
    ⟨(algebraMap k (ResidueField S)).injective, hres⟩

def valueAt (hres : Function.Surjective (algebraMap k (ResidueField S))) : P →ₐ[k] k :=
  (residueAlgEquivOfSurjective hres).symm.toAlgHom.comp
    ((IsScalarTower.toAlgHom k S (ResidueField S)).comp (IsScalarTower.toAlgHom k P S))

variable (hsurj : Function.Surjective (algebraMap P S))
  (hres : Function.Surjective (algebraMap k (ResidueField S)))

omit [IsLocalRing P] in
lemma algebraMap_valueAt (x : P) :
    algebraMap k (ResidueField S) (valueAt hres x) = algebraMap P (ResidueField S) x := by
  have h := (residueAlgEquivOfSurjective hres).apply_symm_apply
    (algebraMap S (ResidueField S) (algebraMap P S x))
  rw [IsScalarTower.algebraMap_apply P S (ResidueField S)]
  exact h

include hsurj in
omit [Algebra k P] [Algebra k S] [IsScalarTower k P S] in
lemma comap_maximalIdeal_eq : (maximalIdeal S).comap (algebraMap P S) = maximalIdeal P :=
  eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ hsurj)

include hsurj in
omit [Algebra k P] [Algebra k S] [IsScalarTower k P S] in
lemma mem_maximalIdeal_iff (x : P) :
    x ∈ maximalIdeal P ↔ algebraMap P (ResidueField S) x = 0 := by
  rw [← comap_maximalIdeal_eq hsurj, Ideal.mem_comap, IsScalarTower.algebraMap_apply P S
    (ResidueField S), ResidueField.algebraMap_eq, residue_eq_zero_iff]

include hsurj in
lemma sub_valueAt_mem (x : P) : x - algebraMap k P (valueAt hres x) ∈ maximalIdeal P := by
  rw [mem_maximalIdeal_iff hsurj, map_sub, ← IsScalarTower.algebraMap_apply k P (ResidueField S),
    algebraMap_valueAt, sub_self]

def cotD : P →ₗ[k] (maximalIdeal P).Cotangent where
  toFun x := (maximalIdeal P).toCotangent ⟨x - algebraMap k P (valueAt hres x),
    sub_valueAt_mem hsurj hres x⟩
  map_add' x y := by
    rw [← map_add]
    congr 1
    ext
    simp only [map_add, Submodule.coe_add]
    ring
  map_smul' c x := by
    rw [RingHom.id_apply]
    conv_rhs => rw [← algebraMap_smul P c, ← LinearMap.map_smul]
    congr 1
    ext
    rw [Submodule.coe_smul, smul_eq_mul]
    show c • x - algebraMap k P (valueAt hres (c • x)) =
      algebraMap k P c * (x - algebraMap k P (valueAt hres x))
    rw [map_smul, smul_eq_mul, map_mul, Algebra.smul_def]
    ring

omit [Algebra k P] [Algebra k S] [IsScalarTower k P S] in
include hsurj in
lemma ker_le_maximalIdeal : RingHom.ker (algebraMap P S) ≤ maximalIdeal P := by
  intro x hx
  rw [← comap_maximalIdeal_eq hsurj, Ideal.mem_comap, RingHom.mem_ker.1 hx]
  exact zero_mem _

variable [IsNoetherianRing P]

omit [Algebra k P] [Algebra k S] [IsScalarTower k P S] in
include hsurj in

lemma spanFinrank_quotient_le (J : Ideal P) [IsLocalRing (P ⧸ J)]
    (hcov : RingHom.ker (algebraMap P S) ≤ J ⊔ maximalIdeal P ^ 2) :
    (maximalIdeal (P ⧸ J)).spanFinrank ≤ (maximalIdeal S).spanFinrank := by
  have : IsNoetherianRing S := isNoetherianRing_of_surjective P S _ hsurj
  obtain ⟨G, hGc, hGs⟩ :=
    Submodule.FG.exists_span_set_encard_eq_spanFinrank (Ideal.fg_of_isNoetherianRing (maximalIdeal S))
  have hGfin : G.Finite := Set.finite_of_encard_eq_coe hGc
  set σ := Function.surjInv hsurj
  have hσ : ∀ s, algebraMap P S (σ s) = s := Function.surjInv_eq hsurj
  have hcomap : (maximalIdeal (P ⧸ J)).comap (Ideal.Quotient.mk J) = maximalIdeal P :=
    eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
  have hmap : Ideal.map (Ideal.Quotient.mk J) (maximalIdeal P) ≤ maximalIdeal (P ⧸ J) :=
    Ideal.map_le_iff_le_comap.2 hcomap.ge
  have hσm : ∀ g ∈ G, σ g ∈ maximalIdeal P := by
    intro g hg
    rw [← comap_maximalIdeal_eq hsurj, Ideal.mem_comap, hσ, ← hGs]
    exact Submodule.subset_span hg
  have hnsub : maximalIdeal P ≤ Ideal.span (σ '' G) ⊔ RingHom.ker (algebraMap P S) := by
    intro x hx
    have hx' : algebraMap P S x ∈ Ideal.map (algebraMap P S) (Ideal.span (σ '' G)) := by
      rw [Ideal.map_span, Set.image_image]
      have : (fun g => algebraMap P S (σ g)) '' G = G := by
        simp only [hσ, Set.image_id']
      rw [this]
      change algebraMap P S x ∈ Submodule.span S G
      rw [hGs, ← Ideal.mem_comap, comap_maximalIdeal_eq hsurj]
      exact hx
    obtain ⟨y, hy, hyx⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).1 hx'
    refine Submodule.mem_sup.2 ⟨y, hy, x - y, ?_, by ring⟩
    rw [RingHom.mem_ker, map_sub, hyx, sub_self]
  set T : Set (P ⧸ J) := Ideal.Quotient.mk J '' (σ '' G)
  have hTm : T ⊆ maximalIdeal (P ⧸ J) := by
    rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    exact hmap (Ideal.mem_map_of_mem _ (hσm g hg))
  have hle : maximalIdeal (P ⧸ J) ≤ Ideal.span T := by
    apply Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
      (maximalIdeal_le_jacobson ⊥)
    intro z hz
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hx : x ∈ maximalIdeal P := by rw [← hcomap]; exact hz
    have hx2 : x ∈ Ideal.span (σ '' G) ⊔ (J ⊔ maximalIdeal P ^ 2) :=
      sup_le_sup_left hcov _ (hnsub hx)
    have h3 := Ideal.mem_map_of_mem (Ideal.Quotient.mk J) hx2
    rw [Ideal.map_sup, Ideal.map_sup, Ideal.map_span, Ideal.map_quotient_self, bot_sup_eq,
      Ideal.map_pow] at h3
    have H : Ideal.map (Ideal.Quotient.mk J) (maximalIdeal P) ^ 2 ≤
        maximalIdeal (P ⧸ J) • maximalIdeal (P ⧸ J) := by
      rw [pow_two, Ideal.smul_eq_mul]
      exact Ideal.mul_mono hmap hmap
    exact sup_le_sup_left H _ h3
  have heq : maximalIdeal (P ⧸ J) = Ideal.span T :=
    le_antisymm hle (Ideal.span_le.2 hTm)
  rw [heq]
  calc (Ideal.span T).spanFinrank ≤ T.ncard :=
        Submodule.spanFinrank_span_le_ncard_of_finite ((hGfin.image _).image _)
    _ ≤ (σ '' G).ncard := Set.ncard_image_le (hGfin.image _)
    _ ≤ G.ncard := Set.ncard_image_le hGfin
    _ = (maximalIdeal S).spanFinrank := by rw [Set.ncard_def, hGc, ENat.toNat_natCast]

omit [Algebra k P] [Algebra k S] [IsScalarTower k P S] in
include hsurj in

lemma ker_le_span_of_spanFinrank_le {κ : Type} [Fintype κ] (f : κ → P)
    (hfI : ∀ i, f i ∈ RingHom.ker (algebraMap P S))
    (hcov : RingHom.ker (algebraMap P S) ≤ Ideal.span (Set.range f) ⊔ maximalIdeal P ^ 2)
    (d : ℕ) (hμ : (maximalIdeal S).spanFinrank ≤ d) (hdim : (d : WithBot ℕ∞) ≤ ringKrullDim S) :
    RingHom.ker (algebraMap P S) ≤ Ideal.span (Set.range f) := by
  set J := Ideal.span (Set.range f)
  have hJI : J ≤ RingHom.ker (algebraMap P S) := Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hfI i)
  have hJtop : J ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal P).ne_top (hJI.trans (ker_le_maximalIdeal hsurj))
  have : Nontrivial (P ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJtop
  have : IsLocalRing (P ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  let ψ : P ⧸ J →+* S := Ideal.Quotient.lift J (algebraMap P S) (fun x hx => hJI hx)
  have hψ : Function.Surjective ψ := by
    intro s
    obtain ⟨x, rfl⟩ := hsurj s
    exact ⟨Ideal.Quotient.mk J x, rfl⟩
  have hspan := spanFinrank_quotient_le hsurj J hcov
  have h1 : ringKrullDim S ≤ ringKrullDim (P ⧸ J) := ringKrullDim_le_of_surjective ψ hψ
  have h2 : ringKrullDim (P ⧸ J) ≤ (maximalIdeal (P ⧸ J)).spanFinrank :=
    ringKrullDim_le_spanFinrank_maximalIdeal _
  have h3 : ((maximalIdeal (P ⧸ J)).spanFinrank : WithBot ℕ∞) ≤ d := by
    exact_mod_cast hspan.trans hμ
  have : IsRegularLocalRing (P ⧸ J) :=
    IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ (h3.trans (hdim.trans h1))
  have : IsDomain (P ⧸ J) := GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isDomain
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    by_contra hz0
    have h5 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hz0)
    let ψ' : (P ⧸ J) ⧸ Ideal.span {z} →+* S := Ideal.Quotient.lift (Ideal.span {z}) ψ (by
      intro w hw
      obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hw
      rw [map_mul, hz, mul_zero])
    have hψ' : Function.Surjective ψ' := by
      intro s
      obtain ⟨w, hw⟩ := hψ s
      exact ⟨Ideal.Quotient.mk _ w, hw⟩
    have h6 := ringKrullDim_le_of_surjective ψ' hψ'
    have h7 : (d : WithBot ℕ∞) + 1 ≤ d :=
      calc (d : WithBot ℕ∞) + 1 ≤ ringKrullDim S + 1 := by gcongr
        _ ≤ ringKrullDim ((P ⧸ J) ⧸ Ideal.span {z}) + 1 := by gcongr
        _ ≤ ringKrullDim (P ⧸ J) := h5
        _ ≤ d := h2.trans h3
    have h8 : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ (d : ℕ) := by exact_mod_cast h7
    have h9 : d + 1 ≤ d := by exact_mod_cast h8
    omega
  intro x hx
  have hx' : ψ (Ideal.Quotient.mk J x) = 0 := RingHom.mem_ker.1 hx
  exact Ideal.Quotient.eq_zero_iff_mem.1 (hinj (hx'.trans (map_zero ψ).symm))

end Presentation

end

end GroundTheory.Arith.Jacobian
