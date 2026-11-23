import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

noncomputable section

namespace GlobalTheory.InvPairing

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {W : Type} [AddCommGroup W] [Module ℂ W]

def stab {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (v : V) : Subgroup G where
  carrier := {g | ρ g v = v}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, Module.End.mul_apply, hb, ha]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem mem_fixed_iff (σ : Representation ℂ G W) (H : Subgroup G) (v : W) :
    v ∈ GlobalTheory.PRep.fixed σ H ↔ ∀ h ∈ H, σ h v = v := by
  constructor
  · intro hv h hh
    have := hv ⟨h, hh⟩
    simpa using this
  · intro hv h
    simpa using hv h h.2

theorem exists_fixed_avg (σ : Representation ℂ G W) (hs : GlobalTheory.PRep.IsSmooth σ) (K : Subgroup G)
    (hK : IsCompact (K : Set G)) (x : W) :
    ∃ x₀ ∈ GlobalTheory.PRep.fixed σ K, ∀ ℓ : W →ₗ[ℂ] ℂ, (∀ k ∈ K, ∀ v, ℓ (σ k v) = ℓ v) → ℓ x = ℓ x₀ := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hSo : IsOpen ((stab σ x : Subgroup G) : Set G) := hs x
  haveI : Finite (K ⧸ (stab σ x).subgroupOf K) :=
    Subgroup.quotient_finite_of_isOpen _ (hSo.preimage continuous_subtype_val)
  let f : K ⧸ (stab σ x).subgroupOf K → W := fun q => Quotient.liftOn' q (fun k : K => σ k x) (by
    intro a b hab
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at hab
    change σ ((a : G)⁻¹ * b) x = x at hab
    show σ a x = σ b x
    calc σ a x = σ a (σ ((a : G)⁻¹ * b) x) := by rw [hab]
      _ = σ b x := by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left])
  have hrange : Set.range f = Set.range (fun k : K => σ k x) := by
    ext w
    constructor
    · rintro ⟨q, rfl⟩
      induction q using QuotientGroup.induction_on with
      | H k => exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨QuotientGroup.mk k, rfl⟩
  have hfin : (Set.range (fun k : K => σ k x)).Finite := hrange ▸ Set.finite_range f
  set O := hfin.toFinset with hO
  have hxO : x ∈ O := by
    rw [hO, Set.Finite.mem_toFinset]
    exact ⟨1, by simp⟩
  have hperm : ∀ k ∈ K, ∑ v ∈ O, σ k v = ∑ v ∈ O, v := by
    intro k hk
    refine Finset.sum_nbij' (fun v => σ k v) (fun v => σ k⁻¹ v) ?_ ?_ ?_ ?_ ?_
    · intro v hv
      rw [hO, Set.Finite.mem_toFinset] at hv ⊢
      obtain ⟨j, rfl⟩ := hv
      exact ⟨⟨k, hk⟩ * j, by simp [Module.End.mul_apply]⟩
    · intro v hv
      rw [hO, Set.Finite.mem_toFinset] at hv ⊢
      obtain ⟨j, rfl⟩ := hv
      exact ⟨⟨k, hk⟩⁻¹ * j, by simp [Module.End.mul_apply]⟩
    · intro v _
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    · intro v _
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    · intro v _
      rfl
  refine ⟨((O.card : ℂ))⁻¹ • ∑ v ∈ O, v, ?_, ?_⟩
  · rw [mem_fixed_iff]
    intro k hk
    rw [map_smul, map_sum, hperm k hk]
  · intro ℓ hℓ
    have hconst : ∀ v ∈ O, ℓ v = ℓ x := by
      intro v hv
      rw [hO, Set.Finite.mem_toFinset] at hv
      obtain ⟨j, rfl⟩ := hv
      exact hℓ j j.2 x
    have hcard : (O.card : ℂ) ≠ 0 := by
      have : 0 < O.card := Finset.card_pos.mpr ⟨x, hxO⟩
      exact_mod_cast this.ne'
    rw [map_smul, map_sum, Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, nsmul_eq_mul,
      ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

theorem exists_rep (U : Submodule ℂ W) [FiniteDimensional ℂ U]
    (B : W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ) (hB : ∀ x, x ≠ 0 → 0 < (B x x).re) (f : U →ₗ[ℂ] ℂ) :
    ∃ z : U, ∀ x : U, f x = B x z := by
  let T : U →ₗ[ℝ] Module.Dual ℂ U :=
    { toFun := fun z => (B.flip (z : W)).comp U.subtype
      map_add' := by intro a b; ext x; simp
      map_smul' := by
        intro r z
        ext x
        simp only [RingHom.id_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.flip_apply,
          Submodule.coe_smul]
        rw [RCLike.real_smul_eq_coe_smul (K := ℂ) r z, Submodule.coe_smul, LinearMap.map_smulₛₗ, Complex.real_smul,
          RCLike.conj_ofReal, smul_eq_mul]
        rfl }
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    by_contra hne
    have h1 : B z z = 0 := by
      have := LinearMap.congr_fun hz z
      simpa [T] using this
    have := hB z (fun h => hne (Subtype.ext h))
    rw [h1] at this
    simp at this
  have hrank : Module.finrank ℝ U = Module.finrank ℝ (Module.Dual ℂ U) := by
    rw [← Module.finrank_mul_finrank ℝ ℂ U, ← Module.finrank_mul_finrank ℝ ℂ (Module.Dual ℂ U),
      Subspace.dual_finrank_eq]
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hinj
  obtain ⟨z, hz⟩ := hsurj f
  exact ⟨z, fun x => by rw [← hz]; rfl⟩

end GlobalTheory.InvPairing

namespace GlobalTheory.InvPairing

theorem exists_intertwiner : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ (W W' : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (σ : Representation ℂ G W) (σ' : Representation ℂ G W'), IsAdmissible σ → GlobalTheory.PRep.IsSmooth σ' → ∀ (B : W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ) (C : W →ₗ[ℂ] W' →ₛₗ[starRingEnd ℂ] ℂ), (∀ x, x ≠ 0 → 0 < (B x x).re) → (∀ g x y, B (σ g x) (σ g y) = B x y) → (∀ g x y, C (σ g x) (σ' g y) = C x y) → ∃ φ : W' →ₗ[ℂ] W, (∀ g y, φ (σ' g y) = σ g (φ y)) ∧ ∀ x y, C x y = B x (φ y) := by
  intro G _ _ _ K hKo hKc W W' _ _ _ _ σ σ' hσ hσ' B C hB hBinv hCinv
  have huniq : ∀ z z' : W, (∀ x, B x z = B x z') → z = z' := by
    intro z z' h
    by_contra hne
    have hne' : z - z' ≠ 0 := sub_ne_zero.mpr hne
    have hpos := hB _ hne'
    have h0 : B (z - z') (z - z') = 0 := by rw [map_sub (B (z - z')), h (z - z'), sub_self]
    rw [h0] at hpos
    simp at hpos
  have hex : ∀ y, ∃ z, ∀ x, C x y = B x z := by
    intro y
    set K' := K ⊓ stab σ' y with hK'
    have hSo : IsOpen ((stab σ' y : Subgroup G) : Set G) := hσ' y
    have hKo' : IsOpen (K' : Set G) := hKo.inter hSo
    have hKc' : IsCompact (K' : Set G) := hKc.inter_right (Subgroup.isClosed_of_isOpen _ hSo)
    haveI := hσ.2 K' hKo' hKc'
    obtain ⟨z, hz⟩ := exists_rep (GlobalTheory.PRep.fixed σ K') B hB ((C.flip y).comp (GlobalTheory.PRep.fixed σ K').subtype)
    refine ⟨z, fun x => ?_⟩
    obtain ⟨x₀, hx₀, hℓ⟩ := exists_fixed_avg σ hσ.1 K' hKc' x
    have e1 := hℓ (C.flip y) (fun k hk v => by
      have hy : σ' k y = y := (Subgroup.mem_inf.mp hk).2
      simp only [LinearMap.flip_apply]
      conv_lhs => rw [← hy]
      exact hCinv k v y)
    have e2 := hℓ (B.flip z) (fun k hk v => by
      have hz' : σ k z = z := (mem_fixed_iff σ K' z).mp z.2 k hk
      simp only [LinearMap.flip_apply]
      conv_lhs => rw [← hz']
      exact hBinv k v z)
    simp only [LinearMap.flip_apply] at e1 e2
    rw [e1, e2]
    exact hz ⟨x₀, hx₀⟩
  choose φ₀ hφ₀ using hex
  refine ⟨{ toFun := φ₀, map_add' := ?_, map_smul' := ?_ }, ?_, fun x y => hφ₀ y x⟩
  · intro a b
    apply huniq
    intro x
    rw [map_add (B x), ← hφ₀, ← hφ₀, ← hφ₀, map_add]
  · intro c a
    apply huniq
    intro x
    rw [RingHom.id_apply, LinearMap.map_smulₛₗ (B x), ← hφ₀, ← hφ₀, LinearMap.map_smulₛₗ]
  · intro g y
    apply huniq
    intro x
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [← hφ₀]
    have hx : x = σ g (σ g⁻¹ x) := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [hx, hCinv, hBinv]
    exact hφ₀ y _

end GlobalTheory.InvPairing
