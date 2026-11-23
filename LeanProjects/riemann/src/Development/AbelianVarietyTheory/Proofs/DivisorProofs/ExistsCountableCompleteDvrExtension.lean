import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRingHom
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCdvrMkLeContinuum
open CategoryTheory AlgebraicGeometry Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.BdDim GlobalTheory.SiegelTor GlobalTheory.ZM GlobalTheory.CM GlobalTheory.Models
open scoped CategoryTheory.Obj

namespace GlobalTheory.SmallDVR

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

def traceSubring (K₀ : Subfield (FractionRing V)) : Subring V :=
  K₀.toSubring.comap (algebraMap V (FractionRing V))

theorem mem_traceSubring {K₀ : Subfield (FractionRing V)} {x : V} :
    x ∈ traceSubring K₀ ↔ algebraMap V (FractionRing V) x ∈ K₀ := Iff.rfl

theorem traceSubring_cancel {K₀ : Subfield (FractionRing V)} {x c : V} (hx : x ∈ traceSubring K₀)
    (hx0 : x ≠ 0) (hxc : x * c ∈ traceSubring K₀) : c ∈ traceSubring K₀ := by
  rw [mem_traceSubring] at *
  have hx0' : algebraMap V (FractionRing V) x ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 hx0
  have : algebraMap V (FractionRing V) c =
      algebraMap V (FractionRing V) (x * c) / algebraMap V (FractionRing V) x := by
    rw [map_mul]; field_simp
  rw [this]; exact K₀.div_mem hxc hx

theorem traceSubring_isUnit_iff {K₀ : Subfield (FractionRing V)} (x : traceSubring K₀) :
    IsUnit x ↔ IsUnit (x : V) := by
  refine ⟨fun h => h.map (traceSubring K₀).subtype, fun h => ?_⟩
  obtain ⟨c, hc⟩ := h.exists_right_inv
  have hx0 : (x : V) ≠ 0 := fun h0 => by simp [h0] at hc
  have hcm : c ∈ traceSubring K₀ :=
    traceSubring_cancel x.2 hx0 (by rw [hc]; exact (traceSubring K₀).one_mem)
  exact isUnit_iff_exists_inv.2 ⟨⟨c, hcm⟩, Subtype.ext hc⟩

theorem traceSubring_isLocalRing (K₀ : Subfield (FractionRing V)) : IsLocalRing (traceSubring K₀) := by
  refine IsLocalRing.of_nonunits_add fun a b ha hb => ?_
  simp only [mem_nonunits_iff, traceSubring_isUnit_iff] at *
  push_cast
  exact IsLocalRing.nonunits_add ha hb

theorem traceSubring_principal (K₀ : Subfield (FractionRing V)) :
    IsPrincipalIdealRing (traceSubring K₀) := by
  classical
  refine ⟨fun I => ?_⟩
  by_cases hI : I = ⊥
  · rw [hI]; exact bot_isPrincipal
  obtain ⟨y₀, hy₀, hy₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hex : ∃ n : ℕ, ∃ y ∈ I, y ≠ 0 ∧ IsDiscreteValuationRing.addVal V (y : V) = n := by
    have hne : IsDiscreteValuationRing.addVal V (y₀ : V) ≠ ⊤ := by
      rw [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
      exact fun h => hy₀0 (Subtype.ext h)
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hne
    exact ⟨n, y₀, hy₀, hy₀0, hn.symm⟩
  obtain ⟨x, hxI, hx0, hxn⟩ := Nat.find_spec hex
  refine ⟨⟨x, le_antisymm (fun y hy => ?_) ?_⟩⟩
  · rw [Submodule.mem_span_singleton]
    by_cases hy0 : y = 0
    · exact ⟨0, by simp [hy0]⟩
    have hyne : IsDiscreteValuationRing.addVal V (y : V) ≠ ⊤ := by
      rw [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
      exact fun h => hy0 (Subtype.ext h)
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hyne
    have hle : Nat.find hex ≤ m := Nat.find_min' hex ⟨y, hy, hy0, hm.symm⟩
    have hdvd : (x : V) ∣ (y : V) := by
      rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, hxn, ← hm]
      exact_mod_cast hle
    obtain ⟨c, hc⟩ := hdvd
    have hx0' : (x : V) ≠ 0 := fun h => hx0 (Subtype.ext h)
    have hcm : c ∈ traceSubring K₀ := traceSubring_cancel x.2 hx0' (by rw [← hc]; exact y.2)
    exact ⟨⟨c, hcm⟩, Subtype.ext (by simp [hc, mul_comm])⟩
  · rw [Submodule.span_le, Set.singleton_subset_iff]; exact hxI

end GlobalTheory.SmallDVR

namespace GlobalTheory.SmallDVR

theorem exists_small_cdvr_of_localHom :
    ∀ (A V : Type) [CommRing A] [IsLocalRing A] [CommRing V] [IsDomain V]
      [IsDiscreteValuationRing V] [CharZero V] (φ : A →+* V), Countable A → IsLocalHom φ →
      (∃ a ∈ maximalIdeal A, φ a ≠ 0) →
      ∃ (T : Formalism.L2.Pj.CDVR) (ψ : A →+* T.V), IsLocalHom ψ ∧ RingHom.ker ψ = RingHom.ker φ ∧
        Cardinal.mk T.V ≤ Cardinal.continuum := by
  intro A V _ _ _ _ _ _ φ hA hφ ⟨a, ha, hφa⟩
  let K₀ : Subfield (FractionRing V) :=
    Subfield.closure (Set.range ((algebraMap V (FractionRing V)).comp φ))
  let V₀ := traceSubring K₀
  have hmem : ∀ x, φ x ∈ V₀ := fun x =>
    (mem_traceSubring).2 (Subfield.subset_closure ⟨x, rfl⟩)
  haveI : Countable K₀ := by
    rw [← Cardinal.mk_le_aleph0_iff]
    refine (Subfield.cardinalMk_closure_le_max _).trans (max_le ?_ le_rfl)
    exact Cardinal.mk_le_aleph0_iff.2 (Set.countable_range _).to_subtype
  haveI : Countable V₀ := by
    refine Function.Injective.countable
      (f := fun x : V₀ => (⟨algebraMap V (FractionRing V) x, x.2⟩ : K₀)) ?_
    intro x y h
    exact Subtype.ext (IsFractionRing.injective V (FractionRing V) (congrArg Subtype.val h))
  haveI : CharZero V₀ := V₀.subtype.charZero
  haveI : IsLocalRing V₀ := traceSubring_isLocalRing K₀
  haveI : IsPrincipalIdealRing V₀ := traceSubring_principal K₀
  let φ₀ : A →+* V₀ := φ.codRestrict V₀ hmem
  have hcomp : V₀.subtype.comp φ₀ = φ := by ext; rfl
  haveI : IsLocalHom (V₀.subtype.comp φ₀) := by rw [hcomp]; exact hφ
  haveI : IsLocalHom φ₀ := isLocalHom_of_comp φ₀ V₀.subtype
  haveI : IsDiscreteValuationRing V₀ := by
    refine { not_a_field' := ?_ }
    intro hbot
    have hnu : ¬ IsUnit (φ₀ a) := fun h =>
      (IsLocalRing.mem_maximalIdeal a).1 ha (IsLocalHom.map_nonunit a h)
    have : φ₀ a ∈ maximalIdeal V₀ := hnu
    rw [hbot, Ideal.mem_bot] at this
    exact hφa (congrArg Subtype.val this)
  obtain ⟨T, i, hi, hil, hcard⟩ := GlobalTheory.CountableCompletion.exists_cdvr_mk_le_continuum V₀ inferInstance
  refine ⟨T, i.comp φ₀, inferInstance, ?_, hcard⟩
  ext x
  simp only [RingHom.mem_ker, RingHom.comp_apply]
  rw [map_eq_zero_iff i hi]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

end GlobalTheory.SmallDVR
