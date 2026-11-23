import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.LatTransfer

open GlobalTheory.UnitLemma

theorem avg_of_const {H : Type} [Group H] (u : H → ℂ) (c : ℂ) (hu : ∀ h, u h = c) : avg u = c := by
  have hs : rStab u = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro k x
    rw [hu, hu]
  have hi : (rStab u).index = 1 := by rw [hs, Subgroup.index_top]
  have hc : Nat.card (H ⧸ rStab u) = 1 := hi
  obtain ⟨x0, hx0⟩ := Nat.card_eq_one_iff_exists.1 hc
  unfold avg
  rw [hi, finsum_eq_single _ x0 (fun y hy => absurd (hx0 y) hy), hu]
  simp

theorem mulLat_eq_self_iff {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (u : Aˣ)
    (L : Submodule O A) : mulLat O (u : A) L = L ↔ u ∈ stabLat O L := by
  constructor
  · intro h
    show ∀ y, y ∈ L ↔ (u : A) * y ∈ L
    intro y
    have := Orbit.mem_mulLat u L ((u : A) * y)
    rw [h, Units.inv_mul_cancel_left] at this
    exact this.symm
  · intro hu
    ext y
    rw [Orbit.mem_mulLat]
    have := hu (((u⁻¹ : Aˣ) : A) * y)
    rw [Units.mul_inv_cancel_left] at this
    exact this

theorem mulLat_mul {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (s t : Aˣ)
    (L : Submodule O A) : mulLat O ((s * t : Aˣ) : A) L = mulLat O (s : A) (mulLat O (t : A) L) := by
  ext y
  rw [Orbit.mem_mulLat, Orbit.mem_mulLat, Orbit.mem_mulLat, _root_.mul_inv_rev, Units.val_mul, mul_assoc]

theorem cast_finsum {α : Type*} (u : α → ℚ) : ((∑ᶠ a, u a : ℚ) : ℂ) = ∑ᶠ a, ((u a : ℚ) : ℂ) := by
  by_cases h : (Function.support u).Finite
  · exact map_finsum (Rat.castHom ℂ) h
  · have e : Function.support (fun a => ((u a : ℚ) : ℂ)) = Function.support u :=
      Function.support_comp_eq (fun r : ℚ => (r : ℂ)) (fun {x} => Rat.cast_eq_zero) u
    have h' : ¬ (Function.support fun a => ((u a : ℚ) : ℂ)).Finite := by rw [e]; exact h
    rw [finsum_of_infinite_support h, finsum_of_infinite_support h', Rat.cast_zero]

theorem twCent_left {G : Type} [Group G] (θ : G →* G) (δ : G) {t : G} (ht : t ∈ twCent θ δ) (k y : G) :
    (t * y * k)⁻¹ * δ * θ (t * y * k) = k⁻¹ * (y⁻¹ * δ * θ y) * θ k := by
  have h : t * δ = δ * θ t := ht
  have h2 : t⁻¹ * δ * θ t = δ := by rw [mul_assoc, ← h]; group
  calc (t * y * k)⁻¹ * δ * θ (t * y * k) = k⁻¹ * (y⁻¹ * (t⁻¹ * δ * θ t) * θ y) * θ k := by
        simp only [map_mul]; group
    _ = _ := by rw [h2]

theorem twOrb_eq_N : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (x : B.A) (G : Type) [Group G] [TopologicalSpace G] (θ : G →* G) (Kg : Subgroup G) (δ : G) (f : G → ℂ) (φ : twCent θ δ ≃* B.T) (Λ : G → Submodule K.O B.A), (∀ k ∈ Kg, ∀ y, f (k⁻¹ * y * θ k) = f y) → (∀ y, f y = 0 ∨ f y = 1) → (∀ t : twCent θ δ, ((t : G) ∈ cptPart (twCent θ δ) ↔ (((φ t : B.T) : B.Aˣ)) ∈ GlobalTheory.UnitLemma.intUnits K.O B.A)) → (∀ q q' : G, Λ q = Λ q' ↔ q⁻¹ * q' ∈ Kg) → (∀ (t : twCent θ δ) (q : G), Λ ((t : G) * q) = GlobalTheory.UnitLemma.mulLat K.O ((((φ t : B.T) : B.Aˣ)) : B.A) (Λ q)) → (∀ q, Λ q ∈ B.X x ↔ f (q⁻¹ * δ * θ q) = 1) → (∀ L ∈ B.X x, ∃ q, Λ q = L) → twOrb θ Kg δ f = ((B.N x : ℚ) : ℂ) := by
  intro K B x G _ _ θ Kg δ f φ Λ hf h01 hcpt hΛK hΛT hΛX hsurj

  have havg : ∀ q : G, avg (fun k : Kg => f ((q * k)⁻¹ * δ * θ (q * k))) = f (q⁻¹ * δ * θ q) := by
    intro q
    refine avg_of_const _ _ fun k => ?_
    rw [← hf k k.2 (q⁻¹ * δ * θ q)]
    congr 1
    simp only [map_mul]
    group

  let ψ : twCent θ δ →* B.Aˣ := B.T.subtype.comp φ.toMonoidHom
  have hψ : ∀ t, ψ t = ((φ t : B.T) : B.Aˣ) := fun t => rfl
  have hle : cptPart (twCent θ δ) ≤ twCent θ δ := by
    unfold cptPart
    rw [Subgroup.closure_le]
    exact fun t ht => ht.1
  have hidx : ∀ q : G, (twCent θ δ ⊓ Kg.map (MulAut.conj q).toMonoidHom).relIndex (cptPart (twCent θ δ)) =
      (stabLat K.O (Λ q) ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) := by
    intro q
    rw [← Subgroup.relIndex_subgroupOf hle]
    have e1 : (twCent θ δ ⊓ Kg.map (MulAut.conj q).toMonoidHom).subgroupOf (twCent θ δ) =
        (stabLat K.O (Λ q) ⊓ B.T).comap ψ := by
      ext t
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_inf, Subgroup.mem_inf, hψ]
      simp only [t.2, (φ t).2, true_and, and_true]
      rw [← mulLat_eq_self_iff, ← hΛT, eq_comm, hΛK, Subgroup.mem_map]
      constructor
      · rintro ⟨k, hk, hkt⟩
        have : (t : G) = q * k * q⁻¹ := by rw [← hkt]; rfl
        rw [this]
        simpa [mul_assoc] using hk
      · intro h
        refine ⟨q⁻¹ * (t * q), h, ?_⟩
        show q * (q⁻¹ * (t * q)) * q⁻¹ = t
        group
    have e2 : (cptPart (twCent θ δ)).subgroupOf (twCent θ δ) = (intUnits K.O B.A ⊓ B.T).comap ψ := by
      ext t
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_inf, hψ, hcpt t]
      simp only [(φ t).2, and_true]
    rw [e1, e2, Subgroup.relIndex_comap, Subgroup.map_comap_eq_self]
    intro y hy
    exact ⟨φ.symm ⟨y, hy.2⟩, by rw [hψ]; simp⟩

  have hdc : ∀ t ∈ twCent θ δ, ∀ k ∈ Kg, ∀ q : G, f ((t * q * k)⁻¹ * δ * θ (t * q * k)) = f (q⁻¹ * δ * θ q) := by
    intro t ht k hk q
    rw [twCent_left θ δ ht k q, hf k hk]
  let r : B.X x → B.X x → Prop := fun L M => ∃ t ∈ B.T, (M : Submodule K.O B.A) = mulLat K.O (t : B.A) L
  have hr : Equivalence r := by
    refine ⟨fun L => ⟨1, B.T.one_mem, ((mulLat_eq_self_iff 1 L.1).2 (stabLat K.O L.1).one_mem).symm⟩, ?_, ?_⟩
    · rintro L M ⟨t, ht, h⟩
      refine ⟨t⁻¹, B.T.inv_mem ht, ?_⟩
      rw [h, ← mulLat_mul, inv_mul_cancel]
      exact ((mulLat_eq_self_iff 1 L.1).2 (stabLat K.O L.1).one_mem).symm
    · rintro L M N ⟨t, ht, h⟩ ⟨s, hs, h'⟩
      exact ⟨s * t, B.T.mul_mem hs ht, by rw [h', h, mulLat_mul]⟩
  let S := {d : DoubleCoset.Quotient (twCent θ δ : Set G) (Kg : Set G) //
    f ((Quotient.out d)⁻¹ * δ * θ (Quotient.out d)) = 1}
  let g : S → Orb K.O B.T (B.X x) := fun d => Quot.mk r ⟨Λ (Quotient.out d.1), (hΛX _).2 d.2⟩
  have hg_surj : Function.Surjective g := by
    intro o
    induction o using Quot.ind with
    | mk L =>
      obtain ⟨q, hq⟩ := hsurj L.1 L.2
      obtain ⟨t, k, ht, hk, hout⟩ := DoubleCoset.mk_out_eq_mul (twCent θ δ) Kg q
      have hf1 : f ((Quotient.out (DoubleCoset.mk (twCent θ δ) Kg q))⁻¹ * δ *
          θ (Quotient.out (DoubleCoset.mk (twCent θ δ) Kg q))) = 1 := by
        rw [hout, hdc t ht k hk q]
        exact (hΛX q).1 (hq ▸ L.2)
      refine ⟨⟨DoubleCoset.mk (twCent θ δ) Kg q, hf1⟩, ?_⟩
      refine (Quot.sound ?_).symm
      refine ⟨((φ ⟨t, ht⟩ : B.T) : B.Aˣ), (φ ⟨t, ht⟩).2, ?_⟩
      show Λ (Quotient.out (DoubleCoset.mk (twCent θ δ) Kg q)) = _
      rw [hout, ← hq, ← hΛT ⟨t, ht⟩ q]
      refine ((hΛK _ _).2 ?_).symm
      simpa [mul_assoc] using hk
  have hg_inj : Function.Injective g := by
    rintro ⟨d1, h1⟩ ⟨d2, h2⟩ h
    obtain ⟨s, hs, hs'⟩ := hr.eqvGen_iff.1 (Quot.eqvGen_exact h)
    apply Subtype.ext
    let t : twCent θ δ := φ.symm ⟨s, hs⟩
    have hts : ((φ t : B.T) : B.Aˣ) = s := by simp [t]
    have h3 : Λ ((t : G) * Quotient.out d1) = Λ (Quotient.out d2) := by
      rw [hΛT, hts]
      exact hs'.symm
    have := (DoubleCoset.eq (twCent θ δ) Kg (Quotient.out d1) (Quotient.out d2)).2
      ⟨t, t.2, (t * Quotient.out d1)⁻¹ * Quotient.out d2, (hΛK _ _).1 h3, by group⟩
    rwa [DoubleCoset.out_eq', DoubleCoset.out_eq'] at this
  let e := Equiv.ofBijective g ⟨hg_inj, hg_surj⟩
  have hN : ((B.N x : ℚ) : ℂ) = ∑ᶠ o : Orb K.O B.T (B.X x), ((Orbit.orbWt B.T (B.X x) o : ℚ) : ℂ) := by
    unfold InvAlg.N
    rw [Orbit.orbSum_eq, cast_finsum]
  rw [hN, ← finsum_comp_equiv e]
  have hw : ∀ s : S, ((Orbit.orbWt B.T (B.X x) (e s) : ℚ) : ℂ) =
      (((stabLat K.O (Λ (Quotient.out s.1)) ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) : ℕ) : ℂ) := by
    intro s
    exact Rat.cast_natCast _
  rw [finsum_congr hw]
  unfold twOrb
  have hsub : (∑ᶠ s : S, (((stabLat K.O (Λ (Quotient.out s.1)) ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) : ℕ) : ℂ)) =
      ∑ᶠ (d : DoubleCoset.Quotient (twCent θ δ : Set G) (Kg : Set G))
        (_ : f ((Quotient.out d)⁻¹ * δ * θ (Quotient.out d)) = 1),
        (((stabLat K.O (Λ (Quotient.out d)) ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) : ℕ) : ℂ) :=
    finsum_subtype_eq_finsum_cond (f := fun d : DoubleCoset.Quotient (twCent θ δ : Set G) (Kg : Set G) =>
      (((stabLat K.O (Λ (Quotient.out d)) ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) : ℕ) : ℂ)) _
  rw [hsub]
  refine finsum_congr fun d => ?_
  rw [havg, hidx, finsum_eq_if]
  rcases h01 ((Quotient.out d)⁻¹ * δ * θ (Quotient.out d)) with h | h
  · rw [h, mul_zero, if_neg (by norm_num)]
  · rw [h, mul_one, if_pos rfl]

end GlobalTheory.LatTransfer
