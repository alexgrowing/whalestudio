import Development.EtaleCohomology.EtaleSheaves.SHExistsPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut Polynomial

namespace LateralTheory.E.SHLocPf

def EtClosed {O Ω : Type} [CommRing O] [Field Ω] (ψ : O →+* Ω) : Prop :=
  ∀ (C : Type) [CommRing C] [Algebra O C] [Algebra.Etale O C] (χ : C →+* Ω),
    χ.comp (algebraMap O C) = ψ → ∃ s : C →ₐ[O] O, ψ.comp s.toRingHom = χ

def Build : Prop := ∀ (A : CommRingCat.{0}) [IsLocalRing A],
  ∃ (O : CommRingCat.{0}) (f : A ⟶ O) (Ω : Type) (_ : Field Ω) (_ : IsSepClosed Ω) (ψ : O →+* Ω),
    IE f ∧ Function.Surjective ψ ∧ (∀ a : A, a ∈ IsLocalRing.maximalIdeal A → ψ (f.hom a) = 0) ∧ EtClosed ψ

def Lift : Prop := ∀ (O Ω : Type) [CommRing O] [Field Ω] (ψ : O →+* Ω), EtClosed ψ →
  ∀ p : O[X], p.Monic → ∀ a₀ : O, ψ (p.eval a₀) = 0 → ψ (p.derivative.eval a₀) ≠ 0 →
    ∃ a : O, p.IsRoot a ∧ ψ a = ψ a₀

def Colim : Prop := ∀ (A : CommRingCat.{0}) (Ω : Type) [Field Ω] (ι : A →+* Ω),
  ∃ (O : CommRingCat.{0}) (f : A ⟶ O) (ψ : O →+* Ω), IE f ∧ ψ.comp f.hom = ι ∧ EtClosed ψ

theorem unit_of_etClosed {O Ω : Type} [CommRing O] [Field Ω] (ψ : O →+* Ω) (h : EtClosed ψ)
    (x : O) (hx : ψ x ≠ 0) : IsUnit x := by
  have hu : IsUnit (ψ x) := isUnit_iff_ne_zero.mpr hx
  let χ : Localization.Away x →+* Ω := IsLocalization.Away.lift x hu
  have hχ : χ.comp (algebraMap O (Localization.Away x)) = ψ := IsLocalization.Away.lift_comp x hu
  obtain ⟨s, -⟩ := h (Localization.Away x) χ hχ
  refine IsUnit.of_mul_eq_one (b :=  s (IsLocalization.Away.invSelf x)) ?_
  have e := congrArg s (IsLocalization.Away.mul_invSelf (S := Localization.Away x) x)
  rw [map_mul, map_one, AlgHom.commutes] at e
  simpa using e

theorem etaleClosed_point_lifts_simple_roots_monic : Lift := by
  intro O Ω _ _ ψ hE p hp a₀ h₁ h₂
  letI : Algebra O Ω := ψ.toAlgebra
  let P : StandardEtalePair O := ⟨p, hp, p.derivative, ⟨1, 0, 1, by ring⟩⟩
  have hev : ∀ q : O[X], aeval (ψ a₀) q = ψ (q.eval a₀) := by
    intro q
    rw [Polynomial.aeval_def]; exact Polynomial.eval₂_at_apply (p := q) ψ a₀
  have hM : P.HasMap (ψ a₀) := ⟨by rw [hev]; exact h₁, by rw [hev]; exact isUnit_iff_ne_zero.mpr h₂⟩
  let χ : P.Ring →+* Ω := (P.lift (ψ a₀) hM).toRingHom
  have hχ : χ.comp (algebraMap O P.Ring) = ψ := (P.lift (ψ a₀) hM).comp_algebraMap
  obtain ⟨s, hs⟩ := hE P.Ring χ hχ
  refine ⟨s P.X, ?_, ?_⟩
  · have h0 : aeval P.X P.f = 0 := P.hasMap_X.1
    have h1 := congrArg s h0
    rw [map_zero, ← Polynomial.aeval_algHom_apply] at h1
    rw [Polynomial.IsRoot.def, ← Polynomial.coe_aeval_eq_eval]
    exact h1
  · have := congrArg (fun g => g P.X) hs
    simp only [RingHom.comp_apply] at this
    rw [show ψ (s P.X) = χ P.X from this]
    exact P.lift_X (ψ a₀) hM

theorem build_of (hC : Colim) : Build := by
  intro A _
  let k := IsLocalRing.ResidueField A
  let ι : A →+* SeparableClosure k := (algebraMap k (SeparableClosure k)).comp (IsLocalRing.residue A)
  obtain ⟨O, f, ψ, hIE, hcomp, hE⟩ := hC A (SeparableClosure k) ι
  refine ⟨O, f, SeparableClosure k, inferInstance, inferInstance, ψ, hIE, ?_, ?_, hE⟩
  · intro ω
    have hsep : (minpoly k ω).Separable := Algebra.IsSeparable.isSeparable k ω
    have hmon : (minpoly k ω).Monic := minpoly.monic (Algebra.IsSeparable.isIntegral k ω)
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic
      ((Polynomial.lifts_iff_coeff_lifts _).2 (fun n => IsLocalRing.residue_surjective _)) hmon
    letI : Algebra O (SeparableClosure k) := ψ.toAlgebra
    let P : StandardEtalePair O :=
      ⟨q.map f.hom, hqm.map _, (q.map f.hom).derivative, ⟨1, 0, 1, by ring⟩⟩
    have hev : ∀ r : A[X], aeval ω (r.map f.hom) = aeval ω (r.map (IsLocalRing.residue A)) := by
      intro r
      rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.eval₂_map]
      congr 1
    have hM : P.HasMap ω := by
      refine ⟨?_, ?_⟩
      · change aeval ω (q.map f.hom) = 0
        rw [hev, hq]; exact minpoly.aeval k ω
      · change IsUnit (aeval ω (q.map f.hom).derivative)
        rw [Polynomial.derivative_map, hev, ← Polynomial.derivative_map, hq]
        exact isUnit_iff_ne_zero.mpr (hsep.aeval_derivative_ne_zero (minpoly.aeval k ω))
    let χ : P.Ring →+* SeparableClosure k := (P.lift ω hM).toRingHom
    have hχ : χ.comp (algebraMap O P.Ring) = ψ := (P.lift ω hM).comp_algebraMap
    obtain ⟨s, hs⟩ := hE P.Ring χ hχ
    refine ⟨s P.X, ?_⟩
    have := congrArg (fun g => g P.X) hs
    simp only [RingHom.comp_apply] at this
    rw [show ψ (s P.X) = χ P.X from this]
    exact P.lift_X ω hM
  · intro a ha
    have e : ψ (f.hom a) = ι a := congrArg (fun g => g a) hcomp
    rw [e]
    simp [ι, (IsLocalRing.residue_eq_zero_iff a).2 ha]

theorem SHLoc_of (hB : Build) (hL : Lift) : LateralTheory.E.SHExistsPf.SHLoc := by
  intro A _
  obtain ⟨O, f, Ω, _, _, ψ, hIE, hs, hm, hE⟩ := hB A
  have hU : ∀ x : O, ψ x ≠ 0 → IsUnit x := unit_of_etClosed ψ hE
  have hZ : ∀ x : O, IsUnit x → ψ x ≠ 0 := fun x hx => (hx.map ψ).ne_zero
  have : Nontrivial O := ⟨⟨1, 0, fun h => by simpa using congrArg ψ h⟩⟩
  have : IsLocalRing O := IsLocalRing.of_nonunits_add (by
    intro a b ha hb hab
    have ha' : ψ a = 0 := by by_contra h; exact ha (hU a h)
    have hb' : ψ b = 0 := by by_contra h; exact hb (hU b h)
    exact hZ _ hab (by rw [map_add, ha', hb', add_zero]))
  have hmem : ∀ x : O, x ∈ IsLocalRing.maximalIdeal O ↔ ψ x = 0 := by
    intro x
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact ⟨fun h => by by_contra h'; exact h (hU x h'), fun h hx => hZ x hx h⟩
  have hker : IsLocalRing.maximalIdeal O = RingHom.ker ψ := by
    ext x; rw [hmem, RingHom.mem_ker]
  let e : IsLocalRing.ResidueField O ≃+* Ω :=
    (Ideal.quotEquivOfEq hker).trans (RingHom.quotientKerEquivOfSurjective hs)
  have hSC : IsSepClosed (IsLocalRing.ResidueField O) := by
    refine IsSepClosed.of_exists_root _ (fun p _ hirr hsep => ?_)
    have hd : (p.map (e : IsLocalRing.ResidueField O →+* Ω)).degree ≠ 0 := by
      rw [Polynomial.degree_map]; exact (Polynomial.degree_pos_of_irreducible hirr).ne'
    obtain ⟨y, hy⟩ := IsSepClosed.exists_root _ hd (hsep.map)
    refine ⟨e.symm y, ?_⟩
    apply e.injective
    rw [map_zero, ← hy]
    have h := Polynomial.eval₂_at_apply (p := p) (e : IsLocalRing.ResidueField O →+* Ω) (e.symm y)
    rw [Polynomial.eval_map]
    simpa using h.symm
  have hH : HenselianLocalRing O := {
    is_henselian := by
      intro p hp a₀ h₁ h₂
      obtain ⟨a, ha, ha'⟩ := hL O Ω ψ hE p hp a₀ ((hmem _).1 h₁) (hZ _ h₂)
      exact ⟨a, ha, (hmem _).2 (by rw [map_sub, ha', sub_self])⟩ }
  refine ⟨O, f, hIE, ⟨hH, hSC⟩, ⟨fun a ha => ?_⟩⟩
  by_contra hna
  exact hZ _ ha (hm a ((IsLocalRing.mem_maximalIdeal _).2 hna))

end LateralTheory.E.SHLocPf
