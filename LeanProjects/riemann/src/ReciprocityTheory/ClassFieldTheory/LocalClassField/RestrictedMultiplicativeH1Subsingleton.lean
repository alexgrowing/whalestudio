import Mathlib
import ReciprocityTheory.NeutralLocalFields.Duality
import ReciprocityTheory.GroupCohomology.InfRes
import ReciprocityTheory.GroupCohomology.FiveTerm
import ReciprocityTheory.ClassFieldTheory.LocalClassField.KbarRepContAction

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1

theorem exists_units_of_cocycle {K L : Type*} [Field K] [Field L] [Algebra K L] (H : Subgroup (L ≃ₐ[K] L))
    (f : H → Lˣ) (E : IntermediateField K L) [FiniteDimensional K E]
    (hE : ∀ h : H, (h : L ≃ₐ[K] L) ∈ E.fixingSubgroup → f h = 1)
    (hc : ∀ g h : H, f (g * h) = f g * Units.map ((g : L ≃ₐ[K] L) : L →* L) (f h)) :
    ∃ β : Lˣ, ∀ h : H, f h = Units.map ((h : L ≃ₐ[K] L) : L →* L) β / β := by
  classical

  let r : H → (E →ₐ[K] L) := fun h => ((h : L ≃ₐ[K] L) : L →ₐ[K] L).comp E.val
  have hr : ∀ (h : H) (x : E), r h x = (h : L ≃ₐ[K] L) (x : L) := fun _ _ => rfl
  have hfr : ∀ g h : H, r g = r h → f g = f h := by
    intro g h hgh
    have hmem : ((g⁻¹ * h : H) : L ≃ₐ[K] L) ∈ E.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have h1 : (g : L ≃ₐ[K] L) x = (h : L ≃ₐ[K] L) x := DFunLike.congr_fun hgh ⟨x, hx⟩
      show ((g : L ≃ₐ[K] L)⁻¹ * (h : L ≃ₐ[K] L)) x = x
      rw [AlgEquiv.mul_apply, ← h1]
      exact (g : L ≃ₐ[K] L).symm_apply_apply x
    have h2 := hc g (g⁻¹ * h)
    rw [mul_inv_cancel_left, hE _ hmem, map_one, mul_one] at h2
    exact h2.symm
  let S := Set.range r
  have : Finite (E →ₐ[K] L) := inferInstance
  let _ : Fintype S := Fintype.ofFinite S
  have hrep : ∀ s : S, ∃ h : H, r h = s.1 := fun s => s.2
  choose rep hrep using hrep
  let a : S → L := fun s => (f (rep s) : L)
  have hli : LinearIndependent L (fun s : S => ((s.1 : E →* L) : E → L)) := by
    refine (linearIndependent_monoidHom E L).comp (fun s : S => (s.1 : E →* L)) ?_
    intro s t hst
    apply Subtype.ext
    apply AlgHom.ext
    intro x
    exact DFunLike.congr_fun hst x
  have hex : ∃ c : E, ∑ s : S, a s * s.1 c ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 : ∑ s : S, a s • ((s.1 : E →* L) : E → L) = 0 := by
      funext c
      rw [Finset.sum_apply]
      exact hcon c
    have := Fintype.linearIndependent_iff.1 hli a h0 ⟨r 1, 1, rfl⟩
    exact (f (rep ⟨r 1, 1, rfl⟩)).ne_zero this
  obtain ⟨c, hcne⟩ := hex
  set b : L := ∑ s : S, a s * s.1 c with hb
  have key : ∀ h : H, b = f h * (h : L ≃ₐ[K] L) b := by
    intro h
    let m : S → S := fun s => ⟨r (h * rep s), _, rfl⟩
    have hm1 : ∀ (s : S) (x : E), (m s).1 x = (h : L ≃ₐ[K] L) (s.1 x) := by
      intro s x
      show r (h * rep s) x = _
      rw [← hrep s, hr, hr]
      rfl
    have hminj : Function.Injective m := by
      intro s t hst
      apply Subtype.ext
      apply AlgHom.ext
      intro x
      apply (h : L ≃ₐ[K] L).injective
      rw [← hm1, ← hm1, hst]
    have hmbij : Function.Bijective m := Finite.injective_iff_bijective.1 hminj
    have hma : ∀ s, a (m s) = f h * (h : L ≃ₐ[K] L) (a s) := by
      intro s
      show (f (rep (m s)) : L) = _
      rw [hfr (rep (m s)) (h * rep s) (hrep (m s)), hc]
      rfl
    calc b = ∑ s, a (m s) * (m s).1 c := (hmbij.sum_comp (fun s => a s * s.1 c)).symm
      _ = f h * (h : L ≃ₐ[K] L) b := by
        rw [hb, map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [hma, hm1, map_mul, mul_assoc]
  refine ⟨(Units.mk0 b hcne)⁻¹, fun h => ?_⟩
  apply Units.ext
  have hb' : (h : L ≃ₐ[K] L) b ≠ 0 := by
    simpa using hcne
  have e1 : ((Units.map ((h : L ≃ₐ[K] L) : L →* L) (Units.mk0 b hcne)⁻¹ / (Units.mk0 b hcne)⁻¹ : Lˣ) : L)
      = ((h : L ≃ₐ[K] L) b)⁻¹ * b := by
    rw [map_inv, div_inv_eq_mul, Units.val_mul, Units.val_inv_eq_inv_val]
    rfl
  rw [e1]
  field_simp
  exact (key h).symm

theorem exists_units_of_continuous_cocycle {K L : Type*} [Field K] [Field L] [Algebra K L]
    (H : Subgroup (L ≃ₐ[K] L)) {X : Type*} [TopologicalSpace X] [DiscreteTopology X] (e : X ≃ Lˣ)
    (f : H → X) (hf : Continuous f)
    (hc : ∀ g h : H, e (f (g * h)) = e (f g) * Units.map ((g : L ≃ₐ[K] L) : L →* L) (e (f h))) :
    ∃ β : Lˣ, ∀ h : H, e (f h) = Units.map ((h : L ≃ₐ[K] L) : L →* L) β / β := by
  have h1 : e (f 1) = 1 := by
    have h := hc 1 1
    rw [mul_one] at h
    have h' : Units.map (((1 : H) : L ≃ₐ[K] L) : L →* L) (e (f 1)) = e (f 1) := Units.ext rfl
    rw [h'] at h
    exact (left_eq_mul.1 h)
  have hopen : IsOpen (f ⁻¹' {f 1}) := (isOpen_discrete _).preimage hf
  obtain ⟨V, hV, hVf⟩ := isOpen_induced_iff.1 hopen
  have h1V : (1 : L ≃ₐ[K] L) ∈ V := by
    have : (1 : H) ∈ Subtype.val ⁻¹' V := by rw [hVf]; rfl
    exact this
  obtain ⟨E, hfin, hEV⟩ := (krullTopology_mem_nhds_one_iff K L V).1 (hV.mem_nhds h1V)
  refine exists_units_of_cocycle H (fun h => e (f h)) E (fun h hh => ?_) hc
  have : h ∈ Subtype.val ⁻¹' V := hEV hh
  rw [hVf] at this
  have h2 : f h = f 1 := this
  show e (f h) = 1
  rw [h2, h1]

section Padic

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem kbar_cocycle_subgroup (H : Subgroup (GK p K)) (f : H → KbarMult p) (hf : Continuous f)
    (hc : ∀ g h : H, f (g * h) = f g + kbarRep p K g (f h)) :
    ∃ m : KbarMult p, ∀ h : H, f h = kbarRep p K h m - m := by
  obtain ⟨β, hβ⟩ := exists_units_of_continuous_cocycle H
    (X := KbarMult p) (Additive.toMul : Additive (PadicAlgCl p)ˣ ≃ (PadicAlgCl p)ˣ) f hf
    (fun g h => congrArg (Additive.toMul : Additive (PadicAlgCl p)ˣ → (PadicAlgCl p)ˣ) (hc g h))
  exact ⟨(Additive.ofMul β : Additive (PadicAlgCl p)ˣ), fun h =>
    congrArg (Additive.ofMul : (PadicAlgCl p)ˣ → Additive (PadicAlgCl p)ˣ) (hβ h)⟩

theorem kbar_cocycle (f : GK p K → KbarMult p) (hf : Continuous f)
    (hc : ∀ g h, f (g * h) = f g + kbarRep p K g (f h)) :
    ∃ m : KbarMult p, ∀ h, f h = kbarRep p K h m - m := by
  obtain ⟨m, hm⟩ := kbar_cocycle_subgroup p K ⊤ (fun h => f h.1) (hf.comp continuous_subtype_val)
    (fun g h => hc g.1 h.1)
  exact ⟨m, fun h => hm ⟨h, Subgroup.mem_top h⟩⟩

theorem h1_kbarRep_subsingleton : Subsingleton (H1 (kbarRep p K)) := by
  rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
  rintro ⟨z, hz⟩ -
  rw [Submodule.mem_comap]
  show z ∈ Bd1 _
  rw [mem_contCoboundaries1]
  exact kbar_cocycle p K z hz.1 hz.2

end Padic

section TRep

open ReciprocityTheory.Coh ReciprocityTheory.Coh.InflationRestrictionInvariants

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem restricted_multiplicative_h1_subsingleton (H : Subgroup (GK p K)) :
    Subsingleton (((kbarT p K).resSub H).H 1) := by
  refine ⟨fun x y => ?_⟩
  have h0 : ∀ x : ((kbarT p K).resSub H).H 1, x = 0 := by
    intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [mk_eq_zero_iff, mem_oneCoboundaries_iff]
    have hz : ((kbarT p K).resSub H).coch.d 1 z.1 = 0 := (memZ z.1).1 z.2
    exact kbar_cocycle_subgroup p K H (fun h => z.1.1 (e1 h))
      (Continuous.comp z.1.2 (continuous_pi fun _ => continuous_id))
      ((wach_d1_eq_zero_iff _ z.1).1 hz)
  rw [h0 x, h0 y]

theorem multiplicative_cochain_h1_subsingleton : Subsingleton ((kbarT p K).H 1) := by
  refine ⟨fun x y => ?_⟩
  have h0 : ∀ x : (kbarT p K).H 1, x = 0 := by
    intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [mk_eq_zero_iff, mem_oneCoboundaries_iff]
    have hz : (kbarT p K).coch.d 1 z.1 = 0 := (memZ z.1).1 z.2
    exact kbar_cocycle p K (fun h => z.1.1 (e1 h))
      (Continuous.comp z.1.2 (continuous_pi fun _ => continuous_id))
      ((wach_d1_eq_zero_iff _ z.1).1 hz)
  rw [h0 x, h0 y]

theorem quotient_multiplicative_h1_subsingleton (N : Subgroup (GK p K)) [N.Normal] (Q : TRep ℤ (GK p K ⧸ N))
    (P : Pair Q (kbarT p K)) (hP : IsInvRep (kbarT p K) N Q P) : Subsingleton (Q.H 1) :=
  have := multiplicative_cochain_h1_subsingleton p K
  (inf_inj (kbarT p K) N Q P hP).subsingleton

theorem multiplicative_inflation_h2_injective (N : Subgroup (GK p K)) [N.Normal] (hN : IsClosed (N : Set (GK p K)))
    (Q : TRep ℤ (GK p K ⧸ N)) (P : Pair Q (kbarT p K)) (hP : IsInvRep (kbarT p K) N Q P) :
    Function.Injective (P.hom.H 2) := by
  have hint : Algebra.IsIntegral K (PadicAlgCl p) := Algebra.IsIntegral.tower_top (R := ℚ_[p])
  have hs := restricted_multiplicative_h1_subsingleton p K N
  obtain ⟨tg, -, hex⟩ := fiveTerm_holds ℤ (GK p K) (kbarT p K) N hN Q P hP ⊤
    (fun x => ⟨fun _ s c _ _ => Subsingleton.elim _ _, fun _ => Submodule.mem_top⟩)
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨x, rfl⟩ := (hex y).1 hy
  have hx : x = 0 := Subsingleton.elim _ _
  rw [hx, map_zero]

end TRep

end ReciprocityTheory.DiscreteGroups.LocalClassField
