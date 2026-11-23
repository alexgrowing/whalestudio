import Mathlib
import GroundTheory.ProfiniteCohomology.LocalTateDuality.KummerCup
set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.KummerCup

open CategoryTheory GroundTheory.ProfCoh IntermediateField

attribute [local instance 2000] Rep.hV2

theorem isLocallyConstant_of_right_invariant {G X : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : Subgroup G) (hH : IsOpen (H : Set G)) (φ : G → X)
    (h : ∀ g, ∀ v ∈ H, φ (g * v) = φ g) : IsLocallyConstant φ := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have ho : IsOpen ((fun y => x⁻¹ * y) ⁻¹' (H : Set G)) := hH.preimage (continuous_const_mul x⁻¹)
  have hm : x ∈ (fun y => x⁻¹ * y) ⁻¹' (H : Set G) := by simp [H.one_mem]
  filter_upwards [ho.mem_nhds hm] with y hy
  have := h x _ hy
  simpa using this

section Coh

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [IsDiscreteRep A]

theorem exists_cocycle_of_cochain (n : ℕ) (c : (Fin n → G) → A) (hc : IsLocallyConstant c)
    (hd : (inhomogeneousCochains.d A n).hom c = 0) :
    ∃ x : cocycles A n, cochainOf A (cocycleι A n x) = c := by
  refine ⟨(cochainsComplex A).cyclesMk (mkCochain A c hc) (n + 1) (by simp) ?_, ?_⟩
  · apply cochainOf_injective (A := A)
    exact (cochainOf_d (A := A) _).trans hd
  · exact congrArg (cochainOf A) ((cochainsComplex A).i_cyclesMk _ _ _ _)

theorem cohomologyπ_succ_eq_zero_iff (n : ℕ) (x : cocycles A (n + 1)) :
    cohomologyπ A (n + 1) x = 0 ↔ ∃ w : (Fin n → G) → A, IsLocallyConstant w ∧
      (inhomogeneousCochains.d A n).hom w = cochainOf A (cocycleι A (n + 1) x) := by
  change ((cochainsComplex A).homologyπ (n + 1)).hom x = 0 ↔ _
  rw [homologyπ_eq_zero_iff, CochainComplex.prev_nat_succ]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨cochainOf A w, isLocallyConstant_cochainOf w, ?_⟩
    rw [← cochainOf_d]
    exact congrArg (cochainOf A) hw
  · rintro ⟨w, hw, h⟩
    refine ⟨mkCochain A w hw, ?_⟩
    apply cochainOf_injective (A := A)
    exact (cochainOf_d (A := A) _).trans h

end Coh

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

theorem exists_eq_div_of_cocycle [IsGalois K Ω] (f : (Ω ≃ₐ[K] Ω) → Ωˣ) (hf : IsLocallyConstant f)
    (hc : ∀ g h, f (g * h) = galUnitsHom K Ω g (f h) * f g) :
    ∃ t : Ωˣ, ∀ g, f g = galUnitsHom K Ω g t / t := by
  let A := galUnits.{0} K Ω
  let c : (Fin 1 → (Ω ≃ₐ[K] Ω)) → A := fun v => Additive.ofMul (f (v 0))
  have hcl : IsLocallyConstant c :=
    (hf.comp_continuous (continuous_apply 0)).comp (fun u => (Additive.ofMul u : A))
  have hd : (inhomogeneousCochains.d A 1).hom c = 0 := by
    funext v
    rw [inhomogeneousCochains_d_one_apply]
    have e := hc (v 0) (v 1)
    show Additive.ofMul (galUnitsHom K Ω (v 0) (f (v 1))) - Additive.ofMul (f (v 0 * v 1)) +
      Additive.ofMul (f (v 0)) = (0 : Additive Ωˣ)
    rw [e]
    apply Additive.toMul.injective
    simp [toMul_add, toMul_sub]
  obtain ⟨x, hx⟩ := exists_cocycle_of_cochain A 1 c hcl hd
  have h0 : cohomologyπ A 1 x = 0 :=
    (subsingleton_cohomology_one_galUnits (K := K) (L := Ω)).elim _ _
  obtain ⟨w, hw, hwx⟩ := (cohomologyπ_succ_eq_zero_iff A 0 x).1 h0
  refine ⟨Additive.toMul (w Fin.elim0 : Additive Ωˣ), fun g => ?_⟩
  have e := congrFun (hwx.trans hx) (fun _ => g)
  simp only [inhomogeneousCochains.d_hom_apply] at e
  simp at e
  have hw0 : ∀ v : Fin 0 → (Ω ≃ₐ[K] Ω), w v = w Fin.elim0 := fun v => by
    rw [Subsingleton.elim v Fin.elim0]
  simp only [hw0 (fun _ => g), hw0 (Fin.contractNth 0 _ _)] at e
  have e' : (Additive.ofMul (galUnitsHom K Ω g (Additive.toMul (w Fin.elim0 : Additive Ωˣ))) +
      -(w Fin.elim0 : Additive Ωˣ) : Additive Ωˣ) = Additive.ofMul (f g) := e
  have e2 := congrArg (Additive.toMul (α := Ωˣ)) e'
  simp only [toMul_add, toMul_neg, toMul_ofMul] at e2
  rw [← e2, div_eq_mul_inv]
  rfl

theorem natCast_eq_of_pow_eq {N : ℕ} [NeZero N] {ζ : Ω} (hζ : IsPrimitiveRoot ζ N) {a b : ℕ}
    (h : ζ ^ a = ζ ^ b) : (a : ZMod N) = b := by
  have hz : ζ ≠ 0 := hζ.ne_zero (NeZero.ne N)
  let z : Ωˣ := Units.mk0 ζ hz
  have hz' : IsPrimitiveRoot z N := (IsPrimitiveRoot.coe_units_iff).1 hζ
  have e : z ^ a = z ^ b := Units.ext (by simpa [z] using h)
  rw [ZMod.natCast_eq_natCast_iff, hz'.eq_orderOf]
  exact pow_eq_pow_iff_modEq.1 e

theorem exists_cochain_of_lift [IsGalois K Ω] [IsSepClosed Ω] (N : ℕ) [NeZero N] {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ N) (c0 : (Ω ≃ₐ[K] Ω) → ZMod N) (hc0 : ∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ ^ (c0 g).val)
    (ψ : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod N)) (hψ : IsOpen (ψ.ker : Set (Ω ≃ₐ[K] Ω)))
    (T : Ωˣ) (κ : (Ω ≃ₐ[K] Ω) → ZMod N) (hκ : ∀ g : Ω ≃ₐ[K] Ω, g (T : Ω) = ζ ^ (κ g).val * T)
    (b : (Ω ≃ₐ[K] Ω) → Ωˣ) (hb : IsLocallyConstant b) (w : (Ω ≃ₐ[K] Ω) → (Ω ≃ₐ[K] Ω) → ℕ)
    (hw : ∀ g h, (Multiplicative.toAdd (ψ g)).val + (Multiplicative.toAdd (ψ h)).val =
      N * w g h + (Multiplicative.toAdd (ψ (g * h))).val)
    (hbc : ∀ g h : Ω ≃ₐ[K] Ω, g (b h : Ω) * (b g : Ω) = ((T : Ω) ^ N) ^ w g h * (b (g * h) : Ω)) :
    ∃ c : (Ω ≃ₐ[K] Ω) → ZMod N, IsLocallyConstant c ∧ ∀ g h : Ω ≃ₐ[K] Ω,
      c0 g * c h - c (g * h) + c g = κ g * Multiplicative.toAdd (ψ h) := by
  have hN0 : N ≠ 0 := NeZero.ne N
  set p : (Ω ≃ₐ[K] Ω) → ℕ := fun g => (Multiplicative.toAdd (ψ g)).val with hp
  have hplc : IsLocallyConstant p :=
    isLocallyConstant_of_right_invariant ψ.ker hψ p fun g v hv => by
      simp [p, map_mul, MonoidHom.mem_ker.1 hv]
  let γu : (Ω ≃ₐ[K] Ω) → Ωˣ := fun h => T ^ p h * (b h)⁻¹
  have hγlc : IsLocallyConstant γu := (hplc.prodMk hb).comp fun q : ℕ × Ωˣ => T ^ q.1 * q.2⁻¹
  have hγv : ∀ h, (γu h : Ω) = (T : Ω) ^ p h / (b h : Ω) := fun h => by
    simp [γu, div_eq_mul_inv]
  have hγ : ∀ g h : Ω ≃ₐ[K] Ω,
      g (γu h : Ω) * (γu g : Ω) = ζ ^ ((κ g).val * p h) * (γu (g * h) : Ω) := by
    intro g h
    have hbg : g (b h : Ω) ≠ 0 := by simp
    have hbb : (b g : Ω) ≠ 0 := by simp
    have hbgh : (b (g * h) : Ω) ≠ 0 := by simp
    have hT0 : (T : Ω) ≠ 0 := by simp
    rw [hγv, hγv, hγv, map_div₀, map_pow, hκ]
    calc (ζ ^ (κ g).val * (T : Ω)) ^ p h / g (b h : Ω) * ((T : Ω) ^ p g / (b g : Ω))
        = ζ ^ ((κ g).val * p h) * (T : Ω) ^ (p g + p h) / (g (b h : Ω) * (b g : Ω)) := by
          rw [mul_pow, pow_add, ← pow_mul]
          field_simp
      _ = ζ ^ ((κ g).val * p h) * ((T : Ω) ^ (N * w g h) * (T : Ω) ^ p (g * h)) /
            (((T : Ω) ^ N) ^ w g h * (b (g * h) : Ω)) := by
          rw [hbc, show p g + p h = N * w g h + p (g * h) from hw g h, pow_add]
      _ = ζ ^ ((κ g).val * p h) * ((T : Ω) ^ p (g * h) / (b (g * h) : Ω)) := by
          rw [pow_mul (T : Ω) N]
          field_simp
  let f : (Ω ≃ₐ[K] Ω) → Ωˣ := fun g => γu g ^ N
  have hflc : IsLocallyConstant f := hγlc.comp fun x : Ωˣ => x ^ N
  have hζN : ζ ^ N = 1 := hζ.pow_eq_one
  have hfc : ∀ g h, f (g * h) = galUnitsHom K Ω g (f h) * f g := by
    intro g h
    apply Units.ext
    simp only [f, Units.val_mul, Units.val_pow_eq_pow_val, coe_galUnitsHom_apply, map_pow]
    rw [← mul_pow, hγ, mul_pow, ← pow_mul, mul_comm _ N, pow_mul, hζN, one_pow, one_mul]
  obtain ⟨t, ht⟩ := exists_eq_div_of_cocycle f hflc hfc
  have : NeZero ((N : ℕ) : Ω) := hζ.neZero'
  obtain ⟨s, hs⟩ := IsSepClosed.exists_pow_nat_eq (t : Ω) N
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [zero_pow hN0] at hs
    exact t.ne_zero hs.symm
  let su : Ωˣ := Units.mk0 s hs0
  have hsuN : su ^ N = t := Units.ext (by simpa [su] using hs)
  have hslc : IsLocallyConstant fun g : Ω ≃ₐ[K] Ω => galUnitsHom K Ω g su := by
    refine isLocallyConstant_of_right_invariant (MulAction.stabilizer (Ω ≃ₐ[K] Ω) s)
      (isOpen_of_forall_apply_eq_mem _ s fun σ h => h) _ fun g v hv => ?_
    have hv' : v s = s := hv
    apply Units.ext
    simp only [coe_galUnitsHom_apply, su, Units.val_mk0, AlgEquiv.mul_apply, hv']
  let d : (Ω ≃ₐ[K] Ω) → Ωˣ := fun g => γu g * su / galUnitsHom K Ω g su
  have hdlc : IsLocallyConstant d :=
    (hγlc.prodMk hslc).comp fun q : Ωˣ × Ωˣ => q.1 * su / q.2
  have hdN : ∀ g, d g ^ N = 1 := by
    intro g
    have h1 : γu g ^ N = galUnitsHom K Ω g t / t := ht g
    simp only [d, div_pow, mul_pow, h1, hsuN, ← map_pow]
    simp
  have hex : ∀ g, ∃ i : ℕ, i < N ∧ ζ ^ i = (d g : Ω) := fun g =>
    hζ.eq_pow_of_pow_eq_one (by rw [← Units.val_pow_eq_pow_val, hdN, Units.val_one])
  classical
  let F : Ωˣ → ZMod N := fun x =>
    if h : ∃ i : ℕ, i < N ∧ ζ ^ i = (x : Ω) then ((Classical.choose h : ℕ) : ZMod N) else 0
  have hF : ∀ g, ζ ^ (F (d g)).val = (d g : Ω) := by
    intro g
    have hs' := Classical.choose_spec (hex g)
    simp only [F, dif_pos (hex g)]
    rw [ZMod.val_cast_of_lt hs'.1]
    exact hs'.2
  refine ⟨fun g => F (d g), hdlc.comp F, fun g h => ?_⟩
  have hsg : ∀ g : Ω ≃ₐ[K] Ω, g s ≠ 0 := fun g => by simpa using hs0
  have hsg' : ∀ g h : Ω ≃ₐ[K] Ω, g (h s) ≠ 0 := fun g h => by simpa using hs0
  have hdv : ∀ g : Ω ≃ₐ[K] Ω, (d g : Ω) = (γu g : Ω) * s / g s := fun g => by
    simp [d, su, Units.val_div_eq_div_val]
  have hcoc : g (d h : Ω) * (d g : Ω) = ζ ^ ((κ g).val * p h) * (d (g * h) : Ω) := by
    rw [hdv, hdv, hdv, map_div₀, map_mul]
    have h1 := hsg g
    have h2 : g (h s) ≠ 0 := hsg' g h
    calc g (γu h : Ω) * g s / g (h s) * ((γu g : Ω) * s / g s)
        = (g (γu h : Ω) * (γu g : Ω)) * s / g (h s) := by field_simp
      _ = _ := by
          rw [hγ, AlgEquiv.mul_apply]
          field_simp
  rw [← hF h, ← hF g, ← hF (g * h), map_pow, hc0, ← pow_mul, ← pow_add, ← pow_add] at hcoc
  have hz := natCast_eq_of_pow_eq hζ hcoc
  push_cast at hz
  simp only [ZMod.natCast_zmod_val, p] at hz
  linear_combination hz

theorem exists_lift_of_norm [IsSepClosure K Ω] (N : ℕ) [NeZero N]
    (ψ : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod N)) (hψ : IsOpen (ψ.ker : Set (Ω ≃ₐ[K] Ω))) (U : Kˣ)
    (hU : ∃ y : IntermediateField.fixedField ψ.ker, Algebra.norm K y = (U : K)) :
    ∃ b : (Ω ≃ₐ[K] Ω) → Ωˣ, IsLocallyConstant b ∧ ∀ g h : Ω ≃ₐ[K] Ω,
      g (b h : Ω) * (b g : Ω) = (algebraMap K Ω (U : K)) ^
        (((Multiplicative.toAdd (ψ g)).val + (Multiplicative.toAdd (ψ h)).val) / N) *
        (b (g * h) : Ω) := by
  let ψa : (Ω ≃ₐ[K] Ω) → ZMod N := fun g => Multiplicative.toAdd (ψ g)
  have hlc : IsLocallyConstant ψa :=
    isLocallyConstant_of_right_invariant ψ.ker hψ ψa fun g v hv => by
      simp [ψa, map_mul, MonoidHom.mem_ker.1 hv]
  let χ : Additive (Ω ≃ₐ[K] Ω) →ₜ+ QZ :=
    { toFun := fun σ => zmodToQZ N (ψa (Additive.toMul σ))
      map_zero' := by simp [ψa]
      map_add' := fun σ τ => by simp [ψa, toAdd_mul]
      continuous_toFun :=
        ((hlc.comp_continuous continuous_toMul).comp (zmodToQZ N)).continuous }
  have hker : charKer (charAdd χ) = ψ.ker := by
    ext g
    rw [mem_charKer, charAdd_apply, AddEquiv.map_eq_zero_iff, MonoidHom.mem_ker]
    constructor
    · intro h
      have h' : ψa g = 0 := zmodToQZ_injective (h.trans (map_zero _).symm)
      exact h'
    · intro h
      show zmodToQZ N (Multiplicative.toAdd (ψ g)) = 0
      rw [h]
      simp
  have hz : galCupClass K Ω χ U = 0 :=
    (galCupClass_eq_zero_iff_of_isSepClosure χ U).2 (by rw [hker]; exact hU)
  obtain ⟨w, hw, hwc⟩ := exists_cocycle_cupCharClassProf (galUnitsZ K Ω) χ (unitsInvariant K Ω U)
  rw [galCupClass, ← hw, cohomologyπ_two_eq_zero_iff] at hz
  obtain ⟨f, hf, hfc⟩ := hz
  refine ⟨fun g => Additive.toMul (f g : Additive Ωˣ), hf.comp _, fun g h => ?_⟩
  have e := hfc g h
  rw [hwc] at e
  have e1 : charCocycle (charAdd χ) (g, h) = bockInt ψa g h :=
    charCocycle_eq_bockInt ψa (charAdd χ) (fun _ => rfl) g h
  set m : ℕ := ((Multiplicative.toAdd (ψ g)).val + (Multiplicative.toAdd (ψ h)).val) / N with hm
  have e2 : charCocycle (charAdd χ) (![g, h] 0, ![g, h] 1) = (m : ℤ) := e1
  rw [e2] at e
  let B : (Ω ≃ₐ[K] Ω) → Ωˣ := fun g => Additive.toMul (f g : Additive Ωˣ)
  let u : Ωˣ := Units.map (algebraMap K Ω : K →* Ω) U
  have e3 : ((m : ℤ) • Additive.ofMul u : Additive Ωˣ) =
      Additive.ofMul (galUnitsHom K Ω g (B h)) - Additive.ofMul (B (g * h)) +
        Additive.ofMul (B g) := e
  have e4 := congrArg (Additive.toMul (α := Ωˣ)) e3
  simp only [natCast_zsmul, toMul_nsmul, toMul_add, toMul_sub, toMul_ofMul] at e4
  have e5 := congrArg (Units.val) e4
  simp only [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_div_eq_div_val,
    coe_galUnitsHom_apply] at e5
  have hu : (u : Ω) = algebraMap K Ω (U : K) := rfl
  rw [hu] at e5
  show g (B h : Ω) * (B g : Ω) = _ * (B (g * h) : Ω)
  rw [e5]
  have hB : (B (g * h) : Ω) ≠ 0 := Units.ne_zero _
  field_simp

theorem kummerCup_eq_coboundary : ∀ {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (N : ℕ), 0 < N → ∀ ζ : Ω, IsPrimitiveRoot ζ N → ∀ c0 : (Ω ≃ₐ[K] Ω) → ZMod N,
    (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ ^ (c0 g).val) → ∀ ψ : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod N),
    IsOpen (ψ.ker : Set (Ω ≃ₐ[K] Ω)) → ∀ U : Kˣ,
    (∃ y : IntermediateField.fixedField ψ.ker, Algebra.norm K y = (U : K)) →
    ∀ (T : Ω) (κ : (Ω ≃ₐ[K] Ω) → ZMod N), T ^ N = algebraMap K Ω (U : K) →
    (∀ g : Ω ≃ₐ[K] Ω, g T = ζ ^ (κ g).val * T) →
    ∃ c : (Ω ≃ₐ[K] Ω) → ZMod N, IsLocallyConstant c ∧ ∀ g h : Ω ≃ₐ[K] Ω,
      c0 g * c h - c (g * h) + c g = κ g * Multiplicative.toAdd (ψ h) := by
  intro K Ω _ _ _ _ N hN ζ hζ c0 hc0 ψ hψ U hU T κ hTN hκ
  have : NeZero N := ⟨hN.ne'⟩
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  obtain ⟨b, hb, hbc⟩ := exists_lift_of_norm N ψ hψ U hU
  have hT0 : T ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hTN
    exact (map_ne_zero _).2 U.ne_zero hTN.symm
  refine exists_cochain_of_lift N hζ c0 hc0 ψ hψ (Units.mk0 T hT0) κ hκ b hb
    (fun g h => ((Multiplicative.toAdd (ψ g)).val + (Multiplicative.toAdd (ψ h)).val) / N)
    (fun g h => ?_) (fun g h => ?_)
  · rw [map_mul, toAdd_mul, ZMod.val_add]
    exact (Nat.div_add_mod _ _).symm
  · rw [hbc, Units.val_mk0, hTN]

end GlobalTheory.CompanionTheory.KummerCup
