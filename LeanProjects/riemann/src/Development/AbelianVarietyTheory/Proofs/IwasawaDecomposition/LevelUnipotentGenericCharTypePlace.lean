import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DatVtEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdMaximalCompactReductionPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypePlaceLevelPlacesDistinctUnderlyingStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSplitPlaceComponentHeckeCharResidueStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceResidueMapUnitCharacterStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdFrameLevelCharacterAtTypePlaceEqStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TypeLevelUni

@[reducible] def unitsDiv : DivisibleBy (Additive ℂˣ) ℤ where
  div a n := if n = 0 then 0 else
    Additive.ofMul (Units.mk0 (Complex.exp (Complex.log ((Additive.toMul a : ℂˣ) : ℂ) / n)) (Complex.exp_ne_zero _))
  div_zero a := if_pos rfl
  div_cancel {n} a hn := by
    rw [if_neg hn]
    apply Additive.toMul.injective
    rw [toMul_zsmul, toMul_ofMul]
    ext
    rw [Units.val_zpow_eq_zpow_val, Units.val_mk0, ← Complex.exp_int_mul,
      mul_div_cancel₀ _ (Int.cast_ne_zero.mpr hn), Complex.exp_log (Units.ne_zero _)]

def charUnit {A : Type} [AddCommGroup A] (ψ : AddChar A ℂ) (x : A) : ℂˣ :=
  ⟨ψ x, ψ (-x), by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one],
    by rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]⟩

theorem addChar_extend {K : Type} [Ring K] (S : Subring K) (ψ : AddChar S ℂ) :
    ∃ ψ₀ : AddChar K ℂ, ∀ x : S, ψ₀ x = ψ x := by
  let _ := unitsDiv
  let g : S →ₗ[ℤ] Additive ℂˣ := AddMonoidHom.toIntLinearMap
    { toFun := fun x => Additive.ofMul (charUnit ψ x)
      map_zero' := by
        apply Additive.toMul.injective
        ext
        simp [charUnit, AddChar.map_zero_eq_one]
      map_add' := fun x y => by
        apply Additive.toMul.injective
        ext
        simp [charUnit, AddChar.map_add_eq_mul] }
  let f : S →ₗ[ℤ] K := (S.subtype : S →+* K).toAddMonoidHom.toIntLinearMap
  obtain ⟨h, hh⟩ := (Module.Baer.of_divisible (Additive ℂˣ)).extension_property f Subtype.val_injective g
  refine ⟨{ toFun := fun x => ((Additive.toMul (h x) : ℂˣ) : ℂ)
            map_zero_eq_one' := by simp
            map_add_eq_mul' := fun x y => by simp [map_add] }, fun x => ?_⟩
  have e := congrArg (fun φ => ((Additive.toMul (φ x) : ℂˣ) : ℂ)) hh
  simpa [f, g, charUnit] using e

theorem exists_localAddChar_lifting_residueChar : ∀ (D : D7) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (φ : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* kP s.w), Function.Surjective φ → (∀ x, φ x = 0 ↔ Valued.v (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) < 1) → ∀ ψ' : AddChar (kP s.w) ℂ, ψ' ≠ 1 → ∃ ψ₀ : AddChar (s.v.adicCompletion (maximalRealSubfield D.host.E)) ℂ, NG.IsPsi0 s ψ₀ ∧ ∀ x : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E), ψ₀ (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) = ψ' (φ x) := by
  intro D s φ hφs hφ0 ψ' hne
  obtain ⟨ψ₀, h⟩ := addChar_extend (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)).toSubring
    (ψ'.compAddMonoidHom φ.toAddMonoidHom)
  refine ⟨ψ₀, ⟨fun x hx => ?_, ?_⟩, fun x => h x⟩
  · have hx1 : x ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hx.le
    have e1 := h ⟨x, hx1⟩
    have e2 : φ ⟨x, hx1⟩ = 0 := (hφ0 ⟨x, hx1⟩).2 hx
    rw [show ψ₀ x = ψ₀ ((⟨x, hx1⟩ : (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)).toSubring) :
      s.v.adicCompletion (maximalRealSubfield D.host.E)) from rfl, e1]
    show ψ' (φ ⟨x, hx1⟩) = 1
    rw [e2, AddChar.map_zero_eq_one]
  · obtain ⟨y, hy⟩ : ∃ y, ψ' y ≠ 1 := by
      by_contra hc
      push_neg at hc
      apply hne
      ext y
      rw [hc y, AddChar.one_apply]
    obtain ⟨x, rfl⟩ := hφs y
    refine ⟨x, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 x.2, ?_⟩
    have e1 := h x
    rw [show ψ₀ (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) =
      ψ₀ ((x : (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)).toSubring) :
        s.v.adicCompletion (maximalRealSubfield D.host.E)) from rfl, e1]
    exact hy

theorem levelUni_typePlace : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → (∀ PP, PP ∈ L.Pg ↔ ∃ k v, PP = D.naut.plGw k v) → ∀ (i : Fin D.R.m) (t : T) (hr : D.R.r ≤ D.R.nV) (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ), IsGenericPsi L.Pg ψ → ∀ s : ReciprocityTheory.Aut.SplitPlace D.host.E, s.w ∈ L.Pg → ∃ (ψ₀ : AddChar (s.v.adicCompletion (maximalRealSubfield D.host.E)) ℂ) (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), NG.IsPsi0 s ψ₀ ∧ NG.IsCompAt (L.C.mu0 i * L.xiH t) s ξ ∧ NG.LevelUni (stdJ (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t))) (stdX (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t))) s D.R.r ψ₀ ξ := by
  intro D T L μ0 hL hPg i t hr ψ hψ s hs
  obtain ⟨-, -, -, h4⟩ := GlobalTheory.T.stdMaximalCompact_reduction_properties D D.R.nV
  obtain ⟨φ, hφs, hφ0, hφa, hφk⟩ := h4 s
  obtain ⟨hoffG, hoffQ, -, hunr⟩ := GlobalTheory.T.typePlace_levelPlaces_distinct_underlying D T L μ0 hL hPg t s hs
  let ψ' : AddChar (kP s.w) ℂ := (ψ s.w).compAddMonoidHom (negAddMonoidHom)
  have hne : ψ' ≠ 1 := by
    intro h1
    apply hψ s.w hs
    ext y
    have := congrArg (fun f : AddChar (kP s.w) ℂ => f (-y)) h1
    simpa [ψ'] using this
  obtain ⟨ψ₀, hP0, hψ₀⟩ := exists_localAddChar_lifting_residueChar D s φ hφs hφ0 ψ' hne
  have hres : IsRes (L.C.mu0 i * L.xiH t) s.w (L.chi ((i : ℕ) + 1) s.w)⁻¹ := by
    intro a k u hk hu
    have h1 := hL.chi i s.w hs a k u hk hu
    have ha : a ∉ s.w.asIdeal := by
      intro hm
      have : (u : kP s.w) = 0 := by rw [hu]; exact Ideal.Quotient.eq_zero_iff_mem.2 hm
      exact u.ne_zero this
    have hunit : IsUnitAt s.w (atFin s.w k) := by
      have e := GlobalTheory.ChainOnto.TameRes.val_alg s.w (k : D.host.E)
      show Valued.v (algebraMap D.host.E (s.w.adicCompletion D.host.E) (k : D.host.E)) = 1
      rw [e, hk]
      exact GlobalTheory.ChainOnto.TameRes.valuation_eq_one_of_not_mem s.w a ha
    have h2 : (L.xiH t).locK s.w k = 1 := hunr _ hunit
    have e : (L.C.mu0 i * L.xiH t).locK s.w k = (L.C.mu0 i).locK s.w k * (L.xiH t).locK s.w k := rfl
    rw [e, h2, mul_one]
    exact h1
  obtain ⟨ξ, hξc, hξr⟩ := GlobalTheory.T.exists_splitPlaceComponent_heckeChar_residue D s φ hφs hφ0 hφa _ _ hres
  refine ⟨ψ₀, ξ, hP0, hξc, ⟨GlobalTheory.T.split_place_residue_map_unit_character D hr L.Pg (L.Q t) ψ (L.chi ((i : ℕ) + 1)) (L.xiR t) s φ hφ0 hφk hs hoffG hoffQ, ?_⟩⟩
  intro κ h hκ u hu
  refine GlobalTheory.T.stdFrameLevelCharacter_at_typePlace_eq D hr L.Pg (L.Q t) ψ (L.chi ((i : ℕ) + 1)) (L.xiR t) s φ hφ0 hφk hs hoffG hoffQ ψ₀ ξ ?_ hξr κ h hκ u hu
  intro x
  rw [hψ₀ x]
  rfl

end GlobalTheory.TypeLevelUni

end
