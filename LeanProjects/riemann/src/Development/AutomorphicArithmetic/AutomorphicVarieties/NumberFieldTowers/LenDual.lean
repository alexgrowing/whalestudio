import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.XTwApplyApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.QzInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ZmodToQZ
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.QzSep
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.DualKer

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

private theorem le_dual (l : ℕ) [Fact l.Prime] (N : Type) [AddCommGroup N] [Module ℤ_[l] N] :
    Module.length ℤ_[l] N ≤ Module.length ℤ_[l] (N →ₗ[ℤ_[l]] QZ l) := by
  rw [← WithBot.coe_le_coe, Module.coe_length, Module.coe_length, ← Order.krullDim_orderDual]
  refine Order.krullDim_le_of_strictMono
    (fun p : (Submodule ℤ_[l] N)ᵒᵈ =>
      LinearMap.ker (LinearMap.lcomp ℤ_[l] (QZ l) (OrderDual.ofDual p).subtype)) ?_
  intro a b hab
  change OrderDual.ofDual b < OrderDual.ofDual a at hab
  obtain ⟨hle, m, hmp, hmq⟩ := SetLike.lt_iff_le_and_exists.mp hab
  refine lt_of_le_of_ne ?_ ?_
  · intro φ hφ
    rw [LinearMap.mem_ker] at hφ ⊢
    ext ⟨x, hx⟩
    have h := LinearMap.congr_fun hφ ⟨x, hle hx⟩
    simpa using h
  · intro heq
    have hm0 : (OrderDual.ofDual b).mkQ m ≠ 0 := by
      rwa [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    obtain ⟨ψ, hψ⟩ := qzSep l _ _ hm0
    have hmem : ψ ∘ₗ (OrderDual.ofDual b).mkQ ∈
        LinearMap.ker (LinearMap.lcomp ℤ_[l] (QZ l) (OrderDual.ofDual b).subtype) := by
      rw [LinearMap.mem_ker]
      ext ⟨x, hx⟩
      simp [(Submodule.Quotient.mk_eq_zero _).mpr hx]
    have hmem' := hmem
    simp only at heq
    rw [← heq, LinearMap.mem_ker] at hmem'
    exact hψ (by simpa using LinearMap.congr_fun hmem' ⟨m, hmp⟩)

private theorem exact_dual (l : ℕ) [Fact l.Prime] {N : Type} [AddCommGroup N] [Module ℤ_[l] N]
    (p : Submodule ℤ_[l] N) :
    Function.Exact (LinearMap.lcomp ℤ_[l] (QZ l) p.mkQ) (LinearMap.lcomp ℤ_[l] (QZ l) p.subtype) := by
  rw [LinearMap.exact_iff]
  have h := (dualKer l N (N ⧸ p) p.mkQ).1
  have hq := Submodule.ker_mkQ p
  generalize LinearMap.ker p.mkQ = q at h hq
  subst hq
  exact h.symm

private theorem simple_dual (l : ℕ) [hl : Fact l.Prime]
    (N : Type) [AddCommGroup N] [Module ℤ_[l] N] [hN : IsSimpleModule ℤ_[l] N] :
    IsSimpleModule ℤ_[l] (N →ₗ[ℤ_[l]] QZ l) := by
  haveI : Nontrivial N := IsSimpleModule.nontrivial ℤ_[l] N
  have hnu : (l : ℤ_[l]) ∈ nonunits ℤ_[l] :=
    (IsLocalRing.mem_maximalIdeal _).mp
      (by rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _)
  have hspan : ∀ s : N, s ≠ 0 → ∀ x : N, ∃ c : ℤ_[l], c • s = x := by
    intro s hs x
    have htop : Submodule.span ℤ_[l] {s} = ⊤ :=
      (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left
        (by simpa [Submodule.span_singleton_eq_bot] using hs)
    exact Submodule.mem_span_singleton.mp (htop ▸ Submodule.mem_top)
  have hkill : ∀ s : N, (l : ℤ_[l]) • s = 0 := by
    intro s
    by_contra h
    obtain ⟨c, hc⟩ := hspan _ h s
    have hu : IsUnit (1 - c * (l : ℤ_[l])) :=
      IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ (mul_mem_nonunits_right hnu)
    have h0 : (1 - c * (l : ℤ_[l])) • s = 0 := by
      rw [sub_smul, one_smul, mul_smul, hc, sub_self]
    have hs0 : s = 0 := (hu.smul_eq_zero).mp h0
    exact h (by rw [hs0, smul_zero])
  obtain ⟨s, hs⟩ := exists_ne (0 : N)
  obtain ⟨φ0, hφ0⟩ := qzSep l N s hs
  obtain ⟨ι, hιinj, hιrange, hιsmul⟩ := zmodToQZ l 1
  haveI : Fact (Nat.Prime (l ^ 1)) := ⟨by rw [pow_one]; exact hl.out⟩
  have hrange : ∀ φ : N →ₗ[ℤ_[l]] QZ l, ∃ a, ι a = φ s := by
    intro φ
    refine (hιrange (φ s)).mpr ?_
    rw [pow_one, ← LinearMap.map_smul_of_tower, hkill, map_zero]
  have key : ∀ φ ψ : N →ₗ[ℤ_[l]] QZ l, φ ≠ 0 → ∃ z : ℤ_[l], ψ = z • φ := by
    intro φ ψ hφ
    have hφs : φ s ≠ 0 := by
      intro h
      apply hφ
      ext x
      obtain ⟨c, rfl⟩ := hspan s hs x
      simp [h]
    obtain ⟨a, ha⟩ := hrange φ
    obtain ⟨b, hb⟩ := hrange ψ
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hφs (by rw [← ha, map_zero])
    obtain ⟨k, hk⟩ := ZMod.natCast_zmod_surjective (b * a⁻¹)
    have hb' : b = PadicInt.toZModPow 1 (k : ℤ_[l]) * a := by
      rw [map_natCast, hk, inv_mul_cancel_right₀ ha0]
    refine ⟨(k : ℤ_[l]), ?_⟩
    ext x
    obtain ⟨c, rfl⟩ := hspan s hs x
    rw [map_smul, LinearMap.smul_apply, map_smul, ← hb, ← ha, hb', hιsmul, smul_comm]
  haveI : Nontrivial (N →ₗ[ℤ_[l]] QZ l) := ⟨⟨φ0, 0, fun h => hφ0 (by rw [h]; rfl)⟩⟩
  refine { eq_bot_or_eq_top := fun P => ?_ }
  by_cases h : P = ⊥
  · exact Or.inl h
  · right
    obtain ⟨φ, hφP, hφ0'⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    rw [eq_top_iff]
    intro ψ _
    obtain ⟨z, rfl⟩ := key φ ψ hφ0'
    exact P.smul_mem z hφP

theorem UpperTheory.V.Tower.lenDual :
    ∀ (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M], Module.length ℤ_[l] (M →ₗ[ℤ_[l]] QZ l) = Module.length ℤ_[l] M := by
  intro l _ M _ _
  by_cases hM : IsFiniteLength ℤ_[l] M
  · induction hM with
    | @of_subsingleton M' _ _ _ =>
      haveI : Subsingleton (M' →ₗ[ℤ_[l]] QZ l) :=
        ⟨fun f g => LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
      simp [Module.length_eq_zero]
    | @of_simple_quotient M' _ _ N _ _ ih =>
      have hS := simple_dual l (M' ⧸ N)
      have e1 := Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype
        N.mkQ_surjective (LinearMap.exact_subtype_mkQ N)
      have e2 := Module.length_eq_add_of_exact (LinearMap.lcomp ℤ_[l] (QZ l) N.mkQ)
        (LinearMap.lcomp ℤ_[l] (QZ l) N.subtype)
        (fun f g h => by
          ext x
          exact LinearMap.congr_fun h x)
        ((dualKer l M' M' (LinearMap.id)).2 N) (exact_dual l N)
      rw [e1, e2, ih, Module.length_eq_one (R := ℤ_[l]) (M := M' ⧸ N),
        Module.length_eq_one (R := ℤ_[l]) (M := (M' ⧸ N) →ₗ[ℤ_[l]] QZ l), add_comm]
  · have h1 : Module.length ℤ_[l] M = ⊤ := by
      rw [← not_ne_iff, Module.length_ne_top_iff]
      exact hM
    have h2 := le_dual l M
    rw [h1, top_le_iff] at h2
    rw [h1, h2]
