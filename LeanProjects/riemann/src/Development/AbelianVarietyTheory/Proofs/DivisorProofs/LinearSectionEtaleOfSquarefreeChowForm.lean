import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqIsoSpecComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPtOfMemConeOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowFormZeroSetExtensionFieldIffCommonConeZeroStatement

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort
open GlobalTheory.HSChoice.EtaleSection

namespace GlobalTheory.HSShort.EtaleSection

theorem spec_zero_iff {F : Type} [Field F] [NumberField F] (T : Tuple F) (hT : T.IsGeometric) (δ : ℕ)
    (f : MvPolynomial (Fin (T.D + 1) × Fin T.N) F) (hf : IsChowForm T.imageIdeal T.D δ f)
    (E : Type) [Field E] [Algebra F E] (s : Fin T.D → Fin T.N → E) (ξ : Fin T.N → AlgebraicClosure E) :
    eval (fun p => ξ p.2) (spec (fun i j => algebraMap E (AlgebraicClosure E) (s i j)) f) = 0 ↔
      ∃ x ∈ T.geomPts E (T.linSection E s),
        ∑ j, ξ j * T.coords (LinSys.toBase x : T.Pt (AlgebraicClosure E)).1 j = 0 := by
  rw [eval_spec]
  obtain ⟨hA, hB⟩ := GlobalTheory.T.chowForm_zeroSet_extensionField_iff_common_cone_zero F _ _ δ _ f hf
  have hs : ∀ (u y : Fin T.N → AlgebraicClosure E) (c : AlgebraicClosure E), ∑ j, u j * y j = 0 →
      ∑ j, u j * (c • y) j = 0 := fun u y c h => by
    simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, ← Finset.mul_sum]
    rw [h, mul_zero]
  constructor
  · intro h0
    obtain ⟨y, hy, hc, h₁, h₂⟩ := hB _ _ _ h0
    obtain ⟨x₀, c, -, h⟩ := GlobalTheory.ConeOnto.exists_pt_of_mem_cone_of_isAlgClosed F T.toLinSys hT.alg.variety hT.alg.bpf _ y hy hc
    obtain ⟨x, rfl⟩ := (T.toLinSys.toBase_bijective E (AlgebraicClosure E)).2 x₀
    refine ⟨x, (T.toLinSys.mem_subPts_cut_baseChange_iff E s x).2 fun i => ?_, ?_⟩ <;> rw [h]
    · exact hs _ _ _ (h₁ i)
    · exact hs _ _ _ h₂
  · rintro ⟨x, hx, h⟩
    refine hA _ _ _ _ (hT.alg.bpf.coords_ne_zero _) (fun g hg => ?_)
      ((T.toLinSys.mem_subPts_cut_baseChange_iff E s x).1 hx) h
    have := T.toLinSys.eval₂_coords_eq_zero (LinSys.toBase x : T.Pt (AlgebraicClosure E)).1 hg
    rwa [LinSys.baseHom_ptOver] at this

theorem simpleAt_of_noSquare : ∀ (F : Type) [Field F] [NumberField F] (T : Tuple F), T.IsGeometric → ∀ (δ : ℕ) (f : MvPolynomial (Fin (T.D + 1) × Fin T.N) F), IsChowForm T.imageIdeal T.D δ f → (δ : ℤ) = T.del → ∀ (E : Type) [Field E] [Algebra F E] (s : Fin T.D → Fin T.N → E), ((T.linSection E s).support : Set (T.toLinSys.baseChange E).Y).Finite → T.InOpen E (T.linSection E s) → NoSquare (spec (fun i j => algebraMap E (AlgebraicClosure E) (s i j)) f) → SimpleAt T δ f E s := by
  intro F _ _ T hT δ f hf hδ E _ _ s hfin hopen hsq
  classical
  obtain ⟨hfs, hmod, hrank⟩ := finite_finrank T hT E s hfin
  letI := algebraΓOfHom ((T.linSection E s).subschemeι ≫ (T.toLinSys.baseChange E).str)
  haveI := hmod
  have hPfin : (T.geomPts E (T.linSection E s)).Finite := hfs.finite_subPts _
  have hcard := natCard_subPts _ _ hfs (AlgebraicClosure E)
  have hI := GlobalTheory.T.etale_of_finrank_le_card_algHom E Γ((T.linSection E s).subscheme, ⊤)
  set P := T.geomPts E (T.linSection E s) with hPdef
  set Ω := AlgebraicClosure E
  let yv : (T.toLinSys.baseChange E).Pt Ω → Fin T.N → Ω := fun x => T.coords (LinSys.toBase x : T.Pt Ω).1
  have hyv : ∀ x, yv x ≠ 0 := fun x => hT.alg.bpf.coords_ne_zero _
  let line : (T.toLinSys.baseChange E).Pt Ω → Submodule Ω (Fin T.N → Ω) := fun x => Submodule.span Ω {yv x}
  have : Finite (line '' P) := (hPfin.image line).to_subtype
  let eR : (line '' P) ≃ Fin (Nat.card (line '' P)) := Finite.equivFin _
  have hrep : ∀ q : Fin (Nat.card (line '' P)), ∃ x ∈ P, line x = (eR.symm q : Submodule Ω (Fin T.N → Ω)) :=
    fun q => (eR.symm q).2
  choose rep hrepP hrepl using hrep
  let y : Fin (Nat.card (line '' P)) → Fin T.N → Ω := fun q => yv (rep q)
  have hinj : ∀ q q', line (rep q) = line (rep q') → q = q' := by
    intro q q' h
    apply eR.symm.injective
    apply Subtype.ext
    rw [← hrepl, ← hrepl, h]
  have hzero : ∀ ξ : Fin T.N → Ω, eval (fun p => ξ p.2) (spec (fun i j => algebraMap E Ω (s i j)) f) = 0 ↔
      ∃ q, ∑ j, ξ j * y q j = 0 := by
    intro ξ
    rw [spec_zero_iff T hT δ f hf E s ξ]
    constructor
    · rintro ⟨x, hx, h0⟩
      obtain ⟨q0, hq0⟩ : ∃ q0, eR.symm q0 = ⟨line x, x, hx, rfl⟩ := ⟨_, eR.symm_apply_apply _⟩
      refine ⟨q0, ?_⟩
      have hl : line (rep q0) = line x := by rw [hrepl, hq0]
      have hm : y q0 ∈ line x := by
        rw [← hl]
        exact Submodule.mem_span_singleton_self _
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hm
      rw [← ha]
      simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ a, ← Finset.mul_sum]
      rw [h0, mul_zero]
    · rintro ⟨q, hq⟩
      exact ⟨rep q, hrepP q, hq⟩
  have hprop : ∀ q q' (c : Ω), y q' = c • y q → q = q' := by
    intro q q' c h
    have hc : c ≠ 0 := by
      rintro rfl
      exact hyv _ (by simpa using h)
    apply hinj
    change Submodule.span Ω {yv (rep q)} = Submodule.span Ω {yv (rep q')}
    rw [show yv (rep q') = c • yv (rep q) from h, Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc)]
  obtain ⟨hmδ, c, hc, hfac⟩ := HyperplaneFactor.eq_C_mul_prod_lin Ω T.N δ _ _ y
    (isHomogeneous_spec _ f hf.homog) hsq (fun q => hyv _) hprop hzero
  have hPf : Finite P := hPfin.to_subtype
  have hrepinj : Function.Injective (fun q => (⟨rep q, hrepP q⟩ : P)) := fun q q' h =>
    hinj q q' (by rw [show rep q = rep q' from congrArg Subtype.val h])
  have hfr : (Module.finrank E Γ((T.linSection E s).subscheme, ⊤) : ℤ) = δ := hrank.trans hδ.symm
  have h1 : Nat.card P = Nat.card (Γ((T.linSection E s).subscheme, ⊤) →ₐ[E] AlgebraicClosure E) := hcard
  have h3 : Module.finrank E Γ((T.linSection E s).subscheme, ⊤) = δ := by exact_mod_cast hfr
  have hPle : Nat.card P ≤ δ := by
    have h2 := hI.2.1
    omega
  have hmP : Nat.card (Fin (Nat.card (line '' P))) ≤ Nat.card P := Nat.card_le_card_of_injective _ hrepinj
  rw [Nat.card_fin] at hmP
  have hPδ : Nat.card P = δ := by omega
  have hbij : Function.Bijective (fun q => (⟨rep q, hrepP q⟩ : P)) :=
    hrepinj.bijective_of_nat_card_le (by rw [Nat.card_fin]; show Nat.card P ≤ _; omega)
  refine ⟨⟨⟨hfs, etale_of_algebraEtale _ _ hfs (hI.2.2 ?_)⟩, hopen⟩, ?_, ?_, c, hc, ?_⟩
  · omega
  · rw [← Nat.card_coe_set_eq]
    exact hPδ
  · intro x hx x' hx' a ha h
    obtain ⟨q, hq⟩ := hbij.2 ⟨x, hx⟩
    obtain ⟨q', hq'⟩ := hbij.2 ⟨x', hx'⟩
    obtain rfl : rep q = x := congrArg Subtype.val hq
    obtain rfl : rep q' = x' := congrArg Subtype.val hq'
    obtain ⟨b, hb, e⟩ := T.toLinSys.exists_coords_baseChange E (rep q).1
    obtain ⟨b', hb', e'⟩ := T.toLinSys.exists_coords_baseChange E (rep q').1
    have e₁ : b' • y q' = a • b • y q := e'.symm.trans (h.trans (congrArg (a • ·) e))
    rw [hprop q q' (b'⁻¹ * a * b) (by rw [mul_smul, mul_smul, ← e₁, inv_smul_smul₀ hb'])]
  · rw [hfac]
    congr 1
    rw [← finprod_eq_prod_of_fintype, ← finprod_mem_univ]
    refine finprod_mem_eq_of_bijOn rep ⟨fun q _ => hrepP q, fun q _ q' _ h => hinj q q' (by rw [h]), fun x hx => ?_⟩
      fun q _ => rfl
    obtain ⟨q, hq⟩ := hbij.2 ⟨x, hx⟩
    exact ⟨q, Set.mem_univ _, congrArg Subtype.val hq⟩

end GlobalTheory.HSShort.EtaleSection
