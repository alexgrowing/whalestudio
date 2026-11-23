import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.EStar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.AdSurj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.ExistsUnitNormQuotientLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.LocBase
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.UaFacts

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.Dict.Br

private theorem cof_val (F : Type) [Field F] [NumberField F] (a : F) (ha : a ≠ 0) :
    ∀ᶠ v : Pl F in Filter.cofinite, v.valuation F a = 1 := by
  have h1 := HeightOneSpectrum.Support.finite (𝓞 F) a
  have h2 := HeightOneSpectrum.Support.finite (𝓞 F) a⁻¹
  have h3 : ((HeightOneSpectrum.Support (𝓞 F) a) ∪ (HeightOneSpectrum.Support (𝓞 F) a⁻¹))ᶜ ∈ Filter.cofinite (α := Pl F) := by
    rw [Filter.mem_cofinite, compl_compl]
    exact h1.union h2
  filter_upwards [h3] with v hv
  simp only [Set.mem_compl_iff, Set.mem_union, not_or, HeightOneSpectrum.Support, Set.mem_setOf_eq, not_lt] at hv
  apply le_antisymm hv.1
  have := hv.2
  rw [map_inv₀] at this
  have h0 : v.valuation F a ≠ 0 := by simpa using ha
  exact (inv_le_one₀ (zero_lt_iff.2 h0)).1 this

private theorem unit_of_val (F : Type) [Field F] [NumberField F] (v : Pl F) (a : F) (h : v.valuation F a = 1) :
    ∃ u : (Ov v)ˣ, algebraMap (Ov v) (Kv v) u = cv v a := by
  have h1 : Valued.v (cv v a) = 1 := by
    rw [← h]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v a
  have h0 : cv v a ≠ 0 := by
    intro h0
    rw [h0] at h1
    simp at h1
  have h2 : Valued.v (cv v a)⁻¹ = 1 := by rw [map_inv₀, h1, inv_one]
  refine ⟨⟨⟨cv v a, h1.le⟩, ⟨(cv v a)⁻¹, h2.le⟩, ?_, ?_⟩, rfl⟩
  · exact Subtype.ext (mul_inv_cancel₀ h0)
  · exact Subtype.ext (inv_mul_cancel₀ h0)

private theorem conj_cmp {A A' : Type} [CommRing A] [CommRing A'] (ρ : A →+* A') (c : A)
    (Y G : GL (Fin 2) A) (P Q R : GL (Fin 2) A')
    (hP : (P : Matrix (Fin 2) (Fin 2) A') = (((Y⁻¹ * G * Y : GL (Fin 2) A)) : Matrix (Fin 2) (Fin 2) A).map ρ)
    (hQ : (Q : Matrix (Fin 2) (Fin 2) A') = (G : Matrix (Fin 2) (Fin 2) A).map ρ)
    (hR : (R : Matrix (Fin 2) (Fin 2) A') = (c • (Y : Matrix (Fin 2) (Fin 2) A)).map ρ) :
    P = R⁻¹ * Q * R := by
  have key : R * P = Q * R := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hP, hQ, hR, ← Matrix.map_mul, ← Matrix.map_mul]
    congr 1
    have : (Y : Matrix (Fin 2) (Fin 2) A) * ((Y⁻¹ * G * Y : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = (G : Matrix (Fin 2) (Fin 2) A) * (Y : Matrix (Fin 2) (Fin 2) A) := by
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    rw [Matrix.smul_mul, this, Matrix.mul_smul]
  rw [mul_assoc, eq_inv_mul_iff_mul_eq, key]

end UpperTheory.V.Z.Sym.Dict.Br

theorem UpperTheory.V.Z.Sym.Dict.Br.okConj :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (B : Bridge L), ∀ x ∈ finU L 2, ∃ y : DA B.Δ, (∀ v, (∀ w, un w = v → cLoc w x = 1) → y.1 v = 1) ∧ ∀ g : SA B.Δ, ∃ g' : SA B.Δ, (g' : DA B.Δ) = y⁻¹ * g * y ∧ (B.bS g' : UA L 2) = x⁻¹ * B.bS g * x := by
  intro L _ _ _ B x hx
  obtain ⟨X, hXu, hXi, hXw⟩ := adSurj L B.toRingBr 2 x
  have hΔ : B.Δ ≠ 0 := by
    intro h0
    have hω : (QuadraticAlgebra.omega : Lsq (Lp L) B.Δ) * QuadraticAlgebra.omega = 0 := by
      ext <;> simp [h0]
    have h1 : B.e QuadraticAlgebra.omega * B.e QuadraticAlgebra.omega = 0 := by
      rw [← map_mul, hω, map_zero]
    have h2 : B.e QuadraticAlgebra.omega = 0 := mul_self_eq_zero.1 h1
    have h3 : (QuadraticAlgebra.omega : Lsq (Lp L) B.Δ) = 0 := (map_eq_zero_iff _ B.e.injective).1 h2
    simpa using congrArg QuadraticAlgebra.im h3
  have h2F : (2 : Lp L) ≠ 0 := two_ne_zero
  have h2 : ∀ v : Pl (Lp L), (2 : Kv v) ≠ 0 := by
    intro v h0
    apply h2F
    apply (cv v).injective
    rw [map_ofNat, map_zero, h0]
  have hΔv : ∀ v : Pl (Lp L), cv v B.Δ ≠ 0 := fun v h0 => hΔ ((map_eq_zero _).1 h0)
  choose Y c hYc hY1 hYK using fun v : Pl (Lp L) => h90 (Ov v) (Kv v) (cv v B.Δ) (h2 v) (hΔv v) (X v) (hXu v)
  have hYA : Y ∈ RP (fun v : Pl (Lp L) => DX (cv v B.Δ)) fun v => KD (cv v B.Δ) (Ov v) := by
    show ∀ᶠ v in Filter.cofinite, Y v ∈ KD (cv v B.Δ) (Ov v)
    filter_upwards [hXi, cof_val (Lp L) B.Δ hΔ, cof_val (Lp L) 2 h2F] with v hi hv h2v
    obtain ⟨h1, -, -, h4⟩ := locBase (Lp L) v
    haveI := h1
    have h2n : (2 : 𝓞 (Lp L)) ∉ v.asIdeal := by
      intro hm
      have := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := Lp L) v (2 : 𝓞 (Lp L))).2 hm
      simp only [map_ofNat] at this
      exact this.ne h2v
    exact hYK v (h4 h2n) (unit_of_val (Lp L) v B.Δ hv) hi
  refine ⟨⟨Y, hYA⟩, ?_, ?_⟩
  · intro v hv
    apply hY1 v
    refine Matrix.ext fun i j => ?_
    rw [← sub_eq_zero]
    apply B.ρ_inj v
    intro w h
    subst h
    have := hXw w
    have h3 : mL w x = 1 := by
      simp only [mL, hv w rfl]
      rfl
    rw [map_sub, sub_eq_zero]
    have h4 := congrFun (congrFun (this.symm.trans h3) i) j
    rw [Matrix.map_apply] at h4
    rw [h4]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  · intro g
    have hmem : ((⟨Y, hYA⟩ : DA B.Δ)⁻¹ * (g : DA B.Δ) * ⟨Y, hYA⟩) ∈ SA B.Δ := by
      have hg := g.2
      simp only [SA, Subgroup.mem_iInf] at hg ⊢
      intro v
      have := hg v
      simp only [Subgroup.mem_comap, SU, MonoidHom.mem_ker, MonoidHom.comp_apply] at this ⊢
      simp only [map_mul, map_inv, this, mul_one, inv_mul_cancel]
    refine ⟨⟨_, hmem⟩, rfl, ?_⟩
    have hF := (uaFacts L 2)
    have hext := hF.2.2.2.2.1
    have hfin := hF.2.2.2.2.2.1
    apply hext
    · intro w
      rw [map_mul, map_mul, map_inv]
      apply conj_cmp (B.ρ _ w rfl) (c (un w) : Lsq (Kv (un w)) (cv (un w) B.Δ)) ((Y (un w) : DX _) : GL (Fin 2) _) (((g : DA B.Δ).1 (un w) : DX _) : GL (Fin 2) _)
      · exact B.bS_loc _ w
      · exact B.bS_loc _ w
      · rw [← hYc]
        exact hXw w
    · intro τ
      have a1 := ((hfin _).1.1 (B.bS ⟨_, hmem⟩).2.1) τ
      have a2 := ((hfin _).1.1 (B.bS g).2.1) τ
      have a3 := ((hfin _).1.1 hx) τ
      rw [a1, map_mul, map_mul, map_inv, a2, a3]
      simp
