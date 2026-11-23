import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.QuasiOrbits.ModulusSquares.HaarEqOneOfSq
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusBounds.DetSurj

noncomputable section

open Matrix Module

namespace PositivityTheory.RgUd.TP.Nil.Orb.Mod

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil.Orb.BModbound

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem det_sqT (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (τ : Matrix (Fin n) (Fin n) k →ₗ[k] k) (hτ : IsTau Z τ) (x : Matrix (Fin n) (Fin n) k)
    (hx : x ∈ Bz Z) (g : GL (Fin n) k) (hg : g ∈ Gz Z) (t : k) (ht : t ≠ 0) (hgx : g.val * x * g⁻¹.val = t • x) :
    (LinearMap.det ((adL g).restrict (cA_inv Z x g hg t ht hgx))) ^ 2 =
      t ^ (finrank k (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) - finrank k (cA Z x)) := by
  classical
  set Cs : Submodule k (Matrix (Fin n) (Fin n) k) :=
    (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))).toSubmodule with hCs
  have memC : ∀ y : Matrix (Fin n) (Fin n) k, y ∈ Cs ↔ y ∈ Bz Z := by
    intro y
    show y ∈ Subalgebra.centralizer k _ ↔ _
    rw [Subalgebra.mem_centralizer_iff]
    rfl
  have hxC : x ∈ Cs := (memC x).2 hx

  have hgx1 : g.val * x = t • (x * g.val) := by
    have := congrArg (· * g.val) hgx
    simpa [mul_assoc, smul_mul_assoc] using this
  have hxg : x * g.val = t⁻¹ • (g.val * x) := by
    rw [hgx1, smul_smul, inv_mul_cancel₀ ht, one_smul]
  have hgx2 : x * g⁻¹.val = t • (g⁻¹.val * x) := by
    have := congrArg (g⁻¹.val * ·) hgx
    simpa [← mul_assoc, mul_smul_comm] using this
  have hginx : g⁻¹.val * x = t⁻¹ • (x * g⁻¹.val) := by
    rw [hgx2, smul_smul, inv_mul_cancel₀ ht, one_smul]
  have hginv : g⁻¹ ∈ Gz Z := fun a ha => PositivityTheory.RgUd.T.Desc.UniPf.inv_comm_of_comm g a (hg a ha)
  have hgx' : (g⁻¹).val * x * (g⁻¹)⁻¹.val = t⁻¹ • x := by
    rw [inv_inv, hginx, smul_mul_assoc, mul_assoc, Units.inv_mul, mul_one]

  set ψ : Module.End k Cs := (adL g).restrict (cC_inv Z g hg) with hψdef
  have hψ : ∀ y : Cs, ((ψ y : Cs) : Matrix (Fin n) (Fin n) k) = g.val * y * g⁻¹.val := fun y => adL_apply g y
  have hδmem : ∀ y ∈ Cs, (LinearMap.mulLeft k x - LinearMap.mulRight k x) y ∈ Cs := by
    intro y hy
    simp only [LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
    exact Cs.sub_mem (Subalgebra.mul_mem _ hxC hy) (Subalgebra.mul_mem _ hy hxC)
  set δ : Module.End k Cs := (LinearMap.mulLeft k x - LinearMap.mulRight k x).restrict hδmem with hδdef
  have hδ : ∀ y : Cs, ((δ y : Cs) : Matrix (Fin n) (Fin n) k) = x * y - y * x := fun y => rfl

  set A' : Submodule k Cs := (cA Z x).comap Cs.subtype with hA'def
  have hAC : cA Z x ≤ Cs := fun y hy => (memC y).2 hy.1
  have hkerδ : LinearMap.ker δ = A' := by
    ext y
    simp only [LinearMap.mem_ker]
    constructor
    · intro h
      have h' : x * (y : Matrix (Fin n) (Fin n) k) - y * x = 0 := by rw [← hδ, h]; rfl
      exact ⟨(memC y).1 y.2, (sub_eq_zero.1 h').symm⟩
    · intro h
      have h2 : (y : Matrix (Fin n) (Fin n) k) * x = x * y := h.2
      apply Subtype.ext
      rw [hδ, ← h2, sub_self]; rfl
  have hA' : ∀ y ∈ A', ψ y ∈ A' := by
    intro y hy
    show ((ψ y : Cs) : Matrix (Fin n) (Fin n) k) ∈ cA Z x
    exact cA_inv Z x g hg t ht hgx _ hy
  set ψinv : Module.End k Cs := (adL g⁻¹).restrict (cC_inv Z g⁻¹ hginv) with hψinvdef
  have hψinv : ∀ y : Cs, ((ψinv y : Cs) : Matrix (Fin n) (Fin n) k) = g⁻¹.val * y * g.val := by
    intro y
    show adL g⁻¹ y = _
    rw [adL_apply, inv_inv]
  have hA'inv : ∀ y ∈ A', ψinv y ∈ A' := by
    intro y hy
    show ((ψinv y : Cs) : Matrix (Fin n) (Fin n) k) ∈ cA Z x
    exact cA_inv Z x g⁻¹ hginv t⁻¹ (inv_ne_zero ht) hgx' _ hy
  set ρ : Module.End k A' := ψ.restrict hA' with hρdef
  set ρinv : Module.End k A' := ψinv.restrict hA'inv with hρinvdef

  have hB : ∀ y ∈ LinearMap.range δ, ψ y ∈ LinearMap.range δ := by
    rintro _ ⟨z, rfl⟩
    refine ⟨t • ψ z, ?_⟩
    apply Subtype.ext
    rw [map_smul, Submodule.coe_smul, hδ, hψ, hψ, hδ]
    calc t • (x * (g.val * z * g⁻¹.val) - g.val * z * g⁻¹.val * x)
        = t • ((x * g.val) * z * g⁻¹.val - g.val * z * (g⁻¹.val * x)) := by simp only [mul_assoc]
      _ = g.val * (x * z - z * x) * g⁻¹.val := by
          rw [hxg, hginx, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, ← smul_sub, smul_smul,
            mul_inv_cancel₀ ht, one_smul]
          simp only [mul_sub, sub_mul, mul_assoc]

  have E1 : LinearMap.det ψ = LinearMap.det ρ * LinearMap.det (t⁻¹ • ψ.restrict hB) := by
    refine det_surj ψ (t⁻¹ • ψ.restrict hB) δ.rangeRestrict δ.surjective_rangeRestrict ?_ A' ?_ hA'
    · intro y
      apply Subtype.ext
      apply Subtype.ext
      show x * ((ψ y : Cs) : Matrix (Fin n) (Fin n) k) - ((ψ y : Cs) : Matrix (Fin n) (Fin n) k) * x =
        t⁻¹ • ((ψ (δ y) : Cs) : Matrix (Fin n) (Fin n) k)
      rw [hψ, hψ, hδ]
      calc x * (g.val * y * g⁻¹.val) - g.val * y * g⁻¹.val * x
          = (x * g.val) * y * g⁻¹.val - g.val * y * (g⁻¹.val * x) := by simp only [mul_assoc]
        _ = t⁻¹ • (g.val * (x * y - y * x) * g⁻¹.val) := by
          rw [hxg, hginx, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, ← smul_sub]
          simp only [mul_sub, sub_mul, mul_assoc]
    · rw [LinearMap.ker_rangeRestrict, hkerδ]

  let Φ : Cs →ₗ[k] Module.Dual k Cs := LinearMap.mk₂ k
    (fun y z : Cs => τ ((y : Matrix (Fin n) (Fin n) k) * (z : Matrix (Fin n) (Fin n) k)))
    (by intros; simp [add_mul]) (by intros; simp)
    (by intros; simp [mul_add]) (by intros; simp)
  have hΦ : ∀ y z : Cs, Φ y z = τ ((y : Matrix (Fin n) (Fin n) k) * (z : Matrix (Fin n) (Fin n) k)) :=
    fun _ _ => rfl
  have hΦinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    apply Subtype.ext
    refine hτ.2 y ((memC y).1 y.2) (fun z hz => ?_)
    have := LinearMap.congr_fun hy ⟨z, (memC z).2 hz⟩
    rw [hΦ] at this
    exact this
  have hΦsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank Subspace.dual_finrank_eq.symm).1 hΦinj
  let L2 : Cs →ₗ[k] Module.Dual k A' := A'.subtype.dualMap ∘ₗ Φ
  have hL2 : ∀ (y : Cs) (a : A'), L2 y a = τ ((y : Matrix (Fin n) (Fin n) k) * ((a : Cs) : Matrix (Fin n) (Fin n) k)) :=
    fun _ _ => rfl
  have hL2surj : Function.Surjective L2 :=
    (LinearMap.dualMap_surjective_of_injective A'.injective_subtype).comp hΦsurj
  have hrk : finrank k (LinearMap.range δ) + finrank k A' = finrank k Cs := by
    rw [← hkerδ]; exact LinearMap.finrank_range_add_finrank_ker δ
  have hBker : LinearMap.range δ = LinearMap.ker L2 := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨z, rfl⟩
      rw [LinearMap.mem_ker]
      ext a
      rw [hL2, hδ, LinearMap.zero_apply]
      have ha : ((a : Cs) : Matrix (Fin n) (Fin n) k) * x = x * ((a : Cs) : Matrix (Fin n) (Fin n) k) := a.2.2
      have hza : (z : Matrix (Fin n) (Fin n) k) * ((a : Cs) : Matrix (Fin n) (Fin n) k) ∈ Cs :=
        Subalgebra.mul_mem _ z.2 (a : Cs).2
      have hs := hτ.1 x hx _ ((memC _).1 hza)
      rw [sub_mul, map_sub, mul_assoc, hs, mul_assoc, ha, ← mul_assoc, sub_self]
    · have h2 := LinearMap.finrank_range_add_finrank_ker L2
      rw [LinearMap.range_eq_top.2 hL2surj, finrank_top, Subspace.dual_finrank_eq] at h2
      omega
  have E2 : LinearMap.det ψ = LinearMap.det (ψ.restrict hB) * LinearMap.det ρinv.dualMap := by
    refine det_surj ψ ρinv.dualMap L2 hL2surj ?_ (LinearMap.range δ) hBker hB
    intro y
    ext a
    rw [hL2, LinearMap.dualMap_apply, hL2, hψ]
    show τ (g.val * (y : Matrix (Fin n) (Fin n) k) * g⁻¹.val * ((a : Cs) : Matrix (Fin n) (Fin n) k)) =
      τ ((y : Matrix (Fin n) (Fin n) k) * ((ψinv a : Cs) : Matrix (Fin n) (Fin n) k))
    rw [hψinv]
    have hgC : g.val ∈ Cs := (memC _).2 fun a ha => hg a ha
    have hginvC : g⁻¹.val ∈ Cs := (memC _).2 fun a ha => hginv a ha
    have hm : (y : Matrix (Fin n) (Fin n) k) * g⁻¹.val * ((a : Cs) : Matrix (Fin n) (Fin n) k) ∈ Cs :=
      Subalgebra.mul_mem _ (Subalgebra.mul_mem _ y.2 hginvC) (a : Cs).2
    have h1 := hτ.1 g.val ((memC _).1 hgC) _ ((memC _).1 hm)
    calc τ (g.val * (y : Matrix (Fin n) (Fin n) k) * g⁻¹.val * ((a : Cs) : Matrix (Fin n) (Fin n) k))
        = τ (g.val * ((y : Matrix (Fin n) (Fin n) k) * g⁻¹.val * ((a : Cs) : Matrix (Fin n) (Fin n) k))) := by
          simp only [mul_assoc]
      _ = τ ((y : Matrix (Fin n) (Fin n) k) * g⁻¹.val * ((a : Cs) : Matrix (Fin n) (Fin n) k) * g.val) := h1
      _ = τ ((y : Matrix (Fin n) (Fin n) k) * (g⁻¹.val * ((a : Cs) : Matrix (Fin n) (Fin n) k) * g.val)) := by
          simp only [mul_assoc]
  have E3 : LinearMap.det ρinv * LinearMap.det ρ = 1 := by
    rw [← LinearMap.det_comp]
    have : ρinv ∘ₗ ρ = LinearMap.id := by
      apply LinearMap.ext; intro y
      apply Subtype.ext; apply Subtype.ext
      show ((ψinv (ψ y) : Cs) : Matrix (Fin n) (Fin n) k) = ((y : Cs) : Matrix (Fin n) (Fin n) k)
      rw [hψinv, hψ]
      simp [mul_assoc]
    rw [this, LinearMap.det_id]
  have E0 : LinearMap.det ψ ^ 2 = 1 := det_C_sq Z τ hτ g hg
  have hψ0 : LinearMap.det ψ ≠ 0 := fun h => by rw [h] at E0; simp at E0

  let eA : A' ≃ₗ[k] cA Z x := Submodule.comapSubtypeEquivOfLe hAC
  have hρA : (eA : A' →ₗ[k] cA Z x) ∘ₗ ρ ∘ₗ (eA.symm : cA Z x →ₗ[k] A') =
      (adL g).restrict (cA_inv Z x g hg t ht hgx) := by
    apply LinearMap.ext; intro y
    apply Subtype.ext
    show ((ψ (eA.symm y : A') : Cs) : Matrix (Fin n) (Fin n) k) = adL g y
    rw [hψ, adL_apply]
    rfl
  have hdetA : LinearMap.det ((adL g).restrict (cA_inv Z x g hg t ht hgx)) = LinearMap.det ρ := by
    rw [← hρA, LinearMap.det_conj]
  have hfr : finrank k (cA Z x) = finrank k A' := eA.finrank_eq.symm
  have hfrC : finrank k (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) = finrank k Cs := rfl
  rw [hdetA, hfr, hfrC, show finrank k Cs - finrank k A' = finrank k (LinearMap.range δ) by omega]
  set r := finrank k (LinearMap.range δ)
  rw [LinearMap.det_dualMap] at E2
  have hdB : LinearMap.det (ψ.restrict hB) = LinearMap.det ψ * LinearMap.det ρ := by
    rw [E2, mul_assoc, E3, mul_one]
  rw [LinearMap.det_smul, hdB] at E1
  have key : LinearMap.det ψ * t ^ r = LinearMap.det ψ * LinearMap.det ρ ^ 2 := by
    calc LinearMap.det ψ * t ^ r
        = LinearMap.det ρ * (t⁻¹ ^ finrank k (LinearMap.range δ) * (LinearMap.det ψ * LinearMap.det ρ)) * t ^ r := by
          rw [← E1]
      _ = LinearMap.det ψ * LinearMap.det ρ ^ 2 * (t⁻¹ ^ r * t ^ r) := by ring
      _ = LinearMap.det ψ * LinearMap.det ρ ^ 2 := by rw [← mul_pow, inv_mul_cancel₀ ht, one_pow, mul_one]
  exact (mul_left_cancel₀ hψ0 key).symm
end PositivityTheory.RgUd.TP.Nil.Orb.Mod
