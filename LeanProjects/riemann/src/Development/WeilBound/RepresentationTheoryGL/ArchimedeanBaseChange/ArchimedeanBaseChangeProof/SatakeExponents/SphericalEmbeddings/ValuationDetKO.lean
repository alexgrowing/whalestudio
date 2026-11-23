import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.ExtremeSph
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviIntegralFacts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrreducibleOfFixedLine
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIrreducibleSubquotient

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix

namespace PositivityTheory.Rg.BcB.N3.Pee

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem valuation_det_KO {m : Type} [Fintype m] [DecidableEq m] {g : GL m k} (hg : g ∈ KO k m) :
    valuation k ((GeneralLinearGroup.det g : kˣ) : k) = 1 := by
  obtain ⟨g', rfl⟩ := hg
  have h1 : ((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap 𝒪[k] k) g') : kˣ) : k) =
      algebraMap 𝒪[k] k (GeneralLinearGroup.det g' : 𝒪[k]ˣ) :=
    ((algebraMap 𝒪[k] k).map_det _).symm
  exact h1.symm ▸ (Valuation.integer.integers (valuation k)).one_of_isUnit (Units.isUnit _)

private theorem deltaHalf_and_torusChar_eq_one_of_mem_KO (n : ℕ) (ξ : Fin n → ℂˣ) (b : parab k (points (Fin n)))
    (hb : (b : GL (Fin n) k) ∈ KO k (Fin n)) :
    deltaHalf k (fun _ : Fin n => Unit) (leviProj k (points (Fin n)) b) = 1 ∧
    torusChar (fun i => unrChar k (ξ i)) ((leviTorus k (Fin n)).symm (leviProj k (points (Fin n)) b)) = 1 := by
  have hL := (GlobalTheory.SmGL.LeviInt.levi_integral_facts k (Fin n) (Fin n) (fun _ => Unit) (points (Fin n))).2.1 b hb
  constructor
  · rw [deltaHalf, MonoidHom.finset_prod_apply]
    refine Finset.prod_eq_one (fun a _ => ?_)
    rw [MonoidHom.comp_apply, detChar_apply]
    exact isUnram_absPow k _ _ (valuation_det_KO (hL a))
  · rw [torusChar, MonoidHom.finset_prod_apply]
    refine Finset.prod_eq_one (fun i _ => ?_)
    have h0 : ord k (GeneralLinearGroup.det (leviProj k (points (Fin n)) b i)) = 0 :=
      ord_eq_zero_iff.mpr (valuation_det_KO (hL i))
    show (ξ i) ^ ord k (GeneralLinearGroup.det (leviProj k (points (Fin n)) b i)) = 1
    rw [h0, zpow_zero]

theorem exists_sph (n : ℕ) (ξ : Fin n → ℂˣ) :
    ∃ f : IndSp (points (Fin n)) ((ofChar (torusChar fun i => unrChar k (ξ i))).comp
      (leviTorus k (Fin n)).symm.toMonoidHom), f ∈ fixed (iP (k := k) ξ) (KO k (Fin n)) ∧ f ≠ 0 := by
  set μ : parab k (points (Fin n)) → ℂ := fun b =>
    ((deltaHalf k (fun _ : Fin n => Unit) (leviProj k (points (Fin n)) b) : ℂˣ) : ℂ) *
      ((torusChar (fun i => unrChar k (ξ i)) ((leviTorus k (Fin n)).symm (leviProj k (points (Fin n)) b)) : ℂˣ) : ℂ) with hμ
  have μmul : ∀ a b : parab k (points (Fin n)), μ (a * b) = μ a * μ b := by
    intro a b
    simp only [hμ, map_mul, Units.val_mul]
    ring
  have μone : ∀ b : parab k (points (Fin n)), (b : GL (Fin n) k) ∈ KO k (Fin n) → μ b = 1 := by
    intro b hb
    obtain ⟨h1, h2⟩ := deltaHalf_and_torusChar_eq_one_of_mem_KO n ξ b hb
    simp only [hμ, h1, h2, Units.val_one, mul_one]
  have hdec := (GlobalTheory.SmGL.LeviInt.levi_integral_facts k (Fin n) (Fin n) (fun _ => Unit) (points (Fin n))).2.2.2.2.2.2.2.2
  choose p hp x hx hg using hdec
  have wd : ∀ (q : parab k (points (Fin n))) (y : GL (Fin n) k), y ∈ KO k (Fin n) → ∀ g, g = (q : GL (Fin n) k) * y →
      μ ⟨p g, hp g⟩ = μ q := by
    intro q y hy g hgq
    have hmem : (q : GL (Fin n) k)⁻¹ * p g ∈ parab k (points (Fin n)) := mul_mem (inv_mem q.2) (hp g)
    have hK : (q : GL (Fin n) k)⁻¹ * p g ∈ KO k (Fin n) := by
      have : (q : GL (Fin n) k)⁻¹ * p g = y * (x g)⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq]
        exact (hg g).symm.trans hgq
      rw [this]
      exact mul_mem hy (inv_mem (hx g))
    have e1 : (⟨p g, hp g⟩ : parab k (points (Fin n))) = q * ⟨_, hmem⟩ := by
      ext1
      simp
    rw [e1, μmul, μone ⟨_, hmem⟩ hK, mul_one]
  set φ : GL (Fin n) k → ℂ := fun g => μ ⟨p g, hp g⟩ with hφ
  have c1 : ∀ (b : borel k (Fin n)) (g : GL (Fin n) k), φ (b * g) =
      ↑((deltaHalf k fun (x : Fin n) ↦ Unit) ((leviProj k (points (Fin n))) b)) •
        ((MonoidHom.comp (ofChar (torusChar (fun i => unrChar k (ξ i)))) (leviTorus k (Fin n)).symm.toMonoidHom)
          ((leviProj k (points (Fin n))) b)) (φ g) := by
    intro b g
    have e2 : φ (b * g) = μ (⟨b.1, b.2⟩ * ⟨p g, hp g⟩) := by
      refine wd _ (x g) (hx g) _ ?_
      rw [Subgroup.coe_mul, mul_assoc, ← hg g]
    rw [e2, μmul]
    change _ = ((deltaHalf k (fun _ : Fin n => Unit) (leviProj k (points (Fin n)) ⟨b.1, b.2⟩) : ℂˣ) : ℂ) *
      (((torusChar (fun i => unrChar k (ξ i)) ((leviTorus k (Fin n)).symm
        (leviProj k (points (Fin n)) ⟨b.1, b.2⟩)) : ℂˣ) : ℂ) * φ g)
    simp only [hμ, hφ]
    ring
  have c2 : ∀ w ∈ KO k (Fin n), ∀ (g : GL (Fin n) k), φ (g * w) = φ g := by
    intro w hw g
    exact wd ⟨p g, hp g⟩ (x g * w) (mul_mem (hx g) hw) _ (by rw [← mul_assoc, ← hg g])
  obtain ⟨f, hf, hfφ⟩ := (SphCompletion.exists_fixed_iff (k := k) (fun i => unrChar k (ξ i)) φ).mpr ⟨c1, c2⟩
  refine ⟨f, hf, fun h0 => ?_⟩
  have h1 : φ 1 = 1 := by
    rw [hφ]
    simp only
    rw [wd 1 1 (one_mem _) 1 (by simp)]
    simp [hμ]
  have h2 := congrFun hfφ 1
  rw [h0, h1] at h2
  exact zero_ne_one h2

theorem sphConst (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    PositivityTheory.Rg.BcB.N3.SphConst k := by
  intro n ξ
  obtain ⟨f, hf, hf0⟩ := exists_sph (k := k) n ξ
  have hne : fixed (iP (k := k) ξ) (KO k (Fin n)) ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    exact ⟨f, hf, hf0⟩
  obtain ⟨Y, i1, i2, σ, hirr, hfix, hsub⟩ := GlobalTheory.CuspRep.ParLaws.exists_irreducible_fixed _ _ hne
  refine ⟨Y, i1, i2, σ, ?_, hirr, hfix, hsub⟩
  obtain ⟨S, F, hF⟩ := hsub
  have hsm : IsSmooth (iP (k := k) ξ) := isSmooth_parInd _ _
  refine isSmooth_of_nhds (fun y => ?_)
  obtain ⟨s, rfl⟩ := hF y
  have ho : IsOpen {g : GL (Fin n) k | (iP ξ g) (s : _) = s} := hsm s
  have h1 : (1 : GL (Fin n) k) ∈ {g : GL (Fin n) k | (iP ξ g) (s : _) = s} := by
    rw [Set.mem_setOf_eq, map_one]
    rfl
  refine Filter.mem_of_superset (ho.mem_nhds h1) ?_
  intro g hg
  have e1 := LinearMap.congr_fun (F.isIntertwining' g) s
  simp only [LinearMap.comp_apply] at e1
  change (σ g) (F.toLinearMap s) = F.toLinearMap s
  rw [← e1]
  congr 1
  exact Subtype.ext hg

end PositivityTheory.Rg.BcB.N3.Pee
