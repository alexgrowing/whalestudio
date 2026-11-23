import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDivisorDominantPullbackWithClass
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapCompConstFn
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Cartier.PullCount

open GlobalTheory.Cartier.DomPull GlobalTheory.Cartier.CartierDiv

section Pull

variable {X X' : Scheme.{0}} [IsIntegral X] [IsIntegral X'] (φ : X' ⟶ X) [IsDominant φ]

theorem fnOf_pull_g (L : LB X) (J J' : (L.pull φ).ι)
    (hg : genericPoint X' ∈ (L.pull φ).U J ⊓ (L.pull φ).U J') :
    fnOf _ hg ((L.pull φ).g J J' : Γ(X', (L.pull φ).U J ⊓ (L.pull φ).U J')) =
      GlobalTheory.functionFieldMap φ (fnOf _ (gen_mem (x := φ (genericPoint X'))
        (show φ (genericPoint X') ∈ L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit) from
          ⟨mem_pull.1 hg.1, mem_pull.1 hg.2⟩))
        (L.g (J PUnit.unit) (J' PUnit.unit) : Γ(X, L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit)))) := by
  have h₀ : genericPoint X' ∈ φ ⁻¹ᵁ (L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit)) :=
    ⟨mem_pull.1 hg.1, mem_pull.1 hg.2⟩
  show fnOf _ hg (Units.val (∏ _k : PUnit.{1}, _ ^ (1 : ℤ))) = _
  rw [Fintype.prod_unique]
  erw [zpow_one, LB.val_res, fnOf_resG]
  exact fnOf_app φ h₀ _

theorem presents_pull {D : CartierDiv X} {L : LB X} {r : L.ι → X.functionFieldˣ} (h : Presents D L r) :
    Presents (pullback φ D) (L.pull φ) (fun J => unitsMap φ (r (J PUnit.unit))) := by
  refine ⟨LB.isLB_pull h.isLB φ, fun J J' hg => ?_,
    fun J x hx => isEqn_pullback φ D (h.isEqn _ _ (mem_pull.1 hx))⟩
  rw [fnOf_pull_g φ L J J' hg]
  show GlobalTheory.functionFieldMap φ _ = GlobalTheory.functionFieldMap φ _ * GlobalTheory.functionFieldMap φ _
  rw [← map_mul, ← h.isRatSec _ _ _]

end Pull

theorem genericPoint_mem_preimage {M W : Scheme.{0}} [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f]
    {V : W.Opens} {y : W} (hy : y ∈ V) : genericPoint M ∈ f ⁻¹ᵁ V := by
  show f (genericPoint M) ∈ V
  have := (genericPoint_spec M).image f.continuous
  rw [Set.image_univ, f.denseRange.closure_range] at this
  rw [this.eq (genericPoint_spec W)]
  exact gen_mem hy

theorem mem_sections_mul_co {M W : Scheme.{0}} [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f]
    {r : ℕ} (co : Fin r → (M.functionField →+ W.functionField))
    (hco : ∀ j c x, co j (GlobalTheory.functionFieldMap f c * x) = c * co j x)
    {D E : CartierDiv W} {A : LB W} {rA : A.ι → W.functionFieldˣ} (hE : Presents E A rA) (t : A.Sec)
    (hP : ∀ (y : W) (i : A.ι) (hi : y ∈ A.U i) (V' : W.Opens), y ∈ V' → ∀ (h : genericPoint M ∈ f ⁻¹ᵁ V')
      (z : Γ(M, f ⁻¹ᵁ V')) (j : Fin r), RegAt y (fnOf _ (gen_mem hi) (t.f i) * co j (fnOf (f ⁻¹ᵁ V') h z)))
    {x : M.functionField} (hx : x ∈ (pullback f D).sections) (j : Fin r) :
    hE.rat t * co j x ∈ (D + E).sections := by
  refine mem_sections.2 fun y => ?_
  obtain ⟨V', hy, g, hg⟩ := D.exists_isEqn_nhds y
  have hgen := genericPoint_mem_preimage f hy
  obtain ⟨z, hz⟩ := exists_fnOf_eq hgen (f := x * GlobalTheory.functionFieldMap f g) fun m hm =>
    (isEqn_pullback f D (hg _ hm)).regularAt_iff.1 (mem_sections.1 hx m)
  obtain ⟨i, hi⟩ := exists_chart hE.isLB y
  have key := hP y i hi V' hy hgen z j
  rw [← hE.rat_mul t i (gen_mem hi), hz, mul_comm x, hco] at key
  refine ((hg y hy).add (hE.isEqn i y hi)).regularAt_iff.2 ?_
  rw [Units.val_mul]
  convert key using 1
  ring

end GlobalTheory.Cartier.PullCount

namespace GlobalTheory.Cartier.PullCount

open GlobalTheory.Cartier.DomPull GlobalTheory.Cartier.CartierDiv

theorem finrank_sections_pullback_le_mul_twist_dominant : ∀ (F : Type) [Field F] (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp F) (f : M ⟶ W) [IsDominant f], IsProjOver p → ∀ {r : ℕ} (co : Fin r → (M.functionField →+ W.functionField)), (∀ j c x, co j (GlobalTheory.functionFieldMap f c * x) = c * co j x) → (∀ x, (∀ j, co j x = 0) → x = 0) → ∀ (A : LB W), A.IsLB → ∀ (t : A.Sec), t ≠ 0 → (∀ (y : W) (i : A.ι) (hi : y ∈ A.U i) (V' : W.Opens), y ∈ V' → ∀ (h : genericPoint M ∈ f ⁻¹ᵁ V') (z : Γ(M, f ⁻¹ᵁ V')) (j : Fin r), RegAt y (fnOf _ (gen_mem hi) (t.f i) * co j (fnOf (f ⁻¹ᵁ V') h z))) → ∀ (B : LB W), B.IsLB → (letI := algebraΓOfHom (f ≫ p); lbH0 F (B.pull f)) ≤ r * (letI := algebraΓOfHom p; lbH0 F (tens B A)) := by
  intro F _ M W _ _ p f _ hp r co hco hinj A hA t ht hP B hB
  obtain ⟨i₀, h₀⟩ := exists_chart hB (genericPoint W)
  have hD := presents_ofLB hB i₀ h₀
  obtain ⟨a₀, ha₀⟩ := exists_chart hA (genericPoint W)
  have hE := presents_ofLB hA a₀ ha₀
  have hDE := hD.tens hE
  have hpull := presents_pull f hD
  have hτ : hE.rat t ≠ 0 := fun e => ht (hE.rat_injective (e.trans (map_zero _).symm))
  letI iW : Algebra F Γ(W, ⊤) := algebraΓOfHom p
  letI iM : Algebra F Γ(M, ⊤) := algebraΓOfHom (f ≫ p)
  letI : Module F (B.pull f).Sec := Module.compHom _ (algebraMap F Γ(M, ⊤))
  haveI : IsScalarTower F Γ(M, ⊤) (B.pull f).Sec := IsScalarTower.of_compHom _ _ _
  letI : Module F (tens B A).Sec := Module.compHom _ (algebraMap F Γ(W, ⊤))
  haveI : IsScalarTower F Γ(W, ⊤) (tens B A).Sec := IsScalarTower.of_compHom _ _ _
  haveI : Module.Finite F (tens B A).Sec := by
    have := finite_coh_zero_twist_of_isProjOver (f := p) (fun _ => rfl) hp (isLB_tens hB hA)
    exact .equiv ((cohZeroTwistEquiv (tens B A)).restrictScalars F)
  have eW (c : F) : algebraMap F Γ(W, ⊤) c = ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p ⊤ c := by
    change p.appTop _ = _
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have eM (c : F) : algebraMap F Γ(M, ⊤) c = ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX (f ≫ p) ⊤ c := by
    change (f ≫ p).appTop _ = _
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have hconst (c : F) : fnOf ⊤ trivial (algebraMap F Γ(M, ⊤) c) =
      GlobalTheory.functionFieldMap f (fnOf ⊤ trivial (algebraMap F Γ(W, ⊤) c)) := by
    rw [eM, eW]
    exact (RingHom.congr_fun (GlobalTheory.EtaleKlt.functionFieldMap_comp_constFn p f) c).symm
  let Ψj (j : Fin r) : (B.pull f).Sec →ₗ[F] (tens B A).Sec :=
    { toFun := fun s => hDE.secEquiv.symm
        ⟨hE.rat t * co j (hpull.rat s), mem_sections_mul_co f co hco hE t hP (hpull.rat_mem s) j⟩
      map_add' := fun s s' => by
        rw [← map_add]
        congr 1
        apply Subtype.ext
        simp only [map_add, mul_add, Submodule.coe_add]
      map_smul' := fun c s => by
        rw [RingHom.id_apply]
        change _ = algebraMap F Γ(W, ⊤) c • (_ : (tens B A).Sec)
        rw [← map_smul]
        congr 1
        apply Subtype.ext
        change hE.rat t * co j (hpull.rat (algebraMap F Γ(M, ⊤) c • s)) =
          algebraMap F Γ(W, ⊤) c • (hE.rat t * co j (hpull.rat s))
        rw [map_smul, Algebra.smul_def, Algebra.smul_def, algebraMap_top, algebraMap_top, hconst, hco,
          mul_left_comm] }
  let Ψ : (B.pull f).Sec →ₗ[F] (Fin r → (tens B A).Sec) := LinearMap.pi Ψj
  have hΨ : Function.Injective Ψ := by
    refine (injective_iff_map_eq_zero Ψ).2 fun s hs => ?_
    refine hpull.rat_injective ((hinj _ fun j => ?_).trans (map_zero _).symm)
    have e := congrArg (fun v => (hDE.secEquiv (v j) : W.functionField)) hs
    simp only [Ψ, Ψj, LinearMap.pi_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.apply_symm_apply,
      Pi.zero_apply, map_zero, ZeroMemClass.coe_zero] at e
    exact (mul_eq_zero.1 e).resolve_left hτ
  rw [lineBundleGlobalSectionsDim_eq_finrank, lineBundleGlobalSectionsDim_eq_finrank]
  calc Module.finrank F (B.pull f).Sec ≤ Module.finrank F (Fin r → (tens B A).Sec) :=
        LinearMap.finrank_le_finrank_of_injective hΨ
    _ = r * Module.finrank F (tens B A).Sec := by
        rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

end GlobalTheory.Cartier.PullCount
