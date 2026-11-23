import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealCochainOfCoboundaryConstantsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareZeroLiftSystemFiltrationInfEqAndFullStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLiftSystemFiltrationSupIffHodgeFiltrationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsComplOfAgreeModSqZeroIdealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineClassSecondSystemEqNegDefectStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocIsoTransportCochainsInIdealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistSquareZeroSmoothLiftSystemByDerivatioStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearLiftOfProjective
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftSys

def Sys.cocyclesInIdealExtensions {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {X₀ : Scheme.{0}}
    {s₀ : X₀ ⟶ Sp R₀} (S : Sys I π s₀) : Submodule R (Z1 S.F) where
  carrier := {z | S.IsIdealValuedLiftSystemCocycle z}
  add_mem' {a b} ha hb U V f := by
    change a.1 U V f + b.1 U V f ∈ _
    exact Ideal.add_mem _ (ha U V f) (hb U V f)
  zero_mem' U V f := Ideal.zero_mem _
  smul_mem' r z hz U V f := by
    change r • z.1 U V f ∈ _
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (hz U V f)

theorem exists_sys_of_summand : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Good s₀ → RhoBC hI hk s₀ → ∀ S' : Sys I π s₀, S'.Full hI → (∃ N, IsCompl (S'.K hI) N) → ∀ K : Submodule R (Cr hI π s₀), (∃ N, IsCompl K N) → K ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) = S'.K hI ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) → ∃ S : Sys I π s₀, S.K hI = K := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ hG hR S' hF hN K hN' hsup
  obtain ⟨N, hN⟩ := hN

  have lin := GlobalTheory.T.isCompl_of_agree_mod_sqZero_ideal R I hI (Cr hI π s₀) (S'.K hI) K N hN hsup
  obtain ⟨hKinf, u, hu, hu0, hall⟩ := lin.2 hN'
  have hKN : IsCompl K N := lin.1 hKinf
  have ksup := GlobalTheory.T.mem_liftSystemFiltration_sup_iff_hodgeFiltration R R₀ I hI π hπ hk X₀ s₀

  have fadd : ∀ (c1 c2 : Cr hI π s₀) (w1 w2 : GlobForm s₀), FormOf hI hk c1 w1 → FormOf hI hk c2 w2 → FormOf hI hk (c1 + c2) (w1 + w2) := by
    rintro c1 c2 w1 w2 ⟨f1, h1, e1⟩ ⟨f2, h2, e2⟩
    exact ⟨f1 + f2, by rw [map_add, map_add, h1, h2], by rw [map_add, Submodule.coe_add, e1, e2]⟩
  have fsmul : ∀ (r : R) (c : Cr hI π s₀) (w : GlobForm s₀), FormOf hI hk c w → FormOf hI hk (r • c) (π r • w) := by
    rintro r c w ⟨f, h, e⟩
    exact ⟨π r • f, by rw [map_smul, h, map_smulₛₗ], by rw [map_smul, Submodule.coe_smul, e]⟩
  have fzero : FormOf hI hk (0 : Cr hI π s₀) 0 := ⟨0, by rw [map_zero, map_zero], by rw [map_zero]; rfl⟩
  have hwd : ∀ (c1 c2 : S'.K hI) (w : GlobForm s₀), FormOf hI hk c1.1 w → FormOf hI hk c2.1 w → u c1 = u c2 := by
    rintro c1 c2 w ⟨f1, h1, e1⟩ ⟨f2, h2, e2⟩
    have hz : cmpForm s₀ (f1 - f2) = 0 := Subtype.ext (by rw [map_sub, Submodule.coe_sub, e1, e2, sub_self]; rfl)
    have hcl := (hG.inj _).2 hz
    rw [map_sub, h1, h2, ← map_sub] at hcl
    have hm := (hR.2 _).1 hcl
    have := hu0 (c1 - c2) (by rw [Submodule.coe_sub]; exact hm)
    rwa [map_sub, sub_eq_zero] at this
  have hex : ∀ c ∈ S'.K hI, ∃ w : GlobForm s₀, FormOf hI hk c w := by
    intro c hc
    have h1 := (ksup S' hR hF c).1 (Submodule.mem_sup_left hc)
    rw [hodgeFiltration_eq_range] at h1
    obtain ⟨f, hf⟩ := h1
    exact ⟨(cmpForm s₀ f).1, f, hf, rfl⟩
  have hexF : ∀ w : GlobForm s₀, ∃ c : S'.K hI, FormOf hI hk c.1 w := by
    intro w
    obtain ⟨f, hf⟩ := hG.surj w
    obtain ⟨c0, hc0⟩ := hR.1 (Form.cl s₀ f)
    have hm : c0 ∈ S'.K hI ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) :=
      (ksup S' hR hF c0).2 (by rw [hc0, hodgeFiltration_eq_range]; exact ⟨f, rfl⟩)
    obtain ⟨k, hk', i, hi, rfl⟩ := Submodule.mem_sup.1 hm
    refine ⟨⟨k, hk'⟩, f, ?_, hf⟩
    rw [← hc0, map_add, (hR.2 i).2 hi, add_zero]
  choose cw hcw using hexF

  let v : GlobForm s₀ →+ CatCoh.H1 S'.F :=
    { toFun := fun w ↦ -S'.r hI (u (cw w))
      map_zero' := by
        rw [hwd (cw 0) 0 0 (hcw 0) fzero, map_zero, map_zero, neg_zero]
      map_add' := fun a b ↦ by
        rw [hwd (cw (a + b)) (cw a + cw b) (a + b) (hcw _) (fadd _ _ _ _ (hcw a) (hcw b)), map_add, map_add,
          neg_add] }
  have hvdef : ∀ w, v w = -S'.r hI (u (cw w)) := fun _ ↦ rfl
  have hv : ∀ (r : R) w, v (π r • w) = r • v w := by
    intro r w
    rw [hvdef, hvdef, hwd (cw (π r • w)) (r • cw w) _ (hcw _) (fsmul r _ _ (hcw w)), map_smul, map_smul, smul_neg]
  have hW : ∀ r, π r = 0 → ∀ m ∈ S'.cocyclesInIdealExtensions, r • m = 0 := by
    intro r hr m hm
    have hrI : r ∈ I := by rw [← hk]; exact hr
    apply Subtype.ext
    funext U V a
    change r • m.1 U V a = 0
    rw [Algebra.smul_def]
    have := Ideal.mul_mem_mul (Ideal.mem_map_of_mem (algebraMap R (S'.F.obj V)) hrI) (hm U V a)
    rw [← sq, map_sq hI, Ideal.zero_eq_bot, Ideal.mem_bot] at this
    exact this
  have trans' := GlobalTheory.T.locIso_transport_cochains_in_ideal R R₀ I hI π hπ hk X₀ s₀
  have hq : ∀ w, ∃ m ∈ S'.cocyclesInIdealExtensions, CatCoh.H1.mk S'.F m = v w := by
    intro w
    obtain ⟨z, z', hz, hmk, -, -⟩ := (trans' S' S' (Sys.LocIso.refl S')).2.2 (-(u (cw w))) (neg_mem (hu (cw w)).1)
    exact ⟨z, hz, by rw [hmk, map_neg]; rfl⟩
  obtain ⟨u', hu's, hu'W, hu'q⟩ := exists_semilinear_lift_of_projective R R₀ π hπ (GlobForm s₀) hG.proj (Z1 S'.F)
    (CatCoh.H1 S'.F) S'.cocyclesInIdealExtensions hW (CatCoh.H1.mk S'.F) v hv hq
  obtain ⟨S'', Φ, θ, hdef, hθ⟩ := GlobalTheory.T.exists_twist_squareZeroSmoothLiftSystem_by_derivationCocycle R R₀ I hI π hπ hk X₀ s₀ hG.par S' u' hu'W hu's

  have hle : K ≤ S''.K hI := by
    intro k hk'
    obtain ⟨c, rfl⟩ := hall k hk'
    obtain ⟨w, hw⟩ := hex c.1 c.2
    obtain ⟨zw, -, hzw⟩ := (trans' S' S'' Φ).1 (u' w) (hu'W w)
    have hmain := GlobalTheory.T.crystallineClass_secondSystem_eq_neg_defect R R₀ I hI π hπ hk X₀ s₀ hG.const S' S'' Φ θ hdef c.1 c.2 w hw zw
      (fun U V a ↦ (hzw U V a).trans (hθ w U V a).symm)
    obtain ⟨z, z2, hzI, hz1, hz2, hzz⟩ := (trans' S' S'' Φ).2.2 (u c) (hu c).1
    have heq : u c = u (cw w) := hwd c (cw w) w hw (hcw w)
    have hsum : CatCoh.H1.mk S'.F (z + u' w) = 0 := by
      rw [map_add, hz1, hu'q w, hvdef, heq, add_neg_cancel]
    obtain ⟨g, hgI, hg⟩ := GlobalTheory.T.exists_ideal_cochain_of_coboundary_constants R R₀ I hI π hπ hk X₀ s₀ hG.const S' (z + u' w)
      (S'.cocyclesInIdealExtensions.add_mem hzI (hu'W w)) hsum
    have h2 : CatCoh.H1.mk S''.F (z2 + zw) = 0 := by
      refine CatCoh.H1.mk_eq_zero.2 ⟨fun W ↦ Φ.φ W (g W), ?_⟩
      funext U V a
      rw [(trans' S' S'' Φ).2.1 g hgI U V a, hg]
      change Φ.φ V (z.1 U V a + (u' w).1 U V a) = z2.1 U V a + zw.1 U V a
      rw [map_add, hzz, hzw]
    rw [map_add] at h2
    have h3 := eq_neg_of_add_eq_zero_left h2
    rw [Sys.K, LinearMap.mem_ker, map_sub, hmain, ← hz2, h3, sub_neg_eq_add, neg_add_cancel]

  have kinf := GlobalTheory.T.squareZeroLiftSystem_filtration_inf_eq_and_full R R₀ I hI π hπ hk X₀ s₀ hG.const
  have hF'' : S''.Full hI := (kinf S' S'').2 hF
  have hsup'' : S''.K hI ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) = S'.K hI ⊔ I • ⊤ := by
    ext c
    rw [ksup S'' hR hF'' c, ksup S' hR hF c]
  have hS''N : IsCompl (S''.K hI) N :=
    (GlobalTheory.T.isCompl_of_agree_mod_sqZero_ideal R I hI (Cr hI π s₀) (S'.K hI) (S''.K hI) N hN hsup'').1 ((kinf S'' S').1)
  refine ⟨S'', le_antisymm ?_ hle⟩
  calc S''.K hI = (K ⊔ N) ⊓ S''.K hI := by rw [hKN.sup_eq_top, top_inf_eq]
    _ = K ⊔ N ⊓ S''.K hI := sup_inf_assoc_of_le N hle
    _ = K := by rw [inf_comm, hS''N.inf_eq_bot, sup_bot_eq]
    _ ≤ K := le_rfl

end GlobalTheory.LiftSys
