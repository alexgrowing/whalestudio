import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SplitOffBadOfSuppSplitOff
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.MovedLat

open GlobalTheory.AdelicLatMove GlobalTheory.AdLat Formalism.IndefR

variable {D : D7}

theorem hat_hLat (V : HSp D) (g : Bridge.Gf V) :
    (hat D.host.F (Bridge.hLat V g : Set (Fin V.rank → D.host.E)) : Set (Fin V.rank → RA D.host.F D.host.E)) =
      g.1.1.mulVec '' (hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E))) := by
  obtain ⟨-, -, hfg, hsp, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  obtain ⟨Λ, hΛ, -, -, h⟩ := exists_lattice_latOf D.host.F D.host.E V.rank (GlobalTheory.Member.latC V) g.1 hfg hsp
  rw [GlobalTheory.RepsCompare.coe_hLat, ← hΛ, h]

theorem hLat_one (V : HSp D) : Bridge.hLat V 1 = GlobalTheory.Member.latC V := by
  obtain ⟨-, -, hfg, hsp, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  apply SetLike.coe_injective
  rw [GlobalTheory.RepsCompare.coe_hLat]
  ext x
  rw [SetLike.mem_coe, ← (hat_rational_points_and_approx D.host.F D.host.E _ _ hfg hsp).1]
  simp [GlobalTheory.AdLat.latOf]

theorem isSelfDualC_hLat (V : HSp D) (g : Bridge.Gf V) : IsSelfDualC V (Bridge.hLat V g) := by
  refine ⟨GlobalTheory.RepsCompare.isLattice_hLat V g, fun v => ?_⟩
  obtain ⟨-, -, hfg, hsp, c2, -, -, gh, gd, -, hsd⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have key := latOf_selfDual D.host.F D.host.E V.rank (GlobalTheory.Member.latC V) (GlobalTheory.Member.cF D) V.gramᵀ 1 g.1 hfg hsp c2 gh gd
    one_ne_zero hsd (GlobalTheory.RepsCompare.isUnA_gf V g)
  rw [← SetLike.mem_coe, GlobalTheory.RepsCompare.coe_hLat, ← key, ← GlobalTheory.RepsCompare.coe_hLat]
  refine forall_congr' fun y => imp_congr_right fun _ => ?_
  have e : ∑ i, ∑ j, star (y i) * V.gram i j * v j = ∑ a, ∑ b, v a * V.gramᵀ a b * GlobalTheory.Member.cF D (y b) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    change star (y b) * V.gram b a * v a = v a * V.gram b a * star (y b)
    ring
  rw [e, FractionalIdeal.mem_one_iff]

theorem mulVec_mem_hatL (V : HSp D) (g : GA D V) (Λ Λ' : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (H : ∀ z ∈ hat D.host.F (Λ : Set (Fin V.rank → D.host.E)),
      (finHom V g).1 *ᵥ z ∈ hat D.host.F (Λ' : Set (Fin V.rank → D.host.E)))
    (x : Fin V.rank → EAf D) (hx : x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) :
    (Formalism.L2.Theta.mt V g).map (toEAf D) *ᵥ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ' := by
  have h := GlobalTheory.PrincInLevel.swap_mem_hatL Λ' _ (H _ (GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ x hx))
  convert h using 1
  funext i
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, AlgEquiv.apply_symm_apply]
  rfl

theorem actO_mem (S T : HSp D) (g : GA D S) (h : GA D T)
    (ΛS ΛS' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT ΛT' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hS : ∀ z ∈ hat D.host.F (ΛS : Set (Fin S.rank → D.host.E)),
      (finHom S g).1 *ᵥ z ∈ hat D.host.F (ΛS' : Set (Fin S.rank → D.host.E)))
    (hT : ∀ z ∈ hat D.host.F (ΛT : Set (Fin T.rank → D.host.E)),
      (finHom T h).1 *ᵥ z ∈ hat D.host.F (ΛT' : Set (Fin T.rank → D.host.E)))
    (u : WO S T)
    (hu : u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) :
    actO S T g h u ∈
      latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True := by
  induction hu using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hu
    have e := rankOne_pure S T a s t 1 α
    rw [mul_one] at e
    rw [← e, actO_rankOne]
    exact rankOne_mem_latO S T ΛS' ΛT' a ha _
      (mulVec_mem_hatL S g ΛS ΛS' hS _ (pure_mem_hatL ΛS 1 (one_mem _) s hs)) _
      (mulVec_mem_hatL T h ΛT ΛT' hT _ (pure_mem_hatL ΛT α hα t ht))
  | zero => simp only [actO, Matrix.mul_zero, Matrix.zero_mul]; exact zero_mem _
  | add y z _ _ hy hz => simp only [actO, Matrix.mul_add, Matrix.add_mul] at hy hz ⊢; exact add_mem hy hz
  | neg y _ hy => simp only [actO, Matrix.mul_neg, Matrix.neg_mul] at hy ⊢; exact neg_mem hy

theorem fwd (V : HSp D) (g : GA D V) : ∀ z ∈ hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)),
    (finHom V g).1 *ᵥ z ∈ hat D.host.F (Bridge.hLat V (FWT.fin V g) : Set (Fin V.rank → D.host.E)) := by
  intro z hz
  rw [← SetLike.mem_coe, hat_hLat]
  exact ⟨z, hz, rfl⟩

theorem bwd (V : HSp D) (g : GA D V) :
    ∀ z ∈ hat D.host.F (Bridge.hLat V (FWT.fin V g) : Set (Fin V.rank → D.host.E)),
    (finHom V g⁻¹).1 *ᵥ z ∈ hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) := by
  intro z hz
  rw [← SetLike.mem_coe, hat_hLat] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  change (finHom V g⁻¹).1 *ᵥ ((finHom V g).1 *ᵥ y) ∈ _
  rw [Matrix.mulVec_mulVec, map_inv, Units.inv_mul, Matrix.one_mulVec]
  exact hy

theorem latG_eq (W : HSp D) (k : GA D W) : Formalism.L2.Pj.latG W k = Submodule.span (𝓞 D.host.E)
    {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v ∈ Bridge.hLat W (FWT.fin W k), w = a • v} := by
  have key : ∀ v, Formalism.L2.Pj.finVec W v ∈ Formalism.L2.Pj.gLat W k ↔ v ∈ Bridge.hLat W (FWT.fin W k) := by
    intro v
    rw [← SetLike.mem_coe, GlobalTheory.RepsCompare.coe_hLat, Formalism.L2.Pj.gLat, (GlobalTheory.Member.latHat_eq_hat_and_gram D W).1]
    exact Iff.rfl
  unfold Formalism.L2.Pj.latG
  simp only [key]

theorem moved_lattices : ∀ (D : D7) (V W : HSp D) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)), (ΛV : Set (Fin V.rank → D.host.E)) = L0c D V → (ΛW : Set (Fin W.rank → D.host.E)) = L0c D W → IsSelfDualC V ΛV → IsSelfDualC W ΛW → ∀ (h : GA D V) (k : GA D W), IsSelfDualC V (Formalism.IndefR.Bridge.hLat V (Formalism.IndefR.FWT.fin V h)) ∧ IsSelfDualC W (Formalism.IndefR.Bridge.hLat W (Formalism.IndefR.FWT.fin W k)) ∧ (∀ u : WO V W, u ∈ (latO V W (Formalism.IndefR.Bridge.hLat V (Formalism.IndefR.FWT.fin V h) : Set (Fin V.rank → D.host.E)) (Formalism.IndefR.Bridge.hLat W (Formalism.IndefR.FWT.fin W k) : Set (Fin W.rank → D.host.E)) fun _ => True) ↔ ∃ u₀ ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True), u = actO V W h k u₀) ∧ Formalism.L2.Pj.latG W k = Submodule.span (𝓞 D.host.E) {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v ∈ Formalism.IndefR.Bridge.hLat W (Formalism.IndefR.FWT.fin W k), w = a • v} ∧ Formalism.IndefR.Bridge.hLat V 1 = ΛV ∧ Formalism.IndefR.Bridge.hLat W 1 = ΛW := by
  intro D V W ΛV ΛW hV hW _ _ h k
  obtain rfl : ΛV = GlobalTheory.Member.latC V := SetLike.coe_injective (hV.trans (GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq V).symm)
  obtain rfl : ΛW = GlobalTheory.Member.latC W := SetLike.coe_injective (hW.trans (GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq W).symm)
  refine ⟨isSelfDualC_hLat V _, isSelfDualC_hLat W _, fun u => ⟨fun hu => ?_, ?_⟩, latG_eq W k, hLat_one V, hLat_one W⟩
  · exact ⟨_, actO_mem V W h⁻¹ k⁻¹ _ _ _ _ (bwd V h) (bwd W k) u hu, (actO_actO_inv V W h k u).symm⟩
  · rintro ⟨u₀, hu, rfl⟩
    exact actO_mem V W h k _ _ _ _ (fwd V h) (fwd W k) u₀ hu

end GlobalTheory.MovedLat
