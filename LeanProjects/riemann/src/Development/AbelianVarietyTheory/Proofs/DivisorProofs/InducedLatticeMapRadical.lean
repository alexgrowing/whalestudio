import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPinnedOfIsUnf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelGroupLiftExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelLiftFiniteCongruenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCongruenceEndomorphismStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceLatticeFractionalMultipleAgree

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts GlobalTheory.GeoLevel
open GlobalTheory.Member (FinCong IotaOK)
open GlobalTheory.LevelCusp (IsMatch)
open GlobalTheory.Dict (castFr)
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GeoLevel

theorem isLift_inv_mul {D : D7} {V : HSp D} {r : ℕ} {hr : V.rank = r} {β : GL (Fin r) (EAf D)}
    {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)} {g : Formalism.L2.DIV.G0 Pg r} {κ₀ κ : GA D V}
    (h₀ : IsLift V hr β Pg g κ₀) (h : IsLift V hr β Pg g κ) : IsLift V hr β Pg 1 (κ₀⁻¹ * κ) := by
  obtain ⟨a₀, b₀, c₀⟩ := h₀
  obtain ⟨a, b, c⟩ := h
  have e : finR V hr (κ₀⁻¹ * κ) = (finR V hr κ₀)⁻¹ * finR V hr κ := by rw [map_mul, map_inv]
  have hb : finR V hr (κ₀⁻¹ * κ) ∈ Formalism.L2.DIV.St β := by
    rw [e]; exact mul_mem (inv_mem b₀) b
  refine ⟨mul_mem (inv_mem a₀) a, hb, fun w => ?_⟩
  have e2 : (⟨finR V hr (κ₀⁻¹ * κ), hb⟩ : Formalism.L2.DIV.St β) = (⟨finR V hr κ₀, b₀⟩ : Formalism.L2.DIV.St β)⁻¹ * ⟨finR V hr κ, b⟩ :=
    Subtype.ext e
  rw [e2, map_mul, map_inv, c₀, c, inv_mul_cancel]
  rfl

theorem cong_latG_of_finCong {D : D7} {V : HSp D} {M : ℕ} {k : GA D V} (hk : FinCong V M k)
    {a : Fin V.rank → D.host.E} (ha : a ∈ latG V 1) :
    ∃ w ∈ latGHat V 1, (finHom V k).1 *ᵥ finVec V a - finVec V a = M • w := by
  refine ((GlobalTheory.Member.AALev.congruences_agree D V k).2 M ⊤).1 (fun b _ z hz => hk _ ?_) a (by rwa [Submodule.top_smul])
  rw [GlobalTheory.Member.AALev.latHat_eq] at hz ⊢
  exact GlobalTheory.Member.AALev.hat_smul_int _ b hz

theorem exists_induces : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l : Level H) (V : HSp D) (r : ℕ) (hr : V.rank = r) (β : GL (Fin r) (EAf D)) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)), IsLatBasis V hr β → (∀ w, w ∈ Pg ↔ l.Mb ≤ w.asIdeal) → l.Mb.IsRadical → ∀ (Dw : Datum H) (ι₀ : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)), LatEmb V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀) → ∀ g : Formalism.L2.DIV.G0 Pg r, ∃ γ₀, Induces Dw l V hr ι₀ β Pg g γ₀ := by
  intro D H l V r hr β Pg hβ hPg hrad Dw ι₀ hι g
  obtain ⟨κ₀, h₀⟩ := GlobalTheory.T.level_group_lift_exists D H l V r hr β Pg hβ hPg g
  obtain ⟨c1, c2⟩ := GlobalTheory.T.level_lift_finite_congruence D H l V r hr β Pg hβ hPg
  have hk₀ := c1 g κ₀ h₀
  obtain ⟨γ₀, hγ⟩ := GlobalTheory.T.lattice_congruence_endomorphism D V Dw.La _ hι l.M (lt_of_lt_of_le (by norm_num) l.three_le) κ₀ hk₀
  refine ⟨γ₀, fun κ hκ a _ => ?_⟩
  obtain ⟨w', hw', e'⟩ := hγ a
  obtain ⟨w, hw, e⟩ := cong_latG_of_finCong (c2 hrad _ (isLift_inv_mul h₀ hκ))
    (hι.2 ▸ LinearMap.mem_range_self _ a :
      (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀) a ∈ latG V 1)
  refine ⟨(finHom V κ₀).1 *ᵥ w + w', add_mem ((GlobalTheory.Member.AALev.congruences_agree D V κ₀).1.2 hk₀ w hw) hw', ?_⟩
  change (finHom V κ).1 *ᵥ finVec V ((LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀) a) -
    finVec V ((LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀) (γ₀ a)) = _
  have e1 : (finHom V κ).1 = (finHom V κ₀).1 * (finHom V (κ₀⁻¹ * κ)).1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel_left]
  have e3 : (finHom V κ₀).1 *ᵥ (l.M • w) = l.M • (finHom V κ₀).1 *ᵥ w := map_nsmul (finHom V κ₀).1.mulVecLin l.M w
  rw [nsmul_add, ← e', ← e3, ← e, Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← e1, sub_add_sub_cancel]

end GlobalTheory.GeoLevel
