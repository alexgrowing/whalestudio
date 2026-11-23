import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCompletedIsometryInducingHalfLevelAutomorp
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsAdelicUnitaryOfLatticeIsometries
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryLatticeRationalTranslateInvariance
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetOneAddSubOne

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.CompRat
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfLift

theorem exists_isometry_agreeing {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H) (l : Level H) (g g' : Dw.La →ₗ[𝓞 E] Dw.La)
    (h : ∀ a, g' (g a) - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) ∧
      g (g' a) - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) :
    ∃ s : Sim Dw, (∀ n, s.ν n = 1) ∧
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), Dw.ModN l.M (s.f l.M a - g a) := by
  have hle : ∀ f : Dw.La →ₗ[𝓞 E] Dw.La, l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) ≤
      (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).comap f := fun f => by
    rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  obtain ⟨s, h1, h2, -⟩ := GlobalTheory.LevelIsometry.exists_isometry_inducing E H Dw l
    (LinearEquiv.ofLinear (Submodule.mapQ _ _ g (hle g)) (Submodule.mapQ _ _ g' (hle g'))
      (Submodule.linearMap_qext _ (LinearMap.ext fun a => (Submodule.Quotient.eq _).2 (h a).2))
      (Submodule.linearMap_qext _ (LinearMap.ext fun a => (Submodule.Quotient.eq _).2 (h a).1)))
  refine ⟨s, h1, fun a ha => ?_⟩
  have key : ∀ x, s.f l.M x - g x ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := fun x =>
    (Submodule.Quotient.eq _).1 (h2 x)
  refine Submodule.smul_induction_on ha (fun r hr y _ => ?_) fun y z hy hz => ?_
  · rw [map_smul, map_smul, ← smul_sub]
    exact GlobalTheory.LevelIsometry.modN_smul_of_mem_smul Dw l hr (key y)
  · rw [map_add, map_add, add_sub_add_comm]
    exact GlobalTheory.SimAlg.modN_add hy hz

theorem add_sub_eq_nsmul {A : Type} [AddCommGroup A] (N : ℕ) (x e w : A) :
    x + N • e + N • w - x = N • (e + w) := by
  rw [smul_add]
  abel

theorem exists_unitary_inducing : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (V : HSp D) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), GlobalTheory.Member.IotaOK Dw V ι → ∀ g g' : Dw.La →ₗ[𝓞 D.host.E] Dw.La, (∀ a, g' (g a) - a ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La) ∧ g (g' a) - a ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) → ∃ u ∈ GfC V, gLat V u = latHat V ∧ ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ w ∈ latGHat V 1, (finHom V u).1.mulVec (finVec V (ι a)) - finVec V (ι (g a)) = (l.M : ℕ) • w := by
  intro D H Dw l V ι hι g g' h
  obtain ⟨s, hν, hs⟩ := exists_isometry_agreeing Dw l g g' h
  obtain ⟨κ, hκ, hκs⟩ := GlobalTheory.ShortMove.exists_adelic_of_isometry D V H Dw ι hι.emb hι.isom s hν
  obtain ⟨b, hb, u, hu, e⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 κ
  have hb' : finHom V b = 1 := hb
  have hf : finHom V u = finHom V κ := by rw [e, map_mul, hb', one_mul]
  obtain ⟨-, m2, -, m4⟩ := GlobalTheory.Member.latG_move D V
  have hL : latG V 1 = latG V u := GlobalTheory.Member.LatMove.lat_eq_of_hat_eq V (hκ.symm.trans (m2 u κ hf).2.symm)
  have hc := m4 1 u hL
  rw [inv_one, one_mul] at hc
  refine ⟨u, hu, GlobalTheory.MarkDet.gLat_eq_of_finCong hc, fun a ha => ?_⟩
  obtain ⟨c, hc'⟩ := hs a ha
  obtain ⟨w, hw, ew⟩ := hκs l.M (lt_of_lt_of_le (by norm_num) l.three_le) a
  have hm : finVec V (ι c) ∈ latGHat V 1 :=
    (GlobalTheory.Member.LatMove.mem_lat_iff V 1 _).1 (hι.emb.2 ▸ LinearMap.mem_range_self ι c)
  refine ⟨finVec V (ι c) + w, add_mem hm hw, ?_⟩
  have h2 : finVec V (ι (s.f l.M a)) = finVec V (ι (g a)) + l.M • finVec V (ι c) := by
    rw [sub_eq_iff_eq_add'.1 hc', map_add, map_nsmul]
    funext i
    simp only [finVec, Pi.add_apply, Pi.smul_apply, TensorProduct.tmul_add]
    congr 1
    exact map_nsmul (TensorProduct.mk D.host.F (Af D.host.F) D.host.E 1) _ _
  rw [hf, ew, h2]
  exact add_sub_eq_nsmul _ _ _ _

end GlobalTheory.HalfLift
