import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqClassSumOfLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisationNonarchimedeanCompatStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftUnfold

theorem exists_fin_mul_real {D : D7} (V : HSp D) (u : GA D V) : ∃ k ∈ GfC V, ∃ a ∈ GinfC V, u = k * a ∧ fin V k = fin V u := by
  obtain ⟨h1, h2⟩ := GlobalTheory.Mass.parts_spec D.sp.cm.sig V.gram
  obtain ⟨k, k1, k2⟩ := h2 1 (finHom V u)
  have hk : k ∈ HR (AF D.host.F) D.sp.cm.sig V.gram :=
    (h1 k).2 ⟨k1 ▸ one_mem _, k2 ▸ ((h1 _).1 u.2).2⟩
  let k' : GA D V := ⟨k, hk⟩
  have e : finHom V k' = finHom V u := k2
  refine ⟨k', k1, k'⁻¹ * u, ?_, (mul_inv_cancel_left _ _).symm, Subtype.ext e⟩
  show finHom V (k'⁻¹ * u) = 1
  rw [map_mul, map_inv, e, inv_mul_cancel]

theorem integrand_right {H G' Gf W X : Type} [Group H] [Group G'] [Group Gf] [AddCommGroup W] [Module ℂ W]
    (om : H × G' →* Module.End ℂ (X → ℂ)) (ρ : H →* Module.End ℂ W) (p : H →* Gf) (L : W →ₗ[ℂ] (X → ℂ)) (f : Gf → W)
    (u k a : H) (hu : u = k * a) (c : ℂˣ) (hk : ρ k⁻¹ = 1) (ha : p a = 1) (hf : ∀ z, f (z * p k) = (c : ℂ) • f z)
    (hLk : ∀ w, om (k, 1) (L w) = (c : ℂ)⁻¹ • L w) (hLa : ∀ w, om (a, 1) (L w) = L (ρ a w)) (x : H) (g : G') :
    om (x * u, g) (L (ρ (x * u)⁻¹ (f (p (x * u))))) = om (x, g) (L (ρ x⁻¹ (f (p x)))) := by
  subst hu
  have e1 : (x * (k * a), g) = (x, g) * (k, (1 : G')) * (a, (1 : G')) := by simp [mul_assoc]
  have e2 : ρ a * ρ (x * (k * a))⁻¹ = ρ x⁻¹ := by
    rw [← map_mul, show a * (x * (k * a))⁻¹ = k⁻¹ * x⁻¹ by group, map_mul, hk, one_mul]
  rw [e1, map_mul om, map_mul om, Module.End.mul_apply, Module.End.mul_apply, hLa, ← Module.End.mul_apply (ρ a), e2, hLk,
    map_mul p, map_mul p, ha, mul_one, hf, map_smul (ρ x⁻¹), map_smul L, smul_smul, inv_mul_cancel₀ c.ne_zero, one_smul]

theorem form_right {H Γ W : Type} [Group H] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ι : Γ →* H)
    (ρ : Γ →* Module.End ℂ W) {J : Subgroup H} {χ : J →* ℂˣ} {f : H → W} (hf : f ∈ Bridge.AdForms ι ρ J χ) (k : J) (z : H) :
    f (z * k) = (χ k : ℂ) • f z := by
  have := hf 1 z k
  rwa [map_one, map_one, one_mul] at this

theorem integral_theta {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om) (hs : S.SigOK)
    (hp : S.IsPosDef) (c : CoefA S) (hc : c.Is) (β : GL (Fin S.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ S.rank)
    (hL : ∀ k, k ∈ Formalism.L2.DIV.lev D.sp.cm S.gram β L ↔ k ∈ Formalism.L2.DIV.lev D.sp.cm S.gram β (Lev.flag1L L))
    {f : Bridge.Gf S → c.W} (hf : f ∈ Bridge.AdForms (Bridge.ratF S) c.coef.ρ (levEnv S β L).J (levEnv S β L).χ)
    (Λ : c.W →ₗ[ℂ] (WO S T → ℂ)) (hΛ : ∀ w, IsThetaFunO ψ S T (Λ w))
    (hΛa : ∀ a ∈ GinfC S, ∀ w, om (a, 1) (Λ w) = Λ (c.ρ a w))
    (hΛk : ∀ k ∈ GfC S, ∀ hk : fin S k ∈ (levEnv S β L).J, ∀ w,
      om (k, 1) (Λ w) = (((levEnv S β L).χ ⟨fin S k, hk⟩ : ℂˣ) : ℂ)⁻¹ • Λ w)
    {ν : Measure (GA D S)} {𝓕 : Set (GA D S)} (hν : IsMeasDef S (Formalism.L2.DIV.lev D.sp.cm S.gram β L) ν 𝓕)
    (J' : Subgroup (Bridge.Gf S)) (Cl : Type) [Fintype Cl] (h : Cl → GA D S) (hle : J' ≤ (levEnv S β L).J)
    (hN : J'.relIndex (levEnv S β L).J ≠ 0) (hy : Bridge.IsReps (Bridge.ratF S) J' (fun k => fin S (h k)))
    (hh : ∀ k, h k ∈ GfC S) (g : GA D T) :
    ∫ x in 𝓕, thetaKO om x g (Λ (c.ext f x)) ∂ν = ∑ k, ((J'.relIndex (levEnv S β L).J : ℕ) : ℂ)⁻¹ *
      ((Nat.card (Bridge.stab (Bridge.ratF S) J' (fin S (h k))) : ℕ) : ℂ)⁻¹ * thetaKO om (h k) g (Λ (f (fin S (h k)))) := by
  rw [GlobalTheory.ClsInt.integral_eq_classSum_of_le D S β L ν 𝓕 hp hs hν hL J' Cl h hle hN hy hh
    (fun x => thetaKO om x g (Λ (c.ext f x))) ?_ ?_]
  · exact Finset.sum_congr rfl fun k _ => by rw [ext_fin c hc f (hh k)]
  · intro γ hγ x
    have e : (γ * x, g) = ((γ, 1) : GA D S × GA D T) * (x, g) := by rw [Prod.mk_mul_mk, one_mul]
    simp only [thetaKO]
    rw [GlobalTheory.ThetaIntegrand.ext_invariant c hf γ hγ, e, map_mul]
    exact hom.om_aut γ hγ 1 (one_mem _) _ (hom.om_pres _ _ (hΛ _))
  · intro u hu x
    refine (exists_fin_mul_real S u).elim fun k hk0 => hk0.2.elim fun a ha0 => ?_
    have hk := hk0.1
    have ha := ha0.1
    have e := ha0.2.2
    have hk' : fin S k ∈ (levEnv S β L).J := by rw [e]; exact hu
    have h1 : c.ρ k⁻¹ = 1 := hc.1 _ (inv_mem hk)
    have h2 : (finHom S).rangeRestrict a = 1 := Subtype.ext (MonoidHom.mem_ker.1 ha)
    have h3 := form_right (Bridge.ratF S) c.coef.ρ hf ⟨fin S k, hk'⟩
    have h4 := integrand_right om c.ρ (finHom S).rangeRestrict Λ f u k a ha0.2.1 ((levEnv S β L).χ ⟨fin S k, hk'⟩)
      h1 h2 h3 (hΛk k hk hk') (hΛa a ha) x g
    exact congrFun h4 0

set_option maxHeartbeats 1000000 in

theorem thF_eq_classSum : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.Char F → ∀ (i : Fin D.R.m) (t : T0) (K' : Type) [Field K'] (σ' : K' →+* ℂ) (c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W) (Cl : Type) [Fintype Cl] (h : Cl → GA D (Vc D i)) (bad : ℕ) (J' : Subgroup (Bridge.Gf (Vc D i))) (Lh : Cl → Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)) (gam : Cl → ℕ) (vol : K'), VStd D i → RepsR R i t h bad J' Lh gam vol → ∀ (y : (R.HV i t).H) (x : Cl → VsV D i K'), Place R i t h c0' y x → ∀ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (g : GA D (Wc D i)), R.thF i t y (fun ρ => u ρ) g = ∑ k, σ' (vol * ((gam k : K'))⁻¹) * thetaKO (R.ωP i t) (h k) g (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ u) (c0' (x k)))) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i t K' _ σ' c0' Cl _ h bad J' Lh gam vol hV hrep y x hpl u g
  refine (hR.thP.thF i t).elim fun thP hPF => ?_
  have hle := hrep.2.2.1
  have hN := hrep.2.2.2.1
  have hvol := hrep.2.2.2.2.1
  have hy := hrep.2.2.2.2.2.1
  have hk := hrep.2.2.2.2.2.2
  have hx : (R.HV i t).e y ∈ Bridge.AdForms (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ
      (levEnv _ (R.βV i) (R.datVt i t)).J (levEnv _ (R.βV i) (R.datVt i t)).χ :=
    (hR.models.HV i t).2.1.le (LinearMap.mem_range_self _ y)
  have hfin : ∀ k ∈ GfC (Vc D i), ∀ hk : fin (Vc D i) k ∈ levJ R i t, ∀ P, R.ωP i t (k, 1) (R.ptP i t P) =
      (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ ⟨fin (Vc D i) k, hk⟩ : ℂˣ) : ℂ)⁻¹ • R.ptP i t P := fun k hk hk' =>
    GlobalTheory.FiniteFock.om_pureTensorO_of_finite R.ψ R.θ (Vc D i) (Wc D i) _ _ (R.ωP i t) hR.models.inf
      (hR.thP.ωP i t) _ _ _ _ _ (hR.thP.pt_theta i t) k hk 1 (one_mem _) _
      (GlobalTheory.T.realisation_nonarchimedean_compat D G Pl0 T0 A Ks R F hR i t k hV hk hk')
  have key := integral_theta (hR.thP.ωP i t) (D.sp.V_sig _) (hR.models.vpos i) (R.cV i) (hR.models.cV i) (R.βV i)
    (R.datVt i t) (fun _ => Iff.rfl) hx
    (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A)))
      (R.vP i t) ∘ₗ R.ioP i (PiTensorProduct.tprod ℂ u)) (fun w => hR.thP.pt_theta i t _)
    (fun a ha w => (hR.thP.ioP i t).1 a ha _ w) (fun k hk hk' w => hfin k hk hk' _)
    (hR.models.νV i t) J' Cl h hle hN hy (fun k => (hk k).1.1) g
  have h1 := congrFun (hPF.2 y u) g
  have h2 := hPF.1.eq ((R.extV i t).rangeRestrict y) (PiTensorProduct.tprod ℂ u) g
  refine h1.trans (h2.trans (Eq.trans ?_ (key.trans (Finset.sum_congr rfl fun k _ => ?_))))
  · rfl
  have h3 : σ' (vol * ((gam k : K'))⁻¹) = ((J'.relIndex (levJ R i t) : ℕ) : ℂ)⁻¹ *
      ((Nat.card (Bridge.stab (Bridge.ratF (Vc D i)) J' (fin (Vc D i) (h k))) : ℕ) : ℂ)⁻¹ := by
    rw [map_mul σ', hvol, map_inv₀ σ', map_inv₀ σ', map_natCast σ', map_natCast σ', (hk k).2.2]
  rw [h3, ← hpl k]
  rfl

end GlobalTheory.LiftUnfold
