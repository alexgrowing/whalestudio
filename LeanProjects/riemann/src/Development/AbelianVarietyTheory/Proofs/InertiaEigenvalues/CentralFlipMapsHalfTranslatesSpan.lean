import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFlipDet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlipIdxNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdemSumMulOfSubset
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmVacuumEqSplitFacSmulSum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.FlipTranslates

open GlobalTheory.SplitScalar

variable {D : D7}

theorem symplO_add_right' (V W : HSp D) (x y y' : WO V W) :
    symplO V W x (y + y') = symplO V W x y + symplO V W x y' := by
  rw [← symplOH_add_self V W x (y + y'), ← symplOH_add_self V W x y, ← symplOH_add_self V W x y',
    symplOH_add_right]
  abel

theorem symplO_nsmul_right (V W : HSp D) (x y : WO V W) (k : ℕ) :
    symplO V W x (k • y) = k • symplO V W x y := by
  induction k with
  | zero => rw [zero_nsmul, zero_nsmul, symplO_zero_right]
  | succ k ih => rw [succ_nsmul, symplO_add_right', ih, succ_nsmul]

theorem cA_invol (x : AE D) : cA D (cA D x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, hx, hy]
  | tmul a x =>
    change a ⊗ₜ[D.host.F] star (star x) = _
    rw [star_star]

theorem flipElt_mul_of_half {e eT x : AE D} (m : ℕ) (hx : e * x = x) (h1 : e * eT = eT) (h3 : e * e = e)
    (h5 : e * cA D eT = 0) : flipElt eT m * x = (e - eT) * x + (m : AE D) * (eT * x) := by
  unfold flipElt
  linear_combination (-(cA D eT * (incA D ((m : D.host.E)⁻¹) - 1) + 1 - e)) * hx +
    (incA D ((m : D.host.E)⁻¹) - 1) * x * h5 - x * h3

theorem fix_of_idemSum (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) {Λ : AddSubgroup (WO V W)}
    (hst : ∀ a : AE D, a * a = a → ∀ u ∈ Λ, a • u ∈ Λ)
    {f₀ : WO V W → ℂ} (hf : IsLatVac (heisO ψ V W) Λ f₀) {ι : Type} (S : Finset ι) (g : ι → AE D) (E : AE D)
    (hEs : E = ∑ i ∈ S, g i) (hg : ∀ i ∈ S, IsSplitIdem D (g i)) (hgE : ∀ i ∈ S, E * g i = g i)
    (hE : E * cA D E = 0) {u : WO V W} (hu : u ∈ Λ) (hhu : IsHalf E u) :
    heisO ψ V W u f₀ = f₀ := by
  have hdec : u = ∑ i ∈ S, g i • u := by
    ext a b
    rw [Matrix.sum_apply]
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [← Finset.sum_mul, ← hEs, hhu a b]
  have horth : ∀ i ∈ S, cA D (g i) * E = 0 := by
    intro i hi
    have h1 : cA D (g i) = cA D (g i) * cA D E := by rw [← map_mul, mul_comm, hgE i hi]
    rw [h1, mul_assoc, mul_comm (cA D E) E, hE, mul_zero]
  have key : ∀ S' : Finset ι, S' ⊆ S → heisO ψ V W (∑ i ∈ S', g i • u) f₀ = f₀ := by
    intro S'
    induction S' using Finset.induction_on with
    | empty => intro _; rw [Finset.sum_empty, heisO_zero]
    | insert j S' hj ih =>
      intro hS'
      have hjS : j ∈ S := hS' (Finset.mem_insert_self j S')
      have hS'S : S' ⊆ S := fun x hx => hS' (Finset.mem_insert_of_mem hx)
      rw [Finset.sum_insert hj]
      have hhalf : IsHalf E (∑ i ∈ S', g i • u) := by
        intro a b
        rw [Matrix.sum_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        simp only [Matrix.smul_apply, smul_eq_mul]
        rw [← mul_assoc, hgE i (hS'S hi)]
      have hsp := hg j hjS
      rw [heisO_add_of_orth ψ V W (symplO_eq_zero V W (horth j hjS) (isHalf_smul hsp.1 u) hhalf), ih hS'S]
      exact hf.2 (g j) hsp (g j • u) (hst _ hsp.1 u hu) (isHalf_smul hsp.1 u)
  rw [hdec]
  exact key S subset_rfl

set_option maxHeartbeats 1000000 in

theorem flip_translates : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (m : ℕ) (eT : AE D) (z : GA D V) (s : ℂ) (Y : Finset (WO V W)), IsIdemSum eT T → Odd m → Nat.Coprime m (GlobalTheory.Tow.badN D) → (∀ PP ∈ T, ((m : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → Formalism.L2.Theta.mt V z = flipElt eT m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) → s ≠ 0 → (∀ y ∈ Y, IsHalf (cA D eT) y ∧ m • y ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True)) → om (z⁻¹, 1) f₀ = s • ∑ y ∈ Y, heisO ψ V W y f₀ → ∀ (M u : ℕ) (e e' : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (O : Subring ℂ), M = m * u → (∀ PP ∈ T, ((u : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → IsIdemSum e P → T ⊆ P → e' = e - eT + cA D eT → zeta M ∈ O → ∀ f ∈ trSp ψ V W ΛV ΛW f₀ e M O, ∃ F ∈ trSp ψ V W ΛV ΛW f₀ e' M O, om (z, 1) (s • F) = f := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hV T m eT z s Y hT hm hmb hmT hz hs hY hom M u e e' P O hM hu he hTP he' hO
  subst he'
  have hvac := hV.2.2.2.2.2.2.2.2
  have hweil := hV.1.weil
  have hth : IsThetaFunO ψ V W f₀ := hvac.2.theta
  have hlat := hvac.2.lat
  obtain ⟨⟨es, hes, hsum⟩, h4⟩ := hT
  have hT' : IsIdemSum eT T := ⟨⟨es, hes, hsum⟩, h4⟩
  have h1 : e * eT = eT := GlobalTheory.Tow.idemSum_mul_of_subset hT' he hTP
  have h2 : eT * eT = eT := GlobalTheory.Tow.idemSum_mul_of_subset hT' hT' subset_rfl
  have h3 : e * e = e := GlobalTheory.Tow.idemSum_mul_of_subset he he subset_rfl
  have h5 : e * cA D eT = 0 := by
    have h := he.2
    calc e * cA D eT = e * cA D (e * eT) := by rw [h1]
      _ = e * cA D e * cA D eT := by rw [map_mul, mul_assoc]
      _ = 0 := by rw [h, zero_mul]
  have h6 : cA D eT * cA D eT = cA D eT := by rw [← map_mul, h2]
  have hm0 : m ≠ 0 := hm.pos.ne'
  have hcc : cA D (cA D eT) = eT := GlobalTheory.FlipTranslates.cA_invol eT
  have hst : ∀ a : AE D, a * a = a → ∀ w ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E))
      (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True), a • w ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E))
      (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) := fun a ha w hw => idem_smul_mem ha w hw
  have hesT : ∀ PP ∈ T, eT * es PP = es PP := by
    intro PP hPP
    rw [hsum, Finset.sum_mul, Finset.sum_eq_single_of_mem PP hPP]
    · exact (hes PP hPP).1.1
    · intro Q hQ hne
      exact GlobalTheory.Tow.idemAt_orth (hes Q hQ) (hes PP hPP) hne

  have hfixT : ∀ w ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True),
      IsHalf eT w → heisO ψ V W w f₀ = f₀ := fun w hw hhw =>
    GlobalTheory.FlipTranslates.fix_of_idemSum ψ V W hst hlat T es eT hsum (fun PP hPP => (hes PP hPP).1) hesT h4 hw hhw
  have hfixC : ∀ w ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True),
      IsHalf (cA D eT) w → heisO ψ V W w f₀ = f₀ := fun w hw hhw =>
    GlobalTheory.FlipTranslates.fix_of_idemSum ψ V W hst hlat T (fun PP => cA D (es PP)) (cA D eT)
      (by rw [hsum, map_sum]) (fun PP hPP => isSplitIdem_conj (hes PP hPP).1)
      (fun PP hPP => by rw [← map_mul, hesT PP hPP]) (by rw [hcc, mul_comm, h4]) hw hhw
  have hT0 : u = 0 → eT = 0 := by
    intro hu0
    have hTe : T = ∅ := by
      by_contra hne
      obtain ⟨PP, hPP⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      apply hu PP hPP
      rw [hu0, Nat.cast_zero]
      exact zero_mem _
    rw [hsum, hTe, Finset.sum_empty]
  have hmt1 : Formalism.L2.Theta.mt W 1 = 1 := by unfold Formalism.L2.Theta.mt; rw [map_one]; rfl
  have hidem : (e - eT) * (e - eT) = e - eT := by linear_combination h3 - 2 * h1 + h2
  let Φ : Module.End ℂ (WO V W → ℂ) := s⁻¹ • om (z⁻¹, 1)
  have hgen : ∀ y : WO V W, IsHalf e y → M • y ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E))
      (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) →
      Φ (heisO ψ V W y f₀) ∈ trSp ψ V W ΛV ΛW f₀ (e - eT + cA D eT) M O := by
    intro y hy hMy
    by_cases hf0 : f₀ = 0
    · have h0 : heisO ψ V W y f₀ = 0 := by
        subst hf0
        funext w
        simp [heisO]
      rw [h0, map_zero]
      exact zero_mem _
    set lam : WO V W := m • (eT • y) with hlam
    set b : WO V W := (e - eT) • y with hb
    have hay : actO V W z⁻¹ 1 y = b + lam := by
      show HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W 1) y) (Formalism.L2.Theta.mt V z⁻¹⁻¹) = _
      rw [inv_inv, hz, hmt1, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]
      ext i j
      rw [Matrix.smul_apply, smul_eq_mul, GlobalTheory.FlipTranslates.flipElt_mul_of_half m (hy i j) h1 h3 h5,
        Matrix.add_apply, hb, hlam]
      simp only [Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul]
    have hlamT : IsHalf eT lam := isHalf_nsmul (isHalf_smul h2 y) m
    have hlam0 : u = 0 → lam = 0 := by
      intro hu0
      rw [hlam, hT0 hu0, zero_smul, smul_zero]
    have hlamΛ : lam ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E))
        (fun _ => True) := by
      by_cases hu0 : u = 0
      · rw [hlam0 hu0]; exact zero_mem _
      have huE : (u : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr hu0
      have hinc : incA D ((u : D.host.E)⁻¹) * (u : AE D) = 1 := by
        rw [← map_natCast (incA D) u, ← map_mul, inv_mul_cancel₀ huE, map_one]
      have heq : lam = (eT * incA D ((u : D.host.E)⁻¹)) • (M • y) := by
        ext i j
        simp only [hlam, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, hM, Nat.cast_mul]
        linear_combination (-((m : AE D) * eT * y i j)) * hinc
      rw [heq]
      refine GlobalTheory.LatticeStable.smul_mem_latO D V W _ _ _ _ ?_ _ hMy
      rw [hsum, Finset.sum_mul, map_sum]
      refine AddSubgroup.sum_mem _ fun PP hPP => ?_
      have hx := (hes PP hPP).2 ((u : ℕ) : 𝓞 D.host.E) (Nat.cast_ne_zero.mpr hu0)
      have hc : (((u : ℕ) : 𝓞 D.host.E) : D.host.E) = (u : D.host.E) := by simp
      rw [hc] at hx
      by_contra hn
      exact hu PP hPP (hx.2 hn)
    have hfl : heisO ψ V W lam f₀ = f₀ := hfixT lam hlamΛ hlamT
    have hbh : IsHalf (e - eT) b := isHalf_smul hidem y
    have hblam : symplO V W b lam = 0 := by
      refine symplO_eq_zero V W ?_ hbh hlamT
      rw [map_sub]
      linear_combination (-cA D e) * h1 + eT * he.2 - h4
    have hby : ∀ y'' ∈ Y, symplO V W b y'' = 0 := by
      intro y'' hy''
      refine symplO_eq_zero V W ?_ hbh (hY y'' hy'').1
      rw [← map_mul, sub_mul, h1, h2, sub_self, map_zero]
    have hpow : ∀ y'' ∈ Y, ψ (symplO V W lam y'') ^ m = 1 := by
      intro y'' hy''
      have hmy := hfixC (m • y'') (hY y'' hy'').2 (isHalf_nsmul (hY y'' hy'').1 m)
      have h := heisO_comm ψ V W lam (m • y'') f₀
      rw [hmy, hfl, hmy, symplO_nsmul_right, AddChar.map_nsmul_eq_pow] at h
      obtain ⟨w, hw⟩ := Function.ne_iff.mp hf0
      have h' := congrFun h w
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h' hw
      have h'' : (ψ (symplO V W lam y'') ^ m - 1) * f₀ w = 0 := by linear_combination -h'
      rcases mul_eq_zero.mp h'' with h0 | h0
      · exact sub_eq_zero.mp h0
      · exact absurd h0 hw
    have hcO : ∀ y'' ∈ Y, ψ (symplO V W lam y'') ∈ O := by
      intro y'' hy''
      by_cases hM0 : M = 0
      · have hu0 : u = 0 := by
          rw [hM] at hM0
          rcases mul_eq_zero.mp hM0 with h | h
          · exact absurd h hm0
          · exact h
        rw [hlam0 hu0, symplO_zero_left, AddChar.map_zero_eq_one]
        exact one_mem _
      have hprim := Complex.isPrimitiveRoot_exp M hM0
      haveI : NeZero M := ⟨hM0⟩
      have hcM : ψ (symplO V W lam y'') ^ M = 1 := by rw [hM, pow_mul, hpow y'' hy'', one_pow]
      obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one hcM
      rw [← hi]
      exact pow_mem hO i
    have hterm : ∀ y'' ∈ Y, heisO ψ V W (b + lam) (heisO ψ V W y'' f₀) =
        ψ (symplO V W lam y'') • heisO ψ V W (b + y'') f₀ := by
      intro y'' hy''
      rw [heisO_add_of_orth ψ V W hblam, heisO_comm ψ V W lam y'', hfl, heisO_smul,
        ← heisO_add_of_orth ψ V W (hby y'' hy'')]
    have hΦ : Φ (heisO ψ V W y f₀) = ∑ y'' ∈ Y, ψ (symplO V W lam y'') • heisO ψ V W (b + y'') f₀ := by
      show s⁻¹ • om (z⁻¹, 1) (heisO ψ V W y f₀) = _
      rw [hweil.om_heis _ _ _ _ hth, hay, hom, heisO_smul, heisO_sum, smul_smul, inv_mul_cancel₀ hs, one_smul]
      exact Finset.sum_congr rfl hterm
    rw [hΦ]
    refine Submodule.sum_mem _ fun y'' hy'' => ?_
    have hsm : ψ (symplO V W lam y'') • heisO ψ V W (b + y'') f₀ =
        (⟨_, hcO y'' hy''⟩ : O) • heisO ψ V W (b + y'') f₀ := rfl
    rw [hsm]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨b + y'', ?_, ?_, rfl⟩)
    · refine isHalf_add (fun i j => ?_) (fun i j => ?_)
      · have hyij := hy i j
        simp only [hb, Matrix.smul_apply, smul_eq_mul]
        linear_combination (y i j) * (h3 - 2 * h1 + h2 + h5 - h4)
      · have hy2 := (hY y'' hy'').1 i j
        linear_combination (1 - (e - eT + cA D eT)) * hy2 + y'' i j * (h5 - h4 + h6)
    · rw [nsmul_add]
      refine add_mem ?_ ?_
      · rw [hb, smul_comm]
        exact idem_smul_mem hidem _ hMy
      · rw [hM, mul_comm, ← smul_smul]
        exact AddSubgroup.nsmul_mem _ (hY y'' hy'').2 u
  have hall : ∀ g ∈ trSp ψ V W ΛV ΛW f₀ e M O, Φ g ∈ trSp ψ V W ΛV ΛW f₀ (e - eT + cA D eT) M O := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, hMy, rfl⟩ := hx
      exact hgen y hy hMy
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ a hx
  intro f hf
  refine ⟨Φ f, hall f hf, ?_⟩
  show om (z, 1) (s • (s⁻¹ • om (z⁻¹, 1) f)) = f
  rw [smul_smul, mul_inv_cancel₀ hs, one_smul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk,
    mul_inv_cancel, mul_one, ← Prod.one_eq_mk, map_one, Module.End.one_apply]

end GlobalTheory.FlipTranslates

end
