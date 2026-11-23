import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFlipDet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlipIdxNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdemSumMulOfSubset
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNeZeroOfIsVacO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
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

namespace GlobalTheory.FlipFixSum

open GlobalTheory.PlaceModel GlobalTheory.PlaceModelSum

variable {D : D7} {S T : HSp D}

theorem smul_half_zero {e c : AE D} (h : e * c = 0) {y : WO S T} (hy : c • y = y) : e • y = 0 := by
  rw [← hy, smul_smul, h, zero_smul]

theorem half_two : algebraMap D.host.F (AF D.host.F) (1 / 2) * 2 = 1 := by
  rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
  norm_num

theorem natCast_mul_inv {m : ℕ} (hm : m ≠ 0) : (m : AE D) * incA D ((m : D.host.E)⁻¹) = 1 := by
  rw [show (m : AE D) = incA D (m : D.host.E) by simp, ← map_mul,
    mul_inv_cancel₀ (Nat.cast_ne_zero.2 hm), map_one]

theorem sum_reindex {X M : Type} [AddCommMonoid M] (Y : Finset X) (G g : X → M) (R : X → X → Prop)
    (hR : ∀ y ∈ Y, ∃ y' ∈ Y, R y y' ∧ G y = g y')
    (hinj : ∀ y₁ ∈ Y, ∀ y₂ ∈ Y, ∀ z ∈ Y, R y₁ z → R y₂ z → y₁ = y₂) :
    ∑ y ∈ Y, G y = ∑ y ∈ Y, g y := by
  classical
  choose! φ hφY hφR hφG using hR
  have hinjOn : Set.InjOn φ Y := fun y₁ h₁ y₂ h₂ he =>
    hinj y₁ h₁ y₂ h₂ (φ y₁) (hφY y₁ h₁) (hφR y₁ h₁) (he ▸ hφR y₂ h₂)
  have himg : Y.image φ = Y := Finset.eq_of_subset_of_card_le
    (Finset.image_subset_iff.2 hφY) (Finset.card_image_of_injOn hinjOn).ge
  calc ∑ y ∈ Y, G y = ∑ y ∈ Y, g (φ y) := Finset.sum_congr rfl hφG
    _ = ∑ z ∈ Y.image φ, g z := (Finset.sum_image hinjOn).symm
    _ = ∑ y ∈ Y, g y := by rw [himg]

end GlobalTheory.FlipFixSum

namespace GlobalTheory.FlipFixSum

open GlobalTheory.PlaceModel GlobalTheory.PlaceModelSum GlobalTheory.LevelSeries

variable {D : D7} {S T : HSp D}

theorem flipElt_eq (e : AE D) (m : ℕ) :
    flipElt e m = (e * (m : AE D) + (1 - e - cA D e)) + cA D e * incA D ((m : D.host.E)⁻¹) := by
  unfold flipElt; ring

theorem cA_intPart (e : AE D) (m : ℕ) :
    cA D (e * (m : AE D) + (1 - e - cA D e)) = cA D e * (m : AE D) + (1 - cA D e - e) := by
  simp only [map_add, map_mul, map_sub, map_one, cA_cA, map_natCast]

set_option maxHeartbeats 1000000 in

theorem phase_eq {ψ : AddChar (AF D.host.F) ℂ} {e c b k : AE D} {m : ℕ} (hc : cA D e = c) (hcc : c * c = c)
    (hec : e * c = 0) (hcb : cA D b = c * (m : AE D) + (1 - c - e)) (hmk : (m : AE D) * k = 1)
    {x y : WO S T} (hy : c • y = y) (hwy : ψ (symplO S T (e • x) ((m : AE D) • y)) = 1)
    (hxx : ψ (symplOH S T x (c • x)) = 1) :
    ψ (symplOH S T ((b + c * k) • x) y) = ψ (symplOH S T (y + (c * k) • x) (b • x)) := by
  have hce : c * e = 0 := by rw [mul_comm, hec]
  have hcA : cA D c = e := by rw [← hc, cA_cA]
  have hqy : symplO S T ((c * k) • x) y = 0 := by
    rw [← smul_smul, symplO_smul, hcA, smul_half_zero hec hy, symplO_zero_right]
  have hby : cA D b • y = c • ((m : AE D) • y) := by
    conv_lhs => rw [← hy]
    rw [smul_smul, smul_smul, hcb]
    congr 1
    linear_combination (m : AE D) * hcc - hcc - hce
  have hwy' : symplO S T (b • x) y = symplO S T (e • x) ((m : AE D) • y) := by
    rw [symplO_smul, hby, symplO_smul S T e, hc]
  have hbq : cA D b • ((c * k) • x) = c • x := by
    rw [smul_smul, hcb]
    congr 1
    linear_combination k * (m : AE D) * hcc - k * hcc - k * hce + c * hmk
  have hqw : symplO S T ((c * k) • x) (b • x) = -symplO S T x (c • x) := by
    rw [symplO_skew S T (b • x) ((c * k) • x), symplO_smul, hbq]
  have key : symplOH S T ((b + c * k) • x) y =
      symplOH S T (y + (c * k) • x) (b • x) + symplO S T (b • x) y + symplOH S T x (c • x) := by
    simp only [symplOH]
    rw [add_smul, symplO_add_left S T (b • x), symplO_add_left S T y, hqy, hqw, symplO_skew S T (b • x) y]
    linear_combination (symplO S T (b • x) y) * half_two (D := D)
  rw [key, AddChar.map_add_eq_mul ψ (symplOH S T (y + (c * k) • x) (b • x) + symplO S T (b • x) y) (symplOH S T x (c • x)),
    AddChar.map_add_eq_mul ψ (symplOH S T (y + (c * k) • x) (b • x)) (symplO S T (b • x) y), hwy', hwy, hxx, mul_one, mul_one]

set_option maxHeartbeats 1000000 in

theorem heisO_translate {ψ : AddChar (AF D.host.F) ℂ} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {f₀ : WO S T → ℂ}
    (hlat : IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f₀)
    {e c b k : AE D} {m : ℕ} (hO : IsOrthSum e) (hc : cA D e = c) (hcc : c * c = c)
    (hec : e * c = 0) (hcb : cA D b = c * (m : AE D) + (1 - c - e)) (hmk : (m : AE D) * k = 1)
    {x y y' : WO S T} (hw : heisO ψ S T (b • x) f₀ = f₀) (hy : c • y = y)
    (hwy : ψ (symplO S T (e • x) ((m : AE D) • y)) = 1) (hxx : ψ (symplOH S T x (c • x)) = 1)
    (hy' : c • y' = y')
    (hl : y + (c * k) • x - y' ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) :
    heisO ψ S T ((b + c * k) • x) (heisO ψ S T y f₀) = heisO ψ S T y' f₀ := by
  have h1 := GlobalTheory.LatVac.heisO_heisO ψ ((b + c * k) • x) y f₀
  have h2 := GlobalTheory.LatVac.heisO_heisO ψ (y + (c * k) • x) (b • x) f₀
  rw [hw] at h2
  have hsum : (b + c * k) • x + y = y + (c * k) • x + b • x := by rw [add_smul]; abel
  rw [h1, phase_eq hc hcc hec hcb hmk hy hwy hxx, hsum, ← h2]
  have hcq : c • ((c * k) • x) = (c * k) • x := by rw [smul_smul, ← mul_assoc, hcc]
  have hlc : c • (y + (c * k) • x - y') = y + (c * k) • x - y' := by rw [smul_sub, smul_add, hy, hcq, hy']
  have hlc' : cA D e • (y + (c * k) • x - y') = y + (c * k) • x - y' := by rw [hc]; exact hlc
  have hl0 : heisO ψ S T (y + (c * k) • x - y') f₀ = f₀ :=
    hO.conj.heisO_eq (by rw [cA_cA, hc, hec]) hlat _ (AddSubgroup.mem_inf.2 ⟨hl, (mem_half S T).2 hlc'⟩)
  have hcA : cA D c = e := by rw [← hc, cA_cA]
  have hp : symplO S T y' (y + (c * k) • x - y') = 0 := by
    have h' : symplO S T y' (y + (c * k) • x - y') = symplO S T (c • y') (y + (c * k) • x - y') := by rw [hy']
    rw [h', symplO_smul, hcA, smul_half_zero hec hlc, symplO_zero_right]
  have h3 := GlobalTheory.LatVac.heisO_heisO ψ y' (y + (c * k) • x - y') f₀
  rw [hl0, symplOH, hp, mul_zero, AddChar.map_zero_eq_one, one_smul] at h3
  rw [h3, add_sub_cancel]

end GlobalTheory.FlipFixSum

namespace GlobalTheory.FlipFixSum

open GlobalTheory.PlaceModel GlobalTheory.PlaceModelSum GlobalTheory.LevelSeries

set_option maxHeartbeats 2000000 in

theorem flip_fix : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (m : ℕ) (eT : AE D), IsIdemSum eT T → Odd m → Nat.Coprime m (GlobalTheory.Tow.badN D) → (∀ PP ∈ T, ((m : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → ∀ Y : Finset (WO V W), (∀ y ∈ Y, IsHalf (cA D eT) y ∧ m • y ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True)) → (∀ y ∈ Y, ∀ y' ∈ Y, y - y' ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) → y = y') → (∀ y : WO V W, IsHalf (cA D eT) y → m • y ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) → ∃ y' ∈ Y, y - y' ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True)) → (∀ u ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True), heisO ψ V W (flipElt eT m • (2 • u)) (∑ y ∈ Y, heisO ψ V W y f₀) = ∑ y ∈ Y, heisO ψ V W y f₀) ∧ ∀ e : AE D, IsSplitIdem D e → ∀ u ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True), IsHalf e u → heisO ψ V W (flipElt eT m • u) (∑ y ∈ Y, heisO ψ V W y f₀) = ∑ y ∈ Y, heisO ψ V W y f₀ := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T m eT hT hm _ _ Y hY hdist hcompl
  obtain ⟨-, -, -, -, hSV, hSW, -, -, hvac⟩ := hP
  obtain ⟨hψ, hv⟩ := hvac
  have hlat := hv.lat
  have hO := isOrthSum_of_isIdemSum hT
  have hec : eT * cA D eT = 0 := hT.2
  have hm0 : m ≠ 0 := hm.pos.ne'
  have hmk := natCast_mul_inv (D := D) hm0
  have hcc : cA D eT * cA D eT = cA D eT := by rw [← map_mul, hO.idem]
  have hee : eT * eT = eT := hO.idem
  have hbu : ∀ u ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True),
      (eT * (m : AE D) + (1 - eT - cA D eT)) • u ∈
        latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) := by
    intro u hu
    have e1 : (eT * (m : AE D) + (1 - eT - cA D eT)) • u = m • (eT • u) + (u - eT • u - cA D eT • u) := by
      rw [add_smul, sub_smul, sub_smul, one_smul, mul_comm, ← smul_smul, Nat.cast_smul_eq_nsmul]
    rw [e1]
    exact add_mem (nsmul_mem (idem_smul_latO hee hu) m)
      (sub_mem (sub_mem hu (idem_smul_latO hee hu)) (idem_smul_latO hcc hu))
  have gen : ∀ x ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True),
      heisO ψ V W ((eT * (m : AE D) + (1 - eT - cA D eT)) • x) f₀ = f₀ →
      ψ (symplOH V W x (cA D eT • x)) = 1 →
      heisO ψ V W (flipElt eT m • x) (∑ y ∈ Y, heisO ψ V W y f₀) = ∑ y ∈ Y, heisO ψ V W y f₀ := by
    intro x hx hw hxx
    rw [flipElt_eq]
    change heisL V W ψ _ (∑ y ∈ Y, heisO ψ V W y f₀) = _
    rw [map_sum]
    refine sum_reindex Y _ _ (fun y y' => y + (cA D eT * incA D ((m : D.host.E)⁻¹)) • x - y' ∈
        latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True))
      (fun y hy => ?_) (fun y₁ h₁ y₂ h₂ z _ r₁ r₂ => ?_)
    · have hyc : cA D eT • y = y := (mem_half V W).1 ((isHalf_iff V W).1 (hY y hy).1)
      have hhalf : IsHalf (cA D eT) (y + (cA D eT * incA D ((m : D.host.E)⁻¹)) • x) :=
        (isHalf_iff V W).2 ((mem_half V W).2 (by rw [smul_add, hyc, smul_smul, ← mul_assoc, hcc]))
      have hmq : m • (y + (cA D eT * incA D ((m : D.host.E)⁻¹)) • x) ∈
          latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) := by
        rw [nsmul_add]
        refine add_mem (hY y hy).2 ?_
        rw [← Nat.cast_smul_eq_nsmul (AE D), smul_smul,
          show (m : AE D) * (cA D eT * incA D ((m : D.host.E)⁻¹)) = cA D eT by
            linear_combination cA D eT * hmk]
        exact idem_smul_latO hcc hx
      obtain ⟨y', hy'Y, hd⟩ := hcompl _ hhalf hmq
      have hy'c : cA D eT • y' = y' := (mem_half V W).1 ((isHalf_iff V W).1 (hY y' hy'Y).1)
      have hwy : ψ (symplO V W (eT • x) ((m : AE D) • y)) = 1 := by
        rw [Nat.cast_smul_eq_nsmul]
        exact GlobalTheory.LatVac.char_sympl_eq_one hψ hSV hSW (idem_smul_latO hee hx) (hY y hy).2
      refine ⟨y', hy'Y, hd, ?_⟩
      exact heisO_translate hlat hO rfl hcc hec (cA_intPart eT m) hmk hw hyc hwy hxx hy'c hd
    · refine hdist y₁ h₁ y₂ h₂ ?_
      have := sub_mem r₁ r₂
      convert this using 1
      abel
  refine ⟨fun u hu => ?_, fun e he u hu hhu => ?_⟩
  · refine gen (2 • u) (nsmul_mem hu 2) ?_ ?_
    · rw [smul_comm]
      exact hlat.1 _ (hbu u hu)
    · have hS := GlobalTheory.LatVac.char_sympl_eq_one hψ hSV hSW hu (idem_smul_latO hcc hu)
      rw [two_nsmul, smul_add, symplOH, symplO_add_left, symplO_add_right]
      have e2 : algebraMap D.host.F (AF D.host.F) (1 / 2) *
          (symplO V W u (cA D eT • u) + symplO V W u (cA D eT • u) +
            (symplO V W u (cA D eT • u) + symplO V W u (cA D eT • u))) =
          symplO V W u (cA D eT • u) + symplO V W u (cA D eT • u) := by
        linear_combination (2 * symplO V W u (cA D eT • u)) * half_two (D := D)
      rw [e2, AddChar.map_add_eq_mul ψ (symplO V W u (cA D eT • u)) (symplO V W u (cA D eT • u)), hS, one_mul]
  · have hue : e • u = u := (mem_half V W).1 ((isHalf_iff V W).1 hhu)
    refine gen u hu ?_ ?_
    · have hb : e • ((eT * (m : AE D) + (1 - eT - cA D eT)) • u) = (eT * (m : AE D) + (1 - eT - cA D eT)) • u := by
        rw [smul_smul, mul_comm, ← smul_smul, hue]
      exact hlat.2 e he _ (hbu u hu) ((isHalf_iff V W).2 ((mem_half V W).2 hb))
    · have h0 : symplO V W u (cA D eT • u) = 0 := by
        have h' : symplO V W u (cA D eT • u) = symplO V W (e • u) (cA D eT • (e • u)) := by rw [hue]
        rw [h', symplO_smul, smul_smul, smul_smul, mul_right_comm (cA D e) (cA D eT) e, mul_comm (cA D e) e, he.2.1, zero_mul,
          zero_smul, symplO_zero_right]
      rw [symplOH, h0, mul_zero, AddChar.map_zero_eq_one]

end GlobalTheory.FlipFixSum
