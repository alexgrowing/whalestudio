import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaPairingInvariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DatP
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerIntertwinerSchwartzBruhatIsTheta
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AddNsmulResidueAssoc
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

noncomputable section

namespace GlobalTheory.BadOrth

variable {D : D7} {S T : HSp D}

theorem thetaIP_eq_ipO (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (f g : WO S T → ℂ) :
    thetaIP μ 𝓕 f g = GlobalTheory.Ker.ipO μ 𝓕 g f := by
  unfold thetaIP GlobalTheory.Ker.ipO
  congr 1; funext w; rw [mul_comm]; rfl

theorem thetaInner_eq_zero_of_eigen {ψ : AddChar (AF D.host.F) ℂ} {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hψ : IsStdChar D ψ (-1)) (hμ : IsCovolOne (ratL T S) μ 𝓕) {f g : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) (y : WO S T) {a b : ℂ} (ha : ‖a‖ = 1) (hab : a ≠ b)
    (hfy : heisO ψ S T y f = a • f) (hgy : heisO ψ S T y g = b • g) : thetaIP μ 𝓕 f g = 0 := by
  rw [thetaIP_eq_ipO]
  have h := GlobalTheory.Size.ipO_heisO hψ hμ.1 hμ.2.1 hg hf y
  rw [hfy, hgy, GlobalTheory.Size.ipO_smul_left, GlobalTheory.Size.ipO_smul_right, ← mul_assoc] at h
  by_contra hX
  have h1 : b * starRingEnd ℂ a = 1 := by
    have := mul_right_cancel₀ hX (h.trans (one_mul _).symm)
    exact this
  have h2 : starRingEnd ℂ a * a = 1 := by
    rw [Complex.conj_mul', ha]; norm_num
  apply hab
  calc a = (b * starRingEnd ℂ a) * a := by rw [h1, one_mul]
    _ = b := by rw [mul_assoc, h2, mul_one]

theorem thetaInner_sum_sum {ψ : AddChar (AF D.host.F) ℂ} {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hψ : IsStdChar D ψ (-1)) (hμ : IsCovolOne (ratL T S) μ 𝓕) {ι : Type} (Q : Finset ι) (f g : ι → WO S T → ℂ)
    (hf : ∀ i ∈ Q, IsThetaFunO ψ S T (f i)) (hg : ∀ i ∈ Q, IsThetaFunO ψ S T (g i)) :
    thetaIP μ 𝓕 (∑ i ∈ Q, f i) (∑ j ∈ Q, g j) = ∑ i ∈ Q, ∑ j ∈ Q, thetaIP μ 𝓕 (f i) (g j) := by
  have hint : ∀ i ∈ Q, ∀ j ∈ Q, Integrable (fun w => star (f i w) * g j w) (μ.restrict 𝓕) := by
    intro i hi j hj
    have := GlobalTheory.Size.integrableOn_mul_conj hψ hμ.1 hμ.2.1 (hg j hj) (hf i hi)
    refine this.congr (ae_of_all _ fun w => ?_)
    simp only [mul_comm (g j w)]; rfl
  unfold thetaIP
  have e : (fun w => star ((∑ i ∈ Q, f i) w) * (∑ j ∈ Q, g j) w) =
      fun w => ∑ i ∈ Q, ∑ j ∈ Q, star (f i w) * g j w := by
    funext w
    simp only [Finset.sum_apply, star_sum, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm
  rw [e, integral_finset_sum _ fun i hi => integrable_finset_sum _ fun j hj => hint i hi j hj]
  exact Finset.sum_congr rfl fun i hi => integral_finset_sum _ fun j hj => hint i hi j hj

end GlobalTheory.BadOrth

namespace GlobalTheory.BadOrth

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in

theorem finCosets : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ a : AE D, a * a = a → ∀ k : ℕ, 0 < k → ∃ C : Finset (WO S T), (∀ c ∈ C, IsHalf a c) ∧ ∀ s : WO S T, IsHalf a s → k • s ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) → ∃ c ∈ C, ∃ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), IsHalf a u ∧ s = c + k • u := by
  intro D S T ΛS ΛT hS hT a ha k hk
  obtain ⟨R, hR, hRm⟩ := GlobalTheory.LatFinMod.latO_finite_mod D S T ΛS ΛT hS.1.fg hT.1.fg (fun _ => True) (k * k)
    (Nat.mul_pos hk hk)
  have half' : ∀ {b : AE D} {u : WO S T}, IsHalf b u ↔ b • u = u := fun {b u} =>
    (PlaceModel.isHalf_iff S T).trans (PlaceModel.mem_half S T)
  let r : AE D := algebraMap D.host.F (AE D) ((k : D.host.F)⁻¹)
  have hrk : r * (k : AE D) = 1 := by
    rw [← map_natCast (algebraMap D.host.F (AE D)) k, ← map_mul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.2 hk.ne'), map_one]
  have hrkz : ∀ z : WO S T, r • (k • z) = z := fun z => by
    rw [← Nat.cast_smul_eq_nsmul (AE D) k z, smul_smul, hrk, one_smul]
  refine ⟨hR.toFinset.image (fun z => a • (r • z)), fun c hc => ?_, fun s hs hks => ?_⟩
  · obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 hc
    exact half'.2 (by rw [smul_smul, ha])
  · obtain ⟨z, hz, u, hu, hzu⟩ := hRm (k • s) hks
    refine ⟨a • (r • z), Finset.mem_image_of_mem _ (hR.mem_toFinset.2 hz), a • u,
      PlaceModelSum.idem_smul_latO ha hu, half'.2 (by rw [smul_smul, ha]), ?_⟩
    calc s = a • (r • (k • s)) := by rw [hrkz, half'.1 hs]
      _ = a • (r • z) + k • (a • u) := by rw [hzu, smul_add, smul_add, mul_smul, hrkz, smul_comm a k u]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in

theorem separate : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ e : AE D, IsSplitIdem D e → ∀ k : ℕ, 0 < k → ∀ x : WO S T, IsHalf (cA D e) x → (∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), IsHalf (cA D e) u → x ≠ k • u) → ∃ y : WO S T, IsHalf e y ∧ (∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), ψ (symplO S T (k • u) y) = 1) ∧ ψ (symplO S T x y) ≠ 1 := by
  intro D ψ S T ΛS ΛT hψ hS hT e he k hk x hx hxL
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have half' : ∀ {a : AE D} {u : WO S T}, IsHalf a u ↔ a • u = u := fun {a u} =>
    (PlaceModel.isHalf_iff S T).trans (PlaceModel.mem_half S T)
  have hce : PlaceModelSum.IsOrthSum (cA D e) :=
    ⟨Unit, {()}, fun _ => cA D e, fun _ _ => PlaceModelSum.isSplitIdem_cA he,
      fun i _ j _ h => absurd (Subsingleton.elim j i) h, by rw [Finset.sum_singleton]⟩

  let r : AE D := algebraMap D.host.F (AE D) ((k : D.host.F)⁻¹)
  have hrk : r * (k : AE D) = 1 := by
    rw [← map_natCast (algebraMap D.host.F (AE D)) k, ← map_mul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.2 hk.ne'), map_one]
  have hcr : cA D r = r := by
    have h1 : cA D r * (k : AE D) = 1 := by rw [← map_natCast (cA D) k, ← map_mul, hrk, map_one]
    calc cA D r = cA D r * ((k : AE D) * r) := by rw [mul_comm (k : AE D) r, hrk, mul_one]
      _ = r := by rw [← mul_assoc, h1, one_mul]
  have hnat : ∀ z : WO S T, k • z = (k : AE D) • z := fun z => (Nat.cast_smul_eq_nsmul (AE D) k z).symm
  have hrkz : ∀ z : WO S T, r • (k • z) = z := fun z => by rw [hnat, smul_smul, hrk, one_smul]
  have hkrz : ∀ z : WO S T, k • (r • z) = z := fun z => by rw [hnat, smul_smul, mul_comm, hrk, one_smul]

  have hΛΛ : ∀ y ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), IsHalf e y → ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), ψ (symplO S T u y) = 1 := by
    intro y hy hye u hu
    have hinf : y.map (infPart D) = 0 := by
      refine hce.conj.infPart_half ((PlaceModel.isHalf_iff S T).1 ?_)
      rw [cA_cA]; exact hye
    rw [PlaceModel.symplO_skew, AddChar.map_neg_eq_inv, (hdual y hinf).1 hy u hu, inv_one]
  by_contra hno
  push_neg at hno
  have hrx : IsHalf (cA D e) (r • x) := half'.2 (by rw [smul_comm, half'.1 hx])
  have hmem := hce.mem_of_dual hdual (r • x) ((PlaceModel.isHalf_iff S T).1 hrx) (fun y hy => by
    obtain ⟨hy1, hy2⟩ := AddSubgroup.mem_inf.1 hy
    have hye : IsHalf e y := by
      have := (PlaceModel.isHalf_iff S T).2 hy2
      rwa [cA_cA] at this
    have hrye : IsHalf e (r • y) := half'.2 (by rw [smul_comm, half'.1 hye])
    have h1 := hno (r • y) hrye (fun u hu => by
      rw [← hcr, ← PlaceModel.symplO_smul S T, hrkz]
      exact hΛΛ y hy1 hye u hu)
    rwa [PlaceModel.symplO_smul S T, hcr])
  obtain ⟨h1, h2⟩ := AddSubgroup.mem_inf.1 hmem
  exact hxL (r • x) h1 ((PlaceModel.isHalf_iff S T).2 h2) (hkrz x).symm

open GlobalTheory.PlaceModel GlobalTheory.PlaceModelSum

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in

theorem orth_of_disjoint : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (Pf : Finset (Pl D.host.E)) (ea e : AE D) (f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → IsIdemSum ea Pf → IsSplitIdem D e → e * ea = e → IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f₀ → IsPlaceModel ψ (symplO S T) (heisO ψ S T) (cA D ea) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Tm → IsCovolOne (ratL T S) μ 𝓕 → ∀ Φ₁ Φ₂ : WO S T → ℂ, IsSBHalf (cA D ea) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) Φ₁ → IsSBHalf (cA D ea) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) Φ₂ → (∀ x x' : WO S T, (∀ a b, (e + cA D e) * x a b = (e + cA D e) * x' a b) → Φ₁ x ≠ 0 → Φ₂ x' ≠ 0 → False) → ∀ Ω : Module.End ℂ (WO S T → ℂ), (∀ g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T (Ω g)) → (∀ y : WO S T, IsHalf e y → ∀ g, IsThetaFunO ψ S T g → Ω (heisO ψ S T y g) = heisO ψ S T y (Ω g)) → thetaIP μ 𝓕 (Tm Φ₁) (Ω (Tm Φ₂)) = 0 := by
  intro D ψ S T ΛS ΛT Pf ea e f₀ Tm μ 𝓕 hψ hS hT hIdem hsplit hee hf₀ hvac hTm hμ Φ₁ Φ₂ hΦ₁ hΦ₂ hdisj Ω hΩt hΩc
  set Λ := (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) with hΛ
  have hea : IsOrthSum ea := isOrthSum_of_isIdemSum hIdem
  have hcea : cA D ea * cA D ea = cA D ea := by rw [← map_mul, hea.idem]
  have hinf : infPart D (cA D ea) = 0 := hea.conj.infPart_eq
  have hce1 : cA D e * cA D e = cA D e := by rw [← map_mul, hsplit.1]
  have hecea : e * cA D ea = 0 := by rw [← hee, mul_assoc, hIdem.2, mul_zero]
  have hcecea : cA D ea * cA D e = cA D e := by rw [← map_mul, mul_comm, hee]
  have half' : ∀ {a : AE D} {u : WO S T}, IsHalf a u ↔ a • u = u := fun {a u} => (isHalf_iff S T).trans (mem_half S T)
  have hθ : ∀ Φ, IsSBHalf (cA D ea) Λ Φ → IsThetaFunO ψ S T (Tm Φ) := fun Φ hΦ =>
    GlobalTheory.SchrTheta.isTheta_placeModel D ψ hψ S T ΛS ΛT hS hT _ hcea hinf f₀ hf₀ Tm hTm Φ hΦ

  obtain ⟨hs₁, k₁, hk₁, hi₁, hl₁⟩ := hΦ₁
  obtain ⟨hs₂, k₂, hk₂, hi₂, hl₂⟩ := hΦ₂
  have hk : 0 < k₁ * k₂ := Nat.mul_pos hk₁ hk₂
  have hhalfU : ∀ (m : ℕ) {a : AE D} {u : WO S T}, u ∈ Λ → IsHalf a u → m • u ∈ Λ ∧ IsHalf a (m • u) :=
    fun m a u hu hue => ⟨AddSubgroup.nsmul_mem _ hu m, half'.2 (by rw [smul_comm, half'.1 hue])⟩
  have hinv₁ : ∀ u ∈ Λ, IsHalf (cA D ea) u → ∀ t, Φ₁ (t + (k₁ * k₂) • u) = Φ₁ t := fun u hu hue t => by
    rw [mul_smul]; exact hi₁ _ (hhalfU k₂ hu hue).1 (hhalfU k₂ hu hue).2 t
  have hinv₂ : ∀ u ∈ Λ, IsHalf (cA D ea) u → ∀ t, Φ₂ (t + (k₁ * k₂) • u) = Φ₂ t := fun u hu hue t => by
    rw [mul_comm, mul_smul]; exact hi₂ _ (hhalfU k₁ hu hue).1 (hhalfU k₁ hu hue).2 t
  have hsup₁ : ∀ t, Φ₁ t ≠ 0 → IsHalf (cA D ea) t ∧ (k₁ * k₂) • t ∈ Λ := fun t ht =>
    ⟨hs₁ t ht, by rw [mul_comm, mul_smul]; exact AddSubgroup.nsmul_mem _ (hl₁ t ht) _⟩
  have hsup₂ : ∀ t, Φ₂ t ≠ 0 → IsHalf (cA D ea) t ∧ (k₁ * k₂) • t ∈ Λ := fun t ht =>
    ⟨hs₂ t ht, by rw [mul_smul]; exact AddSubgroup.nsmul_mem _ (hl₂ t ht) _⟩
  generalize k₁ * k₂ = k at hk hinv₁ hinv₂ hsup₁ hsup₂

  let L : AddSubgroup (WO S T) := AddSubgroup.map (nsmulAddMonoidHom k) (Λ ⊓ half S T (cA D e))
  have memL : ∀ u ∈ Λ, IsHalf (cA D e) u → k • u ∈ L := fun u hu hue =>
    AddSubgroup.mem_map.2 ⟨u, AddSubgroup.mem_inf.2 ⟨hu, (isHalf_iff S T).1 hue⟩, rfl⟩
  have memL' : ∀ x ∈ L, ∃ u ∈ Λ, IsHalf (cA D e) u ∧ x = k • u := fun x hx => by
    obtain ⟨u, hu, rfl⟩ := AddSubgroup.mem_map.1 hx
    exact ⟨u, (AddSubgroup.mem_inf.1 hu).1, (isHalf_iff S T).2 (AddSubgroup.mem_inf.1 hu).2, rfl⟩
  have hceu : ∀ u ∈ Λ, cA D e • u ∈ Λ ∧ IsHalf (cA D e) (cA D e • u) := fun u hu =>
    ⟨idem_smul_latO hce1 hu, half'.2 (by rw [smul_smul, hce1])⟩
  obtain ⟨C, hCh, hC⟩ := finCosets D S T ΛS ΛT hS hT (cA D e) hce1 k hk
  let mkL : WO S T → WO S T ⧸ L := QuotientAddGroup.mk
  let Q : Finset (WO S T ⧸ L) := C.image mkL
  let P : (WO S T → ℂ) → (WO S T ⧸ L) → WO S T → ℂ := fun Φ q t =>
    if mkL (cA D e • t) = q then Φ t else 0

  have hcos : ∀ t, IsHalf (cA D ea) t → k • t ∈ Λ → ∃ c ∈ C, ∃ u ∈ Λ, IsHalf (cA D e) u ∧ cA D e • t = c + k • u :=
    fun t _ htk => hC _ (half'.2 (by rw [smul_smul, hce1])) (by rw [smul_comm]; exact idem_smul_latO hce1 htk)
  have hcover : ∀ Φ : WO S T → ℂ, (∀ t, Φ t ≠ 0 → IsHalf (cA D ea) t ∧ k • t ∈ Λ) → Φ = ∑ q ∈ Q, P Φ q := by
    intro Φ hsup
    funext t
    rw [Finset.sum_apply]
    by_cases h0 : Φ t = 0
    · rw [h0]; exact (Finset.sum_eq_zero fun q _ => by simp only [P, h0, ite_self]).symm
    · have hh := hcos t (hsup t h0).1 (hsup t h0).2
      obtain ⟨c, hc, u, hu, hh⟩ := hh
      obtain ⟨hue, htc⟩ := hh
      have hq : mkL (cA D e • t) = mkL c := by
        rw [htc]; refine QuotientAddGroup.eq.2 ?_
        have : -(c + k • u) + c = -(k • u) := by abel
        rw [this]
        exact neg_mem (memL u hu hue)
      rw [Finset.sum_eq_single_of_mem (mkL c) (Finset.mem_image_of_mem _ hc) fun q _ hq' => by
        simp only [P, hq, if_neg (Ne.symm hq')]]
      simp only [P, hq, if_true]
  have hSB : ∀ Φ : WO S T → ℂ, (∀ t, Φ t ≠ 0 → IsHalf (cA D ea) t ∧ k • t ∈ Λ) →
      (∀ u ∈ Λ, IsHalf (cA D ea) u → ∀ t, Φ (t + k • u) = Φ t) → ∀ q, IsSBHalf (cA D ea) Λ (P Φ q) := by
    intro Φ hsup hinv q
    have hne : ∀ t, P Φ q t ≠ 0 → Φ t ≠ 0 := fun t ht h0 => ht (by simp only [P, h0, ite_self])
    refine ⟨fun t ht => (hsup t (hne t ht)).1, k, hk, fun u hu hue t => ?_, fun t ht => (hsup t (hne t ht)).2⟩
    have hkey : mkL (cA D e • (t + k • u)) = mkL (cA D e • t) := by
      simp only [mkL]
      rw [smul_add, smul_comm, QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff _).2
        (memL _ (hceu u hu).1 (hceu u hu).2), add_zero]
    simp only [P, hkey, hinv u hu hue t]

  have hP₁ := hSB Φ₁ hsup₁ hinv₁
  have hP₂ := hSB Φ₂ hsup₂ hinv₂

  have hPne : ∀ Φ q t, P Φ q t ≠ 0 → mkL (cA D e • t) = q ∧ Φ t ≠ 0 := fun Φ q t h => by
    by_cases hq : mkL (cA D e • t) = q
    · refine ⟨hq, fun h0 => h ?_⟩
      simp only [P, hq, h0, if_true]
    · exact absurd (by simp only [P, hq, if_false]) h

  have hhalf_ce : ∀ t, IsHalf (cA D ea) t → (e + cA D e) • t = cA D e • t := fun t ht => by
    have h0 : e • t = 0 := by rw [← half'.1 ht, smul_smul, hecea, zero_smul]
    rw [add_smul, h0, zero_add]

  have hdisjP : ∀ q, P Φ₁ q = 0 ∨ P Φ₂ q = 0 := by
    intro q
    by_contra hne
    push_neg at hne
    obtain ⟨t, ht⟩ := Function.ne_iff.1 hne.1
    obtain ⟨t', ht'⟩ := Function.ne_iff.1 hne.2
    obtain ⟨hq1, h1⟩ := hPne Φ₁ q t ht
    obtain ⟨hq2, h2⟩ := hPne Φ₂ q t' ht'
    have hL : -(cA D e • t) + cA D e • t' ∈ L := QuotientAddGroup.eq.1 (hq1.trans hq2.symm)
    obtain ⟨w, hw, hwe, hwk⟩ := memL' _ hL
    have hwea : IsHalf (cA D ea) (-w) := half'.2 (by rw [smul_neg, ← half'.1 hwe, smul_smul, hcecea])
    have h2' : Φ₂ (t' + k • (-w)) ≠ 0 := by rw [hinv₂ _ (neg_mem hw) hwea]; exact h2
    have hw' : cA D e • (k • -w) = -(k • w) := by rw [smul_comm, smul_neg, half'.1 hwe, smul_neg]
    have hM : (e + cA D e) • t = (e + cA D e) • (t' + k • (-w)) := by
      rw [hhalf_ce t (hsup₁ t h1).1, hhalf_ce _ (hsup₂ _ h2').1, smul_add, hw', ← hwk]
      abel
    exact hdisj t (t' + k • (-w)) (fun a b => congrFun (congrFun hM a) b) h1 h2'

  have hmod : ∀ y, IsHalf e y → ∀ Φ, IsSBHalf (cA D ea) Λ Φ →
      Tm (fun t => ψ (symplO S T t y) * Φ t) = heisO ψ S T y (Tm Φ) := fun y hy Φ hΦ =>
    hTm.modul Φ hΦ y (by rw [cA_cA]; exact half'.2 (by rw [← half'.1 hy, smul_smul, mul_comm ea e, hee]))

  have heig : ∀ Φ q (c : WO S T), mkL c = q → ∀ y, IsHalf e y → (∀ u ∈ Λ, ψ (symplO S T (k • u) y) = 1) →
      (fun t => ψ (symplO S T t y) * P Φ q t) = ψ (symplO S T c y) • P Φ q := by
    intro Φ q c hc y hy hyL
    funext t
    rw [Pi.smul_apply, smul_eq_mul]
    by_cases hq : mkL (cA D e • t) = q
    · have hL : -(cA D e • t) + c ∈ L := QuotientAddGroup.eq.1 (hq.trans hc.symm)
      obtain ⟨w, hw, hwe, hwk⟩ := memL' _ hL
      have h1 : symplO S T t y = symplO S T (cA D e • t) y := by rw [symplO_smul S T, cA_cA, half'.1 hy]
      have h2 : cA D e • t = c + k • -w := by rw [smul_neg, ← hwk]; abel
      rw [h1, h2, symplO_add_left S T, AddChar.map_add_eq_mul, hyL _ (neg_mem hw), mul_one]
    · simp only [P, hq, if_false, mul_zero]

  have hsep : ∀ q ∈ Q, ∀ q' ∈ Q, q ≠ q' → ∃ y, IsHalf e y ∧ ∃ a b : ℂ, ‖a‖ = 1 ∧ a ≠ b ∧
      (∀ Φ, (fun t => ψ (symplO S T t y) * P Φ q t) = a • P Φ q) ∧
      (∀ Φ, (fun t => ψ (symplO S T t y) * P Φ q' t) = b • P Φ q') := by
    intro q hq q' hq' hne
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hq
    obtain ⟨c', hc', rfl⟩ := Finset.mem_image.1 hq'
    have hx : IsHalf (cA D e) (c - c') :=
      half'.2 (by rw [smul_sub, half'.1 (hCh c hc), half'.1 (hCh c' hc')])
    have hxL : ∀ u ∈ Λ, IsHalf (cA D e) u → c - c' ≠ k • u := fun u hu hue h => hne (QuotientAddGroup.eq.2 (by
      have : -c + c' = -(k • u) := by rw [← h]; abel
      rw [this]; exact neg_mem (memL u hu hue)))
    obtain ⟨y, hy, hyL, hyx⟩ := separate D ψ S T ΛS ΛT hψ hS hT e hsplit k hk (c - c') hx hxL
    refine ⟨y, hy, ψ (symplO S T c y), ψ (symplO S T c' y), hψ.1.2.1 _, fun hab => hyx ?_,
      fun Φ => heig Φ _ c rfl y hy hyL, fun Φ => heig Φ _ c' rfl y hy hyL⟩
    have h1 : ψ (symplO S T c y) = ψ (symplO S T (c - c') y) * ψ (symplO S T c' y) := by
      rw [← AddChar.map_add_eq_mul, ← symplO_add_left S T, sub_add_cancel]
    have hne0 : ψ (symplO S T c' y) ≠ 0 := fun h0 => by
      have := hψ.1.2.1 (symplO S T c' y)
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    exact mul_right_cancel₀ hne0 (h1.symm.trans (hab.trans (one_mul _).symm))

  have eq1 : Tm Φ₁ = ∑ q ∈ Q, Tm (P Φ₁ q) := by
    conv_lhs => rw [hcover Φ₁ hsup₁]
    exact map_sum Tm _ _
  have eq2 : Ω (Tm Φ₂) = ∑ q ∈ Q, Ω (Tm (P Φ₂ q)) := by
    conv_lhs => rw [hcover Φ₂ hsup₂]
    rw [map_sum, map_sum]
  rw [eq1, eq2, thetaInner_sum_sum hψ hμ Q _ _ (fun q _ => hθ _ (hP₁ q)) (fun q _ => hΩt _ (hθ _ (hP₂ q)))]
  refine Finset.sum_eq_zero fun q hq => Finset.sum_eq_zero fun q' hq' => ?_
  by_cases hqq : q = q'
  · subst hqq
    rcases hdisjP q with h | h
    · rw [h, map_zero]; simp [thetaIP]
    · rw [h, map_zero, map_zero]; simp [thetaIP]
  · obtain ⟨y, hy, a, b, ha, hab, h1, h2⟩ := hsep q hq q' hq' hqq
    refine thetaInner_eq_zero_of_eigen hψ hμ (hθ _ (hP₁ q)) (hΩt _ (hθ _ (hP₂ q'))) y ha hab ?_ ?_
    · rw [← hmod y hy _ (hP₁ q), h1 Φ₁, map_smul]
    · rw [← hΩc y hy _ (hθ _ (hP₂ q')), ← hmod y hy _ (hP₂ q'), h2 Φ₂, map_smul, map_smul]

end GlobalTheory.BadOrth

end
