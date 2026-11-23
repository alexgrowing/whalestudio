import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThPDatumEq
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualCLatP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IndVac

variable {D : D7} {S T : HSp D}

theorem mem_of_indL_ne {L : AddSubgroup (WO S T)} {t : WO S T} (h : GlobalTheory.LiftLevel.indL L t ≠ 0) : t ∈ L := by
  by_contra hn
  exact h (by simp only [GlobalTheory.LiftLevel.indL, hn, if_false])

theorem isSBHalf_indL (a : AE D) (Λ L : AddSubgroup (WO S T)) (hL : ∀ x ∈ L, IsHalf a x)
    (h1 : ∃ m : ℕ, 0 < m ∧ ∀ x ∈ L, m • x ∈ Λ) (h2 : ∃ m : ℕ, 0 < m ∧ ∀ x ∈ Λ, IsHalf a x → m • x ∈ L) :
    IsSBHalf a Λ (GlobalTheory.LiftLevel.indL L) := by
  obtain ⟨m, hm, hm1⟩ := h1
  obtain ⟨n, hn, hn2⟩ := h2
  refine ⟨fun t ht => hL t (mem_of_indL_ne ht), m * n, Nat.mul_pos hm hn, fun u hu hu' t => ?_, fun t ht => ?_⟩
  · have hk : (m * n) • u ∈ L := by
      rw [← smul_smul]
      exact L.nsmul_mem (hn2 u hu hu') m
    simp only [GlobalTheory.LiftLevel.indL, L.add_mem_cancel_right hk]
  · rw [mul_comm, ← smul_smul]
    exact Λ.nsmul_mem (hm1 t (mem_of_indL_ne ht)) n

theorem partAt_eq (a : AE D) (w : WO S T) : GlobalTheory.LiftLevel.partAt a w = a • w := rfl

theorem symplO_half_eq_zero {a b : AE D} (hab : cA D b * a = 0) {r x : WO S T}
    (hr : r ∈ GlobalTheory.PlaceModel.half S T b) (hx : x ∈ GlobalTheory.PlaceModel.half S T a) : symplO S T r x = 0 := by
  rw [← (GlobalTheory.PlaceModel.mem_half S T).1 hr, ← (GlobalTheory.PlaceModel.mem_half S T).1 hx, GlobalTheory.PlaceModel.symplO_smul,
    smul_smul, hab, zero_smul, GlobalTheory.PlaceModel.symplO_zero_right]

theorem heisO_fix {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {a : AE D} (ha : a * a = a) (hinf : infPart D a = 0)
    {f₀ : WO S T → ℂ} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm)
    (r : WO S T) (hr0 : heisO ψ S T r f₀ = f₀) (hx : ∀ x, IsHalf a x → symplO S T r x = 0)
    (hy : ∀ y, IsHalf (cA D a) y → symplO S T r y = 0)
    {Φ : WO S T → ℂ} (hΦ : IsSBHalf a (latO S T ΛS ΛT fun _ => True) Φ) : heisO ψ S T r (Tm Φ) = Tm Φ := by
  have hc : ∀ w, symplO S T r w = 0 → ∀ g, heisO ψ S T r (heisO ψ S T w g) = heisO ψ S T w (heisO ψ S T r g) :=
    fun w hw g => by
      have := GlobalTheory.PlaceModel.heisL_comm S T ψ r w g
      rw [hw, AddChar.map_zero_eq_one, one_smul] at this
      exact this
  have h' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀
      ((GlobalTheory.PlaceModel.heisL S T ψ r).comp Tm) :=
    { trans := fun Φ hΦ x hxa => by
        change heisO ψ S T r (Tm _) = heisO ψ S T x (heisO ψ S T r (Tm Φ))
        rw [hTm.trans Φ hΦ x hxa, hc x (hx x hxa)]
      modul := fun Φ hΦ y hya => by
        change heisO ψ S T r (Tm _) = heisO ψ S T y (heisO ψ S T r (Tm Φ))
        rw [hTm.modul Φ hΦ y hya, hc y (hy y hya)]
      vac := by
        change heisO ψ S T r (Tm _) = f₀
        rw [hTm.vac, hr0] }
  exact GlobalTheory.PlaceVec.placeModel_unique hψ hS hT ha hinf h' hTm hΦ

theorem heisenbergTranslate_add_three_fixes_of_trivial_phase (ψ : AddChar (AF D.host.F) ℂ) {f : WO S T → ℂ} {x y z : WO S T}
    (hx : heisO ψ S T x f = f) (hy : heisO ψ S T y f = f) (hz : heisO ψ S T z f = f)
    (p1 : ψ (symplOH S T y z) = 1) (p2 : ψ (symplOH S T x (y + z)) = 1) : heisO ψ S T (x + (y + z)) f = f := by
  have e1 := GlobalTheory.PlaceModel.heisL_heisL S T ψ y z f
  have e2 := GlobalTheory.PlaceModel.heisL_heisL S T ψ x (y + z) f
  change heisO ψ S T y (heisO ψ S T z f) = _ • heisO ψ S T (y + z) f at e1
  change heisO ψ S T x (heisO ψ S T (y + z) f) = _ • heisO ψ S T (x + (y + z)) f at e2
  rw [hz, hy, p1, one_smul] at e1
  rw [← e1, hx, p2, one_smul] at e2
  exact e2.symm

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem indL_theta_fock_latVac : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B : C.Bas), C.IsB B → ∀ (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∀ f₀ : WO S T → ℂ, IsVacO C.ψ C.θ S T (fun _ => 1) (C.sB B) (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) f₀ → ∀ Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ), IsPlaceModel C.ψ (symplO S T) (heisO C.ψ S T) (cA D e) (latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Tm → ∀ L : AddSubgroup (WO S T), (∀ x ∈ L, IsHalf (cA D e) x) → (∃ m : ℕ, 0 < m ∧ ∀ x ∈ L, m • x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) → (∃ m : ℕ, 0 < m ∧ ∀ x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True, IsHalf (cA D e) x → m • x ∈ L) → IsSBHalf (cA D e) (latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) (GlobalTheory.LiftLevel.indL L) ∧ C.IsTh (Tm (GlobalTheory.LiftLevel.indL L)) ∧ C.IsFock B (Tm (GlobalTheory.LiftLevel.indL L)) ∧ ∀ Λ'' : AddSubgroup (WO S T), (∀ u ∈ Λ'', GlobalTheory.LiftLevel.partAt (cA D e) u ∈ L ∧ (∀ t ∈ L, C.ψ (symplO S T t (GlobalTheory.LiftLevel.partAt e u)) = 1) ∧ GlobalTheory.LiftLevel.partAt (1 - e - cA D e) u ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) → IsLatVac (heisO C.ψ S T) Λ'' (Tm (GlobalTheory.LiftLevel.indL L)) := by
  intro D S T C B hB ΛT hT P e he f₀ hvac Tm hTm L hL hm1 hm2
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
  have hee : e * e = e := ho.idem
  have hea : e * cA D e = 0 := he.2
  have ha : cA D e * cA D e = cA D e := ho.conj.idem
  have hcc : cA D (cA D e) = e := cA_cA e
  have hS := GlobalTheory.Ker.Base.selfDualC_stdL C.m.gS
  have hψ := C.std
  have hinf : infPart D (cA D e) = 0 := ho.conj.infPart_eq
  have hinf' : infPart D (cA D (cA D e)) = 0 := ho.conj.conj.infPart_eq
  have hSB := isSBHalf_indL (cA D e) _ L hL hm1 hm2
  have hth : IsThetaAt C.ψ (symplO S T) (heisO C.ψ S T) (cA D e)
      (latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
      1 f₀ (GlobalTheory.LiftLevel.indL L) (Tm (GlobalTheory.LiftLevel.indL L)) :=
    ⟨⟨Tm, hTm⟩, fun T' hT' => GlobalTheory.PlaceVec.placeModel_unique hψ hS hT ha hinf hTm hT' hSB⟩
  have hθf := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ C.inf hth hvac.2.theta
  refine ⟨hSB, hθf, fun τ => GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ.1.1 C.inf hinf hinf' hth hvac.2.theta hθf
    (hvac.2.fock τ), ?_⟩
  obtain ⟨b, hbd⟩ : ∃ b : AE D, b = 1 - e - cA D e := ⟨_, rfl⟩
  have hb : b * b = b := by rw [hbd]; linear_combination hee + ha + 2 * hea
  have hcb : cA D b = b := by rw [hbd, map_sub, map_sub, map_one, hcc]; ring
  have hba : cA D b * cA D e = 0 := by rw [hcb, hbd]; linear_combination -hea - ha
  have hbe : cA D b * e = 0 := by rw [hcb, hbd]; linear_combination -hee - hea
  have hfix_a : ∀ x ∈ L, heisO C.ψ S T x (Tm (GlobalTheory.LiftLevel.indL L)) = Tm (GlobalTheory.LiftLevel.indL L) := fun x hx => by
    rw [← hTm.trans _ hSB x (hL x hx)]
    congr 1
    funext t
    simp only [GlobalTheory.LiftLevel.indL, L.add_mem_cancel_right hx]
  have hfix_e : ∀ y, IsHalf e y → (∀ t ∈ L, C.ψ (symplO S T t y) = 1) →
      heisO C.ψ S T y (Tm (GlobalTheory.LiftLevel.indL L)) = Tm (GlobalTheory.LiftLevel.indL L) := fun y hy ht => by
    rw [← hTm.modul _ hSB y (by rw [hcc]; exact hy)]
    congr 1
    funext t
    by_cases h : t ∈ L
    · simp only [GlobalTheory.LiftLevel.indL, h, if_true, ht t h, one_mul]
    · simp only [GlobalTheory.LiftLevel.indL, h, if_false, mul_zero]
  have hfix_r : ∀ r ∈ GlobalTheory.PlaceModel.half S T b, heisO C.ψ S T r f₀ = f₀ →
      heisO C.ψ S T r (Tm (GlobalTheory.LiftLevel.indL L)) = Tm (GlobalTheory.LiftLevel.indL L) := fun r hr hr0 =>
    heisO_fix hψ hS hT ha hinf hTm r hr0
      (fun x hx => symplO_half_eq_zero hba hr ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hx))
      (fun y hy => symplO_half_eq_zero (by rw [hcc]; exact hbe) hr ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hy)) hSB
  have hdec : ∀ u : WO S T, u = cA D e • u + (e • u + b • u) := fun u => by
    rw [← add_smul, ← add_smul, show cA D e + (e + b) = 1 by rw [hbd]; ring, one_smul]
  have hbmem : ∀ u : WO S T, b • u ∈ GlobalTheory.PlaceModel.half S T b := fun u => by
    show b • b • u = b • u
    rw [smul_smul, hb]
  have hemem : ∀ u : WO S T, e • u ∈ GlobalTheory.PlaceModel.half S T e := fun u => by
    show e • e • u = e • u
    rw [smul_smul, hee]
  have hamem : ∀ u : WO S T, cA D e • u ∈ GlobalTheory.PlaceModel.half S T (cA D e) := fun u => by
    show cA D e • cA D e • u = cA D e • u
    rw [smul_smul, ha]
  have hez : ∀ u : WO S T, symplO S T (e • u) (b • u) = 0 := fun u => by
    rw [GlobalTheory.PlaceModel.symplO_skew, symplO_half_eq_zero hbe (hbmem u) (hemem u), neg_zero]
  have haz : ∀ u : WO S T, symplO S T (cA D e • u) (b • u) = 0 := fun u => by
    rw [GlobalTheory.PlaceModel.symplO_skew, symplO_half_eq_zero hba (hbmem u) (hamem u), neg_zero]
  intro Λ'' hΛ''
  refine ⟨fun u hu => ?_, fun e' he' u hu hh => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hΛ'' u hu
    rw [partAt_eq] at h1 h3
    simp only [partAt_eq] at h2
    rw [← hbd] at h3
    have e2u : 2 • u = 2 • (cA D e • u) + (2 • (e • u) + 2 • (b • u)) := by
      conv_lhs => rw [hdec u]
      rw [smul_add, smul_add]
    rw [e2u]
    have h2' : algebraMap D.host.F (AF D.host.F) (1 / 2) * 2 = 1 := by
      rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
      norm_num
    refine heisenbergTranslate_add_three_fixes_of_trivial_phase C.ψ (hfix_a _ (L.nsmul_mem h1 2))
      (hfix_e _ ((GlobalTheory.PlaceModel.isHalf_iff S T).2 ((GlobalTheory.PlaceModel.half S T e).nsmul_mem (hemem u) 2))
        fun t ht => by rw [two_nsmul, GlobalTheory.PlaceModel.symplO_add_right, AddChar.map_add_eq_mul, h2 t ht, one_mul])
      (hfix_r _ ((GlobalTheory.PlaceModel.half S T _).nsmul_mem (hbmem u) 2) (hvac.2.lat.1 _ h3)) ?_ ?_
    · simp only [symplOH, two_nsmul, GlobalTheory.PlaceModel.symplO_add_left, GlobalTheory.PlaceModel.symplO_add_right, hez, add_zero,
        mul_zero, AddChar.map_zero_eq_one]
    · have hs : symplOH S T (2 • (cA D e • u)) (2 • (e • u) + 2 • (b • u)) =
          symplO S T (cA D e • u) (e • u) + symplO S T (cA D e • u) (e • u) := by
        simp only [symplOH, two_nsmul, GlobalTheory.PlaceModel.symplO_add_left, GlobalTheory.PlaceModel.symplO_add_right, haz, add_zero]
        linear_combination (2 * symplO S T (cA D e • u) (e • u)) * h2'
      rw [hs, AddChar.map_add_eq_mul, h2 _ h1, one_mul]
  · obtain ⟨h1, h2, h3⟩ := hΛ'' u hu
    rw [partAt_eq] at h1 h3
    simp only [partAt_eq] at h2
    rw [← hbd] at h3
    have hu' : u ∈ GlobalTheory.PlaceModel.half S T e' := (GlobalTheory.PlaceModel.isHalf_iff S T).1 hh
    have hin : ∀ c : AE D, c • u ∈ GlobalTheory.PlaceModel.half S T e' := fun c => by
      rw [GlobalTheory.PlaceModel.mem_half, smul_comm, (GlobalTheory.PlaceModel.mem_half S T).1 hu']
    have hae : symplO S T (cA D e • u) (e • u) = 0 :=
      symplO_half_eq_zero (by rw [mul_comm]; exact he'.2.1) (hin _) (hin _)
    rw [hdec u]
    refine heisenbergTranslate_add_three_fixes_of_trivial_phase C.ψ (hfix_a _ h1) (hfix_e _ ((GlobalTheory.PlaceModel.isHalf_iff S T).2 (hemem u)) h2)
      (hfix_r _ (hbmem u) (hvac.2.lat.2 e' he' _ h3 ((GlobalTheory.PlaceModel.isHalf_iff S T).2 (hin _)))) ?_ ?_
    · rw [symplOH, hez, mul_zero, AddChar.map_zero_eq_one]
    · rw [symplOH, GlobalTheory.PlaceModel.symplO_add_right, hae, haz, add_zero, mul_zero, AddChar.map_zero_eq_one]

end GlobalTheory.IndVac

end
