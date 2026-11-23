import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramActLStmt
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.InclusionInjective

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.NormCut Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace Formalism.L2.SG.Pf.SatGramActL

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Act

variable {D : D7} {X : HidaSetting D} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem mapLF_mul_act {Λ : Submodule (𝓞 D.host.E) (VS D).V} {β γ : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hβ : β ∈ Saturated.AutF Λ (lf D F0)) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) {T : D.host.E}
    (F : LFlag (VS D) D.R.rS T) :
    mapLF (β * γ) F = Saturated.act (⟨β, hβ⟩ : Saturated.AutF Λ (lf D F0)) (mapLF γ F) := by
  have hβi : β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := (Saturated.mem_AutF.1 hβ).1.1
  have hβγ : β * γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := (Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem hβi hγ
  have ext : ∀ {G H : LFlag (VS D) D.R.rS T}, G.fl.e = H.fl.e → G.fl.z = H.fl.z → G.zt = H.zt → G = H := by
    rintro ⟨⟨e, z, _, _, _, _⟩, zt⟩ ⟨⟨e', z', _, _, _, _⟩, zt'⟩ he hz hzt
    dsimp only at he hz hzt
    subst he hz hzt
    rfl
  have h1 : mapLF (β * γ) F = ⟨mapFlag (β * γ) hβγ F.fl, (β * γ) F.zt⟩ := by
    simp only [mapLF, dif_pos hβγ]
  have h2 : mapLF γ F = ⟨mapFlag γ hγ F.fl, γ F.zt⟩ := by
    simp only [mapLF, dif_pos hγ]
  rw [h1, h2]
  exact ext rfl rfl rfl

variable (F0 F0') in

def actC (hPD : Saturated.PDIso D) {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V} (x0 : X.B.I.GA)
    (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hx : RatLink X x0 β) (hβ : β ∈ Saturated.AutF Λ (lf D F0))
    (p : GCar X u u' F0 F0' Λ Λ') : GCar X u u' F0 F0' Λ Λ' :=
  ⟨(x0 * p.1.1, β * p.1.2), Formalism.L2.SG.Pf.ratLink_mul X hx p.2.1,
    (Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem (Saturated.mem_AutF.1 hβ).1.1 p.2.2.1,
    by rw [Formalism.L2.SG.Pf.gmap_mul, p.2.2.2.1]; exact (Saturated.mem_AutF.1 hβ).1.2,
    by rw [mapLF_mul_act hβ p.2.2.1]; exact Saturated.pd_act hPD ⟨β, hβ⟩ p.2.2.2.2⟩

theorem grel_actC (hPD : Saturated.PDIso D) {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V} (x0 : X.B.I.GA)
    (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hx : RatLink X x0 β) (hβ : β ∈ Saturated.AutF Λ (lf D F0))
    {p q : GCar X u u' F0 F0' Λ Λ'} (h : GRel X u u' F0 F0' Λ Λ' p q) :
    GRel X u u' F0 F0' Λ Λ' (actC F0 F0' hPD x0 β hx hβ p) (actC F0 F0' hPD x0 β hx hβ q) := by
  unfold GRel at h ⊢
  obtain ⟨n, hn, n', hn', hq⟩ := h
  refine ⟨β * n * β⁻¹, nlam_conj hβ hn, n', hn', ?_⟩
  show β * q.1.2 = β * n * β⁻¹ * (β * p.1.2) * n'
  rw [hq]
  simp only [mul_assoc, inv_mul_cancel_left]

variable (F0 F0') in

def actQ (hPD : Saturated.PDIso D) {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V} (x0 : X.B.I.GA)
    (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hx : RatLink X x0 β) (hβ : β ∈ Saturated.AutF Λ (lf D F0)) :
    GQ X u u' F0 F0' Λ Λ' → GQ X u u' F0 F0' Λ Λ' :=
  Quot.map (actC F0 F0' hPD x0 β hx hβ) (fun _ _ h => grel_actC hPD x0 β hx hβ h)

theorem actQ_mk (hPD : Saturated.PDIso D) {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V} (x0 : X.B.I.GA)
    (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hx : RatLink X x0 β) (hβ : β ∈ Saturated.AutF Λ (lf D F0))
    (p : GCar X u u' F0 F0' Λ Λ') :
    actQ F0 F0' hPD x0 β hx hβ (Quot.mk _ p) = Quot.mk _ (actC F0 F0' hPD x0 β hx hβ p) := rfl

theorem actQ_comp (hPD : Saturated.PDIso D) {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V} (x0 x1 : X.B.I.GA)
    (β β1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hx : RatLink X x0 β) (hx1 : RatLink X x1 β1)
    (hβ : β ∈ Saturated.AutF Λ (lf D F0)) (hβ1 : β1 ∈ Saturated.AutF Λ (lf D F0))
    (e1 : x1 * x0 = 1) (e2 : β1 * β = 1) (c : GQ X u u' F0 F0' Λ Λ') :
    actQ F0 F0' hPD x1 β1 hx1 hβ1 (actQ F0 F0' hPD x0 β hx hβ c) = c := by
  induction c using Quot.ind with
  | mk p =>
    rw [actQ_mk, actQ_mk]
    congr 1
    apply Subtype.ext
    show (x1 * (x0 * p.1.1), β1 * (β * p.1.2)) = p.1
    rw [← mul_assoc, ← mul_assoc, e1, e2, one_mul, one_mul]

variable (what₂ rows') in

def phiT (hPD : Saturated.PDIso D) (x0 : X.B.I.GA) (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hx : RatLink X x0 β)
    (t : GTerm X u u' F0 F0' what₂ rows') : GTerm X u u' F0 F0' what₂ rows' :=
  if h : β ∈ Saturated.AutF t.lam (lf D F0) then
    ⟨t.lam, t.mem, t.lam', t.mem', actQ F0 F0' hPD x0 β hx h t.cls⟩ else t

theorem phiT_pos (hPD : Saturated.PDIso D) (x0 : X.B.I.GA) (β : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hx : RatLink X x0 β) (t : GTerm X u u' F0 F0' what₂ rows') (h : β ∈ Saturated.AutF t.lam (lf D F0)) :
    phiT what₂ rows' hPD x0 β hx t = ⟨t.lam, t.mem, t.lam', t.mem', actQ F0 F0' hPD x0 β hx h t.cls⟩ := by
  simp only [phiT, dif_pos h]

theorem phiT_position (hPD : Saturated.PDIso D) (x0 : X.B.I.GA) (β : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hx : RatLink X x0 β) (t : GTerm X u u' F0 F0' what₂ rows') :
    positionT (phiT what₂ rows' hPD x0 β hx t) = positionT t := by
  unfold phiT
  split_ifs <;> rfl

theorem autF_inv_iff {Λ : Submodule (𝓞 D.host.E) (VS D).V} {β : (VS D).V ≃ₗ[D.host.E] (VS D).V} :
    β⁻¹ ∈ Saturated.AutF Λ (lf D F0) ↔ β ∈ Saturated.AutF Λ (lf D F0) := ⟨fun h => by simpa using Saturated.inv_mem_AutF' h, Saturated.inv_mem_AutF'⟩

theorem phiT_comp (hPD : Saturated.PDIso D) (x0 x1 : X.B.I.GA) (β β1 : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hx : RatLink X x0 β) (hx1 : RatLink X x1 β1) (e1 : x1 * x0 = 1) (e2 : β1 * β = 1)
    (t : GTerm X u u' F0 F0' what₂ rows') :
    phiT what₂ rows' hPD x1 β1 hx1 (phiT what₂ rows' hPD x0 β hx t) = t := by
  have hb1 : β1 = β⁻¹ := eq_inv_of_mul_eq_one_left e2
  by_cases h : β ∈ Saturated.AutF t.lam (lf D F0)
  · have h1 : β1 ∈ Saturated.AutF t.lam (lf D F0) := by
      rw [hb1]; exact Saturated.inv_mem_AutF' h
    rw [phiT_pos hPD x0 β hx t h]
    rw [phiT_pos hPD x1 β1 hx1 (⟨t.lam, t.mem, t.lam', t.mem', actQ F0 F0' hPD x0 β hx h t.cls⟩ :
      GTerm X u u' F0 F0' what₂ rows') h1]
    rw [actQ_comp hPD x0 x1 β β1 hx hx1 h h1 e1 e2]
  · have h1 : β1 ∉ Saturated.AutF t.lam (lf D F0) := by
      rw [hb1, autF_inv_iff]; exact h
    simp only [phiT, dif_neg h, dif_neg h1]

variable (what₂ rows') in

def phiE (hPD : Saturated.PDIso D) (x0 : X.B.I.GA) (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hx : RatLink X x0 β) :
    GTerm X u u' F0 F0' what₂ rows' ≃ GTerm X u u' F0 F0' what₂ rows' where
  toFun := phiT what₂ rows' hPD x0 β hx
  invFun := phiT what₂ rows' hPD x0⁻¹ β⁻¹ (Formalism.L2.SG.Pf.ratLink_inv X hx)
  left_inv t := phiT_comp hPD x0 x0⁻¹ β β⁻¹ hx _ (inv_mul_cancel x0) (inv_mul_cancel β) t
  right_inv t := phiT_comp hPD x0⁻¹ x0 β⁻¹ β _ hx (mul_inv_cancel x0) (mul_inv_cancel β) t

end Act

section FC

variable {D : D7} {X : HidaSetting D} {u u' : D.what₂.Word}

theorem roset_conj {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V} {x0 : X.B.I.GA} {β : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hx : RatLink X x0 β) (hβ : β ∈ Saturated.AutF Λ (lf D (X.Fu u))) (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    {y : X.B.I.Ginf} (hy : y ∈ ROset X (X.Fu u) (X.Fu u') Λ Λ' γ) :
    x0.1 * y * x0.1⁻¹ ∈ ROset X (X.Fu u) (X.Fu u') Λ Λ' (β * γ) := by
  obtain ⟨x, n, hxn, rfl, hn, hn'⟩ := hy
  refine ⟨x0 * x * x0⁻¹, β * n * β⁻¹,
    Formalism.L2.SG.Pf.ratLink_mul X (Formalism.L2.SG.Pf.ratLink_mul X hx hxn) (Formalism.L2.SG.Pf.ratLink_inv X hx), ?_,
    nlam_conj hβ hn, ?_⟩
  · rw [Prod.fst_mul, Prod.fst_mul, Prod.fst_inv]
  · have e : (β * γ)⁻¹ * (β * n * β⁻¹) * (β * γ) = γ⁻¹ * n * γ := by group
    rw [e]; exact hn'

theorem roset_conj' {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V} {x0 : X.B.I.GA} {β : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hx : RatLink X x0 β) (hβ : β ∈ Saturated.AutF Λ (lf D (X.Fu u))) (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    {y : X.B.I.Ginf} (hy : y ∈ ROset X (X.Fu u) (X.Fu u') Λ Λ' (β * γ)) :
    x0.1⁻¹ * y * x0.1 ∈ ROset X (X.Fu u) (X.Fu u') Λ Λ' γ := by
  obtain ⟨x, n, hxn, rfl, hn, hn'⟩ := hy
  have hβi : β⁻¹ ∈ Saturated.AutF Λ (lf D (X.Fu u)) := Saturated.inv_mem_AutF' hβ
  refine ⟨x0⁻¹ * x * x0, β⁻¹ * n * β,
    Formalism.L2.SG.Pf.ratLink_mul X (Formalism.L2.SG.Pf.ratLink_mul X (Formalism.L2.SG.Pf.ratLink_inv X hx) hxn) hx, ?_, ?_, ?_⟩
  · rw [Prod.fst_mul, Prod.fst_mul, Prod.fst_inv]
  · have := nlam_conj hβi hn
    rw [inv_inv] at this
    exact this
  · have e : γ⁻¹ * (β⁻¹ * n * β) * γ = (β * γ)⁻¹ * n * (β * γ) := by group
    rw [e]; exact hn'

theorem fundConj_holds : FundConj := by
  intro D X u u' Λ Λ' x0 β γ hx hβ Ω hΩ
  obtain ⟨hm, hcov, huniq⟩ := hΩ
  refine ⟨?_, fun x => ?_, fun x hx' s hs hsx => ?_⟩
  · exact (measurable_const_mul x0.1⁻¹) hm
  · obtain ⟨s, hs, hsx⟩ := hcov (x0.1⁻¹ * x)
    refine ⟨x0.1 * s * x0.1⁻¹, roset_conj hx hβ γ hs, ?_⟩
    show x0.1⁻¹ * (x0.1 * s * x0.1⁻¹ * x) ∈ Ω
    have e : x0.1⁻¹ * (x0.1 * s * x0.1⁻¹ * x) = s * (x0.1⁻¹ * x) := by group
    rw [e]; exact hsx
  · have hs' := roset_conj' hx hβ γ hs
    have h1 : x0.1⁻¹ * s * x0.1 * (x0.1⁻¹ * x) ∈ Ω := by
      have e : x0.1⁻¹ * s * x0.1 * (x0.1⁻¹ * x) = x0.1⁻¹ * (s * x) := by group
      rw [e]; exact hsx
    have := huniq _ hx' _ hs' h1
    have e2 : s = x0.1 * (x0.1⁻¹ * s * x0.1) * x0.1⁻¹ := by group
    rw [e2, this]; group

end FC

section SM

open Formalism.L2.SG.TermDef Formalism.L2.SG.FourParts

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {Λ : Submodule (𝓞 E) S.V}
  {r : ℕ} {T T' : E} {F : LFlag S r T}

theorem nlam_mapL {β m : S.V ≃ₗ[E] S.V} (hβ : β ∈ Formalism.HermitianLatticesTheory.isom S.hT) (hΛ : Formalism.HermitianLatticesTheory.gmap β Λ = Λ)
    {F₁ : LFlag S r T'} (hm : m ∈ NLam Λ F₁) : β * m * β⁻¹ ∈ NLam Λ (Saturated.mapL β hβ F₁) := by
  refine ⟨⟨(Formalism.HermitianLatticesTheory.isom S.hT).mul_mem ((Formalism.HermitianLatticesTheory.isom S.hT).mul_mem hβ hm.1.1) ((Formalism.HermitianLatticesTheory.isom S.hT).inv_mem hβ),
    by rw [Formalism.L2.SG.Pf.gmap_mul, Formalism.L2.SG.Pf.gmap_mul, Formalism.L2.SG.Pf.gmap_inv hΛ, hm.1.2, hΛ]⟩,
    fun j x hx => ?_, fun x hx => ?_⟩
  · change x ∈ (Formalism.L2.SG.TermOp.mapFlag β hβ F₁.fl).Xa (j + 1) at hx
    change _ ∈ (Formalism.L2.SG.TermOp.mapFlag β hβ F₁.fl).Xa j
    rw [Formalism.L2.SG.Pf.xa_mapFlag] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨m y - y, hm.2.1 j y hy, ?_⟩
    simp [Formalism.L2.SG.Pf.le_mul_app, Formalism.L2.SG.Pf.le_inv_app, map_sub]
  · change x ∈ orth S (Formalism.L2.SG.TermOp.mapFlag β hβ F₁.fl).X at hx
    change _ ∈ (Formalism.L2.SG.TermOp.mapFlag β hβ F₁.fl).X
    rw [Formalism.L2.SG.Pf.x_mapFlag] at hx ⊢
    have hy := Formalism.L2.SG.Pf.orth_map β hβ _ x hx
    refine ⟨m (β.symm x) - β.symm x, hm.2.2 _ hy, ?_⟩
    simp [Formalism.L2.SG.Pf.le_mul_app, Formalism.L2.SG.Pf.le_inv_app, map_sub]

theorem isometry_fix_flagAnisotropicVector_of_fix_frame {β : S.V ≃ₗ[E] S.V} (hβ : β ∈ Saturated.AutF Λ F) : β F.fl.z = F.fl.z := by
  have hl := (Saturated.mem_AutF.1 hβ).2.1 (Fin.last r)
  rwa [Formalism.L2.SG.Pf.frame_last_td] at hl

theorem dcrel_act {β : S.V ≃ₗ[E] S.V} (hβ : β ∈ Saturated.AutF Λ F) {F₁ F₂ : LFlag S r T'}
    (h : DCRel Λ F F₁ F₂) : DCRel Λ F (Saturated.act ⟨β, hβ⟩ F₁) (Saturated.act ⟨β, hβ⟩ F₂) := by
  obtain ⟨n, hn, m, hm, hf, hz⟩ := h
  have hβA := (Saturated.mem_AutF.1 hβ).1
  refine ⟨β * n * β⁻¹, nlam_conj hβ hn, β * m * β⁻¹, nlam_mapL hβA.1 hβA.2 hm, fun a => ?_, ?_⟩
  · simp only [Saturated.act, Saturated.frame_mapL, hf a, Formalism.L2.SG.Pf.le_mul_app, Formalism.L2.SG.Pf.le_inv_app,
      LinearEquiv.symm_apply_apply]
  · simp only [Saturated.act, Saturated.mapL, hz, Formalism.L2.SG.Pf.le_mul_app, Formalism.L2.SG.Pf.le_inv_app,
      LinearEquiv.symm_apply_apply]

theorem idF_act {β : S.V ≃ₗ[E] S.V} (hβ : β ∈ Saturated.AutF Λ F) {F₁ : LFlag S r T'} (h : IsIdF Λ F F₁) :
    IsIdF Λ F (Saturated.act ⟨β, hβ⟩ F₁) := by
  obtain ⟨n, hn, he, hz⟩ := h
  refine ⟨β * n * β⁻¹, nlam_conj hβ hn, fun a => ?_, ?_⟩
  · show β (n (β⁻¹ (F.fl.e a))) = β (F₁.fl.e a)
    rw [inv_fix (fix_e hβ a), he a]
  · show β (n (β⁻¹ F.fl.z)) - β F₁.fl.z ∈ Xsp F
    rw [inv_fix (isometry_fix_flagAnisotropicVector_of_fix_frame hβ), ← map_sub, fix_xsp hβ _ hz]
    exact hz

variable {P : LFlag S r T' → Prop}

theorem mk_act {β : S.V ≃ₗ[E] S.V} (hβ : β ∈ Saturated.AutF Λ F)
    (hP : ∀ x : Carrier P, P (Saturated.act ⟨β, hβ⟩ x.1)) {x y : Carrier P} (h : mk Λ F P x = mk Λ F P y) :
    mk Λ F P ⟨Saturated.act ⟨β, hβ⟩ x.1, hP x⟩ = mk Λ F P ⟨Saturated.act ⟨β, hβ⟩ y.1, hP y⟩ :=
  const_of_mk (fun z : Carrier P => mk Λ F P ⟨Saturated.act ⟨β, hβ⟩ z.1, hP z⟩)
    (fun a b hab => Quot.sound (dcrel_act hβ hab)) h

theorem idT_act {β : S.V ≃ₗ[E] S.V} (hβ : β ∈ Saturated.AutF Λ F)
    (hP : ∀ x : Carrier P, P (Saturated.act ⟨β, hβ⟩ x.1)) {x : Carrier P} (h : IsIdT Λ F P (mk Λ F P x)) :
    IsIdT Λ F P (mk Λ F P ⟨Saturated.act ⟨β, hβ⟩ x.1, hP x⟩) := by
  obtain ⟨F₁, ⟨h₁, hmk⟩, hid⟩ := h
  exact ⟨Saturated.act ⟨β, hβ⟩ F₁, ⟨hP ⟨F₁, h₁⟩, mk_act hβ hP hmk⟩, idF_act hβ hid⟩

theorem act_inv_act {β : S.V ≃ₗ[E] S.V} (hβ : β ∈ Saturated.AutF Λ F) (F₁ : LFlag S r T') :
    Saturated.act ⟨β⁻¹, Saturated.inv_mem_AutF' hβ⟩ (Saturated.act ⟨β, hβ⟩ F₁) = F₁ := by
  have key : ∀ x : S.V, β⁻¹ (β x) = x := fun x => β.symm_apply_apply x
  have ext : ∀ {G H : LFlag S r T'}, G.fl.e = H.fl.e → G.fl.z = H.fl.z → G.zt = H.zt → G = H := by
    rintro ⟨⟨e, z, _, _, _, _⟩, zt⟩ ⟨⟨e', z', _, _, _, _⟩, zt'⟩ he hz hzt
    dsimp only at he hz hzt
    subst he hz hzt
    rfl
  exact ext (funext fun a => key _) (key _) (key _)

end SM

section SMC

open Formalism.L2.SG.TermDef Formalism.L2.SG.FourParts

theorem sMemLeft_holds (hGen : ∀ D : D7, Saturated.GenIso (VS D) D.R.rS (gS D))
    (hPD : ∀ D : D7, Saturated.PDIso D) : SMemLeft := by
  intro D X Y u u' t t' β hβ hl hl' hnn S hS ht
  obtain ⟨n, hn, n', hn', he⟩ := hnn
  obtain ⟨lam2, mem2, lam2', mem2', cls2⟩ := t'
  simp only at hl hl'
  subst hl hl'
  set t' : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') := ⟨t.lam, mem2, t.lam', mem2', cls2⟩ with ht'
  have hβA := (Saturated.mem_AutF.1 hβ).1
  have hβγ : β * t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := (Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem hβA.1 t.rep.2.2.1
  have hdc : DCRel t.lam (lf D (X.Fu u)) (mapLF (β * t.lin) (lf D (X.Fu u'))) (mapLF t'.lin (lf D (X.Fu u'))) :=
    Formalism.L2.SG.Pf.dcrel_of (lf D (X.Fu u)) (lf D (X.Fu u')) hβγ t'.rep.2.2.1
      ((Formalism.L2.SG.Pf.gmap_mul _ _ _).trans ((congrArg (Formalism.HermitianLatticesTheory.gmap β) t.rep.2.2.2.1).trans hβA.2)) hn hn' he
  have hP : ∀ x : Carrier (PD D t.lam (lf D (X.Fu u)) u'),
      PD D t.lam (lf D (X.Fu u)) u' (Saturated.act ⟨β, hβ⟩ x.1) := fun x => Saturated.pd_act (hPD D) ⟨β, hβ⟩ x.2
  let x : Carrier (PD D t.lam (lf D (X.Fu u)) u') := ⟨t.frame, t.rep.2.2.2.2⟩
  let c1 : Carrier (PD D t.lam (lf D (X.Fu u)) u') := ⟨Saturated.act ⟨β, hβ⟩ x.1, hP x⟩
  have hdc' : DCRel t.lam (lf D (X.Fu u)) c1.1 (mapLF t'.lin (lf D (X.Fu u'))) :=
    have e : c1.1 = mapLF (β * t.lin) (lf D (X.Fu u')) := (mapLF_mul_act hβ t.rep.2.2.1 (lf D (X.Fu u'))).symm
    e ▸ hdc
  have hc : t.toTerm.cls = mk t.lam (lf D (X.Fu u)) (PD D t.lam (lf D (X.Fu u)) u') x := rfl
  have hc' : t'.toTerm.cls = mk t.lam (lf D (X.Fu u)) (PD D t.lam (lf D (X.Fu u)) u') c1 :=
    (Quot.sound (r := Rel t.lam (lf D (X.Fu u)) (PD D t.lam (lf D (X.Fu u)) u'))
      (a := c1) (b := ⟨mapLF t'.lin (lf D (X.Fu u')), t'.rep.2.2.2.2⟩) hdc').symm
  have hΛ := (Y.rowsOK u).1 t.lam t.mem
  have hTF := Formalism.L2.SG.Closed.TermFun_holds D u u' (X.Fu u) t.lam hΛ
  have hG : t'.G = t.G := by
    have a1 : Gt t.lam (lf D (X.Fu u)) (PD D t.lam (lf D (X.Fu u)) u')
        (mk t.lam (lf D (X.Fu u)) (PD D t.lam (lf D (X.Fu u)) u') c1) = Gval (lf D (X.Fu u)) c1.1 :=
      Gt_mk hTF.1 c1
    have a2 : Gt t.lam (lf D (X.Fu u)) (PD D t.lam (lf D (X.Fu u)) u')
        (mk t.lam (lf D (X.Fu u)) (PD D t.lam (lf D (X.Fu u)) u') x) = Gval (lf D (X.Fu u)) x.1 :=
      Gt_mk hTF.1 x
    have a3 : Gval (lf D (X.Fu u)) c1.1 = Gval (lf D (X.Fu u)) x.1 := Saturated.gval_act ⟨β, hβ⟩ x.1
    exact (congrArg (Gt t.lam (lf D (X.Fu u)) (PD D t.lam (lf D (X.Fu u)) u')) hc').trans
      (a1.trans (a3.trans a2.symm))
  have hGt : Formalism.L2.SG.TermOp.Gt t' = Formalism.L2.SG.TermOp.Gt t := by
    unfold Formalism.L2.SG.TermOp.Gt; rw [hG]
  have hsat := Saturated.sat_gen (hGen D) hTF.2.2.2.1
  have hgen : t.generic → t'.generic := by
    intro h
    have := hsat.1 ⟨β, hβ⟩ x (hP x) h
    exact cast (congrArg (fun c => IsGen t.lam (lf D (X.Fu u)) (PD D t.lam (lf D (X.Fu u)) u') (gS D) c) hc').symm this
  have hngen : ¬ t.generic → ¬ t'.generic := by
    intro h
    have := hsat.2 ⟨β, hβ⟩ x (hP x) h
    exact cast (congrArg (fun c => ¬ IsGen t.lam (lf D (X.Fu u)) (PD D t.lam (lf D (X.Fu u)) u') (gS D) c) hc').symm this
  have hid : t'.isId → t.isId := by
    intro h
    have h' : IsIdT t.lam (lf D (X.Fu u)) (PD D t.lam (lf D (X.Fu u)) u')
        (mk t.lam (lf D (X.Fu u)) (PD D t.lam (lf D (X.Fu u)) u') c1) :=
      cast (congrArg (fun c => IsIdT t.lam (lf D (X.Fu u)) (PD D t.lam (lf D (X.Fu u)) u') c) hc') h
    have hβi : β⁻¹ ∈ Saturated.AutF t.lam (lf D (X.Fu u)) := Saturated.inv_mem_AutF' hβ
    have hPi : ∀ y : Carrier (PD D t.lam (lf D (X.Fu u)) u'),
        PD D t.lam (lf D (X.Fu u)) u' (Saturated.act ⟨β⁻¹, hβi⟩ y.1) :=
      fun y => Saturated.pd_act (hPD D) ⟨β⁻¹, hβi⟩ y.2
    have h2 := idT_act hβi hPi h'
    have e : (⟨Saturated.act ⟨β⁻¹, hβi⟩ c1.1, hPi c1⟩ : Carrier (PD D t.lam (lf D (X.Fu u)) u')) = x :=
      Subtype.ext (act_inv_act hβ x.1)
    rw [e] at h2
    exact h2
  rcases hS with rfl | rfl | rfl
  · change Formalism.L2.SG.TermOp.Gt t ≠ 0 ∧ t.generic at ht
    show Formalism.L2.SG.TermOp.Gt t' ≠ 0 ∧ t'.generic
    rw [hGt]; exact ⟨ht.1, hgen ht.2⟩
  · change Formalism.L2.SG.TermOp.Gt t ≠ 0 ∧ ¬ t.generic at ht
    show Formalism.L2.SG.TermOp.Gt t' ≠ 0 ∧ ¬ t'.generic
    rw [hGt]; exact ⟨ht.1, hngen ht.2⟩
  · change Formalism.L2.SG.TermOp.Gt t = 0 ∧ ¬ t.isId at ht
    show Formalism.L2.SG.TermOp.Gt t' = 0 ∧ ¬ t'.isId
    rw [hGt]; exact ⟨ht.1, fun h => ht.2 (hid h)⟩

end SMC

section BL

open Matrix

variable {D : D7} (X : HidaSetting D)

theorem crd_inj {y y' : (VS D).V} (h : X.crd y = X.crd y') : y = y' := by
  apply X.bas.repr.injective
  ext i
  have hi := congrArg X.ιE (congrFun h i)
  simpa only [HidaSetting.crd, crdOf, RingEquiv.apply_symm_apply] using hi

def linM (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) : (VS D).V →ₗ[D.host.E] (VS D).V :=
  Matrix.toLin X.bas X.bas (M.map X.ιE)

theorem crd_linM (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) (y : (VS D).V) :
    X.crd (linM X M y) = M *ᵥ X.crd y := by
  funext i
  have h := LinearMap.toMatrix_mulVec_repr X.bas X.bas (linM X M) y
  simp only [linM, LinearMap.toMatrix_toLin] at h
  simp only [HidaSetting.crd, crdOf, linM]
  rw [← h]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, RingEquiv.symm_apply_apply]
  rfl

def linGL (M : GL (Fin X.B.I.n) X.B.I.E) : (VS D).V ≃ₗ[D.host.E] (VS D).V :=
  LinearEquiv.ofLinear (linM X (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E))
    (linM X ((M⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E))
    (LinearMap.ext fun y => crd_inj X (by
      rw [LinearMap.comp_apply, crd_linM, crd_linM, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, Matrix.one_mulVec]; rfl))
    (LinearMap.ext fun y => crd_inj X (by
      rw [LinearMap.comp_apply, crd_linM, crd_linM, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, Matrix.one_mulVec]; rfl))

theorem crd_linGL (M : GL (Fin X.B.I.n) X.B.I.E) (y : (VS D).V) :
    X.crd (linGL X M y) = (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd y := crd_linM X _ y

theorem incl_inj {a b : Fin X.B.I.n → X.B.I.E} (h : incl X.B.I a = incl X.B.I b) : a = b := by
  haveI := Formalism.L2.SG.Pf.Level.af_ntriv X.B.I.F
  have hinj : Function.Injective (Formalism.UG.inclE (F := X.B.I.F) (E := X.B.I.E) (Af X.B.I.F)) := by
    first
      | exact Algebra.TensorProduct.includeLeft_injective (S := X.B.I.F) (RingHom.injective _)
      | exact Algebra.TensorProduct.includeLeft_injective (R := X.B.I.F) (RingHom.injective _)
      | exact Algebra.TensorProduct.includeLeft_injective (RingHom.injective _)
  funext i
  exact hinj (congrFun h i)

theorem fmat_mul (a b : X.B.I.Gf) : X.B.I.fmat (a * b) = X.B.I.fmat a * X.B.I.fmat b := Formalism.L2.SG.PoincareInHH.Cut.fmat_mul X a b

theorem betaLift_holds : BetaLift := by
  intro D X w rs c Λ hΛ γ hk
  obtain ⟨M, hM, h1, h2⟩ : (γ : X.B.I.GA) ∈ X.B.I.GFset := (Subgroup.mem_inf.1 γ.2).1
  have hH : (γ : X.B.I.GA).2 ∈ Hfin X w := (Subgroup.mem_prod.1 (Subgroup.mem_inf.1 γ.2).2).2
  let β := linGL X M
  have hcrd : ∀ y, X.crd (β y) = (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd y := crd_linGL X M

  have hfix : ∀ y, X.crd y ∈ fixSet X w → β y = y := by
    intro y hy
    apply crd_inj X
    rw [hcrd]
    apply incl_inj X
    rw [← Formalism.L2.SG.Pf.incl_mulVec X, ← h2]
    exact hH _ hy
  refine ⟨β, ⟨M, hM, h1, h2, hcrd⟩, ⟨⟨fun x y => ?_, ?_⟩, fun a => ?_, ?_⟩⟩
  · rw [← Formalism.L2.SG.PoincareInHH.Cut.hform_crd, ← Formalism.L2.SG.PoincareInHH.Cut.hform_crd, hcrd, hcrd,
      Formalism.L2.SG.PoincareInHH.Cut.hform_mulVec _ _ _ hM]
  · ext y
    rw [Saturated.mem_gmap_iff]
    set H : X.B.I.Gf := (c.h (c.base Λ) : X.B.I.Gf) * X.xu w
    have hb := c.base_lam Λ hΛ
    have key : ∀ z, (z ∈ Λ ↔ X.B.I.fmat H⁻¹ *ᵥ incl X.B.I (X.crd z) ∈ X.B.I.Lf) := by
      intro z
      have := c.lat_eq (c.base Λ) z
      rw [hb] at this
      exact this
    have hk' : kB c Λ γ = H⁻¹ * (γ : X.B.I.GA).2 * H := rfl
    have e : X.B.I.fmat H⁻¹ *ᵥ incl X.B.I (X.crd y) =
        X.B.I.fmat (kB c Λ γ) *ᵥ (X.B.I.fmat H⁻¹ *ᵥ incl X.B.I (X.crd (β.symm y))) := by
      have ey : y = β (β.symm y) := (β.apply_symm_apply y).symm
      conv_lhs => rw [ey]
      rw [hcrd, ← Formalism.L2.SG.Pf.incl_mulVec X, ← h2, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← fmat_mul X,
        ← fmat_mul X, hk']
      congr 2
      group
    rw [key y, key (β.symm y), e]
    set v := X.B.I.fmat H⁻¹ *ᵥ incl X.B.I (X.crd (β.symm y)) with hv
    constructor
    · intro h
      exact Formalism.L2.SG.Pf.unitaryCongruence.K_mv X.B.I hk h
    · intro h
      have := Formalism.L2.SG.Pf.unitaryCongruence.K_mv X.B.I (Formalism.L2.SG.Pf.unitaryCongruence.K_inv X.B.I hk) h
      rwa [Matrix.mulVec_mulVec, ← fmat_mul X, inv_mul_cancel, show X.B.I.fmat 1 = 1 by simp [AutInst.fmat],
        Matrix.one_mulVec] at this
  · refine Fin.lastCases ?_ (fun i => ?_) a
    · show β ((lf D (X.Fu w)).fl.fvec (Fin.last _)) = (lf D (X.Fu w)).fl.fvec (Fin.last _)
      unfold FlagG.fvec
      rw [Fin.snoc_last]
      change β (X.Fu w).z = (X.Fu w).z
      rw [X.flagZVector w]
      exact hfix _ (Or.inr rfl)
    · show β ((lf D (X.Fu w)).fl.fvec (Fin.castSucc i)) = (lf D (X.Fu w)).fl.fvec (Fin.castSucc i)
      unfold FlagG.fvec
      rw [Fin.snoc_castSucc]
      change β ((X.Fu w).e i) = (X.Fu w).e i
      rw [X.Fu_e w]
      exact hfix _ (Or.inl (Or.inl ⟨i, rfl⟩))
  · show β (X.Fu w).z = (X.Fu w).z
    rw [X.flagZVector w]
    exact hfix _ (Or.inr rfl)

end BL

section HS

variable {D : D7} {X : HidaSetting D}

def piUe (w : D.what₂.Word) (s : X.B.I.Ginf) (hs : s ∈ Hinf X w) : X.Vpi w ≃ₗᵢ[ℂ] X.Vpi w :=
  have hsS : s ∈ X.SinfU w := hinf_le_sinf X w s hs
  have hsS' : s⁻¹ ∈ X.SinfU w := hinf_le_sinf X w s⁻¹ ((Hinf X w).inv_mem hs)
  have e1 : X.piU w s * X.piU w s⁻¹ = 1 := by
    rw [← (X.piU_rep w).2.1 _ hsS _ hsS', mul_inv_cancel, (X.piU_rep w).1]
  have e2 : X.piU w s⁻¹ * X.piU w s = 1 := by
    rw [← (X.piU_rep w).2.1 _ hsS' _ hsS, inv_mul_cancel, (X.piU_rep w).1]
  { toLinearEquiv := LinearEquiv.ofLinearMap (X.piU w s).toLinearMap (X.piU w s⁻¹).toLinearMap
      (LinearMap.ext fun v => by
        have := congrArg (fun A : X.Vpi w →L[ℂ] X.Vpi w => A v) e1
        simpa using this)
      (LinearMap.ext fun v => by
        have := congrArg (fun A : X.Vpi w →L[ℂ] X.Vpi w => A v) e2
        simpa using this)
    norm_map' := (LinearMap.isometryOfInner (X.piU w s).toLinearMap
      (fun x y => (X.piU_rep w).2.2.1 s hsS x y)).norm_map }

theorem piUe_apply (w : D.what₂.Word) (s : X.B.I.Ginf) (hs : s ∈ Hinf X w) (v : X.Vpi w) :
    piUe w s hs v = X.piU w s v := rfl

end HS

section HSc

variable {Wq Wp : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]

def hsL (P : Wp ≃ₗᵢ[ℂ] Wp) : Formalism.L2.SG.PackageTie.HS Wq Wp ≃ₗᵢ[ℂ] Formalism.L2.SG.PackageTie.HS Wq Wp :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun _ => P)

theorem hsL_emb (P : Wp ≃ₗᵢ[ℂ] Wp) (A : Wq →L[ℂ] Wp) :
    hsL P (Formalism.L2.SG.PackageTie.hsEmb A) =
      Formalism.L2.SG.PackageTie.hsEmb ((P.toContinuousLinearEquiv : Wp →L[ℂ] Wp).comp A) := by
  first
    | ext i
      simp [hsL, Formalism.L2.SG.PackageTie.hsEmb]
    | simp [hsL, Formalism.L2.SG.PackageTie.hsEmb]
    | rfl

end HSc

section OOL

variable {D : D7} (X : HidaSetting D)

theorem psiInfU_one' (w : D.what₂.Word) : X.psiInfU w 1 = 1 := by
  have h1m : (1 : X.B.I.Ginf) ∈ X.SinfU w := hinf_le_sinf X w 1 (Hinf X w).one_mem
  have h1 : ∀ x, X.Wu w x = X.psiInfU w 1 • X.Wu w x := fun x => by
    have e : X.Wu w (1 * x) = X.psiInfU w 1 • X.piU w 1 (X.Wu w x) := (X.Wu_spec w).1 1 h1m x
    rwa [one_mul, (X.piU_rep w).1, ContinuousLinearMap.one_apply] at e
  by_contra hne
  have h0 : ∀ x, X.Wu w x = 0 := fun x => by
    have h2 : (1 - X.psiInfU w 1) • X.Wu w x = 0 := by rw [sub_smul, one_smul, ← h1 x, sub_self]
    exact (smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (Ne.symm hne))
  have := (X.Wu_spec w).2.2.2.2
  simp [h0] at this

theorem wu_left (w : D.what₂.Word) {s : X.B.I.Ginf} (hs : s ∈ Hinf X w) (x : X.B.I.Ginf) :
    X.Wu w (s * x) = X.piU w s (X.Wu w x) := by
  have h1 : X.Wu w (s * x) = X.psiInfU w s • X.piU w s (X.Wu w x) :=
    (X.Wu_spec w).1 s (hinf_le_sinf X w s hs) x
  have hp : X.psiInfU w s = 1 := by
    have := Formalism.L2.SG.PoincareInHH.Cut.psiInf_mul_H X w 1 s hs
    rw [one_mul] at this
    rw [this, psiInfU_one']
  rw [h1, hp, one_smul]

theorem rankOne_map_left_eq_comp {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] (A : V →L[ℂ] V) (v : V) (w : V') :
    rk1 (A v) w = A.comp (rk1 v w) := by
  ext x
  simp only [rk1, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, map_smul]

theorem ooLeft_holds : OOLeft := by
  intro D X u u' s hs Ω y _
  have := FiniteDimensional.complete ℂ (X.Vpi u)
  let L : (X.Vpi u' →L[ℂ] X.Vpi u) ≃L[ℂ] (X.Vpi u' →L[ℂ] X.Vpi u) :=
    (ContinuousLinearEquiv.refl ℂ (X.Vpi u')).arrowCongr (piUe u s hs).toContinuousLinearEquiv
  have hL : ∀ f, L f = (X.piU u s).comp f := fun f => by
    ext ξ; rfl
  unfold OO
  rw [← Set.image_mul_left, Formalism.L2.SG.TermOp.Vanish.setIntegral_image_mul]
  have hpt : ∀ x, rk1 (X.Wu u (s * x)) (X.Wu u' ((s * y)⁻¹ * (s * x))) = L (rk1 (X.Wu u x) (X.Wu u' (y⁻¹ * x))) := by
    intro x
    have e : (s * y)⁻¹ * (s * x) = y⁻¹ * x := by group
    rw [e, wu_left X u hs, rankOne_map_left_eq_comp, hL]
  simp_rw [hpt]
  rw [ContinuousLinearEquiv.integral_comp_comm, hL]

end OOL

section Main

open Formalism.L2.SG.Pf.SatGramRep

theorem fundOf_spec {D : D7} {X : HidaSetting D} {u u' : D.what₂.Word}
    {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
    {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (hF : FundExists X u u' F0 F0' what₂ rows')
    (t : GTerm X u u' F0 F0' what₂ rows') : IsSFund X.B.I (ROinf t) (FundOf t) := by
  unfold FundOf; rw [dif_pos (hF t)]; exact (hF t).choose_spec

theorem kOf_mul {D : D7} {X : HidaSetting D} (u u' : D.what₂.Word) (a b : X.B.I.Gf) (x0 x : X.B.I.GA) :
    kOf X u u' a b (x0 * x) = ((a * X.xu u)⁻¹ * x0.2 * (a * X.xu u)) * kOf X u u' a b x := by
  unfold kOf; rw [Prod.snd_mul]; group

theorem left_action_three_families (hPD : ∀ D : D7, Saturated.PDIso D) (hB : BetaLift) (hSM : SMemLeft) (hIL : IotaLeft)
    (hCL : ChiNLeft) (hOL : OOLeft) (hFC : FundConj) (hIR : IotaRepC) (hAR : AmpRepNC) : LeftActC' := by
  intro D X Y u u' hOI _ _ S hS q b hb
  obtain ⟨γ, hk, rfl⟩ := hb
  have hk' : kB (Y.cs u) q.1.1 γ ∈ X.B.I.Kset := hk
  obtain ⟨β, hx, hβ⟩ := hB D X u (Y.what₂ u) (Y.cs u) q.1.1 q.1.2 γ hk'
  have hs : (γ : X.B.I.GA).1 ∈ Hinf X u := (Subgroup.mem_prod.1 (Subgroup.mem_inf.1 γ.2).2).1
  have hF := Formalism.L2.SG.Pf.fundExistsC_holds D X Y u u'

  have key : ∀ t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'), positionT t = q →
      ∃ hβt : β ∈ Saturated.AutF t.lam (lf D (X.Fu u)), t.lam = q.1.1 ∧
        phiT (Y.what₂ u) (Y.what₂ u') (hPD D) (γ : X.B.I.GA) β hx t =
          ⟨t.lam, t.mem, t.lam', t.mem', actQ (X.Fu u) (X.Fu u') (hPD D) (γ : X.B.I.GA) β hx hβt t.cls⟩ := by
    intro t ht
    have hl : t.lam = q.1.1 := congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) ht
    have hβt : β ∈ Saturated.AutF t.lam (lf D (X.Fu u)) := hl ▸ hβ
    exact ⟨hβt, hl, phiT_pos (hPD D) _ β hx t hβt⟩
  have hcls : ∀ (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'))
      (hβt : β ∈ Saturated.AutF t.lam (lf D (X.Fu u))),
      actQ (X.Fu u) (X.Fu u') (hPD D) (γ : X.B.I.GA) β hx hβt t.cls =
        Quot.mk _ (actC (X.Fu u) (X.Fu u') (hPD D) (γ : X.B.I.GA) β hx hβt t.rep) := by
    intro t hβt
    conv_lhs => rw [← Quot.out_eq t.cls]
    rfl

  have memS : ∀ t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'), positionT t = q →
      (t ∈ S ↔ phiT (Y.what₂ u) (Y.what₂ u') (hPD D) (γ : X.B.I.GA) β hx t ∈ S) := by
    intro t ht
    obtain ⟨hβt, -, he⟩ := key t ht
    rw [he]
    set t' : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') :=
      ⟨t.lam, t.mem, t.lam', t.mem', actQ (X.Fu u) (X.Fu u') (hPD D) (γ : X.B.I.GA) β hx hβt t.cls⟩
    obtain ⟨n, hn, n', hn', e⟩ := grel_rep t' _ (hcls t hβt)

    have e' : β * t.lin = n * t'.lin * n' := e
    constructor
    · refine hSM D X Y u u' t t' β hβt rfl rfl ⟨n⁻¹, Formalism.L2.SG.Pf.nlam_inv hn, n'⁻¹, Formalism.L2.SG.Pf.nlam_inv hn', ?_⟩ S hS
      rw [e']; group
    · have hβi : β⁻¹ ∈ Saturated.AutF t'.lam (lf D (X.Fu u)) := Saturated.inv_mem_AutF' hβt
      refine hSM D X Y u u' t' t β⁻¹ hβi rfl rfl ⟨β⁻¹ * n * β, ?_, n', hn', ?_⟩ S hS
      · have := nlam_conj hβi hn
        simpa using this
      · have : t.lin = β⁻¹ * (n * t'.lin * n') := by rw [← e']; group
        rw [this]; group
  refine ⟨phiE (Y.what₂ u) (Y.what₂ u') (hPD D) (γ : X.B.I.GA) β hx, hsL (piUe u (γ : X.B.I.GA).1 hs), ?_, ?_, ?_⟩
  · intro t
    show (t ∈ S ∧ positionT t = q) ↔ (phiT _ _ _ _ β hx t ∈ S ∧ positionT (phiT _ _ _ _ β hx t) = q)
    have hsl : positionT (phiT (Y.what₂ u) (Y.what₂ u') (hPD D) (γ : X.B.I.GA) β hx t) = positionT t :=
      phiT_position (hPD D) _ β hx t
    rw [hsl]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨(memS t h2).1 h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨(memS t h2).2 h1, h2⟩
  · intro t _ ht
    obtain ⟨hβt, hl, he⟩ := key t ht
    show iotaOf Y.TR (Y.cs u) (Y.cs u') (phiT _ _ _ _ β hx t) = _
    rw [he]
    let t' : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') :=
      ⟨t.lam, t.mem, t.lam', t.mem', actQ (X.Fu u) (X.Fu u') (hPD D) (γ : X.B.I.GA) β hx hβt t.cls⟩
    rw [iotaOf_of_mk (hIR D X Y u u') t' (actC (X.Fu u) (X.Fu u') (hPD D) (γ : X.B.I.GA) β hx hβt t.rep)
      (hcls t hβt)]
    rw [iotaOf_of_mk (hIR D X Y u u') t t.rep (Quot.out_eq t.cls).symm]
    have hIL' := hIL D X Y u u' t γ (hl ▸ hk')
    have hb' : kB (Y.cs u) q.1.1 γ = kB (Y.cs u) t.lam γ := by rw [hl]
    have e1 : levi Y.TR (kOf X u u' ((Y.cs u).h ((Y.cs u).base t.lam) : X.B.I.Gf)
        ((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) ((γ : X.B.I.GA) * t.rep.1.1)) =
        levi Y.TR (kB (Y.cs u) q.1.1 γ) * levi Y.TR (kBB Y u u' t.lam t.lam' t.rep.1.1) := by
      rw [kOf_mul, hb']; exact hIL'
    exact e1
  · intro t _ ht
    obtain ⟨hβt, hl, he⟩ := key t ht
    show Formalism.L2.SG.PackageTie.hsEmb (ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') (phiT _ _ _ _ β hx t)) =
      hsL (piUe u (γ : X.B.I.GA).1 hs) (Formalism.L2.SG.PackageTie.hsEmb (ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t))
    rw [he]
    let t' : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') :=
      ⟨t.lam, t.mem, t.lam', t.mem', actQ (X.Fu u) (X.Fu u') (hPD D) (γ : X.B.I.GA) β hx hβt t.cls⟩
    have hft := fundOf_spec hF t
    have hΩ := hFC D X u u' t.lam t.lam' (γ : X.B.I.GA) β t.lin hx hβt (FundOf t) hft
    rw [ampN_of_mk (Y.FN u) (Y.FN u') (hAR D X Y u u') hF hOI t'
      (actC (X.Fu u) (X.Fu u') (hPD D) (γ : X.B.I.GA) β hx hβt t.rep) (hcls t hβt) _ hΩ]
    rw [hsL_emb]
    refine congrArg (fun A => Formalism.L2.SG.PackageTie.hsEmb A) ?_
    have hU : ((piUe u (γ : X.B.I.GA).1 hs).toContinuousLinearEquiv : X.Vpi u →L[ℂ] X.Vpi u) =
        X.piU u (γ : X.B.I.GA).1 := by
      ext v; rfl
    have hOO := hOL D X u u' _ hs (FundOf t) t.rep.1.1.1 hft.1
    have hCL' := hCL D X Y u u' t.lam t.lam' t.mem t.mem' γ (hl ▸ hk') t.rep
    have eκ : chiN X (kOf X u u' ((Y.cs u).h ((Y.cs u).base t.lam) : X.B.I.Gf)
        ((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) ((γ : X.B.I.GA) * t.rep.1.1)) =
        chiN X (kBB Y u u' t.lam t.lam' t.rep.1.1) := by
      rw [kOf_mul]; exact hCL'
    have eO : ((γ : X.B.I.GA) * t.rep.1.1).1 = (γ : X.B.I.GA).1 * t.rep.1.1.1 := Prod.fst_mul _ _
    dsimp only [t']
    simp only [actC]
    rw [eκ, eO, hOO, hU]
    unfold ampN OOt GTerm.pt kBB
    rw [ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_smul]

end Main

end Formalism.L2.SG.Pf.SatGramActL
