import Formalism.LocalToGlobal.HermitianForms.TiedTwSame
import Formalism.LocalToGlobal.HermitianForms.TiedTwJSym
import Formalism.LocalToGlobal.HermitianForms.BothSym

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Herm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure TwChJointS {D : D7} {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop} (T : TwChTied D inQ)
    (H : HermColsCh D) where

  gOf : ∀ u μ i, T.Ch u μ i → H.Ch u i

  Uloc_off : ∀ u μ i (h1 : 1 ≤ i) (hm : i ≤ D.R.m) (β : T.Ch u μ i) (v : HeightOneSpectrum (𝓞 D.host.F)), v ∉ T.Q μ →
    (i + 1 ≠ D.R.m ∨ v ∉ Formalism.L2.Forms.badG D) →
    (T.lev u μ i h1 hm β).Uloc v = (H.lev u i h1 hm (gOf u μ i β)).Uloc v
  Lb_off : ∀ u μ i (h1 : 1 ≤ i) (hm : i ≤ D.R.m) (β : T.Ch u μ i) (v : HeightOneSpectrum (𝓞 D.host.F)), v ∉ T.Q μ →
    locL v (T.lev u μ i h1 hm β).Lb = locL v (H.lev u i h1 hm (gOf u μ i β)).Lb
  Q_off : ∀ u μ, ∀ v ∈ T.Q μ, (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal ∧ ∀ a, (D.host.g a : 𝓞 D.host.F) ∉ v.asIdeal

end Formalism.L2.Herm

namespace Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def eYS {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (F : FormsTiedSym D u Ch chOf) (i : ℕ)
    (hi : i ≤ D.R.m) : (D.mem u).C.Y i ≃ Fr D i hi :=
  if h : i = 0 ∨ i = D.R.m then (F.val i hi h).eY else F.eYC i (by omega) (by omega)

theorem eYS_end {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (F : FormsTiedSym D u Ch chOf) (i : ℕ)
    (hi : i ≤ D.R.m) (h : i = 0 ∨ i = D.R.m) : eYS F i hi = (F.val i hi h).eY := by
  rw [eYS, dif_pos h]

theorem eYS_mid {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (F : FormsTiedSym D u Ch chOf) (i : ℕ)
    (h1 : 1 ≤ i) (h2 : i + 1 ≤ D.R.m) : eYS F i (le_of_succ_m h2) = F.eYC i h1 h2 := by
  have hn : ¬(i = 0 ∨ i = D.R.m) := by omega
  rw [eYS, dif_neg hn]

theorem eYS_de {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (F : FormsTiedSym D u Ch chOf) (i : ℕ)
    (hi : i ≤ D.R.m) :
    ∃ C : GL (Fin (D.R.N i)) D.host.E,
      cT (sigD D : D.host.E →+* D.host.E) C.1 * C.1 = gramN D i hi ∧
      (∀ x : Fin (D.R.N i) → D.host.E, x ∈ selfDualLatticeCoords D i hi ↔ ∀ a, (C.1 *ᵥ x) a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) ∧
      ∀ τ z, (D.mem u).C.de i z τ = embT D τ C.1.det * ((eYS F i hi z).1 τ).det := by
  by_cases h : i = 0 ∨ i = D.R.m
  · rw [eYS_end F i hi h]
    exact (F.val i hi h).de
  · have h1 : 1 ≤ i := by omega
    have h2 : i + 1 ≤ D.R.m := by omega
    have e : eYS F i hi = F.eYC i h1 h2 := eYS_mid F i h1 h2
    rw [e]
    exact F.deC i h1 h2

variable {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop}

def twYS (T : Formalism.L2.Herm.TwChTied D inQ) {Ch : D.what₂.Word → ℕ → Type} {chOf : ∀ u i, (D.mem u).C.cls i → Ch u i}
    (F : ∀ u, FormsTiedSym D u (Ch u) (chOf u)) (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ) (hi : i ≤ D.R.m) :
    (D.chTw u μ).Y i ≃ Fr D i hi :=
  (T.eY u μ i hi).symm.trans (eYS (F u) i hi)

theorem twYS_de (T : Formalism.L2.Herm.TwChTied D inQ) {Ch : D.what₂.Word → ℕ → Type} {chOf : ∀ u i, (D.mem u).C.cls i → Ch u i}
    (F : ∀ u, FormsTiedSym D u (Ch u) (chOf u)) (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ) (hi : i ≤ D.R.m) :
    ∃ C : GL (Fin (D.R.N i)) D.host.E,
      cT (sigD D : D.host.E →+* D.host.E) C.1 * C.1 = gramN D i hi ∧
      (∀ x : Fin (D.R.N i) → D.host.E, x ∈ selfDualLatticeCoords D i hi ↔ ∀ a, (C.1 *ᵥ x) a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) ∧
      ∀ τ z, (D.chTw u μ).de i z τ = embT D τ C.1.det * ((twYS T F u μ i hi z).1 τ).det := by
  obtain ⟨C, hC1, hC2, hC3⟩ := eYS_de (F u) i hi
  refine ⟨C, hC1, hC2, fun τ z => ?_⟩
  calc (D.chTw u μ).de i z τ
      = (D.chTw u μ).de i (T.eY u μ i hi ((T.eY u μ i hi).symm z)) τ := by
        rw [Equiv.apply_symm_apply]
    _ = (D.mem u).C.de i ((T.eY u μ i hi).symm z) τ := T.de_eq u μ i hi _ τ
    _ = embT D τ C.1.det * ((twYS T F u μ i hi z).1 τ).det := hC3 τ _

set_option maxHeartbeats 4000000 in

structure TwFormsTiedS (D : D7) (Tw : TwForms D) {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop}
    (T : Formalism.L2.Herm.TwChTied D inQ) {H : Formalism.L2.Herm.HermColsCh D} (J : Formalism.L2.Herm.TwChJointS T H)
    (F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u)) where

  atT : ∀ u μ, TwAtT Tw u μ

  ch : ∀ (u : D.what₂.Word) (μ : D.what₂.Tup), μ ≠ D.what₂.mu0 → ∀ (i : ℕ), 1 ≤ i → ∀ (hm : i ≤ D.R.m) (β : T.Ch u μ i),
    LevelChart D (D.mem u).A.T (badQ D (T.Q μ)) i hm
      (fun c : {c // T.chOf u μ i c = β} => (D.chTw u μ).stab i c.1) (fun c => latCrd D i hm (T.lat u μ i c.1))

  car : ∀ u μ (hμ : μ ≠ D.what₂.mu0) i (h1 : 1 ≤ i) (hm : i ≤ D.R.m) (β : T.Ch u μ i),
    SameCar (rankN D i hm) (T.lev u μ i h1 hm β).Lb (ch u μ hμ i h1 hm β).lev.Lb
      (T.lev u μ i h1 hm β).Uloc (ch u μ hμ i h1 hm β).lev.Uloc (T.lev u μ i h1 hm β).U (ch u μ hμ i h1 hm β).lev.U
      (fun c => ((T.cls u μ hμ i h1 hm β).y c).1) (fun c => ((ch u μ hμ i h1 hm β).y c).1)
      (fun c s => ((T.cls u μ hμ i h1 hm β).stabI c s).1) (fun c s => ((ch u μ hμ i h1 hm β).stabI c s).1)

  chi_fin : ∀ u μ hμ i h1 hm β, ∃ n : ℕ, 0 < n ∧ ∀ κ, (ch u μ hμ i h1 hm β).lev.chi κ ^ n = 1

  chi_offC : ∀ u μ hμ i h1 (h2 : i + 1 ≤ D.R.m) β (κ : (ch u μ hμ i h1 (le_of_succ_m h2) β).lev.U)
    (κ' : ((F u).ch i h1 h2 (J.gOf u μ i β)).lev.U), κ.1 = κ'.1 →
    (∀ v ∈ T.Q μ, bc (prV (E := D.host.E) v) κ.1 = 1) →
    (ch u μ hμ i h1 (le_of_succ_m h2) β).lev.chi κ = ((F u).ch i h1 h2 (J.gOf u μ i β)).lev.chi κ'

  chi_offM : ∀ u μ hμ (h1 : 1 ≤ D.R.m) β (κ : (ch u μ hμ D.R.m h1 le_rfl β).lev.U)
    (κ' : ((F u).cls D.R.m le_rfl (Or.inr rfl)).lev.U), κ.1 = κ'.1 →
    (∀ v ∈ T.Q μ, bc (prV (E := D.host.E) v) κ.1 = 1) →
    (ch u μ hμ D.R.m h1 le_rfl β).lev.chi κ = ((F u).cls D.R.m le_rfl (Or.inr rfl)).lev.chi κ'

  chiJ : ∀ u μ (h : 1 ≤ D.R.m - 1), (T.levJ u μ h).U →* ℂˣ
  chiJ_eq : ∀ u μ hμ (h : 1 ≤ D.R.m - 1) β (κ : (T.levJ u μ h).U)
    (κ' : (ch u μ hμ (D.R.m - 1) h (Nat.sub_le _ _) β).lev.U), κ'.1 = reGL (rankN D (D.R.m - 1) (Nat.sub_le _ _)) _ κ.1 →
    (ch u μ hμ (D.R.m - 1) h (Nat.sub_le _ _) β).lev.chi κ' = chiJ u μ h κ

  chiJ_off : ∀ u μ (h : 1 ≤ D.R.m - 1) (κ : (T.levJ u μ h).U) (κ' : (F u).levJ.U),
    κ'.1 = reGL (rankN D (D.R.m - 1) (Nat.sub_le _ _)) _ κ.1 →
    (∀ v ∈ T.Q μ, bc (prV (E := D.host.E) v) κ.1 = 1) → chiJ u μ h κ = (F u).levJ.chi κ'

  val : ∀ u μ hμ i h1 hm, ValuationCompatibleChart (Tw.fm u μ) (twYS T F u μ i hm) (okQ D (T.Q μ)) (T.chOf u μ i)
    (lat := fun c => latCrd D i hm (T.lat u μ i c)) (ch u μ hμ i h1 hm)

  dil : ∀ u μ hμ i h1 hm, DilationCompatibleChart (Tw.fm u μ) (twYS T F u μ i hm) ((atT u μ).eV (F u).atT) (T.chOf u μ i)
    (lat := fun c => latCrd D i hm (T.lat u μ i c)) (ch u μ hμ i h1 hm)

  ipV : ∀ u μ i hi, IpVTieG (Tw.fm u μ) (twYS T F u μ i hi)

  norm : ∀ u μ i hi, NormTieG (Tw.fm u μ) (twYS T F u μ i hi)

  twisted_e0_at_mu0_eq_eMu0 : ∀ u x, Tw.e0 u D.what₂.mu0 x = Tw.eMu0 u 0 (Nat.zero_le _) x

set_option maxHeartbeats 4000000 in

structure SymmetricTwistedLevelData {Tw : TwForms D} {T : Formalism.L2.Herm.TwChTied D inQ} {H : Formalism.L2.Herm.HermColsCh D} {J : Formalism.L2.Herm.TwChJointS T H}
    {F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u)} (W : TwFormsTiedS D Tw T J F) where
  lv : ∀ u μ, μ ≠ D.what₂.mu0 → ∀ i, 1 ≤ i → ∀ hm : i ≤ D.R.m,
    LevelCompatibleLattices (Tw.fm u μ) (D.mem u).A.T ((W.atT u μ).res (F u).atT) i hm (fun c => latCrd D i hm (T.lat u μ i c))
  fMe : ∀ u μ hμ i h1 hm β v, (W.ch u μ hμ i h1 hm β).lev.fM (((W.atT u μ).eV (F u).atT) v).1 (((W.atT u μ).eV (F u).atT) v).2 ≃+
    (Tw.A u μ).Fv v
  fv : ∀ u μ hμ i h1 hm, FvTieG (lv u μ hμ i h1 hm) ((W.atT u μ).eV (F u).atT) (W.ch u μ hμ i h1 hm) (fMe u μ hμ i h1 hm)
  upN : ∀ u μ hμ i h1 hm, UpNatTieG (lv u μ hμ i h1 hm) (twYS T F u μ i hm) ((W.atT u μ).eV (F u).atT) (W.ch u μ hμ i h1 hm)
  dnN : ∀ u μ hμ i h1 hm, DnNatTieG (lv u μ hμ i h1 hm) (twYS T F u μ i hm) ((W.atT u μ).eV (F u).atT) (W.ch u μ hμ i h1 hm)
  bw : ∀ u μ, μ ≠ D.what₂.mu0 → ∀ i, 1 ≤ i → ∀ hm : i ≤ D.R.m,
    BwTieG (Tw.fm u μ) (D.mem u).A.T ((W.atT u μ).res (F u).atT) (twYS T F u μ i hm) (fun c => latCrd D i hm (T.lat u μ i c))

structure TwLvSameS {Tw : TwForms D} {T : Formalism.L2.Herm.TwChTied D inQ} {H : Formalism.L2.Herm.HermColsCh D} {J : Formalism.L2.Herm.TwChJointS T H}
    {F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u)} (W : TwFormsTiedS D Tw T J F) where
  step0 : ∀ u μ, LvSame (W.atT u μ) 0 (T.eCls0 u μ) (T.eY u μ 0 (Nat.zero_le _)) (Tw.e0 u μ)
  mu0 : ∀ u i (hi : i ≤ D.R.m), LvSame (W.atT u D.what₂.mu0) i (Formalism.L2.Herm.clsCast D u i) (Formalism.L2.Herm.yCast D u i) (Tw.eMu0 u i hi)

theorem TwFormsTiedS.Fi_zero {Tw : TwForms D} {T : Formalism.L2.Herm.TwChTied D inQ} {H : Formalism.L2.Herm.HermColsCh D}
    {J : Formalism.L2.Herm.TwChJointS T H} {F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u)} (W : TwFormsTiedS D Tw T J F)
    (u : D.what₂.Word) (μ : D.what₂.Tup) :
    (Tw.fm u μ).Fi 0 = ((D.fm u).Fi 0).map (D.e0Tw u μ : _ →ₗ[ℂ] _) := by
  rw [(Tw.fm u μ).Fi_zero, (D.fm u).Fi_zero, (W.atT u μ).Mu0]

end Formalism.L2.Forms

end
