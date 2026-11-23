import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeSocleOverOfSimple
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieDerivativePolynomialFockArchimedeanUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommuteIsomSmul
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct

noncomputable section

open scoped Classical

namespace GlobalTheory.ThKLocSS

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def IsLineDer {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (om : Rep σ Y W) (γ : Multiplicative ℝ →* UA σ W.J)
    (Ψ Ψ₁ : Fn F n d) : Prop :=
  ∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Ψ x) (Ψ₁ x) 0

section Lin

variable {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (om : Rep σ Y W) (γ : Multiplicative ℝ →* UA σ W.J)

theorem isLineDer_unique {Ψ Ψ₁ Ψ₂ : Fn F n d} (h₁ : IsLineDer om γ Ψ Ψ₁) (h₂ : IsLineDer om γ Ψ Ψ₂) : Ψ₁ = Ψ₂ :=
  funext fun x => (h₁ x).unique (h₂ x)

theorem isLineDer_zero : IsLineDer om γ 0 0 := fun x => by
  simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)

theorem isLineDer_add {Ψ Ψ' Ψ₁ Ψ₁' : Fn F n d} (h : IsLineDer om γ Ψ Ψ₁) (h' : IsLineDer om γ Ψ' Ψ₁') :
    IsLineDer om γ (Ψ + Ψ') (Ψ₁ + Ψ₁') := fun x => by
  have e : (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) (Ψ + Ψ') x) =
      fun t => om (1, γ (Multiplicative.ofAdd t)) Ψ x + om (1, γ (Multiplicative.ofAdd t)) Ψ' x := by
    funext t; rw [map_add]; rfl
  rw [e]
  exact (h x).add (h' x)

theorem isLineDer_smul (c : ℂ) {Ψ Ψ₁ : Fn F n d} (h : IsLineDer om γ Ψ Ψ₁) : IsLineDer om γ (c • Ψ) (c • Ψ₁) :=
  fun x => by simpa only [map_smul, Pi.smul_apply, smul_eq_mul] using (h x).const_mul c

end Lin

theorem exists_lineDer_polData (hK : KP) {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E}
    {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (hT : IsTriple B G X om om') (v : Pl F)
    {γ : Multiplicative ℝ →* UA σ G.W.J} (hγ : γ ∈ Lines σ G.W) :
    ∀ Ψ ∈ PolData B G.M, ∃ Ψ₁ ∈ PolData B G.M, IsLineDer om γ Ψ Ψ₁ ∧
      ∀ h ∈ UAt σ G.W (evFin F v), IsLineDer om γ (om (1, h) Ψ) (om (1, h) Ψ₁) := by
  have hP := GlobalTheory.ThK.Inhab.pairV hT
  have hA := GlobalTheory.T.theta_action_exists hK.base
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hdetX : G.V.J.det ≠ 0 := by
    intro h0
    apply GlobalTheory.CartanLines.det_ne_zero_of_cartan (hP.herm.cartan w)
    rw [show G.V.J.map (B.emb w).1 = ((B.emb w).1).mapMatrix G.V.J from rfl, ← RingHom.map_det, h0, map_zero]
  have hdetW : G.W.J.det ≠ 0 := by
    intro h0
    apply GlobalTheory.CartanLines.det_ne_zero_of_cartan (hP.skew.cartan w)
    rw [Matrix.det_smul, show G.W.J.map (B.emb w).1 = ((B.emb w).1).mapMatrix G.W.J from rfl, ← RingHom.map_det, h0,
      map_zero, mul_zero]
  have hL := GlobalTheory.T.lieDerivative_polynomialFock_archimedeanUnitary F E σ hP.base.cm a (a + a') G.V G.W G.M B.ψ X.β (X.β / X.α) om hP.base.std hP.herm.herm hdetX
    hP.skew.skew hdetW hP.resX hP.resW hP.hX hP.hW hP.weil B.emb hP.herm.cartan hP.skew.cartan γ hγ
  have h1 : (1 : UA σ G.V.J) ∈ UAt σ G.V (evFin F v) := by
    intro u _
    show u • (mat (1 : UA σ G.V.J) - 1) = 0
    have : mat (1 : UA σ G.V.J) = 1 := rfl
    rw [this, sub_self, smul_zero]
  have hpd : ∀ f f₁ : SInf F (Fin a × Fin (a + a')),
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ →
      ∀ φ : ∀ w : Pl F, (Fin a × Fin (a + a') → Fv F w) → ℂ, (∀ w, φ w ∈ SB _) →
        (∀ᶠ w in Filter.cofinite, φ w = G.M.vac w) → IsLineDer om γ (pure f φ) (pure f₁ φ) := by
    intro f f₁ hf φ hSB hev x
    have hstd : ∀ᶠ w in Filter.cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 :=
      (hev.and hP.good.std).mono fun w hw => hw.1.trans hw.2
    exact hf _ (GlobalTheory.ThK.EvUniqInf.rest_pure f φ hSB hstd) x
  intro Ψ hΨ
  induction hΨ using Submodule.span_induction with
  | mem Ψ hΨ =>
    obtain ⟨f, hf, φ, hSB, hev, rfl⟩ := hΨ
    obtain ⟨f₁, hf₁⟩ := (hL f hf).1
    have hf₁P : f₁ ∈ G.M.Pol B.ψ B.emb := (hL f hf).2 f₁ hf₁
    refine ⟨pure f₁ φ, Submodule.subset_span ⟨f₁, hf₁P, φ, hSB, hev, rfl⟩, hpd f f₁ hf₁ φ hSB hev, fun h hh => ?_⟩
    have hstd : ∀ᶠ w in Filter.cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 :=
      (hev.and hP.good.std).mono fun w hw => hw.1.trans hw.2
    obtain ⟨φ₁, ⟨hφ₁, hact⟩, -⟩ := (hA F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hP v).1 1 h1 h hh (φ v) (hSB v)
    have hmap : ∀ g : SInf F (Fin a × Fin (a + a')), om (1, h) (pure g φ) = pure g (Function.update φ v φ₁) := by
      intro g
      obtain ⟨ρ, hρ, hρt⟩ := GlobalTheory.PureFactor.exists_rest_factor v g φ hstd
      have hpure : tens (evFin F v) (φ v) ρ = pure g φ := by rw [hρt, Function.update_eq_self]
      have hRest : Rest (evFin F v) (φ v) ρ := ⟨hρ, by rw [hpure]; exact GlobalTheory.TensUniq.pure_mem_schA g φ hSB hstd⟩
      rw [← hpure, hact ρ hRest, hρt]
    have hSB' : ∀ w, Function.update φ v φ₁ w ∈ SB _ := by
      intro w
      by_cases hw : w = v
      · subst hw; rw [Function.update_self]; exact hφ₁
      · rw [Function.update_of_ne hw]; exact hSB w
    have hev' : ∀ᶠ w in Filter.cofinite, Function.update φ v φ₁ w = G.M.vac w := by
      filter_upwards [hev, Filter.eventually_cofinite_ne v] with w hw hne
      rw [Function.update_of_ne hne]; exact hw
    rw [hmap f, hmap f₁]
    exact hpd f f₁ hf₁ _ hSB' hev'
  | zero =>
    refine ⟨0, zero_mem _, isLineDer_zero om γ, fun h _ => ?_⟩
    rw [map_zero]; exact isLineDer_zero om γ
  | add x y _ _ hx hy =>
    obtain ⟨x₁, hx₁, hdx, hhx⟩ := hx
    obtain ⟨y₁, hy₁, hdy, hhy⟩ := hy
    refine ⟨x₁ + y₁, add_mem hx₁ hy₁, isLineDer_add om γ hdx hdy, fun h hh => ?_⟩
    rw [map_add, map_add]; exact isLineDer_add om γ (hhx h hh) (hhy h hh)
  | smul c x _ hx =>
    obtain ⟨x₁, hx₁, hdx, hhx⟩ := hx
    refine ⟨c • x₁, Submodule.smul_mem _ c hx₁, isLineDer_smul om γ c hdx, fun h hh => ?_⟩
    rw [map_smul, map_smul]; exact isLineDer_smul om γ c (hhx h hh)

end GlobalTheory.ThKLocSS

namespace GlobalTheory.ThKLocSS

open GlobalTheory.ThetaFac

theorem socleOver_lineDer : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ N, GlobalTheory.ThetaFac.IsMaxTh B om (GlobalTheory.ThK.PolData B G.M) N → (∀ Ψ ∈ GlobalTheory.ThK.PolData B G.M, G.M.I om Ψ = 0 → Ψ ∈ N) → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.W, ∀ Φ ∈ GlobalTheory.ThKLocSS.socleOver (GlobalTheory.ThKLocSS.opsAt om v) N (GlobalTheory.ThK.PolData B G.M), ∀ Φ₁ ∈ GlobalTheory.ThK.PolData B G.M, (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) → Φ₁ ∈ GlobalTheory.ThKLocSS.socleOver (GlobalTheory.ThKLocSS.opsAt om v) N (GlobalTheory.ThK.PolData B G.M) := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' hT N hN _ v γ hγ Φ hΦ Φ₁ _ hder
  have key := exists_lineDer_polData hK hT v hγ
  have hNder : ∀ Ψ ∈ N, ∀ y, IsLineDer om γ Ψ y → y ∈ N := by
    intro Ψ hΨ y hy
    obtain ⟨y', hy'D, hy', -⟩ := key Ψ (hN.le hΨ)
    rw [isLineDer_unique om γ hy hy']
    exact hN.stab.lie γ hγ Ψ hΨ y' hy'D hy'
  have hDer : ∀ Ψ ∈ PolData B G.M, ∀ y, IsLineDer om γ Ψ y →
      y ∈ PolData B G.M ∧ ∀ h ∈ UAt σ G.W (evFin F v), IsLineDer om γ (om (1, h) Ψ) (om (1, h) y) := by
    intro Ψ hΨ y hy
    obtain ⟨y', hy'D, hy', hh⟩ := key Ψ hΨ
    rw [isLineDer_unique om γ hy hy']
    exact ⟨hy'D, hh⟩
  have hsimple : ∀ S, S ≤ PolData B G.M → IsSimpleOver (opsAt om v) N S → ∀ Ψ ∈ S, ∀ y, IsLineDer om γ Ψ y →
      y ∈ socleOver (opsAt om v) N (PolData B G.M) := by
    intro S hSD hS Ψ hΨ y hy
    have hSst := (opStable_opsAt_iff om v S).1 hS.2.1
    let Img : Submodule ℂ (Fn F a (a + a')) :=
      { carrier := {z | ∃ Ψ ∈ S, IsLineDer om γ Ψ z}
        add_mem' := by
          rintro z z' ⟨Ψ, hΨ, hz⟩ ⟨Ψ', hΨ', hz'⟩
          exact ⟨Ψ + Ψ', S.add_mem hΨ hΨ', isLineDer_add om γ hz hz'⟩
        zero_mem' := ⟨0, S.zero_mem, isLineDer_zero om γ⟩
        smul_mem' := by
          rintro c z ⟨Ψ, hΨ, hz⟩
          exact ⟨c • Ψ, S.smul_mem c hΨ, isLineDer_smul om γ c hz⟩ }
    have hyS' : y ∈ N ⊔ Img := Submodule.mem_sup_right ⟨Ψ, hΨ, hy⟩
    have hNS : N ≤ S := hS.1.le
    have hS'D : N ⊔ Img ≤ PolData B G.M := sup_le hN.le (fun z ⟨Ψ, hΨ, hz⟩ => (hDer Ψ (hSD hΨ) z hz).1)
    have hImgst : ∀ h ∈ UAt σ G.W (evFin F v), ∀ z ∈ Img, om (1, h) z ∈ Img := by
      rintro h hh z ⟨Ψ, hΨ, hz⟩
      exact ⟨om (1, h) Ψ, hSst h hh Ψ hΨ, (hDer Ψ (hSD hΨ) z hz).2 h hh⟩
    have hS'st : ∀ h ∈ UAt σ G.W (evFin F v), ∀ z ∈ N ⊔ Img, om (1, h) z ∈ N ⊔ Img := by
      intro h hh z hz
      obtain ⟨n₀, hn₀, z₀, hz₀, rfl⟩ := Submodule.mem_sup.1 hz
      rw [map_add]
      exact add_mem (Submodule.mem_sup_left (hN.stab.fin v h hh n₀ hn₀)) (Submodule.mem_sup_right (hImgst h hh z₀ hz₀))
    by_cases hEq : N ⊔ Img = N
    · exact le_socleOver _ _ _ (hEq ▸ hyS')
    · refine le_socleOver_of_simple _ hS'D ⟨lt_of_le_of_ne le_sup_left (Ne.symm hEq),
        (opStable_opsAt_iff om v _).2 hS'st, ?_⟩ hyS'
      intro S'' hNS'' hS''S' hS''st
      have hS''st' := (opStable_opsAt_iff om v S'').1 hS''st
      let Pre : Submodule ℂ (Fn F a (a + a')) :=
        { carrier := {Ψ | Ψ ∈ S ∧ ∃ z ∈ S'', IsLineDer om γ Ψ z}
          add_mem' := by
            rintro Ψ Ψ' ⟨hΨ, z, hz, hd⟩ ⟨hΨ', z', hz', hd'⟩
            exact ⟨S.add_mem hΨ hΨ', z + z', S''.add_mem hz hz', isLineDer_add om γ hd hd'⟩
          zero_mem' := ⟨S.zero_mem, 0, S''.zero_mem, isLineDer_zero om γ⟩
          smul_mem' := by
            rintro c Ψ ⟨hΨ, z, hz, hd⟩
            exact ⟨S.smul_mem c hΨ, c • z, S''.smul_mem c hz, isLineDer_smul om γ c hd⟩ }
      have hNPre : N ≤ Pre := by
        intro Ψ hΨ
        obtain ⟨z, -, hz, -⟩ := key Ψ (hN.le hΨ)
        exact ⟨hNS hΨ, z, hNS'' (hNder Ψ hΨ z hz), hz⟩
      have hPreS : Pre ≤ S := fun Ψ h => h.1
      have hPrest : OpStable (opsAt om v) Pre := by
        rw [opStable_opsAt_iff]
        rintro h hh Ψ ⟨hΨ, z, hz, hd⟩
        exact ⟨hSst h hh Ψ hΨ, om (1, h) z, hS''st' h hh z hz, (hDer Ψ (hSD hΨ) z hd).2 h hh⟩
      rcases hS.2.2 Pre hNPre hPreS hPrest with hPN | hPS
      · left
        refine le_antisymm ?_ hNS''
        intro y' hy'
        obtain ⟨n₀, hn₀, z₀, ⟨Ψ₀, hΨ₀, hz₀⟩, rfl⟩ := Submodule.mem_sup.1 (hS''S' hy')
        have hz₀S'' : z₀ ∈ S'' := by
          have := S''.sub_mem hy' (hNS'' hn₀)
          simpa using this
        have hΨ₀P : Ψ₀ ∈ Pre := ⟨hΨ₀, z₀, hz₀S'', hz₀⟩
        rw [hPN] at hΨ₀P
        exact N.add_mem hn₀ (hNder Ψ₀ hΨ₀P z₀ hz₀)
      · right
        refine le_antisymm hS''S' (sup_le hNS'' ?_)
        rintro z ⟨Ψ₀, hΨ₀, hz⟩
        have hΨ₀P : Ψ₀ ∈ Pre := by rw [hPS]; exact hΨ₀
        obtain ⟨-, z', hz', hd'⟩ := hΨ₀P
        rw [isLineDer_unique om γ hz hd']
        exact hz'
  let Q : Submodule ℂ (Fn F a (a + a')) :=
    { carrier := {Ψ | Ψ ∈ PolData B G.M ∧ ∀ y, IsLineDer om γ Ψ y → y ∈ socleOver (opsAt om v) N (PolData B G.M)}
      zero_mem' := ⟨zero_mem _, fun y hy => by rw [isLineDer_unique om γ hy (isLineDer_zero om γ)]; exact zero_mem _⟩
      add_mem' := by
        rintro Ψ Ψ' ⟨hΨ, h1⟩ ⟨hΨ', h2⟩
        refine ⟨add_mem hΨ hΨ', fun y hy => ?_⟩
        obtain ⟨z, -, hz, -⟩ := key Ψ hΨ
        obtain ⟨z', -, hz', -⟩ := key Ψ' hΨ'
        rw [isLineDer_unique om γ hy (isLineDer_add om γ hz hz')]
        exact add_mem (h1 z hz) (h2 z' hz')
      smul_mem' := by
        rintro c Ψ ⟨hΨ, h1⟩
        refine ⟨Submodule.smul_mem _ c hΨ, fun y hy => ?_⟩
        obtain ⟨z, -, hz, -⟩ := key Ψ hΨ
        rw [isLineDer_unique om γ hy (isLineDer_smul om γ c hz)]
        exact Submodule.smul_mem _ c (h1 z hz) }
  have hle : socleOver (opsAt om v) N (PolData B G.M) ≤ Q := by
    refine sup_le (fun Ψ hΨ => ⟨hN.le hΨ, fun y hy => le_socleOver _ _ _ (hNder Ψ hΨ y hy)⟩) (sSup_le ?_)
    rintro S ⟨hSD, hS⟩ Ψ hΨ
    exact ⟨hSD hΨ, fun y hy => hsimple S hSD hS Ψ hΨ y hy⟩
  exact (hle hΦ).2 Φ₁ hder

end GlobalTheory.ThKLocSS

end
