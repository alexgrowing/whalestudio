import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpanSchwartzBruhatProductEqTop
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocMod.BoxModel

open GlobalTheory.LocFlat.CFac

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def prH (p : Place D k) : D.host.E →+* k := p.π.comp (incA D)

theorem map_pr_mul (p : Place D k) {l m m' : Type} [Fintype m] (M : Matrix l m D.host.E) (N : Matrix m m' D.host.E) :
    (M * N).map p.pr = M.map p.pr * N.map p.pr := Matrix.map_mul (f := prH p)

theorem incA_mul_ι (p : Place D k) (a : D.host.E) (x : k) : (incA D a : AE D) * p.ι x = p.ι (p.pr a * x) := by
  have h : p.pr a * x = p.π ((incA D a : AE D) * p.ι x) := by rw [map_mul, p.π_ι]; rfl
  rw [h, p.ι_π, mul_left_comm, ← p.ι_π, p.π_ι]

theorem rat_mul_ι (p : Place D k) {l m : ℕ} {Y : Type} [Fintype Y] (M : Matrix (Fin l) (Fin m) D.host.E)
    (N : Matrix (Fin m) Y k) : (rat M : Matrix (Fin l) (Fin m) (AE D)) * (N.map p.ι) = (M.map p.pr * N).map p.ι := by
  ext i j
  simp only [rat, Matrix.mul_apply, Matrix.map_apply, map_sum, incA_mul_ι]

variable {Z n : Type} [Fintype Z] [DecidableEq Z] [Fintype n] [DecidableEq n]

theorem resT_up (p : Place D k) {S X T L : HSp D} (o : OrthDec X T L) (FS : Frame k S.rank n) (FT : Frame k T.rank Z)
    (FL : Frame k L.rank Unit) (FX : Frame k X.rank (Z ⊕ Unit))
    (hβ : FX.β = fromCols (o.iA.map p.pr * FT.β) (o.iB.map p.pr * FL.β)) (x : Matrix (Z ⊕ Unit) n k) :
    o.resT S (p.up FS FX x) = (p.up FS FT x.toRows₁, p.up FS FL x.toRows₂) := by
  have h1 : ((1 : Matrix (Fin T.rank) (Fin T.rank) D.host.E)).map p.pr = 1 :=
    Matrix.map_one _ (map_zero (prH p)) (map_one (prH p))
  have h1' : ((1 : Matrix (Fin L.rank) (Fin L.rank) D.host.E)).map p.pr = 1 :=
    Matrix.map_one _ (map_zero (prH p)) (map_one (prH p))
  have h0 : ((0 : Matrix (Fin T.rank) (Fin L.rank) D.host.E)).map p.pr = 0 := Matrix.map_zero _ (map_zero (prH p))
  have h0' : ((0 : Matrix (Fin L.rank) (Fin T.rank) D.host.E)).map p.pr = 0 := Matrix.map_zero _ (map_zero (prH p))
  have hA : o.qA.map p.pr * FX.β = fromCols FT.β 0 := by
    rw [hβ, Matrix.mul_fromCols, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← map_pr_mul, ← map_pr_mul, o.qA_iA, o.qA_iB,
      h1, h0, Matrix.one_mul, Matrix.zero_mul]
  have hB : o.qB.map p.pr * FX.β = fromCols 0 FL.β := by
    rw [hβ, Matrix.mul_fromCols, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← map_pr_mul, ← map_pr_mul, o.qB_iA, o.qB_iB,
      h1', h0', Matrix.one_mul, Matrix.zero_mul]
  rw [OrthDec.resT_apply]
  refine Prod.ext ?_ ?_
  · change (rat o.qA : Matrix _ _ (AE D)) * (FX.β * x * FS.γ).map p.ι = (FT.β * x.toRows₁ * FS.γ).map p.ι
    rw [rat_mul_ι, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hA]
    congr 2
    conv_lhs => rw [← Matrix.fromRows_toRows x]
    rw [Matrix.fromCols_mul_fromRows, Matrix.zero_mul, add_zero]
  · change (rat o.qB : Matrix _ _ (AE D)) * (FX.β * x * FS.γ).map p.ι = (FL.β * x.toRows₂ * FS.γ).map p.ι
    rw [rat_mul_ι, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hB]
    congr 2
    conv_lhs => rw [← Matrix.fromRows_toRows x]
    rw [Matrix.fromCols_mul_fromRows, Matrix.zero_mul, zero_add]

end GlobalTheory.LocMod.BoxModel

namespace GlobalTheory.LocMod.BoxModel

open GlobalTheory.LocFlat.CFac

section SlopeTestRemainingChoices
variable {D : D7}

theorem hO_add_left' (S T : HSp D) (x x' y : WO S T) : hO S T (x + x') y = hO S T x y + hO S T x' y := by
  unfold hO
  simp only [Matrix.add_apply, mul_add, ← Finset.sum_add_distrib]

theorem symplO_add_left' (S T : HSp D) (x x' y : WO S T) :
    symplO S T (x + x') y = symplO S T x y + symplO S T x' y := by
  unfold symplO; rw [hO_add_left', mul_add, map_add]

theorem symplO_zero_left' (S T : HSp D) (y : WO S T) : symplO S T 0 y = 0 := by
  have h := symplO_add_left' S T 0 0 y
  simp only [add_zero] at h
  exact left_eq_add.mp h

theorem isThetaFunO_zero' (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : IsThetaFunO ψ S T 0 where
  quasi γ w := by simp
  level := ⟨⊤, isOpen_univ, fun u _ _ => by funext w; simp [heisO]⟩
  cont := continuous_const
  smooth _ _ _ _ _ := contDiff_const

theorem isThetaFunO_add' {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (hg : IsThetaFunO ψ S T g) : IsThetaFunO ψ S T (f + g) where
  quasi γ w := by simp only [Pi.add_apply]; rw [hf.quasi, hg.quasi]; ring
  level := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    obtain ⟨U', hUo', hU'⟩ := hg.level
    refine ⟨U ⊓ U', hUo.inter hUo', fun u hu hi => ?_⟩
    have e : heisO ψ S T u (f + g) = heisO ψ S T u f + heisO ψ S T u g := by
      funext w; simp only [heisO, Pi.add_apply]; ring
    rw [e, hU u hu.1 hi, hU' u hu.2 hi]
  cont := hf.cont.add hg.cont
  smooth k L hL hfin w := (hf.smooth k L hL hfin w).add (hg.smooth k L hL hfin w)

theorem isThetaFunO_smul' {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (c : ℂ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (c • f) where
  quasi γ w := by simp only [Pi.smul_apply, smul_eq_mul]; rw [hf.quasi]; ring
  level := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    refine ⟨U, hUo, fun u hu hi => ?_⟩
    have e : heisO ψ S T u (c • f) = c • heisO ψ S T u f := by
      funext w; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring
    rw [e, hU u hu hi]
  cont := continuous_const.mul hf.cont
  smooth k L hL hfin w := (contDiff_const.mul (hf.smooth k L hL hfin w))

def heisL (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun := heisO ψ S T u
  map_add' f g := by funext w; simp only [heisO, Pi.add_apply]; ring
  map_smul' c f := by funext w; simp only [heisO, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem isLocallyConstant_of_near {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (χ : G → ℂ) (hχ : ∀ a b, χ (a + b) = χ a * χ b) (t₀ : G) (h0 : χ t₀ ≠ 0) (U : Set G) (hU : U ∈ nhds t₀)
    (hc : ∀ t ∈ U, χ t = χ t₀) : IsLocallyConstant χ := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hcont : Continuous fun y : G => y - x + t₀ := (continuous_id.sub continuous_const).add continuous_const
  have hx : (fun y : G => y - x + t₀) x = t₀ := by simp
  have hU' : (fun y : G => y - x + t₀) ⁻¹' U ∈ nhds x := hcont.continuousAt.preimage_mem_nhds (by simp only [sub_self, zero_add]; exact hU)
  filter_upwards [hU'] with y hy
  have e1 : χ (y + t₀) = χ (x + (y - x + t₀)) := by rw [show x + (y - x + t₀) = y + t₀ by abel]
  rw [hχ, hχ, hc _ hy] at e1
  exact mul_right_cancel₀ h0 e1

end SlopeTestRemainingChoices

end GlobalTheory.LocMod.BoxModel

namespace GlobalTheory.LocMod.BoxModel

open GlobalTheory.LocFlat.CFac

theorem isModel_boxT : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (S X T L'' : HSp D) (o'' : OrthDec X T L'') (n Z : Type) [Fintype n] [DecidableEq n] [Fintype Z] [DecidableEq Z] (FS : Frame k S.rank n) (FT : Frame k T.rank Z) (FL : Frame k L''.rank Unit) (FX : Frame k X.rank (Z ⊕ Unit)), FX.β = fromCols (o''.iA.map p.pr * FT.β) (o''.iB.map p.pr * FL.β) → ∀ T₂ TL, p.IsModel ψ FS FT T₂ → p.IsModel ψ FS FL TL → ∀ TX : SB (Matrix (Z ⊕ Unit) n k) →ₗ[ℂ] (WO S X → ℂ), (∀ (a : SB (Matrix Z n k)) (b : SB (Matrix Unit n k)) (Φ : SB (Matrix (Z ⊕ Unit) n k)), (∀ x, Φ.1 x = a.1 x.toRows₁ * b.1 x.toRows₂) → TX Φ = o''.boxT S (T₂ a) (TL b)) → p.IsModel ψ FS FX TX := by
  intro D k _ _ _ _ p ψ S X T L'' o'' n Z _ _ _ _ FS FT FL FX hβ T₂ TL h₂ hL TX hTX
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  haveI : NonarchimedeanAddGroup k := ⟨fun V hV => by
    obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset hV
    exact ⟨⟨⟨⟨⟨GlobalTheory.SplitWeil.cball s, GlobalTheory.SplitWeil.add_mem_cball⟩, by simp [GlobalTheory.SplitWeil.cball]⟩,
      GlobalTheory.SplitWeil.neg_mem_cball⟩, GlobalTheory.SplitWeil.isOpen_cball s⟩, hs⟩⟩
  haveI : TotallyDisconnectedSpace k := inferInstance
  haveI hTD : ∀ (a b : Type) [Fintype a] [Fintype b], TotallyDisconnectedSpace (Matrix a b k) :=
    fun a b _ _ => inferInstanceAs (TotallyDisconnectedSpace (a → b → k))
  haveI hLC : ∀ (a b : Type) [Fintype a] [Fintype b], LocallyCompactSpace (Matrix a b k) :=
    fun a b _ _ => inferInstanceAs (LocallyCompactSpace (a → b → k))
  haveI hT2 : ∀ (a b : Type), T2Space (Matrix a b k) := fun a b => inferInstanceAs (T2Space (a → b → k))
  let e : Matrix (Z ⊕ Unit) n k ≃ₜ Matrix Z n k × Matrix Unit n k := Homeomorph.sumArrowHomeomorphProdArrow
  let P : SB (Matrix Z n k) → SB (Matrix Unit n k) → SB (Matrix (Z ⊕ Unit) n k) := fun a b => comapH e (prodSB a b)
  have hP : ∀ a b x, (P a b).1 x = a.1 x.toRows₁ * b.1 x.toRows₂ := fun _ _ _ => rfl
  have hTP : ∀ a b, TX (P a b) = o''.boxT S (T₂ a) (TL b) := fun a b => hTX a b _ (hP a b)
  have hspan : Submodule.span ℂ (Set.range fun q : SB (Matrix Z n k) × SB (Matrix Unit n k) => P q.1 q.2) = ⊤ := by
    have hsurj : Function.Surjective (comapH e) := fun F => ⟨comapH e.symm F, by
      ext x; simp only [comapH_apply, Homeomorph.symm_apply_apply]⟩
    rw [Set.range_comp' (comapH e) (fun q : SB (Matrix Z n k) × SB (Matrix Unit n k) => prodSB q.1 q.2),
      Submodule.span_image, GlobalTheory.LocFlat.CFac.Span.span_prodSB_eq_top, Submodule.map_top, LinearMap.range_eq_top.mpr hsurj]
  have hres := resT_up p o'' FS FT FL FX hβ
  refine ⟨fun Φ => ?_, fun x Φ Φ' h => ?_, fun y hy Φ Φ' h => ?_⟩
  · have hmem : Φ ∈ Submodule.span ℂ (Set.range fun q : SB (Matrix Z n k) × SB (Matrix Unit n k) => P q.1 q.2) := by
      rw [hspan]; trivial
    induction hmem using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨a, b⟩, rfl⟩ := hx
      rw [hTP]
      exact o''.isThetaFunO_boxT (h₂.theta a) (hL.theta b)
    | zero => rw [map_zero]; exact isThetaFunO_zero' ψ S X
    | add x y _ _ hx hy => rw [map_add]; exact isThetaFunO_add' hx hy
    | smul c x _ hx => rw [map_smul]; exact isThetaFunO_smul' c hx
  · have hΦ' : Φ' = comapH (Homeomorph.addRight x) Φ := Subtype.ext (funext h)
    subst hΦ'
    have key : TX ∘ₗ comapH (Homeomorph.addRight x) = heisL ψ S X (p.up FS FX x) ∘ₗ TX := by
      refine LinearMap.ext_on hspan ?_
      rintro _ ⟨⟨a, b⟩, rfl⟩
      have e1 : comapH (Homeomorph.addRight x) (P a b) =
          P (comapH (Homeomorph.addRight x.toRows₁) a) (comapH (Homeomorph.addRight x.toRows₂) b) := by
        ext t
        rfl
      simp only [LinearMap.comp_apply, e1, hTP]
      rw [h₂.trans x.toRows₁ a _ (fun _ => rfl), hL.trans x.toRows₂ b _ (fun _ => rfl)]
      change _ = heisO ψ S X (p.up FS FX x) (o''.boxT S (T₂ a) (TL b))
      rw [o''.heisO_boxT, hres]
    exact LinearMap.congr_fun key Φ
  · let χ : Matrix (Z ⊕ Unit) n k → ℂ := fun t => ψ (symplO S X (p.up FS FX t) y)
    have hne : ∀ a, ψ a ≠ 0 := fun a h0 => by
      have := AddChar.map_add_eq_mul ψ a (-a)
      rw [add_neg_cancel, AddChar.map_zero_eq_one, h0, zero_mul] at this
      exact one_ne_zero this
    have hχadd : ∀ a b, χ (a + b) = χ a * χ b := fun a b => by
      simp only [χ]
      rw [Witness.up_add p FS FX a b, symplO_add_left', AddChar.map_add_eq_mul]
    by_cases hΦ : Φ = 0
    · have hΦ' : Φ' = 0 := Subtype.ext (funext fun t => by
        rw [h t, hΦ]
        simp)
      rw [hΦ, hΦ', map_zero]
      funext w
      simp [heisO]
    have ht₀ : ∃ t₀, Φ.1 t₀ ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hΦ (Subtype.ext (funext hc))
    obtain ⟨t₀, ht₀⟩ := ht₀
    have hU : {t | Φ.1 t = Φ.1 t₀} ∩ {t | Φ'.1 t = Φ'.1 t₀} ∈ nhds t₀ :=
      ((Φ.2.1.isOpen_fiber _).inter (Φ'.2.1.isOpen_fiber _)).mem_nhds ⟨rfl, rfl⟩
    have hχlc : IsLocallyConstant χ := isLocallyConstant_of_near χ hχadd t₀ (hne _) _ hU fun t ht => by
      have e1 := h t
      rw [ht.1, ht.2, h t₀] at e1
      exact (mul_right_cancel₀ ht₀ e1).symm
    have hΦ' : Φ' = mulLC χ hχlc Φ := Subtype.ext (funext h)
    subst hΦ'
    set y₁ := (o''.resT S y).1 with hy₁d
    set y₂ := (o''.resT S y).2 with hy₂d
    let χ₁ : Matrix Z n k → ℂ := fun t => ψ (symplO S T (p.up FS FT t) y₁)
    let χ₂ : Matrix Unit n k → ℂ := fun t => ψ (symplO S L'' (p.up FS FL t) y₂)
    have hsplit : ∀ t, χ t = χ₁ t.toRows₁ * χ₂ t.toRows₂ := fun t => by
      simp only [χ, χ₁, χ₂]
      rw [o''.symplO_resT, hres, AddChar.map_add_eq_mul]
    have hup0 : ∀ {Y : Type} [Fintype Y] [DecidableEq Y] {V : HSp D} (F : Frame k V.rank Y),
        p.up FS F (0 : Matrix Y n k) = 0 := fun F => by
      have := Witness.up_add p FS F 0 0
      rw [add_zero] at this
      exact left_eq_add.mp this
    have hχ₁ : IsLocallyConstant χ₁ := by
      have e1 : χ₁ = fun t₁ => χ (e.symm (t₁, 0)) := funext fun t₁ => by
        rw [hsplit]
        change χ₁ t₁ = χ₁ t₁ * ψ (symplO S L'' (p.up FS FL 0) y₂)
        rw [hup0, symplO_zero_left', AddChar.map_zero_eq_one, mul_one]
      rw [e1]
      exact hχlc.comp_continuous (e.symm.continuous.comp (continuous_id.prodMk continuous_const))
    have hχ₂ : IsLocallyConstant χ₂ := by
      have e1 : χ₂ = fun t₂ => χ (e.symm (0, t₂)) := funext fun t₂ => by
        rw [hsplit]
        change χ₂ t₂ = ψ (symplO S T (p.up FS FT 0) y₁) * χ₂ t₂
        rw [hup0, symplO_zero_left', AddChar.map_zero_eq_one, one_mul]
      rw [e1]
      exact hχlc.comp_continuous (e.symm.continuous.comp (continuous_const.prodMk continuous_id))
    have hh₁ : IsHalf (cA D p.e) y₁ := fun i j => by
      change cA D p.e * (o''.pA * y) i j = (o''.pA * y) i j
      rw [Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [mul_left_comm, hy l j]
    have hh₂ : IsHalf (cA D p.e) y₂ := fun i j => by
      change cA D p.e * (o''.pB * y) i j = (o''.pB * y) i j
      rw [Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [mul_left_comm, hy l j]
    have key : TX ∘ₗ mulLC χ hχlc = heisL ψ S X y ∘ₗ TX := by
      refine LinearMap.ext_on hspan ?_
      rintro _ ⟨⟨a, b⟩, rfl⟩
      have e1 : mulLC χ hχlc (P a b) = P (mulLC χ₁ hχ₁ a) (mulLC χ₂ hχ₂ b) := by
        ext t
        simp only [mulLC_apply, hP]
        rw [hsplit]
        ring
      simp only [LinearMap.comp_apply, e1, hTP]
      rw [h₂.modul y₁ hh₁ a _ (fun _ => rfl), hL.modul y₂ hh₂ b _ (fun _ => rfl)]
      change _ = heisO ψ S X y (o''.boxT S (T₂ a) (TL b))
      rw [o''.heisO_boxT]
    exact LinearMap.congr_fun key Φ

end GlobalTheory.LocMod.BoxModel
