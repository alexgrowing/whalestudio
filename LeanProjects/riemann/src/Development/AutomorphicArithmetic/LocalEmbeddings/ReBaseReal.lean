import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealMapsRelevantSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationUnitaryEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationUnitaryUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationUnitaryCompat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilModelLineActionExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineGoodModelAction

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ReBase

section First

open scoped Matrix Classical
open Formalism.BasicNotions.TH
open GlobalTheory.RealLift GlobalTheory.RealLift.LieFirstPf GlobalTheory.RealLift.FirstLine

theorem sd_exists : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → M.IsWeil B.ψ χX χW om →
    ∀ γ ∈ Lines σ X, ∀ f ∈ M.Pol B.ψ B.emb, ∃ f₁ : SInf F (Fin n × Fin d),
      GlobalTheory.RealLift.SD (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hB hX hW hM hWeil γ hγ f hf
  choose A hA hAθ using fun w => frameEx_holds _ _ _ _ _ (hX.sig w) (hX.cartan w)
  choose C hC hCθ using fun w => frameEx_holds _ _ _ _ _ (hW.sig w) (hW.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [incM_map_piInf', one_smul]; exact hA w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [incM_map_piInf']; exact hC w
  have fr : Framed B.emb (incM F X.J) (incM F W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  have fr' : Framed B.emb (incM F W.J) (incM F X.J) Complex.I 1 C A := ⟨mul_one _, hC1, hA1⟩
  have hvl := GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives GlobalTheory.T.archHeisenbergDerivatives_exist
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives GlobalTheory.T.archHeisenbergDerivatives_exist F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C hB.cm hB.std fr
  have hr := GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws actsLaws GlobalTheory.T.archHeisenbergDerivatives_exist hvl F E σ _ _ _ _ _ _ X W M B.ψ B.emb A C Φ hB.cm hB.std fr hAθ hCθ hΦ
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (incM F W.J) M.co χX χW om := hWeil
  obtain ⟨d', hdd, hB1'⟩ := hwp.2.1
  have hΦ' := fockMap_swap hΦ hdd
  obtain ⟨c, hact⟩ := GlobalTheory.T.lieScalar_of_prints_derEx_vacLine hKP GlobalTheory.T.archHeisenbergDerivatives_exist hvl F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ d' Complex.I 1 C A _
    (om.comp (MonoidHom.inl _ _)) hB.cm hB.std fr' hΦ' hB1'.1
  obtain ⟨Y, -, hY⟩ := GlobalTheory.T.oneParamSubgroup_generators_exist F E σ (Fin n) r s B.emb (incM F X.J) 1 A hB.cm hA1 γ hγ
  rw [← hr] at hf
  obtain ⟨T, rfl⟩ := hf
  have hT : Φ T = (Φ ∘ₗ (swapT (InfinitePlace F) r s r' s').toLinearMap) ((swapT (InfinitePlace F) r s r' s').symm T) := by
    simp
  have key := hact γ hγ Y hY ((swapT (InfinitePlace F) r s r' s').symm T)
  rw [← hT] at key
  exact ⟨_, key⟩

end First

theorem deriv_conj_line : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → M.IsWeil B.ψ χX χW om →
    ∀ g ∈ UAt σ X (evI F), ∀ h ∈ UAt σ W (evI F), ∀ T : SInf F (Fin n × Fin d) ≃ₗ[ℂ] SInf F (Fin n × Fin d),
    (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g, h)) f (T f)) → (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g⁻¹, h⁻¹)) f (T.symm f)) →
    ∀ γ ∈ Lines σ X, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ →
      ActsD (evI F) (fun t => om (g * γ (Multiplicative.ofAdd t) * g⁻¹, 1)) (T f) (T f₁) := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hB hX hW hM hWeil g hg h hh T hT hTi γ hγ f hf f₁ hf₁
  obtain ⟨f₂, hsd⟩ := sd_exists hKP F E σ B n d X W M χX χW om r s r' s' hB hX hW hM hWeil γ hγ f hf
  have e := (GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) f f₂ f₁).2.2.1 _
    ((GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) f f₂ f₁).1 _ (fun t => map_zero _) hsd) hf₁
  subst e
  have hS := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hWeil
  refine (GlobalTheory.RealLift.actsLaws F _ (T f) (T f₂) (T f₂)).1 _ (fun t => map_zero _) ?_
  intro g' hg' l hl
  have key : ∀ φ : SInf F (Fin n × Fin d), Acts (evI F) (om (g, h)) φ (T φ) →
      om (g, h) (GlobalTheory.WeilM.pureA F φ g') = GlobalTheory.WeilM.pureA F (T φ) g' := by
    intro φ hφ
    have hr : ∀ x z, At (evI F) z → (fun x : Fin n × Fin d → AF F => g' (fun i => (x i).2)) (x + z) =
        (fun x : Fin n × Fin d → AF F => g' (fun i => (x i).2)) x := by
      intro x z hz
      change g' (fun i => (x i + z i).2) = g' (fun i => (x i).2)
      congr 1
      funext i
      change (x i).2 + (z i).2 = (x i).2
      rw [GlobalTheory.RealLift.fin_eq_zero_of_at hz, add_zero]
    exact hφ _ ⟨hr, Submodule.subset_span ⟨φ, g', hg', rfl⟩⟩
  have hfun : (fun t : ℝ => l (om (g * γ (Multiplicative.ofAdd t) * g⁻¹, 1) (GlobalTheory.WeilM.pureA F (T f) g'))) =
      fun t => (l ∘ₗ om (g, h)) (om (γ (Multiplicative.ofAdd t), 1) (GlobalTheory.WeilM.pureA F f g')) := by
    funext t
    rw [← key f (hT f), LinearMap.comp_apply, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    congr 3
    exact Prod.ext (by simp only [Prod.fst_mul, inv_mul_cancel_right]) (by simp)
  rw [hfun, ← key f₂ (hT f₂)]
  exact hsd g' hg' _ (hS.adm (g, h) l hl)

section Second

open GlobalTheory.RealLift

theorem actsD_conj : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → M.IsWeil B.ψ χX χW om →
    ∀ g ∈ UAt σ X (evI F), ∀ h ∈ UAt σ W (evI F), ∀ T : SInf F (Fin n × Fin d) ≃ₗ[ℂ] SInf F (Fin n × Fin d),
    (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g, h)) f (T f)) → (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g⁻¹, h⁻¹)) f (T.symm f)) →
    ∀ γ ∈ Lines σ W, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ →
      ActsD (evI F) (fun t => om (1, h * γ (Multiplicative.ofAdd t) * h⁻¹)) (T f) (T f₁) := by
  intro hK F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hb hX hW _hM hw g _hg h _hh T hT hTs γ hγ f hf f₁ hf₁
  have hder := GlobalTheory.RealLift.Main.i_derex
  have hvl := GlobalTheory.RealLift.Main.i_vacline hder
  have hfe := GlobalTheory.RealLift.Main.i_fockex hder
  choose A hA hAθ using fun w => GlobalTheory.RealLift.Main.i_frameex _ _ _ _ _ (hX.sig w) (hX.cartan w)
  choose C hC hCθ using fun w => GlobalTheory.RealLift.Main.i_frameex _ _ _ _ _ (hW.sig w) (hW.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [GlobalTheory.RealLift.Main.incM_map_piInf, one_smul]; exact hA w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [GlobalTheory.RealLift.Main.incM_map_piInf]; exact hC w
  have fr : Framed B.emb (incM F X.J) (incM F W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  obtain ⟨Φ, hΦ⟩ := hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C hb.cm hb.std fr
  have hr := GlobalTheory.RealLift.Main.i_polrange GlobalTheory.RealLift.actsLaws hder hvl F E σ _ _ _ _ _ _ X W M B.ψ B.emb A C Φ hb.cm
    hb.std fr hAθ hCθ hΦ
  have hsp : IsUSplitting (adeleClass F) B.ψ M.co (actAB (cA σ)) om := IsUWeilPair.isUSplitting hw
  have hsp2 := GlobalTheory.WeilSchrodinger.isUSplitting_inr hsp
  obtain ⟨c, hc⟩ := GlobalTheory.RealLift.Main.i_liescalar hK hder hvl F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C Φ _
    hb.cm hb.std fr hΦ hsp2
  obtain ⟨Yg, -, hY⟩ := GlobalTheory.RealLift.Main.i_genex F E σ (Fin d) _ _ B.emb (incM F W.J) Complex.I C hb.cm hC1 γ hγ
  obtain ⟨T0, rfl⟩ := GlobalTheory.RealLift.Main.pol_eq B M Φ hr hf
  obtain ⟨D, hSD⟩ : ∃ D, SD (fun t => om (1, γ (Multiplicative.ofAdd t))) (Φ T0) D := ⟨_, hc γ hγ Yg hY T0⟩
  have hAD : ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (Φ T0) D :=
    (GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) (Φ T0) D D).1 _ (fun t => map_zero _) hSD
  have e0 : f₁ = D := (GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) (Φ T0) f₁ D).2.2.1 _ hf₁ hAD
  subst e0
  have hSD2 : SD (fun t => om (1, h * γ (Multiplicative.ofAdd t) * h⁻¹)) (T (Φ T0)) (T f₁) := by
    intro g' hg' l hl
    have hl' : l ∘ₗ om (g, h) ∈ (adeleClass F).adm (Fin n × Fin d) := hsp.adm (g, h) l hl
    have hrest : ∀ f0 : SInf F (Fin n × Fin d), Rest (evI F) (⇑f0) (fun x => g' fun i => (x i).2) := fun f0 =>
      ⟨fun x z hz => by
        show g' (fun i => (x i + z i).2) = g' (fun i => (x i).2)
        congr 1
        funext i
        show (x i).2 + (z i).2 = (x i).2
        rw [GlobalTheory.RealLift.fin_eq_zero_of_at hz i, add_zero], Submodule.subset_span ⟨f0, g', hg', rfl⟩⟩
    have hpure : ∀ f0 : SInf F (Fin n × Fin d), pureA F (⇑f0) g' = tens (evI F) (⇑f0) (fun x => g' fun i => (x i).2) :=
      fun _ => rfl
    have e1 : om (g⁻¹, h⁻¹) (pureA F (⇑(T (Φ T0))) g') = pureA F (⇑(Φ T0)) g' := by
      rw [hpure, hTs _ _ (hrest _), LinearEquiv.symm_apply_apply]
      rfl
    have e2 : om (g, h) (pureA F (⇑f₁) g') = pureA F (⇑(T f₁)) g' := by
      rw [hpure, hT _ _ (hrest _)]
      rfl
    have e3 : ∀ t : ℝ, om (1, h * γ (Multiplicative.ofAdd t) * h⁻¹) (pureA F (⇑(T (Φ T0))) g') =
        om (g, h) (om (1, γ (Multiplicative.ofAdd t)) (pureA F (⇑(Φ T0)) g')) := by
      intro t
      have hp : ((1 : UA σ X.J), h * γ (Multiplicative.ofAdd t) * h⁻¹) = (g, h) * (1, γ (Multiplicative.ofAdd t)) * (g⁻¹, h⁻¹) :=
        Prod.ext (by simp) (by simp)
      rw [hp, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, e1]
    simp only [e3]
    have := hSD g' hg' _ hl'
    simpa only [LinearMap.comp_apply, e2] using this
  exact (GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) (T (Φ T0)) (T f₁) (T f₁)).1 _ (fun t => map_zero _) hSD2

end Second

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Pair

open GlobalTheory.MajTransport

variable {n d : ℕ} {X Y : Spc F E n} {W Z : Spc F E d}

theorem pair_quot_pr (hKP : GlobalTheory.FunPr.Hypotheses₂) (hσ : ∀ x, σ (σ x) = x) {B : Base F E} {M : Model σ X W} {χX χW : Chr F E}
    {om : Rep σ X W} {r s r' s' : ℕ}
    (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (hM : M.IsGood B.ψ)
    (hw : M.IsWeil B.ψ χX χW om) {g : UA σ X.J} {h : UA σ W.J} (hg : g ∈ UAt σ X (evI F))
    (hh : h ∈ UAt σ W (evI F)) {T : SInf F (Fin n × Fin d) ≃ₗ[ℂ] SInf F (Fin n × Fin d)}
    (hT1 : ∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g, h)) f (T f))
    (hT2 : ∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g⁻¹, h⁻¹)) f (T.symm f))
    (hθX : ∀ w, (mat g).map (piInf (B.emb w)) * X.θ w = Y.θ w * (mat g).map (piInf (B.emb w)))
    (hθW : ∀ w, (mat h).map (piInf (B.emb w)) * W.θ w = Z.θ w * (mat h).map (piInf (B.emb w)))
    {P : Type} [AddCommGroup P] [Module ℂ P] (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P)
    (hq : RealQuot B (reM M Y Z) om p) :
    RealQuot B M om (p ∘ₗ (T : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d))) := by
  have hpol := pair_pol hB hX hW hM hw hg hh hT1 hT2 hθX hθW
  have memT : ∀ f ∈ M.Pol B.ψ B.emb, T f ∈ (reM M Y Z).Pol B.ψ B.emb := fun f hf => by
    have := Submodule.mem_map_of_mem (f := (T : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d))) hf
    rw [hpol] at this; exact this
  refine ⟨?_, fun γ hγ f hf f₁ hD => ?_, fun k hk f hf f₁ hA => ?_⟩
  · rw [Submodule.map_comp, hpol]; exact hq.onto
  · exact hq.lie _ (lines_conj hσ hγ hg) (T f) (memT f hf) (T f₁)
      (deriv_conj_line hKP F E σ B n d X W M χX χW om r s r' s' hB hX hW hM hw g hg h hh T hT1 hT2 γ hγ f hf f₁ hD)
  · have hA' := acts_conj (pres_of hw) hT1 hT2 hA
    have e : ((g, h) * (k, 1) * (g, h)⁻¹ : UA σ X.J × UA σ W.J) = (g * k * g⁻¹, 1) := Prod.ext rfl (by simp)
    rw [e] at hA'
    exact hq.cpt (g * k * g⁻¹) (kinf_conj B.emb hg hθX hk) (T f) (memT f hf) (T f₁) hA'

open GlobalTheory.RealConjFac in

theorem exists_op {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {χX χW : Chr F E} {om : Rep σ X W} (hψ : IsStd ψ)
    (hw : M.IsWeil ψ χX χW om) {g : UA σ X.J} (hg : g ∈ UAt σ X (evI F)) {h : UA σ W.J} (hh : h ∈ UAt σ W (evI F)) :
    ∃ T : SInf F (Fin n × Fin d) ≃ₗ[ℂ] SInf F (Fin n × Fin d), Continuous T ∧
      (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g, h)) f (T f)) ∧
      ∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g⁻¹, h⁻¹)) f (T.symm f) := by
  classical
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hw
  have hpres : ∀ x, ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), om x Φ ∈ GlobalTheory.WeilM.schA F _ :=
    fun x Φ hΦ => hW.pres x Φ hΦ
  obtain ⟨T₁, hT₁⟩ := GlobalTheory.ArchLocalAct.exists_op_of_UAt hψ hw (g, h) hg hh
  obtain ⟨T₂, hT₂⟩ := GlobalTheory.ArchLocalAct.exists_op_of_UAt hψ hw (g⁻¹, h⁻¹) (inv_mem_UAt hg) (inv_mem_UAt hh)
  have hid : ∀ f : SInf F (Fin n × Fin d), Acts (evI F) (1 : Module.End ℂ _) (⇑f) (⇑f) := fun f r _ => rfl
  have e21 : ∀ f, T₂ (T₁ f) = f := by
    intro f
    have hc := acts_comp (hpres _) (hT₁ f) (hT₂ (T₁ f))
    rw [← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one] at hc
    exact ((GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) f (T₂ (T₁ f)) f).2.2.2.1 _ hc (hid f))
  have e12 : ∀ f, T₁ (T₂ f) = f := by
    intro f
    have hc := acts_comp (hpres _) (hT₂ f) (hT₁ (T₂ f))
    rw [← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_inv_cancel, Prod.mk_one_one, map_one] at hc
    exact ((GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) f (T₁ (T₂ f)) f).2.2.2.1 _ hc (hid f))
  refine ⟨LinearEquiv.ofLinear T₁ T₂ (LinearMap.ext e12) (LinearMap.ext e21), ?_, fun f => hT₁ f, fun f => hT₂ f⟩
  show Continuous T₁
  let g₀ := GlobalTheory.ArchLocality.intInd (F := F) (Fin n × Fin d)
  have hg₀ : g₀ ∈ SB _ := GlobalTheory.ArchLocality.intInd_mem _
  have hg₀0 : g₀ 0 = 1 := by
    simp only [g₀, GlobalTheory.ArchLocality.intInd]
    rw [Set.indicator_of_mem (show (0 : Fin n × Fin d → IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) ∈ Set.pi Set.univ
      fun _ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) from
        fun i _ => zero_mem (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F))]
    rfl
  let r₀ : (Fin n × Fin d → AF F) → ℂ := fun x => g₀ fun i => (x i).2
  have hrr₀ : ∀ x z, At (evI F) z → r₀ (x + z) = r₀ x := by
    intro x z hz
    refine congrArg g₀ (funext fun i => ?_)
    show (x i).2 + (z i).2 = (x i).2
    rw [GlobalTheory.ArchLocality.snd_eq_zero_of_at hz i, add_zero]
  have hR₀ : ∀ f : SInf F (Fin n × Fin d), Rest (evI F) ⇑f r₀ := fun f =>
    ⟨hrr₀, Submodule.subset_span ⟨f, g₀, hg₀, rfl⟩⟩
  refine GlobalTheory.ArchJointCont.continuous_of_weak T₁ fun T => ?_
  obtain ⟨l, hl, hlf⟩ := GlobalTheory.ArchJointCont.exists_adm F T
  obtain ⟨T', hT'⟩ := hW.adm (g, h) l hl g₀ hg₀
  refine T'.continuous.congr fun f => ?_
  have e1 : om (g, h) (pureA F ⇑f g₀) = pureA F ⇑(T₁ f) g₀ := hT₁ f r₀ (hR₀ f)
  have e2 := hT' f
  rw [LinearMap.comp_apply, e1, hlf, hg₀0, one_mul] at e2
  exact e2.symm

end Pair

def reR {a a' : ℕ} (R : RealMaps F a a') (T : SInf F (Fin a × Fin (a + a')) ≃ₗ[ℂ] SInf F (Fin a × Fin (a + a')))
    (T' : SInf F (Fin a' × Fin (a + a')) ≃ₗ[ℂ] SInf F (Fin a' × Fin (a + a'))) : RealMaps F a a' :=
  ⟨R.Pi, R.p ∘ₗ (T : SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a'))),
    R.p' ∘ₗ (T' : SInf F (Fin a' × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a' × Fin (a + a')))⟩

open GlobalTheory.MajTransport in

theorem realMaps_transport (hKP : GlobalTheory.FunPr.Hypotheses₂) {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
    (hT : IsTriple B G X om om') {V : Spc F E a} {V' : Spc F E a'} {W : Spc F E (a + a')} (R₂ : RealMaps F a a')
    {g : UA σ G.V.J} (hg : g ∈ UAt σ G.V (evI F)) {g' : UA σ G.V'.J} (hg' : g' ∈ UAt σ G.V' (evI F))
    {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evI F))
    (hθ : ∀ w, (mat g).map (piInf (B.emb w)) * G.V.θ w = V.θ w * (mat g).map (piInf (B.emb w)))
    (hθ' : ∀ w, (mat g').map (piInf (B.emb w)) * G.V'.θ w = V'.θ w * (mat g').map (piInf (B.emb w)))
    (hθW : ∀ w, (mat h).map (piInf (B.emb w)) * G.W.θ w = W.θ w * (mat h).map (piInf (B.emb w)))
    {T : SInf F (Fin a × Fin (a + a')) ≃ₗ[ℂ] SInf F (Fin a × Fin (a + a'))}
    {T' : SInf F (Fin a' × Fin (a + a')) ≃ₗ[ℂ] SInf F (Fin a' × Fin (a + a'))}
    (hT1 : ∀ f : SInf F (Fin a × Fin (a + a')), Acts (evI F) (om (g, h)) f (T f))
    (hT2 : ∀ f : SInf F (Fin a × Fin (a + a')), Acts (evI F) (om (g⁻¹, h⁻¹)) f (T.symm f))
    (hT1' : ∀ f : SInf F (Fin a' × Fin (a + a')), Acts (evI F) (om' (g', h)) f (T' f))
    (hT2' : ∀ f : SInf F (Fin a' × Fin (a + a')), Acts (evI F) (om' (g'⁻¹, h⁻¹)) f (T'.symm f))
    (hT₂ : IsTriple B (reG G V V' W) X om om') (hR₂ : IsRealMaps B (reG G V V' W) om om' R₂) :
    IsRealMaps B G om om' (reR R₂ T T') := by
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma hT.base.cm
  have hT1s : ∀ f : SInf F (Fin a × Fin (a + a')), Acts (evI F) (om (g⁻¹⁻¹, h⁻¹⁻¹)) f (T.symm.symm f) :=
    fun f => by simpa only [inv_inv, LinearEquiv.symm_symm] using hT1 f
  have hpol := pair_pol (Y := V) (Z := W) hT.base hT.geo.hV hT.geo.hW hT.geo.hM hT.weil hg hh hT1 hT2 hθ hθW
  have hpol' := pair_pol (Y := V') (Z := W) hT.base hT.geo.hV' hT.geo.hW hT.geo.hM' hT.weil' hg' hh hT1' hT2' hθ' hθW
  have memT : ∀ f ∈ G.M.Pol B.ψ B.emb, T f ∈ (reG G V V' W).M.Pol B.ψ B.emb := fun f hf => by
    have := Submodule.mem_map_of_mem (f := (T : SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')))) hf
    rw [hpol] at this; exact this
  have memT' : ∀ f ∈ G.M'.Pol B.ψ B.emb, T' f ∈ (reG G V V' W).M'.Pol B.ψ B.emb := fun f hf => by
    have := Submodule.mem_map_of_mem (f := (T' : SInf F (Fin a' × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a' × Fin (a + a')))) hf
    rw [hpol'] at this; exact this
  have memTs : ∀ f' ∈ (reG G V V' W).M.Pol B.ψ B.emb, T.symm f' ∈ G.M.Pol B.ψ B.emb := fun f' hf' => by
    have hf'' : f' ∈ (G.M.Pol B.ψ B.emb).map (T : SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a'))) := by
      rw [hpol]; exact hf'
    obtain ⟨f, hf, rfl⟩ := hf''
    simpa using hf
  have hW' : ∀ w, (mat h⁻¹).map (piInf (B.emb w)) * W.θ w = G.W.θ w * (mat h⁻¹).map (piInf (B.emb w)) :=
    fun w => rev_conj (map_mul_inv _ h) (map_inv_mul _ h) (hθW w)
  refine ⟨?_, ?_, ?_, ?_, hR₂.nontriv, ?_⟩
  · exact pair_quot_pr (Y := V) (Z := W) hKP hσ hT.base hT.geo.hV hT.geo.hW hT.geo.hM hT.weil hg hh hT1 hT2 hθ hθW
      R₂.p hR₂.quot
  · exact pair_quot_pr (Y := V') (Z := W) hKP hσ hT.base hT.geo.hV' hT.geo.hW hT.geo.hM' hT.weil' hg' hh hT1' hT2' hθ'
      hθW R₂.p' hR₂.quot'
  · intro γ hγ f hf f' hf' f₁ f₁' hD hD' hpp
    exact hR₂.lie _ (lines_conj hσ hγ hh) (T f) (memT f hf) (T' f') (memT' f' hf') (T f₁) (T' f₁')
      (actsD_conj hKP F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ hT.base hT.geo.hV hT.geo.hW hT.geo.hM
        hT.weil g hg h hh T hT1 hT2 γ hγ f hf f₁ hD)
      (actsD_conj hKP F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hT.base hT.geo.hV' hT.geo.hW
        hT.geo.hM' hT.weil' g' hg' h hh T' hT1' hT2' γ hγ f' hf' f₁' hD') hpp
  · intro k hk f hf f' hf' f₁ f₁' hA hA' hpp
    have e : ((g, h) * (1, k) * (g, h)⁻¹ : UA σ G.V.J × UA σ G.W.J) = (1, h * k * h⁻¹) := Prod.ext (by simp) rfl
    have e' : ((g', h) * (1, k) * (g', h)⁻¹ : UA σ G.V'.J × UA σ G.W.J) = (1, h * k * h⁻¹) := Prod.ext (by simp) rfl
    have hB := acts_conj (pres_of hT.weil) hT1 hT2 hA
    have hB' := acts_conj (pres_of hT.weil') hT1' hT2' hA'
    rw [e] at hB
    rw [e'] at hB'
    exact hR₂.cpt (h * k * h⁻¹) (kinf_conj B.emb hh hθW hk) (T f) (memT f hf) (T' f') (memT' f' hf') (T f₁) (T' f₁')
      hB hB' hpp
  · intro N hL hK
    refine hR₂.irred N (fun γ' hγ' f' hf' f₁' hD hN => ?_) (fun k' hk' f' hf' f₁' hA hN => ?_)
    · have hD' := actsD_conj hKP F E σ B a (a + a') (reS G.V V) (reS G.W W) (reG G V V' W).M X.β (X.β / X.α) om _ _ _ _
        hT₂.base hT₂.geo.hV hT₂.geo.hW hT₂.geo.hM hT₂.weil g⁻¹ (uat_inv hg) h⁻¹ (uat_inv hh) T.symm hT2 hT1s γ' hγ'
        f' hf' f₁' hD
      have hN' : R₂.p (T (T.symm f')) ∈ N := by rwa [LinearEquiv.apply_symm_apply]
      have := hL _ (lines_conj hσ hγ' (uat_inv hh)) (T.symm f') (memTs f' hf') (T.symm f₁') hD' hN'
      have this' : R₂.p (T (T.symm f₁')) ∈ N := this
      rwa [LinearEquiv.apply_symm_apply] at this'
    · have hB := acts_conj (pres_of hT.weil) hT2 hT1s hA
      have hB' : Acts (evI F) (om (1, h⁻¹ * (id k' : UA σ G.W.J) * h⁻¹⁻¹)) (T.symm f') (T.symm f₁') := by
        convert hB using 3
        exact Prod.ext (by show (1 : UA σ G.V.J) = g⁻¹ * 1 * g⁻¹⁻¹; simp) rfl
      have hN' : R₂.p (T (T.symm f')) ∈ N := by rwa [LinearEquiv.apply_symm_apply]
      have := hK _ (kinf_conj (X := reS G.W W) (Y := G.W) B.emb (uat_inv hh) hW' hk') (T.symm f') (memTs f' hf')
        (T.symm f₁') hB' hN'
      have this' : R₂.p (T (T.symm f₁')) ∈ N := this
      rwa [LinearEquiv.apply_symm_apply] at this'

open GlobalTheory.MajTransport in

theorem polMatch_transport {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
    (hT : IsTriple B G X om om') {V : Spc F E a} {V' : Spc F E a'} {W : Spc F E (a + a')} (R₂ : RealMaps F a a')
    {g : UA σ G.V.J} (hg : g ∈ UAt σ G.V (evI F)) {g' : UA σ G.V'.J} (hg' : g' ∈ UAt σ G.V' (evI F))
    {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evI F))
    (hθ : ∀ w, (mat g).map (piInf (B.emb w)) * G.V.θ w = V.θ w * (mat g).map (piInf (B.emb w)))
    (hθ' : ∀ w, (mat g').map (piInf (B.emb w)) * G.V'.θ w = V'.θ w * (mat g').map (piInf (B.emb w)))
    (hθW : ∀ w, (mat h).map (piInf (B.emb w)) * G.W.θ w = W.θ w * (mat h).map (piInf (B.emb w)))
    {T : SInf F (Fin a × Fin (a + a')) ≃ₗ[ℂ] SInf F (Fin a × Fin (a + a'))}
    {T' : SInf F (Fin a' × Fin (a + a')) ≃ₗ[ℂ] SInf F (Fin a' × Fin (a + a'))}
    (hT1 : ∀ f : SInf F (Fin a × Fin (a + a')), Acts (evI F) (om (g, h)) f (T f))
    (hT2 : ∀ f : SInf F (Fin a × Fin (a + a')), Acts (evI F) (om (g⁻¹, h⁻¹)) f (T.symm f))
    (hT1' : ∀ f : SInf F (Fin a' × Fin (a + a')), Acts (evI F) (om' (g', h)) f (T' f))
    (hT2' : ∀ f : SInf F (Fin a' × Fin (a + a')), Acts (evI F) (om' (g'⁻¹, h⁻¹)) f (T'.symm f))
    (Rf : FinMaps F a a') {Φ Φ'} (hm : PolMatch B G X (reR R₂ T T') Rf Φ Φ') :
    PolMatch B (reG G V V' W) X R₂ Rf (om (g, h) Φ) (om' (g', h) Φ') := by
  have hpol := pair_pol (Y := V) (Z := W) hT.base hT.geo.hV hT.geo.hW hT.geo.hM hT.weil hg hh hT1 hT2 hθ hθW
  have hpol' := pair_pol (Y := V') (Z := W) hT.base hT.geo.hV' hT.geo.hW hT.geo.hM' hT.weil' hg' hh hT1' hT2' hθ' hθW
  have memT : ∀ f ∈ G.M.Pol B.ψ B.emb, T f ∈ (reG G V V' W).M.Pol B.ψ B.emb := fun f hf => by
    have := Submodule.mem_map_of_mem (f := (T : SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')))) hf
    rw [hpol] at this; exact this
  have memT' : ∀ f ∈ G.M'.Pol B.ψ B.emb, T' f ∈ (reG G V V' W).M'.Pol B.ψ B.emb := fun f hf => by
    have := Submodule.mem_map_of_mem (f := (T' : SInf F (Fin a' × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a' × Fin (a + a')))) hf
    rw [hpol'] at this; exact this
  obtain ⟨T₀, hT₀, m, m', f, φ, f', φ', hf, hf', hΦ, hΦ', hsum⟩ := hm
  have hcof : ∀ᶠ v in cofinite, v ∉ T₀ := T₀.finite_toSet.eventually_cofinite_notMem
  refine ⟨T₀, hT₀, m, m', fun i => T (f i), φ, fun j => T' (f' j), φ',
    fun i => ⟨memT _ (hf i).1, (hf i).2.1, (hf i).2.2⟩, fun j => ⟨memT' _ (hf' j).1, (hf' j).2.1, (hf' j).2.2⟩,
    ?_, ?_, hsum⟩
  · rw [hΦ, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact hT1 (f i) _ (rest_pure (f i) (φ i) (hf i).2.1
      ((hcof.and hT.geo.hM.std).mono fun v hv => ((hf i).2.2 v hv.1).trans hv.2))
  · rw [hΦ', map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact hT1' (f' j) _ (rest_pure (f' j) (φ' j) (hf' j).2.1
      ((hcof.and hT.geo.hM'.std).mono fun v hv => ((hf' j).2.2 v hv.1).trans hv.2))

end GlobalTheory.ReBase

end
