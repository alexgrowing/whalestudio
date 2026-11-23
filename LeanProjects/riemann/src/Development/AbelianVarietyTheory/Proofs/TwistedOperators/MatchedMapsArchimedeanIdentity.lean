import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleGlobalProductFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible

noncomputable section

namespace GlobalTheory.KStableLie

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mem_of_isExp {V : Type} [AddCommGroup V] [Module ℂ V] {L U : Module.End ℂ V} (hU : IsExp L U)
    (N : Submodule ℂ V) (hL : ∀ y ∈ N, L y ∈ N) {v : V} (hv : v ∈ N) : U v ∈ N := by
  have hpow : ∀ m : ℕ, (L ^ m) v ∈ N := by
    intro m
    induction m with
    | zero => simpa using hv
    | succ m ih => rw [pow_succ', Module.End.mul_apply]; exact hL _ ih
  by_contra hn
  obtain ⟨l, hl, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
  have hz : ∀ y ∈ N, l y = 0 := fun y hy => by
    have h' := Submodule.mem_map_of_mem (f := l) hy
    rw [hmap, Submodule.mem_bot] at h'
    exact h'
  have h0 : (fun m : ℕ => ((m.factorial : ℂ))⁻¹ * l ((L ^ m) v)) = fun _ => 0 := by
    funext m; rw [hz _ (hpow m), mul_zero]
  have hs := hU v l
  rw [h0] at hs
  exact hl (hs.unique hasSum_zero)

open scoped Classical in

theorem kStable_of_lieStable (hP : GlobalTheory.FunPr.Hypotheses₂) {σ : E →ₐ[F] E} {B : Base F E} {n d : ℕ} {X : Spc F E n}
    {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ} (hb : B.IsGood σ)
    (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (hw : M.IsWeil B.ψ χX χW om) {Pi : Type} [AddCommGroup Pi]
    [Module ℂ Pi] (p : SInf F (Fin n × Fin d) →ₗ[ℂ] Pi) (N : Submodule ℂ Pi)
    (hlie : ∀ γ ∈ Lines σ W, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ → p f ∈ N → p f₁ ∈ N)
    {k : UA σ W.J} (hk : k ∈ KInf σ W B.emb) {f : SInf F (Fin n × Fin d)} (hf : f ∈ M.Pol B.ψ B.emb)
    {f₁ : SInf F (Fin n × Fin d)} (hact1 : Acts (evI F) (om (1, k)) f f₁) (hfN : p f ∈ N) : p f₁ ∈ N := by
  have hAL : ActsLaws := GlobalTheory.RealLift.actsLaws
  have hfr : GlobalTheory.RealLift.FrameEx := GlobalTheory.T.cartanEigen_orthonormalFrame_exists
  have hder : GlobalTheory.RealLift.DerEx := GlobalTheory.T.archHeisenbergDerivatives_exist
  have hvl : GlobalTheory.RealLift.VacLine := GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives hder
  have hfe : GlobalTheory.RealLift.FockEx := GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives hder
  have hls : GlobalTheory.RealLift.LieScalar := GlobalTheory.T.lieScalar_of_prints_derEx_vacLine hP hder hvl
  have hpr : GlobalTheory.RealLift.PolRange := GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws hAL hder hvl
  have hkl : GlobalTheory.RealLift.KLine := GlobalTheory.RealLift.kLine_of_lineEx GlobalTheory.T.unitaryLieElements_generate_oneParamLines
  choose A hA hAθ using fun w => hfr _ _ _ _ _ (hX.sig w) (hX.cartan w)
  choose C hC hCθ using fun w => hfr _ _ _ _ _ (hW.sig w) (hW.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [GlobalTheory.PolCompact.incM_map_piInf', one_smul]; exact hA w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [GlobalTheory.PolCompact.incM_map_piInf']; exact hC w
  have fr : Framed B.emb (incM F X.J) (incM F W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  obtain ⟨Φ, hΦ⟩ := hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C hb.cm hb.std fr
  have hr := hpr F E σ _ _ _ _ _ _ X W M B.ψ B.emb A C Φ hb.cm hb.std fr hAθ hCθ hΦ
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (incM F W.J) M.co χX χW om := hw
  obtain ⟨c, hact⟩ := hls F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C Φ _ hb.cm hb.std fr hΦ hwp.1.1
  have hadm := fun g => (hwp.isUSplitting).adm g
  obtain ⟨γ, hγ, Yg, hgen, hKC, hγ1⟩ :=
    hkl F E σ (Fin d) _ _ B.emb (incM F W.J) Complex.I C W.θ hb.cm hC1 hCθ k hk.1 hk.2
  have hloc := GlobalTheory.RealLift.locFin_sumPl _ _ _
    (fun w => GlobalTheory.PolCompact.locFin_second r s r' s' (Yg w) (hKC w) (c w * (Yg w).trace))
  obtain ⟨U, hU, hSA⟩ := GlobalTheory.T.weakExponential_action_on_fockVectors F (Fin n × Fin d) _ Φ _ ((om.comp (MonoidHom.inr _ _)).comp γ) hloc
    (fun t l hl => hadm _ l hl) (fun T => hact γ hγ Yg hgen T)
  rw [← hr] at hf
  obtain ⟨T, rfl⟩ := hf

  set N' : Submodule ℂ (Tens F r s r' s') := N.comap (p ∘ₗ Φ) with hN'
  have hstab : ∀ y ∈ N', sumPl (fun w => fockAct2 r s r' s' (Yg w) + (c w * (Yg w).trace) • 1) y ∈ N' := by
    intro y hy
    have hsd := hact γ hγ Yg hgen y
    have had : ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (Φ y)
        (Φ (sumPl (fun w => fockAct2 r s r' s' (Yg w) + (c w * (Yg w).trace) • 1) y)) :=
      (hAL F (Fin n × Fin d) _ _ (Φ y)).1 _ (fun t => map_zero _) hsd
    have hy' : Φ y ∈ M.Pol B.ψ B.emb := hr ▸ LinearMap.mem_range_self Φ y
    exact hlie γ hγ _ hy' _ had hy
  have hUT : U T ∈ N' := mem_of_isExp hU N' hstab hfN
  have h1 := hSA T
  rw [MonoidHom.comp_apply, hγ1] at h1
  have hA2 : Acts (evI F) (om (1, k)) (Φ T) (Φ (U T)) :=
    (hAL F (Fin n × Fin d) (Φ T) (Φ (U T)) (Φ (U T))).2.1 _ (map_zero _) h1
  have he : f₁ = Φ (U T) := (hAL F (Fin n × Fin d) (Φ T) f₁ (Φ (U T))).2.2.2.1 _ hact1 hA2
  rw [he]
  exact hUT

theorem lieStable_kStable : GlobalTheory.FunPr.Hypotheses₂ → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ N : Submodule ℂ R.Pi,
      (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Γ.W, ∀ f ∈ Γ.M.Pol Bs.ψ Bs.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ →
        R.p f ∈ N → R.p f₁ ∈ N) →
      ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ Γ.W Bs.emb, ∀ f ∈ Γ.M.Pol Bs.ψ Bs.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (1, k)) f f₁ → R.p f ∈ N → R.p f₁ ∈ N := by
  intro hP F E _ _ _ _ _ σ a a' Bs Γ Xc om om' R Rf h N hlie k hk f hf f₁ hact hN
  exact kStable_of_lieStable hP h.triple.base h.triple.geo.hV h.triple.geo.hW h.triple.weil R.p N hlie hk hf hact hN

end GlobalTheory.KStableLie

end
