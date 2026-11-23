import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanTranslatesEqTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SingleThetaSeriesKEquivariantLowestType
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicDiscreteSeriesLowestKTypeSmoothIrredu
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolShapeOfOverK
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelSpanOverClasses
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open GlobalTheory.BigTop GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Classical

namespace GlobalTheory.TraceRatPf

theorem zero_of_span' {ι : Type} [Fintype ι] [DecidableEq ι] {L : ι → Type} [∀ j, AddCommGroup (L j)] [∀ j, Module ℂ (L j)]
    {X : Type} [AddCommGroup X] [Module ℂ X] (F : MultilinearMap ℂ L X) (v₀ : ∀ j, L j) (P : ∀ j, L j → Prop)
    (hspan : ∀ j, Submodule.span ℂ {u | P j u} = ⊤)
    (hstep : ∀ (v : ∀ j, L j) (j : ι) (u : L j), v j = v₀ j → P j u → F v = 0 → F (Function.update v j u) = 0)
    (h0 : F v₀ = 0) : ∀ v, F v = 0 := by
  have key : ∀ s : Finset ι, ∀ v : ∀ j, L j, (∀ j ∉ s, v j = v₀ j) → F v = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro v hv
      have : v = v₀ := funext fun j => hv j (Finset.notMem_empty j)
      rw [this]; exact h0
    | insert a s ha ih =>
      intro v hv
      have h1 : F (Function.update v a (v₀ a)) = 0 := ih _ fun j hj => by
        by_cases hja : j = a
        · subst hja; simp
        · rw [Function.update_of_ne hja]; exact hv j (by simp [hja, hj])
      have hmem : v a ∈ Submodule.span ℂ {u | P a u} := by rw [hspan a]; trivial
      have hall : ∀ u ∈ Submodule.span ℂ {u | P a u},
          F (Function.update (Function.update v a (v₀ a)) a u) = 0 := by
        intro u hu
        induction hu using Submodule.span_induction with
        | mem u hu => exact hstep _ a u (by simp) hu h1
        | zero => exact F.map_update_zero _ _
        | add x y _ _ hx hy => rw [F.map_update_add, hx, hy, add_zero]
        | smul c x _ hx => rw [F.map_update_smul, hx, smul_zero]
      have e : Function.update (Function.update v a (v₀ a)) a (v a) = v := by simp
      rw [← e]; exact hall _ hmem
  exact fun v => key Finset.univ v (fun j hj => absurd (Finset.mem_univ j) hj)

theorem adForm_lowT_equiv' {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hHW : R.models_HW) (i : Fin D.R.m) (x : Fin (R.nW i) → D.what₂.LL) (τ : D.what₂.Tau) (k : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (hk : k ∈ Formalism.REAL.Kset ((R.MW i (sg0 D A)).ε τ)) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (u : lowT (R.MW i (sg0 D A)) τ) (hu : ((u : (R.MW i (sg0 D A)).sm τ) : (R.MW i (sg0 D A)).H τ) = (R.MW i (sg0 D A)).σ τ k ((v τ : (R.MW i (sg0 D A)).sm τ) : (R.MW i (sg0 D A)).H τ)) : adForm R i x (fun ρ => (Function.update v τ u ρ : (R.MW i (sg0 D A)).sm ρ)) = Formalism.L2.Theta.rTr (Wc D i) (atTau R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ)) (adForm R i x (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ))) := by
  have hmem : adForm R i x ∈ R.Wall i (sg0 D A) := by
    rw [← (hHW i (sg0 D A)).2.1]
    exact LinearMap.mem_range_self _ _
  have hfr : IsUnit ((R.MW i (sg0 D A)).fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 ((R.MW i (sg0 D A)).fr_unit τ)
  have e1 : (R.MW i (sg0 D A)).fr τ * ((R.MW i (sg0 D A)).fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hfr
  have hkJ : kᴴ * Formalism.REAL.Jm ((R.MW i (sg0 D A)).ε τ) * k = Formalism.REAL.Jm ((R.MW i (sg0 D A)).ε τ) := by
    have hu1 : kᴴ * k = 1 := (Matrix.mem_unitaryGroup_iff').1 hk.1
    rw [Matrix.mul_assoc, ← hk.2, ← Matrix.mul_assoc, hu1, Matrix.one_mul]
  have hg : ((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D (Wc D i) τ) := by
    show _ = _
    rw [← (R.MW i (sg0 D A)).fr_gram τ]
    have e3 : (((R.MW i (sg0 D A)).fr τ)⁻¹)ᴴ * ((R.MW i (sg0 D A)).fr τ)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, e1, Matrix.conjTranspose_one]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (((R.MW i (sg0 D A)).fr τ)⁻¹)ᴴ, e3, Matrix.one_mul,
      ← Matrix.mul_assoc ((R.MW i (sg0 D A)).fr τ) (((R.MW i (sg0 D A)).fr τ)⁻¹), e1, Matrix.one_mul]
    rw [← Matrix.mul_assoc kᴴ, ← Matrix.mul_assoc (kᴴ * _), hkJ]
  have hrep : (R.MW i (sg0 D A)).rep τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ) =
      (R.MW i (sg0 D A)).σ τ k := by
    unfold Formalism.IndefR.Mult.DSModel.rep
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, e1, Matrix.one_mul, Matrix.mul_assoc, e1, Matrix.mul_one]
  have hupd : (fun ρ => (Function.update v τ u ρ : (R.MW i (sg0 D A)).sm ρ)) =
      Function.update (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ)) τ (u : (R.MW i (sg0 D A)).sm τ) := by
    funext ρ
    by_cases hρ : ρ = τ
    · subst hρ; simp
    · simp [Function.update_of_ne hρ]
  rw [hupd]
  suffices H : ∀ T ∈ R.Wall i (sg0 D A), T (Function.update (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ)) τ (u : (R.MW i (sg0 D A)).sm τ)) =
      Formalism.L2.Theta.rTr (Wc D i) (atTau R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ))
        (T (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ))) from H _ hmem
  intro T0 hT0
  induction hT0 using Submodule.span_induction with
  | mem T hT =>
    exact hT.equiv τ _ hg _ _ (by rw [hrep]; exact hu)
  | zero => rfl
  | add S T _ _ hS hT =>
    simp only [MultilinearMap.add_apply, hS, hT]
    rfl
  | smul a T _ hT =>
    simp only [MultilinearMap.smul_apply, hT]
    rfl

end GlobalTheory.TraceRatPf

namespace GlobalTheory.TraceRatPf

theorem translate_all {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)
    (hcore : GlobalTheory.Hk3.Core R F) (hU : R.LUnif) (i : Fin D.R.m) (v₀ : (R.MW i (sg0 D A)).Vec)
    (hext : IsExtVec (R.MW i (sg0 D A)) v₀) {ξ χ ξR Q ω φ} (hker : KerDat R i ξ χ ξR Q ω φ)
    (h : GA D (Vc D i)) (y : (R.cV i).W) (u : ∀ τ, lowT (R.MW i (sg0 D A)) τ)
    (hu : ∀ τ, (u τ : (R.MW i (sg0 D A)).sm τ) = v₀ τ) (x : Fin (R.nW i) → D.what₂.LL)
    (hx : adForm R i x (fun τ => u τ) = singleSeries R i ω φ h y u) (g : G) :
    ∀ v : ∀ τ, lowT (R.MW i (sg0 D A)) τ, adForm R i ((R.FW i).ρ g x) (fun τ => v τ) =
      D.what₂.embLL (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) •
        Formalism.IndefR.Links.actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) (singleSeries R i ω φ h y v) := by
  have hs0 : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  have hσ : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK (sg0 D A) :=
    fun x _ => congrArg (fun s : D.what₂.LL →+* ℂ => s (D.embE x)) hs0
  have hc : (sg0 D A) (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) = D.what₂.embLL (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) :=
    congrArg (fun s : D.what₂.LL →+* ℂ => s (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL)) hs0
  let Lin : LowT (R.MW i (sg0 D A)) →ₗ[ℂ] (GA D (Wc D i) → ℂ) :=
    { toFun := fun t g' => Datum.thetaKO ω h g' (Datum.pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1)
        (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) φ (R.ioP i t y))
      map_add' := fun a b => by funext g'; simp [Datum.thetaKO, map_add]
      map_smul' := fun a b => by funext g'; simp [Datum.thetaKO, map_smul] }
  let act := Formalism.IndefR.Links.actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g)
  let c : ℂ := D.what₂.embLL (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL)
  let Rt : MultilinearMap ℂ (fun ρ => lowT (R.MW i (sg0 D A)) ρ) (GA D (Wc D i) → ℂ) :=
    (c • (act ∘ₗ Lin)).compMultilinearMap (PiTensorProduct.tprod ℂ)
  let Lf : MultilinearMap ℂ (fun ρ => lowT (R.MW i (sg0 D A)) ρ) (GA D (Wc D i) → ℂ) :=
    (adForm R i ((R.FW i).ρ g x)).compLinearMap fun ρ => (lowT (R.MW i (sg0 D A)) ρ).subtype
  have hRt : ∀ w, Rt w = c • act (singleSeries R i ω φ h y w) := fun w => rfl
  have hLf : ∀ w, Lf w = adForm R i ((R.FW i).ρ g x) (fun ρ => (w ρ : (R.MW i (sg0 D A)).sm ρ)) := fun w => rfl
  have hrs : ∀ (g' : GA D (Wc D i)) (a b : GA D (Wc D i) → ℂ) (s : ℂ),
      Formalism.L2.Theta.rTr (Wc D i) g' a - s • Formalism.L2.Theta.rTr (Wc D i) g' b = Formalism.L2.Theta.rTr (Wc D i) g' (a - s • b) :=
    fun _ _ _ _ => rfl
  have hat : Lf u = Rt u := by
    rw [hLf, hRt]
    have e := congrArg (fun T => T (fun ρ => (u ρ : (R.MW i (sg0 D A)).sm ρ))) ((hU i (sg0 D A)).2.2 g x)
    change adForm R i ((R.FW i).ρ g x) _ = _ at e
    rw [e, hc]
    change c • act (adForm R i x (fun ρ => (u ρ : (R.MW i (sg0 D A)).sm ρ))) = _
    rw [hx]
  have key := zero_of_span' (Lf - Rt) u
    (fun ρ z => ∃ k ∈ Formalism.REAL.Kset ((R.MW i (sg0 D A)).ε ρ),
      ((z : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ) = (R.MW i (sg0 D A)).σ ρ k ((v₀ ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ))
    (fun ρ => GlobalTheory.LowSpan.span_translates_eq_top _ _ hext ρ
      ((GlobalTheory.HolLowOnce.lowSm_and_lowIrr D _ _ _ (GlobalTheory.GalLift.ProjLift.holShape_of_overK R i hσ)).2 ρ))
    (fun w ρ z hw ⟨k, hk, hu'⟩ h0 => by
      have hu2 : ((z : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ) = (R.MW i (sg0 D A)).σ ρ k ((w ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ) := by
        rw [hu', hw, hu]
      have e1 := adForm_lowT_equiv' R hcore.models.HW i ((R.FW i).ρ g x) ρ k hk w z hu2
      have e2 := GlobalTheory.SeriesKEquiv.singleSeries_kEquiv R F hcore i _ χ ξR _ ω φ hker _ _ φ hker.vecOf h y g ρ k hk w z hu2
      rw [MultilinearMap.sub_apply, hLf, hRt, e1, e2]
      change Formalism.L2.Theta.rTr (Wc D i) _ (Lf w) - c • Formalism.L2.Theta.rTr (Wc D i) _ (act _) = 0
      rw [hrs, ← hRt, ← MultilinearMap.sub_apply, h0]
      rfl)
    (by rw [MultilinearMap.sub_apply, hat, sub_self])
  intro w
  have := key w
  rw [MultilinearMap.sub_apply, sub_eq_zero, hLf, hRt] at this
  exact this

end GlobalTheory.TraceRatPf

namespace GlobalTheory.TraceRatPf

theorem adForm_sum {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    {ι : Type} (s : Finset ι) (f : ι → Fin (R.nW i) → D.what₂.LL) :
    adForm R i (∑ g ∈ s, f g) = ∑ g ∈ s, adForm R i (f g) := by
  induction s using Finset.induction_on with
  | empty =>
    have e := GlobalTheory.TraceClassRank.adForm_smul (R := R) (i := i) 0 0
    rw [zero_smul, map_zero, zero_smul] at e
    simpa using e
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, GlobalTheory.TraceClassRank.adForm_add, ih]

theorem traceRat : TraceRat := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hcore hU i v₀ hext ξ χ ξR Q ω φ hker U ψ h y u hu x hx
  let c' : G → D.what₂.LL := fun g =>
    if hg : g ∈ U then (((ψ ⟨g, hg⟩)⁻¹ * ((R.FW i).chi g)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) else 0
  refine ⟨∑ g, c' g • (R.FW i).ρ g x, fun v => ?_⟩
  rw [adForm_sum, MultilinearMap.sum_apply]
  unfold levelTrace gaL
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [GlobalTheory.TraceClassRank.adForm_smul, MultilinearMap.smul_apply,
    translate_all R F hcore hU i v₀ hext hker h y u hu x hx g v, LinearMap.smul_apply, smul_smul, ← map_mul]
  congr 2
  by_cases hg : g ∈ U
  · simp only [c', dif_pos hg]
    rw [← Units.val_mul, mul_assoc, inv_mul_cancel, mul_one]
  · simp only [c', dif_neg hg, zero_mul, map_zero]

end GlobalTheory.TraceRatPf
