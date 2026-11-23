import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Forms
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReferenceTupleLiftFormsPassToCoeffEnlargement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockDataLevelFormsTransportFieldMap
import Formalism.LocalToGlobal.Columns.CoefficientsModP.BaseCh
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftFormsReferenceTupleBasisExtendedStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.DefLatBC

section NabAbstract

variable {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K']

theorem exists_coord_of_mem_bcPol (φ : K →+* K') {σ : Type} (F : K' →+ K) (hF : ∀ a x, F (φ a * x) = a * F x)
    (hI : ∀ a : 𝓞 K', ∃ r : 𝓞 K, F (algebraMap (𝓞 K') K' a) = algebraMap (𝓞 K) K r)
    (N : Submodule (𝓞 K) (MvPolynomial σ K)) {p : MvPolynomial σ K'} (hp : p ∈ bcPol φ N) :
    ∀ a : 𝓞 K', ∃ q ∈ N, ∀ m, q.coeff m = F (algebraMap (𝓞 K') K' a * p.coeff m) := by
  unfold bcPol at hp
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    intro a
    obtain ⟨r, hr⟩ := hI a
    refine ⟨r • y, N.smul_mem r hy, fun m => ?_⟩
    beta_reduce
    have hc : (r • y).coeff m = algebraMap (𝓞 K) K r * y.coeff m :=
      (MvPolynomial.coeff_smul m r y).trans (Algebra.smul_def _ _)
    refine hc.trans ?_
    rw [MvPolynomial.coeff_map, mul_comm (algebraMap (𝓞 K') K' a), hF, hr, mul_comm]
  | zero => exact fun a => ⟨0, N.zero_mem, fun m => by simp⟩
  | add x y _ _ hx hy =>
    intro a
    obtain ⟨q, hq, e⟩ := hx a
    obtain ⟨q', hq', e'⟩ := hy a
    exact ⟨q + q', N.add_mem hq hq', fun m => by
      rw [MvPolynomial.coeff_add, MvPolynomial.coeff_add, mul_add, map_add, e, e']⟩
  | smul r x _ hx =>
    intro a
    obtain ⟨q, hq, e⟩ := hx (a * r)
    exact ⟨q, hq, fun m => by
      rw [e, ← algebraMap_smul K' r x, MvPolynomial.coeff_smul, smul_eq_mul, map_mul (algebraMap (𝓞 K') K'), mul_assoc]⟩

theorem integral_span_of_values (φ : K →+* K') {σ C M M' : Type} [AddCommGroup M] [Module K M] [AddCommGroup M'] [Module K' M']
    [Module (𝓞 K') M'] [IsScalarTower (𝓞 K') K' M']
    (L : M →+ M') (hL : ∀ (a : K) (f : M), L (a • f) = φ a • L f) (hsp : ⊤ ≤ Submodule.span K' (Set.range L))
    (ev : C → M →ₗ[K] MvPolynomial σ K) (ev' : C → M' →ₗ[K'] MvPolynomial σ K')
    (hev : ∀ c f, ev' c (L f) = MvPolynomial.map φ (ev c f)) (N : C → Submodule (𝓞 K) (MvPolynomial σ K)) (f' : M') :
    (∀ c, ev' c f' ∈ bcPol φ (N c)) ↔ f' ∈ Submodule.span (𝓞 K') (L '' {f | ∀ c, ev c f ∈ N c}) := by
  constructor
  · intro h
    obtain ⟨m, b, F, hF, hI, hb⟩ := exists_dual_family φ
    obtain ⟨n, a, g, hg⟩ := Submodule.mem_span_set'.1 (hsp (Submodule.mem_top (x := f')))
    choose u hu using fun k => (g k).2
    have hf : f' = ∑ k, a k • L (u k) := by
      rw [← hg]
      exact Finset.sum_congr rfl fun k _ => by rw [hu]
    have h1 : f' = ∑ i, b i • L (∑ k, F i (a k) • u k) := by
      rw [hf]
      simp only [map_sum, hL, Finset.smul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      conv_lhs => rw [hb (a k), Finset.sum_smul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_smul, algebraMap_smul]
    rw [h1]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, fun c => ?_, rfl⟩)
    obtain ⟨q, hq, e⟩ := exists_coord_of_mem_bcPol φ (F i) (hF i) (hI i) (N c) (h c) 1
    have h2 : ev c (∑ k, F i (a k) • u k) = q := by
      ext μ
      rw [e, hf, map_one, one_mul]
      simp only [map_sum, map_smul, hev, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, MvPolynomial.coeff_map,
        smul_eq_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_comm (a k), hF, mul_comm]
    rw [h2]
    exact hq
  · intro h c
    induction h using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      rw [hev]
      exact bc_map_mem φ (hy c)
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx =>
      rw [← algebraMap_smul K' r x, map_smul, algebraMap_smul]
      exact Submodule.smul_mem _ _ hx

theorem mem_polOfVV_iff {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (T : Submodule (𝓞 K) (VV K lam))
    (x : VV K lam) : x.1 ∈ polOfVV lam T ↔ x ∈ T := by
  constructor
  · rintro ⟨y, hy, e⟩
    have : y = x := Subtype.ext e
    exact this ▸ hy
  · exact fun h => ⟨x, h, rfl⟩

def NabSpan [StarRing K] [StarRing K'] (S : CSD K) (S' : CSD K') (T : S.Forms → S'.Forms) : Prop :=
  ∀ f' : S'.Forms, (∀ c, (f' : S'.Cl → S'.V) c ∈ S'.Nab c) ↔
    f' ∈ Submodule.span (𝓞 K') (T '' {f : S.Forms | ∀ c, (f : S.Cl → S.V) c ∈ S.Nab c})

def SemiSpan [StarRing K] [StarRing K'] (φ : K →+* K') (S : CSD K) (S' : CSD K') (T : S.Forms → S'.Forms) : Prop :=
  (∀ f g, T (f + g) = T f + T g) ∧ (∀ (a : K) (f : S.Forms), T (a • f) = φ a • T f) ∧
    ⊤ ≤ Submodule.span K' (Set.range T)

theorem semiSpan_of [StarRing K] [StarRing K'] (φ : K →+* K') (S : CSD K) (S' : CSD K') (T : S.Forms →+ S'.Forms)
    (hT : ∀ (a : K) (f : S.Forms), T (a • f) = φ a • T f)
    (h : ⊤ ≤ Submodule.span K' (Set.range fun k => T (S.basis k))) : SemiSpan φ S S' T :=
  ⟨T.map_add, hT, h.trans (Submodule.span_mono (by rintro _ ⟨k, rfl⟩; exact ⟨S.basis k, rfl⟩))⟩

theorem nabSpan_of_values [StarRing K] [StarRing K'] (φ : K →+* K') {σ : Type} {S : CSD K} {S' : CSD K'}
    (T : S.Forms → S'.Forms) (hT : SemiSpan φ S S' T) (p : S.Cl → S'.Cl) (hp : Function.Surjective p)
    (v : S.V →ₗ[K] MvPolynomial σ K) (v' : S'.V →ₗ[K'] MvPolynomial σ K')
    (hev : ∀ c (f : S.Forms), v' ((T f : S'.Cl → S'.V) (p c)) = MvPolynomial.map φ (v ((f : S.Cl → S.V) c)))
    (N : S.Cl → Submodule (𝓞 K) (MvPolynomial σ K)) (hN : ∀ c x, x ∈ S.Nab c ↔ v x ∈ N c)
    (hN' : ∀ c x, x ∈ S'.Nab (p c) ↔ v' x ∈ bcPol φ (N c)) : NabSpan S S' T := by
  intro f'
  have main := integral_span_of_values φ (C := S.Cl) (AddMonoidHom.mk' T hT.1) hT.2.1 hT.2.2
    (fun c => v ∘ₗ LinearMap.proj (R := K) (φ := fun _ : S.Cl => S.V) c ∘ₗ S.Forms.subtype)
    (fun c => v' ∘ₗ LinearMap.proj (R := K') (φ := fun _ : S'.Cl => S'.V) (p c) ∘ₗ S'.Forms.subtype) hev N f'
  have e1 : {f : S.Forms | ∀ c, (f : S.Cl → S.V) c ∈ S.Nab c} =
      {f | ∀ c, (v ∘ₗ LinearMap.proj (R := K) (φ := fun _ : S.Cl => S.V) c ∘ₗ S.Forms.subtype) f ∈ N c} :=
    Set.ext fun f => forall_congr' fun c => hN c _
  rw [e1, hp.forall]
  exact Iff.trans (forall_congr' fun c => hN' c _) main

end NabAbstract

theorem nab_res_symm {K : Type} [Field K] [NumberField K] [StarRing K] (S : Formalism.L2.Col.GSD K) (h : S.Ok)
    (f : (S.toCSD h).Forms) (c : S.Cl) :
    (((S.res h).symm f : S.EqFun) : S.D → S.V) (Quotient.out c) = (f.1 : S.Cl → S.V) c :=
  congrArg (fun u : (S.toCSD h).Forms => (u.1 : S.Cl → S.V) c) ((S.res h).apply_symm_apply f)

theorem nab_round_bc (X : Formalism.L2.Col.Fields) {L : Type} [Field L] [NumberField L] [StarRing L] (ι : X.K →+* L)
    (e : X.Tau → X.E →+* L) (he : ∀ τ, ι.comp (X.emb τ) = e τ) {n : ℕ} (lam : X.Tau → DomWeight n)
    {SG₁ SG₂ : Finset (HeightOneSpectrum (𝓞 X.E))} (hS : SG₂ = SG₁)
    (Λ₁ : Formalism.L2.Col.LevFam X.E X.K n SG₁) (Λ₂ : Formalism.L2.Col.LevFam X.E L n SG₂)
    (hH : ∀ (w : ↥SG₁) (hw : w.1 ∈ SG₂), (Λ₂ ⟨w.1, hw⟩).H = (Λ₁ w).H)
    (c₁ : X.K →+* ℂ) (c₂ : L →+* ℂ) (hc : ∀ x, c₂ (ι x) = c₁ x)
    (h₁ : (Formalism.L2.Col.formGSD (Formalism.L2.Col.roundPk X lam fun d : Formalism.L2.Col.DecoSet X.E n ∅ SG₁ => d.1.N) Λ₁).Ok)
    (h₂ : (Formalism.L2.Col.formGSD (X := ({F := X.F, E := X.E, K := L, Tau := X.Tau, emb := e} : Formalism.L2.Col.Fields))
      (Formalism.L2.Col.roundPk ({F := X.F, E := X.E, K := L, Tau := X.Tau, emb := e} : Formalism.L2.Col.Fields) lam
        fun d : Formalism.L2.Col.DecoSet X.E n ∅ SG₂ => d.1.N) Λ₂).Ok)
    (T : (Formalism.L2.Col.GSD.toCSD _ h₁).Forms → (Formalism.L2.Col.GSD.toCSD _ h₂).Forms)
    (hT : SemiSpan ι (Formalism.L2.Col.GSD.toCSD _ h₁) (Formalism.L2.Col.GSD.toCSD _ h₂) T)
    (hf : ∀ f d₁ d₂, HEq d₂ d₁ → HEq (MvPolynomial.map c₂ (((Formalism.L2.Col.GSD.res _ h₂).symm (T f)).1 d₂).1)
      (MvPolynomial.map c₁ (((Formalism.L2.Col.GSD.res _ h₁).symm f).1 d₁).1)) :
    NabSpan (Formalism.L2.Col.GSD.toCSD _ h₁) (Formalism.L2.Col.GSD.toCSD _ h₂) T := by
  subst hS
  have he' : e = fun τ => ι.comp (X.emb τ) := funext fun τ => (he τ).symm
  subst he'
  obtain ⟨H₂, l₂, rfl⟩ : ∃ (H₂ : ∀ w : ↥SG₂, Subgroup (GL (Fin n) (𝓞 X.E ⧸ w.1.asIdeal))) (l₂ : ∀ w, ↥(H₂ w) →* Lˣ),
      Λ₂ = fun w => ⟨H₂ w, l₂ w⟩ := ⟨fun w => (Λ₂ w).H, fun w => (Λ₂ w).lam, rfl⟩
  have hH' : H₂ = fun w => (Λ₁ w).H := funext fun w => hH w w.2
  subst hH'
  have key : ∀ (p : Pol X.K X.Tau n) (q : Pol L X.Tau n), HEq (MvPolynomial.map c₂ q) (MvPolynomial.map c₁ p) →
      q = MvPolynomial.map ι p := by
    intro p q h
    apply MvPolynomial.map_injective c₂ c₂.injective
    rw [eq_of_heq h, MvPolynomial.map_map, show c₂.comp ι = c₁ from RingHom.ext hc]
  have hev : ∀ (c : (Formalism.L2.Col.GSD.toCSD _ h₁).Cl) f, ((T f).1 c).1 = MvPolynomial.map ι (f.1 c).1 := by
    intro c f
    have a1 := key _ _ (hf f (Quotient.out c) (Quotient.out c) HEq.rfl)
    have b1 := nab_res_symm _ h₁ f c
    have b3 := nab_res_symm _ h₂ (T f) c
    exact (congrArg Subtype.val b3).symm.trans (a1.trans (congrArg (fun v => MvPolynomial.map ι (Subtype.val v)) b1))
  refine nabSpan_of_values ι T hT (fun c => c) (fun c => ⟨c, rfl⟩) (VV X.K lam).subtype (VV L lam).subtype hev
    (fun c => polOfVV lam (nabAtr X.emb lam (Quotient.out c : Formalism.L2.Col.DecoSet X.E n ∅ SG₂).1.N))
    (fun c x => (mem_polOfVV_iff lam _ x).symm) fun c x => ?_
  rw [← (nablaDeltaBaseChangeAt_holds X.E X.K L ι X.Tau n X.emb lam _
    (Quotient.out c : Formalism.L2.Col.DecoSet X.E n ∅ SG₂).2.lat).2.2.1]
  exact (mem_polOfVV_iff lam _ x).symm

theorem nab_glue_inv_H {E K L : Type} [Field E] [NumberField E] [Field K] [Field L] {n : ℕ}
    {SG₁ Q₁ SG₂ Q₂ : Finset (HeightOneSpectrum (𝓞 E))} (hQ₁ : Q₁ = ∅) (hQ₂ : Q₂ = ∅)
    (A₁ : Formalism.L2.Col.LevFam E K n SG₁) (B₁ : Formalism.L2.Col.LevFam E K n Q₁)
    (A₂ : Formalism.L2.Col.LevFam E L n SG₂) (B₂ : Formalism.L2.Col.LevFam E L n Q₂)
    (hA : ∀ (w : ↥SG₁) (hw : w.1 ∈ SG₂), (A₂ ⟨w.1, hw⟩).H = (A₁ w).H) :
    ∀ (w : ↥(Formalism.L2.Col.uSG SG₁ Q₁)) (hw : w.1 ∈ Formalism.L2.Col.uSG SG₂ Q₂),
      ((A₂.glue B₂).inv ⟨w.1, hw⟩).H = ((A₁.glue B₁).inv w).H := by
  intro w hw
  have h1 : w.1 ∈ SG₁ := by
    have := w.2
    simp only [Formalism.L2.Col.uSG, hQ₁, Finset.union_empty] at this
    exact this
  have h2 : w.1 ∈ SG₂ := by
    have := hw
    simp only [Formalism.L2.Col.uSG, hQ₂, Finset.union_empty] at this
    exact this
  show ((A₂.glue B₂) ⟨w.1, hw⟩).H = ((A₁.glue B₁) w).H
  rw [Formalism.L2.Col.LevFam.glue_of_mem _ _ _ h2, Formalism.L2.Col.LevFam.glue_of_mem _ _ _ h1]
  exact hA ⟨w.1, h1⟩ h2

set_option maxHeartbeats 1000000 in

theorem nab_refTuple {B₁ B₂ : Base} {f₁ : Fr B₁.toPre} {f₂ : Fr B₂.toPre} {T₁ : TwDat B₁} {T₂ : TwDat B₂}
    (w₁ : ColW B₁ f₁ T₁) (w₂ : ColW B₂ f₂ T₂) (W₁ : Set B₁.places.Pl) (W₂ : Set B₂.places.Pl)
    (hpre : B₂.toPre = B₁.toPre) (hp : HEq w₂.px w₁.px) (j₁ j₂ : ℕ) (hj : j₁ = j₂)
    (ι : B₁.LL →+* B₂.LL) (hι : ∀ x, B₂.embLL (ι x) = B₁.embLL x)
    (h₁ : (Formalism.L2.Col.mtKGSD (Pr := B₁.primes w₁.px) B₁.wts w₁.I.Ch w₁.I.sel (mu0F (X := B₁.fields) (tuOf w₁.I (usedOf w₁.I T₁ W₁))).1 j₁).Ok) (h₂ : (Formalism.L2.Col.mtKGSD (Pr := B₂.primes w₂.px) B₂.wts w₂.I.Ch w₂.I.sel (mu0F (X := B₂.fields) (tuOf w₂.I (usedOf w₂.I T₂ W₂))).1 j₂).Ok)
    (T : (Formalism.L2.Col.GSD.toCSD _ h₁).Forms → (Formalism.L2.Col.GSD.toCSD _ h₂).Forms)
    (hT : SemiSpan (K := B₁.fields.K) (K' := B₂.fields.K) ι (Formalism.L2.Col.GSD.toCSD _ h₁) (Formalism.L2.Col.GSD.toCSD _ h₂) T)
    (hf : ∀ f d₁ d₂, HEq d₂ d₁ → HEq (MvPolynomial.map (B₂.embLL : B₂.fields.K →+* ℂ) (((Formalism.L2.Col.GSD.res _ h₂).symm (T f)).1 d₂).1)
      (MvPolynomial.map (B₁.embLL : B₁.fields.K →+* ℂ) (((Formalism.L2.Col.GSD.res _ h₁).symm f).1 d₁).1)) :
    NabSpan (Formalism.L2.Col.GSD.toCSD _ h₁) (Formalism.L2.Col.GSD.toCSD _ h₂) T := by
  subst hj
  cases B₁ with | mk P₁ =>
  cases B₂ with | mk P₂ =>
  dsimp only at hpre
  subst hpre
  have hpx : w₂.px = w₁.px := eq_of_heq hp
  refine nab_round_bc (baseOfColW w₁).fields ι (baseOfColW w₂).tauLL ?_ ((baseOfColW w₁).wts.lamV j₁) ?_
    (Formalism.L2.Col.mtTyKK w₁.I.Ch w₁.I.sel (mu0F (X := (baseOfColW w₁).fields) (tuOf w₁.I (usedOf w₁.I T₁ W₁))).1 j₁).inv
    (Formalism.L2.Col.mtTyKK w₂.I.Ch w₂.I.sel (mu0F (X := (baseOfColW w₂).fields) (tuOf w₂.I (usedOf w₂.I T₂ W₂))).1 j₁).inv
    ?_ (baseOfColW w₁).embLL
    (baseOfColW w₂).embLL hι h₁ h₂ T hT hf
  · intro τ
    ext x
    apply (baseOfColW w₂).embLL.injective
    have h1 := congrArg (fun g => g x) (Base.fields_embC (baseOfColW w₁) τ)
    have h2 := congrArg (fun g => g x) (Base.fields_embC (baseOfColW w₂) τ)
    simp only [Formalism.L2.Col.Fields.embC, RingHom.comp_apply] at h1 h2
    rw [RingHom.comp_apply, hι]
    exact h1.trans h2.symm
  · refine (rowLevelPrimes_colTuples_eq_vGs w₂ W₂).trans (Eq.trans ?_ (rowLevelPrimes_colTuples_eq_vGs w₁ W₁).symm)
    rw [hpx]
    rfl
  · exact nab_glue_inv_H (twistRamifiedPrimes_empty_colTuples w₁ W₁) (twistRamifiedPrimes_empty_colTuples w₂ W₂) _ _ _ _ fun w hw => rfl

set_option maxHeartbeats 1000000 in

theorem nab_ext : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (L : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms →+ ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.Forms), (∀ (a : (w.st Z).toD7.what₂.LL) (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms), L (a • f) = φ a • L f) → (∀ (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms) (d : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D) (d' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D), HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 hX' ((j' : ℕ) + 1))).symm (L f) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).V) d').1) (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 hX ((j : ℕ) + 1))).symm f : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).V) d).1)) → ∀ f' : ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.Forms, (∀ c, (f' : ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.Cl → ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.V) c ∈ ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.Nab c) ↔ f' ∈ Submodule.span (𝓞 (w'.st Z').toD7.what₂.LL) (L '' {f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms | ∀ c, (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Cl → ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.V) c ∈ ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Nab c})) := by
  intro h1 h2 h3 h4 h5 h6 h7
  refine StepW.trans (GlobalTheory.T.liftForms_referenceTuple_basis_extended h1 h2 h3 h4 h5 h6 h7) (StepW.of_all ?_)
  intro K B' f' T' w' _ _ H B f T w hE hf hP hpx Z hX Wt z g1 g2 g3 g4 Z' hX' g5 g6 g7 z' g8 g9 j j' hj φ hφ L hL hC
  beta_reduce at H
  have Ha := (H B f T w hE hf hP hpx Z hX Wt z g1 g2 g3 g4 Z' hX' g5 g6 g7 z' g8 g9 j j' hj φ hφ L hL hC).2
  have Hb := semiSpan_of φ _ _ L hL Ha
  clear H Ha
  show NabSpan ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S (fun x => L x)
  exact nab_refTuple w w' Wt {v | B'.places.resChar v ∈ T'.pl} hE.1 hpx ((j : ℕ) + 1) ((j' : ℕ) + 1) (by rw [hj]) φ hφ
    (Formalism.L2.Col.mtKOk (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 hX ((j : ℕ) + 1))
    (Formalism.L2.Col.mtKOk (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 hX' ((j' : ℕ) + 1))
    (fun x => L x) Hb hC

end GlobalTheory.Mem.R3.DefLatBC
