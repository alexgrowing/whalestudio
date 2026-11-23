import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ToTermAct

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.PackageTie2 Formalism.L2.SG.NormCut Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf.unitaryCongruence

namespace Formalism.L2.SG.Pf.KernelOfEmbedding

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Ker

variable {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}

theorem mem_orth_iff {U : Submodule D.host.E (VS D).V} {x : (VS D).V} : x ∈ orth (VS D) U ↔ x ∈ perpS (VS D) U := by
  unfold orth perpS
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  first
    | exact Iff.rfl
    | (constructor <;> intro h <;> exact h)

theorem act_of_dec (hN : Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u' Y.hK) (q : {Λ // Λ ∈ Y.what₂ u'})
    {s s' : TT Y u u'} (hq : s.lam' = q.1) (hl : s.lam = s'.lam) (hl' : s.lam' = s'.lam')
    {n ν c : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ NLam s.lam (lf D (X.Fu u)))
    (hν : ν ∈ NLam s.lam' (lf D (X.Fu u'))) (hc : c ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hg : Formalism.HermitianLatticesTheory.gmap c s.lam' = s.lam') (hfix : ∀ a, c ((X.Fu u').fvec a) = (X.Fu u').fvec a)
    (he : s'.lin = n * s.lin * ν * c) :
    ∃ γ : Formalism.L2.SG.Pf.Act.GamL (Y.cs u') q, s' = act Y q γ s ∧
      ∀ y ∈ perpS (VS D) (X.Fu u').X, c y - (Formalism.L2.SG.Pf.Act.isoG γ.1)⁻¹ y ∈ (X.Fu u').X := by
  obtain ⟨Λ', hΛ'⟩ := q
  simp only at hq
  subst hq
  have hst := Formalism.L2.SG.Pf.FibreCounting.stabF_of_fix (X.Fu u') hc hfix
  obtain ⟨g, hgq⟩ := (Formalism.L2.SG.Pf.Act.gamL_autLz_bij (Y.cs u') Y.hK hN ⟨s.lam', hΛ'⟩).2
    ⟨Formalism.L2.SG.Pf.Act.indW c hst, Formalism.L2.SG.Pf.Act.indW_mem s.lam' c hst hg⟩
  have hW : (Formalism.L2.SG.Pf.Act.indW (Formalism.L2.SG.Pf.Act.isoG g.1) (Formalism.L2.SG.Pf.Act.isoG_stab g.1) :
      Formalism.MainNotions.S.WbQ D (X.Fu u') → Formalism.MainNotions.S.WbQ D (X.Fu u')) = Formalism.L2.SG.Pf.Act.indW c hst :=
    congrArg Subtype.val hgq
  have hq : ∀ y ∈ perpS (VS D) (X.Fu u').X, c y - Formalism.L2.SG.Pf.Act.isoG g.1 y ∈ (X.Fu u').X := by
    intro y hy
    have e := congrFun hW.symm (Submodule.Quotient.mk ⟨y, hy⟩)
    rw [Formalism.L2.SG.Pf.Act.indW_mk, Formalism.L2.SG.Pf.Act.indW_mk, Submodule.Quotient.eq] at e
    simpa using e
  have hfixg : ∀ a, Formalism.L2.SG.Pf.Act.isoG g.1 ((X.Fu u').fvec a) = (X.Fu u').fvec a := by
    intro a
    refine Fin.lastCases ?_ (fun i => ?_) a
    · simp only [FlagG.fvec, Fin.snoc_last]
      rw [X.flagZVector u']
      exact Formalism.L2.SG.Pf.Act.isoG_fix g.1 _ (Or.inr rfl)
    · simp only [FlagG.fvec, Fin.snoc_castSucc]
      rw [X.Fu_e u']
      exact Formalism.L2.SG.Pf.Act.isoG_e g.1 i
  have hA : IsAutLam (VS D) s.lam' c := ⟨hc, hg⟩
  have hA' : IsAutLam (VS D) s.lam' (Formalism.L2.SG.Pf.Act.isoG g.1) :=
    ⟨(Formalism.L2.SG.Pf.Act.isoG_stab g.1).1, Formalism.L2.SG.Pf.Act.isoG_lat (Y.cs u') ⟨s.lam', hΛ'⟩ g⟩
  have hm := Formalism.L2.SG.Pf.FibreCounting.nlam_of_sub (X.Fu u') hA hA' hfix hfixg hq
  have hkinv : colD ((Y.cs u').h ((Y.cs u').base s.lam')) (iotaF X u' g.1⁻¹ * (Y.cs u').h ((Y.cs u').base s.lam'))
      ∈ X.B.I.Kset := by
    rw [← Formalism.L2.SG.Pf.Act.aK_eq]
    have h1 := K_inv X.B.I (kB_mem (Y := Y) ⟨s.lam', hΛ'⟩ g)
    unfold Formalism.L2.SG.Pf.SatGramActL.kB at h1
    rw [map_inv]
    convert h1 using 1
    push_cast
    group
  let γ : Formalism.L2.SG.Pf.Act.GamL (Y.cs u') ⟨s.lam', hΛ'⟩ := ⟨g.1⁻¹, hkinv⟩
  have hxg := (isoG_lift Y ⟨s.lam', hΛ'⟩ g).1
  have hxi : RatLink X (γ.1 : X.B.I.GA) (Formalism.L2.SG.Pf.Act.isoG g.1)⁻¹ := by
    have := Formalism.L2.SG.Pf.ratLink_inv X hxg
    simpa [γ] using this
  have hiso : Formalism.L2.SG.Pf.Act.isoG γ.1 = (Formalism.L2.SG.Pf.Act.isoG g.1)⁻¹ := (eq_isoG hxi).symm
  refine ⟨γ, ?_, fun y hy => by rw [hiso, inv_inv]; exact hq y hy⟩
  have hβt : Formalism.L2.SG.Pf.Act.isoG γ.1 ∈ Formalism.L2.SG.Saturated.AutF s.lam' (lf D (X.Fu u')) :=
    (isoG_lift Y ⟨s.lam', hΛ'⟩ γ).2
  have hcls := Formalism.L2.SG.Pf.SatGramActR.tmap_cls (γ.1 : X.B.I.GA) (Formalism.L2.SG.Pf.Act.isoG γ.1)
    Formalism.L2.SG.Pf.SatGramActR.autFConjN_holds (isoG_lift Y ⟨s.lam', hΛ'⟩ γ).1 s hβt
  set G := Formalism.L2.SG.Pf.Act.isoG g.1 with hG
  have hGA : G⁻¹ ∈ Formalism.L2.SG.Saturated.AutF s.lam' (lf D (X.Fu u')) := by rw [← hiso]; exact hβt
  have hν2 : G⁻¹ * ν * G⁻¹⁻¹ ∈ NLam s.lam' (lf D (X.Fu u')) :=
    Formalism.L2.SG.Pf.SatGramActL.nlam_conj hGA hν
  have hν3 : (G⁻¹ * ν * G⁻¹⁻¹) * (c⁻¹ * G)⁻¹ ∈ NLam s.lam' (lf D (X.Fu u')) :=
    Formalism.L2.SG.Pf.nlamPf_mul hν2 (Formalism.L2.SG.Pf.nlamPf_inv hm)
  rcases s' with ⟨k, hk, k', hk', q'⟩
  simp only at hl hl' he
  subst hl hl'
  show (⟨s.lam, hk, s.lam', hk', q'⟩ : TT Y u u') =
    ⟨s.lam, s.mem, s.lam', s.mem', (Formalism.L2.SG.Pf.SatGramActR.tmap (γ.1 : X.B.I.GA) (Formalism.L2.SG.Pf.Act.isoG γ.1)
      Formalism.L2.SG.Pf.SatGramActR.autFConjN_holds (isoG_lift Y ⟨s.lam', hΛ'⟩ γ).1 s).cls⟩
  rw [hcls]
  congr 1
  rw [← Quot.out_eq q']
  refine (Quot.sound ⟨n, hn, (G⁻¹ * ν * G⁻¹⁻¹) * (c⁻¹ * G)⁻¹, hν3, ?_⟩).symm
  show GTerm.lin (⟨s.lam, hk, s.lam', hk', q'⟩ : TT Y u u') =
    n * (GTerm.lin s * (Formalism.L2.SG.Pf.Act.isoG γ.1)⁻¹) * ((G⁻¹ * ν * G⁻¹⁻¹) * (c⁻¹ * G)⁻¹)
  rw [he, hiso]
  group

theorem nlam_frame (s : TT Y u u') {m : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hm : m ∈ NLam s.lam s.frame) :
    s.lin⁻¹ * m * s.lin ∈ NLam s.lam' (lf D (X.Fu u')) := by
  have hm' : m ∈ NLam (Formalism.HermitianLatticesTheory.gmap s.lin s.lam')
      (Formalism.L2.SG.Saturated.mapL s.lin (Formalism.L2.SG.Pf.FibreCounting.lin_isom s) (lf D (X.Fu u'))) := by
    rw [Formalism.L2.SG.Pf.FibreCounting.lin_gmap s, ← Formalism.L2.SG.Pf.FibreCounting.frame_eq s]; exact hm
  exact (Formalism.L2.SG.Pf.mem_NLam_map _ (Formalism.L2.SG.Pf.FibreCounting.lin_isom s) s.lam' (lf D (X.Fu u')) m).1 hm'

theorem fix_of_ez {c : (VS D).V ≃ₗ[D.host.E] (VS D).V} (he : ∀ a, c ((X.Fu u').e a) = (X.Fu u').e a)
    (hz : c (X.Fu u').z = (X.Fu u').z) : ∀ a, c ((X.Fu u').fvec a) = (X.Fu u').fvec a := by
  intro a
  unfold Formalism.MainNotions.S.FlagG.fvec
  refine Fin.lastCases ?_ (fun i => ?_) a
  · simp only [Fin.snoc_last]
    exact hz
  · simp only [Fin.snoc_castSucc]
    exact he i

theorem iotaKer_core (hN : Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u' Y.hK) (hIR : Formalism.L2.SG.Pf.SatGramRep.IotaRepC)
    (s₁ s₂ t₁ t₂ : TT Y u u') (n₁ n₂ m₁ m₂ c₁ c₂ : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hs2 : s₂.lam = s₁.lam) (ht1 : t₁.lam = s₁.lam) (ht2 : t₂.lam = s₁.lam)
    (hs2' : s₂.lam' = s₁.lam') (ht1' : t₁.lam' = s₁.lam') (ht2' : t₂.lam' = s₁.lam')
    (hn₁ : n₁ ∈ NLam s₁.lam (lf D (X.Fu u))) (hn₂ : n₂ ∈ NLam s₁.lam (lf D (X.Fu u)))
    (hm₁ : m₁ ∈ NLam s₁.lam s₁.frame) (hm₂ : m₂ ∈ NLam s₁.lam s₂.frame)
    (hc₁ : c₁ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hc₂ : c₂ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hg₁ : Formalism.HermitianLatticesTheory.gmap c₁ s₁.lam' = s₁.lam') (hg₂ : Formalism.HermitianLatticesTheory.gmap c₂ s₁.lam' = s₁.lam')
    (he₁ : ∀ a, c₁ ((X.Fu u').e a) = (X.Fu u').e a) (he₂ : ∀ a, c₂ ((X.Fu u').e a) = (X.Fu u').e a)
    (hz₁ : c₁ (X.Fu u').z = (X.Fu u').z) (hz₂ : c₂ (X.Fu u').z = (X.Fu u').z)
    (hl₁ : t₁.lin = n₁ * m₁ * s₁.lin * c₁) (hl₂ : t₂.lin = n₂ * m₂ * s₂.lin * c₂)
    (hι : iotaOf Y.TR (Y.cs u) (Y.cs u') s₁ = iotaOf Y.TR (Y.cs u) (Y.cs u') s₂)
    (hι' : iotaOf Y.TR (Y.cs u) (Y.cs u') t₁ = iotaOf Y.TR (Y.cs u) (Y.cs u') t₂) :
    ∀ x ∈ orth (VS D) (X.Fu u').X, (c₂ * c₁⁻¹) x - x ∈ (X.Fu u').X := by
  let q : {Λ // Λ ∈ Y.what₂ u'} := ⟨s₁.lam', s₁.mem'⟩
  have hfix₁ := fix_of_ez he₁ hz₁
  have hfix₂ := fix_of_ez he₂ hz₂
  have hμ₁ := nlam_frame s₁ hm₁
  have hm₂' : m₂ ∈ NLam s₂.lam s₂.frame := by rw [hs2]; exact hm₂
  have hμ₂ := nlam_frame s₂ hm₂'
  have e₁ : t₁.lin = n₁ * s₁.lin * (s₁.lin⁻¹ * m₁ * s₁.lin) * c₁ := by rw [hl₁]; group
  have e₂ : t₂.lin = n₂ * s₂.lin * (s₂.lin⁻¹ * m₂ * s₂.lin) * c₂ := by rw [hl₂]; group
  have hn₂' : n₂ ∈ NLam s₂.lam (lf D (X.Fu u)) := by rw [hs2]; exact hn₂
  have hg₂' : Formalism.HermitianLatticesTheory.gmap c₂ s₂.lam' = s₂.lam' := by rw [hs2']; exact hg₂
  obtain ⟨γ₁, hγ₁, hq₁⟩ := act_of_dec hN q rfl ht1.symm ht1'.symm hn₁ hμ₁ hc₁ hg₁ hfix₁ e₁
  obtain ⟨γ₂, hγ₂, hq₂⟩ := act_of_dec hN q hs2' (hs2.trans ht2.symm) (hs2'.trans ht2'.symm) hn₂' hμ₂ hc₂ hg₂'
    hfix₂ e₂
  have i₁ := iota_act hIR q γ₁ s₁ rfl
  have i₂ := iota_act hIR q γ₂ s₂ hs2'
  rw [← hγ₁] at i₁
  rw [← hγ₂] at i₂
  rw [i₁, i₂, hι] at hι'
  have hlev : levi Y.TR (Formalism.L2.SG.Pf.SatGramActL.kB (Y.cs u') q.1 γ₁.1) =
      levi Y.TR (Formalism.L2.SG.Pf.SatGramActL.kB (Y.cs u') q.1 γ₂.1) := inv_injective (mul_left_cancel hι')
  have hγ : γ₁ = γ₂ := by
    apply (Formalism.L2.SG.Pf.Act.gamL_levi_bij (Y.cs u') Y.TR Y.hK hN q).1
    apply Subtype.ext
    show levi Y.TR (colD ((Y.cs u').h ((Y.cs u').base q.1)) (iotaF X u' γ₁.1 * (Y.cs u').h ((Y.cs u').base q.1))) =
      levi Y.TR (colD ((Y.cs u').h ((Y.cs u').base q.1)) (iotaF X u' γ₂.1 * (Y.cs u').h ((Y.cs u').base q.1)))
    rw [← Formalism.L2.SG.Pf.Act.aK_eq, ← Formalism.L2.SG.Pf.Act.aK_eq]
    exact hlev
  subst hγ
  intro x hx
  rw [mem_orth_iff] at hx
  have hinv := Formalism.L2.SG.Pf.FibreCounting.inv_fix (X.Fu u') hfix₁
  have hc₁i : c₁⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := Subgroup.inv_mem _ hc₁
  have hy : c₁⁻¹ x ∈ perpS (VS D) (X.Fu u').X := Formalism.L2.SG.Pf.FibreCounting.perp_maps (X.Fu u') hc₁i hinv x hx
  have d₁ := hq₁ _ hy
  have d₂ := hq₂ _ hy
  have e3 : (c₂ * c₁⁻¹) x - x = (c₂ (c₁⁻¹ x) - (Formalism.L2.SG.Pf.Act.isoG γ₁.1)⁻¹ (c₁⁻¹ x)) -
      (c₁ (c₁⁻¹ x) - (Formalism.L2.SG.Pf.Act.isoG γ₁.1)⁻¹ (c₁⁻¹ x)) := by
    simp only [LinearEquiv.mul_apply]
    have : c₁ (c₁⁻¹ x) = x := by
      show c₁ (c₁.symm x) = x
      exact c₁.apply_symm_apply x
    rw [this]; abel
  rw [e3]
  exact sub_mem d₂ d₁

end Ker

end Formalism.L2.SG.Pf.KernelOfEmbedding
