import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.UnipotentFundamentalDomain
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.NRatBridgeHolds

noncomputable section

open MeasureTheory NumberField Set
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets
open scoped TensorProduct

namespace MassDataMassesW

section Level

variable {D : D7} (X : HidaSetting D)

theorem kset_mul {x y : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) (hy : y ∈ X.B.I.Kset) : x * y ∈ X.B.I.Kset :=
  (Formalism.UG.stabGL X.B.I.Lf).mul_mem hx hy

theorem kset_inv {x : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) : x⁻¹ ∈ X.B.I.Kset :=
  (Formalism.UG.stabGL X.B.I.Lf).inv_mem hx

theorem gf_eq_one (hb : AdBridgeIso X.B.I) (δ : X.B.I.GA) (hδ : δ ∈ X.B.I.GFset) (h1 : δ.1 = 1) : δ = 1 := by
  obtain ⟨g, -, hinf, hfin⟩ := hδ
  obtain v := (inferInstance : Nonempty (InfinitePlace X.B.I.F)).some
  have hdet : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v)
  have hP' : X.B.I.P v * (X.B.I.P v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hv := hinf v
  rw [h1] at hv
  have hone : Formalism.MainNotions.S.uMat ((1 : X.B.I.Ginf) v) = 1 := rfl
  rw [hone] at hv
  have hM : (g : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) = 1 := by
    calc (g : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v)
        = X.B.I.P v * ((X.B.I.P v)⁻¹ * (g : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) *
            X.B.I.P v) * (X.B.I.P v)⁻¹ := by
          simp only [Matrix.mul_assoc, hP', Matrix.mul_one]
          rw [← Matrix.mul_assoc, hP', Matrix.one_mul]
      _ = 1 := by rw [← hv, Matrix.mul_one, hP']
  have hg : (g : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) = 1 := by
    ext i j
    have := congrFun (congrFun hM i) j
    rw [Matrix.map_apply, Matrix.one_apply] at this
    rw [Matrix.one_apply]
    apply (X.B.I.φ v).injective
    rw [this]
    split_ifs <;> simp
  refine Prod.ext h1 ?_
  apply Subtype.ext
  apply Units.ext
  show X.B.I.fmat δ.2 = 1
  rw [hfin, hg]
  ext i j
  simp only [Matrix.map_apply, Matrix.one_apply]
  split_ifs <;> simp

end Level

theorem fundamental_domain_of_compact_open (hKo : KCompactOpen) (hRB : NRatBridge) : UnipotentFundamentalDomain := by
  intro hSA hNL hBK hS D X hb hK u FdN hTie hL hF
  have : BorelSpace (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  have : BorelSpace (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  have : BorelSpace (HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩

  have core : ∀ γ : HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J,
      γ ∈ (HFinIn (AF X.B.I.F) X.B.I.cm.sig X.B.I.J : Subgroup (HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J)) →
      γ ∈ Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) →
      ∀ (n : HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J) (s s' : X.B.I.Ginf), s ∈ FdN → s' ∈ FdN →
      (splitA X.B.I.cm.sig X.B.I.J n).1 = X.toInf hb s → (splitA X.B.I.cm.sig X.B.I.J n).2 ∈ KX X →
      (splitA X.B.I.cm.sig X.B.I.J (γ * n)).1 = X.toInf hb s' →
      (splitA X.B.I.cm.sig X.B.I.J (γ * n)).2 ∈ KX X → γ = 1 := by
    intro γ hγF hγN n s s' hs hs' h1 h2 h1' h2'
    set δ := (toHA X.B.I hb).symm γ with hδdef
    have hδ : toHA X.B.I hb δ = γ := (toHA X.B.I hb).apply_symm_apply γ
    obtain ⟨hGF, hinf, hfin⟩ := (hRB X hb u δ).1 ⟨by rw [hδ]; exact hγF, by rw [hδ]; exact hγN⟩
    have hsp : splitA X.B.I.cm.sig X.B.I.J γ = (X.toInf hb δ.1, finHA X hb δ.2) := by
      rw [← hδ]
      exact split_toHA X hb hS δ
    have hmul : splitA X.B.I.cm.sig X.B.I.J (γ * n) =
        splitA X.B.I.cm.sig X.B.I.J γ * splitA X.B.I.cm.sig X.B.I.J n := map_mul _ _ _
    rw [hsp] at hmul
    have hfinK : finHA X hb δ.2 ∈ KX X := by
      have e2 : finHA X hb δ.2 = (splitA X.B.I.cm.sig X.B.I.J (γ * n)).2 *
          ((splitA X.B.I.cm.sig X.B.I.J n).2)⁻¹ := by
        rw [hmul]
        simp
      rw [e2]
      exact (KX X).mul_mem h2' ((KX X).inv_mem h2)
    have hKs : δ.2 ∈ X.B.I.Kset := (hBK X hb δ.2).2 hfinK
    have hK2 := hNL X u δ.2 hfin hKs
    have hNO : δ.1 ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u := ⟨δ, hGF, rfl, hinf, hfin, hK2⟩
    have hreal : X.toInf hb s' = X.toInf hb (δ.1 * s) := by
      rw [toInf_mul, ← h1', hmul, ← h1]
      rfl
    have hs'' : s' = δ.1 * s := toInf_injective X hb hS hreal
    have hδ1 : δ.1 = 1 := hF.2.2 s hs δ.1 hNO (hs'' ▸ hs')
    have hδ1' : δ = 1 := gf_eq_one X hb δ hGF hδ1
    rw [← hδ, hδ1', map_one]

  obtain ⟨e, he⟩ := hS X.B.I.cm.sig X.B.I.J
  have hc : Continuous (splitA X.B.I.cm.sig X.B.I.J) := by rw [← he]; exact e.continuous_toFun
  have hm : Measurable (splitA X.B.I.cm.sig X.B.I.J) :=
    (continuous_fst.comp hc).measurable.prodMk (continuous_snd.comp hc).measurable
  have hTm : MeasurableSet (X.toInf hb '' FdN) := measurableSet_image_toInf X hb hS hF.1
  have hKm : MeasurableSet (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) := (hKo X).2.measurableSet
  have hRm : MeasurableSet ((X.toInf hb '' FdN) ×ˢ (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))) :=
    hTm.prod hKm
  have hFd : FdA X hb u FdN = Subtype.val ⁻¹' (splitA X.B.I.cm.sig X.B.I.J ⁻¹'
      ((X.toInf hb '' FdN) ×ˢ (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)))) := by
    ext n
    simp only [FdA, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_prod, Set.mem_image]
    constructor
    · rintro ⟨s, hs, h1, h2⟩
      exact ⟨⟨s, hs, h1.symm⟩, h2⟩
    · rintro ⟨⟨s, hs, h1⟩, h2⟩
      exact ⟨s, hs, h1.symm, h2⟩
  have hmeas : MeasurableSet (FdA X hb u FdN) := by
    rw [hFd]
    exact measurable_subtype_coe (hm hRm)

  have cover : ∀ n : ↥(Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)),
      ∃ g : ratOf (K := Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)), g • n ∈ FdA X hb u FdN := by
    intro n
    obtain ⟨γ, hγF, hγN, hγK⟩ := hSA X u n n.2
    obtain ⟨t, ht⟩ := toInf_surjective X hb hS (splitA X.B.I.cm.sig X.B.I.J (γ * n)).1
    obtain ⟨s, hsNO, hst⟩ := hF.2.1 t
    obtain ⟨δ, hGF, hδs, hinf, hfin, hK2⟩ := hsNO
    obtain ⟨hγ'F, hγ'N⟩ := (hRB X hb u δ).2 ⟨hGF, hinf, hfin⟩
    have hKs : δ.2 ∈ X.B.I.Kset := by
      have hx := X.xu_K u
      have h2 := hL.2.1 _ hK2
      have : δ.2 = X.xu u * ((X.xu u)⁻¹ * δ.2 * X.xu u) * (X.xu u)⁻¹ := by group
      rw [this]
      exact kset_mul X (kset_mul X hx h2) (kset_inv X hx)
    have hfinK : finHA X hb δ.2 ∈ KX X := (hBK X hb δ.2).1 hKs
    refine ⟨⟨⟨toHA X.B.I hb δ * γ, (Nsub _ _ _ _).mul_mem hγ'N hγN⟩,
      Subgroup.mem_comap.2 (Subgroup.mul_mem _ hγ'F hγF)⟩, ?_⟩
    have hsp : splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb δ * γ * (n : HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J)) =
        (X.toInf hb δ.1, finHA X hb δ.2) * splitA X.B.I.cm.sig X.B.I.J (γ * n) := by
      rw [mul_assoc, map_mul, split_toHA X hb hS δ]
    refine ⟨s * t, hst, ?_, ?_⟩
    · show (splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb δ * γ * (n : HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J))).1 = _
      rw [hsp, toInf_mul, Prod.fst_mul, ← ht, hδs]
    · show (splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb δ * γ * (n : HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J))).2 ∈ _
      rw [hsp, Prod.snd_mul]
      exact (KX X).mul_mem hfinK hγK
  refine IsFundamentalDomain.mk' hmeas.nullMeasurableSet fun n => ?_
  obtain ⟨g0, hg0⟩ := cover n
  refine ⟨g0, hg0, fun g hg => ?_⟩

  obtain ⟨s, hs, h1, h2⟩ := hg0
  obtain ⟨s', hs', h1', h2'⟩ := hg
  have hγF : (((g * g0⁻¹ : ratOf (K := Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) :
      ↥(Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) : HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J) ∈
      (HFinIn (AF X.B.I.F) X.B.I.cm.sig X.B.I.J : Subgroup (HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J)) :=
    Subgroup.mem_comap.1 (g * g0⁻¹).2
  have hγN := ((g * g0⁻¹ : ratOf (K := Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) :
      ↥(Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))).2
  have hgn0 : ((g * g0⁻¹ : ratOf (K := Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) :
      ↥(Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) * (g0 • n) = g • n := by
    rw [Subgroup.smul_def, Subgroup.smul_def, smul_eq_mul, smul_eq_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      mul_assoc, inv_mul_cancel_left]
  have hgn : (((g * g0⁻¹ : ratOf (K := Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) :
      ↥(Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) : HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J) *
      ((g0 • n : ↥(Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) : HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J) =
      ((g • n : ↥(Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) : HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J) :=
    congrArg Subtype.val hgn0
  have h1g : (g * g0⁻¹ : ratOf (K := Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) = 1 := by
    have := core _ hγF hγN _ s s' hs hs' h1 h2 (by rw [hgn]; exact h1') (by rw [hgn]; exact h2')
    exact Subtype.ext (Subtype.ext this)
  exact mul_inv_eq_one.1 h1g

end MassDataMassesW
