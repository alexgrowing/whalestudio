import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedUnip
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundamentalDomainClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentFundamentalDomainExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnitaryLeviLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingInjectiveStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviConjHaar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem conj_mem_unip {d d₁ : ℕ} {W : Spc F E d} {H : Plane E d d₁} {k : UA σ W.J}
    {M : Matrix (Fin d₁) (Fin d₁) (AE F E)} (hx : mat k *ᵥ incV F H.x = incV F H.x)
    (hι : mat k * incM F H.ι = incM F H.ι * M) {u : UA σ W.J} (hu : u ∈ unip σ W H) :
    k⁻¹ * u * k ∈ unip σ W H := by
  have hinv : mat k⁻¹ * mat k = 1 := GlobalTheory.ThK.UnipClosed.mat_inv_mul k
  have hx' : mat k⁻¹ *ᵥ incV F H.x = incV F H.x := by
    conv_lhs => rw [← hx]
    rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have hk : ∀ z, mat k *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ (M *ᵥ z) := fun z => by
    rw [Matrix.mulVec_mulVec, hι, ← Matrix.mulVec_mulVec]
  have hk' : ∀ z, mat k⁻¹ *ᵥ (incM F H.ι *ᵥ (M *ᵥ z)) = incM F H.ι *ᵥ z := fun z => by
    rw [← hk, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have hle : unip σ W H ≤ (unip σ W H).comap (MulAut.conj k⁻¹).toMonoidHom := by
    refine (Subgroup.closure_le _).2 fun s hs => ?_
    obtain ⟨hs1, hs2⟩ := hs
    simp only [Subgroup.coe_comap, Set.mem_preimage, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    refine Subgroup.subset_closure ⟨?_, fun z => ?_⟩
    · rw [GlobalTheory.ThK.UnipClosed.mat_mul, GlobalTheory.ThK.UnipClosed.mat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        hx, hs1, hx']
    · obtain ⟨c, hc⟩ := hs2 (M *ᵥ z)
      refine ⟨c, ?_⟩
      rw [GlobalTheory.ThK.UnipClosed.mat_mul, GlobalTheory.ThK.UnipClosed.mat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        hk, hc, Matrix.mulVec_add, Matrix.mulVec_smul, hk', hx']
  simpa [MulAut.conj_apply] using hle hu

end GlobalTheory.LeviConjHaar

open GlobalTheory.LeviConjHaar in

theorem GlobalTheory.LeviConjHaar.lintegral_conj_levi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → B.IsGood σ → G.IsGood B → G₁.IsGood B →
    ∀ m : (AE F E)ˣ → UA σ G₁.V.J → UA σ G.V.J, (∀ l g₀, IsLevi H l g₀ (m l g₀)) →
    ∀ μN : Measure (unip σ G.V H), μN.IsHaarMeasure →
    ∀ γ ∈ ratU σ G₁.V.J, ∀ f : UA σ G.V.J → ENNReal, Measurable f →
      ∫⁻ n, f (n.1 * m 1 γ) ∂μN = ∫⁻ n, f (m 1 γ * n.1) ∂μN := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hC hB hG hG₁ m hm μN hμ γ hγ f _
  obtain ⟨h, hrat, hL⟩ := GlobalTheory.T.rational_unitary_levi_lift F E σ B b a' G G₁ H H' hC hB hG hG₁ γ hγ
  have heq : m 1 γ = h := GlobalTheory.T.levi_lift_unique F E σ B b a' G G₁ H H' hC hB hG hG₁ 1 γ (m 1 γ) h (hm 1 γ) hL
  set g := m 1 γ with hgdef
  have hg : IsLevi H 1 γ g := hm 1 γ
  have hratg : g ∈ ratU σ G.V.J := heq ▸ hrat
  have hx : mat g *ᵥ incV F H.x = incV F H.x := by rw [hg.1]; simp
  have hinvg : mat g⁻¹ * mat g = 1 := GlobalTheory.ThK.UnipClosed.mat_inv_mul g
  have hx' : mat g⁻¹ *ᵥ incV F H.x = incV F H.x := by
    conv_lhs => rw [← hx]
    rw [Matrix.mulVec_mulVec, hinvg, Matrix.one_mulVec]
  have hγγ : mat γ * mat γ⁻¹ = 1 := by
    rw [← GlobalTheory.ThK.UnipClosed.mat_mul, mul_inv_cancel, GlobalTheory.ThK.UnipClosed.mat_one]
  have hι' : mat g⁻¹ * incM F H.ι = incM F H.ι * mat γ⁻¹ := by
    calc mat g⁻¹ * incM F H.ι = mat g⁻¹ * (incM F H.ι * (mat γ * mat γ⁻¹)) := by rw [hγγ, Matrix.mul_one]
      _ = (mat g⁻¹ * mat g) * incM F H.ι * mat γ⁻¹ := by rw [Matrix.mul_assoc (mat g⁻¹), hg.2.2]; simp only [Matrix.mul_assoc]
      _ = incM F H.ι * mat γ⁻¹ := by rw [hinvg, Matrix.one_mul]
  have hA : ∀ u ∈ unip σ G.V H, g⁻¹ * u * g ∈ unip σ G.V H := fun u hu => conj_mem_unip hx hg.2.2 hu
  have hB' : ∀ u ∈ unip σ G.V H, g * u * g⁻¹ ∈ unip σ G.V H := fun u hu => by
    simpa using conj_mem_unip hx' hι' hu
  let ce : unip σ G.V H ≃* unip σ G.V H :=
    { toFun := fun u => ⟨g⁻¹ * u.1 * g, hA _ u.2⟩
      invFun := fun u => ⟨g * u.1 * g⁻¹, hB' _ u.2⟩
      left_inv := fun u => Subtype.ext (by simp [mul_assoc])
      right_inv := fun u => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun u v => Subtype.ext (by simp [mul_assoc]) }
  have hce : ∀ u, (ce u).1 = g⁻¹ * u.1 * g := fun u => rfl
  have hces : ∀ u, (ce.symm u).1 = g * u.1 * g⁻¹ := fun u => rfl
  obtain ⟨hTG, hLC, hSC, hT2⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ (b + 2) G.V.J
  haveI := hTG
  haveI := hLC
  haveI := hSC
  haveI := hT2
  haveI : BorelSpace (UA σ G.V.J) := ⟨rfl⟩
  have hcl := GlobalTheory.ThK.UnipClosed.isClosed_unip F E σ _ _ G.V H
  haveI : LocallyCompactSpace (unip σ G.V H) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (unip σ G.V H) :=
    hcl.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  have hc1 : Continuous ce :=
    Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
  have hc2 : Continuous ce.symm :=
    Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
  let tt : unip σ G.V H ≃ₜ unip σ G.V H := ⟨ce.toEquiv, hc1, hc2⟩
  let me := tt.toMeasurableEquiv
  have hme : ∀ u, me u = ce u := fun u => rfl
  have hp : MeasurePreserving me μN (μN.map me) := ⟨me.measurable, rfl⟩
  haveI hHaar : (μN.map me).IsHaarMeasure := MulEquiv.isHaarMeasure_map μN ce hc1 hc2
  have hps : MeasurePreserving me.symm (μN.map me) μN := hp.symm

  have hsc := MeasureTheory.Measure.isMulLeftInvariant_eq_smul (μN.map me) μN
  set s := MeasureTheory.Measure.haarScalarFactor (μN.map me) μN with hsdef

  let Γ := (ratU σ G.V.J).subgroupOf (unip σ G.V H)
  haveI hΓc : Countable Γ := by
    haveI := GlobalTheory.QDom.countable_ratU σ G.V.J
    refine Function.Injective.countable (f := fun x : Γ => (⟨x.1.1, x.2⟩ : ratU σ G.V.J)) ?_
    intro x y hxy
    exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hxy))
  have hΓ : ∀ x : Γ, ce x.1 ∈ Γ := fun x => by
    refine Subgroup.mem_subgroupOf.2 ?_
    rw [hce]
    exact mul_mem (mul_mem (inv_mem hratg) (Subgroup.mem_subgroupOf.1 x.2)) hratg
  have hΓ' : ∀ x : Γ, ce.symm x.1 ∈ Γ := fun x => by
    refine Subgroup.mem_subgroupOf.2 ?_
    rw [hces]
    exact mul_mem (mul_mem hratg (Subgroup.mem_subgroupOf.1 x.2)) (inv_mem hratg)
  let eΓ : Γ → Γ := fun x => ⟨ce x.1, hΓ x⟩
  have heΓ : Function.Bijective eΓ :=
    ⟨fun x y hxy => Subtype.ext (ce.injective (congrArg Subtype.val hxy)),
      fun x => ⟨⟨ce.symm x.1, hΓ' x⟩, Subtype.ext (ce.apply_symm_apply x.1)⟩⟩
  obtain ⟨𝓕, h𝓕, h0, htop⟩ := GlobalTheory.T.unipotent_fundamental_domain_exists F E σ B b a' G G₁ H H' hC hB hG hG₁ μN hμ
  have hfd : IsFundamentalDomain Γ (me.symm ⁻¹' 𝓕) (μN.map me) :=
    h𝓕.preimage_of_equiv hps.quasiMeasurePreserving heΓ fun x y => by
      show ce.symm (ce x.1 * y) = x.1 * ce.symm y
      rw [map_mul, ce.symm_apply_apply]
  have hset : me ⁻¹' (me.symm ⁻¹' 𝓕) = 𝓕 := by
    ext x
    simp
  have hmass : (μN.map me) (me.symm ⁻¹' 𝓕) = μN 𝓕 := by
    rw [MeasurableEquiv.map_apply, hset]
  have hfd2 : IsFundamentalDomain Γ 𝓕 (μN.map me) := by
    rw [hsc]
    exact h𝓕.mono Measure.smul_absolutelyContinuous
  haveI : SMulInvariantMeasure Γ (unip σ G.V H) (μN.map me) :=
    ⟨fun c A _ => by
      show (μN.map me) ((fun x => (c : unip σ G.V H) * x) ⁻¹' A) = _
      exact measure_preimage_mul _ _ _⟩
  haveI : MeasurableConstSMul Γ (unip σ G.V H) :=
    ⟨fun c => by
      show Measurable fun x : unip σ G.V H => (c : unip σ G.V H) * x
      exact measurable_const_mul _⟩
  have hmeq : (μN.map me) 𝓕 = (μN.map me) (me.symm ⁻¹' 𝓕) := hfd2.measure_eq hfd
  have hs1 : s = 1 := by
    have h2 : (μN.map me) 𝓕 = (s : ENNReal) * μN 𝓕 := by
      rw [hsc, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    have h1 : (s : ENNReal) * μN 𝓕 = 1 * μN 𝓕 := by
      rw [one_mul, ← h2, hmeq, hmass]
    have := (ENNReal.mul_left_inj h0 htop).1 h1
    exact_mod_cast this
  have hmap : μN.map me = μN := by
    rw [hsc, hs1, one_smul]
  calc ∫⁻ n, f (n.1 * g) ∂μN = ∫⁻ n, f (g * (me n).1) ∂μN := by
        refine lintegral_congr fun n => ?_
        rw [hme, hce]
        simp [mul_assoc]
    _ = ∫⁻ n, f (g * n.1) ∂(μN.map me) := (lintegral_map_equiv (fun n : unip σ G.V H => f (g * n.1)) me).symm
    _ = ∫⁻ n, f (g * n.1) ∂μN := by rw [hmap]
