import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfMemSpanImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianTwistToHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology

noncomputable section

namespace GlobalTheory.ThetaCplV

open scoped ComplexConjugate
open GlobalTheory.ThetaFacCompl

section Abstract

variable {M : Type*} [AddCommGroup M] [Module ℂ M] {Gr : Type*} [Group Gr]

def typeSet (ρ : Gr →* Module.End ℂ M) (Z T : Submodule ℂ M) : Set M :=
  {g | ∃ L : T →ₗ[ℂ] M, (∀ t, L t ∈ Z) ∧ (∀ (k : Gr) (t t' : T), (t' : M) = ρ k t → L t' = ρ k (L t)) ∧
    g ∈ LinearMap.range L}

def rt {G : Type*} [Group G] (K : Subgroup G) : K →* Module.End ℂ (G → ℂ) where
  toFun k := LinearMap.funLeft ℂ ℂ fun x => x * (k : G)
  map_one' := by ext f x; simp [LinearMap.funLeft_apply]
  map_mul' k k' := by ext f x; simp [LinearMap.funLeft_apply, mul_assoc]

@[simp] theorem rt_apply {G : Type*} [Group G] (K : Subgroup G) (k : K) (f : G → ℂ) (x : G) :
    rt K k f x = f (x * k) := rfl

theorem exists_orth_of_types (Z : Submodule ℂ M) (q : M → M → ℂ)
    (hadd : ∀ a ∈ Z, ∀ b ∈ Z, ∀ c ∈ Z, q (a + b) c = q a c + q b c)
    (hsmul : ∀ a ∈ Z, ∀ c ∈ Z, ∀ t : ℂ, q (t • a) c = t * q a c)
    (hherm : ∀ a ∈ Z, ∀ b ∈ Z, q b a = conj (q a b)) (hpos : ∀ a ∈ Z, q a a = 0 → a = 0)
    (ρ : Gr →* Module.End ℂ M) (hZ : ∀ k, ∀ a ∈ Z, ρ k a ∈ Z)
    (hinv : ∀ k, ∀ a ∈ Z, ∀ b ∈ Z, q (ρ k a) (ρ k b) = q a b)
    (N : Submodule ℂ M) (hNZ : N ≤ Z) (hN : ∀ k, ∀ a ∈ N, ρ k a ∈ N)
    (hfin : ∀ a ∈ N, FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => ρ k a)))
    (f : M) (hf : f ∈ Z)
    (hadm : FiniteDimensional ℂ
      (Submodule.span ℂ (typeSet ρ Z (Submodule.span ℂ (Set.range fun k => ρ k f))))) :
    ∃ n ∈ N, ∀ m ∈ N, q m (f - n) = 0 := by

  have proj : ∀ U : Submodule ℂ M, FiniteDimensional ℂ U → U ≤ Z → ∀ x ∈ Z, ∃ a ∈ U, ∀ u ∈ U, q u (x - a) = 0 := by
    intro U hU hUZ x hx
    obtain ⟨S, hS⟩ : U.FG := (Submodule.fg_iff_finiteDimensional U).2 hU
    have hSZ : (↑S : Set M) ⊆ Z := fun y hy => hUZ (hS ▸ Submodule.subset_span hy)
    obtain ⟨a, ha, h⟩ := exists_orth Z q hadd hsmul hherm hpos S hSZ x hx
    refine ⟨a, hS ▸ ha, fun u hu => ?_⟩
    exact q_span_left Z q hadd hsmul hSZ (Z.sub_mem hx (hUZ (hS ▸ ha))) h u (hS ▸ hu)
  set T := Submodule.span ℂ (Set.range fun k => ρ k f) with hT
  set Y := Submodule.span ℂ (typeSet ρ Z T) with hY
  have hTZ : T ≤ Z := Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hZ k f hf)
  have hYZ : Y ≤ Z := Submodule.span_le.2 (by rintro _ ⟨L, hL, -, t, rfl⟩; exact hL t)
  have hfT : f ∈ T := Submodule.subset_span ⟨1, by simp⟩
  have hfY : f ∈ Y := Submodule.subset_span ⟨T.subtype, fun t => hTZ t.2, fun k t t' h => h, ⟨f, hfT⟩, rfl⟩
  haveI : FiniteDimensional ℂ ↥(Y ⊓ N) := Submodule.finiteDimensional_of_le inf_le_left
  obtain ⟨n, hn, hrn⟩ := proj (Y ⊓ N) inferInstance (inf_le_right.trans hNZ) f hf
  refine ⟨n, hn.2, fun m hm => ?_⟩
  set U := Submodule.span ℂ (Set.range fun k => ρ k m) with hU
  have hUN : U ≤ N := Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hN k m hm)
  have hUZ : U ≤ Z := hUN.trans hNZ
  have hUst : ∀ k, ∀ u ∈ U, ρ k u ∈ U := by
    intro k u hu
    have : U.map (ρ k) ≤ U := by
      rw [hU, Submodule.map_span_le]
      rintro _ ⟨k', rfl⟩
      exact Submodule.subset_span ⟨k * k', by simp⟩
    exact this ⟨u, hu, rfl⟩
  let P : M → M → Prop := fun x a => a ∈ U ∧ ∀ u ∈ U, q u (x - a) = 0
  have ex : ∀ x ∈ Z, ∃ a, P x a := fun x hx => proj U (hfin m hm) hUZ x hx
  have uniq : ∀ x ∈ Z, ∀ a b, P x a → P x b → a = b := by
    intro x hx a b ha hb
    have hab : a - b ∈ U := U.sub_mem ha.1 hb.1
    have e : a - b = (x - b) - (x - a) := by abel
    refine sub_eq_zero.1 (hpos _ (hUZ hab) ?_)
    conv_lhs => arg 2; rw [e]
    rw [q_sub_right Z q hadd hsmul hherm (Z.sub_mem hx (hUZ hb.1)) (Z.sub_mem hx (hUZ ha.1)) (hUZ hab),
      ha.2 _ hab, hb.2 _ hab, sub_zero]
  have Padd : ∀ x ∈ Z, ∀ y ∈ Z, ∀ a b, P x a → P y b → P (x + y) (a + b) := by
    intro x hx y hy a b ha hb
    refine ⟨U.add_mem ha.1 hb.1, fun u hu => ?_⟩
    have e : x + y - (a + b) = (x - a) + (y - b) := by abel
    rw [e, q_add_right Z q hadd hherm (Z.sub_mem hx (hUZ ha.1)) (Z.sub_mem hy (hUZ hb.1)) (hUZ hu), ha.2 u hu,
      hb.2 u hu, add_zero]
  have Psmul : ∀ (c : ℂ), ∀ x ∈ Z, ∀ a, P x a → P (c • x) (c • a) := by
    intro c x hx a ha
    refine ⟨U.smul_mem c ha.1, fun u hu => ?_⟩
    rw [← smul_sub, q_smul_right Z q hsmul hherm (Z.sub_mem hx (hUZ ha.1)) (hUZ hu), ha.2 u hu, mul_zero]
  have Pact : ∀ k, ∀ x ∈ Z, ∀ a, P x a → P (ρ k x) (ρ k a) := by
    intro k x hx a ha
    refine ⟨hUst k a ha.1, fun u hu => ?_⟩
    have e : u = ρ k (ρ k⁻¹ u) := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [← map_sub, e, hinv k _ (hUZ (hUst _ u hu)) _ (Z.sub_mem hx (hUZ ha.1))]
    exact ha.2 _ (hUst _ u hu)
  have key : ∀ y ∈ Y, ∃ a ∈ Y, P y a := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨L, hL, hLe, t, rfl⟩ := hx
      let c : T → M := fun t => (ex (L t) (hL t)).choose
      have hc : ∀ t, P (L t) (c t) := fun t => (ex (L t) (hL t)).choose_spec
      let L' : T →ₗ[ℂ] M :=
        { toFun := c
          map_add' := fun s t => uniq _ (hL (s + t)) _ _ (hc _) (by
            rw [map_add]; exact Padd _ (hL s) _ (hL t) _ _ (hc s) (hc t))
          map_smul' := fun d t => uniq _ (hL (d • t)) _ _ (hc _) (by
            rw [map_smul]; exact Psmul d _ (hL t) _ (hc t)) }
      refine ⟨c t, Submodule.subset_span ⟨L', fun s => hUZ (hc s).1, fun k s s' h => ?_, t, rfl⟩, hc t⟩
      refine uniq _ (hL s') _ _ (hc s') ?_
      rw [hLe k s s' h]
      exact Pact k _ (hL s) _ (hc s)
    | zero => exact ⟨0, Y.zero_mem, U.zero_mem, fun u hu => by
        have := q_smul_right Z q hsmul hherm Z.zero_mem (hUZ hu) 0
        simpa using this⟩
    | add x y hx hy ihx ihy =>
      obtain ⟨a, ha, hPa⟩ := ihx
      obtain ⟨b, hb, hPb⟩ := ihy
      exact ⟨a + b, Y.add_mem ha hb, Padd _ (hYZ hx) _ (hYZ hy) _ _ hPa hPb⟩
    | smul c x hx ihx =>
      obtain ⟨a, ha, hPa⟩ := ihx
      exact ⟨c • a, Y.smul_mem c ha, Psmul c _ (hYZ hx) _ hPa⟩
  have hrY : f - n ∈ Y := Y.sub_mem hfY hn.1
  obtain ⟨a, haY, haU, hPa⟩ := key _ hrY
  have h1 : q a (f - n) = 0 := hrn a ⟨haY, hUN haU⟩
  have h2 := hPa a haU
  rw [q_sub_right Z q hadd hsmul hherm (hYZ hrY) (hUZ haU) (hUZ haU), h1, zero_sub, neg_eq_zero] at h2
  have ha0 : a = 0 := hpos a (hUZ haU) h2
  have := hPa m (Submodule.subset_span ⟨1, by simp⟩)
  rwa [ha0, sub_zero] at this

end Abstract

section Domain

open MeasureTheory

variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] {μ : Measure G} [μ.IsMulLeftInvariant]
  [μ.IsMulRightInvariant] {Γ : Subgroup G} [Countable Γ] {𝓕 : Set G}

omit [μ.IsMulLeftInvariant] [Countable Γ] in

theorem isFundamentalDomain_mul_right (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (g : G) :
    IsFundamentalDomain Γ ((fun x => x * g) '' 𝓕) μ := by
  have hg' : MeasurePreserving (MeasurableEquiv.mulRight g) μ μ := measurePreserving_mul_right μ g
  exact h𝓕.image_of_equiv (MeasurableEquiv.mulRight g).toEquiv hg'.symm.quasiMeasurePreserving (Equiv.refl _)
      (fun γ x => by
        show (γ • x) * g = γ • (x * g)
        simp only [Subgroup.smul_def, smul_eq_mul, mul_assoc])

theorem setIntegral_mul_right {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    (f : G → V) (hf : ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) (g : G) :
    ∫ x in 𝓕, f (x * g) ∂μ = ∫ x in 𝓕, f x ∂μ := by
  rw [← (measurePreserving_mul_right μ g).setIntegral_image_emb (measurableEmbedding_mulRight g) f 𝓕]
  refine (isFundamentalDomain_mul_right h𝓕 g).setIntegral_eq h𝓕 ?_
  intro γ x
  rw [Subgroup.smul_def, smul_eq_mul]
  exact hf γ γ.2 x

theorem integrableOn_mul_right {V : Type} [NormedAddCommGroup V] (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    (f : G → V) (hf : ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) (hi : IntegrableOn f 𝓕 μ) (g : G) :
    IntegrableOn (fun x => f (x * g)) 𝓕 μ := by
  have h1 : IntegrableOn f ((fun x => x * g) '' 𝓕) μ :=
    ((isFundamentalDomain_mul_right h𝓕 g).integrableOn_iff h𝓕 (fun γ x => by
      rw [Subgroup.smul_def, smul_eq_mul]; exact hf γ γ.2 x)).2 hi
  exact ((measurePreserving_mul_right μ g).integrableOn_image (measurableEmbedding_mulRight g)).1 h1

end Domain

section Deriv

open MeasureTheory

theorem setIntegral_deriv_eq_zero {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (Γ : Subgroup G) [Countable Γ] (𝓕 : Set G)
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (f f₁ : G → ℂ) (hf : ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x)
    (hf₁ : ∀ γ ∈ Γ, ∀ x, f₁ (γ * x) = f₁ x) (hc : Continuous f₁) (hi : IntegrableOn f 𝓕 μ)
    (hi₁ : IntegrableOn f₁ 𝓕 μ) (γ : Multiplicative ℝ →* G) (hγ : Continuous γ)
    (hd : ∀ x, HasDerivAt (fun t : ℝ => f (x * γ (Multiplicative.ofAdd t))) (f₁ x) 0) :
    ∫ x in 𝓕, f₁ x ∂μ = 0 := by
  have hγ' : Continuous fun t : ℝ => γ (Multiplicative.ofAdd t) := hγ.comp continuous_ofAdd
  have hds : ∀ x s, HasDerivAt (fun t : ℝ => f (x * γ (Multiplicative.ofAdd t)))
      (f₁ (x * γ (Multiplicative.ofAdd s))) s := by
    intro x s
    have h0 := hd (x * γ (Multiplicative.ofAdd s))
    have h1 : HasDerivAt (fun t : ℝ => f (x * γ (Multiplicative.ofAdd s) * γ (Multiplicative.ofAdd t)))
      (f₁ (x * γ (Multiplicative.ofAdd s))) (s - s) := by rwa [sub_self]
    have h2 := h1.comp_sub_const s s
    have e : (fun t : ℝ => f (x * γ (Multiplicative.ofAdd s) * γ (Multiplicative.ofAdd (t - s)))) =
        fun t : ℝ => f (x * γ (Multiplicative.ofAdd t)) := by
      funext t
      rw [mul_assoc, ← map_mul, ← ofAdd_add, add_sub_cancel]
    rwa [e] at h2
  have ftc : ∀ x, ∫ s in Set.Ioc (0 : ℝ) 1, f₁ (x * γ (Multiplicative.ofAdd s)) =
      f (x * γ (Multiplicative.ofAdd 1)) - f x := by
    intro x
    rw [← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hds x s)
        ((hc.comp (continuous_const.mul hγ')).intervalIntegrable 0 1)]
    simp
  have hint : Integrable (Function.uncurry fun (x : G) (s : ℝ) => f₁ (x * γ (Multiplicative.ofAdd s)))
      ((μ.restrict 𝓕).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
    have hm : Continuous (Function.uncurry fun (x : G) (s : ℝ) => f₁ (x * γ (Multiplicative.ofAdd s))) :=
      hc.comp (continuous_fst.mul (hγ'.comp continuous_snd))
    rw [integrable_prod_iff' hm.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun s =>
      integrableOn_mul_right h𝓕 f₁ hf₁ hi₁ (γ (Multiplicative.ofAdd s)), ?_⟩
    have e : (fun s : ℝ => ∫ x in 𝓕, ‖f₁ (x * γ (Multiplicative.ofAdd s))‖ ∂μ) = fun _ => ∫ x in 𝓕, ‖f₁ x‖ ∂μ :=
      funext fun s => setIntegral_mul_right h𝓕 (fun x => ‖f₁ x‖) (fun c hc x => by rw [hf₁ c hc]) _
    simp only [Function.uncurry_apply_pair]
    rw [e]
    exact integrable_const _
  have sw := integral_integral_swap hint
  simp only [ftc] at sw
  rw [integral_sub (integrableOn_mul_right h𝓕 f hf hi _) hi, setIntegral_mul_right h𝓕 f hf, sub_self] at sw
  simp only [setIntegral_mul_right h𝓕 f₁ hf₁] at sw
  simpa using sw.symm

end Deriv

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def finU (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Subgroup (UA σ J) :=
  ((Matrix.GeneralLinearGroup.map (n := Fin n)
    (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) : AE F E →+* Ainf F ⊗[F] E)).comp (Subgroup.subtype _)).ker

theorem mem_finU {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {k : UA σ J} :
    k ∈ finU σ J ↔ (mat k).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1 :=
  ⟨fun h => congrArg Units.val (MonoidHom.mem_ker.1 h), fun h => MonoidHom.mem_ker.2 (Units.ext h)⟩

theorem isMulRightInvariant_skew {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (B : Base F E) {n r s : ℕ} (W : Spc F E n)
    (hW : W.IsSkew σ B r s) (μ : Measure (UA σ W.J)) [μ.IsHaarMeasure] : μ.IsMulRightInvariant := by
  have hσ := GlobalTheory.SkewToHerm.sigma_invol σ hcm
  obtain ⟨x, hx⟩ := GlobalTheory.SkewToHerm.exists_sigma_ne σ hcm
  obtain ⟨c, hc, hJ⟩ := GlobalTheory.SkewToHerm.exists_hermND F E σ hcm B n W r s hW
  obtain ⟨_, _, _, _⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ n W.J
  haveI : BorelSpace (UA σ W.J) := ⟨rfl⟩
  let e := GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc
  have he : Continuous e := continuous_subtype_val.subtype_mk _
  have he' : Continuous e.symm := continuous_subtype_val.subtype_mk _
  haveI hH : (μ.map e).IsHaarMeasure := MulEquiv.isHaarMeasure_map μ e he he'
  have hR : (μ.map e).IsMulRightInvariant :=
    GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_adelic σ hσ (δ := x - σ x) (sub_ne_zero.2 (Ne.symm hx))
      (by rw [map_sub, hσ]; ring) hJ (μ.map e)
  have e1 : μ = (μ.map e).map e.symm := by
    rw [Measure.map_map he'.measurable he.measurable]
    simp
  refine ⟨fun g => ?_⟩
  conv_rhs => rw [e1, ← hR.map_mul_right_eq_self (e g)]
  rw [Measure.map_map he'.measurable (measurable_mul_const _),
    Measure.map_map (he'.measurable.comp (measurable_mul_const _)) he.measurable]
  congr 1

end GlobalTheory.ThetaCplV

end
