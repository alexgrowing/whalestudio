import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvcPowRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqOfPointsOfGerm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionExtOfApplyEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealFactorIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIdealPowLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomEqOfCompEqId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentFixLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingFiniteIdealsOfMaximalIdealPrincipalNilp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapMemMaximalIdealIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyOfDegreeIntActionHarrisTaylor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentCoordsBaseChangeSmoothCommGroup
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES GlobalTheory.IwLevel
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.UPel.HT.ES.KerFin

theorem finite_ideals {k : Type} [Field k] [IsAlgClosed k] {A B₁ : Over (Sp k)} [GrpObj A] [IsCommMonObj A]
    [GrpObj B₁] (hA : IsAbelianScheme A) (π₀ : A ⟶ A) [IsMonHom π₀] {d : ℕ} (hd : IsIsogDeg π₀ d) (g : A ⟶ B₁)
    (hline : ∀ v₁ v₂ : epsR k ⟶ A, IsTangent v₁ → IsTangent v₂ → v₁ ≫ g = 1 → v₂ ≫ g = 1 →
      ∃ c : k, v₁.left = spMap (epsScaleR c) ≫ v₂.left ∨ v₂.left = spMap (epsScaleR c) ≫ v₁.left)
    (x₀ : A.left) (hx₀ : x₀ ∈ Set.range (η[A]).left.base) (J₁ Je : Ideal (A.left.presheaf.stalk x₀))
    (hJ₁ : ∀ (R' : Type) [CommRing R'] (ψ : A.left.presheaf.stalk x₀ →+* R'),
      KerDet.InK π₀ (Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk x₀) ↔ J₁ ≤ RingHom.ker ψ)
    (hJe : ∀ (R' : Type) [CommRing R'] (ψ : A.left.presheaf.stalk x₀ →+* R'),
      KerDet.InK g (Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk x₀) ↔ Je ≤ RingHom.ker ψ) :
    Set.Finite {I | J₁ ⊔ Je ≤ I} := by
  set JG := J₁ ⊔ Je with hJG
  by_cases htop : JG = ⊤
  · refine (Set.finite_singleton ⊤).subset ?_
    intro I hI
    simp only [Set.mem_setOf_eq] at hI
    rw [htop, top_le_iff] at hI
    exact hI
  haveI : Nontrivial (A.left.presheaf.stalk x₀ ⧸ JG) := Ideal.Quotient.nontrivial_iff.2 htop
  haveI : IsLocalRing (A.left.presheaf.stalk x₀ ⧸ JG) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk JG) Ideal.Quotient.mk_surjective
  have hJGm : JG ≤ IsLocalRing.maximalIdeal _ := IsLocalRing.le_maximalIdeal htop
  obtain ⟨M, hM⟩ := GlobalTheory.KerIdeal.maximalIdeal_pow_le k A A π₀ d hA hA inferInstance hd x₀ hx₀ J₁ hJ₁
  have hunit : ∀ a : A.left.presheaf.stalk x₀, IsUnit (Ideal.Quotient.mk JG a) → IsUnit a := by
    intro a hu
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_mul, ← map_one (Ideal.Quotient.mk JG), Ideal.Quotient.eq] at hy
    have h1 : a * y - 1 ∈ IsLocalRing.maximalIdeal _ := hJGm hy
    have h2 : IsUnit (a * y) := by
      by_contra hn
      have h3 : a * y ∈ IsLocalRing.maximalIdeal _ := hn
      have h4 : (1 : A.left.presheaf.stalk x₀) ∈ IsLocalRing.maximalIdeal _ := by
        simpa using Ideal.sub_mem _ h3 h1
      exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 h4)
    exact isUnit_of_mul_isUnit_left h2
  have hmS : IsLocalRing.maximalIdeal (A.left.presheaf.stalk x₀ ⧸ JG) ≤
      (IsLocalRing.maximalIdeal _).map (Ideal.Quotient.mk JG) := by
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    refine Ideal.mem_map_of_mem _ ?_
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha ⊢
    exact fun hu => ha (hu.map _)
  have hnil : IsNilpotent (IsLocalRing.maximalIdeal (A.left.presheaf.stalk x₀ ⧸ JG)) := by
    refine ⟨M, le_bot_iff.1 ?_⟩
    calc IsLocalRing.maximalIdeal (A.left.presheaf.stalk x₀ ⧸ JG) ^ M
        ≤ ((IsLocalRing.maximalIdeal _).map (Ideal.Quotient.mk JG)) ^ M := Ideal.pow_right_mono hmS M
      _ = (IsLocalRing.maximalIdeal _ ^ M).map (Ideal.Quotient.mk JG) := (Ideal.map_pow _ _ _).symm
      _ ≤ JG.map (Ideal.Quotient.mk JG) := Ideal.map_mono (hM.trans le_sup_left)
      _ = ⊥ := by rw [Ideal.map_quotient_self]
  obtain ⟨jk, hres, htan, hinjT⟩ := GlobalTheory.TangentStalk.tangent_eq_stalk_dual k A x₀ hx₀
  letI : Algebra k (A.left.presheaf.stalk x₀ ⧸ JG) := ((Ideal.Quotient.mk JG).comp jk).toAlgebra
  have halg : ∀ c : k, algebraMap k (A.left.presheaf.stalk x₀ ⧸ JG) c = Ideal.Quotient.mk JG (jk c) :=
    fun c => rfl
  have hpt : ∀ (ψ : A.left.presheaf.stalk x₀ →+* DualNumber k) (v : epsR k ⟶ A),
      v.left = Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk x₀ → JG ≤ RingHom.ker ψ →
      v ≫ g = 1 := by
    intro ψ v hv hJ
    rw [KerDet.comp_eq_one_iff, hv]
    exact (hJe _ ψ).2 (le_sup_right.trans hJ)
  have hprin : (IsLocalRing.maximalIdeal (A.left.presheaf.stalk x₀ ⧸ JG)).IsPrincipal := by
    refine GlobalTheory.LocalTangent.maximalIdeal_isPrincipal k _ ?_ hnil ?_
    · intro a
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨c, hc⟩ := hres a
      refine ⟨c, ?_⟩
      rw [halg, ← map_sub, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact fun hu => (IsLocalRing.mem_maximalIdeal _).1 hc (hunit _ hu)
    · intro χ₁ χ₂
      have hcomp : ∀ χ : (A.left.presheaf.stalk x₀ ⧸ JG) →ₐ[k] DualNumber k,
          ((χ : (A.left.presheaf.stalk x₀ ⧸ JG) →+* DualNumber k).comp (Ideal.Quotient.mk JG)).comp jk = algebraMap k (DualNumber k) := by
        intro χ
        refine RingHom.ext fun c => ?_
        simp only [RingHom.comp_apply, RingHom.coe_coe]
        rw [← halg]
        exact χ.commutes c
      have hker : ∀ χ : (A.left.presheaf.stalk x₀ ⧸ JG) →ₐ[k] DualNumber k,
          JG ≤ RingHom.ker ((χ : (A.left.presheaf.stalk x₀ ⧸ JG) →+* DualNumber k).comp (Ideal.Quotient.mk JG)) := by
        intro χ a ha
        rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]
      obtain ⟨v₁, hv₁t, hv₁⟩ := htan _ (hcomp χ₁)
      obtain ⟨v₂, hv₂t, hv₂⟩ := htan _ (hcomp χ₂)
      have k₁ := hpt _ v₁ hv₁ (hker χ₁)
      have k₂ := hpt _ v₂ hv₂ (hker χ₂)
      obtain ⟨c, hc⟩ := hline v₁ v₂ hv₁t hv₂t k₁ k₂
      refine ⟨c, ?_⟩
      have hscale : ∀ ψ : A.left.presheaf.stalk x₀ →+* DualNumber k, ψ.comp jk = algebraMap k _ →
          ((epsScaleR c).comp ψ).comp jk = algebraMap k _ := by
        intro ψ hψ
        rw [RingHom.comp_assoc, hψ]
        refine RingHom.ext fun x => ?_
        simp [epsScaleR]
      have hsp : ∀ ψ : A.left.presheaf.stalk x₀ →+* DualNumber k,
          spMap (epsScaleR c) ≫ Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk x₀ =
            Spec.map (CommRingCat.ofHom ((epsScaleR c).comp ψ)) ≫ A.left.fromSpecStalk x₀ := by
        intro ψ
        rw [← Category.assoc, spMap, ← Spec.map_comp, CommRingCat.ofHom_comp]
      have hdesc : ∀ χ χ' : (A.left.presheaf.stalk x₀ ⧸ JG) →ₐ[k] DualNumber k,
          (χ : (A.left.presheaf.stalk x₀ ⧸ JG) →+* DualNumber k).comp (Ideal.Quotient.mk JG) =
            (epsScaleR c).comp ((χ' : (A.left.presheaf.stalk x₀ ⧸ JG) →+* DualNumber k).comp (Ideal.Quotient.mk JG)) →
          (χ : (A.left.presheaf.stalk x₀ ⧸ JG) →+* DualNumber k) = (epsScaleR c).comp (χ' : (A.left.presheaf.stalk x₀ ⧸ JG) →+* DualNumber k) := by
        intro χ χ' h
        apply Ideal.Quotient.ringHom_ext
        rw [RingHom.comp_assoc]
        exact h
      rcases hc with hc | hc
      · left
        refine hdesc _ _ (hinjT _ _ (hcomp χ₁) (hscale _ (hcomp χ₂)) ?_)
        rw [← hv₁, hc, hv₂, hsp]
      · right
        refine hdesc _ _ (hinjT _ _ (hcomp χ₂) (hscale _ (hcomp χ₁)) ?_)
        rw [← hv₂, hc, hv₁, hsp]
  refine ((GlobalTheory.localRing_finite_ideals_of_maximalIdeal_principal_nilpotent _ hprin hnil).image (fun I => I.comap (Ideal.Quotient.mk JG))).subset ?_
  intro I hI
  refine ⟨I.map (Ideal.Quotient.mk JG), trivial, ?_⟩
  simp only
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  exact sup_eq_left.2 hI

theorem comp_lift_eq_one {S : Scheme.{0}} {A B C T : Over S} [GrpObj B] [GrpObj C] (f : A ⟶ B) (g : A ⟶ C)
    (x : T ⟶ A) : x ≫ lift f g = 1 ↔ x ≫ f = 1 ∧ x ≫ g = 1 := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa using congrArg (· ≫ fst B C) h
    · simpa using congrArg (· ≫ snd B C) h
  · rintro ⟨h₁, h₂⟩
    apply CartesianMonoidalCategory.hom_ext <;> simp [h₁, h₂]

theorem finite_subgroups {k : Type} [Field k] [IsAlgClosed k] {A B₁ : Over (Sp k)} [GrpObj A] [IsCommMonObj A]
    [GrpObj B₁] (hA : IsAbelianScheme A) (hB₁ : IsAbelianScheme B₁) (π₀ : A ⟶ A) [IsMonHom π₀] {d : ℕ}
    (hd : IsIsogDeg π₀ d) (g : A ⟶ B₁) [IsMonHom g]
    (hline : ∀ v₁ v₂ : epsR k ⟶ A, IsTangent v₁ → IsTangent v₂ → v₁ ≫ g = 1 → v₂ ≫ g = 1 →
      ∃ c : k, v₁.left = spMap (epsScaleR c) ≫ v₂.left ∨ v₂.left = spMap (epsScaleR c) ≫ v₁.left) :
    Set.Finite {P : ∀ T : Over (Sp k), (T ⟶ A) → Prop | ∃ (B : Over (Sp k)) (_ : GrpObj B) (ψ : A ⟶ B),
      IsAbelianScheme B ∧ IsMonHom ψ ∧ P = fun T x => x ≫ π₀ = 1 ∧ x ≫ g = 1 ∧ x ≫ ψ = 1} := by
  let x₀ : A.left := (η[A]).left.base (IsLocalRing.closedPoint k)
  have hx₀ : x₀ ∈ Set.range (η[A]).left.base := ⟨_, rfl⟩
  obtain ⟨J₁, hJ₁⟩ := GlobalTheory.KerIdeal.kernel_ideal k A A π₀ hA x₀
  obtain ⟨Je, hJe⟩ := GlobalTheory.KerIdeal.kernel_ideal k A B₁ g hB₁ x₀
  have hfinI := finite_ideals hA π₀ hd g hline x₀ hx₀ J₁ Je hJ₁ hJe
  have hfinP := finite_points_ker k A A π₀ d hd
  let pt : ∀ (R' : Type) (_ : CommRing R') (φ : A.left.presheaf.stalk x₀ →+* R'),
      Over.mk ((Spec.map (CommRingCat.ofHom φ) ≫ A.left.fromSpecStalk x₀) ≫ A.hom) ⟶ A :=
    fun R' _ φ => Over.homMk (Spec.map (CommRingCat.ofHom φ) ≫ A.left.fromSpecStalk x₀) rfl
  let f : (∀ T : Over (Sp k), (T ⟶ A) → Prop) → Set (𝟙_ (Over (Sp k)) ⟶ A) ×
      (∀ (R' : Type) (_ : CommRing R') (φ : A.left.presheaf.stalk x₀ →+* R'), Prop) :=
    fun P => ({a | P _ a}, fun R' i φ => P _ (pt R' i φ))
  let G : Ideal (A.left.presheaf.stalk x₀) →
      (∀ (R' : Type) (_ : CommRing R') (φ : A.left.presheaf.stalk x₀ →+* R'), Prop) :=
    fun I R' _ φ => I ≤ RingHom.ker φ
  refine Set.Finite.of_finite_image (f := f) ((hfinP.finite_subsets.prod (hfinI.image G)).subset ?_) ?_
  · rintro _ ⟨P, ⟨B, _, ψ, hB, hψ, rfl⟩, rfl⟩
    obtain ⟨J, hJ⟩ := GlobalTheory.KerIdeal.kernel_ideal k A B ψ hB x₀
    refine ⟨fun a ha => ha.1, J₁ ⊔ Je ⊔ J, (le_sup_left : J₁ ⊔ Je ≤ _), ?_⟩
    funext R' _ φ
    apply propext
    simp only [G, f, sup_le_iff, KerDet.comp_eq_one_iff, and_assoc]
    exact (and_congr (hJ₁ R' φ) (and_congr (hJe R' φ) (hJ R' φ))).symm
  · have key : ∀ (B : Over (Sp k)) [GrpObj B] (ψ : A ⟶ B) [IsMonHom ψ] (B' : Over (Sp k)) [GrpObj B'] (ψ' : A ⟶ B')
        [IsMonHom ψ'], IsAbelianScheme B →
        f (fun T x => x ≫ π₀ = 1 ∧ x ≫ g = 1 ∧ x ≫ ψ = 1) = f (fun T x => x ≫ π₀ = 1 ∧ x ≫ g = 1 ∧ x ≫ ψ' = 1) →
        ∀ (T : Over (Sp k)) (x : T ⟶ A), (x ≫ π₀ = 1 ∧ x ≫ g = 1 ∧ x ≫ ψ = 1) → x ≫ ψ' = 1 := by
      intro B _ ψ _ B' _ ψ' _ hB e T x hx
      have hAB := AbelianSchemeGerms.isAbelianScheme_tensor A _ hA (AbelianSchemeGerms.isAbelianScheme_tensor B₁ B hB₁ hB)
      have := hAB.proper
      have : IsSeparated ((fst A (B₁ ⊗ B)).left ≫ A.hom) := by rw [Over.w]; infer_instance
      have : IsSeparated (fst A (B₁ ⊗ B)).left := IsSeparated.of_comp _ A.hom
      have : IsFinite ((lift π₀ (lift g ψ)).left ≫ (fst A (B₁ ⊗ B)).left) := by
        rw [← Over.comp_left, lift_fst]; exact hd.fin
      have : IsFinite (lift π₀ (lift g ψ)).left := IsFinite.of_comp _ (fst A (B₁ ⊗ B)).left
      rw [KerDet.comp_eq_one_iff]
      refine KerDet.inK_of_inK (lift π₀ (lift g ψ)) ψ' (fun a ha => ?_) x₀ hx₀ (fun R' i φ hφ => ?_) _ ?_
      · rw [comp_lift_eq_one, comp_lift_eq_one] at ha
        have e₁ : {a : 𝟙_ (Over (Sp k)) ⟶ A | a ≫ π₀ = 1 ∧ a ≫ g = 1 ∧ a ≫ ψ = 1} =
          {a | a ≫ π₀ = 1 ∧ a ≫ g = 1 ∧ a ≫ ψ' = 1} := congrArg Prod.fst e
        exact ((Set.ext_iff.1 e₁ a).1 ha).2.2
      · have h := (KerDet.comp_eq_one_iff _ (pt R' i φ)).2 hφ
        rw [comp_lift_eq_one, comp_lift_eq_one] at h
        have e₂ := congrFun (congrFun (congrFun (congrArg Prod.snd e) R') i) φ
        exact (KerDet.comp_eq_one_iff _ (pt R' i φ)).1 (e₂.mp h).2.2
      · rw [← KerDet.comp_eq_one_iff, comp_lift_eq_one, comp_lift_eq_one]
        exact hx
    rintro _ ⟨B, _, ψ, hB, hψ, rfl⟩ _ ⟨B', _, ψ', hB', hψ', rfl⟩ e
    funext T x
    exact propext ⟨fun h => ⟨h.1, h.2.1, key B ψ B' ψ' hB e T x h⟩,
      fun h => ⟨h.1, h.2.1, key B' ψ' B ψ hB' e.symm T x h⟩⟩

end GlobalTheory.UPel.HT.ES.KerFin

namespace GlobalTheory.UPel.HT.ES.KerFin

open GlobalTheory.HTLieFix

theorem exists_local_idempotents {B : Type} [CommRing B] (c : B) [Finite (B ⧸ Ideal.span {c})] :
    ∃ (κ : Type) (_ : Fintype κ) (e : κ → B), (∑ i, e i) - 1 ∈ Ideal.span {c} ∧
      (∀ i, (1 - e i) * e i ∈ Ideal.span {c}) ∧
      ∀ i (P Q : Ideal B), P.IsPrime → Q.IsPrime → c ∈ P → c ∈ Q → e i ∉ P → e i ∉ Q → P = Q := by
  classical
  let Q := B ⧸ Ideal.span {c}
  let π : B →+* Q := Ideal.Quotient.mk _
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  letI : Fintype (MaximalSpectrum Q) := Fintype.ofFinite _
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_nilradical (R := Q)
  have hinf : (⨅ I : MaximalSpectrum Q, I.asIdeal ^ (n + 1)) = ⊥ := by
    rw [← IsArtinianRing.nilradical_pow_eq_iInf, pow_succ, hn]; simp
  have hz : ∀ x : Q, (∀ I : MaximalSpectrum Q, x ∈ I.asIdeal ^ (n + 1)) → x = 0 := fun x hx => by
    rw [← Ideal.mem_bot, ← hinf, Ideal.mem_iInf]; exact hx
  have hcop : Pairwise (Function.onFun IsCoprime fun I : MaximalSpectrum Q => I.asIdeal ^ (n + 1)) :=
    fun I J h => (MaximalSpectrum.isCoprime_of_ne h).pow
  have hex : ∀ I : MaximalSpectrum Q, ∃ x : B, ∀ J : MaximalSpectrum Q,
      π x - (if J = I then 1 else 0) ∈ J.asIdeal ^ (n + 1) := fun I => by
    obtain ⟨x, hx⟩ := Ideal.exists_forall_sub_mem_ideal hcop (fun J => if J = I then (1 : Q) else 0)
    obtain ⟨y, rfl⟩ := hπ x
    exact ⟨y, hx⟩
  choose e he using hex
  refine ⟨MaximalSpectrum Q, inferInstance, e, ?_, fun I => ?_, fun I P P' hP hP' hc hc' h h' => ?_⟩
  · rw [← Ideal.Quotient.eq_zero_iff_mem]
    refine hz _ fun J => ?_
    have := Ideal.sum_mem (J.asIdeal ^ (n + 1)) (t := Finset.univ) fun I _ => he I J
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq, if_pos (Finset.mem_univ _), ← map_sum] at this
    simpa using this
  · rw [← Ideal.Quotient.eq_zero_iff_mem]
    refine hz _ fun J => ?_
    have := he I J
    change π _ ∈ _
    rw [map_mul, map_sub, map_one]
    split_ifs at this
    · refine Ideal.mul_mem_right _ _ ?_
      rw [← neg_sub]; exact neg_mem this
    · rw [sub_zero] at this
      exact Ideal.mul_mem_left _ _ this
  · have key : ∀ P : Ideal B, P.IsPrime → c ∈ P → e I ∉ P → P = I.asIdeal.comap π := by
      intro P hP hc h
      have hk : RingHom.ker π ≤ P := by
        rw [Ideal.mk_ker, Ideal.span_le, Set.singleton_subset_iff]; exact hc
      have hpr : (P.map π).IsPrime := Ideal.map_isPrime_of_surjective hπ hk
      have hcm : (P.map π).comap π = P := by
        rw [Ideal.comap_map_of_surjective _ hπ, ← RingHom.ker_eq_comap_bot]; exact sup_eq_left.2 hk
      let J : MaximalSpectrum Q := ⟨P.map π, IsArtinianRing.isMaximal_of_isPrime _⟩
      by_cases hJ : J = I
      · rw [← hJ]; exact hcm.symm
      · have := he I J
        rw [if_neg hJ, sub_zero] at this
        exact (h (hcm ▸ (Ideal.pow_le_self (Nat.succ_ne_zero n) this : π (e I) ∈ P.map π))).elim
    rw [key P hP hc h, key P' hP' hc' h']

theorem tangent_line {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    (hm : D.m = 1) {k : Type} [Field k] [IsAlgClosed k] [CharP k p] (β : R →+* k) (o : Obj b N (spMap β))
    (r : ℤ) (hr : β b.ρ = r) (L : ℕ) (e : 𝓞 D.F) (he : ∀ i j, β (b.t i e) ≠ 0 → β (b.t j e) ≠ 0 → i = j)
    (v₁ v₂ : epsR k ⟶ o.A) (ht₁ : IsTangent v₁) (ht₂ : IsTangent v₂)
    (hk₁ : v₁ ≫ o.act.act (algebraMap (𝓞 D.F) D.O ((D.ω - r) ^ L)) = 1)
    (hk₂ : v₂ ≫ o.act.act (algebraMap (𝓞 D.F) D.O ((D.ω - r) ^ L)) = 1)
    (hf₁ : v₁ ≫ o.act.act (algebraMap (𝓞 D.F) D.O (1 - e)) = 1)
    (hf₂ : v₂ ≫ o.act.act (algebraMap (𝓞 D.F) D.O (1 - e)) = 1) :
    ∃ c : k, v₁.left = spMap (epsScaleR c) ≫ v₂.left ∨ v₂.left = spMap (epsScaleR c) ≫ v₁.left := by
  classical
  obtain ⟨n, M, hM⟩ := GlobalTheory.LieCoordR.exists_coords_baseChange k o.A (@IsAbelianScheme.smooth _ _ _ o.ab)
  obtain ⟨T, Tinj, Trng, Tadd, Tsm, Tu⟩ := hM k (RingHom.id k)
  have hid : spMap (RingHom.id k) = 𝟙 (Sp k) := Spec.map_id _
  have hx : spMap (RingHom.id k) ≫ spMap β = spMap β := by rw [hid, Category.id_comp]
  have T0 : T 0 = 1 := by
    have h := Tadd 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm

  let fa : D.O → Matrix (Fin n) (Fin n) k := fun a => (M (o.act.act a)).map (RingHom.id k)
  have key : ∀ a v, T v ≫ o.act.act a = T ((fa a).mulVec v) := fun a v => Tu _ (o.act.hom a) v
  have f1 : fa 1 = 1 := mat_ext' fun v => Tinj (by
    rw [← key, o.act.one, Category.comp_id, Matrix.one_mulVec])
  have fmul : ∀ a c, fa (a * c) = fa a * fa c := fun a c => mat_ext' fun v => Tinj (by
    rw [← key, o.act.mul, ← Category.assoc, key, key, Matrix.mulVec_mulVec])
  have fadd : ∀ a c, fa (a + c) = fa a + fa c := fun a c => mat_ext' fun v => Tinj (by
    rw [← key, o.act.add, MonObj.comp_mul, key, key, ← Tadd, Matrix.add_mulVec])
  have f0 : fa 0 = 0 := by
    have h := fadd 0 0
    rw [add_zero] at h
    exact add_left_cancel (h.symm.trans (add_zero _).symm)
  let f : D.O →+* Matrix (Fin n) (Fin n) k :=
    { toFun := fa, map_one' := f1, map_mul' := fmul, map_zero' := f0, map_add' := fadd }
  have keyf : ∀ a v, T v ≫ o.act.act a = T ((f a).mulVec v) := key

  have hw : ∀ v : epsR k ⟶ o.A, v.left ≫ o.A.hom = (GlobalTheory.UPel.HT.epsPtR (spMap (RingHom.id k))).hom := fun v => by
    show v.left ≫ o.A.hom = spMap (algebraMap k (DualNumber k)) ≫ spMap (RingHom.id k)
    rw [hid, Category.comp_id]
    exact Over.w v
  let cv : (epsR k ⟶ o.A) → (GlobalTheory.UPel.HT.epsPtR (spMap (RingHom.id k)) ⟶ o.A) := fun v => Over.homMk v.left (hw v)
  have cvl : ∀ v, (cv v).left = v.left := fun v => Over.homMk_left _ _
  have coord : ∀ v : epsR k ⟶ o.A, IsTangent v → ∃ c, cv v = T c := fun v hv => by
    have h1 : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ (cv v).left =
        (1 : Over.mk (spMap (RingHom.id k)) ⟶ o.A).left := by
      rw [one_left', cvl]
      change _ = spMap (RingHom.id k) ≫ η[o.A].left
      rw [hid, Category.id_comp]
      exact hv
    obtain ⟨c, hc⟩ := (Trng (cv v)).1 h1
    exact ⟨c, hc.symm⟩
  have kill : ∀ (v : epsR k ⟶ o.A) (c : Fin n → k) (a : D.O), cv v = T c → v ≫ o.act.act a = 1 →
      (f a).mulVec c = 0 := by
    intro v c a hc h
    apply Tinj
    rw [← keyf, ← hc, T0]
    apply Over.OverMorphism.ext
    have h' := congrArg Over.Hom.left h
    rw [Over.comp_left, one_left'] at h'
    rw [Over.comp_left, one_left', cvl, h']
    change spMap (algebraMap k (DualNumber k)) ≫ η[o.A].left =
      (spMap (algebraMap k (DualNumber k)) ≫ spMap (RingHom.id k)) ≫ η[o.A].left
    rw [hid, Category.comp_id]
  let φ : 𝓞 D.F →+* Matrix (Fin n) (Fin n) k := f.comp (algebraMap (𝓞 D.F) D.O)
  have hρk : (r : k) ^ 2 - D.tr * r + D.nm = 0 := by
    have := congrArg β b.ρ_root
    simpa [hr] using this
  have hδ : ((D.tr - 2 * r : ℤ) : k) ≠ 0 := fun h => by
    refine D.disc_p ((CharP.intCast_eq_zero_iff k p _).1 ?_)
    push_cast at h ⊢
    linear_combination (D.tr - 2 * r : k) * h - 4 * hρk
  obtain ⟨q, hq⟩ : (p : ℤ) ∣ r ^ 2 - D.tr * r + D.nm :=
    (CharP.intCast_eq_zero_iff k p _).1 (by push_cast; exact hρk)
  have hsq : ∀ l : ℕ, φ ((D.ω - r) ^ (l + 1)) = (((D.tr - 2 * r : ℤ) : k) ^ l) • φ (D.ω - r) := by
    have hq' : (r : 𝓞 D.F) ^ 2 - D.tr * r + D.nm = p * q := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 D.F) hq
    have e₁ : (D.ω - r) * (D.ω - r) = ((D.tr - 2 * r : ℤ) : 𝓞 D.F) * (D.ω - r) - (p : 𝓞 D.F) * q := by
      push_cast
      linear_combination D.ω * D.tr_eq - D.nm_eq - hq'
    have hp0 : φ (p : 𝓞 D.F) = 0 := by
      rw [map_natCast, ← map_natCast (algebraMap k (Matrix (Fin n) (Fin n) k)), CharP.cast_eq_zero, map_zero]
    have e₂ : φ (D.ω - r) * φ (D.ω - r) = ((D.tr - 2 * r : ℤ) : k) • φ (D.ω - r) := by
      rw [← map_mul, e₁, map_sub φ (_ * _), map_mul, map_mul φ (p : 𝓞 D.F), hp0, zero_mul, sub_zero, map_intCast,
        Int.cast_smul_eq_zsmul, zsmul_eq_mul]
    intro l
    induction l with
    | zero => simp
    | succ l ih => rw [pow_succ, map_mul, ih, smul_mul_assoc, e₂, smul_smul, pow_succ]
  let Eig : Fin D.a → Submodule k (Fin n → k) := fun i =>
    ⨅ c, LinearMap.ker (Matrix.mulVecLin (φ c) - β.comp (b.t i) c • LinearMap.id)
  have memE : ∀ i x, x ∈ Eig i ↔ ∀ c, (φ c).mulVec x = β (b.t i c) • x := by
    intro i x
    simp [Eig, Submodule.mem_iInf, sub_eq_zero]
  have hdim : ∀ i, Module.finrank k (Eig i) = D.m := fun i =>
    (GlobalTheory.LieCoordMult.lieMult_iff_finrank_eig k o.A (𝓞 D.F) (o.act.toF D) n k (RingHom.id k) T φ Tinj Trng
      Tadd Tsm (fun c v => keyf _ v) (β.comp (b.t i)) D.m).1 (o.lieRank k (spMap (RingHom.id k)) β hx i)
  have dec : ∀ (v : epsR k ⟶ o.A) (c : Fin n → k), cv v = T c →
      v ≫ o.act.act (algebraMap (𝓞 D.F) D.O ((D.ω - r) ^ L)) = 1 →
      v ≫ o.act.act (algebraMap (𝓞 D.F) D.O (1 - e)) = 1 →
      ∃ u : Fin D.a → Fin n → k, (∀ j, u j ∈ Eig j) ∧ c = ∑ j, β (b.t j e) • u j := by
    intro v c hc h₁ h₂
    have hωc : (f (algebraMap (𝓞 D.F) D.O D.ω)).mulVec c = β b.ρ • c := by
      have h0 : (φ ((D.ω - r) ^ L)).mulVec c = 0 := kill v c _ hc h₁
      have h1 : (φ ((D.ω - r) ^ (L + 1))).mulVec c = 0 := by
        rw [pow_succ', map_mul, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
      rw [hsq, Matrix.smul_mulVec, smul_eq_zero, or_iff_right (pow_ne_zero _ hδ), map_sub, Matrix.sub_mulVec,
        sub_eq_zero, map_intCast] at h1
      refine h1.trans ?_
      rw [hr]
      simp
    have htan : IsTanScal o.act (spMap (RingHom.id k)) (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) (T c) := by
      refine ⟨(Trng _).2 ⟨c, rfl⟩, ?_⟩
      rw [keyf, hωc, Tsm]
    obtain ⟨wv, hwv, hprod⟩ := o.lie k β (spMap (RingHom.id k)) hx (T c) htan
    choose u hu using fun j => (Trng (wv j)).1 (hwv j 0).1
    have hc' : c = ∑ j, u j := by
      apply Tinj
      rw [hprod, ← prod_ofFn_eq' T T0 Tadd]
      simp only [hu]
    have hE : ∀ j, u j ∈ Eig j := fun j => by
      rw [memE]
      intro c'
      apply Tinj
      apply Over.OverMorphism.ext
      rw [Tsm]
      change (T ((f _).mulVec _)).left = _
      rw [← keyf, hu j]
      exact (hwv j c').2
    refine ⟨u, hE, ?_⟩
    have h0 : (φ (1 - e)).mulVec c = 0 := kill v c _ hc h₂
    rw [map_sub, map_one, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
    rw [h0, hc', Matrix.mulVec_sum]
    exact Finset.sum_congr rfl fun j _ => (memE j _).1 (hE j) e
  obtain ⟨c₁, hc₁⟩ := coord v₁ ht₁
  obtain ⟨c₂, hc₂⟩ := coord v₂ ht₂
  obtain ⟨u₁, hu₁, e₁⟩ := dec v₁ c₁ hc₁ hk₁ hf₁
  obtain ⟨u₂, hu₂, e₂⟩ := dec v₂ c₂ hc₂ hk₂ hf₂
  obtain ⟨c, hc⟩ : ∃ c : k, c₁ = c • c₂ ∨ c₂ = c • c₁ := by
    by_cases h : ∃ i, β (b.t i e) ≠ 0
    · obtain ⟨i, hi⟩ := h
      have mem : ∀ u : Fin D.a → Fin n → k, (∀ j, u j ∈ Eig j) → ∑ j, β (b.t j e) • u j ∈ Eig i := by
        intro u hu
        refine Submodule.sum_mem _ fun j _ => ?_
        by_cases hj : β (b.t j e) = 0
        · rw [hj, zero_smul]; exact Submodule.zero_mem _
        · obtain rfl := he i j hi hj
          exact Submodule.smul_mem _ _ (hu _)
      obtain ⟨z, hz⟩ := finrank_le_one_iff.mp ((hdim i).trans hm).le
      obtain ⟨a₁, ha₁⟩ := hz ⟨c₁, e₁ ▸ mem u₁ hu₁⟩
      obtain ⟨a₂, ha₂⟩ := hz ⟨c₂, e₂ ▸ mem u₂ hu₂⟩
      have f₁ : a₁ • (z : Fin n → k) = c₁ := congrArg Subtype.val ha₁
      have f₂ : a₂ • (z : Fin n → k) = c₂ := congrArg Subtype.val ha₂
      by_cases h : a₂ = 0
      · refine ⟨0, Or.inr ?_⟩
        rw [← f₂, h, zero_smul, zero_smul]
      · refine ⟨a₁ / a₂, Or.inl ?_⟩
        rw [← f₁, ← f₂, smul_smul, div_mul_cancel₀ _ h]
    · push Not at h
      refine ⟨0, Or.inl ?_⟩
      rw [e₁]
      simp [h]
  refine ⟨c, hc.imp (fun h => ?_) (fun h => ?_)⟩
  · rw [← cvl v₁, ← cvl v₂, hc₁, hc₂, h, Tsm]
  · rw [← cvl v₁, ← cvl v₂, hc₁, hc₂, h, Tsm]

end GlobalTheory.UPel.HT.ES.KerFin

namespace GlobalTheory.UPel.HT.ES.KerFin

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {S : Scheme.{0}}
  {s : S ⟶ Sp R}

theorem act_zero (o : Obj b N s) : o.act.act 0 = 1 := by
  have h := o.act.add 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

theorem act_natCast (o : Obj b N s) (n : ℕ) : o.act.act (n : D.O) = (𝟙 o.A) ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, act_zero, pow_zero]
  | succ n ih => rw [Nat.cast_succ, o.act.add, ih, o.act.one, pow_succ]

def transp {o o' : Obj b N s} (ψ : o.A ⟶ o'.A) (hψ : IsMonHom ψ)
    (hlin : ∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ o'.act.act c') {T : Over S} (x : T ⟶ o.A) : Ideal (𝓞 D.F) where
  carrier := {z | (x ≫ o.act.act (algebraMap (𝓞 D.F) D.O z)) ≫ ψ = 1}
  add_mem' := by
    intro z z' hz hz'
    simp only [Set.mem_setOf_eq] at hz hz' ⊢
    rw [map_add, o.act.add, MonObj.comp_mul, MonObj.mul_comp, hz, hz', _root_.mul_one]
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    rw [map_zero, act_zero, MonObj.comp_one, MonObj.one_comp]
  smul_mem' := by
    intro c z hz
    simp only [Set.mem_setOf_eq] at hz ⊢
    have := o'.act.hom (algebraMap (𝓞 D.F) D.O c)
    rw [smul_eq_mul, map_mul, o.act.mul, ← Category.assoc, Category.assoc _ _ ψ, hlin, ← Category.assoc, hz,
      MonObj.one_comp]

theorem mem_transp {o o' : Obj b N s} {ψ : o.A ⟶ o'.A} (hψ : IsMonHom ψ)
    (hlin : ∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ o'.act.act c') {T : Over S} (x : T ⟶ o.A) (z : 𝓞 D.F) :
    z ∈ transp ψ hψ hlin x ↔ (x ≫ o.act.act (algebraMap (𝓞 D.F) D.O z)) ≫ ψ = 1 := Iff.rfl

theorem kill_of_dvd {n : ℕ} {o o' : Obj b N s} {ψ : o.A ⟶ o'.A} (h : IsPIsog (p ^ n) o o' ψ) {T : Over S}
    (x : T ⟶ o.A) (hx : x ≫ ψ = 1) (z : 𝓞 D.F) (hz : (p : 𝓞 D.F) ^ n ∣ z) :
    x ≫ o.act.act (algebraMap (𝓞 D.F) D.O z) = 1 := by
  obtain ⟨φ, hφ, e, -⟩ := h.2.2.2.2.2
  obtain ⟨y, rfl⟩ := hz
  have := o.act.hom (algebraMap (𝓞 D.F) D.O y)
  rw [mul_comm, map_mul, o.act.mul, ← Nat.cast_pow, map_natCast, act_natCast, ← e, ← Category.assoc,
    ← Category.assoc, hx, MonObj.one_comp, MonObj.one_comp]

end GlobalTheory.UPel.HT.ES.KerFin

open GlobalTheory.UPel.HT.ES.KerFin in

theorem GlobalTheory.UPel.HT.ES.KerFin.finite_kernels : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → D.m = 1 → ∀ (c : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharP k p] (s : Sp k ⟶ Sp R) (o : Obj b N s), Set.Finite {P : ∀ T : Over (Sp k), (T ⟶ o.A) → Prop | ∃ (o' : Obj b N s) (ψ : o.A ⟶ o'.A), IsPIsog c o o' ψ ∧ P = fun T x => x ≫ ψ = 1} := by
  intro p _ D R _ b N _ _ hm c k _ _ _ s o
  classical
  obtain ⟨β, rfl⟩ : ∃ β : R →+* k, spMap β = s := ⟨(Spec.preimage s).hom, by simp [spMap]⟩
  by_cases hc : ∃ n : ℕ, c = p ^ n
  swap
  · refine Set.finite_empty.subset ?_
    rintro P ⟨o', ψ, h, -⟩
    exact (hc h.1).elim
  obtain ⟨n, rfl⟩ := hc
  have hp : (p : ℕ).Prime := Fact.out
  have hρk : (β b.ρ) ^ 2 - D.tr * β b.ρ + D.nm = 0 := by
    have := congrArg β b.ρ_root
    simpa using this
  obtain ⟨r, hr⟩ : ∃ r : ℤ, β b.ρ = r := by
    obtain ⟨r, hq⟩ := D.split
    have h1 := (CharP.intCast_eq_zero_iff k p _).2 hq
    push_cast at h1
    have hprod : (β b.ρ - r) * (β b.ρ - (D.tr - r)) = 0 := by linear_combination hρk - h1
    rcases mul_eq_zero.1 hprod with h | h
    · exact ⟨r, sub_eq_zero.1 h⟩
    · exact ⟨D.tr - r, by push_cast; exact sub_eq_zero.1 h⟩
  obtain ⟨q, hq⟩ : (p : ℤ) ∣ r ^ 2 - D.tr * r + D.nm :=
    (CharP.intCast_eq_zero_iff k p _).1 (by push_cast; rw [← hr]; exact hρk)
  have hq' : (r : 𝓞 D.F) ^ 2 - D.tr * r + D.nm = p * q := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 D.F) hq
  let u : 𝓞 D.F := D.ω - r
  let u' : 𝓞 D.F := D.ω - (D.tr - r)
  have huu : u * u' = p * (-q) := by
    simp only [u, u']
    linear_combination D.ω * D.tr_eq - D.nm_eq - hq'
  have hbar : D.bar u' = -u := by
    simp only [u, u', map_sub, map_intCast]
    linear_combination D.tr_eq
  let Q : 𝓞 D.F := (p : 𝓞 D.F) ^ (n + 1)
  have hQ0 : Q ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hp.ne_zero)
  have hQn : (p : 𝓞 D.F) ^ n ∣ Q := pow_dvd_pow _ (Nat.le_succ n)
  haveI : Finite (𝓞 D.F ⧸ Ideal.span {Q}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by rwa [Ne, Ideal.span_singleton_eq_bot])
  obtain ⟨κ, _, e, hsum, hidem, hloc⟩ := exists_local_idempotents Q
  rw [Ideal.mem_span_singleton] at hsum
  simp only [Ideal.mem_span_singleton] at hidem
  let ac : 𝓞 D.F → (o.A ⟶ o.A) := fun z => o.act.act (algebraMap (𝓞 D.F) D.O z)
  haveI hac : ∀ z, IsMonHom (ac z) := fun z => o.act.hom _
  have acmul : ∀ z z', ac z ≫ ac z' = ac (z' * z) := fun z z' => by
    simp only [ac]; rw [map_mul, o.act.mul]
  let g : κ → (o.A ⟶ o.A ⊗ o.A) := fun i => lift (ac (u ^ n)) (ac (1 - e i))
  haveI hg : ∀ i, IsMonHom (g i) := fun i => by simp only [g]; infer_instance
  have hfin := fun i => finite_subgroups o.ab (AbelianSchemeGerms.isAbelianScheme_tensor _ _ o.ab o.ab) (ac Q)
    (GlobalTheory.HTTors.isIsogDeg_intAct p D R b N _ _ o Q hQ0) (g i) (fun v₁ v₂ h₁ h₂ k₁ k₂ => by
      rw [comp_lift_eq_one] at k₁ k₂
      refine tangent_line hm β o r hr n (e i) (fun j j' hj hj' => ?_) v₁ v₂ h₁ h₂ k₁.1 k₂.1 k₁.2 k₂.2
      by_contra hne
      have hQ : ∀ l, Q ∈ RingHom.ker (β.comp (b.t l)) := fun l => by
        rw [RingHom.mem_ker, map_pow, map_natCast, CharP.cast_eq_zero, zero_pow (Nat.succ_ne_zero n)]
      exact b.apart j j' hne k β (hloc i _ _ (RingHom.ker_isPrime _) (RingHom.ker_isPrime _) (hQ j) (hQ j') hj hj'))
  let f : (∀ T : Over (Sp k), (T ⟶ o.A) → Prop) → κ → (∀ T : Over (Sp k), (T ⟶ o.A) → Prop) :=
    fun P i T x => x ≫ ac Q = 1 ∧ x ≫ g i = 1 ∧ P T x
  refine Set.Finite.of_finite_image (f := f) ((Set.Finite.pi' hfin).subset ?_) ?_
  · rintro _ ⟨P, ⟨o', ψ, h, rfl⟩, rfl⟩ i
    exact ⟨o'.A, inferInstance, ψ, o'.ab, h.2.1, rfl⟩
  have step : ∀ (o₁ o₂ : Obj b N (spMap β)) (ψ₁ : o.A ⟶ o₁.A) (ψ₂ : o.A ⟶ o₂.A), IsPIsog (p ^ n) o o₁ ψ₁ →
      IsPIsog (p ^ n) o o₂ ψ₂ → f (fun T x => x ≫ ψ₁ = 1) = f (fun T x => x ≫ ψ₂ = 1) →
      ∀ (T : Over (Sp k)) (x : T ⟶ o.A), x ≫ ψ₁ = 1 → (x ≫ ac (u' ^ n)) ≫ ψ₂ = 1 := by
    intro o₁ o₂ ψ₁ ψ₂ h₁ h₂ heq T x hx
    haveI := h₁.2.1
    haveI := h₂.2.1
    have hi : ∀ i, e i * u' ^ n ∈ transp ψ₂ h₂.2.1 h₂.2.2.1 x := fun i => by
      refine ((congrFun (congrFun (congrFun heq i) T) (x ≫ ac (e i * u' ^ n))).mp ⟨?_, ?_, ?_⟩).2.2
      · rw [Category.assoc, acmul]
        exact kill_of_dvd h₁ x hx _ (hQn.mul_right _)
      · rw [comp_lift_eq_one, Category.assoc, Category.assoc, acmul, acmul]
        refine ⟨kill_of_dvd h₁ x hx _ ⟨(-q) ^ n * e i, ?_⟩, kill_of_dvd h₁ x hx _ ?_⟩
        · rw [mul_left_comm, ← mul_pow, huu, mul_pow]; ring
        · rw [← _root_.mul_assoc]; exact (hQn.trans (hidem i)).mul_right _
      · change (x ≫ o.act.act _) ≫ ψ₁ = 1
        haveI := o₁.act.hom (algebraMap (𝓞 D.F) D.O (e i * u' ^ n))
        rw [Category.assoc, h₁.2.2.1, ← Category.assoc, hx, MonObj.one_comp]
    have h0 : ((∑ i, e i) - 1) * u' ^ n ∈ transp ψ₂ h₂.2.1 h₂.2.2.1 x := by
      rw [mem_transp, kill_of_dvd h₁ x hx _ ((hQn.trans hsum).mul_right _), MonObj.one_comp]
    have := Ideal.sub_mem _ (Ideal.sum_mem _ (t := Finset.univ) fun i _ => hi i) h0
    rw [← Finset.sum_mul, ← sub_mul, sub_sub_cancel, _root_.one_mul] at this
    exact this
  have key : ∀ (o₁ o₂ : Obj b N (spMap β)) (ψ₁ : o.A ⟶ o₁.A) (ψ₂ : o.A ⟶ o₂.A), IsPIsog (p ^ n) o o₁ ψ₁ →
      IsPIsog (p ^ n) o o₂ ψ₂ → f (fun T x => x ≫ ψ₁ = 1) = f (fun T x => x ≫ ψ₂ = 1) →
      ∀ (T : Over (Sp k)) (x : T ⟶ o.A), x ≫ ψ₁ = 1 → x ≫ ψ₂ = 1 := by
    intro o₁ o₂ ψ₁ ψ₂ h₁ h₂ heq T x hx
    haveI := h₂.2.1
    have a₁ : u' ^ n ∈ transp ψ₂ h₂.2.1 h₂.2.2.1 x := step o₁ o₂ ψ₁ ψ₂ h₁ h₂ heq T x hx
    have a₂ : (-u) ^ n ∈ transp ψ₂ h₂.2.1 h₂.2.2.1 x := by
      have := star_ker_le h₁ h₂ _ (step o₂ o₁ ψ₂ ψ₁ h₂ h₁ heq.symm) T x hx
      rw [D.star_F, MulOpposite.unop_op, map_pow, hbar] at this
      exact this
    have a₃ : (p : 𝓞 D.F) ^ n ∈ transp ψ₂ h₂.2.1 h₂.2.2.1 x := by
      rw [mem_transp, kill_of_dvd h₁ x hx _ dvd_rfl, MonObj.one_comp]
    have htop : transp ψ₂ h₂.2.1 h₂.2.2.1 x = ⊤ := by
      by_contra hne
      obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hne
      have b₁ := h𝔪.isPrime.mem_of_pow_mem n (hle a₁)
      have b₂ := h𝔪.isPrime.mem_of_pow_mem n (hle a₂)
      have b₃ := h𝔪.isPrime.mem_of_pow_mem n (hle a₃)
      obtain ⟨y, z, hyz⟩ := ((Nat.prime_iff_prime_int.1 hp).coprime_iff_not_dvd.2 D.disc_p)
      have hyz' : (y : 𝓞 D.F) * p + z * (D.tr ^ 2 - 4 * D.nm) = 1 := by
        exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 D.F) hyz
      refine h𝔪.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
      have : (1 : 𝓞 D.F) = (y - 4 * z * q) * p + z * (u' + -u) * (u' + -u) := by
        simp only [u, u']
        linear_combination -hyz' - 4 * z * hq'
      rw [this]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ b₃) (Ideal.mul_mem_left _ _ (Ideal.add_mem _ b₁ b₂))
    have h1 : (1 : 𝓞 D.F) ∈ transp ψ₂ h₂.2.1 h₂.2.2.1 x := htop ▸ Submodule.mem_top
    rwa [mem_transp, map_one, o.act.one, Category.comp_id] at h1
  rintro _ ⟨o₁, ψ₁, h₁, rfl⟩ _ ⟨o₂, ψ₂, h₂, rfl⟩ heq
  funext T x
  exact propext ⟨key o₁ o₂ ψ₁ ψ₂ h₁ h₂ heq T x, key o₂ o₁ ψ₂ ψ₁ h₂ h₁ heq.symm T x⟩
