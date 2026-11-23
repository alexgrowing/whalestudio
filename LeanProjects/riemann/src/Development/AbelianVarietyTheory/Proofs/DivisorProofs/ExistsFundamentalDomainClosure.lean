import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.QDom

open scoped Pointwise

theorem isFundamentalDomain_inf {G : Type} [Group G] [MeasurableSpace G] {μ : Measure G}
    (hm : ∀ g : G, Measurable (g * ·)) (hinv : ∀ g : G, μ.map (g * ·) = μ)
    {Γ : Subgroup G} [Countable Γ] {D : Set G} (hD : IsFundamentalDomain Γ D μ) (S : Subgroup G) :
    ∃ 𝓓 : Set G, IsFundamentalDomain ↥(Γ ⊓ S) 𝓓 μ := by
  classical
  let Q' : Subgroup Γ := (Γ ⊓ S).subgroupOf Γ
  haveI : Countable (Γ ⧸ Q') := Function.Surjective.countable QuotientGroup.mk_surjective
  let rep : Γ ⧸ Q' → Γ := fun c => (Quotient.out c)⁻¹
  have hmp : ∀ g : G, MeasurePreserving (g * ·) μ μ := fun g => ⟨hm g, hinv g⟩
  have himg : ∀ (g : G) (s : Set G), g • s = (g⁻¹ * ·) ⁻¹' s := by
    intro g s; ext x; simp [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]
  have hnm : ∀ g : G, NullMeasurableSet (g • D) μ := fun g => by
    rw [himg]; exact hD.nullMeasurableSet.preimage (hmp g⁻¹).quasiMeasurePreserving
  refine ⟨⋃ c, ((rep c : Γ) : G) • D, ?_⟩
  refine IsFundamentalDomain.mk'' ?_ ?_ ?_ ?_
  · exact NullMeasurableSet.iUnion fun c => hnm _
  · filter_upwards [hD.ae_covers] with x hx
    obtain ⟨γ, hγ⟩ := hx
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul Q' γ
    have hQ : ((h : Γ) : G) ∈ Γ ⊓ S := (Subgroup.mem_subgroupOf).1 h.2
    refine ⟨⟨((h : Γ) : G)⁻¹, inv_mem hQ⟩, Set.mem_iUnion.2 ⟨(γ : Γ ⧸ Q'), ?_⟩⟩
    rw [himg, Set.mem_preimage]
    have e1 : ((rep (γ : Γ ⧸ Q') : Γ) : G)⁻¹ = (γ : G) * ((h : Γ) : G) := by
      simp only [rep, inv_inv]
      have := congrArg (fun y : Γ => (y : G)) hh
      simpa using this
    rw [e1]
    have : (γ : G) * ((h : Γ) : G) * ((⟨((h : Γ) : G)⁻¹, inv_mem hQ⟩ : ↥(Γ ⊓ S)) • x) = γ • x := by
      rw [Subgroup.smul_def, Subgroup.smul_def]
      simp [smul_eq_mul, mul_assoc]
    rw [this]; exact hγ
  · intro g hg
    have hsm : g • ⋃ c, ((rep c : Γ) : G) • D = ⋃ c, ((g : G) * ((rep c : Γ) : G)) • D := by
      rw [Set.smul_set_iUnion]
      refine Set.iUnion_congr fun c => ?_
      rw [← smul_smul]; rfl
    rw [hsm, AEDisjoint.iUnion_left_iff]
    intro c
    rw [AEDisjoint.iUnion_right_iff]
    intro c'
    have hgΓ : (g : G) ∈ Γ := (Subgroup.mem_inf.1 g.2).1
    let γ₁ : Γ := ⟨g, hgΓ⟩ * rep c
    have hne : γ₁ ≠ rep c' := by
      intro heq
      have hmem : (Quotient.out c)⁻¹ * Quotient.out c' ∈ Q' := by
        rw [Subgroup.mem_subgroupOf]
        have : (Quotient.out c')⁻¹ = ⟨g, hgΓ⟩ * (Quotient.out c)⁻¹ := by
          simpa [γ₁, rep] using heq.symm
        have h2 : (Quotient.out c)⁻¹ * Quotient.out c' = (⟨g, hgΓ⟩ : Γ)⁻¹ := by
          rw [← inv_inj, mul_inv_rev, inv_inv, this, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
        rw [h2]
        simpa using inv_mem g.2
      have hcc : c = c' := by
        rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c']
        exact (QuotientGroup.eq).2 hmem
      subst hcc
      apply hg
      have : (⟨g, hgΓ⟩ : Γ) = 1 := by simpa [γ₁] using heq
      ext; simpa using congrArg Subtype.val this
    exact hD.aedisjoint hne
  · intro g
    exact (hmp (g : G)).quasiMeasurePreserving

end GlobalTheory.QDom

namespace GlobalTheory.QDom

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem countable_numberField : Countable E :=
  Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm

theorem countable_ratU (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Countable (ratU σ J) := by
  classical
  haveI := countable_numberField (E := E)
  haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  have hmat : Countable (GL (Fin n) E) := Function.Injective.countable (f := fun A : GL (Fin n) E => (A : Matrix (Fin n) (Fin n) E)) Units.val_injective
  have hpre : ∀ x : ratU σ J, ∃ A : GL (Fin n) E, Matrix.GeneralLinearGroup.map (inclR (AF F)) A = ((x : UA σ J) : GL (Fin n) (AE F E)) := by
    intro x
    have := x.2
    unfold ratU at this
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_range] at this
    exact this
  choose f hf using hpre
  refine Function.Injective.countable (f := f) ?_
  intro x y hxy
  apply Subtype.ext; apply Subtype.ext
  rw [← hf x, ← hf y, hxy]

set_option synthInstance.maxHeartbeats 400000 in
theorem measurable_mul_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : UA σ J) :
    Measurable (g * ·) := by
  haveI : BorelSpace (UA σ J) := ⟨rfl⟩
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  apply Continuous.measurable
  apply Continuous.subtype_mk
  rw [Units.continuous_iff]
  constructor
  · simp only [Function.comp_def, Subgroup.coe_mul, Units.val_mul]
    exact continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtype_val)
  · simp only [Subgroup.coe_mul, mul_inv_rev, Units.val_mul]
    exact (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_mul continuous_const

end GlobalTheory.QDom

namespace GlobalTheory.QDom

theorem exists_fundamentalDomain_ratStab : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∃ 𝓓 : Set (UA σ G.V.J), IsFundamentalDomain ↥(ratU σ G.V.J ⊓ Subgroup.closure {g : UA σ G.V.J | mat g *ᵥ incV F H.x = incV F H.x}) 𝓓 G.M.μ := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' _ X om om' hT
  haveI := countable_ratU σ G.V.J
  have hgood := hT.geo.hM
  haveI := hgood.haar
  exact isFundamentalDomain_inf (measurable_mul_left σ G.V.J) (fun g => map_mul_left_eq_self G.M.μ g) hgood.dom _

end GlobalTheory.QDom
