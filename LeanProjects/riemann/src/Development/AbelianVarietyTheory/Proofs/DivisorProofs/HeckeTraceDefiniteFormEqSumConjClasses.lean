import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.TraceDefinitePairsEqAutomorphicTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateEigenSubDegreeEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldedEqOrbitalReps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDoubleCosetDefiniteHermitianFormLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteFormStabilizerFiniteAwayFromPStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTestProductSupportFiniteLeftCosetsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairAdelicProdUnramifiedEmbeddingInjec

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.HeckeTrace

variable {Γ H V : Type} [Group Γ] [Group H] [AddCommGroup V] [Module ℂ V]

theorem out_smul (K : Subgroup H) (k : H) (h : H ⧸ K) : ∃ κ ∈ K, ((k • h : H ⧸ K).out : H) = k * h.out * κ := by
  have e : (k • h : H ⧸ K) = QuotientGroup.mk (k * h.out) := by
    conv_lhs => rw [← QuotientGroup.out_eq' h]
    rfl
  obtain ⟨κ, hκ⟩ := QuotientGroup.mk_out_eq_mul K (k * h.out)
  exact ⟨κ, κ.2, by rw [e, hκ]⟩

def heckeFun (K : Subgroup H) (F : H → ℂ) (φ : H → V) (g : H) : V :=
  ∑ᶠ h : H ⧸ K, F h.out • φ (g * h.out)

theorem support_sub (K : Subgroup H) (F : H → ℂ) (v : H ⧸ K → V) :
    Function.support (fun h : H ⧸ K => F h.out • v h) ⊆ Function.support (fun h : H ⧸ K => F h.out) :=
  Function.support_smul_subset_left _ _

theorem heckeFun_mul_right (K : Subgroup H) (F : H → ℂ) (hF : ∀ k ∈ K, ∀ k' ∈ K, ∀ g, F (k * g * k') = F g)
    (φ : H → V) (hφ : ∀ k ∈ K, ∀ g, φ (g * k) = φ g) (g k : H) (hk : k ∈ K) :
    heckeFun K F φ (g * k) = heckeFun K F φ g := by
  unfold heckeFun
  rw [← finsum_comp_equiv (MulAction.toPerm (k⁻¹ : H) : Equiv.Perm (H ⧸ K)).symm.symm]
  refine finsum_congr fun h => ?_
  simp only [Equiv.symm_symm, MulAction.toPerm_apply]
  obtain ⟨κ, hκ, he⟩ := out_smul K k⁻¹ h
  rw [he]
  have h1 : F (k⁻¹ * h.out * κ) = F h.out := hF _ (K.inv_mem hk) _ hκ _
  have h2 : φ (g * k * (k⁻¹ * h.out * κ)) = φ (g * h.out) := by
    rw [show g * k * (k⁻¹ * h.out * κ) = g * h.out * κ by group, hφ _ hκ]
  rw [h1, h2]

theorem heckeFun_mul_left (ι : Γ →* H) (K : Subgroup H) (ξ : Representation ℂ Γ V) (F : H → ℂ)
    (hs : (Function.support (fun q : H ⧸ K => F q.out)).Finite)
    (φ : H → V) (hφ : ∀ γ g, φ (ι γ * g) = ξ γ (φ g)) (γ : Γ) (g : H) :
    heckeFun K F φ (ι γ * g) = ξ γ (heckeFun K F φ g) := by
  unfold heckeFun
  rw [map_finsum _ (hs.subset (support_sub K F _))]
  refine finsum_congr fun h => ?_
  rw [map_smul, mul_assoc, hφ]

def hecke (ι : Γ →* H) (K : Subgroup H) (ξ : Representation ℂ Γ V) (F : H → ℂ)
    (hF : ∀ k ∈ K, ∀ k' ∈ K, ∀ g, F (k * g * k') = F g)
    (hs : (Function.support (fun q : H ⧸ K => F q.out)).Finite) :
    GlobalTheory.LKDef.HeckeTraceForms.forms ι K ξ →ₗ[ℂ] GlobalTheory.LKDef.HeckeTraceForms.forms ι K ξ where
  toFun φ := ⟨heckeFun K F (φ : H → V), fun γ g => heckeFun_mul_left ι K ξ F hs _ (φ.2.1) γ g,
    fun k hk g => heckeFun_mul_right K F hF _ (φ.2.2) g k hk⟩
  map_add' φ ψ := by
    apply Subtype.ext; funext g
    show heckeFun K F (fun x => (φ : H → V) x + (ψ : H → V) x) g = heckeFun K F (φ : H → V) g + heckeFun K F (ψ : H → V) g
    unfold heckeFun
    simp only [smul_add]
    exact finsum_add_distrib (hs.subset (support_sub K F _)) (hs.subset (support_sub K F _))
  map_smul' c φ := by
    apply Subtype.ext; funext g
    show heckeFun K F (fun x => c • (φ : H → V) x) g = c • heckeFun K F (φ : H → V) g
    unfold heckeFun
    rw [smul_finsum]
    refine finsum_congr fun h => ?_
    rw [smul_comm]

theorem isHecke_hecke (ι : Γ →* H) (K : Subgroup H) (ξ : Representation ℂ Γ V) (F : H → ℂ)
    (hF : ∀ k ∈ K, ∀ k' ∈ K, ∀ g, F (k * g * k') = F g)
    (hs : (Function.support (fun q : H ⧸ K => F q.out)).Finite) :
    GlobalTheory.LKDef.HeckeTraceForms.IsHecke ι K ξ F (hecke ι K ξ F hF hs) := fun _ _ => rfl

theorem heckeTrace_eq (ι : Γ →* H) (K : Subgroup H) (ξ : Representation ℂ Γ V) (F : H → ℂ)
    (hF : ∀ k ∈ K, ∀ k' ∈ K, ∀ g, F (k * g * k') = F g)
    (hs : (Function.support (fun q : H ⧸ K => F q.out)).Finite) :
    GlobalTheory.LKDef.HeckeTraceForms.heckeTrace ι K ξ F =
      LinearMap.trace ℂ (GlobalTheory.LKDef.HeckeTraceForms.forms ι K ξ) (hecke ι K ξ F hF hs) := by
  have h : ∃ T, GlobalTheory.LKDef.HeckeTraceForms.IsHecke ι K ξ F T := ⟨_, isHecke_hecke ι K ξ F hF hs⟩
  rw [GlobalTheory.LKDef.HeckeTraceForms.heckeTrace, dif_pos h]
  congr 1
  apply LinearMap.ext; intro φ; apply Subtype.ext; funext g
  rw [h.choose_spec φ g]; rfl

end GlobalTheory.HeckeTrace

namespace GlobalTheory.HeckeTrace

variable {Γ H V : Type} [Group Γ] [Group H] [AddCommGroup V] [Module ℂ V]

theorem isConj_map {A B : Type} [Group A] [Group B] (e : A ≃* B) {a b : A} (h : IsConj a b) : IsConj (e a) (e b) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  exact isConj_iff.2 ⟨e c, by rw [← map_inv, ← map_mul, ← map_mul, hc]⟩

theorem mk_out_conj (c : ConjClasses Γ) : ConjClasses.mk (Quotient.out c) = c := Quotient.out_eq c

theorem heckeTrace_eq_orbital [FiniteDimensional ℂ V] (ι : Γ →* H) (hι : Function.Injective ι) (K : Subgroup H)
    (ξ : Representation ℂ Γ V) (F : H → ℂ)
    (hF : ∀ k ∈ K, ∀ k' ∈ K, ∀ g, F (k * g * k') = F g)
    (hs : (Function.support (fun q : H ⧸ K => F q.out)).Finite)
    (hQ : Finite (DoubleCoset.Quotient (ι.range : Set H) (K : Set H)))
    (hloc : ∀ x : H, Finite (GlobalTheory.LKLoc.locPart ι.range K x)) :
    GlobalTheory.LKDef.HeckeTraceForms.heckeTrace ι K ξ F =
      ∑ᶠ c : ConjClasses Γ, LinearMap.trace ℂ V (ξ (Quotient.out c)) *
        ∑ᶠ q : DoubleCoset.Quotient ((Subgroup.centralizer {ι (Quotient.out c)} ⊓ ι.range : Subgroup H) : Set H) (K : Set H),
          (1 / (Nat.card (GlobalTheory.LKLoc.locPart (Subgroup.centralizer {ι (Quotient.out c)} ⊓ ι.range) K q.out) : ℂ)) *
            F (q.out⁻¹ * ι (Quotient.out c) * q.out) := by
  let e : Γ ≃* ι.range := MonoidHom.ofInjective hι
  have he : ∀ γ : Γ, ((e γ : ι.range) : H) = ι γ := fun γ => MonoidHom.ofInjective_apply hι
  let ξ' : Representation ℂ ι.range V := ξ.comp e.symm.toMonoidHom
  have hξ : ∀ γ : Γ, ξ' (e γ) = ξ γ := fun γ => by
    simp only [ξ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  have hM : ∀ φ : H → V, φ ∈ GlobalTheory.LKDef.HeckeTraceForms.forms ι K ξ ↔
      (∀ γ : ι.range, ∀ g, φ ((γ : H) * g) = ξ' γ (φ g)) ∧ ∀ k ∈ K, ∀ g, φ (g * k) = φ g := by
    intro φ
    change ((∀ γ g, φ (ι γ * g) = ξ γ (φ g)) ∧ ∀ k ∈ K, ∀ g, φ (g * k) = φ g) ↔ _
    refine and_congr_left' ⟨fun h γ' g => ?_, fun h γ g => ?_⟩
    · obtain ⟨γ, rfl⟩ := e.surjective γ'
      rw [he, hξ, h]
    · rw [← he, h, hξ]
  rw [heckeTrace_eq ι K ξ F hF hs,
    GlobalTheory.FinTF.finite_trace_formula H ι.range K V ξ' hQ hloc F hF hs _ hM _ (isHecke_hecke ι K ξ F hF hs)]
  let R : Set ι.range := Set.range (fun c : ConjClasses Γ => e (Quotient.out c))
  have hcls : ∀ (c : ConjClasses Γ) (γ : Γ), IsConj (e γ) (e (Quotient.out c)) → c = ConjClasses.mk γ := by
    intro c γ h
    have h' : IsConj γ (Quotient.out c) := by
      simpa using isConj_map e.symm h
    rw [← mk_out_conj c]
    exact (ConjClasses.mk_eq_mk_iff_isConj.2 h').symm
  have hR : ∀ γ' : ι.range, ∃! ρ, ρ ∈ R ∧ IsConj γ' ρ := by
    intro γ'
    obtain ⟨γ, rfl⟩ := e.surjective γ'
    refine ⟨e (Quotient.out (ConjClasses.mk γ)), ⟨⟨_, rfl⟩, isConj_map e ?_⟩, ?_⟩
    · exact ConjClasses.mk_eq_mk_iff_isConj.1 (mk_out_conj (ConjClasses.mk γ)).symm
    · rintro ρ ⟨⟨c, rfl⟩, hρ⟩
      rw [hcls c γ hρ]
  have hinj : Function.Injective (fun c : ConjClasses Γ => e (Quotient.out c)) := fun a b h => by
    rw [← mk_out_conj a, ← mk_out_conj b, e.injective h]
  rw [GlobalTheory.FinTrace.unfolded_eq_orbital_reps H ι.range K V ξ' hQ hloc F hF hs R hR, finsum_mem_range hinj]
  refine finsum_congr fun c => ?_
  simp only [hξ, he]
  rfl

end GlobalTheory.HeckeTrace

namespace GlobalTheory.HeckeTrace

variable {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂]

theorem mem_map_conj {H : Type} [Group H] (K : Subgroup H) (x g : H) :
    g ∈ K.map (MulAut.conj x).toMonoidHom ↔ x⁻¹ * g * x ∈ K := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    simpa [mul_assoc] using hk
  · intro h
    exact ⟨_, h, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩

theorem locPart_map_eq (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂)
    (C : Subgroup Γ) (x : G₁ × G₂) :
    GlobalTheory.LKLoc.locPart (C.map (ι₁.prod ι₂)) (K₁.prod K₂) x = (stab ι₁ ι₂ K₁ K₂ x ⊓ C).map (ι₁.prod ι₂) := by
  ext δ
  rw [GlobalTheory.FinTF.mem_locPart_iff]
  simp only [Subgroup.mem_map, Subgroup.mem_inf, stab, Subgroup.mem_comap, mem_map_conj, Subgroup.mem_prod]
  constructor
  · rintro ⟨⟨w, hw, rfl⟩, h1, h2⟩
    exact ⟨w, ⟨⟨(mem_map_conj _ _ _).2 (by simpa using h1), (mem_map_conj _ _ _).2 (by simpa using h2)⟩, hw⟩, rfl⟩
  · rintro ⟨w, ⟨⟨h1, h2⟩, hw⟩, rfl⟩
    exact ⟨⟨w, hw, rfl⟩, by simpa using (mem_map_conj _ _ _).1 h1, by simpa using (mem_map_conj _ _ _).1 h2⟩

theorem cent_map_eq (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (hι : Function.Injective (ι₁.prod ι₂)) (γ : Γ) :
    Subgroup.centralizer {(ι₁.prod ι₂) γ} ⊓ (ι₁.prod ι₂).range =
      (Subgroup.centralizer {γ}).map (ι₁.prod ι₂) := by
  ext z
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, MonoidHom.mem_range, Subgroup.mem_map]
  constructor
  · rintro ⟨hc, w, rfl⟩
    refine ⟨w, hι ?_, rfl⟩
    rw [map_mul, map_mul, hc]
  · rintro ⟨w, hw, rfl⟩
    exact ⟨by rw [← map_mul, ← map_mul, hw], w, rfl⟩

theorem orbital_eq_centSum (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (hι : Function.Injective (ι₁.prod ι₂))
    (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (f₁ : G₁ → ℂ) (f₂ : G₂ → ℂ) (γ : Γ) :
    ∑ᶠ q : DoubleCoset.Quotient ((Subgroup.centralizer {(ι₁.prod ι₂) γ} ⊓ (ι₁.prod ι₂).range : Subgroup (G₁ × G₂)) :
        Set (G₁ × G₂)) ((K₁.prod K₂ : Subgroup (G₁ × G₂)) : Set (G₁ × G₂)),
      (1 / (Nat.card (GlobalTheory.LKLoc.locPart (Subgroup.centralizer {(ι₁.prod ι₂) γ} ⊓ (ι₁.prod ι₂).range)
          (K₁.prod K₂) q.out) : ℂ)) *
        (fun h : G₁ × G₂ => f₁ h.1 * f₂ h.2) (q.out⁻¹ * (ι₁.prod ι₂) γ * q.out) =
      centSum ι₁ ι₂ (MonoidHom.id G₂) K₁ K₂ 1 f₁ f₂ γ := by
  rw [cent_map_eq ι₁ ι₂ hι γ, centSum]
  refine finsum_congr fun q => ?_
  rw [locPart_map_eq, Subgroup.card_map_of_injective hι, one_div]
  simp [term]

end GlobalTheory.HeckeTrace

namespace GlobalTheory.HeckeTrace

variable {p : ℕ} [Fact p.Prime]

theorem emb_injective {G : HTGroup p} (B : GlobalTheory.LKDef.DForm G) : Function.Injective B.emb := by
  haveI : Nontrivial (AfP p) := GlobalTheory.LKMid.finiteAdeleRingAway_nontrivial p
  have hinj : Function.Injective (inC G (AfP p)) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap ℚ (AfP p)).injective
  have hq : Function.Injective (algebraMap ℚ (AfP p)) := (algebraMap ℚ (AfP p)).injective
  intro y z h
  have h1 := congrArg (fun w : G.GAf × Gr G 1 => ((w.1 : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ)) h
  simp only [GlobalTheory.LKDef.DForm.emb, GlobalTheory.LKDef.DForm.embAt, MonoidHom.prod_apply, GlobalTheory.LKCx.toAfF,
    MonoidHom.codRestrict_apply] at h1
  obtain ⟨ha, hb⟩ := Prod.ext_iff.1 h1
  simp at ha hb
  have ha' := congrArg (fun u : (AfP p ⊗[ℚ] G.C)ˣ => (u : AfP p ⊗[ℚ] G.C)) ha
  have hb' := congrArg (fun u : (AfP p)ˣ => (u : AfP p)) hb
  simp only [Units.coe_map, MonoidHom.coe_coe] at ha' hb'
  exact Subtype.ext (Prod.ext (Units.ext (hinj ha')) (Units.ext (hq hb')))

end GlobalTheory.HeckeTrace

namespace GlobalTheory.HeckeTrace

theorem dform_trace_eq : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 →
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ξ : Representation ℂ (G.Cˣ × ℚˣ) V)
    (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
    ∀ B : GlobalTheory.LKDef.DForm G,
      B.trace ξ L.K.toSubgroup f K' f' =
        ∑ᶠ c : ConjClasses (GlobalTheory.LKCx.grp G B.β),
          LinearMap.trace ℂ V (ξ (Quotient.out c : GlobalTheory.LKCx.grp G B.β).1) *
            centSum (GlobalTheory.LKCx.toAfF G B.β B.trivAf.choose B.trivAf.choose_spec.choose B.trivAf.choose_spec.choose_spec)
              (GlobalTheory.LKCx.toP1 G B.β) (MonoidHom.id (Gr G 1)) L.K.toSubgroup K' 1 f f' (Quotient.out c) := by
  intro p _ G ha V _ _ _ ξ L f hfT hf K' f' hf'T hf' B
  have hinj := emb_injective B
  have hF : ∀ k ∈ L.K.toSubgroup.prod K', ∀ k' ∈ L.K.toSubgroup.prod K', ∀ g : G.GAf × Gr G 1,
      (fun h : G.GAf × Gr G 1 => f h.1 * f' h.2) (k * g * k') = (fun h : G.GAf × Gr G 1 => f h.1 * f' h.2) g := by
    intro k hk k' hk' g
    simp only [Prod.fst_mul, Prod.snd_mul]
    rw [hf _ hk.1 _ hk'.1, hf' _ hk.2 _ hk'.2]
  rw [GlobalTheory.LKDef.DForm.trace, heckeTrace_eq_orbital B.emb hinj _ _ _ hF
    (GlobalTheory.T.heckeTestProduct_support_finite_leftCosets p G L f hfT hf K' f' hf'T hf') (GlobalTheory.T.finite_doubleCoset_definiteHermitianForm_level p G ha L K' hf'T.1 B)
    (GlobalTheory.T.definiteForm_stabilizer_finite_away_from_p p G ha L K' hf'T.1 B)]
  refine finsum_congr fun c => ?_
  congr 1
  exact orbital_eq_centSum _ _ hinj _ _ f f' _

end GlobalTheory.HeckeTrace
