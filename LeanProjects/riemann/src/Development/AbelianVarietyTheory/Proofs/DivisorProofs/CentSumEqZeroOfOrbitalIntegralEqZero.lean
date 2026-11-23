import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.TraceDefinitePairsEqAutomorphicTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzPointCountOneClassCommensurable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactOpenLevelConjCommensurableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitarySimilitudeIntegralSubgroupCommensuratedFrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDoubleCosetDefiniteHermitianFormLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteFormStabilizerFiniteAwayFromPStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTestProductSupportFiniteLeftCosetsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairAdelicProdUnramifiedEmbeddingInjec
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.DefVanish

section Generic

variable {Γ H : Type} [Group Γ] [Group H]

theorem finite_coset_preimage (ι : Γ →* H) (hι : Function.Injective ι) (K : Subgroup H) (x : H) (c : H ⧸ K)
    (hstab : Finite (GlobalTheory.LKLoc.locPart ι.range K x)) :
    {w : Γ | (QuotientGroup.mk (x⁻¹ * ι w * x) : H ⧸ K) = c}.Finite := by
  by_cases hne : ∃ w₀ : Γ, (QuotientGroup.mk (x⁻¹ * ι w₀ * x) : H ⧸ K) = c
  · obtain ⟨w₀, hw₀⟩ := hne
    have hfin : ((GlobalTheory.LKLoc.locPart ι.range K x : Subgroup H) : Set H).Finite := Set.toFinite _
    have hpre : (ι ⁻¹' (GlobalTheory.LKLoc.locPart ι.range K x : Set H)).Finite := hfin.preimage hι.injOn
    refine (hpre.image (fun u => w₀ * u)).subset ?_
    intro w hw
    refine ⟨w₀⁻¹ * w, ?_, by simp⟩
    have h1 : (QuotientGroup.mk (x⁻¹ * ι w * x) : H ⧸ K) = QuotientGroup.mk (x⁻¹ * ι w₀ * x) := by
      rw [hw, hw₀]
    rw [QuotientGroup.eq] at h1
    simp only [Set.mem_preimage, SetLike.mem_coe, GlobalTheory.LKLoc.locPart, Subgroup.mem_inf, MonoidHom.mem_range]
    refine ⟨⟨w₀⁻¹ * w, rfl⟩, ?_⟩
    rw [GlobalTheory.LKCountPoint.mem_map_conj]
    have e : x⁻¹ * ι (w₀⁻¹ * w) * x = (x⁻¹ * ι w₀ * x)⁻¹ * (x⁻¹ * ι w * x) := by
      simp only [map_mul, map_inv]; group
    rw [e]
    have h2 := K.inv_mem h1
    rwa [_root_.mul_inv_rev, inv_inv] at h2
  · push_neg at hne
    convert Set.finite_empty
    ext w; simp [hne w]

theorem finite_supp_cent (ι : Γ →* H) (hι : Function.Injective ι) (K : Subgroup H) (F₀ : H → ℂ) (y : Γ)
    (hbi : ∀ k ∈ K, ∀ k' ∈ K, ∀ g, F₀ (k * g * k') = F₀ g)
    (hcls : Finite (DoubleCoset.Quotient (ι.range : Set H) (K : Set H)))
    (hstab : ∀ x, Finite (GlobalTheory.LKLoc.locPart ι.range K x))
    (hsupp : (Function.support (fun c : H ⧸ K => F₀ c.out)).Finite) :
    {q : DoubleCoset.Quotient (((Subgroup.centralizer {y}).map ι : Subgroup H) : Set H) (K : Set H) |
      F₀ ((Quotient.out q)⁻¹ * ι y * Quotient.out q) ≠ 0}.Finite := by
  set D := DoubleCoset.Quotient (ι.range : Set H) (K : Set H)

  set W : Set Γ := ⋃ d : D, ⋃ c ∈ Function.support (fun c : H ⧸ K => F₀ c.out),
    {w : Γ | (QuotientGroup.mk ((Quotient.out d)⁻¹ * ι w * Quotient.out d) : H ⧸ K) = c}
  have hW : W.Finite :=
    Set.finite_iUnion fun d => hsupp.biUnion fun c _ => finite_coset_preimage ι hι K _ c (hstab _)
  let cj : Γ → Γ := fun w => if h : ∃ γ : Γ, γ⁻¹ * y * γ = w then h.choose else 1
  let g : Γ × D → DoubleCoset.Quotient (((Subgroup.centralizer {y}).map ι : Subgroup H) : Set H) (K : Set H) :=
    fun wd => DoubleCoset.mk _ K (ι (cj wd.1) * Quotient.out wd.2)
  refine ((hW.prod (Set.finite_univ (α := D))).image g).subset ?_
  intro q hq
  simp only [Set.mem_setOf_eq] at hq
  set x := Quotient.out q
  obtain ⟨h, k, hh, hk, hd⟩ := DoubleCoset.mk_out_eq_mul ι.range K x
  obtain ⟨γ₀, rfl⟩ := hh
  set d : D := DoubleCoset.mk ι.range K x

  have hx : x = ι γ₀⁻¹ * Quotient.out d * k⁻¹ := by
    rw [hd, map_inv]; group
  set w := γ₀ * y * γ₀⁻¹
  have hconj : x⁻¹ * ι y * x = k * ((Quotient.out d)⁻¹ * ι w * Quotient.out d) * k⁻¹ := by
    rw [hx]; simp only [w, map_mul, map_inv]; group
  have hF : F₀ ((Quotient.out d)⁻¹ * ι w * Quotient.out d) ≠ 0 := by
    rw [hconj, hbi k hk _ (K.inv_mem hk)] at hq; exact hq
  have hwW : w ∈ W := by
    simp only [W, Set.mem_iUnion, Set.mem_setOf_eq]
    refine ⟨d, QuotientGroup.mk ((Quotient.out d)⁻¹ * ι w * Quotient.out d), ?_, rfl⟩
    simp only [Function.mem_support]
    obtain ⟨k', hk'⟩ := QuotientGroup.mk_out_eq_mul K ((Quotient.out d)⁻¹ * ι w * Quotient.out d)
    rw [hk']
    have := hbi 1 K.one_mem k' k'.2 ((Quotient.out d)⁻¹ * ι w * Quotient.out d)
    rw [one_mul] at this
    rw [this]; exact hF
  refine ⟨(w, d), ⟨hwW, Set.mem_univ _⟩, ?_⟩
  have hex : ∃ γ : Γ, γ⁻¹ * y * γ = w := ⟨γ₀⁻¹, by simp [w]⟩
  have hcj : cj w = hex.choose := dif_pos hex
  have hcs := hex.choose_spec
  set γw := hex.choose

  have hz : γ₀⁻¹ * γw⁻¹ ∈ Subgroup.centralizer {y} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e : y * γw = γw * w := by rw [← hcs]; group
    have e2 : w = γ₀ * y * γ₀⁻¹ := rfl
    calc γ₀⁻¹ * γw⁻¹ * y = γ₀⁻¹ * (γw⁻¹ * (y * γw)) * γw⁻¹ := by group
      _ = γ₀⁻¹ * w * γw⁻¹ := by rw [e]; group
      _ = y * (γ₀⁻¹ * γw⁻¹) := by rw [e2]; group
  show DoubleCoset.mk _ K (ι (cj w) * Quotient.out d) = q
  rw [← DoubleCoset.out_eq' _ K q]
  rw [DoubleCoset.eq]
  refine ⟨ι (γ₀⁻¹ * γw⁻¹), ⟨_, hz, rfl⟩, k⁻¹, K.inv_mem hk, ?_⟩
  show x = _
  rw [hx, hcj]; simp only [map_mul, map_inv]; group

end Generic

end GlobalTheory.DefVanish

namespace GlobalTheory.DefVanish

variable {p : ℕ} [Fact p.Prime]

theorem toAfF_injective (G : HTGroup p) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) : Function.Injective (GlobalTheory.LKCx.toAfF G β x t hx) := by
  haveI := GlobalTheory.LKMid.finiteAdeleRingAway_nontrivial p
  intro a b h
  have h0 := congrArg Subtype.val h
  have h1 := congrArg Prod.fst h0
  have h2 := congrArg Prod.snd h0
  simp only [GlobalTheory.LKCx.toAfF, MonoidHom.codRestrict_apply, MonoidHom.comp_apply, MonoidHom.prodMap, MonoidHom.prod_apply,
    Prod.map_fst, Prod.map_snd, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_left_inj,
    mul_right_inj] at h1 h2
  have e1 : (a : G.Cˣ × ℚˣ).1 = (b : G.Cˣ × ℚˣ).1 := by
    apply Units.ext
    have := congrArg Units.val h1
    simp only [Units.coe_map, MonoidHom.coe_coe] at this
    exact Algebra.TensorProduct.includeRight_injective (algebraMap ℚ (AfP p)).injective this
  have e2 : (a : G.Cˣ × ℚˣ).2 = (b : G.Cˣ × ℚˣ).2 := by
    apply Units.ext
    have := congrArg Units.val h2
    simp only [Units.coe_map, MonoidHom.coe_coe] at this
    exact (algebraMap ℚ (AfP p)).injective this
  exact Subtype.ext (Prod.ext e1 e2)

theorem emb_injective (G : HTGroup p) (B : GlobalTheory.LKDef.DForm G) : Function.Injective B.emb := fun a b h =>
  toAfF_injective G B.β _ _ _ (congrArg Prod.fst h)

end GlobalTheory.DefVanish

open scoped Pointwise

namespace GlobalTheory.DefVanish
theorem conjAct_smul_eq_map' {H : Type} [Group H] (g : H) (S : Subgroup H) :
    (ConjAct.toConjAct g • S) = S.map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.pointwise_smul_def]
  rfl
end GlobalTheory.DefVanish

open GlobalTheory.DefVanish in

theorem GlobalTheory.LKDef.DForm.centSum_eq_zero_of_orbK : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 →
    ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
    ∀ (B : GlobalTheory.LKDef.DForm G) (y : GlobalTheory.LKCx.grp G B.β),
      orbK (MonoidHom.id _) (L.K.toSubgroup.prod K') (B.emb y) (fun h => f h.1 * f' h.2) = 0 →
      centSum (GlobalTheory.LKCx.toAfF G B.β B.trivAf.choose B.trivAf.choose_spec.choose B.trivAf.choose_spec.choose_spec)
        (GlobalTheory.LKCx.toP1 G B.β) (MonoidHom.id (Gr G 1)) L.K.toSubgroup K' 1 f f' y = 0 := by
  intro p _ G ha L f hf hfb K' f' hf' hf'b B y horb
  have hι : Function.Injective B.emb := emb_injective G B
  have hemb : (GlobalTheory.LKCx.toAfF G B.β B.trivAf.choose B.trivAf.choose_spec.choose B.trivAf.choose_spec.choose_spec).prod
      (GlobalTheory.LKCx.toP1 G B.β) = B.emb := rfl
  set K : Subgroup (G.GAf × Gr G 1) := L.K.toSubgroup.prod K' with hKdef
  set F₀ : G.GAf × Gr G 1 → ℂ := fun h => f h.1 * f' h.2 with hF₀
  set Γ' : Subgroup (G.GAf × Gr G 1) := (Subgroup.centralizer {y}).map B.emb with hΓ'
  set T : Subgroup (G.GAf × Gr G 1) := GlobalTheory.BCT.twCent (MonoidHom.id _) (B.emb y) with hT
  have hK'c : ∀ g : Gr G 1, (K'.map (MulAut.conj g).toMonoidHom).Commensurable K' := by
    intro g
    have h1 : (K'.map (MulAut.conj g).toMonoidHom).Commensurable
        ((KHT p G.m G.n 1 G.Fw).map (MulAut.conj g).toMonoidHom) := by
      rw [← conjAct_smul_eq_map', ← conjAct_smul_eq_map']
      exact (Subgroup.Commensurable.commensurable_conj _).1 hf'.1
    exact (h1.trans ((GlobalTheory.T.unitarySimilitudeIntegralSubgroup_commensurated_frobenius p G 1 one_pos).1 g)).trans hf'.1.symm
  have hK : ∀ x : G.GAf × Gr G 1, (K.map (MulAut.conj x).toMonoidHom).Commensurable K :=
    GlobalTheory.LKCountComm.commensurable_prod _ _ (GlobalTheory.T.compactOpenLevel_conj_commensurable p G L) hK'c
  have hbi : ∀ k ∈ K, ∀ k' ∈ K, ∀ g, F₀ (k * g * k') = F₀ g := by
    intro k hk k' hk' g
    obtain ⟨hk1, hk2⟩ := Subgroup.mem_prod.1 hk
    obtain ⟨hk1', hk2'⟩ := Subgroup.mem_prod.1 hk'
    simp only [hF₀, Prod.fst_mul, Prod.snd_mul]
    rw [hfb _ hk1 _ hk1', hf'b _ hk2 _ hk2']
  have hrange : Γ' ≤ B.emb.range := by
    rintro _ ⟨c, -, rfl⟩; exact ⟨c, rfl⟩
  have hΓT : Γ' ≤ T := by
    rintro _ ⟨c, hc, rfl⟩
    show B.emb c * B.emb y = B.emb y * (MonoidHom.id _) (B.emb c)
    rw [MonoidHom.id_apply, ← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 hc]
  have hF : ∀ t ∈ T, ∀ x, ∀ k ∈ K, F₀ ((t * x * k)⁻¹ * B.emb y * (t * x * k)) = F₀ (x⁻¹ * B.emb y * x) := by
    intro t ht x k hk
    have ht' : t * B.emb y = B.emb y * t := ht
    have e : (t * x * k)⁻¹ * B.emb y * (t * x * k) = k⁻¹ * (x⁻¹ * B.emb y * x) * k := by
      have e0 : t⁻¹ * B.emb y * t = B.emb y := by rw [mul_assoc, ← ht', inv_mul_cancel_left]
      calc (t * x * k)⁻¹ * B.emb y * (t * x * k) = k⁻¹ * (x⁻¹ * (t⁻¹ * B.emb y * t) * x) * k := by group
        _ = _ := by rw [e0]
    rw [e, hbi _ (K.inv_mem hk) _ hk]
  have hstab := GlobalTheory.T.definiteForm_stabilizer_finite_away_from_p p G ha L K' hf'.1 B
  have hfin : ∀ x : G.GAf × Gr G 1, ((Γ' ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup (G.GAf × Gr G 1)) : Set (G.GAf × Gr G 1)).Finite := by
    intro x
    haveI := hstab x
    exact (Set.toFinite ((GlobalTheory.LKLoc.locPart B.emb.range K x : Subgroup (G.GAf × Gr G 1)) : Set (G.GAf × Gr G 1))).subset
      (SetLike.coe_subset_coe.2 (inf_le_inf_right _ hrange))
  have hsupp := finite_supp_cent B.emb hι K F₀ y hbi (GlobalTheory.T.finite_doubleCoset_definiteHermitianForm_level p G ha L K' hf'.1 B) hstab
    (GlobalTheory.T.heckeTestProduct_support_finite_leftCosets p G L f hf hfb K' f' hf' hf'b)
  have hcore := (GlobalTheory.LKCountComm.core_count_of_commensurable Γ' T K (fun x => F₀ (x⁻¹ * B.emb y * x)) hΓT hK
    hF hfin hsupp).1
  have horb' : (∑ᶠ q : DoubleCoset.Quotient (T : Set (G.GAf × Gr G 1)) (K : Set (G.GAf × Gr G 1)),
      ((vol (T ⊓ K) (T ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom) : ℚ) : ℂ)⁻¹ *
        F₀ ((Quotient.out q)⁻¹ * B.emb y * Quotient.out q)) = 0 := horb
  rw [horb', mul_zero] at hcore
  have hcard : ∀ x : G.GAf × Gr G 1, Nat.card (GlobalTheory.LKCount.stab (GlobalTheory.LKCx.toAfF G B.β B.trivAf.choose
      B.trivAf.choose_spec.choose B.trivAf.choose_spec.choose_spec) (GlobalTheory.LKCx.toP1 G B.β) L.K.toSubgroup K' x ⊓
      Subgroup.centralizer {y} : Subgroup (GlobalTheory.LKCx.grp G B.β)) =
      Nat.card (Γ' ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup (G.GAf × Gr G 1)) := by
    intro x
    rw [GlobalTheory.LKCountPoint.stab_eq]
    change Nat.card (((K.map (MulAut.conj x).toMonoidHom).comap B.emb ⊓ Subgroup.centralizer {y} :
      Subgroup (GlobalTheory.LKCx.grp G B.β))) = _
    refine Nat.card_congr ((Subgroup.equivMapOfInjective _ _ hι).toEquiv.trans (Equiv.setCongr ?_))
    congr 1
    rw [Subgroup.map_inf_eq _ _ _ hι, Subgroup.map_comap_eq, inf_comm B.emb.range, inf_assoc,
      inf_eq_right.2 hrange, inf_comm]
  rw [← hcore]
  unfold centSum
  refine finsum_congr fun q => ?_
  rw [hcard]
  congr 1
  · simp only [term, hF₀, hemb, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv, mul_one, MonoidHom.id_apply]
    rfl
