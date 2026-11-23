import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsIntEKMulVbar
import ReciprocityTheory.ClassFieldTheory.LocalClassField.GalBasic
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
import ReciprocityTheory.ClassFieldTheory.LocalClassField.HSubsingletonOfUniquelyDivisible
import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnitsCT
import ReciprocityTheory.ClassFieldTheory.LocalClassField.BrUnrA

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K}

theorem admissible_valuation_layer {L : IntermediateField ℚ_[p] (PadicAlgCl p)} (he : 0 < eK p L) (h : K ≤ L)
    [(subG p K L).Normal] : admitted (layerUIncl p K L) (vLayer p K L) where
  i_id := rfl
  p_id := rfl
  emb := (Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap continuous_of_discreteTopology
    (layerUIncl_injective p) fun _ _ => isOpen_discrete _).isEmbedding
  exact := fun y => by
    have h0 := ker_vLayer p he h
    rw [← LinearMap.mem_ker, h0]
    rfl
  sec := ⟨Function.surjInv (vLayer_surjective p he h), continuous_of_discreteTopology, Function.surjInv_eq _⟩

theorem eK_Kn_pos (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) : 0 < eK p (Kn p K n) := by
  rw [eK_Kn p hK hn]; exact eK_pos p K hK

theorem eK_Kur_pos (hK : FiniteDimensional ℚ_[p] K) : 0 < eK p (MaximalUnramifiedExtension p K) := by
  rw [eK_Kur p hK]; exact eK_pos p K hK

theorem valuation_unramified_layer_h2_bijective (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    Bijective ((vLayer p K (Kn p K n)).hom.H 2) :=
  bijective_H_of_adm (admissible_valuation_layer (eK_Kn_pos hK hn) le_sup_left) 2
    (layerU_Kn_H_subsingleton hK hn 2 two_pos) (layerU_Kn_H_subsingleton hK hn 3 three_pos)

theorem valuation_unramified_closure_h2_bijective (hK : FiniteDimensional ℚ_[p] K) :
    Bijective ((vLayer p K (MaximalUnramifiedExtension p K)).hom.H 2) :=
  bijective_H_of_adm (admissible_valuation_layer (eK_Kur_pos hK) le_Kur) 2
    (layerU_Kur_H_subsingleton hK 2 two_pos) (layerU_Kur_H_subsingleton hK 3 three_pos)

theorem card_h2_unramified_layer (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    Nat.card ((layer p K (Kn p K n)).H 2) = n := by
  have hL := finiteDimensional_Kn p K hK hn
  have := discreteTopology_GalLK (K := K) hL
  have := finite_GalLK (K := K) hL
  rw [Nat.card_congr (Equiv.ofBijective _ (valuation_unramified_layer_h2_bijective hK hn)),
    card_h2_trivial_int_cyclic _ (frobLK p K (Kn p K n)) (mem_zpowers_frobLK_Kn hK hn), card_GalLK, degLK_Kn hK hn]

theorem vLayerMap_Kur_eq_one (hK : FiniteDimensional ℚ_[p] K) (π : (urT p K).V)
    (hπ : (eK p K : ℝ) * vbar p π.1 = 1) : vLayerMap p K (MaximalUnramifiedExtension p K) π = 1 := by
  apply Int.cast_injective (α := ℝ)
  rw [vLayerMap_spec p le_Kur, eK_Kur p hK, hπ, Int.cast_one]

theorem vLayer_Kur_cls (hK : FiniteDimensional ℚ_[p] K) (π : (urT p K).V)
    (hπ : (eK p K : ℝ) * vbar p π.1 = 1) (m : (Fin 2 → GalLK p K (MaximalUnramifiedExtension p K)) → ℤ)
    (z : (urT p K).coch.X 2) (hz : (urT p K).coch.d 2 z = 0) (hzm : ∀ g, z.1 g = m g • π)
    (y : (trivRep (GalLK p K (MaximalUnramifiedExtension p K)) ℤ).coch.X 2) (hy : (trivRep (GalLK p K (MaximalUnramifiedExtension p K)) ℤ).coch.d 2 y = 0)
    (hym : y.1 = m) :
    (vLayer p K (MaximalUnramifiedExtension p K)).hom.H 2 ((urT p K).coch.cls 2 z hz) =
      (trivRep (GalLK p K (MaximalUnramifiedExtension p K)) ℤ).coch.cls 2 y hy := by
  rw [Cx.Hom.H_cls]
  apply Cx.cls_congr
  apply Subtype.ext
  funext g
  show vLayerMap p K (MaximalUnramifiedExtension p K) (z.1 fun i => g i) = y.1 g
  rw [hym, hzm, map_zsmul, vLayerMap_Kur_eq_one hK π hπ]
  simp

theorem exists_invariant_of_connecting_map (hK : FiniteDimensional ℚ_[p] K) :
    ∃ f : (urT p K).H 2 ≃+ QZ, IsInv p K f.toAddMonoidHom ∧
      ∀ δ, Cx.IsConn (trivMap (GalLK p K (MaximalUnramifiedExtension p K)) (Int.castAddHom ℚ)).hom
        (trivMap (GalLK p K (MaximalUnramifiedExtension p K)) (QuotientAddGroup.mk' (Int.castAddHom ℚ).range)).hom δ →
      ∀ (c : (urT p K).H 2) (x) (hx),
        (vLayer p K (MaximalUnramifiedExtension p K)).hom.H 2 c = δ 1 ((trivRep (GalLK p K (MaximalUnramifiedExtension p K)) QZ).coch.cls 1 x hx) →
        f c = x.1 ![frobLK p K (MaximalUnramifiedExtension p K)] := by
  obtain ⟨e, he⟩ := exists_h2_int_equiv_rat_mod_int (GalLK p K (MaximalUnramifiedExtension p K)) (frobLK p K (MaximalUnramifiedExtension p K)) (isZHat_GalKur hK)
  refine ⟨(AddEquiv.ofBijective ((vLayer p K (MaximalUnramifiedExtension p K)).hom.H 2).toAddMonoidHom
    (valuation_unramified_closure_h2_bijective hK)).trans e, ?_, ?_⟩
  · intro π t m z hz _ hπ ht hm hzm
    have s := admissibility_holds ℤ _ _ _ _ _ _ (admissible_int_rat_sequence (GalLK p K (MaximalUnramifiedExtension p K)))
    obtain ⟨⟨δ, h1, -⟩, -⟩ := lES_holds ℤ _ _ _ _ _ s
    obtain ⟨x, hx, y, hy, e1, e2, e3⟩ := conn_cls_of_lift δ h1 t ht m hm
    show e ((vLayer p K (MaximalUnramifiedExtension p K)).hom.H 2 ((urT p K).coch.cls 2 z hz)) = _
    rw [vLayer_Kur_cls hK π hπ m z hz hzm y hy e2]
    exact (congrArg e e3.symm).trans ((he δ h1 x hx).trans (e1 _))
  · intro δ hδ c x hx h
    show e ((vLayer p K (MaximalUnramifiedExtension p K)).hom.H 2 c) = _
    exact (congrArg e h).trans (he δ hδ x hx)

theorem exists_isInv (hK : FiniteDimensional ℚ_[p] K) :
    ∃ f : (urT p K).H 2 ≃+ QZ, IsInv p K f.toAddMonoidHom := by
  obtain ⟨f, hf, -⟩ := exists_invariant_of_connecting_map hK
  exact ⟨f, hf⟩

theorem exists_uniformiser_Kur (hK : FiniteDimensional ℚ_[p] K) :
    ∃ π : (urT p K).V, π.1 ∈ multOf p K ∧ (eK p K : ℝ) * vbar p π.1 = 1 := by
  obtain ⟨x, hx⟩ := vOn_surjective p K hK 1
  have h1 := vOn_spec p K x
  rw [hx, Int.cast_one] at h1
  have hx' : x.1 ∈ multOf p (MaximalUnramifiedExtension p K) := le_Kur (K := K) x.2
  exact ⟨toLayer p ⟨x.1, hx'⟩, x.2, h1.symm⟩

theorem exists_std_cocycle (hK : FiniteDimensional ℚ_[p] K) (c : (urT p K).H 2) :
    ∃ (π : (urT p K).V) (t : GalLK p K (MaximalUnramifiedExtension p K) → ℚ) (m : (Fin 2 → GalLK p K (MaximalUnramifiedExtension p K)) → ℤ)
      (z : (urT p K).coch.X 2) (hz : (urT p K).coch.d 2 z = 0),
      π.1 ∈ multOf p K ∧ (eK p K : ℝ) * vbar p π.1 = 1 ∧ IsLocallyConstant t ∧
      (∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) ∧ (∀ g, z.1 g = m g • π) ∧
      c = (urT p K).coch.cls 2 z hz := by
  obtain ⟨π, hπK, hπ⟩ := exists_uniformiser_Kur hK
  obtain ⟨t, m, y, hy, ht, hm, hym, hc⟩ := exists_cocycle_form ((vLayer p K (MaximalUnramifiedExtension p K)).hom.H 2 c)
  have hinv := (layer_invariant_iff π).2 hπK
  have hyc : Continuous y.1 := y.2
  have hzc : Continuous fun g : Fin 2 → GalLK p K (MaximalUnramifiedExtension p K) => m g • π := by
    have h0 : Continuous fun k : (trivRep (GalLK p K (MaximalUnramifiedExtension p K)) ℤ).V => (show ℤ from k) • π :=
      continuous_of_discreteTopology
    rw [← hym]
    exact h0.comp hyc
  let z : (urT p K).coch.X 2 := ⟨fun g => m g • π, hzc⟩
  have hz : (urT p K).coch.d 2 z = 0 := by
    apply LowDeg.coch_d_eq_zero
    funext g
    have h0 := congrFun (LowDeg.dn_eq_zero _ hy) g
    rw [LowDeg.dn_two_apply, hym] at h0
    have h1 : m ![g 1, g 2] - m ![g 0 * g 1, g 2] + m ![g 0, g 1 * g 2] - m ![g 0, g 1] = 0 := h0
    rw [LowDeg.dn_two_apply]
    show (urT p K).rho (g 0) (m ![g 1, g 2] • π) - m ![g 0 * g 1, g 2] • π + m ![g 0, g 1 * g 2] • π -
      m ![g 0, g 1] • π = 0
    rw [map_zsmul, hinv, ← sub_smul, ← add_smul, ← sub_smul, h1, zero_smul]
  refine ⟨π, t, m, z, hz, hπK, hπ, ht, hm, fun _ => rfl, ?_⟩
  apply (valuation_unramified_closure_h2_bijective hK).1
  rw [hc, vLayer_Kur_cls hK π hπ m z hz (fun _ => rfl) y hy hym]

theorem IsInv.unique (hK : FiniteDimensional ℚ_[p] K) {f g : (urT p K).H 2 →+ QZ} (hf : IsInv p K f)
    (hg : IsInv p K g) : f = g := by
  ext c
  obtain ⟨π, t, m, z, hz, h1, h2, h3, h4, h5, rfl⟩ := exists_std_cocycle hK c
  rw [hf π t m z hz h1 h2 h3 h4 h5, hg π t m z hz h1 h2 h3 h4 h5]

theorem isInv_invUr (hK : FiniteDimensional ℚ_[p] K) : IsInv p K (invUr p K) := by
  obtain ⟨f, hf⟩ := exists_isInv hK
  have h : ∃ f, IsInv p K f := ⟨_, hf⟩
  unfold invUr
  rw [dif_pos h]
  exact h.choose_spec

theorem invUr_bijective (hK : FiniteDimensional ℚ_[p] K) : Bijective (invUr p K) := by
  obtain ⟨f, hf⟩ := exists_isInv hK
  rw [IsInv.unique hK (isInv_invUr hK) hf]
  exact f.bijective

theorem invUr_eq (hK : FiniteDimensional ℚ_[p] K) (δ)
    (hδ : Cx.IsConn (trivMap (GalLK p K (MaximalUnramifiedExtension p K)) (Int.castAddHom ℚ)).hom
      (trivMap (GalLK p K (MaximalUnramifiedExtension p K)) (QuotientAddGroup.mk' (Int.castAddHom ℚ).range)).hom δ)
    (c : (urT p K).H 2) (x) (hx)
    (h : (vLayer p K (MaximalUnramifiedExtension p K)).hom.H 2 c = δ 1 ((trivRep (GalLK p K (MaximalUnramifiedExtension p K)) QZ).coch.cls 1 x hx)) :
    invUr p K c = x.1 ![frobLK p K (MaximalUnramifiedExtension p K)] := by
  obtain ⟨f, hf, hf'⟩ := exists_invariant_of_connecting_map hK
  rw [IsInv.unique hK (isInv_invUr hK) hf]
  exact hf' δ hδ c x hx h

theorem layerInfl_u_val {L L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : L ≤ L') [(subG p K L).Normal]
    [(subG p K L').Normal] (x : (layer p K L).V) : ((layerInfl (K := K) h).u x).1 = x.1 := rfl

theorem vLayerMap_layerInfl {L L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (hL : K ≤ L) (h : L ≤ L')
    [(subG p K L).Normal] [(subG p K L').Normal] (he : eK p L' = eK p L) (x : (layer p K L).V) :
    vLayerMap p K L' ((layerInfl (K := K) h).u x) = vLayerMap p K L x := by
  apply Int.cast_injective (α := ℝ)
  rw [vLayerMap_spec p (hL.trans h), vLayerMap_spec p hL, he, layerInfl_u_val]

theorem layerInfl_φ_surjective {L L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : L ≤ L')
    [(subG p K L).Normal] [(subG p K L').Normal] : Surjective (layerInfl (K := K) h).φ := by
  intro g
  induction g using QuotientGroup.induction_on with
  | H σ => exact ⟨QuotientGroup.mk σ, rfl⟩

theorem vLayer_layerInfl_H {L L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (hL : K ≤ L) (h : L ≤ L')
    [(subG p K L).Normal] [(subG p K L').Normal] (he : eK p L' = eK p L) (i : ℕ) (c : (layer p K L).H i) :
    (vLayer p K L').hom.H i ((layerInfl (K := K) h).hom.H i c) =
      (trivInfl (layerInfl (K := K) h).φ (layerInfl (K := K) h).φ_cont ℤ).hom.H i
        ((vLayer p K L).hom.H i c) := by
  obtain ⟨x, hx, rfl⟩ := Cx.exists_cls c
  rw [Cx.Hom.H_cls, Cx.Hom.H_cls, Cx.Hom.H_cls, Cx.Hom.H_cls]
  apply Cx.cls_congr
  apply Subtype.ext
  funext g
  exact vLayerMap_layerInfl hL h he _

theorem inflation_h2_injective_of_same_ramification {L L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (hL : K ≤ L) (h : L ≤ L')
    [(subG p K L).Normal] [(subG p K L').Normal] (he : eK p L' = eK p L)
    (hv : Injective ((vLayer p K L).hom.H 2)) : Injective ((layerInfl (K := K) h).hom.H 2) := by
  intro a b hab
  apply hv
  apply trivial_inflation_h2_int_injective _ (layerInfl (K := K) h).φ_cont (layerInfl_φ_surjective h)
  rw [← vLayer_layerInfl_H hL h he, ← vLayer_layerInfl_H hL h he, hab]

theorem inflation_unramified_layer_h2_injective (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    Injective ((layerInfl (K := K) (L := Kn p K n) (L' := MaximalUnramifiedExtension p K) (Kn_le_Kur hn)).hom.H 2) :=
  inflation_h2_injective_of_same_ramification (L := Kn p K n) le_sup_left (Kn_le_Kur hn) ((eK_Kur p hK).trans (eK_Kn p hK hn).symm)
    (valuation_unramified_layer_h2_bijective hK hn).1

theorem mem_range_layerInfl_Kn_iff (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) (x : (urT p K).H 2) :
    x ∈ LinearMap.range ((layerInfl (K := K) (L := Kn p K n) (L' := MaximalUnramifiedExtension p K) (Kn_le_Kur hn)).hom.H 2) ↔ n • x = 0 := by
  have hsub : Set.range ((layerInfl (K := K) (L := Kn p K n) (L' := MaximalUnramifiedExtension p K) (Kn_le_Kur hn)).hom.H 2) ⊆
      {x : (urT p K).H 2 | n • x = 0} := by
    rintro _ ⟨y, rfl⟩
    show n • _ = 0
    have h0 : n • y = 0 := by
      have h1 := card_nsmul_eq_zero' (x := y)
      rwa [card_h2_unramified_layer hK hn] at h1
    rw [← map_nsmul, h0, map_zero]
  obtain ⟨f, -⟩ := exists_isInv hK
  have hT : Nat.card {x : (urT p K).H 2 | n • x = 0} = n := by
    refine (Nat.card_congr (Equiv.subtypeEquiv f.toEquiv fun a => ?_)).trans (card_QZ_torsion n hn)
    show n • a = 0 ↔ n • f a = 0
    rw [← map_nsmul, map_eq_zero_iff f f.injective]
  have hfin : ({x : (urT p K).H 2 | n • x = 0} : Set _).Finite :=
    Nat.finite_of_card_ne_zero (by rw [hT]; exact hn.ne')
  have hS : Nat.card (Set.range ((layerInfl (K := K) (L := Kn p K n) (L' := MaximalUnramifiedExtension p K) (Kn_le_Kur hn)).hom.H 2)) = n := by
    rw [Nat.card_range_of_injective (inflation_unramified_layer_h2_injective hK hn), card_h2_unramified_layer hK hn]
  have heq := Set.eq_of_subset_of_ncard_le hsub
    (by rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hT, hS]) hfin
  show x ∈ Set.range _ ↔ _
  rw [heq]
  rfl

end ReciprocityTheory.DiscreteGroups.LocalClassField
