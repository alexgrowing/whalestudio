import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsIntEKMulVbar
import ReciprocityTheory.ClassFieldTheory.LocalClassField.GalBasic
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
import ReciprocityTheory.ClassFieldTheory.LocalClassField.InflationH2InjectiveOfSameRamification

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

noncomputable def trivPull {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G'] (φ : G' →* G)
    (hφ : Continuous φ) (A : Type) [AddCommGroup A] : Pair (trivRep G A) (trivRep G' A) where
  φ := φ
  u := LinearMap.id
  φ_cont := hφ
  u_cont := continuous_of_discreteTopology
  equiv _ _ := rfl

theorem conn_trivPull {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G']
    [TopologicalSpace G'] [IsTopologicalGroup G'] (φ : G' →* G) (hφ : Continuous φ) (δ δ')
    (hδ : Cx.IsConn (trivMap G (Int.castAddHom ℚ)).hom
      (trivMap G (QuotientAddGroup.mk' (Int.castAddHom ℚ).range)).hom δ)
    (hδ' : Cx.IsConn (trivMap G' (Int.castAddHom ℚ)).hom
      (trivMap G' (QuotientAddGroup.mk' (Int.castAddHom ℚ).range)).hom δ') (n : ℕ) (x) :
    δ' n ((trivPull φ hφ QZ).hom.H n x) = (trivPull φ hφ ℤ).hom.H (n + 1) (δ n x) :=
  connNat_holds ℤ _ _ _ _ _ _ _ _ _ _ (trivPull φ hφ ℤ).hom (trivPull φ hφ ℚ).hom (trivPull φ hφ QZ).hom δ δ'
    (admissibility_holds ℤ G _ _ _ _ _ (admissible_int_rat_sequence G)) (admissibility_holds ℤ G' _ _ _ _ _ (admissible_int_rat_sequence G'))
    (fun _ _ => rfl) (fun _ _ => rfl) hδ hδ' n x

theorem cocycle_pow {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (x : (trivRep G QZ).coch.X 1) (hx : (trivRep G QZ).coch.d 1 x = 0)
    (g : G) (k : ℕ) : x.1 ![g ^ k] = k • x.1 ![g] := by
  obtain ⟨e, he⟩ := exists_h1_equiv_characters G
  rw [← he x hx, ← he x hx, ofMul_pow, map_nsmul]
  rfl

theorem resGK_mem_subG_Kur (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L)
    (σ : GK p L) (hσ : σ ∈ subG p L (MaximalUnramifiedExtension p L)) : resGK h σ ∈ subG p K (MaximalUnramifiedExtension p K) :=
  fun x hx => hσ x (Kur_le_Kur L hK hL h hx)

noncomputable def invMap {R : Type} [CommRing R] {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G']
    [TopologicalSpace G'] [IsTopologicalGroup G'] {M : TRep R G} {M' : TRep R G'} (Q : Pair M M') (N : Subgroup G)
    [N.Normal] (N' : Subgroup G') [N'.Normal] (hN : ∀ g ∈ N', Q.φ g ∈ N) :
    Pair (InflationRestrictionInvariants.invQ M N) (InflationRestrictionInvariants.invQ M' N') where
  φ := QuotientGroup.map N' N Q.φ hN
  u :=
    { toFun := fun x => ⟨Q.u x.1, fun g => by
        have h1 : M.rho (Q.φ g.1) x.1 = x.1 := x.2 ⟨Q.φ g.1, hN g.1 g.2⟩
        show M'.rho g.1 (Q.u x.1) = Q.u x.1
        rw [← Q.equiv, h1]⟩
      map_add' := fun x y => Subtype.ext (map_add Q.u x.1 y.1)
      map_smul' := fun r x => Subtype.ext (map_smul Q.u r x.1) }
  φ_cont := (QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.continuous_iff).2
    (continuous_quot_mk.comp Q.φ_cont)
  u_cont := Continuous.subtype_mk (Q.u_cont.comp continuous_subtype_val) _
  equiv g m := by
    induction g using QuotientGroup.induction_on with
    | H σ => exact Subtype.ext (Q.equiv σ m.1)

theorem invMap_φ {R : Type} [CommRing R] {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G']
    [TopologicalSpace G'] [IsTopologicalGroup G'] {M : TRep R G} {M' : TRep R G'} (Q : Pair M M') (N : Subgroup G)
    [N.Normal] (N' : Subgroup G') [N'.Normal] (hN : ∀ g ∈ N', Q.φ g ∈ N) (σ : G') :
    (invMap Q N N' hN).φ (QuotientGroup.mk σ) = QuotientGroup.mk (Q.φ σ) := rfl

theorem invMap_u {R : Type} [CommRing R] {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G']
    [TopologicalSpace G'] [IsTopologicalGroup G'] {M : TRep R G} {M' : TRep R G'} (Q : Pair M M') (N : Subgroup G)
    [N.Normal] (N' : Subgroup G') [N'.Normal] (hN : ∀ g ∈ N', Q.φ g ∈ N) (x : (InflationRestrictionInvariants.invQ M N).V) :
    ((invMap Q N N' hN).u x).1 = Q.u x.1 := rfl

theorem invMap_H {R : Type} [CommRing R] {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G']
    [TopologicalSpace G'] [IsTopologicalGroup G'] {M : TRep R G} {M' : TRep R G'} (Q : Pair M M') (N : Subgroup G)
    [N.Normal] (N' : Subgroup G') [N'.Normal] (hN : ∀ g ∈ N', Q.φ g ∈ N) (n : ℕ) (x : (InflationRestrictionInvariants.invQ M N).H n) :
    Q.hom.H n ((InflationRestrictionInvariants.invP M N).hom.H n x) =
      (InflationRestrictionInvariants.invP M' N').hom.H n ((invMap Q N N' hN).hom.H n x) := by
  induction x using Cx.H_ind with
  | h x hx => exact Cx.cls_congr _ _ (Subtype.ext (funext fun _ => rfl))

noncomputable def urRes (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) :
    Pair (urT p K) (urT p L) :=
  invMap (resPair h) (subG p K (MaximalUnramifiedExtension p K)) (subG p L (MaximalUnramifiedExtension p L)) (resGK_mem_subG_Kur hK hL h)

theorem exists_urRes (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) :
    ∃ P : Pair (urT p K) (urT p L), (∀ σ : GK p L, P.φ (QuotientGroup.mk σ) = QuotientGroup.mk (resGK h σ)) ∧
      (∀ x, (P.u x).1 = x.1) ∧
      ∀ n x, (resPair h).hom.H n ((layerInf p K (MaximalUnramifiedExtension p K)).hom.H n x) =
        (layerInf p L (MaximalUnramifiedExtension p L)).hom.H n (P.hom.H n x) := by
  exact ⟨urRes hK hL h, invMap_φ (resPair h) _ _ _, invMap_u (resPair h) _ _ _, invMap_H (resPair h) _ _ _⟩

theorem vLayerMap_urRes (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L)
    (x : (urT p K).V) (y : (urT p L).V) (hxy : y.1 = x.1) :
    vLayerMap p L (MaximalUnramifiedExtension p L) y = (eLK p K L : ℤ) • vLayerMap p K (MaximalUnramifiedExtension p K) x := by
  apply Int.cast_injective (α := ℝ)
  rw [vLayerMap_spec p (le_Kur (K := L)), smul_eq_mul, Int.cast_mul, vLayerMap_spec p (le_Kur (K := K)), eK_Kur p hK,
    eK_Kur p hL, eK_eq_mul p hL h, hxy]
  push_cast
  ring

theorem invUr_urRes (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L)
    (P : Pair (urT p K) (urT p L)) (hφ : ∀ σ : GK p L, P.φ (QuotientGroup.mk σ) = QuotientGroup.mk (resGK h σ))
    (hu : ∀ x, (P.u x).1 = x.1) (x : (urT p K).H 2) :
    invUr p L (P.hom.H 2 x) = degLK p K L • invUr p K x := by
  obtain ⟨⟨δ, hδ, -⟩, -⟩ := lES_holds ℤ _ _ _ _ _
    (admissibility_holds ℤ (GalLK p K (MaximalUnramifiedExtension p K)) _ _ _ _ _ (admissible_int_rat_sequence (GalLK p K (MaximalUnramifiedExtension p K))))
  obtain ⟨⟨δ', hδ', -⟩, -⟩ := lES_holds ℤ _ _ _ _ _
    (admissibility_holds ℤ (GalLK p L (MaximalUnramifiedExtension p L)) _ _ _ _ _ (admissible_int_rat_sequence (GalLK p L (MaximalUnramifiedExtension p L))))
  obtain ⟨c, hc⟩ := (conn_int_rat_bijective _ δ hδ 1 one_pos).2 ((vLayer p K (MaximalUnramifiedExtension p K)).hom.H 2 x)
  obtain ⟨χ, hχ, rfl⟩ := Cx.exists_cls c
  have h1 := invUr_eq hK δ hδ x χ hχ hc.symm
  have hv : (vLayer p L (MaximalUnramifiedExtension p L)).hom.H 2 (P.hom.H 2 x) =
      (eLK p K L : ℤ) • (trivPull P.φ P.φ_cont ℤ).hom.H 2 ((vLayer p K (MaximalUnramifiedExtension p K)).hom.H 2 x) := by
    induction x using Cx.H_ind with
    | h z hz =>
      refine Cx.cls_congr _ _ (Subtype.ext (funext fun g => ?_))
      exact vLayerMap_urRes hK hL h _ _ (hu _)
  have hn := conn_trivPull P.φ P.φ_cont δ δ' hδ hδ' 1 (Cx.cls _ 1 χ hχ)
  rw [← hc] at hv
  have hd : (trivRep (GalLK p L (MaximalUnramifiedExtension p L)) QZ).coch.d 1
      ((eLK p K L : ℤ) • (trivPull P.φ P.φ_cont QZ).hom.f 1 χ) = 0 := by
    rw [map_smul, ← Cx.Hom.comm, hχ, map_zero, smul_zero]
  have h2 := invUr_eq hL δ' hδ' (P.hom.H 2 x) ((eLK p K L : ℤ) • (trivPull P.φ P.φ_cont QZ).hom.f 1 χ) hd
    (hv.trans ((congrArg ((eLK p K L : ℤ) • ·) hn.symm).trans (map_smul (δ' 1) _ _).symm))
  have h3 : ((eLK p K L : ℤ) • (trivPull P.φ P.φ_cont QZ).hom.f 1 χ).1 ![frobLK p L (MaximalUnramifiedExtension p L)] =
      eLK p K L • χ.1 ![P.φ (frobLK p L (MaximalUnramifiedExtension p L))] := by
    refine Eq.trans ?_ (natCast_zsmul _ _)
    refine congrArg ((eLK p K L : ℤ) • ·) (congrArg χ.1 (funext fun i => ?_))
    fin_cases i
    rfl
  have h4 : P.φ (frobLK p L (MaximalUnramifiedExtension p L)) = frobLK p K (MaximalUnramifiedExtension p K) ^ fLK p K L :=
    (hφ _).trans (resGK_frobK L hK hL h (qK_eq_pow_fLK p hL h))
  rw [h2, h3, h4, cocycle_pow χ hχ, h1, ← eLK_mul_fLK_eq_degLK p hL h]
  exact (mul_smul (eLK p K L) (fLK p K L) (χ.1 ![frobLK p K (MaximalUnramifiedExtension p K)] : QZ)).symm

theorem exists_res_ur (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L)
    (x : (urT p K).H 2) : ∃ y : (urT p L).H 2,
      (resPair h).hom.H 2 ((layerInf p K (MaximalUnramifiedExtension p K)).hom.H 2 x) = (layerInf p L (MaximalUnramifiedExtension p L)).hom.H 2 y ∧
      invUr p L y = degLK p K L • invUr p K x := by
  obtain ⟨P, hφ, hu, hP⟩ := exists_urRes hK hL h
  exact ⟨P.hom.H 2 x, hP 2 x, invUr_urRes hK hL h P hφ hu x⟩

end ReciprocityTheory.DiscreteGroups.LocalClassField
