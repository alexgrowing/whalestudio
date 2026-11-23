import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates

noncomputable section

namespace Formalism.MainNotions.WachCoordinates.Br

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Module

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {LL' O' : Type} [Field LL'] [Algebra Qp LL'] [TopologicalSpace LL'] [CommRing O'] [Algebra O' LL']
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]

theorem comp_inj {E : Type} [Field E] [Algebra Qp E] (ι : LL →ₐ[Qp] LL') :
    Function.Injective (fun τ : E →ₐ[Qp] LL => ι.comp τ) := by
  intro τ τ' h
  apply AlgHom.ext
  intro x
  exact ι.toRingHom.injective (congrArg (fun f : E →ₐ[Qp] LL' => f x) h)

theorem comp_bij {E : Type} [Field E] [Algebra Qp E] [FiniteDimensional Qp E] (ι : LL →ₐ[Qp] LL')
    (hcard : Nat.card (E →ₐ[Qp] LL) = finrank Qp E) :
    Function.Bijective (fun τ : E →ₐ[Qp] LL => ι.comp τ) :=
  (comp_inj ι).bijective_of_nat_card_le (hcard ▸ card_algHom_le_finrank Qp E LL')

variable [Fintype (K →ₐ[Qp] LL)] [Fintype (K →ₐ[Qp] LL')]

theorem thmELiftAt_bc (ι : LL →ₐ[Qp] LL') (v' : AddValuation LL' (WithTop ℚ))
    (emb : ZMod n → (K₀ →ₐ[Qp] LL)) (hfin : FiniteDimensional Qp LL') (hv' : v' (PD.p : LL') = 1)
    (hO' : ∃ hO : IsDomain O', @IsDiscreteValuationRing O' _ hO ∧ IsFractionRing O' LL')
    (hBC : BCAt PD (LL := LL) (O := O) (O' := O') ι)
    (H : ThmELiftAt PD (O := O') n (fun i => ι.comp (emb i)) v') :
    ThmELiftAt PD (O := O) n emb v := by
  intro hL h5 T₁ T₂ F hG hc₁ hc₂ hon j Gp S η h ty cuts arcLen Mb₁ hb₁ Mb₂ hb₂ hK hJ hg hS hC hT hb1 hb2
    hW
  obtain ⟨T₁', T₂', F', hc₁', hc₂', hon', hj, -, hlift, -⟩ := hBC T₁ T₂ F hc₁ hc₂ hon
  apply hlift
  have := PD.finK
  have := PD.finK₀
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := hL
  have hbK := comp_bij (E := K) ι (by rw [Nat.card_eq_fintype_card]; exact hG.1.2)
  have hbK₀ := comp_bij (E := K₀) ι (by
    rw [← Nat.card_congr (Equiv.ofBijective emb l4), Nat.card_zmod, l3])
  have hL' : Letters PD LL' v' (fun i => ι.comp (emb i)) :=
    ⟨l1, hfin, l3, hbK₀.comp l4, fun i => by
      change (ι.comp (emb (i + 1))).comp PD.σ = ι.comp (emb i)
      rw [AlgHom.comp_assoc, l5], hv'⟩
  have hG' : GoodCoeffs (K := K) (Qp := Qp) (LL := LL') (O := O') (V := T₁'.V) := by
    refine ⟨⟨hfin, ?_⟩, hc₁'.2.1, hO'⟩
    rw [← hG.1.2]
    exact (Fintype.card_of_bijective hbK).symm
  have tr₁ : ∀ (i : ZMod n) (X : Set ℤ), JumpsAtE PD T₁ emb i X →
      JumpsAtE PD T₁' (fun i => ι.comp (emb i)) i X := by
    intro i X hX τ' hτ' a ha
    obtain ⟨τ, rfl⟩ := hbK.2 τ'
    exact hX τ (comp_inj ι (by simpa [AlgHom.comp_assoc] using hτ')) a ((hj τ a).1.1 ha)
  have tr₂ : ∀ (i : ZMod n) (X : Set ℤ), JumpsAtE PD T₂ emb i X →
      JumpsAtE PD T₂' (fun i => ι.comp (emb i)) i X := by
    intro i X hX τ' hτ' a ha
    obtain ⟨τ, rfl⟩ := hbK.2 τ'
    exact hX τ (comp_inj ι (by simpa [AlgHom.comp_assoc] using hτ')) a ((hj τ a).2.1 ha)
  refine H hL' h5 T₁' T₂' F' hG' hc₁' hc₂' hon' j Gp S η h ty cuts arcLen Mb₁ hb₁ Mb₂ hb₂
    (fun i => tr₁ i _ (hK i)) ?_ hg hS hC hT (fun i => tr₁ i _ (hb1 i)) (fun i => tr₂ i _ (hb2 i)) hW
  intro τ' a ha
  obtain ⟨τ, rfl⟩ := hbK.2 τ'
  exact hJ τ a ((hj τ a).1.1 ha)

end Formalism.MainNotions.WachCoordinates.Br
