import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFinitenessGl1UnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFinitenessSeparableNormStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.TwFin

theorem prod {H₁ H₂ : Type} [Group H₁] [Group H₂] (θ₁ : H₁ →* H₁) (θ₂ : H₂ →* H₂) (K₁ : Subgroup H₁)
    (K₂ : Subgroup H₂) (δ₁ N₁ : H₁) (δ₂ N₂ : H₂) (h₁ : TwFin θ₁ K₁ δ₁ N₁) (h₂ : TwFin θ₂ K₂ δ₂ N₂) :
    TwFin (θ₁.prodMap θ₂) (K₁.prod K₂) (δ₁, δ₂) (N₁, N₂) := by
  intro E
  obtain ⟨D₁, hD₁⟩ := h₁ (E.image Prod.fst)
  obtain ⟨D₂, hD₂⟩ := h₂ (E.image Prod.snd)
  refine ⟨D₁ ×ˢ D₂, fun t ht ⟨e, he, k, hk, hte⟩ => ?_⟩
  have ht1 : t.1 * N₁ = N₁ * t.1 := congrArg Prod.fst ht
  have ht2 : t.2 * N₂ = N₂ * t.2 := congrArg Prod.snd ht
  obtain ⟨u₁, hu₁, d₁, hd₁, k₁, hk₁, e₁⟩ :=
    hD₁ t.1 ht1 ⟨e.1, Finset.mem_image_of_mem _ he, k.1, hk.1, congrArg Prod.fst hte⟩
  obtain ⟨u₂, hu₂, d₂, hd₂, k₂, hk₂, e₂⟩ :=
    hD₂ t.2 ht2 ⟨e.2, Finset.mem_image_of_mem _ he, k.2, hk.2, congrArg Prod.snd hte⟩
  refine ⟨(u₁, u₂), ?_, (d₁, d₂), Finset.mem_product.2 ⟨hd₁, hd₂⟩, (k₁, k₂), ⟨hk₁, hk₂⟩, Prod.ext e₁ e₂⟩
  exact Prod.ext hu₁ hu₂

theorem pi {ι : Type} [Fintype ι] [DecidableEq ι] {H : ι → Type} [∀ i, Group (H i)] (θ : ∀ i, H i →* H i)
    (K : ∀ i, Subgroup (H i)) (δ N : ∀ i, H i) (h : ∀ i, TwFin (θ i) (K i) (δ i) (N i)) :
    TwFin (Pi.monoidHom fun i => (θ i).comp (Pi.evalMonoidHom H i)) (Subgroup.pi Set.univ K) δ N := by
  intro E
  have h' := fun i => h i (E.image fun x => x i)
  choose D hD using h'
  refine ⟨Fintype.piFinset D, fun t ht ⟨e, he, k, hk, hte⟩ => ?_⟩
  have hi : ∀ i, ∃ u ∈ GlobalTheory.BCT.twCent (θ i) (δ i), ∃ d ∈ D i, ∃ k ∈ K i, t i = u * d * k := fun i =>
    hD i (t i) (congrFun ht i) ⟨e i, Finset.mem_image_of_mem _ he, k i, hk i (Set.mem_univ i), congrFun hte i⟩
  choose u hu d hd k' hk' e' using hi
  refine ⟨u, ?_, d, Fintype.mem_piFinset.2 hd, k', fun i _ => hk' i, funext e'⟩
  funext i
  exact hu i

theorem map_nrmG {H H' : Type} [Group H] [Group H'] (θ : H →* H) (θ' : H' →* H') (f : H →* H')
    (hf : ∀ x, f (θ x) = θ' (f x)) (r : ℕ) (δ : H) : f (nrmG θ r δ) = nrmG θ' r (f δ) := by
  unfold nrmG
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact Function.Semiconj.iterate_right hf i δ

theorem main : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ), 0 < r → ∀ γ : Gp G, regular₂ G γ → ∀ δ z : Gr G r, IsNrm G r γ δ z → ∀ E : Finset (Gr G r), ∃ D : Finset (Gr G r), ∀ t : Gr G r, t * nrmG (sigG G r) r δ = nrmG (sigG G r) r δ * t → (∃ e ∈ E, ∃ k ∈ KHT p G.m G.n r G.Fw, t⁻¹ * δ * sigG G r t = e * k) → ∃ u ∈ GlobalTheory.BCT.twCent (sigG G r) δ, ∃ d ∈ D, ∃ k ∈ KHT p G.m G.n r G.Fw, t = u * d * k := by
  intro p _ G r hr γ hγ δ z hN
  have e2 : ∀ i, (nrmG (sigG G r) r δ).2 i = nrmRes p (G.Fw i) G.n r (δ.2 i) := fun i =>
    map_nrmG (sigG G r) _ ((Pi.evalMonoidHom _ i).comp (MonoidHom.snd _ _)) (fun x => rfl) r δ
  have hsep : ∀ i, (nrmRes p (G.Fw i) G.n r (δ.2 i)).val.charpoly.Separable := by
    intro i
    rw [← e2, hN]
    have h1 : ((z⁻¹ * inclG G r γ * z).2 i).val =
        ((z.2 i)⁻¹).val * (γ.2 i).val.map ((inclK p (G.Fw i) r : G.Fw i →+* KQ p (G.Fw i) r)) * (z.2 i).val := rfl
    rw [h1, Matrix.coe_units_inv, Matrix.charpoly_units_conj', Matrix.charpoly_map]
    exact (hγ i).map
  have key : TwFin (sigG G r) (KHT p G.m G.n r G.Fw) (δ.1, δ.2)
      ((nrmG (sigG G r) r δ).1, (nrmG (sigG G r) r δ).2) :=
    prod _ _ _ _ _ _ _ _ (GlobalTheory.T.twisted_finiteness_gl1_unramified p r hr _ _) (pi _ _ _ _ fun i => by
      rw [e2 i]; exact GlobalTheory.T.twisted_finiteness_separable_norm p (G.Fw i) inferInstance G.n r hr _ (hsep i))
  exact key

end GlobalTheory.TwFin
