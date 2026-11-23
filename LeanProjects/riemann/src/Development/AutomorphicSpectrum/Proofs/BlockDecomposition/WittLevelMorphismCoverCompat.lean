import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.ResVq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemBiInf
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG CrystallineSemistableComparison.Pb.SubquotientResolution GlobalTheory.CompanionTheory.DisoHm

noncomputable section

namespace GlobalTheory.CompanionTheory.FlatCoverGlue

set_option maxHeartbeats 1000000 in

theorem glue {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O]
    {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (U : Cov q) (n : ℕ) (c : WittVector l k)
    (m : QMor (sW l (B.schFn q) ρ n) (sW l (B.schFn q) ρ (n + 1)) (IdF.span _ c))
    (hG : ∀ (𝒱 : Set X.Opens) (T : (stF q ρ (n + 1) 𝒱).FullSubcategory),
      stF q ρ n 𝒱 (m.G.obj ⟨T.obj, T.property.1⟩).obj)
    (hloc : ∀ S : Finset U.ι, S.Nonempty → ∀ j, Function.Bijective
      (((subQ m (stF q ρ n {⨅ α ∈ S, U.U α}) (stF q ρ (n + 1) {⨅ α ∈ S, U.U α}) (fun _ h => h.1) (hG _)).o
        (IdF.span _ c) (fun _ => le_rfl)).pull j)) (j : ℕ) :
    Function.Bijective
      (((subQ m (stF q ρ n (Set.range U.U)) (stF q ρ (n + 1) (Set.range U.U)) (fun _ h => h.1) (hG _)).o
        (IdF.span _ c) (fun _ => le_rfl)).pull j) := by
  have hGU : ∀ (α : U.ι) (T : (stF q ρ (n + 1) (Set.range U.U)).FullSubcategory), InU (U.U α) T.obj →
      InU (U.U α) (m.G.obj ⟨T.obj, T.property.1⟩).obj := fun α T hT => by
    obtain ⟨-, V, rfl, hV⟩ := hG {U.U α} ⟨T.obj, T.property.1, U.U α, rfl, hT⟩
    exact hV
  refine cover_bij ((subQ m (stF q ρ n (Set.range U.U)) (stF q ρ (n + 1) (Set.range U.U)) (fun _ h => h.1) (hG _)).o
      (IdF.span _ c) (fun _ => le_rfl))
    (fun α T => InU (U.U α) T.obj) (fun α T => InU (U.U α) T.obj) (fun α T T' φ hT => Site.inU_hom φ.hom hT)
    (fun α T T' φ hT => Site.inU_hom φ.hom hT) (fun T => ?_) (fun T => ?_) (fun α T hT => hGU α T hT)
    (fun S hS j => ?_) j
  · obtain ⟨-, V, ⟨α, rfl⟩, hV⟩ := T.property
    exact ⟨α, hV⟩
  · obtain ⟨-, V, ⟨α, rfl⟩, hV⟩ := T.property
    exact ⟨α, hV⟩
  have h₁ : ∀ (r : ℕ) T, stF q ρ r {⨅ α ∈ S, U.U α} T →
      ∃ hp : stF q ρ r (Set.range U.U) T,
        capS (fun α (T : (stF q ρ r (Set.range U.U)).FullSubcategory) => InU (U.U α) T.obj) S ⟨T, hp⟩ :=
    fun r T hT => ⟨((st_inf _ U S hS T).1 hT).1, ((st_inf _ U S hS T).1 hT).2⟩
  have a₀ := nestAdj (h₁ n) (fun T => (st_inf _ U S hS T.obj.obj).2 ⟨T.obj.property, T.property⟩)
  have a₁ := nestAdj (h₁ (n + 1)) (fun T => (st_inf _ U S hS T.obj.obj).2 ⟨T.obj.property, T.property⟩)
  let rL : CH.Mor ((capS (fun α (T : (stF q ρ n (Set.range U.U)).FullSubcategory) => InU (U.U α) T.obj) S).ι ⋙
      CH.modF (sV q ρ n (Set.range U.U)).A) (CH.modF (sV q ρ n {⨅ α ∈ S, U.U α}).A) (RingHom.id _) :=
    CH.Mor.restrict _ (nestF (h₁ n))
  let rO : CH.Mor ((capS (fun α (T : (stF q ρ (n + 1) (Set.range U.U)).FullSubcategory) => InU (U.U α) T.obj) S).ι ⋙
      sq (IdF.top (sV q ρ (n + 1) (Set.range U.U)).A) (IdF.span (sV q ρ (n + 1) (Set.range U.U)).A c))
      (sq (IdF.top (sV q ρ (n + 1) {⨅ α ∈ S, U.U α}).A) (IdF.span (sV q ρ (n + 1) {⨅ α ∈ S, U.U α}).A c)) (RingHom.id _) :=
    CH.Mor.restrict _ (nestF (h₁ (n + 1)))
  have bL : Function.Bijective (rL.pull j) := CrystallineSemistableComparison.P.adj _ _ _ a₀ j
  have bO : Function.Bijective (rO.pull j) := CrystallineSemistableComparison.P.adj _ _ _ a₁ j
  refine (Function.Bijective.of_comp_iff' bO _).1 ?_
  have e : ∀ x, rO.pull j ((morU ((subQ m (stF q ρ n (Set.range U.U)) (stF q ρ (n + 1) (Set.range U.U)) (fun _ h => h.1) (hG _)).o
        (IdF.span _ c) (fun _ => le_rfl))
      (U := capS (fun α T => InU (U.U α) T.obj) S) (U' := capS (fun α T => InU (U.U α) T.obj) S)
      fun T hT α hα => hGU α T (hT α hα)).pull j x) =
      ((subQ m (stF q ρ n {⨅ α ∈ S, U.U α}) (stF q ρ (n + 1) {⨅ α ∈ S, U.U α}) (fun _ h => h.1) (hG _)).o
        (IdF.span _ c) (fun _ => le_rfl)).pull j (rL.pull j x) := by
    intro x
    refine ((CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id _) _ rO j x).1).symm.trans
      (Eq.trans ?_ ((CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id _) rL _ j x).1))
    refine CrystallineSemistableComparison.P.prism (σ := RingHom.id _) _ _ (𝟙 _) (fun T y => ?_) j x
    first
      | rfl
      | (simp only [NatTrans.id_app, CategoryTheory.Functor.map_id]; rfl)
  have e2 := funext e
  refine (show Function.Bijective (fun x => rO.pull j ((morU ((subQ m (stF q ρ n (Set.range U.U)) (stF q ρ (n + 1) (Set.range U.U)) (fun _ h => h.1) (hG _)).o
        (IdF.span _ c) (fun _ => le_rfl))
      (U := capS (fun α T => InU (U.U α) T.obj) S) (U' := capS (fun α T => InU (U.U α) T.obj) S)
      fun T hT α hα => hGU α T (hT α hα)).pull j x)) from ?_)
  rw [e2]
  exact (hloc S hS j).comp bL

end GlobalTheory.CompanionTheory.FlatCoverGlue
