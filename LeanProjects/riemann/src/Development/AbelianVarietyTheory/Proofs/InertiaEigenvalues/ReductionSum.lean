import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JSmul
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied

noncomputable section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.Present.SumRed

section General
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n₀ : ℕ}

theorem exists_proj {T T' Z : LocLat G Qp LL O} (f : LatHom T.L Z.L) (g : LatHom T'.L Z.L)
    (hb : Function.Bijective (f.f.coprod g.f))
    (hs : ∀ z ∈ Z.L.T, ∃ x ∈ T.L.T, ∃ y ∈ T'.L.T, z = f.f x + g.f y) :
    ∃ (p : LatHom Z.L T.L) (p' : LatHom Z.L T'.L), latAdd (latComp f p) (latComp g p') = latId Z := by
  let e : (T.V × T'.V) ≃ₗ[LL] Z.V := LinearEquiv.ofBijective _ hb
  have he : ∀ x y, e.symm (f.f x + g.f y) = (x, y) := fun x y => by
    rw [LinearEquiv.symm_apply_eq]; rfl
  have hz : ∀ z, f.f (e.symm z).1 + g.f (e.symm z).2 = z := fun z => e.apply_symm_apply z
  have hρ : ∀ σ z, e.symm (Z.ρ σ z) = (T.ρ σ (e.symm z).1, T'.ρ σ (e.symm z).2) := fun σ z => by
    rw [← he, f.equiv, g.equiv, ← map_add, hz]
  haveI := T.mtop.toContinuousSMul
  haveI := T'.mtop.toContinuousSMul
  refine ⟨⟨LinearMap.fst LL _ _ ∘ₗ e.symm.toLinearMap, fun σ z => ?_,
      IsModuleTopology.continuous_of_linearMap _, fun z h => ?_⟩,
    ⟨LinearMap.snd LL _ _ ∘ₗ e.symm.toLinearMap, fun σ z => ?_,
      IsModuleTopology.continuous_of_linearMap _, fun z h => ?_⟩, ?_⟩
  · exact congrArg Prod.fst (hρ σ z)
  · obtain ⟨x, hx, y, hy, rfl⟩ := hs z h
    change (e.symm _).1 ∈ _
    rw [he]; exact hx
  · exact congrArg Prod.snd (hρ σ z)
  · obtain ⟨x, hx, y, hy, rfl⟩ := hs z h
    change (e.symm _).2 ∈ _
    rw [he]; exact hy
  · unfold latAdd latId
    congr 1
    exact LinearMap.ext hz

variable (W : LocWach PD LL O v n₀)

theorem map_mem {T Z : LocLat G Qp LL O} (f : LatHom T.L Z.L) (x : ↥(DΔ W T)) :
    W.map f (x : W.DD T) ∈ DΔ W Z := fun δ hδ => by
  rw [← W.map_γ, x.2 δ hδ]

theorem red_sum {k : Type} [Field k] [Algebra O k] {l n : ℕ} {R : RingPG k l} {F : DFun R n G}
    {ι : k⸨X⸩ →ₐ[k] k⸨X⸩} {τ : ZMod n → ZMod n₀} {γ : W.Gam} (p : Pres W F ι τ γ)
    {T T' Z : LocLat G Qp LL O} {A A' C : Ob k G} {q q' r}
    (hq : Onto T A q) (hq' : Onto T' A' q') (hr : Onto Z C r)
    (hT : IsCrys PD T.ρ) (hT' : IsCrys PD T'.ρ) (hZ : IsCrys PD Z.ρ)
    (f : LatHom T.L Z.L) (g : LatHom T'.L Z.L) (a : (Fin A.m → k) →ₗ[k] (Fin C.m → k))
    (b : (Fin A'.m → k) →ₗ[k] (Fin C.m → k)) (hb : Function.Bijective (f.f.coprod g.f))
    (hs : ∀ z ∈ Z.L.T, ∃ x ∈ T.L.T, ∃ y ∈ T'.L.T, z = f.f x + g.f y) (ha : IsHom A C a) (hb' : IsHom A' C b)
    (hfa : ∀ (x : ↥T.L.T) (x' : ↥Z.L.T), (x' : Z.V) = f.f x → r x' = a (q x))
    (hgb : ∀ (x : ↥T'.L.T) (x' : ↥Z.L.T), (x' : Z.V) = g.f x → r x' = b (q' x))
    (N : Lats k n A.m) (N' : Lats k n A'.m) (L : Lats k n C.m)
    (hN : ∀ i y, y ∈ N i ↔ ∃ x : ↥(DΔ W T), (x : W.DD T) ∈ W.N T ∧ p.j T A q i x = y)
    (hN' : ∀ i y, y ∈ N' i ↔ ∃ x : ↥(DΔ W T'), (x : W.DD T') ∈ W.N T' ∧ p.j T' A' q' i x = y)
    (hL : ∀ i y, y ∈ L i ↔ ∃ x : ↥(DΔ W Z), (x : W.DD Z) ∈ W.N Z ∧ p.j Z C r i x = y) (i : ZMod n) :
    L i = F.push A C a N i ⊔ F.push A' C b N' i := by
  obtain ⟨π, π', hπ⟩ := exists_proj f g hb hs
  apply le_antisymm
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := (hL i y).1 hy
    let x₁ : ↥(DΔ W T) := ⟨_, map_mem W π x⟩
    let x₂ : ↥(DΔ W T') := ⟨_, map_mem W π' x⟩
    have hsum : x = ⟨_, map_mem W f x₁⟩ + ⟨_, map_mem W g x₂⟩ := by
      apply Subtype.ext
      have := W.map_id Z x
      rw [← hπ, W.map_latAdd, W.map_comp, W.map_comp] at this
      exact this.symm
    rw [hsum, map_add, p.j_map T A q Z C r hq hr f a ha hfa i x₁ _ rfl,
      p.j_map T' A' q' Z C r hq' hr g b hb' hgb i x₂ _ rfl]
    exact Submodule.add_mem_sup
      ⟨_, (hN i _).2 ⟨x₁, W.map_N π hZ hT _ hx, rfl⟩, rfl⟩
      ⟨_, (hN' i _).2 ⟨x₂, W.map_N π' hZ hT' _ hx, rfl⟩, rfl⟩
  · refine sup_le ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨x, hx, rfl⟩ := (hN i y).1 hy
      exact (hL i _).2 ⟨⟨_, map_mem W f x⟩, W.map_N f hT hZ _ hx,
        p.j_map T A q Z C r hq hr f a ha hfa i x _ rfl⟩
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨x, hx, rfl⟩ := (hN' i y).1 hy
      exact (hL i _).2 ⟨⟨_, map_mem W g x⟩, W.map_N g hT' hZ _ hx,
        p.j_map T' A' q' Z C r hq' hr g b hb' hgb i x _ rfl⟩

end General

theorem reduction_sum : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (S : TopSit P) (k : Type) [Field k] [Algebra S.O k] [CharP k l], S.IsRes k → ∀ {R : RingPG k l} (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) (F : DFun R S.n S.G) (τ : ZMod S.n → ZMod (Module.finrank ℚ_[l] ↥(K0 S.K))) (γ : (S.W H).Gam) (p : Pres (S.W H) F ι τ γ), GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι → (∀ i, (S.W H).emb (τ i) = S.emb i) → ((S.W H).χΓ γ : S.O) = 1 + (l : S.O) → GlobalTheory.WachUse.QN (S.W H) → ∀ (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (A : Ob k S.G) q (U : ZMod S.n → Multiset ℤ), Onto T A q → KerIs S.Γ.lam q → CrysWith (P.PD S.K) S.emb T.ρ U → ∀ (T' : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (A' : Ob k S.G) q' (U' : ZMod S.n → Multiset ℤ), Onto T' A' q' → KerIs S.Γ.lam q' → CrysWith (P.PD S.K) S.emb T'.ρ U' → ∀ (Z : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (C : Ob k S.G) r (V : ZMod S.n → Multiset ℤ), Onto Z C r → KerIs S.Γ.lam r → CrysWith (P.PD S.K) S.emb Z.ρ V → ∀ (f : LatHom T.L Z.L) (g : LatHom T'.L Z.L) (a : (Fin A.m → k) →ₗ[k] (Fin C.m → k)) (b : (Fin A'.m → k) →ₗ[k] (Fin C.m → k)), Function.Bijective (f.f.coprod g.f) → (∀ z ∈ Z.L.T, ∃ x ∈ T.L.T, ∃ y ∈ T'.L.T, z = f.f x + g.f y) → IsHom A C a → IsHom A' C b → (∀ (x : ↥T.L.T) (x' : ↥Z.L.T), (x' : Z.V) = f.f x → r x' = a (q x)) → (∀ (x : ↥T'.L.T) (x' : ↥Z.L.T), (x' : Z.V) = g.f x → r x' = b (q' x)) → ∀ (N : Lats k S.n A.m) (N' : Lats k S.n A'.m) (L : Lats k S.n C.m), (∀ i y, y ∈ N i ↔ ∃ x : ↥(DΔ (S.W H) T), (x : (S.W H).DD T) ∈ (S.W H).N T ∧ p.j T A q i x = y) → (∀ i y, y ∈ N' i ↔ ∃ x : ↥(DΔ (S.W H) T'), (x : (S.W H).DD T') ∈ (S.W H).N T' ∧ p.j T' A' q' i x = y) → (∀ i y, y ∈ L i ↔ ∃ x : ↥(DΔ (S.W H) Z), (x : (S.W H).DD Z) ∈ (S.W H).N Z ∧ p.j Z C r i x = y) → ∀ i, L i = F.push A C a N i ⊔ F.push A' C b N' i := by
  intro l _ P H S k _ _ _ _ R ι F τ γ p _ _ _ _ T A q U hq _ hT T' A' q' U' hq' _ hT' Z C r V hr _ hZ
    f g a b hb hs ha hb' hfa hgb N N' L hN hN' hL i
  exact red_sum (S.W H) p hq hq' hr hT.1 hT'.1 hZ.1 f g a b hb hs ha hb' hfa hgb N N' L hN hN' hL i

end GlobalTheory.Present.SumRed
