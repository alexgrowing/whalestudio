import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonneAt

noncomputable section

open CategoryTheory WittVector Ideal TensorProduct Coalgebra

namespace GlobalTheory.PrismHodge

open GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.Published

section Torsion

variable {p : ℕ} {O : Type} [CommRing O] (G : PDivGroup p O)

variable [Fact p.Prime] [IsDomain O]

end Torsion

section Integers

variable {p : ℕ} [Fact p.Prime] {C : Type} [NormedField C] [NormedAlgebra ℚ_[p] C]
  {O : Type} [CommRing O] [Algebra O C] (H : IsIntegers O C)
include H

theorem integers_valuation [IsUltrametricDist C] :
    (NormedField.valuation (K := C)).Integers O where
  hom_inj := H.inj
  map_le_one a := by
    rw [NormedField.valuation_apply]
    exact_mod_cast (H.mem_iff _).1 ⟨a, rfl⟩
  exists_of_le_one x hx := (H.mem_iff x).2 (by
    rw [NormedField.valuation_apply] at hx
    exact_mod_cast hx)

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]

omit [IsAdicComplete (span {(p : O)}) O] in
theorem isDomain_ainf : IsDomain (Ainf p O) := by
  have : IsUltrametricDist C := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  have : IsDomain (PreTilt O p) := PreTilt.isDomain C _ O (integers_valuation H) p
  infer_instance

end Integers

section Main

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O]

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O] {ε : PreTilt O p}

theorem theta_nu_ne_zero (hε : IsPrimitiveSystem ε) : fontaineTheta O p (nu ε) ≠ 0 := by
  rw [nu, map_sub, fontaineTheta_teichmuller, map_one, sub_ne_zero]
  have : Nontrivial O := ⟨p, 1, fun h => (Fact.out : ¬IsUnit (p : O)) (h ▸ isUnit_one)⟩
  exact (hε 1).ne_one (by simpa using (Fact.out : p.Prime).one_lt)

theorem mu_ne_zero (hε : IsPrimitiveSystem ε) : Sandwich.mu ε ≠ 0 := fun h =>
  theta_nu_ne_zero hε (by rw [← phiInv_mu, h, map_zero, map_zero])

variable {C : Type} [NormedField C] [NormedAlgebra ℚ_[p] C] [IsAlgClosed C] [Algebra O C]

def PrismaticDieudonneHodgeAt (hε : IsPrimitiveSystem ε) : Prop :=
  ∃ (M : PDivGroup p O → ModuleCat.{0} (Ainf p O))
    (map : ∀ G H : PDivGroup p O, (G ⟶ H) →+ (M H →ₗ[Ainf p O] M G))
    (φ : ∀ G, M G →ₛₗ[(frobenius : Ainf p O →+* Ainf p O)] M G)
    (lie : ∀ G, M G →ₛₗ[fontaineTheta O p] G.dual.Lie)
    (dR : ∀ G, M G →ₛₗ[fontaineTheta O p] G.RigExt),
    ((∀ G, Module.Free (Ainf p O) (M G) ∧ Module.Finite (Ainf p O) (M G) ∧
      Module.finrank (Ainf p O) (M G) = G.height ∧
      Function.Injective (φ G) ∧ (∀ m, ∃ n, φ G n = frobenius (xi ε) • m) ∧
      Module.Projective O G.dual.Lie ∧ Function.Surjective (lie G) ∧
      (∀ m, lie G m = 0 ↔ ∃ n, φ G m = frobenius (xi ε) • n) ∧
      Function.Surjective (dR G) ∧ (∀ m, dR G m = 0 ↔ ∃ n, m = xi ε • n) ∧
      map G G (𝟙 G) = LinearMap.id) ∧
    (∀ (G H K : PDivGroup p O) (f : G ⟶ H) (g : H ⟶ K),
      map G K (f ≫ g) = map G H f ∘ₗ map H K g) ∧
    (∀ (G H : PDivGroup p O) (f : G ⟶ H) (m : M H),
      map G H f (φ H m) = φ G (map G H f m) ∧
      lie G (map G H f m) = lieMap H.dual G.dual (dualHom G H f) (lie H m) ∧
      dR G (map G H f m) = rigExtMap f (dR H m)) ∧
    (∀ G H : PDivGroup p O, Function.Injective (map G H) ∧
      ∀ u : M H →ₗ[Ainf p O] M G, (∀ m, u (φ H m) = φ G (u m)) → ∃ f, map G H f = u) ∧
    ∃ (l : M (PDivGroup.mu p O)) (e : M (const p O)),
      Function.Bijective (LinearMap.toSpanSingleton (Ainf p O) _ l) ∧
      Function.Bijective (LinearMap.toSpanSingleton (Ainf p O) _ e) ∧
      φ _ l = frobenius (xi ε) • l ∧ φ _ e = e ∧
      map _ _ (epsHom (zeta ε) hε.zeta_zero (zeta_succ_pow ε)) l = Sandwich.mu ε • e) ∧
    (∀ (G : PDivGroup p O) (m : M G), lie G m = 0 ↔ dR G m ∈ LinearMap.range G.rigOfOmega) ∧
    ∃ ι : ∀ G : PDivGroup p O, G.VecExt ≃ₗ[O] G.dual.Lie,
      (∀ (G : PDivGroup p O) (m : M G), ι G (G.rigToExt (dR G m)) = lie G m) ∧
      ∀ (G H : PDivGroup p O) (f : G ⟶ H) (x : H.VecExt),
        ι G (vecExtMap f x) = lieMap H.dual G.dual (dualHom G H f) (ι H x)

end Main

end GlobalTheory.PrismHodge
