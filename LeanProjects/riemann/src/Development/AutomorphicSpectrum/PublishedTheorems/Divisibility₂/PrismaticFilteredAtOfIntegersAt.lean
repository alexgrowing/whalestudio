import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SettingInhabited
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeAtOfPrismaticDieudonneAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrder

set_option autoImplicit false

noncomputable section

open CategoryTheory WittVector Ideal

namespace GlobalTheory.CompanionTheory.Published

open GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta

def PrismaticDieudonneIntegersAt {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (span {(p : O)}) O] (ε : PreTilt O p) (h0 : zeta ε 0 = 1) : Prop :=
  ∃ (M : PDivGroup p O → ModuleCat.{0} (Ainf p O))
    (map : ∀ G H : PDivGroup p O, (G ⟶ H) →+ (M H →ₗ[Ainf p O] M G))
    (φ : ∀ G : PDivGroup p O, M G →ₛₗ[(frobenius : Ainf p O →+* Ainf p O)] M G)
    (lie : ∀ G : PDivGroup p O, M G →ₛₗ[fontaineTheta O p] G.dual.Lie)
    (du : ∀ G : PDivGroup p O, M G.dual ≃ₗ[Ainf p O] Module.Dual (Ainf p O) (M G))
    (l : M (PDivGroup.mu p O)) (e : M (const p O)),
    (∀ G : PDivGroup p O, Module.Projective (Ainf p O) (M G) ∧ Module.Finite (Ainf p O) (M G) ∧
      (∀ q, Module.rankAtStalk (R := Ainf p O) (M G) q = G.height) ∧
      (∀ m, ∃ n, φ G n = frobenius (xi ε) • m) ∧
      Function.Surjective (lie G) ∧ (∀ m, lie G m = 0 ↔ ∃ n, φ G m = frobenius (xi ε) • n) ∧
      map G G (𝟙 G) = LinearMap.id) ∧
    (∀ (G H K : PDivGroup p O) (f : G ⟶ H) (g : H ⟶ K), map G K (f ≫ g) = map G H f ∘ₗ map H K g) ∧
    (∀ (G H : PDivGroup p O) (f : G ⟶ H) (m : M H),
      map G H f (φ H m) = φ G (map G H f m) ∧
      lie G (map G H f m) = lieMap H.dual G.dual (dualHom G H f) (lie H m) ∧
      ∀ x : M G.dual, du H (map H.dual G.dual (dualHom G H f) x) m = du G x (map G H f m)) ∧
    Function.Bijective (LinearMap.toSpanSingleton (Ainf p O) _ l) ∧
    Function.Bijective (LinearMap.toSpanSingleton (Ainf p O) _ e) ∧
    φ _ l = frobenius (xi ε) • l ∧ φ _ e = e ∧
    map _ _ (epsHom (zeta ε) h0 (zeta_succ_pow ε)) l = Sandwich.mu ε • e ∧
    du (PDivGroup.mu p O) e l = 1

def PrismaticDieudonneIntegers : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O →
    ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O] (ε : PreTilt O p)
      (hε : IsPrimitiveRoot (root ε).untilt p),
      PrismaticDieudonneIntegersAt ε (GlobalTheory.Dieudonne.untilt_root_zero hε)

end GlobalTheory.CompanionTheory.Published

namespace GlobalTheory.CompanionTheory.Ar.Prism

open GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich

def PrismaticFilteredAt {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (span {(p : O)}) O] (ε : PreTilt O p) : Prop :=
  ∃ (M : PDivGroup p O → ModuleCat.{0} (Ainf p O))
    (map : ∀ G H : PDivGroup p O, (G ⟶ H) →+ (M H →ₗ[Ainf p O] M G))
    (φ : ∀ G : PDivGroup p O, M G →ₛₗ[(frobenius : Ainf p O →+* Ainf p O)] M G)
    (lie : ∀ G : PDivGroup p O, M G →ₛₗ[fontaineTheta O p] G.dual.Lie)
    (du : ∀ G : PDivGroup p O, M G.dual ≃ₗ[Ainf p O] Module.Dual (Ainf p O) (M G))
    (l : M (PDivGroup.mu p O)) (e : M (const p O)),
    (∀ G : PDivGroup p O, Module.Projective (Ainf p O) (M G) ∧ Module.Finite (Ainf p O) (M G) ∧
      (∀ q, Module.rankAtStalk (R := Ainf p O) (M G) q = G.height) ∧
      (∀ m, ∃ n, φ G n = frobenius (xi ε) • m) ∧
      Function.Surjective (lie G) ∧ (∀ m, lie G m = 0 ↔ ∃ n, φ G m = frobenius (xi ε) • n) ∧
      (∀ (x : M G.dual) (m : M G), du G (φ G.dual x) (φ G m) = frobenius (xi ε) * frobenius (du G x m)) ∧
      map G G (𝟙 G) = LinearMap.id) ∧
    (∀ (G H K : PDivGroup p O) (f : G ⟶ H) (g : H ⟶ K), map G K (f ≫ g) = map G H f ∘ₗ map H K g) ∧
    (∀ (G H : PDivGroup p O) (f : G ⟶ H) (m : M H),
      map G H f (φ H m) = φ G (map G H f m) ∧
      lie G (map G H f m) = lieMap H.dual G.dual (dualHom G H f) (lie H m) ∧
      ∀ x : M G.dual, du H (map H.dual G.dual (dualHom G H f) x) m = du G x (map G H f m)) ∧
    (Function.Bijective (LinearMap.toSpanSingleton (Ainf p O) _ l) ∧
      Function.Bijective (LinearMap.toSpanSingleton (Ainf p O) _ e) ∧
      φ _ l = frobenius (xi ε) • l ∧ φ _ e = e) ∧
    Function.Injective (map (const p O) (PDivGroup.mu p O)) ∧
    ∀ u : M (PDivGroup.mu p O) →ₗ[Ainf p O] M (const p O), (∀ m, u (φ _ m) = φ _ (u m)) →
      ∃ f, map (const p O) (PDivGroup.mu p O) f = u

def PrismaticFiltered : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O →
    ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O] (ε : PreTilt O p),
      IsPrimitiveRoot (root ε).untilt p → PrismaticFilteredAt ε

section Proofs

open GlobalTheory.PrismHodge GlobalTheory.Dieudonne GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

omit [IsAdicComplete (span {(p : O)}) O] in

theorem frobenius_ofPadic_eq (c : ℤ_[p]) :
    (WittVector.frobenius (ofPadic p O c) : Ainf p O) = ofPadic p O c := by
  ext n
  rw [coeff_frobenius_charP]
  simp only [ofPadic, RingHom.comp_apply, map_coeff]
  rw [← map_pow, ZMod.pow_card]

theorem exists_padic_of_eigen [IsDomain (PreTilt O p)] {ε : PreTilt O p}
    (hε : IsPrimitiveRoot (root ε).untilt p) {a : Ainf p O}
    (h : WittVector.frobenius a = WittVector.frobenius (xi ε) * a) :
    ∃ c : ℤ_[p], ofPadic p O c * Sandwich.mu ε = a := by
  let : Algebra ℤ_[p] (Ainf p O) := (ofPadic p O).toAlgebra
  have hs : ∀ (c : ℤ_[p]) (x : Ainf p O), c • x = ofPadic p O c * x := fun _ _ => rfl
  have : IsAdicComplete (span {(p : Ainf p O)}) (Ainf p O) := WittVector.isAdicCompleteIdealSpanP
  let N : Submodule ℤ_[p] (Ainf p O) :=
    { carrier := {a | WittVector.frobenius a = WittVector.frobenius (xi ε) * a}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [map_add, ha, hb, mul_add]
      zero_mem' := by simp
      smul_mem' := fun c a ha => by
        simp only [Set.mem_ofPred_eq] at ha ⊢
        rw [hs, map_mul, frobenius_ofPadic_eq, ha]; ring }
  let m : N := ⟨Sandwich.mu ε, frobenius_mu ε⟩
  suffices hsurj : Function.Surjective (LinearMap.toSpanSingleton ℤ_[p] N m) by
    obtain ⟨c, hc⟩ := hsurj ⟨a, h⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  refine TateFree.surjective_of_mod _ (fun y hy => ?_) (fun y => ?_)
  · refine Subtype.ext (IsHausdorff.haus' (I := span {(p : Ainf p O)}) _ fun n => ?_)
    obtain ⟨z, hz⟩ := hy n
    rw [SModEq.zero, ← hz, Ideal.span_singleton_pow, Submodule.coe_smul, hs, map_pow, map_natCast,
      ← smul_eq_mul]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  · obtain ⟨c, b, hc, hb⟩ := GlobalTheory.DieudonneTest.eigen_step hε y.2
    refine ⟨c, ⟨b, hb⟩, Subtype.ext ?_⟩
    change ofPadic p O p * b = y - ofPadic p O c * Sandwich.mu ε
    rw [map_natCast, map_intCast, hc]; ring

example (h : Published.PrismaticDieudonneIntegers) (p : ℕ) [Fact p.Prime] :
    ∃ (_ : Fact ¬IsUnit ((p : ℕ) : 𝓞_ℂ_[p]))
      (_ : IsAdicComplete (span {((p : ℕ) : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p]) (ε : PreTilt 𝓞_ℂ_[p] p)
      (hε : IsPrimitiveRoot (root ε).untilt p),
      Published.PrismaticDieudonneIntegersAt ε (untilt_root_zero hε) := by
  obtain ⟨h1, h2, ε, hv, hε⟩ := PadicComplexHost.main p
  exact ⟨h1, h2, ε, hε, h p ℂ_[p] Valued.v _ hv ε hε⟩

end Proofs

end GlobalTheory.CompanionTheory.Ar.Prism
