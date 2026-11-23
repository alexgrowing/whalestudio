import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPinnedOfIsUnf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelGroupLiftExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelLiftFiniteCongruenceStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MarkingComponentUniqueFrameUniqueArithmeticGroup
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceLatticeFractionalMultipleAgree

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts GlobalTheory.GeoLevel
open GlobalTheory.Member (FinCong IotaOK)
open GlobalTheory.LevelCusp (IsMatch)
open GlobalTheory.Dict (castFr)
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GeoLevel.ModHalf

theorem mem_of_coprime {R A : Type} [CommRing R] [AddCommGroup A] [Module R A] {I J : Ideal R} (h : I ⊔ J = ⊤)
    (f : A →ₗ[R] A) (hf : ∀ a ∈ J • (⊤ : Submodule R A), f a ∈ I • (⊤ : Submodule R A)) (a : A) :
    f a ∈ I • (⊤ : Submodule R A) := by
  have h1 : (1 : R) ∈ I ⊔ J := by rw [h]; trivial
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 h1
  have : a = x • a + y • a := by rw [← add_smul, hxy, one_smul]
  rw [this, map_add, map_smul]
  exact add_mem (Submodule.smul_mem_smul hx trivial) (hf _ (Submodule.smul_mem_smul hy trivial))

theorem map_mem_smul_top {R A : Type} [CommRing R] [AddCommGroup A] [Module R A] {J : Ideal R}
    (f : A →ₗ[R] A) {a : A} (ha : a ∈ J • (⊤ : Submodule R A)) : f a ∈ J • (⊤ : Submodule R A) := by
  refine Submodule.smul_induction_on ha (fun r hr x _ => ?_) (fun x y hx hy => ?_)
  · rw [map_smul]; exact Submodule.smul_mem_smul hr trivial
  · rw [map_add]; exact add_mem hx hy

theorem mem_of_range {R A B : Type} [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    {I J : Ideal R} {N : ℕ} (h : I * J = Ideal.span {(N : R)}) (ι : A →ₗ[R] B) (hι : Function.Injective ι)
    {x y : A} {u : B} (hu : u ∈ LinearMap.range ι) (e : ι x - ι y = N • u) : x - y ∈ I • (⊤ : Submodule R A) := by
  obtain ⟨v, rfl⟩ := hu
  rw [← map_nsmul, ← map_sub] at e
  have e' : x - y = (N : R) • v := by rw [Nat.cast_smul_eq_nsmul]; exact hι e
  rw [e']
  refine Submodule.smul_mem_smul ?_ trivial
  have : (N : R) ∈ I * J := by
    rw [h]; exact Ideal.mem_span_singleton_self _
  exact (Ideal.mul_le_inf this).1

set_option maxHeartbeats 1600000 in

theorem mem_of_finVec {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (l : Level H) (V : HSp D)
    {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (hι : LatEmb V ι) (x y : La) (w : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) (hw : w ∈ latGHat V 1)
    (h : finVec V (ι x) - finVec V (ι y) = l.M • w) : x - y ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) La) := by
  obtain ⟨u, hu, e⟩ := GlobalTheory.MarkUniq.exists_of_finVec_eq_nsmul V 1 l.M (by have := l.three_le; omega)
    (ι x - ι y) w hw ((GlobalTheory.MarkUniq.finVec_sub V (ι x) (ι y)).trans h)
  exact mem_of_range l.prod ι hι.1 (hι.2.ge hu) e

theorem isLift_mul {D : D7} {V : HSp D} {r : ℕ} {hr : V.rank = r} {β : GL (Fin r) (EAf D)}
    {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)} {g h : Formalism.L2.DIV.G0 Pg r} {κ κ' : GA D V}
    (h1 : IsLift V hr β Pg g κ) (h2 : IsLift V hr β Pg h κ') : IsLift V hr β Pg (g * h) (κ * κ') := by
  obtain ⟨a1, b1, c1⟩ := h1
  obtain ⟨a2, b2, c2⟩ := h2
  refine ⟨mul_mem a1 a2, by rw [map_mul]; exact mul_mem b1 b2, fun w => ?_⟩
  have : (⟨finR V hr (κ * κ'), by rw [map_mul]; exact mul_mem b1 b2⟩ : Formalism.L2.DIV.St β) =
      ⟨finR V hr κ, b1⟩ * ⟨finR V hr κ', b2⟩ := Subtype.ext (map_mul _ _ _)
  rw [this, map_mul, c1, c2]; rfl

theorem flip_sub {M : Type} [AddCommGroup M] (N : ℕ) {p q w : M} (e : p - q = N • w) : q - p = N • (-w) := by
  rw [smul_neg, ← e, neg_sub]

theorem cocycle {M : Type} [AddCommGroup M] (k : M →+ M) (N : ℕ) {p q s t w₁ w₂ w₃ : M}
    (e1 : p - q = N • w₁) (e2 : k q - s = N • w₂) (e3 : k p - t = N • w₃) :
    t - s = N • (k w₁ + w₂ - w₃) := by
  rw [smul_sub, smul_add, ← map_nsmul, ← e1, ← e2, ← e3, map_sub]; abel

set_option maxHeartbeats 1600000 in

theorem action_mod_half : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l : Level H) (V : HSp D) (r : ℕ) (hr : V.rank = r) (β : GL (Fin r) (EAf D)) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)), IsLatBasis V hr β → (∀ w, w ∈ Pg ↔ l.Mb ≤ w.asIdeal) → ∀ (Dw : Datum H) (ι₀ : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)), LatEmb V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀) → ∀ γ : Formalism.L2.DIV.G0 Pg r → Dw.La →ₗ[𝓞 D.host.E] Dw.La, (∀ g, Induces Dw l V hr ι₀ β Pg g (γ g)) → (∀ a, γ 1 a - a ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) ∧ ∀ g h a, γ (g * h) a - γ g (γ h a) ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La) := by
  intro D H l V r hr β Pg hβ hPg Dw ι₀ hι γ hγ
  refine ⟨fun a => ?_, fun g h a => ?_⟩
  · refine mem_of_coprime l.coprime (γ 1 - LinearMap.id) (fun a ha => ?_) a
    obtain ⟨w, hw, e⟩ := hγ 1 1 (isLift_one V hr β Pg) a ha
    rw [map_one, Units.val_one, Matrix.one_mulVec] at e
    exact mem_of_finVec l V _ hι (γ 1 a) a (-w) (neg_mem hw) (flip_sub l.M e)
  · refine mem_of_coprime l.coprime (γ (g * h) - γ g ∘ₗ γ h) (fun a ha => ?_) a
    obtain ⟨κ, hκ⟩ := GlobalTheory.T.level_group_lift_exists D H l V r hr β Pg hβ hPg g
    obtain ⟨κ', hκ'⟩ := GlobalTheory.T.level_group_lift_exists D H l V r hr β Pg hβ hPg h
    obtain ⟨w₁, hw₁, e₁⟩ := hγ h κ' hκ' a ha
    obtain ⟨w₂, hw₂, e₂⟩ := hγ g κ hκ (γ h a) (map_mem_smul_top (γ h) ha)
    obtain ⟨w₃, hw₃, e₃⟩ := hγ (g * h) (κ * κ') (isLift_mul hκ hκ') a ha
    rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec] at e₃
    have hk := (GlobalTheory.Member.AALev.congruences_agree D V κ).1.2
      ((GlobalTheory.T.level_lift_finite_congruence D H l V r hr β Pg hβ hPg).1 g κ hκ) w₁ hw₁
    exact mem_of_finVec l V _ hι (γ (g * h) a) (γ g (γ h a)) _ (sub_mem (add_mem hk hw₂) hw₃)
      (cocycle (Matrix.mulVecLin (finHom V κ).1).toAddMonoidHom l.M e₁ e₂ e₃)

end GlobalTheory.GeoLevel.ModHalf
