import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopLeOfClosedPoint
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.QCoh GlobalTheory.ChainPts GlobalTheory.ChainPts.PullHT
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.Twist (resM resM_resM)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChainPts.FrameNorm

open GlobalTheory.VB (IsFrame)

theorem repr_eq_sum {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]
    (b b' : Module.Basis ι R M) (u : M) (m : ι) : b'.repr u m = ∑ l, b.repr u l * b'.repr (b l) m := by
  conv_lhs => rw [← b.sum_repr u]
  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]

theorem exists_transition {X : Scheme.{0}} {F : X.Modules} {r : ℕ} (d : Bool) {V V₁ V' : X.Opens}
    {e : Fin r → Γ(F, V)} {e₁ : Fin r → Γ(F, V₁)} {s : Fin r → Γ(F, V')} (he : IsFrame e) (he₁ : IsFrame e₁)
    (hs : IsFrame s) : ∃ B : Fin r → Fin r → Γ(X, V ⊓ V₁), ∀ (U : X.Opens) (h₀ : U ≤ V ⊓ V₁) (h : U ≤ V ⊓ V')
      (h₁ : U ≤ V₁ ⊓ V') (m i : Fin r),
      resG X h₁ (coef d he₁ hs m i) = ∑ l, resG X h₀ (B m l) * resG X h (coef d he hs l i) := by
  cases d
  · refine ⟨fun m l => (he₁.basis inf_le_right).repr (resM F inf_le_left (e l)) m, fun U h₀ h h₁ m i => ?_⟩
    simp only [coef, ← IsFrame.repr_resM, resM_resM]
    rw [repr_eq_sum (he.basis (h.trans inf_le_left))]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_comm, IsFrame.basis_apply]
  · refine ⟨fun m l => (he.basis inf_le_left).repr (resM F inf_le_right (e₁ m)) l, fun U h₀ h h₁ m i => ?_⟩
    simp only [coef, ← IsFrame.repr_resM, resM_resM]
    rw [repr_eq_sum (he.basis (h.trans inf_le_left))]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [IsFrame.basis_apply]

def valHom {k : Type} [Field k] {X : Scheme.{0}} (x : Sp k ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* k :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.comp (x.appLE U ⊤ h).hom

theorem valF_eq_valHom {k : Type} [Field k] {X : Scheme.{0}} (x : Sp k ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (a : Γ(X, U)) : valF x U a = valHom x U h a := dif_pos h

theorem valHom_resG {k : Type} [Field k] {X : Scheme.{0}} (x : Sp k ⟶ X) {U V : X.Opens} (e : V ≤ U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (a : Γ(X, U)) : valHom x V h (resG X e a) = valF x U a := by
  have h' : ⊤ ≤ x ⁻¹ᵁ U := fun q hq => e (h hq)
  rw [valF, dif_pos h', ← Scheme.Hom.map_appLE x h (homOfLE e).op]
  rfl

theorem norm_valF_le_one {X : Scheme.{0}} (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C]
    (w : Sp ↥(intO C) ⟶ X) (U : X.Opens) (hw : ⊤ ≤ w ⁻¹ᵁ U) (a : Γ(X, U)) :
    ‖valF (spMap (intO C).subtype ≫ w) U a‖ ≤ 1 := by
  have h' : ⊤ ≤ (spMap (intO C).subtype ≫ w) ⁻¹ᵁ U := fun q _ => hw (Set.mem_univ (spMap (intO C).subtype q))
  rw [valF, dif_pos h']
  have e : (spMap (intO C).subtype ≫ w).appLE U ⊤ h' = w.appLE U ⊤ hw ≫ (spMap (intO C).subtype).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE (spMap (intO C).subtype) w U ⊤ ⊤ hw le_rfl).symm
  have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (intO C).subtype)
  have n' := congrArg (fun q => q.hom ((w.appLE U ⊤ hw).hom a)) n
  rw [e]
  refine le_of_eq_of_le (congrArg norm n') ?_
  exact ((Scheme.ΓSpecIso (CommRingCat.of ↥(intO C))).hom.hom ((w.appLE U ⊤ hw).hom a)).2

theorem norm_le_of_norm_le {X : Scheme.{0}} {F : X.Modules} {r : ℕ} (d : Bool) {V V₁ V' : X.Opens}
    {e : Fin r → Γ(F, V)} {e₁ : Fin r → Γ(F, V₁)} {s : Fin r → Γ(F, V')} (he : IsFrame e) (he₁ : IsFrame e₁)
    (hs : IsFrame s) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (w : Sp ↥(intO C) ⟶ X)
    (hV : ⊤ ≤ w ⁻¹ᵁ V) (hV₁ : ⊤ ≤ w ⁻¹ᵁ V₁) (cf : Fin r → C)
    (H : ∀ l, ‖∑ i, cf i * valF (spMap (intO C).subtype ≫ w) _ (coef d he hs l i)‖ ≤ 1) (m : Fin r) :
    ‖∑ i, cf i * valF (spMap (intO C).subtype ≫ w) _ (coef d he₁ hs m i)‖ ≤ 1 := by
  by_cases hx : ⊤ ≤ (spMap (intO C).subtype ≫ w) ⁻¹ᵁ (V₁ ⊓ V')
  · obtain ⟨B, hB⟩ := exists_transition d he he₁ hs
    have hw : ⊤ ≤ w ⁻¹ᵁ (V ⊓ V₁) := fun q hq => ⟨hV hq, hV₁ hq⟩
    have hU : ⊤ ≤ (spMap (intO C).subtype ≫ w) ⁻¹ᵁ (V ⊓ (V₁ ⊓ V')) :=
      fun q hq => ⟨hV (Set.mem_univ (spMap (intO C).subtype q)), hx hq⟩
    have h₀ : V ⊓ (V₁ ⊓ V') ≤ V ⊓ V₁ := inf_le_inf_left _ inf_le_left
    have h : V ⊓ (V₁ ⊓ V') ≤ V ⊓ V' := inf_le_inf_left _ inf_le_right
    have h₁ : V ⊓ (V₁ ⊓ V') ≤ V₁ ⊓ V' := inf_le_right
    have key : ∀ i, valF (spMap (intO C).subtype ≫ w) _ (coef d he₁ hs m i) =
        ∑ l, valF (spMap (intO C).subtype ≫ w) _ (B m l) *
          valF (spMap (intO C).subtype ≫ w) _ (coef d he hs l i) := fun i => by
      rw [← valHom_resG _ h₁ hU, hB _ h₀ h h₁, map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_mul, valHom_resG, valHom_resG]
    have eq : ∑ i, cf i * valF (spMap (intO C).subtype ≫ w) _ (coef d he₁ hs m i) =
        ∑ l, valF (spMap (intO C).subtype ≫ w) _ (B m l) *
          ∑ i, cf i * valF (spMap (intO C).subtype ≫ w) _ (coef d he hs l i) := by
      simp only [key, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [eq]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun l _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (norm_valF_le_one C w _ hw _) (norm_nonneg _) (H l)
  · simp only [valF, dif_neg hx, mul_zero, Finset.sum_const_zero, norm_zero, zero_le_one]

theorem norm_le_one_iff : ∀ {X : Scheme.{0}} {F : X.Modules} {r : ℕ} (d : Bool) {V V₁ V' : X.Opens} {e : Fin r → Γ(F, V)} {e₁ : Fin r → Γ(F, V₁)} {s : Fin r → Γ(F, V')} (he : GlobalTheory.VB.IsFrame e) (he₁ : GlobalTheory.VB.IsFrame e₁) (hs : GlobalTheory.VB.IsFrame s) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (w : Sp ↥(intO C) ⟶ X), ⊤ ≤ w ⁻¹ᵁ V → ⊤ ≤ w ⁻¹ᵁ V₁ → ∀ cf : Fin r → C, (∀ l, ‖∑ i, cf i * valF (spMap (intO C).subtype ≫ w) _ (coef d he hs l i)‖ ≤ 1) ↔ ∀ l, ‖∑ i, cf i * valF (spMap (intO C).subtype ≫ w) _ (coef d he₁ hs l i)‖ ≤ 1 :=
  fun d _ _ _ _ _ _ he he₁ hs C _ _ w hV hV₁ cf =>
    ⟨norm_le_of_norm_le d he he₁ hs C w hV hV₁ cf, norm_le_of_norm_le d he₁ he hs C w hV₁ hV cf⟩

end GlobalTheory.ChainPts.FrameNorm

end
