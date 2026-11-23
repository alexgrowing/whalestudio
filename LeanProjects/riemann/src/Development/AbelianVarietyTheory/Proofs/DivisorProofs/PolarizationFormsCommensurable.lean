import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
open GlobalTheory.AbDual
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.RealMult.PolScale

section Push

variable {R : Type} [CommRing R] {I : Ideal R} {S : Scheme.{0}} {κ : DividedPowers I} {t : S ⟶ Sp R}
  {A : Over S} [GrpObj A]

theorem push_fst_inl (x : Crys κ t A) : push κ t (fst A A) (push κ t (inl A A) x) = x := by
  rw [push_push _ _ _ (lift_fst _ _), push_id]; rfl

theorem push_snd_inl (x : Crys κ t A) : push κ t (snd A A) (push κ t (inl A A) x) = 0 := by
  rw [push_push _ _ _ (lift_snd _ _), push_one]; rfl

theorem push_fst_inr (x : Crys κ t A) : push κ t (fst A A) (push κ t (inr A A) x) = 0 := by
  rw [push_push _ _ _ (lift_fst _ _), push_one]; rfl

theorem push_snd_inr (x : Crys κ t A) : push κ t (snd A A) (push κ t (inr A A) x) = x := by
  rw [push_push _ _ _ (lift_snd _ _), push_id]; rfl

theorem push_fst_diag (x : Crys κ t A) : push κ t (fst A A) (push κ t (lift (𝟙 A) (𝟙 A)) x) = x := by
  rw [push_push _ _ _ (lift_fst _ _), push_id]; rfl

theorem push_snd_diag (x : Crys κ t A) : push κ t (snd A A) (push κ t (lift (𝟙 A) (𝟙 A)) x) = x := by
  rw [push_push _ _ _ (lift_snd _ _), push_id]; rfl

theorem push_swap_inl (x : Crys κ t A) :
    push κ t (lift (snd A A) (fst A A)) (push κ t (inl A A) x) = push κ t (inr A A) x :=
  push_push _ _ _ (by rw [comp_lift, lift_snd, lift_fst]) x

theorem push_swap_inr (x : Crys κ t A) :
    push κ t (lift (snd A A) (fst A A)) (push κ t (inr A A) x) = push κ t (inl A A) x :=
  push_push _ _ _ (by rw [comp_lift, lift_snd, lift_fst]) x

end Push

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R]

theorem exists_corrForm (H : Published.AbelianDeRham.Free) (X : Obj F 𝔠 (Sp R)) (c : 𝔠.elt) :
    ∃ φ, IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P c) φ :=
  exists_isCorrForm (cupSquare_of_free H (AbelianSchemeGerms.isAbelianScheme_tensor X.A X.A X.ab X.ab)
    (smooth_prod X.dim X.dim)) (X.isLB c) (X.rig₁ c) (X.rig₂ c)

theorem corrForm_antisymm (H : Published.AbelianDeRham.Free) (X : Obj F 𝔠 (Sp R)) (c : 𝔠.elt)
    {φ : HdR X.A →ₗ[R] HdR X.A →ₗ[R] R} (hφ : IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P c) φ) (x y : HdR X.A) :
    φ x y = -φ y x := by
  have C := cupSquare_of_free H (AbelianSchemeGerms.isAbelianScheme_tensor X.A X.A X.ab X.ab) (smooth_prod X.dim X.dim)
  obtain ⟨ψ, hψ, e⟩ := hφ.isPolForm
  obtain ⟨ψ', hψ', k⟩ := hψ.pull (homMor (dp0 R) (𝟙 _) (lift (snd X.A X.A) (fst X.A X.A)))
  have hψ'' : IsPolForm (dp0 R) (𝟙 _) (X.A ⊗ X.A) (X.P c) ψ' := by
    obtain ⟨n, a, b, hc, rfl⟩ := hψ'
    exact ⟨n, a, b, (isChern_existsUnique_and_iso _ _ _ _ _).2 _ _ (pull_isLB (X.isLB c) _) (X.isLB c)
      (X.symm c).symm _ hc, rfl⟩
  have u := Published.AbelianDualCrystal.polForm_unique C (X.isLB c) hψ hψ''
  have k' := k (push (dp0 R) (𝟙 _) (lift (snd X.A X.A) (fst X.A X.A)) (push (dp0 R) (𝟙 _) (inl X.A X.A) x))
    (push (dp0 R) (𝟙 _) (inl X.A X.A) x)
    (push (dp0 R) (𝟙 _) (lift (snd X.A X.A) (fst X.A X.A)) (push (dp0 R) (𝟙 _) (inr X.A X.A) y))
    (push (dp0 R) (𝟙 _) (inr X.A X.A) y) (fun _ ↦ rfl) fun _ ↦ rfl
  rw [← u, RingHom.id_apply, push_swap_inl, push_swap_inr, e, e] at k'
  simp only [push_fst_inl, push_snd_inl, push_fst_inr, push_snd_inr, map_zero, LinearMap.zero_apply,
    sub_zero, zero_sub] at k'
  exact k'

theorem isPolForm_diag (X : Obj F 𝔠 (Sp R)) (c : 𝔠.elt) {φ : HdR X.A →ₗ[R] HdR X.A →ₗ[R] R}
    (hφ : IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P c) φ) :
    IsPolForm (dp0 R) (𝟙 _) X.A (X.diag c) (φ - LinearMap.flip φ : HdR X.A →ₗ[R] HdR X.A →ₗ[R] R) := by
  obtain ⟨ψ, hψ, e⟩ := hφ.isPolForm
  obtain ⟨ψ', hψ', k⟩ := hψ.pull (homMor (dp0 R) (𝟙 _) (lift (𝟙 X.A) (𝟙 X.A)))
  have eq : (φ - LinearMap.flip φ : HdR X.A →ₗ[R] HdR X.A →ₗ[R] R) = ψ' := by
    refine LinearMap.ext fun x ↦ LinearMap.ext fun y ↦ ?_
    rw [k (push (dp0 R) (𝟙 _) (lift (𝟙 X.A) (𝟙 X.A)) x) x (push (dp0 R) (𝟙 _) (lift (𝟙 X.A) (𝟙 X.A)) y) y
      (fun _ ↦ rfl) (fun _ ↦ rfl), RingHom.id_apply, e]
    simp only [push_fst_diag, push_snd_diag, LinearMap.sub_apply, LinearMap.flip_apply]
  rw [eq]
  exact hψ'

theorem exists_corrForm_smul (X : Obj F 𝔠 (Sp R)) (a : 𝓞 F) (c : 𝔠.elt) {φ : HdR X.A →ₗ[R] HdR X.A →ₗ[R] R}
    (hφ : IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P c) φ) :
    ∃ φ' : HdR X.A →ₗ[R] HdR X.A →ₗ[R] R, IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P (a • c)) φ' ∧
      ∀ x y, φ' x y = φ x (act (dp0 R) (𝟙 _) X.rm a y) := by
  haveI := X.rm.hom a
  obtain ⟨φ', h', k⟩ := hφ.pull (X.isLB c) (homMor (dp0 R) (𝟙 _) (𝟙 X.A)) (homMor (dp0 R) (𝟙 _) (X.rm.act a))
    (h := (lift (fst X.A X.A) (snd X.A X.A ≫ X.rm.act a)).left)
    (by simp only [← Over.comp_left, lift_fst, Category.comp_id])
    (by simp only [← Over.comp_left, lift_snd]) (X.isLB (a • c)) (X.smul a c).symm
  refine ⟨φ', h', fun x y ↦ ?_⟩
  rw [k (push (dp0 R) (𝟙 _) (𝟙 X.A) x) x (push (dp0 R) (𝟙 _) (X.rm.act a) y) y (fun _ ↦ rfl) (fun _ ↦ rfl),
    RingHom.id_apply, push_id, act_apply]
  rfl

theorem exists_nat_smul_eq (c c₀ : 𝔠.elt) (h₀ : (c₀ : F) ≠ 0) :
    ∃ (n : ℕ) (t : 𝓞 F), n ≠ 0 ∧ (n : 𝓞 F) • c = t • c₀ := by
  obtain ⟨y, hy, hi⟩ := IsAlgebraic.exists_integral_multiple
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic ((c : F) / c₀)))
  let s : 𝓞 F := ⟨y • ((c : F) / c₀), hi⟩
  have hs : (s : F) * c₀ = (y : F) * c := by
    change y • ((c : F) / c₀) * c₀ = _
    rw [zsmul_eq_mul]; field_simp
  have key : ∀ (n : ℕ) (t : 𝓞 F), (t : F) * c₀ = (n : F) * c → (n : 𝓞 F) • c = t • c₀ := fun n t e ↦ by
    apply Subtype.ext
    simp only [Submodule.coe_smul, Algebra.smul_def, map_natCast]
    exact e.symm.trans rfl
  rcases Int.natAbs_eq y with h | h
  · have hn : ((y.natAbs : ℕ) : F) = (y : F) := by rw [← Int.cast_natCast, ← h]
    exact ⟨y.natAbs, s, Int.natAbs_ne_zero.2 hy, key _ _ (by rw [hs, hn])⟩
  · have hn : (y : F) = -((y.natAbs : ℕ) : F) := by
      rw [← Int.cast_natCast, ← Int.cast_neg]; exact congrArg Int.cast h
    refine ⟨y.natAbs, -s, Int.natAbs_ne_zero.2 hy, key _ _ ?_⟩
    rw [show ((-s : 𝓞 F) : F) = -(s : F) from rfl, neg_mul, hs, hn]; ring

theorem act_natCast (X : Obj F 𝔠 (Sp R)) (n : ℕ) (x : HdR X.A) :
    act (dp0 R) (𝟙 _) X.rm (n : 𝓞 F) x = (n : R) • x := by
  rw [map_natCast]; simp [Nat.cast_smul_eq_nsmul]

end GlobalTheory.RealMult.PolScale

namespace GlobalTheory.RealMult.PolScale

theorem exists_nat_mul_polForm_eq : GlobalTheory.Published.AbelianDeRham → ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (R : Type) [CommRing R]
    (X : Obj F 𝔠 (Sp R)) (c c₀ : 𝔠.elt), (c₀ : F) ≠ 0 → ∀ ψ ψ₀ : LinearMap.BilinForm R (HdR X.A),
    IsPolForm (dp0 R) (𝟙 _) X.A (X.diag c) ψ → IsPolForm (dp0 R) (𝟙 _) X.A (X.diag c₀) ψ₀ →
    ∃ (n : ℕ) (t : 𝓞 F), n ≠ 0 ∧ ∀ x y, (n : R) * ψ x y = ψ₀ x (act (dp0 R) (𝟙 _) X.rm t y) := by
  intro H F _ _ 𝔠 R _ X c c₀ h₀ ψ ψ₀ hψ hψ₀
  have C := cupSquare_of_free H.1 X.ab X.dim
  have hD : ∀ d : 𝔠.elt, (X.diag d).IsLB := fun d ↦ pull_isLB (X.isLB d) _
  obtain ⟨n, t, hn, e⟩ := exists_nat_smul_eq c c₀ h₀
  obtain ⟨φ, hφ⟩ := exists_corrForm H.1 X c
  obtain ⟨φ₀, hφ₀⟩ := exists_corrForm H.1 X c₀
  obtain ⟨φn, hφn, kn⟩ := exists_corrForm_smul X (n : 𝓞 F) c hφ
  obtain ⟨φt, hφt, kt⟩ := exists_corrForm_smul X t c₀ hφ₀
  rw [e] at hφn
  have u := Published.AbelianDualCrystal.polForm_unique C (hD _) (isPolForm_diag X _ hφn) (isPolForm_diag X _ hφt)
  have u₁ := Published.AbelianDualCrystal.polForm_unique C (hD c) hψ (isPolForm_diag X c hφ)
  have u₂ := Published.AbelianDualCrystal.polForm_unique C (hD c₀) hψ₀ (isPolForm_diag X c₀ hφ₀)
  refine ⟨n, t, hn, fun x y ↦ ?_⟩
  have v := LinearMap.congr_fun (LinearMap.congr_fun u x) y
  rw [u₁, u₂]
  simp only [LinearMap.sub_apply, LinearMap.flip_apply, kn, kt, act_natCast, map_smul, LinearMap.smul_apply,
    smul_eq_mul] at v ⊢
  have a₁ := corrForm_antisymm H.1 X _ hφt y x
  have a₂ := corrForm_antisymm H.1 X c₀ hφ₀ (act (dp0 R) (𝟙 _) X.rm t y) x
  rw [kt, kt] at a₁
  linear_combination v + a₂ - a₁

end GlobalTheory.RealMult.PolScale
