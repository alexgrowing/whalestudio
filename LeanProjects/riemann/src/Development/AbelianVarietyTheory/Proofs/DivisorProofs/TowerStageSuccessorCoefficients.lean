import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StageTriangleFactorStepFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHyperbolicPlaneSplitHermitianLatticeSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianSelfDualLatticeHyperbolicPlaneSplit

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HermitianSkewAdaptation

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.PlaneSkew
open GlobalTheory.AdelicU (IsSplitBasis)
open scoped Matrix

section Planes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable (σ) in

def IsSum {n n₁ : ℕ} (Y : Spc F E n) (Y₁ : Spc F E n₁) (x y : Fin n → E) (ι : Matrix (Fin n) (Fin n₁) E) : Prop :=
  form σ Y.J x x = 0 ∧ form σ Y.J y y = 0 ∧ form σ Y.J x y = 1 ∧
    (∀ u, form σ Y.J (ι *ᵥ u) x = 0 ∧ form σ Y.J (ι *ᵥ u) y = 0) ∧ ιᵀ * Y.J * ι.map σ = Y₁.J ∧ (∀ u, u ∈ Y₁.L ↔ ι *ᵥ u ∈ Y.L) ∧
    (∀ z ∈ Y.L, ∃ (s t : E) (u : Fin n₁ → E), s • x ∈ Y.L ∧ t • y ∈ Y.L ∧ u ∈ Y₁.L ∧ z = s • x + ι *ᵥ u + t • y) ∧
    Function.Injective ι.mulVec

theorem parts_eq_zero {n n₁ : ℕ} {J : Matrix (Fin n) (Fin n) E} {x y : Fin n → E} {ι : Matrix (Fin n) (Fin n₁) E}
    (hxx : form σ J x x = 0) (hyy : form σ J y y = 0) (hxy : form σ J x y = 1) (hyx : form σ J y x ≠ 0)
    (ho : ∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) (hi : Function.Injective ι.mulVec)
    (s t : E) (u : Fin n₁ → E) (h : s • x + ι *ᵥ u + t • y = 0) : s = 0 ∧ t = 0 ∧ u = 0 := by
  have h0 : ∀ z, form σ J 0 z = 0 := fun z => by simp [form]
  have h1 := congrArg (fun z => form σ J z y) h
  have h2 := congrArg (fun z => form σ J z x) h
  simp only [GlobalTheory.KTowerPlane.form_add_left, GlobalTheory.KTowerPlane.form_smul_left, hxx, hyy, hxy, ho, h0, mul_zero, mul_one, add_zero,
    zero_add] at h1 h2
  have ht := (mul_eq_zero.1 h2).resolve_right hyx
  rw [h1, ht, zero_smul, zero_smul, zero_add, add_zero] at h
  exact ⟨h1, ht, hi (by rw [h, Matrix.mulVec_zero])⟩

theorem IsSum.exists_bases (hCM : IsCMExt F E σ) (B : Base F E) {n₁ : ℕ} {Y : Spc F E (n₁ + 2)} {Y₁ : Spc F E n₁}
    {x₀ y₀ : Fin (n₁ + 2) → E} {ι : Matrix (Fin (n₁ + 2)) (Fin n₁) E} (h : IsSum σ Y Y₁ x₀ y₀ ι) (hyx : form σ Y.J y₀ x₀ ≠ 0)
    (hL : Y.L.IsLattice E) (hb : ∀ v : B.P, IsSplitBasis (B.τ v) Y₁.L (Y₁.bas v)) {i₀ i₁ : ℕ} (h01 : i₀ < i₁) (h1n : i₁ < n₁ + 2) :
    ∃ (x y : Fin (n₁ + 2) → E) (𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (β : ∀ v : Pl F, GL (Fin (n₁ + 2)) (Fv F v)),
      IsSum σ Y Y₁ x y ι ∧ (∀ s : E, s ∈ 𝔟 ↔ s • x ∈ Y.L) ∧ (∀ v : B.P, IsSplitBasis (B.τ v) Y.L (β v)) ∧
      ∀ (v : B.P) (i : Fin (n₁ + 2)), (i.1 = i₀ → ∀ r, (β v).1 r i = B.τ v (x r)) ∧ (i.1 = i₁ → ∀ r, (β v).1 r i = B.τ v (y r)) ∧
        ∀ j : Fin n₁, i.1 = skip i₀ i₁ j → ∀ r, (β v).1 r i = (ι.map (B.τ v) * (Y₁.bas v).1) r j := by
  classical
  obtain ⟨hxx₀, hyy₀, hxy₀, horth₀, hg, hlow, hsplit₀, hinj⟩ := h
  have hx₀ : x₀ ≠ 0 := by rintro rfl; simp [form] at hxy₀
  have hy₀ : y₀ ≠ 0 := by rintro rfl; simp [form] at hyx
  obtain ⟨c, hc, hprim⟩ := GlobalTheory.T.exists_rescale_primitive_in_lattice_at_split_primes F E σ hCM (n₁ + 2) Y.L hL x₀ y₀ hx₀ hy₀ B.P B.τ
  have hσc : σ c ≠ 0 := (map_ne_zero σ).2 hc
  set x := c • x₀ with hxdef
  set y := (σ c)⁻¹ • y₀ with hydef
  have hxx : form σ Y.J x x = 0 := by rw [form_smul_left, form_smul_right, hxx₀, mul_zero, mul_zero]
  have hyy : form σ Y.J y y = 0 := by rw [form_smul_left, form_smul_right, hyy₀, mul_zero, mul_zero]
  have hxy : form σ Y.J x y = 1 := by
    rw [form_smul_left, form_smul_right, hxy₀, map_inv₀, sigma_sigma hCM, mul_one, mul_inv_cancel₀ hc]
  have hyx' : form σ Y.J y x ≠ 0 := by
    rw [form_smul_left, form_smul_right]
    exact mul_ne_zero (inv_ne_zero hσc) (mul_ne_zero hσc hyx)
  have horth : ∀ u, form σ Y.J (ι *ᵥ u) x = 0 ∧ form σ Y.J (ι *ᵥ u) y = 0 := fun u => by
    rw [form_smul_right, form_smul_right, (horth₀ u).1, (horth₀ u).2, mul_zero, mul_zero]; exact ⟨rfl, rfl⟩
  have hsplit : ∀ z ∈ Y.L, ∃ (s t : E) (u : Fin n₁ → E), s • x ∈ Y.L ∧ t • y ∈ Y.L ∧ u ∈ Y₁.L ∧
      z = s • x + ι *ᵥ u + t • y := by
    intro z hz
    obtain ⟨s', t, u, h1, h2, h3, rfl⟩ := hsplit₀ z hz
    have e1 : (s' / c) • x = s' • x₀ := by rw [hxdef, smul_smul, div_mul_cancel₀ _ hc]
    have e2 : (t * σ c) • y = t • y₀ := by rw [hydef, smul_smul, mul_assoc, mul_inv_cancel₀ hσc, mul_one]
    exact ⟨s' / c, t * σ c, u, e1 ▸ h1, e2 ▸ h2, h3, by rw [e1, e2]⟩
  obtain ⟨𝔟, h𝔟⟩ := GlobalTheory.T.exists_fractionalIdeal_mem_iff_smul_mem_lattice E (n₁ + 2) Y.L hL x (smul_ne_zero hc hx₀)
  have eL : lowLat ι Y.L = Y₁.L := Submodule.ext fun u => (hlow u).symm
  choose βY hβY using fun v : B.P => GlobalTheory.T.exists_splitPlace_localLatticeBasis_hyperbolicPlane F E σ hCM v.1 (B.τ v) n₁ Y.L x y ι (Y₁.bas v) i₀ i₁ h01 h1n
    (fun z hz => by
      obtain ⟨s, t, u, h1, h2, h3, h4⟩ := hsplit z hz
      exact ⟨s, t, u, h1, h2, (hlow u).1 h3, h4⟩)
    (parts_eq_zero hxx hyy hxy hyx' horth hinj) (hprim v).1 (hprim v).2 (eL ▸ hb v)
  refine ⟨x, y, 𝔟, fun v => if h : v ∈ B.P then βY ⟨v, h⟩ else 1, ⟨hxx, hyy, hxy, horth, hg, hlow, hsplit, hinj⟩, h𝔟,
    fun v => ?_, fun v i => ?_⟩
  · simp only [dif_pos v.2]; exact (hβY v).1
  · simp only [dif_pos v.2]; exact (hβY v).2 i

theorem IsSum.adapt_herm (hCM : IsCMExt F E σ) {B : Base F E} {n n₁ : ℕ} (hn : n = n₁ + 2) {Y : Spc F E n} {Y₁ : Spc F E n₁}
    {x₀ y₀ : Fin n → E} {ι : Matrix (Fin n) (Fin n₁) E} (h : IsSum σ Y Y₁ x₀ y₀ ι) {r s r₁ s₁ : ℕ} (hY : Y.IsHerm σ B r s)
    (hY₁ : Y₁.IsHerm σ B r₁ s₁) {i₀ i₁ : ℕ} (h01 : i₀ < i₁) (h1n : i₁ < n) :
    ∃ (Y' : Spc F E n) (H : Plane E n n₁), (reS Y Y').IsHerm σ B r s ∧ H.IsAdapted σ B (reS Y Y') Y₁ i₀ i₁ := by
  subst hn
  obtain ⟨x, y, 𝔟, β, ⟨hxx, hyy, hxy, horth, hg, hlow, hsplit, hinj⟩, h𝔟, hβ, hβ'⟩ := h.exists_bases hCM B
    (by rw [GlobalTheory.KTowerPlane.form_swap hCM hY.herm, h.2.2.1, map_one]; exact one_ne_zero) hY.lat hY₁.bas h01 h1n
  obtain ⟨g, hgι⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.mulVecLin ι) (LinearMap.ker_eq_bot.2 hinj)
  have hP : LinearMap.toMatrix' g * ι = 1 := by
    rw [← LinearMap.toMatrix'_toLin' ι, ← LinearMap.toMatrix'_comp, Matrix.toLin'_apply', hgι, LinearMap.toMatrix'_id]
  choose θ hθ using fun w => GlobalTheory.T.exists_cartanInvolution_extend_swapping_hyperbolicPair _ n₁ (Y.J.map (B.emb w).1) (fun i => (B.emb w).1 (x i)) (fun i => (B.emb w).1 (y i))
    (ι.map (B.emb w).1) ((LinearMap.toMatrix' g).map (B.emb w).1) (Y₁.θ w) rfl (GlobalTheory.KTowerPlane.map_herm hCM _ hY.herm)
    (by rw [← GlobalTheory.KTowerPlane.map_form hCM, hxx, map_zero]) (by rw [← GlobalTheory.KTowerPlane.map_form hCM, hyy, map_zero])
    (by rw [← GlobalTheory.KTowerPlane.map_form hCM, hxy, map_one])
    (GlobalTheory.KTowerPlane.map_orth hCM _ Y.J ι x fun u => (horth u).1) (GlobalTheory.KTowerPlane.map_orth hCM _ Y.J ι y fun u => (horth u).2)
    (by rw [← Matrix.map_mul, hP, Matrix.map_one _ (map_zero _) (map_one _)])
    (by rw [GlobalTheory.KTowerPlane.map_gram hCM, hg]; exact hY₁.cartan w)
  exact ⟨⟨Y.J, Y.L, θ, β⟩, ⟨x, y, ι, 𝔟⟩, ⟨hY.herm, hY.sig, hY.lat, hY.dual, fun w => (hθ w).1, hβ⟩,
    ⟨rfl, hxx, hyy, hxy, horth, hg, hlow, hsplit, h𝔟,
      fun w => ⟨(hθ w).2.1, 1, one_ne_zero, by rw [one_smul]; exact (hθ w).2.2.symm⟩, hβ'⟩⟩

theorem IsSum.adapt_skew (hCM : IsCMExt F E σ) {B : Base F E} {n n₁ : ℕ} (hn : n = n₁ + 2) {Y : Spc F E n} {Y₁ : Spc F E n₁}
    {x₀ y₀ : Fin n → E} {ι : Matrix (Fin n) (Fin n₁) E} (h : IsSum σ Y Y₁ x₀ y₀ ι) (hyx : form σ Y.J y₀ x₀ ≠ 0) {r s r₁ s₁ : ℕ}
    (hY : Y.IsSkew σ B r s) (hY₁ : Y₁.IsSkew σ B r₁ s₁) {i₀ i₁ : ℕ} (h01 : i₀ < i₁) (h1n : i₁ < n) :
    ∃ (Y' : Spc F E n) (H : Plane E n n₁), (reS Y Y').IsSkew σ B r s ∧ H.IsAdapted σ B (reS Y Y') Y₁ i₀ i₁ := by
  subst hn
  have hτσ : ∀ (τ : E →+* ℂ) (a : E), τ (σ a) = star (τ a) := hCM.2.2.2
  obtain ⟨x, y, 𝔟, β, ⟨hxx, hyy, hxy, horth, hg, hlow, hsplit, hinj⟩, h𝔟, hβ, hβ'⟩ := h.exists_bases hCM B hyx hY.lat hY₁.bas h01 h1n
  choose θ hθ using fun w => GlobalTheory.T.exists_cartanInvolution_hyperbolicSwap_extension n₁ (Complex.I • Y.J.map (B.emb w).1) (fun i => (B.emb w).1 (x i))
    (fun i => (B.emb w).1 (y i)) (ι.map (B.emb w).1) (Y₁.θ w) (herm_map _ (hτσ _) hY.skew)
    (by rw [form_map _ (hτσ _), hxx, map_zero, mul_zero]) (by rw [form_map _ (hτσ _), hyy, map_zero, mul_zero])
    (by rw [form_map _ (hτσ _), hxy, map_one, mul_one])
    (fun u => ⟨orth_map _ (hτσ _) Y.J ι x (fun u => (horth u).1) u, orth_map _ (hτσ _) Y.J ι y (fun u => (horth u).2) u⟩)
    (inj_map _ ι hinj) (by rw [gram_map _ (hτσ _), hg]; exact hY₁.cartan w)
  exact ⟨⟨Y.J, Y.L, θ, β⟩, ⟨x, y, ι, 𝔟⟩, ⟨hY.skew, hY.sig, hY.lat, hY.dual, fun w => (hθ w).1, hβ⟩,
    ⟨rfl, hxx, hyy, hxy, horth, hg, hlow, hsplit, h𝔟, fun w => (hθ w).2, hβ'⟩⟩

end Planes

section Transport

open GlobalTheory.SqStepK GlobalTheory.SqStepBig

variable {D : D7}

def crd (ε : D.host.E →+* D.host.E) (S : HSp D) (z : S.V) : Fin S.rank → D.host.E := fun i => ε (S.frame.equivFun z i)

theorem crd_add (ε : D.host.E →+* D.host.E) (S : HSp D) (z z' : S.V) : crd ε S (z + z') = crd ε S z + crd ε S z' :=
  funext fun i => by simp [crd]

theorem crd_smul (ε : D.host.E →+* D.host.E) (S : HSp D) (s : D.host.E) (z : S.V) : crd ε S (s • z) = ε s • crd ε S z :=
  funext fun i => by simp [crd]

theorem crd_surj {ε : D.host.E →+* D.host.E} (hε : ∀ a, ε (ε a) = a) (S : HSp D) : Function.Surjective (crd ε S) := fun w =>
  ⟨S.frame.equivFun.symm fun i => ε (w i), funext fun i => by simp only [crd, LinearEquiv.apply_symm_apply, hε]⟩

theorem crd_inj (ε : D.host.E →+* D.host.E) (S : HSp D) : Function.Injective (crd ε S) := fun _ _ h =>
  S.frame.equivFun.injective (funext fun i => ε.injective (congrFun h i))

theorem crd_map (ε : D.host.E →+* D.host.E) {S S₁ : HSp D} (ι : S₁.V →ₗ[D.host.E] S.V) (u : S₁.V) :
    (LinearMap.toMatrix S₁.frame S.frame ι).map ε *ᵥ crd ε S₁ u = crd ε S (ι u) := by
  funext i
  have := congrFun (LinearMap.toMatrix_mulVec_repr S₁.frame S.frame ι u) i
  simp only [crd, Module.Basis.equivFun_apply, ← this]
  exact (RingHom.map_mulVec ε _ _ i).symm

theorem hD_swap (S : HSp D) (u v : S.V) : S.hD v u = star (S.hD u v) := (S.herm.eq v u).symm

theorem hT_sum (S : HSp D) (u v : S.V) :
    S.hT u v = ∑ i, ∑ j, star (S.frame.equivFun u i) * S.gram i j * S.frame.equivFun v j := by
  conv_lhs => rw [← S.frame.sum_repr u, ← S.frame.sum_repr v]
  simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, HSpace.gram, RingHom.id_apply,
    starRingEnd_apply, Module.Basis.equivFun_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem isomEmb_inj {S S₁ : HSp D} {ι : S₁.V →ₗ[D.host.E] S.V} (h : HSpace.IsIsomEmb S₁ S ι) : Function.Injective ι := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  exact S₁.nondeg.1 u fun v => by rw [← h, hu, map_zero, LinearMap.zero_apply]

theorem isSum_of_split {S S₁ : HSp D} {Λ Λ₁ ι x y} (hs : PlaneSplit S S₁ Λ Λ₁ ι x y) {ε : D.host.E →+* D.host.E}
    (hε : ∀ a, ε (ε a) = a) {c : D.host.E} (hc : c ≠ 0) (Y : Spc D.host.F D.host.E S.rank) (Y₁ : Spc D.host.F D.host.E S₁.rank)
    (hJ : ∀ u v, form D.sp.cm.sig Y.J (crd ε S u) (crd ε S v) = c * ε (S.hD u v))
    (hJ₁ : ∀ u v, form D.sp.cm.sig Y₁.J (crd ε S₁ u) (crd ε S₁ v) = c * ε (S₁.hD u v))
    (hL : ∀ z, crd ε S z ∈ Y.L ↔ InLat S Λ z) (hL₁ : ∀ z, crd ε S₁ z ∈ Y₁.L ↔ InLat S₁ Λ₁ z) :
    ∃ x' y' ι', IsSum D.sp.cm.sig Y Y₁ x' y' ι' ∧ form D.sp.cm.sig Y.J y' x' ≠ 0 := by
  obtain ⟨-, hι, hxx, hyy, hxy, ho, hlow, hsp⟩ := hs
  have hσ : ∀ a, D.sp.cm.sig a = star a := fun _ => rfl
  have hc' : star c ≠ 0 := star_ne_zero.2 hc
  refine ⟨crd ε S x, (star c)⁻¹ • crd ε S y, (LinearMap.toMatrix S₁.frame S.frame ι).map ε,
    ⟨?_, ?_, ?_, fun u => ?_, ?_, fun u => ?_, fun z hz => ?_, fun u u' h => ?_⟩, ?_⟩
  · rw [hJ, hxx, map_zero, mul_zero]
  · rw [form_smul_left, form_smul_right, hJ, hyy, map_zero, mul_zero, mul_zero, mul_zero]
  · rw [form_smul_right, hJ, hxy, map_one, mul_one, map_inv₀, hσ, star_star, inv_mul_cancel₀ hc]
  · obtain ⟨u, rfl⟩ := crd_surj hε S₁ u
    rw [crd_map, form_smul_right, hJ, hJ, (ho u).1, (ho u).2, map_zero, mul_zero, mul_zero]
    exact ⟨rfl, rfl⟩
  · refine Matrix.ext fun i j => ?_
    refine (GlobalTheory.KTowerPlane.form_single (σ := D.sp.cm.sig) _ i j).symm.trans
      (Eq.trans ?_ (GlobalTheory.KTowerPlane.form_single (σ := D.sp.cm.sig) Y₁.J i j))
    rw [GlobalTheory.KTowerPlane.form_gram]
    obtain ⟨u, hu⟩ := crd_surj hε S₁ (Pi.single i 1)
    obtain ⟨v, hv⟩ := crd_surj hε S₁ (Pi.single j 1)
    rw [← hu, ← hv, crd_map, crd_map, hJ, hJ₁, HSpace.hD, HSpace.hD, hι]
  · obtain ⟨u, rfl⟩ := crd_surj hε S₁ u
    rw [crd_map, hL, hL₁, hlow]
  · obtain ⟨z, rfl⟩ := crd_surj hε S z
    obtain ⟨s, r, u, h1, h2, h3, rfl⟩ := hsp z ((hL z).1 hz)
    have e : (ε r * star c) • (star c)⁻¹ • crd ε S y = crd ε S (r • y) := by
      rw [smul_smul, mul_assoc, mul_inv_cancel₀ hc', mul_one, crd_smul]
    refine ⟨ε s, ε r * star c, crd ε S₁ u, ?_, ?_, (hL₁ u).2 h3, ?_⟩
    · rw [← crd_smul]; exact (hL _).2 h1
    · rw [e]; exact (hL _).2 h2
    · rw [e, crd_map, crd_add, crd_add, crd_smul]
  · obtain ⟨u, rfl⟩ := crd_surj hε S₁ u
    obtain ⟨u', rfl⟩ := crd_surj hε S₁ u'
    rw [crd_map, crd_map] at h
    rw [isomEmb_inj hι (crd_inj ε S h)]
  · rw [form_smul_left, hJ, hD_swap, hxy, star_one, map_one, mul_one]
    exact mul_ne_zero (inv_ne_zero hc') hc

theorem scale_ne_zero (D : D7) : D.host.AA ≠ 0 := by
  refine mul_ne_zero ?_ (inv_ne_zero ?_)
  · rw [FractionalIdeal.coeIdeal_ne_zero]
    intro h
    exact D.host.ccK_ne_bot ((Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.algebraMap.injective _ _)).1 h)
  · rw [FractionalIdeal.coeIdeal_ne_zero]
    intro h
    have h1 := D.host.𝔟_spec.1
    rw [h, Ideal.bot_mul] at h1
    exact differentIdeal_ne_bot h1

theorem split_scLat {S S₁ : HSp D} {Λ Λ₁ ι x y} (hs : PlaneSplit S S₁ Λ Λ₁ ι x y)
    {𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E} (h𝔞 : 𝔞 ≠ 0) :
    PlaneSplit S S₁ (GlobalTheory.SkewLat.scLat 𝔞 Λ) (GlobalTheory.SkewLat.scLat 𝔞 Λ₁) ι x y := by
  obtain ⟨hr, hι, hxx, hyy, hxy, ho, hlow, hsp⟩ := hs
  have m : ∀ {S : HSp D} {Λ} (z : S.V), InLat S (GlobalTheory.SkewLat.scLat 𝔞 Λ) z ↔ ∀ c ∈ 𝔞⁻¹, InLat S Λ (c • z) := fun z => by
    simp only [InLat, map_smul]; rfl
  have hyx : S.hD y x = 1 := by rw [hD_swap, hxy, star_one]
  have l1 : ∀ (s r : D.host.E) u, S.hD (s • x + ι u + r • y) y = s := fun s r u => by
    have := ho u
    simp only [HSpace.hD] at *
    simp [*]
  have l2 : ∀ (s r : D.host.E) u, S.hD (s • x + ι u + r • y) x = r := fun s r u => by
    have := ho u
    simp only [HSpace.hD] at *
    simp [*]
  refine ⟨hr, hι, hxx, hyy, hxy, ho, fun u => ?_, fun z hz => ?_⟩
  · simp only [m, hlow, map_smul]
  · obtain ⟨c₀, hc₀, h0⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger (inv_ne_zero h𝔞)
    have hc : algebraMap (𝓞 D.host.E) D.host.E c₀ ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 hc₀
    set c := algebraMap (𝓞 D.host.E) D.host.E c₀
    obtain ⟨s, r, u, -, -, -, e⟩ := hsp _ ((m z).1 hz c h0)
    have ez : z = (c⁻¹ * s) • x + ι (c⁻¹ • u) + (c⁻¹ * r) • y := by
      rw [map_smul, mul_smul, mul_smul, ← smul_add, ← smul_add, ← e, inv_smul_smul₀ hc]
    generalize c⁻¹ * s = s₀, c⁻¹ • u = u₀, c⁻¹ * r = r₀ at ez
    have key : ∀ a ∈ 𝔞⁻¹, InLat S Λ (a • s₀ • x) ∧ InLat S Λ (a • r₀ • y) ∧ InLat S₁ Λ₁ (a • u₀) := fun a ha => by
      obtain ⟨s', r', u', h1, h2, h3, e'⟩ := hsp _ ((m z).1 hz a ha)
      have e2 : (a * s₀) • x + ι (a • u₀) + (a * r₀) • y = s' • x + ι u' + r' • y := by
        rw [← e', ez, map_smul, mul_smul, mul_smul, smul_add, smul_add]
      have es : a * s₀ = s' := by rw [← l1 (a * s₀) (a * r₀) (a • u₀), e2, l1]
      have er : a * r₀ = r' := by rw [← l2 (a * s₀) (a * r₀) (a • u₀), e2, l2]
      rw [es, er, add_left_inj, add_right_inj] at e2
      rw [smul_smul, smul_smul, es, er, isomEmb_inj hι e2]
      exact ⟨h1, h2, h3⟩
    exact ⟨s₀, r₀, u₀, (m _).2 fun a ha => (key a ha).1, (m _).2 fun a ha => (key a ha).2.1, (m _).2 fun a ha => (key a ha).2.2, ez⟩

theorem overH_crd {c : D.host.E} {S : HSp D} {Λ} {Y : Spc D.host.F D.host.E S.rank} (h : OverH c S Λ Y) :
    (∀ u v, form D.sp.cm.sig Y.J (crd (starRingEnd _) S u) (crd (starRingEnd _) S v) = c * starRingEnd _ (S.hD u v)) ∧
      ∀ z, crd (starRingEnd _) S z ∈ Y.L ↔ InLat S Λ z := by
  obtain ⟨e, hJ, hL⟩ := h
  have hσ : ∀ a, D.sp.cm.sig a = star a := fun _ => rfl
  refine ⟨fun u v => ?_, fun z => ?_⟩
  · have hJ' : ∀ i j, Y.J i j = c * S.gram i j := fun i j => by rw [hJ]; rfl
    rw [starRingEnd_apply, ← hD_swap, HSpace.hD, hT_sum]
    simp only [form, dotProduct, Matrix.mulVec, crd, hσ, hJ', Finset.mul_sum, starRingEnd_apply, star_star]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  · rw [hL]
    simp only [crd, starRingEnd_apply, star_star]
    rfl

theorem overW_crd {S : HSp D} {Λ} {Y : Spc D.host.F D.host.E S.rank} (h : OverW S Λ Y) :
    (∀ u v, form D.sp.cm.sig Y.J (crd (RingHom.id _) S u) (crd (RingHom.id _) S v) = D.host.xi0 * RingHom.id _ (S.hD u v)) ∧
      ∀ z, crd (RingHom.id _) S z ∈ Y.L ↔ InLat S (GlobalTheory.SkewLat.scLat D.host.AA Λ) z := by
  obtain ⟨e, hJ, hL⟩ := h
  have hσ : ∀ a, D.sp.cm.sig a = star a := fun _ => rfl
  refine ⟨fun u v => ?_, fun z => ?_⟩
  · have hJ' : ∀ i j, Y.J i j = D.host.xi0 * S.gram j i := fun i j => by rw [hJ]; rfl
    rw [RingHom.id_apply, HSpace.hD, hT_sum, Finset.sum_comm]
    simp only [form, dotProduct, Matrix.mulVec, crd, hσ, hJ', Finset.mul_sum, RingHom.id_apply]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  · rw [hL]
    rfl

theorem plane_herm {B : Base D.host.F D.host.E} (hB : B.IsGood D.sp.cm.sig) {S S₁ : HSp D} {Λ Λ₁ ι x y}
    (hs : PlaneSplit S S₁ Λ Λ₁ ι x y) {c : D.host.E} (hc : c ≠ 0) {Y : Spc D.host.F D.host.E S.rank}
    {Y₁ : Spc D.host.F D.host.E S₁.rank} (o : OverH c S Λ Y) (o₁ : OverH c S₁ Λ₁ Y₁) {r s r₁ s₁ : ℕ}
    (hY : Y.IsHerm D.sp.cm.sig B r s) (hY₁ : Y₁.IsHerm D.sp.cm.sig B r₁ s₁) {i₀ i₁ : ℕ} (h01 : i₀ < i₁) (h1n : i₁ < S.rank) :
    ∃ Y' H, (reS Y Y').IsHerm D.sp.cm.sig B r s ∧ Plane.IsAdapted D.sp.cm.sig B H (reS Y Y') Y₁ i₀ i₁ := by
  obtain ⟨x', y', ι', h, -⟩ := isSum_of_split hs (ε := starRingEnd _) star_star hc Y Y₁ (overH_crd o).1 (overH_crd o₁).1
    (overH_crd o).2 (overH_crd o₁).2
  exact h.adapt_herm hB.cm hs.1 hY hY₁ h01 h1n

theorem plane_skew {B : Base D.host.F D.host.E} (hB : B.IsGood D.sp.cm.sig) {S S₁ : HSp D} {Λ Λ₁ ι x y}
    (hs : PlaneSplit S S₁ Λ Λ₁ ι x y) {n n₁ : ℕ} {Y : Spc D.host.F D.host.E n}
    {Y₁ : Spc D.host.F D.host.E n₁} (o : OverW S Λ Y) (o₁ : OverW S₁ Λ₁ Y₁) {r s r₁ s₁ : ℕ}
    (hY : Y.IsSkew D.sp.cm.sig B r s) (hY₁ : Y₁.IsSkew D.sp.cm.sig B r₁ s₁) {i₀ i₁ : ℕ} (h01 : i₀ < i₁) (h1n : i₁ < n) :
    ∃ Y' H, (reS Y Y').IsSkew D.sp.cm.sig B r s ∧ Plane.IsAdapted D.sp.cm.sig B H (reS Y Y') Y₁ i₀ i₁ := by
  obtain rfl : S.rank = n := o.1
  obtain rfl : S₁.rank = n₁ := o₁.1
  obtain ⟨x', y', ι', h, h'⟩ := isSum_of_split (split_scLat hs (scale_ne_zero D)) (ε := RingHom.id _) (fun _ => rfl)
    GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero Y Y₁ (overW_crd o).1 (overW_crd o₁).1 (overW_crd o).2 (overW_crd o₁).2
  exact h.adapt_skew hB.cm hs.1 h' hY hY₁ h01 h1n

end Transport

section Cast

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem cast_rank (B : Base F E) {a b n : ℕ} (hn : n = b + 2) (Γ : Geo σ a n) (Γ₁ : Geo σ a b) (H : Plane E n b)
    (H' : Plane E (a + n) (a + b)) (R : RealMaps F a n) (h1 : Γ₁.V = Γ.V) (h2 : Γ₁.p = Γ.p) (h3 : Γ₁.q + 1 = Γ.q)
    (h4 : H.IsAdapted σ B Γ.V' Γ₁.V' 0 (b + 1)) (h5 : H'.IsAdapted σ B Γ.W Γ₁.W a (a + b + 1)) :
    ∃ (Γ' : Geo σ a (b + 2)) (K : Plane E (b + 2) b) (K' : Plane E (a + (b + 2)) (a + b)) (R' : RealMaps F a (b + 2)),
      Γ₁.V = Γ'.V ∧ Γ₁.p = Γ'.p ∧ Γ₁.q + 1 = Γ'.q ∧ K.IsAdapted σ B Γ'.V' Γ₁.V' 0 (b + 1) ∧
      K'.IsAdapted σ B Γ'.W Γ₁.W a (a + b + 1) ∧
      ∀ X κ, GlobalTheory.SqStepK.HasConstR B Γ R X κ → GlobalTheory.SqStepK.HasConstR B Γ' R' X κ := by
  subst hn
  exact ⟨Γ, H, H', R, h1, h2, h3, h4, h5, fun _ _ h => h⟩

theorem const_pair (hP : GlobalTheory.FunPr.Hypotheses₂) (hK : ThetaIntegralsAgree) (hM : LocalMatching) {B : Base F E} (hB : B.IsGood σ)
    {a a' : ℕ} {Γ : Geo σ a a'} (g : Γ.IsGood B) {Xa Xb : Chars F E} (xa : Xa.IsGood B a a') (xb : Xb.IsGood B a a') {la lb : ℂ}
    (hlb : lb ≠ 0)
    (H : ∀ R om om' Rf om₀ om₀' Rf₀ (c c₀ : ℂ), IsMatched B Γ Xa om om' R Rf → IsMatched B Γ Xb om₀ om₀' R Rf₀ →
      IsConst B Γ Xa om om' R Rf c → IsConst B Γ Xb om₀ om₀' R Rf₀ c₀ →
      ∃ k : (AE F E)ˣ, c * lb = ((Xa.ν k / Xb.ν k : Circle) : ℂ) * (c₀ * la))
    {V : Spc F E a} {V' : Spc F E a'} {Z : Spc F E (a + a')} (g₂ : (reG Γ V V' Z).IsGood B) :
    ∃ (R : RealMaps F a a') (d : ℂ) (k : (AE F E)ˣ), d ≠ 0 ∧
      GlobalTheory.SqStepK.HasConstR B (reG Γ V V' Z) R Xa (d * ((Xa.ν k / Xb.ν k : Circle) : ℂ) * la) ∧
      GlobalTheory.SqStepK.HasConstR B (reG Γ V V' Z) R Xb (d * ((Xb.ν k / Xb.ν k : Circle) : ℂ) * lb) := by
  obtain ⟨oa, oa', ob, ob', R, Ra, Rb, da, db, m1, m2, k1, k2, hdb, k, hk⟩ := GlobalTheory.SqStepBig.pair_reG hP hK hM hB g xa xb H g₂
  refine ⟨R, db / lb, k, div_ne_zero hdb hlb, ⟨oa, oa', Ra, m1, ?_⟩, ⟨ob, ob', Rb, m2, ?_⟩⟩
  · convert k1 using 1
    field_simp
    linear_combination -hk
  · convert k2 using 1
    rw [div_self', Circle.coe_one, mul_one, div_mul_cancel₀ _ hlb]

end Cast

open GlobalTheory.SqStepBig in

theorem tower_stage_successor_relation : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW B' WW₁ : HSp D) (X : Tri T A A' WW)
      (Y : Tri T A B' WW₁) (lam c : T → ℂ) (e : ℕ), GlobalTheory.SqTower.IsStageC W i j p (q + 1) X →
      GlobalTheory.SqTower.IsStageC W i j p q Y → GlobalTheory.SqStepK.IsStepB X Y → Factor X W.ψ W.θ lam → Factor Y W.ψ W.θ c →
      A.rank = A'.rank + 2 * e → ∀ t, ∃ (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (b : ℕ)
        (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig A.rank (b + 2)) (Γ₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig A.rank b)
        (H : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Plane D.host.E (b + 2) b) (H' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Plane D.host.E (A.rank + (b + 2)) (A.rank + b))
        (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F A.rank (b + 2)) (R₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F A.rank b) (d d₁ : ℂ)
        (k k₁ : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E)ˣ),
        GlobalTheory.SqStep.BaseFits G W i j t Bs ∧ A'.rank = b + 2 ∧ Γ₁.V = Γ.V ∧ Γ₁.p = Γ.p ∧ Γ₁.q + 1 = Γ.q ∧
        H.IsAdapted D.sp.cm.sig Bs Γ.V' Γ₁.V' 0 (b + 1) ∧ H'.IsAdapted D.sp.cm.sig Bs Γ.W Γ₁.W A.rank (A.rank + b + 1) ∧
        d ≠ 0 ∧ d₁ ≠ 0 ∧ ∀ t' ∈ ({t, μ₀} : Set T),
          GlobalTheory.SqStepK.HasConstR Bs Γ R (GlobalTheory.SqStep.chs G i j t')
            (d * (((GlobalTheory.SqStep.chs G i j t').ν k / (GlobalTheory.SqStep.chs G i j μ₀).ν k : Circle) : ℂ) * lam t') ∧
          GlobalTheory.SqStepK.HasConstR Bs Γ₁ R₁ (GlobalTheory.SqStep.chs G i j t')
            (d₁ * (((GlobalTheory.SqStep.chs G i j t').ν k₁ / (GlobalTheory.SqStep.chs G i j μ₀).ν k₁ : Circle) : ℂ) * c t') := by
  intro hP hK hM
  refine gbig_of_three GlobalTheory.T.exists_realEmbeddings_sharedBase_towerStage (GlobalTheory.T.tower_stage_fit_factor hP hK hM) GlobalTheory.T.exists_realEmbeddings_sharedBase_towerStage ?_
  rintro D T Lc sc G μ₀ C x b qb qd - W S hψ hN i j p q A A' WW B' WW₁ X Y lam c e hX hY ⟨hA, ⟨ι, x, y, hs⟩, ι', x', y', hs'⟩ hF hc he t
  obtain ⟨emb, hemb⟩ := qb W hψ i j _ _ A A' WW X hX
  obtain ⟨Bs, -, f⟩ := hemb t
  have hn : A'.rank = B'.rank + 2 := hs.1
  have f₁ : Fit G W i j t μ₀ Bs A.rank B'.rank := Fit.down_right (hn ▸ f)
  obtain ⟨Γ, o, pΓ, qΓ, g, HX⟩ := qd W hψ i j _ _ A A' WW X lam t Bs hX hF f
  obtain ⟨Γ₁, o₁, pΓ₁, qΓ₁, g₁, HY⟩ := qd W hψ i j _ _ A B' WW₁ Y c t Bs hY hc f₁
  obtain ⟨U, H, hU, hH⟩ := plane_herm f.2.1 hs (neg_ne_zero.2 one_ne_zero) o.2.1 o₁.2.1 g.hV' g₁.hV' (i₀ := 0) (i₁ := B'.rank + 1)
    (by omega) (by omega)
  obtain ⟨Z, H', hZ, hH'⟩ := plane_skew f.2.1 hs' o.2.2 o₁.2.2 g.hW g₁.hW (i₀ := A.rank) (i₁ := A.rank + B'.rank + 1)
    (by omega) (by omega)
  have eV : reS Γ₁.V Γ.V = reS Γ.V Γ.V := reS_congr Γ.V (o.1.eq (hA ▸ o₁.1))
  have hV : (reS Γ.V Γ.V).IsHerm D.sp.cm.sig Bs (A.rank - Γ.p) Γ.p := g.hV
  have g₂ : (reG Γ Γ.V U Z).IsGood Bs := isGood_reG g hV hU hZ
  have g₃ : (reG Γ₁ Γ.V Γ₁.V' Γ₁.W).IsGood Bs := isGood_reG g₁ (by rw [eV, pΓ₁, ← pΓ]; exact hV) g₁.hV' g₁.hW
  obtain ⟨R, d, k, hd, c1, c2⟩ := const_pair hP hK hM f.2.1 g f.2.2.2.1 f.2.2.2.2.1 (hF.1 μ₀) HX g₂
  obtain ⟨R₁, d₁, k₁, hd₁, c3, c4⟩ := const_pair hP hK hM f.2.1 g₁ f₁.2.2.2.1 f₁.2.2.2.2.1 (hc.1 μ₀) HY g₃
  obtain ⟨Γ', K, K', R', e1, e2, e3, e4, e5, e6⟩ := cast_rank Bs hn (reG Γ Γ.V U Z) (reG Γ₁ Γ.V Γ₁.V' Γ₁.W) H H' R eV
    (pΓ₁.trans pΓ.symm) (by show Γ₁.q + 1 = Γ.q; rw [qΓ, qΓ₁]) hH hH'
  refine ⟨Bs, B'.rank, Γ', _, K, K', R', R₁, d, d₁, k, k₁, f.1, hn, e1, e2, e3, e4, e5, hd, hd₁, ?_⟩
  rintro t' (rfl | rfl)
  · exact ⟨e6 _ _ c1, c3⟩
  · exact ⟨e6 _ _ c2, c4⟩

end GlobalTheory.HermitianSkewAdaptation

end
