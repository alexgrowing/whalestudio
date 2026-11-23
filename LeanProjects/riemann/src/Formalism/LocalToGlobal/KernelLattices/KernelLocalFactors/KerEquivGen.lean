import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def conjE {m n : ℕ} (g : Sp E m ≃ₗ[E] Sp E m) (g' : Sp E n ≃ₗ[E] Sp E n) : HomE E m n ≃ₗ[𝓞 E] HomE E m n where
  toFun x := g'.toLinearMap ∘ₗ x ∘ₗ g.symm.toLinearMap
  invFun y := g'.symm.toLinearMap ∘ₗ y ∘ₗ g.toLinearMap
  map_add' x y := LinearMap.ext fun v => by simp
  map_smul' r x := LinearMap.ext fun v => by
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, RingHom.id_apply]
    exact equiv_osmul g' r _
  left_inv x := LinearMap.ext fun v => by simp
  right_inv y := LinearMap.ext fun v => by simp

theorem conjE_apply {m n : ℕ} (g : Sp E m ≃ₗ[E] Sp E m) (g' : Sp E n ≃ₗ[E] Sp E n) (x : HomE E m n) :
    conjE g g' x = g'.toLinearMap ∘ₗ x ∘ₗ g.symm.toLinearMap := rfl

theorem conjE_symm_apply {m n : ℕ} (g : Sp E m ≃ₗ[E] Sp E m) (g' : Sp E n ≃ₗ[E] Sp E n) (y : HomE E m n) :
    (conjE g g').symm y = g'.symm.toLinearMap ∘ₗ y ∘ₗ g.toLinearMap := rfl

theorem homAt_gmap {m n : ℕ} (S : Finset (HeightOneSpectrum (𝓞 E))) (g : Sp E m ≃ₗ[E] Sp E m) (g' : Sp E n ≃ₗ[E] Sp E n)
    (N : Submodule (𝓞 E) (Sp E m)) (N' : Submodule (𝓞 E) (Sp E n)) :
    homAt S (gmap g N) (gmap g' N') = (homAt S N N').map (conjE g g' : HomE E m n →ₗ[𝓞 E] HomE E m n) := by
  ext x
  rw [Submodule.mem_map_equiv]
  change (∀ P ∈ S, ∀ y ∈ localization₂ P.asIdeal (gmap g N), x y ∈ localization₂ P.asIdeal (gmap g' N')) ↔
    ∀ P ∈ S, ∀ u ∈ localization₂ P.asIdeal N, ((conjE g g').symm x) u ∈ localization₂ P.asIdeal N'
  constructor
  · intro h P hP u hu
    have h1 := h P hP (g u) ((mem_localization_gmap P g N (g u)).2 (by simpa using hu))
    rw [mem_localization_gmap] at h1
    simpa [conjE_symm_apply] using h1
  · intro h P hP y hy
    rw [mem_localization_gmap]
    have h1 := h P hP (g.symm y) ((mem_localization_gmap P g N y).1 hy)
    simpa [conjE_symm_apply] using h1

theorem divLat_map {H : Type} [AddCommGroup H] [Module (𝓞 E) H] (Φ : H ≃ₗ[𝓞 E] H) (c : ℕ) (M : Submodule (𝓞 E) H) :
    divLat c (M.map (Φ : H →ₗ[𝓞 E] H)) = (divLat c M).map (Φ : H →ₗ[𝓞 E] H) := by
  ext x
  rw [Submodule.mem_map_equiv]
  simp only [divLat, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply, Submodule.mem_map_equiv, map_smul]

theorem mulLat_map {H : Type} [AddCommGroup H] [Module (𝓞 E) H] (Φ : H ≃ₗ[𝓞 E] H) (c : ℕ) (M : Submodule (𝓞 E) H) :
    mulLat c (M.map (Φ : H →ₗ[𝓞 E] H)) = (mulLat c M).map (Φ : H →ₗ[𝓞 E] H) := by
  unfold mulLat
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  ext v
  simp

theorem latSum_map {H M : Type} [AddCommGroup H] [Module (𝓞 E) H] [AddCommMonoid M] (Φ : H ≃ₗ[𝓞 E] H)
    (A B : Submodule (𝓞 E) H) (F : H → M) (hF : ∀ x z, z ∈ B.map (Φ : H →ₗ[𝓞 E] H) → F (x + z) = F x) :
    latSum (A.map (Φ : H →ₗ[𝓞 E] H)) (B.map (Φ : H →ₗ[𝓞 E] H)) F = latSum A B (fun x => F (Φ x)) := by
  unfold latSum
  let eA : ↥A ≃ₗ[𝓞 E] ↥(A.map (Φ : H →ₗ[𝓞 E] H)) := Φ.submoduleMap A
  have hq : (B.comap A.subtype).map (eA : ↥A →ₗ[𝓞 E] ↥(A.map (Φ : H →ₗ[𝓞 E] H))) = (B.map (Φ : H →ₗ[𝓞 E] H)).comap (A.map (Φ : H →ₗ[𝓞 E] H)).subtype := by
    ext x
    rw [Submodule.mem_map_equiv, Submodule.mem_comap, Submodule.mem_comap, Submodule.mem_map_equiv]
    rfl
  let q := Submodule.Quotient.equiv _ _ eA hq
  rw [← finsum_comp_equiv q.toEquiv]
  apply finsum_congr
  intro w
  set s := Function.surjInv (Submodule.Quotient.mk_surjective (B.comap A.subtype)) w
  set r := Function.surjInv (Submodule.Quotient.mk_surjective ((B.map (Φ : H →ₗ[𝓞 E] H)).comap (A.map (Φ : H →ₗ[𝓞 E] H)).subtype)) (q.toEquiv w)
  have hs : Submodule.Quotient.mk s = w := Function.surjInv_eq _ w
  have hr : Submodule.Quotient.mk r = q.toEquiv w := Function.surjInv_eq _ _
  have hrs : Submodule.Quotient.mk r = (Submodule.Quotient.mk (eA s) : ↥(A.map (Φ : H →ₗ[𝓞 E] H)) ⧸ (B.map (Φ : H →ₗ[𝓞 E] H)).comap (A.map (Φ : H →ₗ[𝓞 E] H)).subtype) := by
    rw [hr, ← hs]; rfl
  rw [Submodule.Quotient.eq] at hrs
  have hd : ((r : H) - Φ (s : H)) ∈ B.map (Φ : H →ₗ[𝓞 E] H) := hrs
  have := hF (Φ (s : H)) _ hd
  rw [add_sub_cancel] at this
  exact this

theorem finsum_map_of_injective {ι M N : Type} [AddCommMonoid M] [AddCommMonoid N] (T : M →+ N)
    (hT : Function.Injective T) (f : ι → M) : ∑ᶠ i, T (f i) = T (∑ᶠ i, f i) := by
  by_cases h : (Function.support f).Finite
  · exact (map_finsum T h).symm
  · have hs : Function.support (fun i => T (f i)) = Function.support f := by
      ext i
      simp only [Function.mem_support, ne_eq, map_eq_zero_iff T hT]
    rw [finsum_of_infinite_support h, finsum_of_infinite_support (by rw [hs]; exact h), map_zero]

theorem isSdLat_gmap {n : ℕ} {N : Submodule (𝓞 E) (Sp E n)} (hN : IsSdLat N) (γ : UF E n) : IsSdLat (gmap γ.1 N) := by
  refine ⟨gmap_lattice γ.1 N hN.1, ?_⟩
  change dual (hStd E n) (gmap γ.1 N) = gmap γ.1 N
  rw [dual_gmap γ.1 γ.2, hN.2]

variable {K : Type} [Field K] {a b : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 E))}
  {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

theorem kerOf_move_one {th : ThDist E K a b SB V V'} {Sall : Finset (HeightOneSpectrum (𝓞 E))} {D cA cB : ℕ}
    {rho : UF E a →* Module.End K V} {rho' : UF E b →* Module.End K V'} {sS sT : SB → E → K}
    (hth : ThDist.Ok th Sall D rho rho' sS sT)
    {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)} (hN : IsSdLat N) (hN' : IsSdLat N')
    (fr : Frs E a SB) (fr' : Frs E b SB) (γ : UF E a) (γ' : UF E b)
    (Ξ Ξ₁ : HomE E a b → K) (c : K)
    (hinv : ∀ x z, z ∈ mulLat cB (homAt Sall N N') → Ξ (x + z) = Ξ x)
    (hΞ : ∀ x, Ξ₁ (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) = c * Ξ x) :
    kerOf th Sall cA cB (gmap γ.1 N) (fun P => γ.1 * fr P) (gmap γ'.1 N') (fun P => γ'.1 * fr' P) Ξ₁ =
      c • ((rho' γ') ∘ₗ kerOf th Sall cA cB N fr N' fr' Ξ ∘ₗ (rho γ⁻¹)) := by
  have hsd := isSdLat_gmap hN γ
  have hsd' := isSdLat_gmap hN' γ'
  have hH := homAt_gmap Sall γ.1 γ'.1 N N'
  have hΞ' : ∀ y, Ξ₁ y = c * Ξ ((conjE γ.1 γ'.1).symm y) := fun y => by
    have := hΞ ((conjE γ.1 γ'.1).symm y)
    rwa [← conjE_apply, LinearEquiv.apply_symm_apply] at this
  have step : (fun x => Ξ₁ x • th (gmap γ.1 N) (fun P => γ.1 * fr P) (gmap γ'.1 N') (fun P => γ'.1 * fr' P) cB x) =
      fun x => (c * Ξ ((conjE γ.1 γ'.1).symm x)) • th (gmap γ.1 N) (fun P => γ.1 * fr P) (gmap γ'.1 N') (fun P => γ'.1 * fr' P) cB x := by
    funext x
    rw [hΞ']
  unfold kerOf
  rw [step, hH, divLat_map, mulLat_map, latSum_map]
  · unfold latSum
    simp only [LinearEquiv.symm_apply_apply]
    simp only [conjE_apply]
    simp only [hth.equiv γ γ' N fr N' fr' cB _ hN hN']
    rcases eq_or_ne c 0 with rfl | hc
    · simp
    · let T : (V →ₗ[K] V') →+ (V →ₗ[K] V') :=
        { toFun := fun f => c • (rho' γ' ∘ₗ f ∘ₗ rho γ⁻¹)
          map_zero' := by simp
          map_add' := fun f g => by simp [LinearMap.add_comp, LinearMap.comp_add, smul_add] }
      have e1 : ∀ w, rho γ⁻¹ (rho γ w) = w := fun w => by
        show (rho γ⁻¹ * rho γ) w = w
        rw [← map_mul, inv_mul_cancel, map_one]; rfl
      have e2 : ∀ w, rho' γ'⁻¹ (rho' γ' w) = w := fun w => by
        show (rho' γ'⁻¹ * rho' γ') w = w
        rw [← map_mul, inv_mul_cancel, map_one]; rfl
      have hT : Function.Injective T := by
        intro f g h
        have h1 := congrArg (fun u => c⁻¹ • u) h
        simp only [T, AddMonoidHom.coe_mk, ZeroHom.coe_mk, inv_smul_smul₀ hc] at h1
        refine LinearMap.ext fun v => ?_
        have h2 := LinearMap.congr_fun h1 (rho γ v)
        simp only [LinearMap.comp_apply, e1] at h2
        have h3 := congrArg (rho' γ'⁻¹) h2
        rwa [e2, e2] at h3
      have hTa : ∀ f, T f = c • (rho' γ' ∘ₗ f ∘ₗ rho γ⁻¹) := fun _ => rfl
      rw [← hTa, ← finsum_map_of_injective T hT]
      apply finsum_congr
      intro z
      rw [hTa]
      simp only [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
  · intro x z hz
    have hz' : (conjE γ.1 γ'.1).symm z ∈ mulLat cB (homAt Sall N N') := (Submodule.mem_map_equiv _).1 hz
    rw [map_add, hinv _ _ hz', hth.cong _ _ _ _ cB (x + z) x hsd hsd' (by rw [hH, mulLat_map, add_sub_cancel_left]; exact hz)]

theorem kerOf_move {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {a b : ℕ}
    {SB : Finset (HeightOneSpectrum (𝓞 E))} {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
    {th : ThDist E K a b SB V V'} {Sall : Finset (HeightOneSpectrum (𝓞 E))} {cA cB : ℕ}
    {rho : UF E a →* Module.End K V} {rho' : UF E b →* Module.End K V'} {sS sT : SB → E → K}
    (hth : ThDist.Ok th Sall (cA * cB) rho rho' sS sT) (hB : 0 < cB)
    {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)} (hN : IsSdLat N) (hN' : IsSdLat N')
    (fr : Frs E a SB) (fr' : Frs E b SB) (γ : UF E a) (γ' : UF E b)
    (κ : ∀ P : SB, ↥(GLint E a P.1)) (κ' : ∀ P : SB, ↥(GLint E b P.1))
    (Ξ Ξ₁ : HomE E a b → K) (c : K)
    (hinv : ∀ x z, z ∈ mulLat cB (homAt Sall N N') → Ξ (x + z) = Ξ x)
    (hΞ : ∀ x, (∏ P : SB, sS P (LinearEquiv.det (κ P).1 : Eˣ) * sT P (LinearEquiv.det (κ' P).1 : Eˣ)) *
        Ξ₁ (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) = c * Ξ x) :
    kerOf th Sall cA cB (gmap γ.1 N) (fun P => γ.1 * fr P * (κ P).1) (gmap γ'.1 N') (fun P => γ'.1 * fr' P * (κ' P).1) Ξ₁ =
      c • ((rho' γ') ∘ₗ kerOf th Sall cA cB N fr N' fr' Ξ ∘ₗ (rho γ⁻¹)) := by
  have hsd := isSdLat_gmap hN γ
  have hsd' := isSdLat_gmap hN' γ'
  have e : kerOf th Sall cA cB (gmap γ.1 N) (fun P => γ.1 * fr P * (κ P).1) (gmap γ'.1 N') (fun P => γ'.1 * fr' P * (κ' P).1) Ξ₁ =
      kerOf th Sall cA cB (gmap γ.1 N) (fun P => γ.1 * fr P) (gmap γ'.1 N') (fun P => γ'.1 * fr' P)
        (fun y => (∏ P : SB, sS P (LinearEquiv.det (κ P).1 : Eˣ) * sT P (LinearEquiv.det (κ' P).1 : Eˣ)) * Ξ₁ y) := by
    unfold kerOf
    congr 1
    funext x
    rw [hth.det (gmap γ.1 N) (fun P => γ.1 * fr P) (gmap γ'.1 N') (fun P => γ'.1 * fr' P) cB x κ κ' hsd hsd', smul_smul,
      mul_comm]
  rw [e]
  exact kerOf_move_one hth hN hN' fr fr' γ γ' Ξ _ c hinv hΞ

end Formalism.L2.Ker
