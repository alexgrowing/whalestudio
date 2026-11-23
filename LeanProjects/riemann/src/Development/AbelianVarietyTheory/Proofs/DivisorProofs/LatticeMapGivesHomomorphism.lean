import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPolAVHypSRetract
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneOfSurjective
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HolUnifHom

open GlobalTheory.SS GlobalTheory.EighthPowerFactor CechPic in

theorem exists_polAV_retract_dim (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g : ℕ)
    (hB : IsAbelianScheme B) (hd : SmoothOfRelativeDimension g B.hom) (M : LB B.left) (hM : M.IsLB)
    (ha : Out.RelAmple B M) (hK : Out.KTriv B M) :
    ∃ (Q : Out.PolAV (Sp k)) (i : B ⟶ Q.A) (r : Q.A ⟶ B),
      Q.g = 8 * g ∧ IsMonHom i ∧ IsMonHom r ∧ i ≫ r = 𝟙 B := by
  have := hB.comm
  obtain ⟨L₁, L₂⟩ := abelianSchemeLaws_all
  obtain ⟨W, hW, hbas⟩ := ZM.exists_isE8_isSharpBasis
  obtain ⟨bas, hb⟩ := hbas g
  obtain ⟨a, w, w', hw, hw', hs⟩ := exists_matrices hW.2
  let b : ZM.TBase k 1 := ⟨1, by simp, fun K _ β => by simp⟩
  have hc : (siegOne L₁.globalFns hB hM g).Principal :=
    ⟨relAmple_diag_lam hB hM (exists_gen_theta_of_isAbelianScheme k B hB M hM) ha,
      fun T x hx => SiegelOfPolarised.eq_one_of_lam hM hK x hx⟩
  obtain ⟨t, ⟨pr, hpr, hu, -⟩, -, -, -⟩ := exists_isSharp_and_prim L₁ L₂ Moduli.cube_of_isLB g _ W _ a w w' bas hW hb
    hw hw' hs 1 k b _ (𝟙 _) (siegOne L₁.globalFns hB hM g) (one_pow _) odd_one hc hd
  obtain ⟨i, hi, -⟩ := hu B fun _ => 𝟙 B
  refine ⟨t.pol, i, pr 0, rfl, isMonHom_of_coord hpr hu fun u => ?_, hpr 0, hi 0⟩
  rw [hi u]
  exact inferInstanceAs (IsMonHom (𝟙 B))

end GlobalTheory.HolUnifHom

namespace GlobalTheory.HolUnifHom

open GlobalTheory GlobalTheory.SurjIsogeny GlobalTheory.IsogenyModel GlobalTheory.HolUnifEnd in

theorem exists_linear_factor (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hgA : SmoothOfRelativeDimension g A.hom) (L : LB A.left) (u : HolUnif A L g) :
    ∃ (Q : Out.PolAV (Sp ℂ)) (v : HolUnif Q.A Q.L (8 * g)) (i : A ⟶ Q.A) (r : Q.A ⟶ A)
      (J : (Fin g → ℂ) →ₗ[ℂ] (Fin (8 * g) → ℂ)) (R : (Fin (8 * g) → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (m : ℕ),
      Q.g = 8 * g ∧ IsMonHom i ∧ IsMonHom r ∧ 1 ≤ m ∧ (∀ z, v.ex (J z) = u.ex z ≫ i) ∧
      (∀ z, u.ex (R z) = v.ex z ≫ r) ∧ (∀ x ∈ u.Λ, J x ∈ v.Λ) ∧ (∀ x ∈ v.Λ, R x ∈ u.Λ) ∧
      ∀ z, R (J z) = m • z := by
  obtain ⟨B, _, MB, i, r, m, hB, hgB, hMB, hamp, hK, hi, hr, hm, hri⟩ :=
    SS.PrincIsog.exists_isogeny_kTriv ℂ A g hA hgA
  obtain ⟨Q, i', r', hQg, hi', hr', hir'⟩ := exists_polAV_retract_dim ℂ B g hB hgB MB hMB hamp hK
  haveI := hi; haveI := hr; haveI := hi'; haveI := hr'
  suffices key : ∀ n, Q.g = n → ∃ (v : HolUnif Q.A Q.L n) (J : (Fin g → ℂ) →ₗ[ℂ] (Fin n → ℂ))
      (R : (Fin n → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ z, v.ex (J z) = u.ex z ≫ (i ≫ i')) ∧
      (∀ z, u.ex (R z) = v.ex z ≫ (r' ≫ r)) ∧ (∀ x ∈ u.Λ, J x ∈ v.Λ) ∧ (∀ x ∈ v.Λ, R x ∈ u.Λ) ∧
      ∀ z, R (J z) = m • z by
    obtain ⟨v, J, R, hJ, hR, hJΛ, hRΛ, hRJ⟩ := key (8 * g) hQg
    exact ⟨Q, v, i ≫ i', r' ≫ r, J, R, m, hQg, inferInstance, inferInstance, hm, hJ, hR, hJΛ, hRΛ, hRJ⟩
  rintro n rfl
  obtain ⟨rig, hrig⟩ := Q.rigid
  obtain ⟨v, -, -, -, -, -, hv1, hv2, -⟩ := thetaUnifAV_all Q rig hrig
  have hu := TorusTransfer.tangent_bijective u hgA
  obtain ⟨J, hJ, hJΛ, -, -⟩ := HomLinear.exists_linear_of_isMonHom A Q.A hA Q.isAb L Q.L g Q.g u v
    hv1 hv2 (i ≫ i') inferInstance
  obtain ⟨R, hR, hRΛ, -, -⟩ := HomLinear.exists_linear_of_isMonHom Q.A A Q.isAb hA Q.L L Q.g g v u
    hu.1 hu.2 (r' ≫ r) inferInstance
  have hunit : IsUnit ((m : ℕ) : Γ(Sp ℂ, ⊤)) := by
    have := (IsUnit.mk0 (m : ℂ) (by exact_mod_cast (show m ≠ 0 by omega))).map
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
    rwa [map_natCast] at this
  have hsB := (abelianScheme_id_pow_finite_etale_surjective _ B m hB hunit).2.2.2
  have : Surjective (r.left ≫ i.left) := by rw [← Over.comp_left, hri]; exact hsB
  have : Surjective i.left := Surjective.of_comp r.left i.left
  obtain ⟨n, hn, hkill⟩ := exists_pow_eq_one_of_surjective A B g hA hB hgA hgB i
  have hpt : ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, x ≫ (i ≫ i') ≫ (r' ≫ r) ≫ (i ≫ i') = (x ≫ i ≫ i') ^ m := by
    intro x
    simp only [Category.assoc]
    rw [reassoc_of% hir', reassoc_of% hri, ← Category.assoc x i, ← Category.assoc (x ≫ i), MonObj.comp_pow,
      Category.comp_id, MonObj.pow_comp, Category.assoc]
  have hsubv : ∀ a b, v.ex a = v.ex b → a - b ∈ v.Λ := by
    intro a b h
    rw [← v.ker]
    have e := v.ex_add (a - b) b
    rw [sub_add_cancel, h] at e
    have e2 := congrArg (· * (v.ex b)⁻¹) e
    simpa using e2.symm
  have hRJ : ∀ z, R (J z) = m • z := by
    intro z
    have hJy : ∀ t : ℂ, J (t • (R (J z) - m • z)) ∈ v.Λ := by
      intro t
      have h1 : v.ex (J (R (J (t • z)))) = v.ex (m • J (t • z)) := by
        rw [hJ, hR, hJ, holUnif_ex_nsmul_eq_pow, hJ, ← hpt]
        simp only [Category.assoc]
      have h2 := hsubv _ _ h1
      have h3 : t • (R (J z) - m • z) = R (J (t • z)) - m • (t • z) := by
        rw [map_smul, map_smul, smul_sub, smul_comm t m z]
      rw [h3, map_sub, map_nsmul]
      exact h2
    have hJy0 : J (R (J z) - m • z) = 0 :=
      LatticeHom.eq_zero_of_forall_smul_mem v.Λ v.discrete fun t => by rw [← map_smul]; exact hJy t
    have hker : ∀ t : ℂ, u.ex (t • (R (J z) - m • z)) ≫ i = 1 := by
      intro t
      have h2 : u.ex (t • (R (J z) - m • z)) ≫ i ≫ i' = 1 := by
        rw [← hJ, map_smul, hJy0, smul_zero, holUnif_ex_zero_eq_one]
      calc u.ex (t • (R (J z) - m • z)) ≫ i = u.ex (t • (R (J z) - m • z)) ≫ i ≫ i' ≫ r' := by
            rw [hir', Category.comp_id]
        _ = (u.ex (t • (R (J z) - m • z)) ≫ i ≫ i') ≫ r' := by simp only [Category.assoc]
        _ = 1 := by rw [h2, MonObj.one_comp]
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hy0 : R (J z) - m • z = 0 := LatticeHom.eq_zero_of_forall_smul_mem u.Λ u.discrete fun t => by
      rw [← u.ker]
      have e := hkill _ (hker ((n : ℂ)⁻¹ * t))
      rw [← holUnif_ex_nsmul_eq_pow, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ← _root_.mul_assoc,
        mul_inv_cancel₀ hn0, _root_.one_mul] at e
      exact e
    exact sub_eq_zero.1 hy0
  exact ⟨v, J, R, hJ, hR, hJΛ, hRΛ, hRJ⟩

end GlobalTheory.HolUnifHom

namespace GlobalTheory.HolUnifHom

open GlobalTheory.HolUnifEnd in

theorem exists_isMonHom_of_map_lattice :
    ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (g : ℕ), IsAbelianScheme A → IsAbelianScheme A' →
    SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g A'.hom →
    ∀ (L : LB A.left) (L' : LB A'.left) (u : HolUnif A L g) (u' : HolUnif A' L' g) (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
      (∀ x ∈ u.Λ, M x ∈ u'.Λ) → ∃ α : A ⟶ A', IsMonHom α ∧ ∀ w, u'.ex (M w) = u.ex w ≫ α := by
  intro A A' _ _ g hA hA' hgA hgA' L L' u u' M hM
  obtain ⟨hL, -⟩ := abelianSchemeLaws_all
  obtain ⟨Q, v, i, r, J, R, m, hQ, hi, hr, hm, hJ, hR, hJΛ, hRΛ, hRJ⟩ := exists_linear_factor A g hA hgA L u
  obtain ⟨Q', v', i', r', J', R', m', hQ', hi', hr', hm', hJ', hR', hJΛ', hRΛ', hRJ'⟩ :=
    exists_linear_factor A' g hA' hgA' L' u'
  obtain ⟨β, hβ, hβe⟩ := _root_.GlobalTheory.exists_isMonHom_of_map_lattice thetaUnifAV_all hL Q Q' (8 * g) v v'
    (J' ∘ₗ M ∘ₗ R) hQ hQ' (fun l hl => hJΛ' _ (hM _ (hRΛ _ hl)))
  haveI := hi; haveI := hr'; haveI := hβ
  have hφ : ∀ z, u.ex z ≫ i ≫ β ≫ r' = u'.ex ((m' * m) • M z) := by
    intro z
    have e := hβe (J z)
    simp only [LinearMap.comp_apply] at e
    rw [← Category.assoc, ← hJ, ← Category.assoc, ← e, ← hR', hRJ', hRJ, map_nsmul, smul_smul]
  have := hA'.proper
  obtain ⟨α, hα, hαφ⟩ := exists_factor_pow A A' hA (m' * m) (Nat.one_le_iff_ne_zero.2 (by positivity))
    (i ≫ β ≫ r') fun y hy => by
      obtain ⟨z, rfl⟩ := u.ex_onto y
      rw [← holUnif_ex_nsmul_eq_pow, u.ker] at hy
      rw [hφ, u'.ker, ← map_nsmul]
      exact hM _ hy
  refine ⟨α, hα, fun w => ?_⟩
  have hN0 : ((m' * m : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show m' * m ≠ 0 by positivity)
  have hw : (m' * m) • (((m' * m : ℕ) : ℂ)⁻¹ • w) = w := by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hN0, one_smul]
  calc u'.ex (M w) = u'.ex ((m' * m) • M (((m' * m : ℕ) : ℂ)⁻¹ • w)) := by rw [← map_nsmul, hw]
    _ = u.ex (((m' * m : ℕ) : ℂ)⁻¹ • w) ≫ i ≫ β ≫ r' := (hφ _).symm
    _ = u.ex (((m' * m : ℕ) : ℂ)⁻¹ • w) ≫ (𝟙 A ^ (m' * m)) ≫ α := by rw [hαφ]
    _ = u.ex w ≫ α := by
      rw [← Category.assoc, MonObj.comp_pow, Category.comp_id, ← holUnif_ex_nsmul_eq_pow, hw]

end GlobalTheory.HolUnifHom
