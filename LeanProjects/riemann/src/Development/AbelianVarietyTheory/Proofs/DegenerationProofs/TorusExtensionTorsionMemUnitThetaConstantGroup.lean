import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtOntoDivisibleKernel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairingStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionMapsCompatibleInLevelStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaConstantValuationsUnitsEveryCosetStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.OneBasis.UnitGen
open GlobalTheory.TorusExt

theorem mem_of_step {M T : Type} [CommGroup M] (S : Subgroup M) (φ : T → M) (n j : ℕ) (h₀ : ∀ t, φ t ^ (n ^ j) = 1)
    (h : ∀ t, ∃ s ∈ S, ∃ t', φ t = s * φ t' ^ n) (t : T) : φ t ∈ S := by
  have key : ∀ i : ℕ, ∃ s ∈ S, ∃ t', φ t = s * φ t' ^ (n ^ i) := fun i => by
    induction i with
    | zero => exact ⟨1, S.one_mem, t, by simp⟩
    | succ i ih =>
      obtain ⟨s, hs, t', e⟩ := ih
      obtain ⟨s', hs', t'', e'⟩ := h t'
      refine ⟨s * s' ^ (n ^ i), S.mul_mem hs (S.pow_mem hs' _), t'', ?_⟩
      rw [e, e', mul_pow, ← pow_mul, _root_.mul_assoc, pow_succ']
  obtain ⟨s, hs, t', e⟩ := key j
  rwa [e, h₀, _root_.mul_one]

attribute [local instance] gtGroup

theorem exists_hom {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (hB : D.TauBimult) {F : Type} [Field F]
    [Algebra (FractionRing R) F] {k : ℕ} {M : Type} [CommGroup M] (f : QkPt D F k → M)
    (hf : ∀ p p' p'', QkAdd p p' p'' → f p'' = f p * f p') :
    ∃ φ : (nsmulAddMonoidHom k : GtPtF D F →+ GtPtF D F).ker →+ Additive M,
      ∀ t (p : QkPt D F k), p.y = 0 → p.g = t.1 → φ t = Additive.ofMul (f p) := by
  let r : (nsmulAddMonoidHom k : GtPtF D F →+ GtPtF D F).ker → QkPt D F k := fun t =>
    qkMk hB 0 t.1 ((show k • t.1 = 0 from t.2).trans (map_zero _).symm)
  refine ⟨AddMonoidHom.mk' (fun t => Additive.ofMul (f (r t))) fun t t' => ?_, fun t p hy hg => ?_⟩
  · rw [← ofMul_mul, ← hf _ _ _ (qkAdd_qkAdd hB (r t) (r t'))]
    exact congrArg (fun p => Additive.ofMul (f p)) (qk_ext (add_zero _).symm rfl)
  · exact congrArg (fun p => Additive.ofMul (f p)) (qk_ext hy.symm hg.symm)

theorem fromGt_mem_unitGrp : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (th : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ → Prim D Q v ϑ → ∀ n j : ℕ, n.Prime → Odd n → IsUnit (n : V) → 2 ≤ j → ∀ x : TFK (R := V) F ⟶ A.A, FromGt U.toUnifPre (n ^ j) x → x ∈ unitGrp v ρ th (n ^ j) := by
  intro hL h₁ h₂ h₃ h₄ V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN th ϑ hE hP n j hn ho hu hj x hx
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  have hB := D.tau_bimult
  have hdvd : n ∣ n ^ j := dvd_pow_self n (by omega)
  have hdvd₂ : n * n ∣ n ^ j := by rw [← pow_two]; exact pow_dvd_pow n hj
  have hm : Odd (n ^ j) := ho.pow
  have hum : IsUnit ((n ^ j : ℕ) : V) := by rw [Nat.cast_pow]; exact hu.pow j
  have kill : ∀ {M : Type} [CommGroup M]
      (φ : (nsmulAddMonoidHom (n ^ j) : GtPtF D.toPre F →+ GtPtF D.toPre F).ker →+ Additive M) t,
      Additive.toMul (φ t) ^ (n ^ j) = 1 := fun φ t => by
    rw [← toMul_nsmul, ← map_nsmul, show (n ^ j) • t = 0 from Subtype.ext t.2, map_zero, toMul_zero]
  have ua := (GlobalTheory.T.theta_constant_valuations_units_every_coset hL h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hN th ϑ hE hP _ hm hum).2 n hn.two_le hdvd
  have fin : ∀ {M T : Type} [CommGroup M] (S : Subgroup M) (φ : T → M), (∀ t, φ t ^ (n ^ j) = 1) →
    (∀ t, ∃ s ∈ S, ∃ t', φ t = s * φ t' ^ n) → ∀ t, φ t ∈ S := fun S φ => mem_of_step S φ n j
  generalize n ^ j = m at *
  have m1 : 1 ≤ m := hm.pos
  have div := (gt_onto_divisible_kernel hL V _ hA D F).2.1
  have lev := fun p q x => (GlobalTheory.T.uniformisation_torsion_maps_compatible_in_level hL V _ hA D A G hG U F m m (m ^ 2) m1 m1 (pow_two m) p q x).2
  obtain ⟨f, f₁, -, f₃, f₄, -⟩ := GlobalTheory.T.uniformisation_torsion_identification_with_pairing hL V _ hA D A G hG U F m m1
  obtain ⟨f', f₁', -, -, f₄', -⟩ := GlobalTheory.T.uniformisation_torsion_identification_with_pairing hL V _ hA D A G hG U F (m ^ 2) (pow_pos hm.pos 2)
  obtain ⟨φ, hφ⟩ := exists_hom hB f f₄
  obtain ⟨φ', hφ'⟩ := exists_hom hB f' f₄'
  have mem : ∀ {k} (p : QkPt D.toPre F k), p.y = 0 →
      p.g ∈ (nsmulAddMonoidHom k : GtPtF D.toPre F →+ GtPtF D.toPre F).ker := fun {k} p hy => by
    show k • p.g = 0
    rw [qk_nsmul hB, hy, map_zero]
  have mk : ∀ {k : ℕ} (g : GtPtF D.toPre F), k • g = 0 → ∃ p : QkPt D.toPre F k, p.y = 0 ∧ p.g = g := fun g h =>
    ⟨qkMk hB 0 g (h.trans (map_zero _).symm), rfl, rfl⟩
  have inj : ∀ t, φ t = 0 → t = 0 := fun t ht => by
    obtain ⟨p, py, pg⟩ := mk t.1 t.2
    obtain ⟨o, oy, og⟩ := mk (k := m) 0 (nsmul_zero m)
    have e : f o = f p := Additive.ofMul.injective (by rw [← hφ t p py pg, ← hφ 0 o oy og, ht, map_zero])
    obtain ⟨z, hy, hg⟩ := (equiv_iff hB _ _).1 ((f₃ _ _).1 e)
    rw [py, oy, zero_add] at hy
    have z0 : z = 0 := by
      by_contra h0
      have b₁ := QForm.Q_pos hϖ D hQ h0
      have b₂ := Q_nsmul hϖ hQ m z
      rw [← hy, QForm.Q_zero hϖ D hQ] at b₂
      have b₃ : (0 : ℤ) < (m : ℤ) ^ 2 := by exact_mod_cast pow_pos hm.pos 2
      exact absurd b₂ (mul_pos b₃ (by omega)).ne
    rw [z0, map_zero, add_zero, pg, og] at hg
    exact Subtype.ext hg
  obtain ⟨p, py, hp⟩ := hx
  have ex : x = Additive.toMul (φ ⟨p.g, mem p py⟩) := by rw [hφ _ p py rfl, (f₁ p x).1 hp]; rfl
  rw [ex]
  refine fin _ (fun t => Additive.toMul (φ t)) (kill φ) (fun t => ?_) _
  obtain ⟨r, ry, rg⟩ := mk t.1 t.2
  obtain ⟨g', hg'⟩ := div m m1 t.1
  have e₁ : t.1 = m • g' := (isNsmul_iff_eq _ _ _).1 hg'
  obtain ⟨q, qy, qg⟩ := mk (k := m ^ 2) g' (by rw [pow_two, mul_smul, ← e₁]; exact t.2)
  have hq : QkToAkU U.toUnifPre F (m ^ 2) q (f' q) := (f₁' _ _).2 rfl
  have e₂ : f' q ^ m = Additive.toMul (φ t) := by
    rw [hφ t r ry rg]
    exact (f₁ _ _).1 (lev r q _ (ry.trans qy.symm) (by rw [qg, rg]; exact hg') hq)
  obtain ⟨p', x', t₁, c, py', hx', hn', hT, hc₀⟩ := ua q _ qy hq
  have x1 : x' ^ (m ^ 2) = 1 := by
    rw [(f₁' _ _).1 hx']
    have := congrArg Additive.toMul (hφ' ⟨_, mem p' py'⟩ p' py' rfl)
    rw [toMul_ofMul] at this
    rw [← this, ← toMul_nsmul, ← map_nsmul,
      show (m ^ 2) • (⟨_, mem p' py'⟩ : (nsmulAddMonoidHom (m ^ 2) : GtPtF D.toPre F →+ GtPtF D.toPre F).ker) = 0 from
        Subtype.ext (mem p' py'), map_zero, toMul_zero]
  obtain ⟨s, sy, sg⟩ := mk (k := m) (m • p'.g) (by rw [← mul_smul, ← pow_two]; exact mem p' py')
  have e₃ : x' ^ m = Additive.toMul (φ ⟨_, mem s sy⟩) := by
    rw [hφ _ s sy rfl]
    exact (f₁ _ _).1 (lev s p' _ (sy.trans py'.symm) ((isNsmul_iff_eq _ _ _).2 sg) hx')
  refine ⟨x' ^ m, Subgroup.subset_closure ⟨x', t₁, c, x1, hT, hc₀, rfl⟩, ?_⟩
  rw [e₂, e₃] at hn'
  rw [e₃]
  generalize (⟨_, mem s sy⟩ : (nsmulAddMonoidHom m : GtPtF D.toPre F →+ GtPtF D.toPre F).ker) = a at hn'
  have z : n • (a - t) = 0 := inj _ (by
    rw [map_nsmul, map_sub]
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_sub, div_eq_mul_inv, hn', toMul_zero])
  obtain ⟨w, hw⟩ := div n hn.one_le (t - a).1
  have e₄ : (t - a).1 = n • w := (isNsmul_iff_eq _ _ _).1 hw
  have z' : n • (t - a) = 0 := by rw [← neg_sub, smul_neg, z, neg_zero]
  have wm : m • w = 0 := by
    obtain ⟨d, hd⟩ := hdvd₂
    have : n • (t - a).1 = 0 := congrArg Subtype.val z'
    rw [hd, _root_.mul_comm, mul_smul, mul_smul, ← e₄, this, smul_zero]
  refine ⟨⟨w, wm⟩, ?_⟩
  show Additive.toMul (φ t) = Additive.toMul (φ a) * Additive.toMul (φ ⟨w, wm⟩) ^ n
  rw [← toMul_nsmul, ← map_nsmul, ← toMul_add, ← map_add,
    show n • (⟨w, wm⟩ : (nsmulAddMonoidHom m : GtPtF D.toPre F →+ GtPtF D.toPre F).ker) = t - a from
      Subtype.ext e₄.symm, add_sub_cancel]

end GlobalTheory.OneBasis.UnitGen
end
