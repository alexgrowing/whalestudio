import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SPushPsi
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CoeffSlD
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SCycZ
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.EqOneOfMemPrincOne

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups Classical

private theorem root_mem {l : ℕ} [hl : Fact l.Prime] (c : Coef l) {x : Qbar l} (hx : x ^ (l - 1) = 1) : x ∈ c.O := by
  have hpos : 0 < l - 1 := Nat.sub_pos_of_lt hl.out.one_lt
  haveI : NeZero (l - 1) := ⟨hpos.ne'⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod l)ˣ)
  rw [Nat.card_eq_fintype_card, ZMod.card_units] at hg
  have hg1 : g ∈ rootsOfUnity (l - 1) (ZMod l) := by
    rw [mem_rootsOfUnity, ← hg, pow_orderOf_eq_one]
  rw [← KStar.TotallyRealRoots.map_red_rootsOfUnity (l := l) dvd_rfl] at hg1
  obtain ⟨ζ, hζ, hζg⟩ := hg1
  have hζ1 : ζ ^ (l - 1) = 1 := hζ
  have hp : IsPrimitiveRoot ζ (l - 1) := by
    refine ⟨hζ1, fun k hk => ?_⟩
    rw [← hg, orderOf_dvd_iff_pow_eq_one, ← hζg, ← map_pow, hk, map_one]
  have hinj : Function.Injective (algebraMap ℤ_[l] (Qbar l)) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (Qbar l), RingHom.coe_comp]
    exact (algebraMap ℚ_[l] (Qbar l)).injective.comp Subtype.val_injective
  have hq := (IsPrimitiveRoot.coe_units_iff.2 hp).map_of_injective hinj
  obtain ⟨i, -, rfl⟩ := hq.eq_pow_of_pow_eq_one hx
  exact pow_mem (c.O.algebraMap_mem _) i

private theorem nle {l : ℕ} [Fact l.Prime] (c : Coef l) {a : Qbar l} (ha : a ∈ c.O) : ‖a‖ ≤ 1 := by
  have hi : IsIntegral ℤ_[l] a := (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨a, ha⟩ : c.O)).map c.O.val
  have hq : IsIntegral ℚ_[l] a := Algebra.IsIntegral.isIntegral a
  change spectralValue (minpoly ℚ_[l] a) ≤ 1
  rw [spectralValue_le_one_iff (minpoly.monic hq)]
  intro k
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hi, Polynomial.coeff_map]
  exact PadicInt.norm_le_one _

private theorem mv_mem {l : ℕ} [Fact l.Prime] (c : Coef l) {M : Matrix (Fin 2) (Fin 2) (Qbar l)} {v : Fin 2 → Qbar l}
    (hM : ∀ i k, M i k ∈ c.O) (hv : ∀ k, v k ∈ c.O) (i : Fin 2) : (M *ᵥ v) i ∈ c.O := by
  rw [Matrix.mulVec, dotProduct]
  exact sum_mem fun k _ => mul_mem (hM i k) (hv k)

private def rd (l : ℕ) : (ZMod (l ^ 1))ˣ →* (ZMod l)ˣ :=
  Units.map (ZMod.castHom (dvd_pow_self l one_ne_zero) (ZMod l)).toMonoidHom

private theorem rd_val (l : ℕ) [Fact l.Prime] (y : (ZMod (l ^ 1))ˣ) :
    ((rd l y : (ZMod l)ˣ) : ZMod l) = (((y : ZMod (l ^ 1)).val : ℕ) : ZMod l) := by
  rw [ZMod.natCast_val]; rfl

theorem UpperTheory.V.Z.Kato.Nb.sInteg :
    UpperTheory.V.Z.Kato.Nb.SInteg := by
  intro l hl Ω _ _ _ ι e gN A W ε X pr N _ x c d gm ψ cf hA he hW
  obtain ⟨-, -, -, -, -, -, hpr, -, -, -, -, χ, -, -, hχ⟩ := hA
  have hS := (sSlD Ω ε X N (Nat.pos_of_ne_zero (NeZero.ne N))).2.2.2.2.2.2.2
  have hχ' : ∀ s : G ℚ Ω, (χ s : Qbar l) = ψ (rd l (cycMod ℚ Ω l 1 s) : (ZMod l)ˣ) := fun s => by
    rw [rd_val]; exact hχ s
  have hsurj : ∀ u : (ZMod l)ˣ, ∃ s : G ℚ Ω, rd l (cycMod ℚ Ω l 1 s) = u := by
    intro u
    refine ⟨repM l u, ?_⟩
    have h1 := (sCycZ Ω l 1 (repM l u)).1
    have h2 := (hS (l ^ 1) (repM l u)).2.2.2.2 l (dvd_pow_self l one_ne_zero)
    rw [h1]
    exact h2.trans ((hS l 1).2.2.1 u)
  have h1 : ψ 1 = 1 := by
    have := hχ' 1
    rw [map_one, map_one, map_one, Units.val_one, Units.val_one] at this
    exact this.symm
  have hmul : ∀ u v : (ZMod l)ˣ, ψ ((u * v : (ZMod l)ˣ) : ZMod l) = ψ u * ψ v := by
    intro u v
    obtain ⟨s, rfl⟩ := hsurj u
    obtain ⟨t, rfl⟩ := hsurj v
    rw [← map_mul, ← map_mul, ← hχ', ← hχ', ← hχ', map_mul, Units.val_mul]
  have hpow : ∀ s : G ℚ Ω, χ s ^ (l - 1) = 1 := by
    intro s
    apply Units.ext
    rw [← map_pow, hχ', map_pow, map_pow, ZMod.units_pow_card_sub_one_eq_one, Units.val_one, h1, Units.val_one]
  have hχO : ∀ s : G ℚ Ω, (χ s : Qbar l) ∈ cf.O := fun s =>
    root_mem cf (by rw [← Units.val_pow_eq_pow_val, hpow, Units.val_one])
  have hεO : ∀ s : G ℚ Ω, eps l s ∈ cf.O := fun s => cf.O.algebraMap_mem ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l])
  let θ : G ℚ Ω →* (Qbar l)ˣ := (cycBar ℚ Ω l ^ e)⁻¹ * χ
  have hθ : ∀ s, thK l e ψ s = (θ s : Qbar l) := fun s => by
    simp only [thK, θ, ← hχ s, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.pow_apply, Units.val_mul,
      Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
  have hθO : ∀ s, (θ s : Qbar l) ∈ cf.O := fun s => by
    have h2 : (θ s : Qbar l) = eps l s⁻¹ ^ e * (χ s : Qbar l) := by
      simp only [θ, eps, map_inv, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.pow_apply, Units.val_mul,
        Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, inv_pow]
    rw [h2]
    exact mul_mem (pow_mem (hεO _) e) (hχO s)
  have hθi : ∀ s, (θ s : Qbar l)⁻¹ = (θ s⁻¹ : (Qbar l)ˣ) := fun s => by
    rw [map_inv, Units.val_inv_eq_inv_val]
  have hρO : ∀ s i k, rhoK W e ψ s i k ∈ cf.O := fun s i k => by
    rw [rhoK, hθ, hθi, Matrix.smul_apply, smul_eq_mul]
    exact mul_mem (hθO _) (hW s i k)
  refine ⟨fun s => ?_, h1, hmul, fun u => ?_, hρO, fun s t => ?_, fun c₀ Y hY r s y i => ?_⟩
  · have h2 := nle cf (hθO s⁻¹)
    rw [← hθi, norm_inv, inv_le_one₀ (norm_pos_iff.2 (θ s).ne_zero)] at h2
    rw [hθ]
    exact le_antisymm (nle cf (hθO s)) h2
  · obtain ⟨s, rfl⟩ := hsurj u
    rw [← hχ']
    exact hχO s
  · simp only [rhoK, hθ, mat, map_mul, Units.val_mul, mul_inv, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [mul_comm ((θ s : Qbar l)⁻¹)]
  · obtain ⟨bB, hbB, b, hb, hc⟩ := hY r 0
    have hF : YfB X l pr W e ψ 0 r N bB s y i ∈ cf.O := by
      unfold YfB GlobalTheory.KA.push
      rw [Finset.sum_apply]
      refine sum_mem fun z _ => mv_mem cf (hρO _) (fun k => hpr _ (hbB _ ?_).1 k) i
      have hM := hS (topM l 0 r (N * N))
      have hm : ∀ s t : Ω ≃ₐ[ℚ] Ω, cycM (topM l 0 r (N * N)) (s * t) = _ := fun s t => (hM s).2.1 t
      have hr := (hM 1).2.2.1
      refine (hM _).2.2.2.1.2 ?_
      have h3 := hm (repM (topM l 0 r (N * N)) z) ((repM (topM l 0 r (N * N)) z)⁻¹ * s *
        repM (topM l 0 r (N * N)) (z * (cycM (topM l 0 r (N * N)) s)⁻¹))
      rw [← mul_assoc, mul_inv_cancel_left, hm, hr, hr, mul_left_comm, mul_inv_cancel, mul_one] at h3
      exact (mul_eq_left.1 h3.symm)
    have h4 := hc s y i
    have h5 := nle cf (add_mem hF (sub_mem (mv_mem cf (hρO s) (hb (y * (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹)) i) (hb y i)))
    rw [Cg, pow_zero, norm_one] at h4
    have h7 : ∀ a a' : Qbar l, ‖a - a'‖ ≤ 1 → ‖a'‖ ≤ 1 → ‖a‖ ≤ 1 := fun a a' ha ha' => by
      have h6 := (IsUltrametricDist.norm_add_le_max (a - a') a').trans (max_le ha ha')
      rwa [sub_add_cancel] at h6
    exact h7 _ _ h4 h5
