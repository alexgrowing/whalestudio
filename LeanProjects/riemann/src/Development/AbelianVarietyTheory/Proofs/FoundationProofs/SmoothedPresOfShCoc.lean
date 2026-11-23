import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsZetaSystemFixedExponent
import Development.AbelianVarietyTheory.Definitions.Foundations.AdmissibleNewformZetaData
import Development.AbelianVarietyTheory.Definitions.Foundations.AdmissibleHodgeTateZetaClassParams
import Development.AbelianVarietyTheory.Definitions.Foundations.HTPresNuOfPolys
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamF
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamFROfIsLamF
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamFR2
import Development.AbelianVarietyTheory.Definitions.Foundations.ChiProj
import Development.AbelianVarietyTheory.Definitions.Foundations.CoPtMu
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousOfCg

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4
open scoped Matrix MatrixGroups

namespace GlobalTheory.LambdaValuationPowers.Smooth

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem cg_sub_sub {m : ℕ} {a b a' b' : Qbar l} (h : Cg m a a') (h' : Cg m b b') : Cg m (a - b) (a' - b') := by
  have e : a - b - (a' - b') = (a - a') + -(b - b') := by ring
  rw [Cg, e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h (by rw [norm_neg]; exact h'))

theorem isUnit_natCast_padic {d : ℕ} (hd : Nat.Coprime d l) : IsUnit (d : ℤ_[l]) := by
  have hlp : l.Prime := Fact.out
  by_contra h
  have h1 : ‖((d : ℤ) : ℤ_[l])‖ < 1 := by
    rw [← PadicInt.mem_nonunits]; simpa using h
  rw [PadicInt.norm_int_lt_one_iff_dvd] at h1
  exact (Nat.Prime.coprime_iff_not_dvd hlp).1 hd.symm (Int.natCast_dvd_natCast.mp h1)

theorem smoothed_pres [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (hA : OverL l A) (c : Coef l)
    (ν : G ℚ Ω → (Qbar l)ˣ) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l)
    (hL : ∀ r, Layer2 c A ν r (Z r)) (hc : ∀ r, Continuous fun s => Z r s 1)
    (hI : ∀ s ∈ Ine (F := ℚ) A, ν s = 1) (d₀ : ℕ) (hd₀ : Nat.Coprime d₀ l) (m : ℕ) (ζ : Ω)
    (hζ : IsPrimitiveRoot ζ (l ^ m)) :
    ∃ (ι : Type) (_ : Fintype ι) (P : ι → Polynomial Ω) (o : ι → Qbar l),
      HTPresNuOfPolys A c m 0 (fun r s y => Z r s y - (d₀ : Qbar l) * Z r s (y * ZMod.unitOfCoprime d₀ (Nat.Coprime.pow_right r hd₀)))
        ζ P o := by
  classical
  have hlp : l.Prime := Fact.out
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i =>
    haveI : NeZero ((l ^ i : ℕ) : Ω) := ⟨Nat.cast_ne_zero.2 (pow_pos hlp.pos i).ne'⟩
    inferInstance
  have hpos : 0 < l ^ m := pow_pos hlp.pos _
  haveI : NeZero (l ^ m) := ⟨hpos.ne'⟩
  have hz := hL m
  set z := Z m with hzdef
  set uu := ZMod.unitOfCoprime d₀ (Nat.Coprime.pow_right m hd₀) with huu
  have hl : A.valuation (l : Ω) < 1 := by
    obtain ⟨v, hv, hlv⟩ := hA
    have := (hv (l : 𝓞 ℚ)).2 hlv
    simpa using this
  let H : Subgroup (G ℚ Ω) := Ine (F := ℚ) A ⊓ (cycMod ℚ Ω l m).ker
  have hH : ∀ s, s ∈ H ↔ s ∈ Ine (F := ℚ) A ∧ cycMod ℚ Ω l m s = 1 := fun s => Iff.rfl
  have hfix : ∀ s, cycMod ℚ Ω l m s = 1 → s ζ = ζ := fun s hs =>
    GlobalTheory.Col.fix_of_cycMod le_rfl hs hζ.pow_eq_one

  have hu₀ := isUnit_natCast_padic (l := l) hd₀
  obtain ⟨ρ, hρ, hρc⟩ := GlobalTheory.CycInertia.exists_mem_Ine_toZModPow Ω l A hl hu₀.unit m
  rw [hu₀.unit_spec, map_natCast] at hρc
  have hρD : ρ ∈ Dec (F := ℚ) A := Ine_le_Dec A hρ
  have hρi : ρ⁻¹ ∈ Ine (F := ℚ) A := inv_mem hρ
  have hρζ : ρ ζ = ζ ^ d₀ := by
    have hspec : ρ ζ = ζ ^ (PadicInt.toZModPow m ((cycZ ℚ Ω l ρ : ℤ_[l]ˣ) : ℤ_[l])).val :=
      cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G ℚ Ω) Ω ρ) ζ hζ.pow_eq_one
    rw [hspec, hρc, ZMod.val_natCast, hζ.eq_orderOf, pow_mod_orderOf]
  have hcρ : (cycMod ℚ Ω l m ρ⁻¹)⁻¹ = uu := by
    rw [map_inv, inv_inv]
    exact Units.ext (by rw [huu, ZMod.coe_unitOfCoprime]; exact hρc)
  have z11 : z 1 1 = 0 := GlobalTheory.KZ.UnitPres.layer_one hz
  have key : ∀ s ∈ H, z s uu = z (ρ⁻¹ * s * ρ) 1 := by
    intro s hs
    obtain ⟨hsI, hsc⟩ := (hH s).1 hs
    have hsD := Ine_le_Dec A hsI
    have e1 := hz.2 ρ⁻¹ (inv_mem hρD) (s * ρ) (mul_mem hsD hρD) 1
    have e2 := hz.2 s hsD ρ hρD uu
    have e3 := hz.2 ρ⁻¹ (inv_mem hρD) ρ hρD 1
    rw [hcρ] at e1 e3
    rw [inv_mul_cancel, z11, hI _ hρi, Units.val_one, one_mul, one_mul] at e3
    rw [hI _ hρi, Units.val_one, one_mul, one_mul] at e1
    rw [hI _ hsI, Units.val_one, one_mul, hsc, inv_one, mul_one] at e2
    rw [mul_assoc]
    linear_combination -e1 - e2 + e3
  have hHρ : ∀ s ∈ H, ρ⁻¹ * s * ρ ∈ H := fun s hs => by
    obtain ⟨hsI, hsc⟩ := (hH s).1 hs
    refine (hH _).2 ⟨?_, ?_⟩
    · have := conj_mem_Ine (inv_mem hρD) hsI
      rwa [inv_inv] at this
    · rw [map_mul, map_mul, hsc, mul_one, map_inv, inv_mul_cancel]
  obtain ⟨ι, hι, o, crd, ho, hadd, hzero, hcrd, -⟩ := GlobalTheory.CoefCoord.coord_mod_pow l c m
  obtain ⟨U, hU, hUz⟩ := GlobalTheory.KZ.UnitPres.exists_open (fun s => z s 1) (hc m) z11 m
  have hex : ∀ i, ∃ u : Ω, u ≠ 0 ∧ (∀ s ∈ H, s u = u) ∧
      ∀ s ∈ H, GlobalTheory.Col.KumVal (l := l) m ζ u s (crd (z s 1) i) := fun i =>
    GlobalTheory.KumFix.exists_kumVal l Ω m H (GlobalTheory.isClosed_Ine_inf_ker_cycMod l Ω A _) ζ hζ
      (fun s hs => hfix s hs.2) (fun s => crd (z s 1) i)
      (fun s hs t ht => by
        show crd (z (s * t) 1) i = crd (z s 1) i + crd (z t 1) i
        rw [GlobalTheory.KZ.UnitPres.layer_add hz (Ine_le_Dec A hs.1) (Ine_le_Dec A ht.1) hs.2, hI s hs.1, Units.val_one, one_mul,
          hadd _ (hz.1 _ _) _ (hz.1 _ _), Pi.add_apply])
      U hU (fun s _ hs => by
        show crd (z s 1) i = 0
        rw [hzero _ (hz.1 _ _) (hUz s hs), Pi.zero_apply])
  choose u hu0 hufix huk using hex

  have hw0 : ∀ i, u i * (ρ (u i))⁻¹ ≠ 0 := fun i =>
    mul_ne_zero (hu0 i) (inv_ne_zero ((map_ne_zero ρ).2 (hu0 i)))
  have hvw : ∀ i, A.valuation (u i * (ρ (u i))⁻¹) = 1 := fun i => by
    rw [map_mul, map_inv₀, GlobalTheory.TameLabels.valuation_apply_of_mem_Dec hρD, mul_inv_cancel₀]
    exact (Valuation.ne_zero_iff _).2 (hu0 i)
  have hwfix : ∀ i, ∀ s ∈ H, s (u i * (ρ (u i))⁻¹) = u i * (ρ (u i))⁻¹ := fun i s hs => by
    have e : s (ρ (u i)) = ρ ((ρ⁻¹ * s * ρ) (u i)) := by
      rw [← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply]; congr 1; group
    rw [map_mul, map_inv₀, hufix i s hs, e, hufix i _ (hHρ s hs)]
  have hP : ∀ i, ∃ P : Polynomial Ω, (∀ x ∈ P.coeffs, x ∈ A ∧ ∀ s ∈ Ine (F := ℚ) A, s x = x) ∧
      P.eval ζ = u i * (ρ (u i))⁻¹ := fun i =>
    GlobalTheory.CycIne.exists_poly_of_fixed l Ω A hA m ζ hζ _ ((A.valuation_le_one_iff _).1 (hvw i).le)
      (fun s h1 h2 => hwfix i s ((hH s).2 ⟨h1, h2⟩))
  choose P hPc hPe using hP
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hpos.ne'

  have hkw : ∀ s ∈ H, ∀ i, GlobalTheory.Col.KumVal (l := l) m ζ (u i * (ρ (u i))⁻¹) s
      ((((crd (z s 1) i).val : ℤ) - (d₀ : ℤ) * ((crd (z (ρ⁻¹ * s * ρ) 1) i).val : ℤ) : ℤ) : ZMod (l ^ m)) := by
    intro s hs i
    obtain ⟨v, hv, hsv⟩ := huk i s hs
    obtain ⟨v', hv', hsv'⟩ := huk i _ (hHρ s hs)
    refine GlobalTheory.KZ.UnitPres.kumVal_int hζ.pow_eq_one (v := v * (ρ v')⁻¹) ?_ ?_
    · rw [mul_pow, inv_pow, ← map_pow, hv', hv]
    · have e : s (ρ v') = ρ ((ρ⁻¹ * s * ρ) v') := by
        rw [← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply]; congr 1; group
      rw [map_mul, map_inv₀, hsv, e, hsv', map_mul, map_pow, hρζ, zpow_sub₀ hζ0, zpow_mul]
      simp only [zpow_natCast]
      ring
  refine ⟨ι, hι, P, o, hζ, hPc, fun i => (ho i).1, fun i => by rw [hPe]; exact hw0 i, ?_⟩
  show GlobalTheory.Col.KumPres A m m (ζ ^ l ^ 0) _ _ _
  rw [pow_zero, pow_one]
  refine ⟨hζ, le_rfl, fun i => ?_, fun i => (ho i).2, fun s hs hc' _ => ?_⟩
  · simp only [hPe]
    refine ⟨(A.valuation_le_one_iff _).1 (hvw i).le, hw0 i, (A.valuation_le_one_iff _).1 ?_⟩
    rw [map_inv₀, hvw i, inv_one]
  · have hsH : s ∈ H := (hH s).2 ⟨hs, hc'⟩
    refine ⟨fun i => ((((crd (z s 1) i).val : ℤ) - (d₀ : ℤ) * ((crd (z (ρ⁻¹ * s * ρ) 1) i).val : ℤ) : ℤ) : ZMod (l ^ m)),
      fun i => by simp only [hPe]; exact hkw s hsH i, ?_⟩
    show Cg m (z s 1 - (d₀ : Qbar l) * z s (1 * uu)) _
    rw [one_mul, key s hsH]
    have h2 := hcrd _ (hz.1 s 1)
    have h3 := hcrd _ (hz.1 (ρ⁻¹ * s * ρ) 1)
    have h4 := cg_sub_sub h2 (GlobalTheory.KumUnit.cg_mul_left (o := (d₀ : Qbar l)) (IsUltrametricDist.norm_natCast_le_one (Qbar l) d₀) h3)
    refine GlobalTheory.KumUnit.cg_trans h4 (GlobalTheory.KumUnit.cg_symm (GlobalTheory.KumUnit.cg_trans
      (GlobalTheory.KumUnit.cg_sum _ fun i _ => GlobalTheory.KumUnit.cg_mul_left (ho i).2 (GlobalTheory.KZ.UnitPres.cg_intCast _ _)) ?_))
    have e : (∑ i, o i * ((((crd (z s 1) i).val : ℤ) - (d₀ : ℤ) * ((crd (z (ρ⁻¹ * s * ρ) 1) i).val : ℤ) : ℤ) : Qbar l)) =
        (∑ i, o i * ((crd (z s 1) i).val : Qbar l)) - (d₀ : Qbar l) * ∑ i, o i * ((crd (z (ρ⁻¹ * s * ρ) 1) i).val : Qbar l) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast; ring
    rw [e, Cg, sub_self, norm_zero]
    exact norm_nonneg _

theorem smoothed_pres_of_shCoc [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (hA : OverL l A) (c : Coef l)
    (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l))
    (hD : ∀ s ∈ Dec (F := ℚ) A, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 0 = 0)
    (hI : ∀ s ∈ Ine (F := ℚ) A, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 1 = 1)
    (Y : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l)
    (hY : ∀ r, GlobalTheory.KA.ShCoc (fun s => (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l))) (cycMod (F := ℚ) (Ω := Ω) l r)⁻¹ (Y r))
    (hc : ∀ (r n : ℕ), ∃ E0 : Finset Ω, ∀ (s s' : G ℚ Ω) (y : (ZMod (l ^ r))ˣ), (∀ z ∈ E0, s' z = z) →
      Cg n (Y r (s * s') y 1) (Y r s y 1))
    (hO : ∀ r s y, Y r s y 1 ∈ c.O) (d₀ : ℕ) (hd₀ : Nat.Coprime d₀ l) (m : ℕ) (ζ : Ω) (hζ : IsPrimitiveRoot ζ (l ^ m)) :
    ∃ (ι : Type) (_ : Fintype ι) (P : ι → Polynomial Ω) (o : ι → Qbar l),
      HTPresNuOfPolys A c m 0 (fun r s y => Y r s y 1 - (d₀ : Qbar l) *
        Y r s (y * ZMod.unitOfCoprime d₀ (Nat.Coprime.pow_right r hd₀)) 1) ζ P o := by
  classical
  have hnz : ∀ s ∈ Dec (F := ℚ) A, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 1 ≠ 0 := by
    intro s hs h
    have := (ρ s).det_ne_zero
    rw [Matrix.det_fin_two, hD s hs, h] at this
    simp at this
  let ν : G ℚ Ω → (Qbar l)ˣ := fun s =>
    if h : (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 1 ≠ 0 then Units.mk0 _ h else 1
  have hν : ∀ s ∈ Dec (F := ℚ) A, (ν s : Qbar l) = (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 1 := by
    intro s hs
    simp only [ν, dif_pos (hnz s hs), Units.val_mk0]
  refine smoothed_pres A hA c ν (fun r s y => Y r s y 1) (fun r => ⟨hO r, fun s hs u _ x => ?_⟩)
    (fun r => GlobalTheory.LambdaValuationPowers.AllRoots.continuous_of_cg _ fun n => ?_) (fun s hs => ?_) d₀ hd₀ m ζ hζ
  · have := congrFun (hY r s u x) 1
    show Y r (s * u) x 1 = Y r s x 1 + (ν s : Qbar l) * Y r u (x * (cycMod ℚ Ω l r s)⁻¹) 1
    rw [this, hν s hs]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hD s hs]
  · obtain ⟨E0, hE⟩ := hc r n
    exact ⟨E0, fun s s' h => hE s s' 1 h⟩
  · exact Units.ext (by rw [hν s (Ine_le_Dec A hs), hI s hs, Units.val_one])

theorem exists_pres_smoothed : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl)
    (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)), Nf e S A W → SrcUr ι e A W g →
  ∀ (ε : Ω →+* ℂ) (X : Tower Ω ε) (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (cw : ZMod N → Qbar l) (c d : ℕ)
    (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ₀ : ZMod l → Qbar l) (cf : Coef l) (α : Qbar l),
    (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → l ≠ 2 → 1 ≤ e →
    AdmWn ι e g A W X pr N cw c d gm ψ₀ cf → GlobalTheory.LambdaValuationPowers.AdmissibleHodgeTateZetaClassParams e X pr N gm α →
  ∀ (j : Ω →+* Qbar l), (∀ y, y ∈ A ↔ ‖j y‖ ≤ 1) →
  ∀ (c₀ : ℕ) (Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l),
    IsZWc X l pr W e ψ₀ N cw c d (2 * e + 1) gm cf c₀ Y →
    (∀ r, GlobalTheory.KA.ShCoc (rhoK W e ψ₀) (cycMod (F := ℚ) (Ω := Ω) l r)⁻¹ (Y r)) →
    (∀ (r n : ℕ), ∃ E0 : Finset Ω, ∀ (s s' : Ω ≃ₐ[ℚ] Ω) (y : (ZMod (l ^ r))ˣ), (∀ z ∈ E0, s' z = z) → Cg n (Y r (s * s') y 1) (Y r s y 1)) →
    (∀ r s y, Y r s y 1 ∈ cf.O) →
  ∀ (d₀ : ℕ) (hd₀ : Nat.Coprime d₀ l), 2 ≤ d₀ →
  ∃ (m₀ c₀' : ℕ), ∀ m, m₀ ≤ m → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ m) → ∃ (ι : Type) (_ : Fintype ι) (P : ι → Polynomial Ω) (o : ι → Qbar l),
    HTPresNuOfPolys A cf m c₀' (fun r s y => Y r s y 1 - (d₀ : Qbar l) * Y r s (y * ZMod.unitOfCoprime d₀ (Nat.Coprime.pow_right r hd₀)) 1) ζ P o := by
  intro l _ Ω _ _ _ ι e S A W g hN hS ε X pr N _ cw c d gm ψ₀ cf α _ _ _ hAdm _ j _ c₀ Y hZ hY hc hO d₀ hd₀ _
  refine ⟨0, 0, fun m _ ζ hζ => ?_⟩
  by_cases hcw : ∃ x, cw x ≠ 0
  · obtain ⟨x, hx⟩ := hcw
    obtain ⟨ρ, hρ, -, hD, hI, -⟩ := GlobalTheory.RhoAdm.rho_ordinary_shape l Ω ι e S A W g ψ₀ hN hS
      (hAdm.1 x hx).2.2.2.2.2.2.2.2.2.2.2
    have hfun : rhoK W e ψ₀ = fun s => (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) := funext fun s => (hρ s).symm
    exact smoothed_pres_of_shCoc A hN.atL cf ρ hD hI Y (fun r => hfun ▸ hY r) hc hO d₀ hd₀ m ζ hζ
  · refine GlobalTheory.LambdaValuationPowers.AllRoots.pres_of_vanish A cf _ m ζ hζ fun s _ _ => ?_
    obtain ⟨Yx, -, hs⟩ := hZ
    push_neg at hcw
    simp [hs, hcw]

end GlobalTheory.LambdaValuationPowers.Smooth
