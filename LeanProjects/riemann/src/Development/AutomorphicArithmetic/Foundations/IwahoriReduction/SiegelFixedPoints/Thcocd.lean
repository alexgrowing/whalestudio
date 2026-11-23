import Development.AbelianVarietyTheory.Definitions.Foundations.IsZetaTW
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsEqSubOfMemCob
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff
import Development.AbelianVarietyTheory.Definitions.Foundations.PieceEqPieceT
import Development.AbelianVarietyTheory.Definitions.Foundations.AdmissibleHodgeTateZetaClassParams
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.Imports
import Development.AbelianVarietyTheory.Definitions.Foundations.KumValUnique

open scoped MatrixGroups Matrix
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.KZ GlobalTheory.Ord2 GlobalTheory.K4

theorem UpperTheory.Kd.L.thcocd :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], l ≠ 2 →
      (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
      ∀ (A : ValuationSubring Ω) (j : Ω →+* Qbar l), OverL l A → (∀ z : Ω, z ∈ A ↔ ‖j z‖ ≤ 1) →
      ∀ (N : ℕ) [NeZero N], ¬ l ∣ N → ∀ (c d e : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)),
      1 < c → 1 < d → Nat.Coprime c (6 * l * N) → Nat.Coprime d (6 * l * N) → 1 ≤ e →
      (∀ r₀ : (ZMod l)ˣ, ∃ t : (ZMod l)ˣ,
          (![0, 1] : Fin 2 → ZMod l) ᵥ* ((gm r₀ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod l))) =
            (t : ZMod l) • ![(r₀ : ZMod l), -1]) →
      (∀ r₀ : (ZMod l)ˣ, (N : ℤ) ∣ (gm r₀ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) →
      ∀ (pr : X.Fn l → Fin 2 → Qbar l) (α : Qbar l), GlobalTheory.LambdaValuationPowers.AdmissibleHodgeTateZetaClassParams e X pr N gm α →
      ∃ (c₁ : ℕ) (κ₀ : Qbar l), κ₀ ≠ 0 ∧ ∀ (x : ZMod N) (δ : ℕ), Nat.Coprime δ N →
      ∀ (m n c₀ : ℕ), 1 ≤ m → m ≤ n → ∀ bB : (Ω ≃ₐ[ℚ] Ω) → X.Fn l,
        (∀ σ ∈ fixMu Ω (topMu l n m N), LiftB X l N (2 * e - 1) n c₀ (clsBmu X l n m N x c d (2 * e + 1) gm σ) (bB σ)) →
        ∀ (y : (ZMod (l ^ m))ˣ), ∃ g : HahnSeries ℚ Ω, (∀ r, g.coeff r ∈ A) ∧
        ∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 → ∀ (φ : HahnSeries ℚ Ω),
        GlobalTheory.Glue.IsThB X A N l n
          (X.diam N l δ (GlobalTheory.KA.push (redM l n m (N * N)) (fun (s' : Ω ≃ₐ[ℚ] Ω) (y' : (ZMod (topM l n m (N * N)))ˣ) =>
            X.galB l (repM (topM l n m (N * N)) y')
              (bB ((repM (topM l n m (N * N)) y')⁻¹ * s' * repM (topM l n m (N * N)) (y' * (cycM (topM l n m (N * N)) s')⁻¹)))) s y)) φ →
        ∀ tt : ZMod (l ^ n), GlobalTheory.Glue.IsLamG ε l n m s tt →
        ∀ (β : ℕ) (t : ℤ), (β : ZMod (l ^ m)) = (y : ZMod (l ^ m)) → (β : ZMod N) = 1 → (l : ℤ) ^ m * t ≡ 1 [ZMOD N] →
        ∀ i : ℕ,
          Cg n ((l : Qbar l) ^ c₁ * GlobalTheory.KummerEisensteinGalois.seqN 1 j φ i)
            ((l : Qbar l) ^ c₁ * ((l : Qbar l) ^ c₀ * κ₀ * ((tt.val : ℕ) : Qbar l) * (l : Qbar l) ^ m *
                j (GlobalTheory.KummerEisensteinGalois.toQ (l ^ m) (GlobalTheory.KummerEisensteinGalois.pieceT N l m m (2 * e + 1) (1 : DirichletCharacter Ω (l ^ m)) (c : ℤ) (d : ℤ)
                  ((x.val : ℤ) * t * ((((δ : ZMod N)⁻¹).val : ℕ) : ℤ), 0) (t * ((((δ : ZMod N)⁻¹).val : ℕ) : ℤ), 0) (eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m)) ^ β)
                  ((GlobalTheory.KummerEisensteinGalois.unitSet l m).filter fun γ => (γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))).det = 1)) i)) +
              (j (s (g.coeff (i : ℚ))) - j (g.coeff (i : ℚ)))) := by
  intro Ω _ _ _ ε X l _ hl2 hj A j hOver hjA N _ hN c d e gm hc hd hcc hdc he _hrow _hN10 pr α hAdm
  have hl : l.Prime := Fact.out
  have hl0 : l ≠ 0 := hl.ne_zero
  haveI : NeZero l := ⟨hl0⟩
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.mpr hl0⟩
  haveI : ∀ i : ℕ, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => IsSepClosed.hasEnoughRootsOfUnity_pow Ω l i
  have hw : Odd (2 * e - 1) := ⟨e - 1, by omega⟩
  have hw2 : 2 * e - 1 + 2 = 2 * e + 1 := by omega
  obtain ⟨c₁, κ, hκ, H⟩ := UpperTheory.Kd.L.twist l N (2 * e - 1) hw
  refine ⟨c₁, (κ : Qbar l), by exact_mod_cast hκ, ?_⟩
  intro x δ hδ m n c₀ hm hmn bB hB y
  have hG1 : ∀ r : (ZMod l)ˣ, gm r ∈ CongruenceSubgroup.Gamma1 N := fun r => (hAdm.2.2.1 r).1
  have hP : Par l N c d gm := by
    refine ⟨hl2, hAdm.1, hN, hc, hd, hcc, hdc, fun r => ?_, fun r => ?_, fun r => (hAdm.2.2.1 r).2⟩
    · exact CongruenceSubgroup.Gamma0_mem.mpr ((CongruenceSubgroup.Gamma1_mem N _).mp (hG1 r)).2.2
    · simp only [GlobalTheory.KZ.en]
      rw [((CongruenceSubgroup.Gamma1_mem N _).mp (hG1 r)).1, ((CongruenceSubgroup.Gamma1_mem N _).mp (hG1 1)).1]
  have hlA : ((l : ℕ) : Ω) ∈ A.nonunits := by
    obtain ⟨v, hv, hlv⟩ := hOver
    rw [ValuationSubring.mem_nonunits_iff]
    have := (hv (l : 𝓞 ℚ)).mpr (by exact_mod_cast hlv)
    simpa using this
  have hB' : ∀ σ ∈ fixMu Ω (topMu l n m N),
      LiftB X l N (2 * e - 1) n c₀ (clsBmu X l n m N x c d (2 * e - 1 + 2) gm σ) (bB σ) := by
    rw [hw2]; exact hB
  set δu : (ZMod N)ˣ := ZMod.unitOfCoprime δ hδ with hδu
  obtain ⟨g, hgA, hg⟩ := H ε X c d gm hP hG1 A hlA x m n c₀ hm hmn bB hB' y δu
  refine ⟨g, hgA, ?_⟩
  intro s hs hcyc φ hφ tt htt β t hβy hβ1 hlt i
  have hStab : GlobalTheory.Glue.Stab A s := fun z => apply_mem_iff_of_mem_Dec (F := ℚ) hs.1 z
  have hval : ∀ a ∈ A, A.valuation (s a - a) < 1 := fun a ha => hs.2 a ((A.valuation_le_one_iff a).mpr ha)
  have hzt : s (GlobalTheory.Glue.zt ε l m) = GlobalTheory.Glue.zt ε l m :=
    GlobalTheory.Col.fix_of_cycMod le_rfl hcyc (GlobalTheory.Glue.IsNTr.isPrimitiveRoot_zt ε l m).pow_eq_one
  have hsg : sgD N l ((δu : ZMod N).val) = sgD N l δ := by
    unfold sgD
    congr 1
    funext γ
    simp only [IsDiam, hδu, ZMod.coe_unitOfCoprime, ZMod.natCast_zmod_val, ZMod.natCast_val, ZMod.cast_id', id]
  have hφ' : GlobalTheory.Glue.IsThB X A N l n (X.diam N l (δu : ZMod N).val
      (GlobalTheory.KA.push (redM l n m (N * N)) (UpperTheory.Kd.L.bTop X l n m N bB) s y)) φ := by
    rw [show X.diam N l ((δu : ZMod N).val) = X.diam N l δ by unfold Tower.diam; rw [hsg]]
    exact hφ
  have key := hg s hStab hval hzt φ hφ' tt htt β t hβy hβ1 hlt i
  have hinv : ((δu⁻¹ : (ZMod N)ˣ) : ZMod N) = (δ : ZMod N)⁻¹ := by
    rw [← ZMod.inv_coe_unit, hδu, ZMod.coe_unitOfCoprime]
  rw [hinv, hw2] at key
  have gen : ∀ a b : Ω, GlobalTheory.Glue.CgA A l n a b → Cg n (j a) (j b) := by
    rintro a b ⟨z, hz, h⟩
    unfold Cg
    rw [← map_sub, h, map_mul, map_pow, map_natCast, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) ((hjA z).mp hz)
  have := gen _ _ key
  clear H hg hB hB' hφ hφ' _hrow key gen hsg hStab hval hzt hP hG1 hAdm hlA hjA hj hOver
  convert this using 2
  · simp [GlobalTheory.KummerEisensteinGalois.seqN]
  · simp only [map_add, map_mul, map_sub, map_pow, map_natCast, map_ratCast]
