import Development.AbelianVarietyTheory.Definitions.Foundations.IsZetaTW
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsEqSubOfMemCob
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff
import Development.AbelianVarietyTheory.Definitions.Foundations.PieceEqPieceT
import Development.AbelianVarietyTheory.Definitions.Foundations.AdmissibleHodgeTateZetaClassParams
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.Thcocd

open scoped MatrixGroups Matrix
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.KZ GlobalTheory.Ord2 GlobalTheory.K4

theorem UpperTheory.Kd.L.thdiam :
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
      ∃ (c₁ : ℕ) (κ₀ : Qbar l), κ₀ ≠ 0 ∧ ∀ (x : ZMod N),
      ∀ (m n c₀ : ℕ), 1 ≤ m → m ≤ n → ∀ bB : (Ω ≃ₐ[ℚ] Ω) → X.Fn l,
        (∀ σ ∈ fixMu Ω (topMu l n m N), LiftB X l N (2 * e - 1) n c₀ (clsBmu X l n m N x c d (2 * e + 1) gm σ) (bB σ)) →
        ∀ (y : (ZMod (l ^ m))ˣ) (δ : (ZMod N)ˣ), ∃ g : HahnSeries ℚ Ω, (∀ r, g.coeff r ∈ A) ∧
        ∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 → ∀ (φ : HahnSeries ℚ Ω),
        GlobalTheory.Glue.IsThB X A N l n
          (X.diam N l (δ : ZMod N).val (GlobalTheory.KA.push (redM l n m (N * N)) (fun (s' : Ω ≃ₐ[ℚ] Ω) (y' : (ZMod (topM l n m (N * N)))ˣ) =>
            X.galB l (repM (topM l n m (N * N)) y')
              (bB ((repM (topM l n m (N * N)) y')⁻¹ * s' * repM (topM l n m (N * N)) (y' * (cycM (topM l n m (N * N)) s')⁻¹)))) s y)) φ →
        ∀ tt : ZMod (l ^ n), GlobalTheory.Glue.IsLamG ε l n m s tt →
        ∀ (β : ℕ) (t : ℤ), (β : ZMod (l ^ m)) = (y : ZMod (l ^ m)) → (β : ZMod N) = 1 → (l : ℤ) ^ m * t ≡ 1 [ZMOD N] →
        ∀ i : ℕ,
          Cg n ((l : Qbar l) ^ c₁ * GlobalTheory.KummerEisensteinGalois.seqN 1 j φ i)
            ((l : Qbar l) ^ c₁ * ((l : Qbar l) ^ c₀ * κ₀ * ((tt.val : ℕ) : Qbar l) * (l : Qbar l) ^ m *
                j (GlobalTheory.KummerEisensteinGalois.toQ (l ^ m) (GlobalTheory.KummerEisensteinGalois.pieceT N l m m (2 * e + 1) (1 : DirichletCharacter Ω (l ^ m)) (c : ℤ) (d : ℤ)
                  ((x.val : ℤ) * t * (((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ), 0) (t * (((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ), 0) (eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m)) ^ β)
                  ((GlobalTheory.KummerEisensteinGalois.unitSet l m).filter fun γ => (γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))).det = 1)) i)) +
              (j (s (g.coeff (i : ℚ))) - j (g.coeff (i : ℚ)))) := by
  intro Ω _ _ _ ε X l _ hl2 hj A j hOver hjA N _ hN c d e gm hc hd hcc hdc he hrow hN10 pr α hAdm
  obtain ⟨c₁, κ₀, hκ, H⟩ := UpperTheory.Kd.L.thcocd Ω ε X l hl2 hj A j hOver hjA N hN c d e gm hc hd hcc hdc he
    hrow hN10 pr α hAdm
  refine ⟨c₁, κ₀, hκ, ?_⟩
  intro x m n c₀ hm hmn bB hB y δ
  obtain ⟨g, hgA, hg⟩ := H x (δ : ZMod N).val (ZMod.val_coe_unit_coprime δ) m n c₀ hm hmn bB hB y
  refine ⟨g, hgA, ?_⟩
  intro s hs hcyc φ hφ tt htt β t hβy hβ1 hlt i
  have key := hg s hs hcyc φ hφ tt htt β t hβy hβ1 hlt i
  have hinv : (((δ : ZMod N).val : ZMod N))⁻¹ = ((δ⁻¹ : (ZMod N)ˣ) : ZMod N) := by
    rw [ZMod.natCast_zmod_val, ZMod.inv_coe_unit]
  rw [hinv] at key
  exact key
