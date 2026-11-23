import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.FormQuasiInvariantMirabolic
open PositivityTheory.JacquetShalikaLocal MeasureTheory
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.SatakeBound

section Lat

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

open GroundTheory.Automorphic.GLnLocal in

theorem exists_pow_mul_mem_integer (a : F) :
    ∃ M : ℕ, (uniformizer F : F) ^ M * a ∈ 𝒪[F] := by
  by_cases ha : a ∈ 𝒪[F]
  · exact ⟨0, by simpa using ha⟩
  · have ha0 : a ≠ 0 := fun h => ha (h ▸ zero_mem _)
    have hinv : a⁻¹ ∈ 𝒪[F] := by
      rw [Valuation.mem_integer_iff] at ha ⊢
      rw [map_inv₀]
      exact inv_le_one_of_one_le₀ (le_of_lt (not_le.mp ha))
    have hne : (⟨a⁻¹, hinv⟩ : 𝒪[F]) ≠ 0 := fun h => inv_ne_zero ha0 (congrArg Subtype.val h)
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne (irreducible_uniformizer F)
    refine ⟨n, ?_⟩
    have hu' : ((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) * (⟨a⁻¹, hinv⟩ : 𝒪[F]) = uniformizer F ^ n := by
      rw [hu, ← mul_assoc, Units.inv_mul, one_mul]
    have h2 := congrArg Subtype.val hu'
    push_cast at h2
    have key : (uniformizer F : F) ^ n * a = (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) := by
      rw [← h2, mul_assoc, inv_mul_cancel₀ ha0, mul_one]
    rw [key]
    exact SetLike.coe_mem _

open GroundTheory.Automorphic.GLnLocal in

theorem pow_mul_mem_of_le {M M' : ℕ} (h : M ≤ M') {a : F}
    (ha : (uniformizer F : F) ^ M * a ∈ 𝒪[F]) : (uniformizer F : F) ^ M' * a ∈ 𝒪[F] := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add, mul_comm ((uniformizer F : F) ^ M), mul_assoc]
  exact mul_mem (pow_mem (uniformizer F).2 d) ha

theorem lat_mono {m M M' : ℕ} (h : M ≤ M') : lat F m M ⊆ lat F m M' := by
  intro x hx
  simp only [lat, Set.mem_ofPred_eq] at hx ⊢
  exact fun i => pow_mul_mem_of_le h (hx i)

theorem exists_mem_lat {m : ℕ} (y : Fin m → F) : ∃ M, y ∈ lat F m M := by
  choose N hN using fun i => exists_pow_mul_mem_integer (y i)
  refine ⟨Finset.univ.sup N, ?_⟩
  simp only [lat, Set.mem_ofPred_eq]
  exact fun i => pow_mul_mem_of_le (Finset.le_sup (Finset.mem_univ i)) (hN i)

theorem add_mem_lat {m M : ℕ} {x y : Fin m → F} (hx : x ∈ lat F m M) (hy : y ∈ lat F m M) :
    x + y ∈ lat F m M := by
  simp only [lat, Set.mem_ofPred_eq] at hx hy ⊢
  intro i
  rw [Pi.add_apply, mul_add]
  exact add_mem (hx i) (hy i)

theorem sub_mem_lat {m M : ℕ} {x y : Fin m → F} (hx : x ∈ lat F m M) (hy : y ∈ lat F m M) :
    x - y ∈ lat F m M := by
  simp only [lat, Set.mem_ofPred_eq] at hx hy ⊢
  intro i
  rw [Pi.sub_apply, mul_sub]
  exact sub_mem (hx i) (hy i)

theorem setIntegral_lat_add [MeasurableSpace F] [BorelSpace F] (μ : Measure F)
    [μ.IsAddHaarMeasure] {m M : ℕ} (hmeas : MeasurableSet (lat F m M))
    {y : Fin m → F} (hy : y ∈ lat F m M) (f : (Fin m → F) → ℂ) :
    ∫ x in lat F m M, f (x + y) ∂(Measure.pi fun _ => μ)
      = ∫ x in lat F m M, f x ∂(Measure.pi fun _ => μ) := by
  have hpre : (fun x => y + x) ⁻¹' lat F m M = lat F m M := by
    ext x
    simp only [Set.mem_preimage]
    constructor
    · intro h
      have h' := sub_mem_lat h hy
      rwa [add_sub_cancel_left] at h'
    · intro h
      exact add_mem_lat hy h
  have hmp := measurePreserving_add_left (Measure.pi fun _ : Fin m => μ) y
  have e := hmp.setIntegral_preimage_emb (measurableEmbedding_addLeft y) f (lat F m M)
  rw [hpre] at e
  simp only [add_comm y] at e
  exact e

end Lat

theorem equivariant_of_steps : L0 → ColumnsMirabolic → ColumnsUnipotent → FormCoefficientStability → FormEquivariantColumn := by
  intro hL0 hL3c hL3d _
  unfold L0 ColumnsMirabolic ColumnsUnipotent FormEquivariantColumn ForR ForF at *
  intro F _ _ _ _ _ _ μ _ ψ hψ n V _ _ ρ _ l k B B' hk hInv hChar g hg u u'
  obtain ⟨-, hlat⟩ := hL0 F μ ψ hψ
  have hmeas : ∀ M, MeasurableSet (lat F (k + 1) M) := fun M => ((hlat (k + 1)).1 M).2.2.1
  obtain ⟨hadd, -⟩ := hL3c F μ ψ hψ n k hk
  obtain ⟨hd1, hd2⟩ := hL3d F μ ψ hψ n k hk
  obtain ⟨-, -, -, -, hequi⟩ := hInv
  obtain ⟨g', x₀, hg', rfl, hpsi⟩ := hd1 g hg
  obtain ⟨M₁, hM₁⟩ := hChar ((ρ (g' * col n k x₀)) u) u'
  obtain ⟨M₂, hM₂⟩ := hChar u u'
  obtain ⟨M₃, hM₃⟩ := exists_mem_lat x₀
  have hx₀ : x₀ ∈ lat F (k + 1) (M₁ + M₂ + M₃) := lat_mono (by omega) hM₃
  have hpt : ∀ x : Fin (k + 1) → F,
      ψ (-x (Fin.last k)) * (B u') ((ρ (col n k x)) ((ρ (g' * col n k x₀)) u)) =
        GroundTheory.Automorphic.Whittaker.psiN ψ g' * ψ (x₀ (Fin.last k)) *
          (ψ (-(x + x₀) (Fin.last k)) * (B u') ((ρ (col n k (x + x₀))) u)) := by
    intro x
    obtain ⟨g'', hg'', hc, hps⟩ := hd2 g' hg' x
    have hr : (ρ (col n k x)) ((ρ (g' * col n k x₀)) u) = (ρ g'') ((ρ (col n k (x + x₀))) u) := by
      rw [← Module.End.mul_apply, ← map_mul, ← mul_assoc, hc, mul_assoc, ← hadd, map_mul,
        Module.End.mul_apply]
    have hψ' : ψ (-x (Fin.last k)) = ψ (x₀ (Fin.last k)) * ψ (-(x + x₀) (Fin.last k)) := by
      rw [← AddChar.map_add_eq_mul]
      congr 1
      rw [Pi.add_apply]
      ring
    rw [hr, hequi g'' hg'', hps, hψ']
    ring
  rw [hM₁ (M₁ + M₂ + M₃) (by omega), hM₂ (M₁ + M₂ + M₃) (by omega), hpsi]
  simp_rw [hpt]
  rw [integral_const_mul]
  have e := setIntegral_lat_add μ (hmeas (M₁ + M₂ + M₃)) hx₀
    (fun x => ψ (-x (Fin.last k)) * (B u') ((ρ (col n k x)) u))
  beta_reduce at e
  rw [e]

end GlobalTheory.CompanionTheory.SatakeBound
