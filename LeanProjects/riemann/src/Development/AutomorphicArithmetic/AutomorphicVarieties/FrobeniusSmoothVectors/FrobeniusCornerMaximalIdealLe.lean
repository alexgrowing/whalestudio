import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CornerUnits
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.MemPowSmulLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.IsInternalCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CoB

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem mem_of_forall_sup_pow {B : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    (P : Ideal B) (b : B) (h : ∀ N : ℕ, ∃ y ∈ P, b - y ∈ maximalIdeal B ^ N) : b ∈ P := by
  by_cases hP : P = ⊤
  · rw [hP]
    exact Submodule.mem_top
  haveI : Nontrivial (B ⧸ P) := Ideal.Quotient.nontrivial_iff.2 hP
  haveI : IsLocalRing (B ⧸ P) := IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  have hPm : P ≤ maximalIdeal B := IsLocalRing.le_maximalIdeal hP
  have hmap : maximalIdeal B ≤ (maximalIdeal (B ⧸ P)).comap (Ideal.Quotient.mk P) := by
    intro x hx
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (↑u⁻¹ : B ⧸ P)
    have h1 : Ideal.Quotient.mk P (x * y - 1) = 0 := by
      rw [map_sub, map_mul, hy, ← hu, Units.mul_inv, map_one, sub_self]
    have h2 := hPm (Ideal.Quotient.eq_zero_iff_mem.1 h1)
    have h3 := (maximalIdeal B).sub_mem ((maximalIdeal B).mul_mem_right y hx) h2
    rw [sub_sub_cancel] at h3
    exact (IsLocalRing.maximalIdeal.isMaximal B).ne_top ((Ideal.eq_top_iff_one _).2 h3)
  have hb : Ideal.Quotient.mk P b ∈ ⨅ N : ℕ, (maximalIdeal (B ⧸ P)) ^ N := by
    rw [Ideal.mem_iInf]
    intro N
    obtain ⟨y, hy, hby⟩ := h N
    have h3 := Ideal.mem_map_of_mem (Ideal.Quotient.mk P) hby
    rw [Ideal.map_pow] at h3
    have h4 := Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 hmap) N h3
    rwa [map_sub, Ideal.Quotient.eq_zero_iff_mem.2 hy, sub_zero] at h4
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top, Ideal.mem_bot,
    Ideal.Quotient.eq_zero_iff_mem] at hb
  exact hb

theorem UpperTheory.V.Fr.frobenius_corner_maximalIdeal_le :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ (S : Space O F n) (P : Ideal S.B), (maximalIdeal O).map (algebraMap O S.B) ≤ P → (∀ x : S.B, (x : S.R) ∈ S.ρ.mon 0 → ∃ c : O, x - algebraMap O S.B c ∈ P) → (∀ v i g, ∃ c : O, S.ψB v i g - algebraMap O S.B c ∈ P) → S.mB ≤ P := by
  intro l _ O _ _ _ _ F C₀ n hF hn S P hO hmon hψ
  obtain ⟨hco, hmax⟩ := co_B hF hn S
  haveI := hco
  obtain ⟨-, -, h0, -, -, -, -⟩ := gr_A hF hn S
  obtain ⟨-, -, -, hcl⟩ := cont_u hF hn S
  have hinj : Function.Injective (algebraMap S.B S.A) := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : S.A => (z : S.R)) hxy
  by_cases hPt : P = ⊤
  · rw [hPt]
    exact le_top
  have hPm : P ≤ S.mB := hmax ▸ IsLocalRing.le_maximalIdeal hPt
  let T : Subalgebra O S.R :=
    { carrier := {r | ∃ hr : r ∈ S.B, ∃ c : O, (⟨r, hr⟩ : S.B) - algebraMap O S.B c ∈ P}
      mul_mem' := by
        rintro a b ⟨ha, c, hc⟩ ⟨hb, d, hd⟩
        refine ⟨S.B.mul_mem ha hb, c * d, ?_⟩
        have e1 : (⟨a * b, S.B.mul_mem ha hb⟩ : S.B) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
        have e : (⟨a, ha⟩ * ⟨b, hb⟩ : S.B) - algebraMap O S.B (c * d) =
            (⟨a, ha⟩ - algebraMap O S.B c) * ⟨b, hb⟩ + algebraMap O S.B c * (⟨b, hb⟩ - algebraMap O S.B d) := by
          rw [map_mul]
          ring
        rw [e1, e]
        exact P.add_mem (P.mul_mem_right _ hc) (P.mul_mem_left _ hd)
      add_mem' := by
        rintro a b ⟨ha, c, hc⟩ ⟨hb, d, hd⟩
        refine ⟨S.B.add_mem ha hb, c + d, ?_⟩
        have e1 : (⟨a + b, S.B.add_mem ha hb⟩ : S.B) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
        have e : (⟨a, ha⟩ + ⟨b, hb⟩ : S.B) - algebraMap O S.B (c + d) =
            (⟨a, ha⟩ - algebraMap O S.B c) + (⟨b, hb⟩ - algebraMap O S.B d) := by
          rw [map_add]
          ring
        rw [e1, e]
        exact P.add_mem hc hd
      algebraMap_mem' := by
        intro c
        refine ⟨S.B.algebraMap_mem c, c, ?_⟩
        have e : (⟨algebraMap O S.R c, S.B.algebraMap_mem c⟩ : S.B) = algebraMap O S.B c := rfl
        rw [e, sub_self]
        exact P.zero_mem }
  have hB0 : Algebra.adjoin O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = ((S.ρ.ψ v i g : S.Rˣ) : S.R)}) ≤ T := by
    rw [Algebra.adjoin_le_iff]
    rintro r (hr | ⟨v, i, g, rfl⟩)
    · exact ⟨S.mon_mem hr, hmon ⟨r, S.mon_mem hr⟩ hr⟩
    · exact ⟨(S.ψB v i g).2, hψ v i g⟩
  intro x hx
  apply mem_of_forall_sup_pow P x
  intro N
  obtain ⟨M, hM⟩ := hcl 0 (N + 1)
  have hxB : ∀ K : ℕ, ∃ y ∈ Algebra.adjoin O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = ((S.ρ.ψ v i g : S.Rˣ) : S.R)}),
      (x : S.R) - y ∈ maximalIdeal S.R ^ K := x.2
  obtain ⟨y0, hy0, hxy⟩ := hxB M
  obtain ⟨hy0B, c, hc⟩ := hB0 hy0
  obtain ⟨z, hzdef⟩ : ∃ z : S.B, z = x - ⟨y0, hy0B⟩ := ⟨_, rfl⟩
  have hz : algebraMap S.B S.A z ∈ S.mB ^ (N + 1) • S.gr 0 := by
    refine hM _ ?_ ?_
    · rw [h0]
      exact Submodule.algebraMap_mem z
    · rw [hzdef]
      exact hxy
  rw [h0] at hz
  have key : ∀ a ∈ S.mB ^ (N + 1) • (1 : Submodule S.B S.A), ∃ w ∈ S.mB ^ (N + 1), a = algebraMap S.B S.A w := by
    intro a ha
    refine Submodule.smul_induction_on (p := fun a => ∃ w ∈ S.mB ^ (N + 1), a = algebraMap S.B S.A w) ha ?_ ?_
    · intro r hr t ht
      obtain ⟨s, rfl⟩ := Submodule.mem_one.1 ht
      exact ⟨r * s, Ideal.mul_mem_right _ _ hr, by rw [Algebra.smul_def, map_mul]⟩
    · rintro a b ⟨w1, h1, rfl⟩ ⟨w2, h2, rfl⟩
      exact ⟨w1 + w2, add_mem h1 h2, (map_add _ _ _).symm⟩
  obtain ⟨w, hw, hzw⟩ := key _ hz
  have hzw' : z = w := hinj hzw
  have hzm : z ∈ S.mB := hzw' ▸ Ideal.pow_le_self (Nat.succ_ne_zero N) hw
  have hzN : z ∈ S.mB ^ N := hzw' ▸ Ideal.pow_le_pow_right (Nat.le_succ N) hw
  have hyB : (⟨y0, hy0B⟩ : S.B) ∈ S.mB := by
    have e : (⟨y0, hy0B⟩ : S.B) = x - z := by rw [hzdef, sub_sub_cancel]
    rw [e]
    exact S.mB.sub_mem hx hzm
  have hcB : algebraMap O S.B c ∈ S.mB := by
    have e : algebraMap O S.B c = ⟨y0, hy0B⟩ - (⟨y0, hy0B⟩ - algebraMap O S.B c) := (sub_sub_cancel _ _).symm
    rw [e]
    exact S.mB.sub_mem hyB (hPm hc)
  have hcO : c ∈ maximalIdeal O := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h1 : ((algebraMap O S.B c : S.B) : S.R) ∈ maximalIdeal S.R := hcB
    have h2 : IsUnit ((algebraMap O S.B c : S.B) : S.R) := hu.map (algebraMap O S.R)
    exact ((IsLocalRing.mem_maximalIdeal _).1 h1) h2
  have hyP : (⟨y0, hy0B⟩ : S.B) ∈ P := by
    have e : (⟨y0, hy0B⟩ : S.B) = (⟨y0, hy0B⟩ - algebraMap O S.B c) + algebraMap O S.B c := (sub_add_cancel _ _).symm
    rw [e]
    exact P.add_mem hc (hO (Ideal.mem_map_of_mem _ hcO))
  refine ⟨⟨y0, hy0B⟩, hyP, ?_⟩
  rw [hmax, ← hzdef]
  exact hzN
