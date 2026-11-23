import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSatMOfSmul

noncomputable section

namespace GlobalTheory.NL.SatPhiSpan

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.Coker

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem isUnit_Q : IsUnit (algebraMap (LetA O n) W.EE W.Q) := by
  have hq : IsUnit (algebraMap (LetA O n) W.EE W.q) := by
    have h1 : (letπ : LetA O n) * W.q = (1 + letπ) ^ PD.p - 1 := by
      funext i
      simpa [letπ, LocWach.q] using W.q₀_def
    set x := algebraMap (LetA O n) W.EE letπ with hx
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq PD.hp (1 : W.EE) x
    obtain ⟨u, hu⟩ : IsUnit (x ^ PD.p) := W.EE_π.pow _
    have := W.EE_complete
    have hj : ((PD.p : ℕ) : W.EE) ∈ Ideal.jacobson (⊥ : Ideal W.EE) :=
      IsAdicComplete.le_jacobson_bot (Ideal.span {((PD.p : ℕ) : W.EE)})
        (Ideal.mem_span_singleton_self _)
    have h2 := (Ideal.mem_jacobson_bot.1 hj) (x * r * (↑u⁻¹ : W.EE))
    have h3 : x * algebraMap (LetA O n) W.EE W.q =
        (((PD.p : ℕ) : W.EE) * (x * r * (↑u⁻¹ : W.EE)) + 1) * u := by
      rw [hx, ← map_mul, h1, map_sub, map_pow, map_add, map_one, ← hx, hr, ← hu]
      have := u.inv_mul
      linear_combination (-((PD.p : ℕ) : W.EE) * x * r) * this
    exact isUnit_of_mul_isUnit_right (h3 ▸ h2.mul u.isUnit)
  have key : ∀ k : ℕ, IsUnit (algebraMap (LetA O n) W.EE ((W.φA ^ k) W.q)) := by
    intro k
    induction k with
    | zero => simpa using hq
    | succ k ih =>
      rw [pow_succ', AlgHom.mul_apply]
      have := W.φE_ext ((W.φA ^ k) W.q)
      exact this ▸ ih.map W.φE
  exact key _

variable {W}

def basisS {T : LocLat G Qp LL O} {S : Submodule (LetA O n) (W.DD T)} {r : ℕ}
    {b : Fin r → W.DD T} (hbS : ∀ j, b j ∈ S)
    (hu : ∀ x ∈ S, ∃! a : Fin r → LetA O n, x = ∑ j, a j • b j) :
    Module.Basis (Fin r) (LetA O n) S :=
  Module.Basis.mk (v := fun j => (⟨b j, hbS j⟩ : S))
    (by
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      have h0 : (0 : W.DD T) = ∑ j, g j • b j := by
        have := congrArg Subtype.val hg
        simpa [Submodule.coe_sum] using this.symm
      obtain ⟨a, -, ha⟩ := hu 0 S.zero_mem
      have e1 := ha g h0
      have e2 := ha 0 (by simp)
      exact congrFun (e1.trans e2.symm) i)
    (by
      rintro ⟨x, hx⟩ -
      obtain ⟨a, ha, -⟩ := hu x hx
      have : (⟨x, hx⟩ : S) = ∑ j, a j • (⟨b j, hbS j⟩ : S) := by
        apply Subtype.ext
        simp only [Submodule.coe_sum, Submodule.coe_smul]
        exact ha
      rw [this]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))

def basisDD {T : LocLat G Qp LL O} {S : Submodule (LetA O n) (W.DD T)} {r : ℕ}
    {b : Fin r → W.DD T} (hbS : ∀ j, b j ∈ S)
    (hu : ∀ x ∈ S, ∃! a : Fin r → LetA O n, x = ∑ j, a j • b j)
    (hS : IsBaseChange W.EE S.subtype) : Module.Basis (Fin r) W.EE (W.DD T) :=
  (Algebra.TensorProduct.basis W.EE (basisS hbS hu)).map hS.equiv

theorem basisDD_apply {T : LocLat G Qp LL O} {S : Submodule (LetA O n) (W.DD T)} {r : ℕ}
    {b : Fin r → W.DD T} (hbS : ∀ j, b j ∈ S)
    (hu : ∀ x ∈ S, ∃! a : Fin r → LetA O n, x = ∑ j, a j • b j)
    (hS : IsBaseChange W.EE S.subtype) (j : Fin r) : basisDD hbS hu hS j = b j := by
  simp [basisDD, Algebra.TensorProduct.basis_apply, IsBaseChange.equiv_tmul, basisS,
    Module.Basis.mk_apply]

theorem phi_mem_span {T : LocLat G Qp LL O} {r : ℕ} (β : Module.Basis (Fin r) W.EE (W.DD T))
    (x : W.DD T) : W.φD T x ∈ Submodule.span W.EE (Set.range fun i => W.φD T (β i)) := by
  rw [← β.sum_repr x, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [W.φD_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem span_phi_eq_top {T : LocLat G Qp LL O} {r : ℕ} (β : Module.Basis (Fin r) W.EE (W.DD T))
    (hβ : ∀ j, ∃ m : ℕ, W.Q ^ m • β j ∈ Submodule.span (LetA O n) (Set.range (W.φD T))) :
    Submodule.span W.EE (Set.range fun i => W.φD T (β i)) = ⊤ := by
  set P := Submodule.span W.EE (Set.range fun i => W.φD T (β i)) with hP
  have hrange : Submodule.span (LetA O n) (Set.range (W.φD T)) ≤ P.restrictScalars (LetA O n) := by
    rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact phi_mem_span β x
  rw [eq_top_iff, ← β.span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  obtain ⟨m, hm⟩ := hβ j
  have h1 : algebraMap (LetA O n) W.EE (W.Q ^ m) • β j ∈ P := by
    rw [algebraMap_smul]; exact hrange hm
  obtain ⟨u, hu⟩ := (isUnit_Q W).pow m
  rw [map_pow, ← hu] at h1
  have := P.smul_mem ((u⁻¹ : W.EEˣ) : W.EE) h1
  rwa [smul_smul, Units.inv_mul, one_smul] at this

theorem phi_injective {T : LocLat G Qp LL O} {r : ℕ} (β : Module.Basis (Fin r) W.EE (W.DD T))
    (htop : Submodule.span W.EE (Set.range fun i => W.φD T (β i)) = ⊤) :
    Function.Injective (Fintype.linearCombination W.EE (fun i => W.φD T (β i))) := by
  haveI : Module.Finite W.EE (W.DD T) := Module.Finite.of_basis β
  refine OrzechProperty.injective_of_surjective_of_injective β.equivFun.symm.toLinearMap _
    β.equivFun.symm.injective ?_
  intro z
  have hz : z ∈ Submodule.span W.EE (Set.range fun i => W.φD T (β i)) := htop ▸ Submodule.mem_top
  obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun W.EE).1 hz
  exact ⟨e, by rw [Fintype.linearCombination_apply]; exact he⟩

theorem mem_span_of_smul_mem {T : LocLat G Qp LL O}
    (htf : ∀ (k : ℕ) (a : LetA O n), ((PD.p : ℕ) : LetA O n) ^ k * a = 0 → a = 0)
    {r : ℕ} (c : Fin r → W.DD T)
    (hsurj : ∀ z : W.DD T, ∃ e : Fin r → W.EE, ∑ j, e j • c j = z)
    (hinj : Function.Injective (Fintype.linearCombination W.EE c))
    (z : W.DD T) (k : ℕ)
    (h1 : ((PD.p : ℕ) : LetA O n) ^ k • z ∈ Submodule.span (LetA O n) (Set.range c))
    (h2 : (letπ : LetA O n) ^ k • z ∈ Submodule.span (LetA O n) (Set.range c)) :
    z ∈ Submodule.span (LetA O n) (Set.range c) := by
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (LetA O n)).1 h1
  obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun (LetA O n)).1 h2
  obtain ⟨e, he⟩ := hsurj z
  have coord : ∀ (t : LetA O n) (f : Fin r → LetA O n), ∑ j, f j • c j = t • z →
      ∀ j, algebraMap (LetA O n) W.EE (f j) = algebraMap (LetA O n) W.EE t * e j := by
    intro t f hf
    have : (fun j => algebraMap (LetA O n) W.EE (f j)) =
        (fun j => algebraMap (LetA O n) W.EE t * e j) := by
      apply hinj
      simp only [Fintype.linearCombination_apply, algebraMap_smul]
      rw [hf, ← he, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← algebraMap_smul W.EE t, smul_smul]
    exact fun j => congrFun this j
  have ca := coord _ a ha
  have cb := coord _ b hb
  have ha' : ∀ j, ∃ a' : LetA O n, a j = ((PD.p : ℕ) : LetA O n) ^ k * a' := by
    intro j
    apply W.EE_sat
    rw [ca j, map_pow, map_natCast, Ideal.mem_span_singleton]
    exact Dvd.intro _ rfl
  choose a' ha' using ha'
  have hbj : ∀ j, b j = letπ ^ k * a' j := by
    intro j
    have e1 : algebraMap (LetA O n) W.EE (((PD.p : ℕ) : LetA O n) ^ k * b j) =
        algebraMap (LetA O n) W.EE (((PD.p : ℕ) : LetA O n) ^ k * (letπ ^ k * a' j)) := by
      rw [map_mul, cb j, ← mul_assoc, mul_comm (algebraMap _ _ (((PD.p : ℕ) : LetA O n) ^ k)),
        mul_assoc, ← ca j, ha' j]
      simp only [map_mul, map_pow]
      ring
    have e2 := W.EE_inj e1
    have e3 : ((PD.p : ℕ) : LetA O n) ^ k * (b j - letπ ^ k * a' j) = 0 := by
      rw [mul_sub, e2, sub_self]
    exact sub_eq_zero.1 (htf k _ e3)
  have hej : ∀ j, e j = algebraMap (LetA O n) W.EE (a' j) := by
    intro j
    have e1 := cb j
    rw [hbj j, map_mul] at e1
    have hu : IsUnit (algebraMap (LetA O n) W.EE (letπ ^ k)) := by
      rw [map_pow]; exact W.EE_π.pow k
    exact ((hu.mul_right_inj).1 e1).symm
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨a', ?_⟩
  rw [← he]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hej j, algebraMap_smul]

theorem φD_smulA {T : LocLat G Qp LL O} (a : LetA O n) (x : W.DD T) :
    W.φD T (a • x) = W.φA a • W.φD T x := by
  have := W.φD_smul T (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.φE_ext, algebraMap_smul] at this
  exact this

theorem Qpow_mem_of_mem_image {T₁ T₂ : LocLat G Qp LL O} (π : LatHom T₁.L T₂.L)
    {S : Submodule (LetA O n) (W.DD T₂)} (hS : (W.N T₁).map (mapA W π) ≤ S)
    {w : W.DD T₂} (hw : w ∈ (W.N T₁).map (mapA W π)) : ∃ j : ℕ, W.Q ^ j • w ∈ φspan W T₂ S := by
  obtain ⟨x, hx, rfl⟩ := hw
  obtain ⟨j, hj⟩ := W.N_φinv T₁ x hx
  refine ⟨j, ?_⟩
  have hle : (Submodule.span (LetA O n) (W.φD T₁ '' (W.N T₁ : Set (W.DD T₁)))).map (mapA W π) ≤
      φspan W T₂ S := by
    rw [Submodule.map_span_le]
    rintro _ ⟨z, hz, rfl⟩
    apply Submodule.subset_span
    exact ⟨mapA W π z, hS ⟨z, hz, rfl⟩, (W.map_φ π z).symm⟩
  have := hle ⟨_, hj, rfl⟩
  rw [map_smul] at this
  exact this

theorem Qpow_mem_φspan_satM {T₁ T₂ : LocLat G Qp LL O} (l : ℕ) (hpl : PD.p = l)
    (htf : ∀ (k : ℕ) (a : LetA O n), ((PD.p : ℕ) : LetA O n) ^ k * a = 0 → a = 0)
    (π : LatHom T₁.L T₂.L) (hc₁ : IsCrys PD T₁.ρ) (hc₂ : IsCrys PD T₂.ρ)
    (hfree : FreeA W T₂ (satM l ((W.N T₁).map (mapA W π)) (W.N T₂)))
    (hbc : IsBaseChange W.EE (satM l ((W.N T₁).map (mapA W π)) (W.N T₂)).subtype) :
    ∀ y ∈ satM l ((W.N T₁).map (mapA W π)) (W.N T₂), ∃ k : ℕ,
      W.Q ^ k • y ∈ φspan W T₂ (satM l ((W.N T₁).map (mapA W π)) (W.N T₂)) := by
  subst hpl
  have hN2 : (W.N T₁).map (mapA W π) ≤ W.N T₂ := by
    rintro _ ⟨x, hx, rfl⟩
    exact W.map_N π hc₁ hc₂ x hx
  have hS : (W.N T₁).map (mapA W π) ≤ satM PD.p ((W.N T₁).map (mapA W π)) (W.N T₂) :=
    le_satM PD.p hN2
  obtain ⟨r, b, hbS, hu⟩ := hfree
  have hβb : ∀ j, basisDD hbS hu hbc j = b j := basisDD_apply hbS hu hbc
  have hβ : ∀ j, ∃ m : ℕ, W.Q ^ m • basisDD hbS hu hbc j ∈
      Submodule.span (LetA O n) (Set.range (W.φD T₂)) := by
    intro j
    obtain ⟨m, hm⟩ := W.N_φinv T₂ (basisDD hbS hu hbc j)
      (by rw [hβb]; exact satM_le _ _ _ (hbS j))
    exact ⟨m, Submodule.span_mono (Set.image_subset_range _ _) hm⟩
  have htop := span_phi_eq_top (basisDD hbS hu hbc) hβ
  have hinj := phi_injective (basisDD hbS hu hbc) htop
  set c : Fin r → W.DD T₂ := fun j => W.φD T₂ (basisDD hbS hu hbc j) with hc
  have hsurj : ∀ z : W.DD T₂, ∃ e : Fin r → W.EE, ∑ j, e j • c j = z := fun z =>
    (Submodule.mem_span_range_iff_exists_fun W.EE).1 (htop ▸ Submodule.mem_top)
  have hcb : ∀ j, c j = W.φD T₂ (b j) := fun j => by simp only [hc, hβb]
  have hRc : φspan W T₂ (satM PD.p ((W.N T₁).map (mapA W π)) (W.N T₂)) =
      Submodule.span (LetA O n) (Set.range c) := by
    apply le_antisymm
    · rw [φspan, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨a, ha, -⟩ := hu x hx
      rw [ha, map_sum]
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [φD_smulA]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hcb j⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      rw [hcb]
      exact Submodule.subset_span ⟨b j, hbS j, rfl⟩
  intro y hy
  obtain ⟨-, k, hk1, hk2⟩ := hy
  obtain ⟨j₁, hj₁⟩ := Qpow_mem_of_mem_image π hS hk1
  obtain ⟨j₂, hj₂⟩ := Qpow_mem_of_mem_image π hS hk2
  refine ⟨j₁ + j₂, ?_⟩
  rw [hRc] at hj₁ hj₂ ⊢
  apply mem_span_of_smul_mem htf c hsurj hinj _ k
  · have e : ((PD.p : ℕ) : LetA O n) ^ k • W.Q ^ (j₁ + j₂) • y =
        W.Q ^ j₂ • W.Q ^ j₁ • ((PD.p : ℕ) : LetA O n) ^ k • y := by
      simp only [smul_smul]; congr 1; ring
    rw [e]
    exact Submodule.smul_mem _ _ hj₁
  · have e : (letπ : LetA O n) ^ k • W.Q ^ (j₁ + j₂) • y =
        W.Q ^ j₁ • W.Q ^ j₂ • (letπ : LetA O n) ^ k • y := by
      simp only [smul_smul]; congr 1; ring
    rw [e]
    exact Submodule.smul_mem _ _ hj₂

end Generic

theorem natCast_pow_mul_eq_zero {l : ℕ} [Fact l.Prime] {LL : FinExt l} {n : ℕ} (k : ℕ)
    (a : LetA ↥(OL LL) n) (h : ((l : ℕ) : LetA ↥(OL LL) n) ^ k * a = 0) : a = 0 := by
  funext i
  have hi := congrFun h i
  simp only [Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply, Pi.zero_apply] at hi
  have hl : ((l : ℕ) : PowerSeries ↥(OL LL)) ≠ 0 := by
    intro h0
    have h1 : ((l : ℕ) : ↥(OL LL)) = 0 := by
      have := congrArg PowerSeries.constantCoeff h0
      simpa using this
    have h2 : ((l : ℕ) : ↥LL.1) = 0 := by
      have := congrArg (fun x : ↥(OL LL) => (x : ↥LL.1)) h1
      simpa using this
    have h3 : ((l : ℕ) : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
    apply h3
    have : algebraMap ℚ_[l] ↥LL.1 (l : ℚ_[l]) = 0 := by rw [map_natCast]; exact h2
    exact (algebraMap ℚ_[l] ↥LL.1).injective (this.trans (map_zero _).symm)
  exact (mul_eq_zero.1 hi).resolve_left (pow_ne_zero _ hl)

theorem satM_Qpow_mem_φspan : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₁ T₂ : Lt K LL) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → FreeA W T₂ (GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂)) → IsBaseChange W.EE (GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂)).subtype → ∀ y ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂), ∃ k : ℕ, W.Q ^ k • y ∈ φspan W T₂ (GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂)) := by
  intro D HW F l _ K s LL h W T₁ T₂ π hc₁ hc₂ hfree hbc
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  refine Qpow_mem_φspan_satM (W := W) l hp ?_ π hc₁ hc₂ hfree hbc
  intro k a ha
  rw [hp] at ha
  exact natCast_pow_mul_eq_zero k a ha

end GlobalTheory.NL.SatPhiSpan
