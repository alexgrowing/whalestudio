import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsDual
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsEasy
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.LevelSubgroupFiniteAdelicStandard

noncomputable section

namespace GlobalTheory.NormSum.AdLattice

open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

def lat (g : GL n 𝒜) : Submodule (𝓞 E) (n → E) :=
  Formalism.UG.CS.globLat g (stdLat (n := n) (A := E) (𝓞 E))

theorem mem_latS_std (v : n → 𝒜) :
    v ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 (stdLat (n := n) (A := E) (𝓞 E)) ↔ ∀ i, v i ∈ 𝒮 := by
  rw [easyc_latS_std, adelstab_mem_stdLat]

theorem mem_lat (g : GL n 𝒜) (x : n → E) :
    x ∈ lat g ↔ ∀ i, (((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (fun j => ι (x j))) i ∈ 𝒮 :=
  mem_latS_std _

theorem lat_isLattice (g : GL n 𝒜) : Submodule.IsLattice E (lat g) :=
  global_lattice_isLattice_holds F E n _ (standard_lattice_full_holds E n).1 (standard_lattice_full_holds E n).2 g

theorem lat_span (g : GL n 𝒜) (u : n → 𝒜) :
    u ∈ Submodule.span 𝒮 ((fun x : n → E => fun i => ι (x i)) '' (lat g : Set (n → E))) ↔
      ∀ i, (((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ u) i ∈ 𝒮 :=
  (span_recovery_of_integral_adelic_approx csGlob_intAdApprox F E n _ (standard_lattice_full_holds E n).1 (standard_lattice_full_holds E n).2
    g u).trans (mem_latS_std _)

theorem incl_mem_iff (e : E) : ι e ∈ 𝒮 ↔ e ∈ (algebraMap (𝓞 E) E).range := by
  constructor
  · intro h
    exact ⟨⟨e, csGlob_int (F := F) e h⟩, rfl⟩
  · rintro ⟨b, rfl⟩
    exact adelstab_incl_int b

theorem mulVec_int {M : Matrix n n 𝒜} (hM : ∀ i j, M i j ∈ 𝒮) {v : n → 𝒜} (hv : ∀ i, v i ∈ 𝒮) (i : n) :
    (M *ᵥ v) i ∈ 𝒮 := by
  simp only [mulVec, dotProduct]
  exact sum_mem fun j _ => mul_mem (hM i j) (hv j)

theorem lat_le_of_int {g g' : GL n 𝒜} (h : ∀ i j, ((g'⁻¹ * g : GL n 𝒜) : Matrix n n 𝒜) i j ∈ 𝒮) :
    lat g ≤ lat g' := by
  intro x hx
  rw [mem_lat] at hx ⊢
  intro i
  have := mulVec_int h hx i
  rwa [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel_right] at this

theorem int_of_lat_le {g g' : GL n 𝒜} (h : lat g ≤ lat g') (i j : n) :
    ((g'⁻¹ * g : GL n 𝒜) : Matrix n n 𝒜) i j ∈ 𝒮 := by
  have h1 := (lat_span g ((g : Matrix n n 𝒜) *ᵥ Pi.single j 1)).2 (by
    intro k
    rw [mulVec_mulVec, Units.inv_mul, one_mulVec, Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _)
  have h2 := (lat_span g' _).1 (Submodule.span_mono (Set.image_mono h) h1) i
  rwa [mulVec_mulVec, ← Units.val_mul, mulVec_single_one] at h2

theorem map_one_incl : (1 : Matrix n n E).map ι = 1 := Matrix.map_one _ (map_zero _) (map_one _)

theorem hform_one {A : Type} [CommRing A] (σ : A →+* A) (x y : n → A) :
    hform σ (1 : Matrix n n A) x y = ∑ i, σ (x i) * y i := by
  rw [hform_eq_dot, one_mulVec]; rfl

theorem lat_selfDual (σ : E →ₐ[F] E) (g : GL n 𝒜)
    (hg : g ∈ UPts σ (1 : Matrix n n E) (FiniteAdeleRing (𝓞 F) F)) (y : n → E) :
    y ∈ lat g ↔ ∀ x ∈ lat g, ∑ i, σ (x i) * y i ∈ (algebraMap (𝓞 E) E).range := by
  have hU : cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (g : Matrix n n 𝒜) * (1 : Matrix n n E).map ι *
      (g : Matrix n n 𝒜) = (1 : Matrix n n E).map ι := hg
  have hback : ∀ v : n → 𝒜, (g : Matrix n n 𝒜) *ᵥ (((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ v) = v := by
    intro v; rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
  constructor
  · intro hy x hx
    rw [mem_lat] at hx hy
    have h1 := csDual_hform_incl σ (1 : Matrix n n E) x y
    rw [← hback (fun i => ι (x i)), ← hback (fun i => ι (y i)), hform_mulVec, hU, map_one_incl,
      hform_one, hform_one] at h1
    rw [← incl_mem_iff (F := F)]
    have h2 : ι (∑ i, σ (x i) * y i) = _ := h1.symm
    rw [h2]
    exact sum_mem fun i _ => mul_mem (csDual_sig_mem σ (hx i)) (hy i)
  · intro hy
    rw [mem_lat]
    intro j
    have h1 := (lat_span g ((g : Matrix n n 𝒜) *ᵥ Pi.single j 1)).2 (by
      intro k
      rw [mulVec_mulVec, Units.inv_mul, one_mulVec, Pi.single_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _)
    have h2 := csDual_span σ (1 : Matrix n n E) (lat g) y
      (fun x hx => by rw [hform_one]; exact hy x hx) _ h1
    rwa [← hback (fun i => ι (y i)), hform_mulVec, hU, map_one_incl, sf_single, one_mulVec] at h2

theorem mem_lat_one (x : n → E) :
    x ∈ lat (1 : GL n 𝒜) ↔ ∀ i, x i ∈ (algebraMap (𝓞 E) E).range := by
  rw [mem_lat, inv_one, Units.val_one, one_mulVec]
  exact forall_congr' fun i => incl_mem_iff _

theorem mem_lat_rat (γA g : GL n 𝒜) (γ : Matrix n n E) (h : (γA : Matrix n n 𝒜) = γ.map ι)
    (x : n → E) : x ∈ lat g ↔ γ *ᵥ x ∈ lat (γA * g) := by
  have key : (fun i => ι ((γ *ᵥ x) i)) = (γA : Matrix n n 𝒜) *ᵥ (fun i => ι (x i)) := by
    ext i; rw [RingHom.map_mulVec, h]; rfl
  rw [mem_lat, mem_lat, key, mulVec_mulVec, ← Units.val_mul, _root_.mul_inv_rev, inv_mul_cancel_right]

theorem inv_entry (σ : E →ₐ[F] E) (g : GL n 𝒜)
    (hg : g ∈ UPts σ (1 : Matrix n n E) (FiniteAdeleRing (𝓞 F) F)) (i j : n) :
    ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) i j =
      sigR σ (FiniteAdeleRing (𝓞 F) F) ((g : Matrix n n 𝒜) j i) := by
  have hU : cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (g : Matrix n n 𝒜) * (1 : Matrix n n E).map ι *
      (g : Matrix n n 𝒜) = (1 : Matrix n n E).map ι := hg
  rw [map_one_incl, Matrix.mul_one] at hU
  have : ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) = cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (g : Matrix n n 𝒜) :=
    Units.inv_eq_of_mul_eq_one_left hU
  rw [this]; rfl

theorem smul_mem_lat {g g' : GL n 𝒜} (s : ℕ)
    (h : ∀ i j, (s : 𝒜) * ((g'⁻¹ * g : GL n 𝒜) : Matrix n n 𝒜) i j ∈ 𝒮) {x : n → E} (hx : x ∈ lat g) :
    (s : E) • x ∈ lat g' := by
  rw [mem_lat] at hx ⊢
  intro i
  have := mulVec_int (M := (s : 𝒜) • ((g'⁻¹ * g : GL n 𝒜) : Matrix n n 𝒜)) h hx i
  rw [smul_mulVec, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel_right, ← mulVec_smul] at this
  have e : (fun j => ι (((s : E) • x) j)) = (s : 𝒜) • fun j => ι (x j) := by
    funext j
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, map_natCast]
  rw [e]
  exact this

theorem eq_up_to (σ : E →ₐ[F] E) (g : GL n 𝒜)
    (hg : g ∈ UPts σ (1 : Matrix n n E) (FiniteAdeleRing (𝓞 F) F)) (p : ℕ)
    (h : ∀ i j, ∃ m : ℕ, Nat.Coprime m p ∧
      (m : 𝒜) * ((g : Matrix n n 𝒜) i j - (1 : Matrix n n 𝒜) i j) ∈ 𝒮) :
    ∃ s : ℕ, Nat.Coprime s p ∧ (∀ x ∈ lat (1 : GL n 𝒜), (s : E) • x ∈ lat g) ∧
      ∀ x ∈ lat g, (s : E) • x ∈ lat (1 : GL n 𝒜) := by
  choose m hm hmS using h
  set s : ℕ := ∏ q : n × n, m q.1 q.2 with hs
  have hint : ∀ i j, (s : 𝒜) * (g : Matrix n n 𝒜) i j ∈ 𝒮 := by
    intro i j
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun q : n × n => m q.1 q.2) (Finset.mem_univ (i, j))
    have h1 : (1 : Matrix n n 𝒜) i j ∈ 𝒮 := by
      rw [Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    have : (s : 𝒜) * (g : Matrix n n 𝒜) i j = (k : 𝒜) * ((m i j : 𝒜) *
        ((g : Matrix n n 𝒜) i j - (1 : Matrix n n 𝒜) i j)) + (s : 𝒜) * (1 : Matrix n n 𝒜) i j := by
      rw [hs, hk]; push_cast; ring
    rw [this]
    exact add_mem (mul_mem (natCast_mem _ k) (hmS i j)) (mul_mem (natCast_mem _ s) h1)
  refine ⟨s, Nat.Coprime.prod_left fun q _ => hm q.1 q.2, fun x hx => smul_mem_lat s ?_ hx,
    fun x hx => smul_mem_lat s ?_ hx⟩
  · intro i j
    rw [mul_one, inv_entry σ g hg]
    have := csDual_sig_mem σ (hint j i)
    rwa [map_mul, map_natCast] at this
  · intro i j
    rw [inv_one, one_mul]
    exact hint i j

end General

end GlobalTheory.NormSum.AdLattice

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum.AdLattice

theorem star_eq_conj (D : D7) (x : D.host.E) : (letI := D.host.cmStar; star x) = D.host.conj x := by
  apply D.host.φ₀.injective
  letI := D.host.isCMField_hostE
  show D.host.φ₀ (IsCMField.complexConj D.host.E x) = _
  rw [NumberField.IsCMField.complexEmbedding_complexConj, D.host.toHostAx.conjE_apply]

theorem intG_of_mem (D : D7) (N : ℕ) (k : GA D N) (hk : k ∈ intG D N) :
    IntG D (k : GL (Fin N) (AE D)) := by
  have hmul : ∀ M M' : Matrix (Fin N) (Fin N) (AE D), (∀ i j, M i j ∈ OhE D) → (∀ i j, M' i j ∈ OhE D) →
      ∀ i j, (M * M') i j ∈ OhE D := by
    intro M M' h h' i j
    rw [Matrix.mul_apply]
    exact sum_mem fun l _ => mul_mem (h i l) (h' l j)
  induction hk using Subgroup.closure_induction with
  | mem k hk => exact hk
  | one =>
    intro i j
    have h1 : (1 : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D := by
      rw [Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    rw [OneMemClass.coe_one, inv_one]
    exact ⟨h1, h1⟩
  | mul a b _ _ ha hb =>
    intro i j
    rw [Subgroup.coe_mul, mul_inv_rev, Units.val_mul, Units.val_mul]
    exact ⟨hmul _ _ (fun i j => (ha i j).1) (fun i j => (hb i j).1) i j,
      hmul _ _ (fun i j => (hb i j).2) (fun i j => (ha i j).2) i j⟩
  | inv a _ ha =>
    intro i j
    rw [Subgroup.coe_inv, inv_inv]
    exact ⟨(ha i j).2, (ha i j).1⟩

theorem lat_one_eq (D : D7) (N : ℕ) : lat (1 : GL (Fin N) (AE D)) = stdL D N := by
  ext x
  rw [mem_lat_one, stdL, Submodule.mem_pi]
  refine forall_congr' fun i => ?_
  simp only [Set.mem_univ, true_implies, Submodule.mem_one, RingHom.mem_range]

end GlobalTheory.NormSum.AdLattice

open GlobalTheory.NormSum.AdLattice in

theorem GlobalTheory.NormSum.exists_lattice_of_adelic_point : ∀ (D : D7) (N : ℕ), ∃ Lt : GA D N → Submodule (𝓞 D.host.E) (Fin N → D.host.E), (∀ g : GA D N, Moves D (g : GL (Fin N) (AE D)) (Lt g) ∧ SD D (Lt g)) ∧ Lt 1 = stdL D N ∧ (∀ g g' : GA D N, Lt g = Lt g' ↔ g⁻¹ * g' ∈ intG D N) ∧ (∀ (γA g : GA D N) γ, IsRat D (γA : GL (Fin N) (AE D)) γ → ∀ x, x ∈ Lt g ↔ γ.mulVec x ∈ Lt (γA * g)) ∧ (∀ (p : ℕ) (g : GA D N), p.Prime → TrivAt D p (g : GL (Fin N) (AE D)) → EqAt D p (stdL D N) (Lt g)) := by
  intro D N
  refine ⟨fun g => lat (g : GL (Fin N) (AE D)), fun g => ⟨fun x => mem_lat _ x, ?_⟩, lat_one_eq D N,
    fun g g' => ⟨fun h => ?_, fun h => ?_⟩, fun γA g γ h x => mem_lat_rat _ _ γ h x, fun p g _ h => ?_⟩
  · refine ⟨(lat_isLattice _).fg, (lat_isLattice _).span_eq_top, fun y => ?_⟩
    rw [lat_selfDual (D.host.conj : D.host.E →ₐ[ℚ] D.host.E) _ g.2 y]
    refine forall₂_congr fun x _ => ?_
    simp only [stdH, star_eq_conj]
    rfl
  · refine Subgroup.subset_closure fun i j => ?_
    rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv]
    exact ⟨int_of_lat_le h.ge i j, int_of_lat_le h.le i j⟩
  · have hk := intG_of_mem D N _ h
    rw [IntG, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv] at hk
    exact le_antisymm (lat_le_of_int fun i j => (hk i j).2) (lat_le_of_int fun i j => (hk i j).1)
  · rw [← lat_one_eq]
    refine eq_up_to (D.host.conj : D.host.E →ₐ[ℚ] D.host.E) _ g.2 p fun i j => ?_
    obtain ⟨m, -, hm, s, hs, he⟩ := h i j 0
    refine ⟨m, hm, ?_⟩
    rw [pow_zero, one_mul] at he
    rw [he]
    exact hs
