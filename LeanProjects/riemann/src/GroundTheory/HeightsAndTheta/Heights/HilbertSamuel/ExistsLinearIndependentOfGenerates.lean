import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNefFibresAmple
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNefAmpleFibre
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLiftModel
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothMetricOfIsSmoothHerm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

theorem isProjVarF_map_of_isArithVar {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {D : ℕ} (hP : IsArithVar P (D + 1)) :
    IsProjVarF (P.map (MvPolynomial.map (Int.castRingHom ℚ))) D := by
  classical
  have h := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.isProjVarQ_of_isArithVar hP
  exact ⟨(GroundTheory.Heights₂.Heights.NumbersDVR.Objects.isMultiProjPrime_iff _).mp h.1, h.2⟩

section Basis

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

theorem isMultiHomog_aeval_linear {κ κ' : Type} [Fintype κ] [Fintype κ'] (c : κ → κ' → ℤ)
    {g : MRing (fun _ : Unit => κ)} {d : Unit → ℕ} (hg : IsMultiHomog g d) :
    IsMultiHomog (aeval (fun p : Σ _ : Unit, κ => ∑ i, C (c p.2 i) * X (⟨(), i⟩ : Σ _ : Unit, κ')) g) d := by
  have hdeg : ∀ {τ : Type} [Fintype τ] (m : (Σ _ : Unit, τ) →₀ ℕ), m.degree = ∑ i, m ⟨(), i⟩ := by
    intro τ _ m
    classical
    rw [Finsupp.degree_apply, Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => by
      simpa using hx), Fintype.sum_sigma, Fintype.sum_unique]
  have hw : ∀ {τ : Type} (m : τ →₀ ℕ), Finsupp.weight 1 m = m.degree := by
    intro τ m
    rw [Finsupp.degree_eq_weight_one]
    rfl
  have hH : g.IsHomogeneous (d ()) := by
    intro m hm
    rw [hw, hdeg]
    exact hg m (mem_support_iff.mpr hm) ()
  have hL : ∀ p : Σ _ : Unit, κ,
      (∑ i, C (c p.2 i) * X (⟨(), i⟩ : Σ _ : Unit, κ') : MRing (fun _ : Unit => κ')).IsHomogeneous 1 :=
    fun p => IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_C_mul_X _ _
  have h := hH.aeval _ hL
  rw [one_mul] at h
  intro m hm k
  have := h (mem_support_iff.mp hm)
  rw [hw, hdeg] at this
  exact this

omit [∀ k, Fintype (ι k)] in

theorem exists_linearIndependent_of_generates (y : (Σ k, ι k) → Ω) (n : K → ℤ) {ι' : Type} [Fintype ι']
    (x' : ι' → Ω) (hmem : ∀ j, x' j ∈ chartLat y n 1) (hgen : KH.GeneratesOn y n x')
    (hbir : Birational (fun p : Σ _ : Unit, ι' => x' p.2)) :
    ∃ (ι'' : Type) (_ : Fintype ι'') (x'' : ι'' → Ω), (∀ j, x'' j ∈ chartLat y n 1) ∧
      LinearIndependent ℤ x'' ∧ KH.GeneratesOn y n x'' ∧ Birational (fun p : Σ _ : Unit, ι'' => x'' p.2) := by
  classical
  let L : Submodule ℤ Ω := Submodule.span ℤ (Set.range x')
  have : Module.Finite ℤ L := Module.Finite.span_of_finite ℤ (Set.finite_range x')
  let b := Module.Free.chooseBasis ℤ L
  let x'' : Module.Free.ChooseBasisIndex ℤ L → Ω := fun i => (b i : Ω)
  have hL : L ≤ (chartLat y n 1).toIntSubmodule :=
    Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hmem j)
  let cf : ι' → Module.Free.ChooseBasisIndex ℤ L → ℤ :=
    fun j => b.repr ⟨x' j, Submodule.subset_span ⟨j, rfl⟩⟩
  have hexp : ∀ j, x' j = ∑ i, (cf j i : Ω) * x'' i := by
    intro j
    have h := congrArg Subtype.val (b.sum_repr ⟨x' j, Submodule.subset_span ⟨j, rfl⟩⟩)
    rw [Submodule.coe_sum] at h
    refine h.symm.trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [Submodule.coe_smul, zsmul_eq_mul]
  refine ⟨_, inferInstance, x'', fun i => hL (b i).2, b.linearIndependent.map' L.subtype L.ker_subtype,
    fun c hc => ?_, fun s => ?_⟩
  · obtain ⟨u, hu, hsum⟩ := hgen c hc
    refine ⟨fun i => ∑ j, (cf j i : Ω) * u j, fun i => ?_, ?_⟩
    · exact Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ _) (hu j)
    · rw [← hsum]
      calc ∑ i, (∑ j, (cf j i : Ω) * u j) * (x'' i * ∏ k, y ⟨k, c k⟩ ^ (-n k))
          = ∑ j, u j * ((∑ i, (cf j i : Ω) * x'' i) * ∏ k, y ⟨k, c k⟩ ^ (-n k)) := by
            simp only [Finset.sum_mul, Finset.mul_sum]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
        _ = ∑ j, u j * (x' j * ∏ k, y ⟨k, c k⟩ ^ (-n k)) :=
            Finset.sum_congr rfl fun j _ => by rw [← hexp j]
  · obtain ⟨d, g, h, hg, hh, hh0, hgh⟩ := hbir s
    let σ : MRing (fun _ : Unit => ι') →ₐ[ℤ] MRing (fun _ : Unit => Module.Free.ChooseBasisIndex ℤ L) :=
      aeval fun p => ∑ i, C (cf p.2 i) * X ⟨(), i⟩
    have hev : ∀ f, aeval (fun p : Σ _ : Unit, Module.Free.ChooseBasisIndex ℤ L => x'' p.2) (σ f) =
        aeval (fun p : Σ _ : Unit, ι' => x' p.2) f := by
      intro f
      rw [← AlgHom.comp_apply, comp_aeval]
      congr 2
      funext p
      simp [hexp p.2]
    refine ⟨d, σ g, σ h, isMultiHomog_aeval_linear cf hg, isMultiHomog_aeval_linear cf hh, ?_, ?_⟩
    · rw [hev]; exact hh0
    · rw [hev, hev]; exact hgh

end Basis

theorem Lift.proof (hKA : KH.KAmpStatement) (hNF : NefAmpleFibre.Statement) (hLM : LiftModel.Statement) :
    Lift.Statement := by
  intro K _ ι _ Ω _ _ y D α t I hI hV hbir ht hnef hnefQ
  classical
  let _ : LinearOrder K := LinearOrder.lift' _ (Fintype.equivFin K).injective
  let _ : ∀ k, LinearOrder (ι k) := fun k => LinearOrder.lift' _ (Fintype.equivFin (ι k)).injective
  have hnum : 0 < t.num := Rat.num_pos.mpr ht
  set p : ℕ := t.num.toNat with hp_def
  set q : ℕ := t.den with hq_def
  have hp : 1 ≤ p := by omega
  have hq : 1 ≤ q := t.den_pos
  have hpn : ((p : ℤ) : ℚ) = t.num := by
    rw [hp_def, Int.toNat_of_nonneg hnum.le]
  have htq : t = (p : ℚ) / q := by
    rw [hq_def, ← Int.cast_natCast, hpn]
    exact (Rat.num_div_den t).symm
  have hGen := hKA ℚ K ι I (KH.genIdeal y) D α q p hI (isProjVarF_map_of_isArithVar hV) hnefQ hq hp
  have hFib : ∀ ℓ : ℕ, ℓ.Prime → KH.AmpleV (ZMod ℓ) (fibreIdeal ℓ y) (q • α + fun _ => (p : ℤ)) := by
    intro ℓ hℓ
    have h := hNF K ι Ω y D α q p ℓ hV hnef hq hp hℓ
    rwa [natCast_zsmul] at h
  have hGen2 := hKA ℚ K ι I (KH.genIdeal y) D α (2 * q) (2 * p - 1) hI (isProjVarF_map_of_isArithVar hV) hnefQ
    (by omega) (by omega)
  have hExtra : ∃ c : ℕ, 1 ≤ c ∧
      KH.AmpleV ℚ (KH.genIdeal y) (c • (q • α + fun _ => (p : ℤ)) - fun _ => 1) := by
    refine ⟨2, by norm_num, ?_⟩
    have he : (2 • (q • α + fun _ => (p : ℤ)) - fun _ => (1 : ℤ) : K → ℤ) =
        (2 * q) • α + fun _ => ((2 * p - 1 : ℕ) : ℤ) := by
      funext k
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
      simp only [nsmul_eq_mul]
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [he]
    exact hGen2
  obtain ⟨a, ι', _, x', ha, hmem, hgen, hbir'⟩ := hLM K ι Ω y D _ hV hbir hGen hExtra hFib
  obtain ⟨ι'', _, x'', hmem'', hli, hgen'', hbir''⟩ :=
    exists_linearIndependent_of_generates y _ x' hmem hgen hbir'
  refine ⟨a * q, _, ι'', inferInstance, x'', Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)),
    fun k => ?_, hmem'', hli, hgen'', hbir''⟩
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  simp only [Pi.smul_apply, Pi.add_apply, nsmul_eq_mul, Int.cast_mul, Int.cast_add,
    Int.cast_natCast, Nat.cast_mul, htq]
  field_simp
  simp only [Pi.mul_apply, Pi.natCast_apply]
  push_cast
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
