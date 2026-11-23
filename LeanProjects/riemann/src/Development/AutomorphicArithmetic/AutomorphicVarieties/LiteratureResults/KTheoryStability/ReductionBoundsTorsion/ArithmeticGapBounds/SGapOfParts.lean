import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.PGlueG
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.PGlueM
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.PGlueK

noncomputable section

open NumberField Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.SpectralGap

namespace Glue

open GlueG GlueM GlueK

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

theorem emb_eq (γ : Gm L N) : emb L N γ = toP L N (toK L N γ) := rfl

theorem hecke_eq (π : 𝓞 L) (hπ : π ≠ 0) (f : Gp L N → ℝ) (y : Gp L N) :
    hecke (toK L N) (toP L N) (qel L N π hπ) f y =
      ((Hq L N π hπ).index : ℝ)⁻¹ * ∑ᶠ c : Quotient (QuotientGroup.rightRel (Hq L N π hπ)),
        f (toP L N (qel L N π hπ * toK L N c.out) * y) := rfl

theorem coset_inv (π : 𝓞 L) (hπ : π ≠ 0) (f : Gp L N → ℝ) (hf : ∀ γ x, f (emb L N γ * x) = f x)
    (y : Gp L N) (h : Gm L N) (hh : h ∈ Hq L N π hπ) (γ : Gm L N) :
    f (toP L N (qel L N π hπ * toK L N (h * γ)) * y) = f (toP L N (qel L N π hπ * toK L N γ) * y) := by
  obtain ⟨k, ⟨γ', rfl⟩, hk⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hh)
  have e : qel L N π hπ * toK L N h = toK L N γ' * qel L N π hπ := by
    rw [← hk]
    simp [MulAut.conj_apply, mul_assoc]
  rw [(toK L N).map_mul h γ, ← mul_assoc, e, mul_assoc, (toP L N).map_mul, ← emb_eq, mul_assoc, hf]

end Glue

open Glue GlueG GlueM GlueK in
theorem _root_.PositivityTheory.KB.sGap_of_parts : GapAbs → Unfold → Arith → Dens → SGap := by
  intro hGap _ hAr hDe L _ _ hTC π hπp h25 N hN d f hf
  have hπ : π ≠ 0 := hπp.ne_zero
  have hN0 : 0 < N := by omega
  obtain ⟨hfc, hfe, hfs, hfi, hf0⟩ := hf
  haveI := d.haar
  obtain ⟨q, s, hq⟩ := exists_q L N π hπ 1 hN0
  obtain ⟨q₂, s₂, hq₂⟩ := exists_q L N π hπ 2 hN0
  have hmem1 := mem_map_Kg L N π hπ 1 q s hq
  have hmem2 := mem_map_Kg L N π hπ 2 q₂ s₂ hq₂
  have hfund0 : IsFundamentalDomain (Subgroup.map (jS L N) (Kg L N π 0)) d.D d.μ := by
    rw [map_Kg_zero]
    exact d.fund
  obtain ⟨hD1, hμ1, hint1⟩ := fund_conj d.μ (latS L N) _ q hmem1 d.D d.fund
  obtain ⟨hD2, -, -⟩ := fund_conj d.μ (latS L N) _ q₂ hmem2 d.D d.fund
  let w : Sp L N → ℝ := fun x => f (ofS L N (q * x))
  have hwc : Continuous w :=
    hfc.comp ((continuous_ofS L N).comp (continuous_const.mul continuous_id))
  have hwinv : LInv (jS L N) (Kg L N π 1) w := by
    intro γ hγ x
    have h1 : q * jS L N γ * q⁻¹ ∈ latS L N := (hmem1 _).1 ⟨γ, hγ, rfl⟩
    obtain ⟨δ, hδ⟩ := latS_emb L N _ h1
    show f (ofS L N (q * (jS L N γ * x))) = f (ofS L N (q * x))
    have e : q * (jS L N γ * x) = (q * jS L N γ * q⁻¹) * (q * x) := by group
    rw [e, map_mul, hδ, hfe]
  have hwint : IntegrableOn (fun x => w x ^ 2) ((fun x => q * x) ⁻¹' d.D) d.μ :=
    (hint1 (fun y => f (ofS L N y) ^ 2)).1.mpr hfi
  have hw0 : ∫ x in (fun x => q * x) ⁻¹' d.D, w x ∂d.μ = 0 := by
    rw [← hf0]
    exact (hint1 (fun y => f (ofS L N y))).2
  have hw2 : ∫ x in (fun x => q * x) ⁻¹' d.D, w x ^ 2 ∂d.μ = ∫ x in d.D, f (ofS L N x) ^ 2 ∂d.μ :=
    (hint1 (fun y => f (ofS L N y) ^ 2)).2
  have htri := hAr L π hπp h25 N hN
  obtain ⟨hAint, hA0, hAle⟩ := hGap (Matrix.SpecialLinearGroup (Fin N) L) (Sp L N) d.μ (jS L N)
    (jS_injective L N) (Kg L N π 0) (Kg L N π 1) (Kg L N π 2) htri (hDe L hTC π hπp N hN)
    d.D _ _ hfund0 hD1 hD2 d.fin hμ1 w hwc.measurable hwinv hwint hw0
  let C : Subgroup (Matrix.SpecialLinearGroup (Fin N) (𝓞 L)) :=
    (Hq L N π hπ).comap (Matrix.SpecialLinearGroup.toGL)
  let ψ : Matrix.SpecialLinearGroup (Fin N) (𝓞 L) →* Kg L N π 0 :=
    (iO L N).codRestrict (Kg L N π 0) (fun a => (mem_Kg_zero L N π _).2 ⟨a, rfl⟩)
  let H' : Subgroup (Kg L N π 0) := (Kg L N π 0 ⊓ Kg L N π 1).subgroupOf (Kg L N π 0)
  have hψ : ∀ a, ψ a ∈ H' ↔ a ∈ C := by
    intro a
    show iO L N a ∈ Kg L N π 0 ⊓ Kg L N π 1 ↔ Matrix.SpecialLinearGroup.toGL a ∈ Hq L N π hπ
    rw [Subgroup.mem_inf, mem_Hq]
    exact ⟨fun h => h.2, fun h => ⟨(mem_Kg_zero L N π _).2 ⟨a, rfl⟩, h⟩⟩
  have hψs : ∀ γ : Kg L N π 0, ∃ a, γ * (ψ a)⁻¹ ∈ H' := by
    intro γ
    obtain ⟨a, ha⟩ := (mem_Kg_zero L N π _).1 γ.2
    refine ⟨a, ?_⟩
    have : ψ a = γ := Subtype.ext ha
    rw [this, mul_inv_cancel]
    exact H'.one_mem
  have hkey : ∀ x : Sp L N, hecke (toK L N) (toP L N) (qel L N π hπ) f (ofS L N x) =
      avg (jS L N) (Kg L N π 0 ⊓ Kg L N π 1) (Kg L N π 0) w x := by
    intro x
    obtain ⟨e1, i1⟩ := finsum_transfer (Matrix.SpecialLinearGroup.toGL) (Hq L N π hπ) C
      (fun a => Iff.rfl) (fun γ => Hq_surj L N π hπ hN0 γ)
      (fun γ => f (toP L N (qel L N π hπ * toK L N γ) * ofS L N x))
      (fun h hh γ => coset_inv π hπ f hfe (ofS L N x) h hh γ)
    obtain ⟨e2, i2⟩ := finsum_transfer ψ H' C hψ hψs
      (fun k : Kg L N π 0 => w (jS L N k * x))
      (fun h hh k => by
        show w (jS L N ((h : _) * k) * x) = w (jS L N k * x)
        rw [map_mul, mul_assoc]
        exact hwinv _ (Subgroup.mem_subgroupOf.1 hh).2 _)
    beta_reduce at e1 e2
    rw [hecke_eq]
    unfold avg
    rw [e1, e2, ← i1, ← i2]
    congr 1
    apply finsum_congr
    intro c
    show f (toP L N (qel L N π hπ * toK L N (Matrix.SpecialLinearGroup.toGL c.out)) * ofS L N x) =
      f (ofS L N (q * (jS L N (iO L N c.out) * x)))
    have e : ofS L N (q * (jS L N (iO L N c.out) * x)) =
        scal L N s * (toP L N (qel L N π hπ * toK L N (Matrix.SpecialLinearGroup.toGL c.out)) * ofS L N x) := by
      rw [map_mul, map_mul, ofS_q L N π hπ q s hq, ← toP_toGL, map_mul]
      simp only [mul_assoc]
    rw [e, hfs]
  have hle : (Kg L N π 0 ⊓ Kg L N π 1 ⊓ Kg L N π 2).subgroupOf (Kg L N π 0) ≤ H' := by
    intro k hk
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    exact hk.1
  have hH'0 : H'.index ≠ 0 := by
    intro h0
    have hd := Subgroup.index_dvd_of_le hle
    rw [h0] at hd
    exact htri.fin₀ (Nat.eq_zero_of_zero_dvd hd)
  have hHq0 : (Hq L N π hπ).index ≠ 0 := by
    obtain ⟨-, i1⟩ := finsum_transfer (Matrix.SpecialLinearGroup.toGL) (Hq L N π hπ) C
      (fun a => Iff.rfl) (fun γ => Hq_surj L N π hπ hN0 γ) (E := ℝ) (fun _ => 0) (fun _ _ _ => rfl)
    obtain ⟨-, i2⟩ := finsum_transfer ψ H' C hψ hψs (E := ℝ) (fun _ => 0) (fun _ _ _ => rfl)
    rw [← i1, i2]
    exact hH'0
  refine ⟨?_, ?_⟩
  · unfold Lz
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have e : hecke (toK L N) (toP L N) (qel L N π hπ) f = fun y =>
          ((Hq L N π hπ).index : ℝ)⁻¹ * ∑ᶠ c : Quotient (QuotientGroup.rightRel (Hq L N π hπ)),
            f (toP L N (qel L N π hπ * toK L N c.out) * y) := funext (hecke_eq π hπ f)
      rw [e]
      exact continuous_const.mul (continuous_finsum_quot (Hq L N π hπ) hHq0
        (fun γ y => f (toP L N (qel L N π hπ * toK L N γ) * y))
        (fun γ => hfc.comp (continuous_const.mul continuous_id)))
    · intro γ x
      rw [hecke_eq, hecke_eq]
      congr 1
      have h := finsum_mul_right (Hq L N π hπ)
        (fun δ => f (toP L N (qel L N π hπ * toK L N δ) * x))
        (fun h hh δ => coset_inv π hπ f hfe x h hh δ) γ
      beta_reduce at h
      rw [← h]
      apply finsum_congr
      intro c
      simp only [emb_eq, map_mul, mul_assoc]
    · intro s' x
      rw [hecke_eq, hecke_eq]
      congr 1
      apply finsum_congr
      intro c
      rw [← mul_assoc, ← scal_comm L N s', mul_assoc, hfs]
    · simp only [hkey]
      exact hAint
    · simp only [hkey]
      exact hA0
  · calc ∫ x in d.D, hecke (toK L N) (toP L N) (qel L N π hπ) f (ofS L N x) ^ 2 ∂d.μ
        = ∫ x in d.D, avg (jS L N) (Kg L N π 0 ⊓ Kg L N π 1) (Kg L N π 0) w x ^ 2 ∂d.μ := by
          simp only [hkey]
      _ ≤ (2 / 5) ^ 2 * ∫ x in (fun x => q * x) ⁻¹' d.D, w x ^ 2 ∂d.μ := hAle
      _ = (2 / 5) ^ 2 * ∫ x in d.D, f (ofS L N x) ^ 2 ∂d.μ := by rw [hw2]
      _ ≤ (3 / 5) ^ 2 * ∫ x in d.D, f (ofS L N x) ^ 2 ∂d.μ := by
          apply mul_le_mul_of_nonneg_right (by norm_num)
          exact integral_nonneg (fun x => sq_nonneg _)

end PositivityTheory.KB.SpectralGap

end
