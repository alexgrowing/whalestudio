import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PStringStepB
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.PAdicHodge.AInfGalois

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec
open scoped ComplexConjugate

namespace PositivityTheory.Rg.Rs.StrStepC

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

def twL {a₁ a₂ d₁ d₂ : ℕ} (π₁ : CuspSub E a₁) (π₂ : CuspSub E a₂) (x : Fin d₁ → ℂ) (y : Fin d₂ → ℂ) :
    List (Σ a, CG E a) :=
  List.ofFn (fun i => (⟨a₁, (CG.mk π₁).twist (GlobalTheory.CuspRep.Model.absC E (x i))⟩ : Σ a, CG E a)) ++
    List.ofFn (fun j => (⟨a₂, (CG.mk π₂).twist (GlobalTheory.CuspRep.Model.absC E (y j))⟩ : Σ a, CG E a))

theorem map_fsum {α β ι : Type} (f : α → β) (s : Finset ι) (g : ι → Multiset α) :
    (∑ i ∈ s, g i).map f = ∑ i ∈ s, (g i).map f :=
  map_sum (Multiset.mapAddMonoidHom f) g s

omit [IsTotallyComplex E] in
theorem absNorm_ne_zero (w : HeightOneSpectrum (𝓞 E)) : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ≠ 0 := by
  have := NumberField.HeightOneSpectrum.one_lt_absNorm w
  exact_mod_cast (by omega : Ideal.absNorm w.asIdeal ≠ 0)

theorem hinv_absC (w : HeightOneSpectrum (𝓞 E)) (x : ℂ) :
    (star ((GlobalTheory.CuspRep.Model.absC E x).val w))⁻¹ = (GlobalTheory.CuspRep.Model.absC E (-conj x)).val w := by
  apply Units.ext
  rw [Units.val_inv_eq_inv_val, Units.coe_star, StrStepB.absC_val, StrStepB.absC_val]
  have hq : (((Ideal.absNorm w.asIdeal : ℕ) : ℂ)).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm
  have h1 := Complex.cpow_conj ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) (-x) hq
  rw [Complex.conj_natCast] at h1
  change (conj (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-x)))⁻¹ = _
  rw [← h1, ← Complex.cpow_neg, map_neg, neg_neg]

omit [IsTotallyComplex E] in

theorem satTw_string (w : HeightOneSpectrum (𝓞 E)) (z : ℂ) (C B₀ : Multiset ℂˣ) {d : ℕ} (e : Fin d → ℝ)
    (h : C.map (fun b : ℂˣ => (b : ℂ)) = ∑ i, satTw w (e i : ℂ) B₀) :
    satTw w z C = ∑ i, B₀.map fun b : ℂˣ => (b : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-(z + (e i : ℂ))) := by
  have e1 : satTw w z C = (C.map fun b : ℂˣ => (b : ℂ)).map
      (fun c => c * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-z)) := by
    unfold satTw; congr 1
    exact Multiset.bind_singleton _ _
  rw [e1, h, map_fsum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e2 : satTw w (e i : ℂ) B₀ = (B₀.map fun b : ℂˣ => (b : ℂ)).map
      (fun c => c * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-(e i : ℂ))) := by
    unfold satTw; congr 1
    exact Multiset.bind_singleton _ _
  rw [e2, Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl fun b _ => ?_
  simp only [Function.comp_apply]
  rw [neg_add, Complex.cpow_add _ _ (absNorm_ne_zero w)]
  ring

theorem sat_expand (hI : SatInd2) (hA : SatAsc) (hH : SatHerm) {r s : ℕ} (V : Submodule ℂ (Sm E (r + s)))
    (V₁ : Submodule ℂ (Sm E r)) (V₂ : Submodule ℂ (Sm E s)) (z₁ z₂ : ℂ) (hV : IsDiscrete V) (hV₁ : IsDiscrete V₁)
    (hV₂ : IsDiscrete V₂) (hemb : Emb V (MemInd2 (tw V₁ z₁) (tw V₂ z₂))) {a₁ d₁ a₂ d₂ : ℕ} (π₁ : CuspSub E a₁)
    (π₂ : CuspSub E a₂) (ha₁ : 1 ≤ a₁) (ha₂ : 1 ≤ a₂) (hu₁ : π₁.IsUnitary) (hn₁ : IsNormalised π₁)
    (hu₂ : π₂.IsUnitary) (hn₂ : IsNormalised π₂) (h₁ : AscEmb V₁ π₁ d₁) (h₂ : AscEmb V₂ π₂ d₂) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ BV B₁ B₂ : Multiset ℂˣ, SatV V w BV ∧
      (CG.mk π₁).HasSat w B₁ ∧ (CG.mk π₂).HasSat w B₂ ∧
      BV.map (fun b : ℂˣ => (b : ℂ)) =
        (∑ i : Fin d₁, B₁.map fun b : ℂˣ =>
          (b : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-(z₁ - (s : ℂ) / 2 + (spehExp d₁ i : ℂ)))) +
          ∑ j : Fin d₂, B₂.map (fun b : ℂˣ =>
            (b : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-(z₂ + (r : ℂ) / 2 + (spehExp d₂ j : ℂ)))) ∧
      BV.map (fun b => (star b)⁻¹) = BV ∧ B₁.map (fun b => (star b)⁻¹) = B₁ ∧ B₂.map (fun b => (star b)⁻¹) = B₂ := by
  filter_upwards [hI E r s V V₁ V₂ z₁ z₂ hV hV₁ hV₂ hemb, hA E r a₁ d₁ V₁ π₁ hV₁ h₁,
    hA E s a₂ d₂ V₂ π₂ hV₂ h₂] with w hw hw₁ hw₂
  obtain ⟨B, C₁, C₂, hB, hC₁, hC₂, e⟩ := hw
  obtain ⟨B₁, hs₁, hall₁⟩ := hw₁
  obtain ⟨B₂, hs₂, hall₂⟩ := hw₂
  refine ⟨B, B₁, B₂, hB, hs₁, hs₂, ?_, (hH E (r + s) w B).1 V hV hB, (hH E a₁ w B₁).2 π₁ ha₁ hu₁ hn₁ hs₁,
    (hH E a₂ w B₂).2 π₂ ha₂ hu₂ hn₂ hs₂⟩
  rw [e, satTw_string w _ C₁ B₁ (spehExp d₁) (hall₁ C₁ hC₁), satTw_string w _ C₂ B₂ (spehExp d₂) (hall₂ C₂ hC₂)]

theorem perm_of (hR : GlobalTheory.Published.JacquetShalikaRigidity) {a₁ a₂ d₁ d₂ : ℕ} (π₁ : CuspSub E a₁) (π₂ : CuspSub E a₂)
    (ha₁ : 1 ≤ a₁) (ha₂ : 1 ≤ a₂) (x : Fin d₁ → ℂ) (y : Fin d₂ → ℂ)
    (hw : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ BV B₁ B₂ : Multiset ℂˣ,
      (CG.mk π₁).HasSat w B₁ ∧ (CG.mk π₂).HasSat w B₂ ∧
      BV.map (fun b : ℂˣ => (b : ℂ)) =
        (∑ i, B₁.map fun b : ℂˣ => (b : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-x i)) +
          ∑ j, B₂.map (fun b : ℂˣ => (b : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-y j)) ∧
      BV.map (fun b => (star b)⁻¹) = BV ∧ B₁.map (fun b => (star b)⁻¹) = B₁ ∧ B₂.map (fun b => (star b)⁻¹) = B₂) :
    (twL π₁ π₂ x y).Perm (twL π₁ π₂ (fun i => -conj (x i)) (fun j => -conj (y j))) := by
  classical
  have hpos : ∀ (x' : Fin d₁ → ℂ) (y' : Fin d₂ → ℂ), ∀ p ∈ twL π₁ π₂ x' y', 1 ≤ p.1 := by
    intro x' y' p hp
    simp only [twL, List.mem_append, List.mem_ofFn] at hp
    rcases hp with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · exact ha₁
    · exact ha₂
  refine hR.perm _ _ (hpos _ _) (hpos _ _) (hw.mono fun w hw' => ?_)
  obtain ⟨BV, B₁, B₂, h₁, h₂, e, hV, hh₁, hh₂⟩ := hw'
  let B : (Σ a, CG E a) → Multiset ℂˣ := fun p => if h : ∃ B, p.2.HasSat w B then h.choose else 0
  have hB : ∀ p (B' : Multiset ℂˣ), p.2.HasSat w B' → B p = B' := fun p B' h => by
    have hex : ∃ B, p.2.HasSat w B := ⟨B', h⟩
    simp only [B, dif_pos hex]
    exact hex.choose_spec.unique h
  have t₁ : ∀ u : ℂ, B ⟨a₁, (CG.mk π₁).twist (GlobalTheory.CuspRep.Model.absC E u)⟩ =
      B₁.map (· * (GlobalTheory.CuspRep.Model.absC E u).val w) :=
    fun u => hB _ _ (StrStepB.hasSat_twist_absC π₁ h₁ u)
  have t₂ : ∀ u : ℂ, B ⟨a₂, (CG.mk π₂).twist (GlobalTheory.CuspRep.Model.absC E u)⟩ =
      B₂.map (· * (GlobalTheory.CuspRep.Model.absC E u).val w) :=
    fun u => hB _ _ (StrStepB.hasSat_twist_absC π₂ h₂ u)
  have hsat : ∀ (x' : Fin d₁ → ℂ) (y' : Fin d₂ → ℂ), ∀ p ∈ twL π₁ π₂ x' y', p.2.HasSat w (B p) := by
    intro x' y' p hp
    simp only [twL, List.mem_append, List.mem_ofFn] at hp
    rcases hp with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · rw [t₁]; exact StrStepB.hasSat_twist_absC π₁ h₁ _
    · rw [t₂]; exact StrStepB.hasSat_twist_absC π₂ h₂ _
  refine ⟨B, hsat x y, hsat _ _, ?_⟩
  simp only [twL, List.map_append, List.map_ofFn, List.sum_append, List.sum_ofFn, Function.comp_def, t₁, t₂]
  have hT : (∑ i, B₁.map (· * (GlobalTheory.CuspRep.Model.absC E (x i)).val w)) +
      ∑ j, B₂.map (· * (GlobalTheory.CuspRep.Model.absC E (y j)).val w) = BV := by
    apply Multiset.map_injective (f := fun b : ℂˣ => (b : ℂ)) Units.val_injective
    rw [e, Multiset.map_add, map_fsum, map_fsum]
    congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;> rw [Multiset.map_map] <;>
      refine Multiset.map_congr rfl fun b _ => ?_ <;> simp [StrStepB.absC_val]
  have hm : ∀ (C : Multiset ℂˣ) (u : ℂˣ), C.map (fun b => (star b)⁻¹) = C →
      (C.map (· * u)).map (fun b => (star b)⁻¹) = C.map (· * (star u)⁻¹) := by
    intro C u hC
    conv_rhs => rw [← hC]
    rw [Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl fun b _ => ?_
    simp [star_mul', mul_comm]
  calc _ = BV := hT
    _ = BV.map (fun b => (star b)⁻¹) := hV.symm
    _ = _ := by
      rw [← hT, Multiset.map_add, map_fsum, map_fsum]
      simp only [hm B₁ _ hh₁, hm B₂ _ hh₂, hinv_absC]

end PositivityTheory.Rg.Rs.StrStepC

end
