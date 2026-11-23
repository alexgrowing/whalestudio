import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecPairDefs
import ReciprocityTheory.GroupCohomology.ComapZeroCoboundariesEqBot
import ReciprocityTheory.GroupCohomology.DEqZeroOfMemB

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem kbarT_rho_ofK (g : GK p K) (a : Additive Kˣ) : (kbarT p K).rho g (ofK p K a) = ofK p K a :=
  Units.ext (g.commutes _)

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem exists_int_of_mk_eq {x y : ℚ} (h : (QuotientAddGroup.mk x : QZ) = QuotientAddGroup.mk y) :
    ∃ n : ℤ, (n : ℚ) = x - y := by
  have h0 : (QuotientAddGroup.mk (x - y) : QZ) = 0 := by
    rw [QuotientAddGroup.mk_sub, h, sub_self]
  obtain ⟨n, hn⟩ := (QuotientAddGroup.eq_zero_iff _).1 h0
  exact ⟨n, hn⟩

theorem exists_defect (χ : Additive G →+ QZ) (t : G → ℚ)
    (ht : ∀ g, (QuotientAddGroup.mk (t g) : QZ) = χ (Additive.ofMul g)) :
    ∃ m : (Fin 2 → G) → ℤ, ∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1) := by
  have h : ∀ g : Fin 2 → G, ∃ n : ℤ, (n : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1) := fun g =>
    exists_int_of_mk_eq (by rw [QuotientAddGroup.mk_add, ht, ht, ht, ofMul_mul, map_add])
  choose m hm using h
  exact ⟨m, hm⟩

theorem defect_isLocallyConstant {t : G → ℚ} (ht : IsLocallyConstant t) {m : (Fin 2 → G) → ℤ}
    (hm : ∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) : IsLocallyConstant m := by
  have h : IsLocallyConstant (fun g : Fin 2 → G => t (g 0) + t (g 1) - t (g 0 * g 1)) :=
    ((ht.comp_continuous (continuous_apply 0)).add (ht.comp_continuous (continuous_apply 1))).sub
      (ht.comp_continuous ((continuous_apply 0).mul (continuous_apply 1)))
  refine IsLocallyConstant.desc m (fun n : ℤ => (n : ℚ)) ?_ Int.cast_injective
  have e : (fun n : ℤ => (n : ℚ)) ∘ m = fun g : Fin 2 → G => t (g 0) + t (g 1) - t (g 0 * g 1) := funext hm
  rw [e]; exact h

theorem defect_cocycle {t : G → ℚ} {m : (Fin 2 → G) → ℤ}
    (hm : ∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) (v : Fin 3 → G) :
    m ![v 1, v 2] - m ![v 0 * v 1, v 2] + m ![v 0, v 1 * v 2] - m ![v 0, v 1] = 0 := by
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [hm, hm, hm, hm]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_assoc]
  ring

theorem trep_dn_one {R : Type} [CommRing R] (M : TRep R G) (f : (Fin 1 → G) → M.V) (v : Fin 2 → G) :
    ReciprocityTheory.Gal.dn M.rho 1 f v = M.rho (v 0) (f ![v 1]) - f ![v 0 * v 1] + f ![v 0] :=
  LowDeg.dn_one_apply M.rho f v

theorem trep_dn_two {R : Type} [CommRing R] (M : TRep R G) (f : (Fin 2 → G) → M.V) (v : Fin 3 → G) :
    ReciprocityTheory.Gal.dn M.rho 2 f v = M.rho (v 0) (f ![v 1, v 2]) - f ![v 0 * v 1, v 2] + f ![v 0, v 1 * v 2] -
      f ![v 0, v 1] :=
  LowDeg.dn_two_apply M.rho f v

variable (M : TRep ℤ G)

theorem exists_defect_cocycle {a : M.V} (ha : ∀ g, M.rho g a = a) {t : G → ℚ} (ht : IsLocallyConstant t)
    {m : (Fin 2 → G) → ℤ} (hm : ∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) :
    ∃ (z : M.coch.X 2) (_ : M.coch.d 2 z = 0), ∀ g, z.1 g = m g • a := by
  refine ⟨⟨fun g => m g • a, ((defect_isLocallyConstant ht hm).comp (· • a)).continuous⟩, ?_, fun g => rfl⟩
  refine LowDeg.coch_d_eq_zero M (funext fun v => ?_)
  rw [trep_dn_two]
  show M.rho (v 0) (m ![v 1, v 2] • a) - m ![v 0 * v 1, v 2] • a + m ![v 0, v 1 * v 2] • a - m ![v 0, v 1] • a = 0
  rw [map_zsmul, ha, ← sub_smul, ← add_smul, ← sub_smul, defect_cocycle hm, zero_smul]

theorem defect_cls_eq {a : M.V} (ha : ∀ g, M.rho g a = a) {t t' : G → ℚ} (ht : IsLocallyConstant t)
    (ht' : IsLocallyConstant t') (htt : ∀ g, (QuotientAddGroup.mk (t g) : QZ) = QuotientAddGroup.mk (t' g))
    {m m' : (Fin 2 → G) → ℤ} (hm : ∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1))
    (hm' : ∀ g, (m' g : ℚ) = t' (g 0) + t' (g 1) - t' (g 0 * g 1))
    {z z' : M.coch.X 2} (hz : M.coch.d 2 z = 0) (hz' : M.coch.d 2 z' = 0)
    (hzv : ∀ g, z.1 g = m g • a) (hzv' : ∀ g, z'.1 g = m' g • a) :
    M.coch.cls 2 z hz = M.coch.cls 2 z' hz' := by
  choose u hu using fun g => exists_int_of_mk_eq (htt g)
  have hul : IsLocallyConstant u := by
    refine IsLocallyConstant.desc u (fun n : ℤ => (n : ℚ)) ?_ Int.cast_injective
    have e : (fun n : ℤ => (n : ℚ)) ∘ u = fun g => t g - t' g := funext hu
    rw [e]; exact ht.sub ht'
  rw [Cx.cls_eq_iff]
  refine ⟨⟨fun g => u (g 0) • a,
    ((hul.comp_continuous (continuous_apply 0)).comp (· • a)).continuous⟩, Subtype.ext (funext fun v => ?_)⟩
  refine (trep_dn_one M (fun g => u (g 0) • a) v).trans ?_
  show M.rho (v 0) (u (v 1) • a) - u (v 0 * v 1) • a + u (v 0) • a = z.1 v - z'.1 v
  rw [hzv, hzv']
  rw [map_zsmul, ha, ← sub_smul, ← add_smul, ← sub_smul]
  congr 1
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [hu, hu, hu, hm, hm']
  ring

end General

end ReciprocityTheory.DiscreteGroups.LocalClassField
