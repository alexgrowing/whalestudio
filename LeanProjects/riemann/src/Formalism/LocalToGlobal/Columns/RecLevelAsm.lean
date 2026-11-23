import Formalism.LocalToGlobal.Columns.RecLevelCls
import Formalism.LocalToGlobal.Columns.RecLevelTop
import Formalism.LocalToGlobal.Columns.RecLevelDiv
import Formalism.LocalToGlobal.Columns.RecLevelHost

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP St redAt redFn)

section Pack

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

structure RecCls (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (Lb : Submodule (𝓞 E) (Fin n → E))
    (U : Subgroup (GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) {cls : Type} (stab : cls → Type) [∀ c, Group (stab c)]
    (lat : cls → Submodule (𝓞 E) (Fin n → E)) where
  y : cls → Formalism.UG.UPts hc.sig J (FiniteAdeleRing (𝓞 F) F)
  y_bij : Function.Bijective (fun c : cls =>
    (Quotient.mk'' (y c) : Formalism.UG.ClassSet
      ((Formalism.UG.ratPts hc.sig J (FiniteAdeleRing (𝓞 F) F)).subgroupOf (Formalism.UG.UPts hc.sig J (FiniteAdeleRing (𝓞 F) F)))
      (U.subgroupOf (Formalism.UG.UPts hc.sig J (FiniteAdeleRing (𝓞 F) F)))))
  y_lat : ∀ c (x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F),
    x ∈ Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) (lat c) ↔
    ((((y c : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))⁻¹ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
      Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ x ∈
      Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) Lb
  stabI : ∀ c, stab c →* Formalism.UG.UJ (hc.sig : E →+* E) J
  stabI_inj : ∀ c, Function.Injective (stabI c)
  stabI_range : ∀ c (γ : GL (Fin n) E) (hγ : γ ∈ Formalism.UG.UJ (hc.sig : E →+* E) J),
    (⟨γ, hγ⟩ : Formalism.UG.UJ (hc.sig : E →+* E) J) ∈ (stabI c).range ↔
      Formalism.UG.bc (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ ∈
        U.map (MulAut.conj (y c : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))).toMonoidHom
  stabI_lat : ∀ c (γ : stab c) (x : Fin n → E),
    x ∈ lat c ↔ (((stabI c γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ x) ∈ lat c

end Pack

section Dia

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Pl E)) (H : Subgroup (GLG E n SG))

theorem rla_dia_inv (c : DiaG E ST) (d : DecoSet E n ST SG) : (d.dia c⁻¹).dia c = d := by
  apply Subtype.ext
  show (d.1.dia c⁻¹).dia c = d.1
  ext <;> simp [Deco.dia, ← mul_assoc]

theorem rla_dia_inv' (c : DiaG E ST) (d : DecoSet E n ST SG) : (d.dia c).dia c⁻¹ = d := by
  apply Subtype.ext
  show (d.1.dia c).dia c⁻¹ = d.1
  ext <;> simp [Deco.dia, ← mul_assoc]

theorem rla_dia_inj (c : DiaG E ST) {d d' : DecoSet E n ST SG} (h : d.dia c = d'.dia c) : d = d' := by
  rw [← rla_dia_inv' n ST SG c d, h, rla_dia_inv' n ST SG c d']

theorem DecoSet.dia_L (c : DiaG E ST) (d : DecoSet E n ST SG) : (d.dia c).1.L = d.1.L := by
  show (d.1.dia c).L = d.1.L
  unfold Deco.L
  congr 1
  ext x
  simp only [Deco.dia, Set.mem_setOf_eq, Units.mul_right_eq_zero]

theorem decoOfD_ptOfD (hS : DecoPtSurj hc n ST SG) (c : DiaG E ST) (d : DecoSet E n ST SG) :
    decoOfD n ST SG c (ptOfD hc n ST SG c d : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = d := by
  show (decoOf ST SG (ptOf hc n ST SG (d.dia c⁻¹) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))).dia c = d
  rw [decoOf_ptOf hc n ST SG hS (d.dia c⁻¹)]
  exact rla_dia_inv n ST SG c d

theorem rla_dia_smulH (c : DiaG E ST) (g : UF E n × H) (d : DecoSet E n ST SG) : (g • d).dia c = g • d.dia c := rfl

theorem rla_cls_eq {d d' : DecoSet E n ST SG} :
    decoCls n ST SG H d = decoCls n ST SG H d' ↔ ∃ g : UF E n × H, g • d' = d := by
  constructor
  · intro h
    exact MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp (Quotient.exact h))
  · rintro ⟨g, hg⟩
    exact Quotient.sound (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨g, hg⟩))

theorem levU_y_bijD (hS : DecoPtSurj hc n ST SG) (c₀ : DiaG E ST) (s : DecoCl n ST SG H → DecoSet E n ST SG)
    (hs : ∀ c, decoCls n ST SG H (s c) = c) :
    Function.Bijective (fun c : DecoCl n ST SG H =>
      (Quotient.mk'' (ptOfD hc n ST SG c₀ (s c)) : AdCl hc n ST SG H)) := by
  classical

  let Φ : DecoCl n ST SG H → DecoCl n ST SG H := fun q => Quotient.liftOn' q
    (fun d => decoCls n ST SG H (d.dia c₀⁻¹)) (fun a b hab => by
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hab)
      rw [← hg]
      exact Quotient.sound (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨g, rfl⟩)))
  let Ψ : DecoCl n ST SG H → DecoCl n ST SG H := fun q => Quotient.liftOn' q
    (fun d => decoCls n ST SG H (d.dia c₀)) (fun a b hab => by
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hab)
      rw [← hg]
      exact Quotient.sound (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨g, rfl⟩)))
  have hΦΨ : ∀ q, Φ (Ψ q) = q := by
    intro q
    induction q using Quotient.inductionOn' with
    | h d =>
      show decoCls n ST SG H ((d.dia c₀).dia c₀⁻¹) = _
      rw [rla_dia_inv' n ST SG c₀ d]
      rfl
  have hΨΦ : ∀ q, Ψ (Φ q) = q := by
    intro q
    induction q using Quotient.inductionOn' with
    | h d =>
      show decoCls n ST SG H ((d.dia c₀⁻¹).dia c₀) = _
      rw [rla_dia_inv n ST SG c₀ d]
      rfl
  have hΦ : Function.Bijective Φ := Function.bijective_iff_has_inverse.mpr ⟨Ψ, hΨΦ, hΦΨ⟩
  let s' : DecoCl n ST SG H → DecoSet E n ST SG := fun c => (s (Ψ c)).dia c₀⁻¹
  have hs' : ∀ c, decoCls n ST SG H (s' c) = c := by
    intro c
    calc decoCls n ST SG H (s' c) = Φ (decoCls n ST SG H (s (Ψ c))) := rfl
      _ = Φ (Ψ c) := by rw [hs (Ψ c)]
      _ = c := hΦΨ c
  have hF := levU_y_bij hc n ST SG H hS s' hs'
  have heq : (fun c : DecoCl n ST SG H => (Quotient.mk'' (ptOfD hc n ST SG c₀ (s c)) : AdCl hc n ST SG H)) =
      (fun c => (Quotient.mk'' (ptOf hc n ST SG (s' (Φ c))) : AdCl hc n ST SG H)) := by
    funext c
    show _ = (Quotient.mk'' (ptOf hc n ST SG ((s (Ψ (Φ c))).dia c₀⁻¹)) : AdCl hc n ST SG H)
    rw [hΨΦ c]
    rfl
  rw [heq]
  exact hF.comp hΦ

theorem rla_mem_stab_dia (c : DiaG E ST) (d : DecoSet E n ST SG) (g : UF E n × H) :
    g ∈ MulAction.stabilizer (UF E n × H) (d.dia c) ↔ g ∈ MulAction.stabilizer (UF E n × H) d := by
  simp only [MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    exact rla_dia_inj n ST SG c (d := g • d) (d' := d) h
  · intro h
    show (g • d).dia c = d.dia c
    rw [h]

theorem rla_mem_range_stabRat (d : DecoSet E n ST SG) (γ : URat hc n) :
    γ ∈ (stabRat hc n ST SG H d).range ↔ ∃ h : H, (ratHom hc n γ, h) ∈ MulAction.stabilizer (UF E n × H) d := by
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨a.1.2, ?_⟩
    rw [rlc_ratHom_stabRat hc n ST SG H d a]
    exact a.2
  · rintro ⟨h, hmem⟩
    refine ⟨⟨(ratHom hc n γ, h), hmem⟩, ?_⟩
    apply (ratHom_bijective hc n).1
    rw [rlc_ratHom_stabRat]

theorem stabRat_rangeD (c : DiaG E ST) (d : DecoSet E n ST SG) (y : UAd hc n)
    (hy : decoOfD n ST SG c (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = d) (γ : URat hc n) :
    γ ∈ (stabRat hc n ST SG H d).range ↔
      Formalism.UG.bc (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ : GL (Fin n) E) ∈
        (levU hc n ST SG H).map (MulAut.conj (y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))).toMonoidHom := by
  have hy' : decoOf ST SG (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = d.dia c⁻¹ := by
    rw [← hy]
    exact (rla_dia_inv' n ST SG c _).symm
  rw [← stabRat_range hc n ST SG H (d.dia c⁻¹) y hy' γ, rla_mem_range_stabRat, rla_mem_range_stabRat]
  simp only [rla_mem_stab_dia]

theorem levU_y_latD (hS : DecoPtSurj hc n ST SG) (c : DiaG E ST) (d : DecoSet E n ST SG)
    (x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    x ∈ Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) d.1.L ↔
    ((((ptOfD hc n ST SG c d : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))⁻¹ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
      Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ x ∈
      Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) (baseLb E n ST) := by
  rw [← DecoSet.dia_L n ST SG c⁻¹ d]
  exact levU_y_lat hc n ST SG hS (d.dia c⁻¹) x

def recCls (hS : DecoPtSurj hc n ST SG) (c₀ : DiaG E ST) (s : DecoCl n ST SG H → DecoSet E n ST SG)
    (hs : ∀ c, decoCls n ST SG H (s c) = c) :
    RecCls hc (1 : Matrix (Fin n) (Fin n) E) (baseLb E n ST) (levU hc n ST SG H)
      (fun c => MulAction.stabilizer (UF E n × H) (s c)) (fun c => (s c).1.L) where
  y c := ptOfD hc n ST SG c₀ (s c)
  y_bij := levU_y_bijD hc n ST SG H hS c₀ s hs
  y_lat c x := levU_y_latD hc n ST SG hS c₀ (s c) x
  stabI c := stabRat hc n ST SG H (s c)
  stabI_inj c := stabRat_injective hc n ST SG H (s c)
  stabI_range c γ hγ := stabRat_rangeD hc n ST SG H c₀ (s c) _ (decoOfD_ptOfD hc n ST SG hS c₀ (s c)) ⟨γ, hγ⟩
  stabI_lat c γ x := stabRat_lat hc n ST SG H (s c) γ x

end Dia

end Formalism.L2.Col
