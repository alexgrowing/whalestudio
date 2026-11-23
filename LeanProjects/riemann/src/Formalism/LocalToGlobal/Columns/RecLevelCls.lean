import Formalism.LocalToGlobal.Columns.RecLevel
import Formalism.LocalToGlobal.Columns.CoefColLemmas

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP St redAt redFn)

section Cls

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Pl E)) (H : Subgroup (GLG E n SG))

theorem rlc_decoOf_val {x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hx : x ∈ UAd hc n) :
    (decoOf ST SG x).1 = decoRaw ST SG x := by
  unfold decoOf
  rw [dif_pos (decorated_lattice_exists hc n ST SG x hx)]

theorem rlc_smul_val (a : UF E n × H) (d : DecoSet E n ST SG) :
    (a • d).1 = d.1.act a.1.1 (a.2 : GLG E n SG) := rfl

theorem rlc_decoOf_sm (γ : URat hc n) (k : levU hc n ST SG H) (x : UAd hc n) :
    decoOf ST SG (Formalism.UG.bc (iA F E) (γ : GL (Fin n) E) * (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
        (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹) =
      ((ratHom hc n γ, levRed hc n ST SG H k) : UF E n × H) • decoOf ST SG (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
  have hk : (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈ J0 hc n ST := unipotentLevel_le_mirabolicLevel hc n ST SG H k.2
  have hm : Formalism.UG.bc (iA F E) (γ : GL (Fin n) E) * (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
      (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ ∈ UAd hc n :=
    (rawSm hc n ST γ ⟨k.1, hk⟩ x).2
  apply Subtype.ext
  rw [rlc_decoOf_val hc n ST SG hm, rlc_smul_val, rlc_decoOf_val hc n ST SG x.2]
  exact decoRaw_rawSm hc ST SG γ ⟨k.1, hk⟩ x

def adToCls : AdCl hc n ST SG H → DecoCl n ST SG H :=
  Quotient.lift (fun x : UAd hc n => decoCls n ST SG H (decoOf ST SG (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)))) (by
    intro a b hab
    obtain ⟨h, hh, k, hk, e⟩ := DoubleCoset.rel_iff.1 hab
    obtain ⟨γ, hγ⟩ := Formalism.L2.DIV.ratEl_surjective (⟨h, hh⟩ : Formalism.L2.DIV.UQ hc (1 : Matrix (Fin n) (Fin n) E))
    have hk' : (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ ∈ levU hc n ST SG H :=
      Subgroup.inv_mem _ (Subgroup.mem_subgroupOf.1 hk)
    have hh' : (h : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = Formalism.UG.bc (iA F E) (γ : GL (Fin n) E) :=
      (congrArg (fun z : Formalism.L2.DIV.UQ hc (1 : Matrix (Fin n) (Fin n) E) =>
        ((z : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) hγ).symm
    have e' : (b : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = Formalism.UG.bc (iA F E) (γ : GL (Fin n) E) *
        (a : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
        (((⟨_, hk'⟩ : levU hc n ST SG H) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)))⁻¹ := by
      rw [e, Subgroup.coe_mul, Subgroup.coe_mul, hh', inv_inv]
    show decoCls n ST SG H _ = decoCls n ST SG H _
    rw [e', rlc_decoOf_sm]
    exact (Quotient.sound (MulAction.orbitRel_apply.2 ⟨_, rfl⟩)).symm)

theorem adToCls_mk (x : UAd hc n) :
    adToCls hc n ST SG H (Quotient.mk'' x) = decoCls n ST SG H (decoOf ST SG (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) := rfl

theorem rlc_rel_of_orbit {x y : UAd hc n} (a : UF E n × H)
    (h : decoOf ST SG (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      a • decoOf ST SG (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) :
    ∃ (γ : URat hc n) (k : levU hc n ST SG H), ratHom hc n γ = a.1 ∧ levRed hc n ST SG H k = a.2 ∧
      (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = Formalism.UG.bc (iA F E) (γ : GL (Fin n) E) *
        (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ := by
  obtain ⟨γ, hγ⟩ := (ratHom_bijective hc n).2 a.1
  set y' : UAd hc n := ratIn hc n γ * y with hy'
  have h1 : decoOf ST SG (y' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      ((ratHom hc n γ, 1) : UF E n × H) • decoOf ST SG (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    have := rlc_decoOf_sm hc n ST SG H γ 1 y
    rw [map_one] at this
    rw [← this]
    congr 1
    simp [hy', ratIn_val]
  have h2 : decoOf ST SG (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      ((1, a.2) : UF E n × H) • decoOf ST SG (y' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    rw [h, h1, smul_smul]
    congr 1
    rw [Prod.mk_mul_mk, one_mul, mul_one, hγ]
  have h3 : decoRaw ST SG (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      (decoRaw ST SG (y' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))).act 1 (a.2 : GLG E n SG) := by
    have := congrArg Subtype.val h2
    rw [rlc_decoOf_val hc n ST SG x.2, rlc_smul_val, rlc_decoOf_val hc n ST SG y'.2] at this
    exact this
  obtain ⟨hJ, hr⟩ := mem_congruence_of_action hc ST SG x.2 y'.2 (a.2 : GLG E n SG) h3
  have hkU : (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ * (y' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈
      levU hc n ST SG H := (mem_levU hc n ST SG H).2 ⟨hJ, by rw [hr]; exact a.2.2⟩
  refine ⟨γ, ⟨_, hkU⟩, hγ, Subtype.ext hr, ?_⟩
  show _ = _ * _ * ((x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ * (y' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)))⁻¹
  rw [hy', Subgroup.coe_mul, ratIn_val]
  group

theorem rlc_mk_eq {x y : UAd hc n} (γ : URat hc n) (k : levU hc n ST SG H)
    (e : (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = Formalism.UG.bc (iA F E) (γ : GL (Fin n) E) *
        (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹) :
    (Quotient.mk'' y : AdCl hc n ST SG H) = Quotient.mk'' x := by
  refine Quotient.sound' (DoubleCoset.rel_iff.2 ⟨(Formalism.L2.DIV.ratEl γ).1, (Formalism.L2.DIV.ratEl γ).2,
    ⟨(k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹, levU_le_UAd hc n ST SG H (Subgroup.inv_mem _ k.2)⟩,
    Subgroup.mem_subgroupOf.2 (Subgroup.inv_mem _ k.2), Subtype.ext e⟩)

theorem adToCls_injective : Function.Injective (adToCls hc n ST SG H) := by
  intro c c'
  induction c using Quotient.inductionOn' with
  | h x =>
  induction c' using Quotient.inductionOn' with
  | h y =>
    intro h
    rw [adToCls_mk, adToCls_mk] at h
    obtain ⟨a, ha⟩ := MulAction.orbitRel_apply.1 (Quotient.exact h)
    obtain ⟨γ, k, -, -, e⟩ := rlc_rel_of_orbit hc n ST SG H a ha.symm
    exact (rlc_mk_eq hc n ST SG H γ k e).symm

theorem decoOf_ptOf (hS : DecoPtSurj hc n ST SG) (d : DecoSet E n ST SG) :
    decoOf ST SG (ptOf hc n ST SG d : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = d := by
  have hex : ∃ x : UAd hc n, decoOf ST SG (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = d := by
    obtain ⟨q, hq⟩ := hS d
    induction q using QuotientGroup.induction_on with
    | H x => exact ⟨x, by rw [← decoPt_mk hc n ST SG x]; exact hq⟩
  unfold ptOf
  rw [dif_pos hex]
  exact hex.choose_spec

theorem adToCls_adClsOf (hS : DecoPtSurj hc n ST SG) (d : DecoSet E n ST SG) :
    adToCls hc n ST SG H (adClsOf hc n ST SG H d) = decoCls n ST SG H d := by
  unfold adClsOf
  rw [adToCls_mk, decoOf_ptOf hc n ST SG hS]

theorem adToCls_surjective (hS : DecoPtSurj hc n ST SG) : Function.Surjective (adToCls hc n ST SG H) := by
  intro c
  induction c using Quotient.inductionOn' with
  | h d => exact ⟨adClsOf hc n ST SG H d, adToCls_adClsOf hc n ST SG H hS d⟩

theorem adToCls_bijective (hS : DecoPtSurj hc n ST SG) : Function.Bijective (adToCls hc n ST SG H) :=
  ⟨adToCls_injective hc n ST SG H, adToCls_surjective hc n ST SG H hS⟩

theorem levU_y_bij (hS : DecoPtSurj hc n ST SG) (s : DecoCl n ST SG H → DecoSet E n ST SG)
    (hs : ∀ c, decoCls n ST SG H (s c) = c) :
    Function.Bijective (fun c : DecoCl n ST SG H =>
      (Quotient.mk'' (ptOf hc n ST SG (s c)) : Formalism.UG.ClassSet
        ((Formalism.UG.ratPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)).subgroupOf
          (Formalism.UG.UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)))
        ((levU hc n ST SG H).subgroupOf (Formalism.UG.UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F))))) := by
  have hinv : ∀ c, adToCls hc n ST SG H (adClsOf hc n ST SG H (s c)) = c := fun c => by
    rw [adToCls_adClsOf hc n ST SG H hS, hs]
  constructor
  · intro c c' h
    have h' : adClsOf hc n ST SG H (s c) = adClsOf hc n ST SG H (s c') := h
    rw [← hinv c, ← hinv c', h']
  · intro q
    refine ⟨adToCls hc n ST SG H q, ?_⟩
    exact adToCls_injective hc n ST SG H (hinv _)

theorem rlc_ratHom_stabRat (d : DecoSet E n ST SG) (a : MulAction.stabilizer (UF E n × H) d) :
    ratHom hc n (stabRat hc n ST SG H d a) = a.1.1 :=
  (ratEquiv hc n).apply_symm_apply a.1.1

theorem stabRat_injective (d : DecoSet E n ST SG) : Function.Injective (stabRat hc n ST SG H d) := by
  intro a b hab
  have h1 : a.1.1 = b.1.1 := by
    rw [← rlc_ratHom_stabRat hc n ST SG H d a, ← rlc_ratHom_stabRat hc n ST SG H d b, hab]
  have ha : ((a.1.1, (a.1.2 : GLG E n SG)) : UF E n × GLG E n SG) • d = d := a.2
  have hb : ((b.1.1, (b.1.2 : GLG E n SG)) : UF E n × GLG E n SG) • d = d := b.2
  have h2 := DecoSet.stab_fst_injective d ha hb h1
  exact Subtype.ext (Prod.ext h1 (Subtype.ext (congrArg Prod.snd h2)))

theorem stabRat_range (d : DecoSet E n ST SG) (y : UAd hc n)
    (hy : decoOf ST SG (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = d) (γ : URat hc n) :
    γ ∈ (stabRat hc n ST SG H d).range ↔
      Formalism.UG.bc (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ : GL (Fin n) E) ∈
        (levU hc n ST SG H).map (MulAut.conj (y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))).toMonoidHom := by
  constructor
  · rintro ⟨a, rfl⟩
    have ha : decoOf ST SG (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
        a.1 • decoOf ST SG (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
      rw [hy]; exact a.2.symm
    obtain ⟨γ', k, h1, -, e⟩ := rlc_rel_of_orbit hc n ST SG H a.1 ha
    have hγ : γ' = stabRat hc n ST SG H d a :=
      (ratHom_bijective hc n).1 (h1.trans (rlc_ratHom_stabRat hc n ST SG H d a).symm)
    refine ⟨k.1, k.2, ?_⟩
    rw [← hγ]
    show (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * k.1 * (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ = _
    have e' : Formalism.UG.bc (iA F E) (γ' : GL (Fin n) E) = (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * k.1 *
        (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ := by
      exact eq_mul_inv_of_mul_eq (eq_mul_inv_iff_mul_eq.1 e).symm
    exact e'.symm
  · rintro ⟨k, hk, e⟩
    have e' : (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * k * (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ =
        Formalism.UG.bc (iA F E) (γ : GL (Fin n) E) := e
    have h1 := rlc_decoOf_sm hc n ST SG H γ ⟨k, hk⟩ y
    have h2 : Formalism.UG.bc (iA F E) (γ : GL (Fin n) E) * (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * k⁻¹ =
        (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
      rw [← e']; group
    have h3 : ((ratHom hc n γ, levRed hc n ST SG H ⟨k, hk⟩) : UF E n × H) • d = d := by
      have h1' : decoOf ST SG (Formalism.UG.bc (iA F E) (γ : GL (Fin n) E) * (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * k⁻¹) =
        ((ratHom hc n γ, levRed hc n ST SG H ⟨k, hk⟩) : UF E n × H) •
          decoOf ST SG (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := h1
      rw [h2, hy] at h1'
      exact h1'.symm
    refine ⟨⟨_, h3⟩, ?_⟩
    exact (ratHom_bijective hc n).1 (rlc_ratHom_stabRat hc n ST SG H d ⟨_, h3⟩)

theorem rlc_ratHom_apply (γ : URat hc n) (x : Fin n → E) :
    ((ratHom hc n γ : UF E n) : Sp E n ≃ₗ[E] Sp E n) x = ((γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ x := by
  simp [ratHom, Formalism.UG.glEquiv]

theorem stabRat_lat (d : DecoSet E n ST SG) (a : MulAction.stabilizer (UF E n × H) d) (x : Fin n → E) :
    x ∈ d.1.L ↔ (((stabRat hc n ST SG H d a : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ x) ∈ d.1.L := by
  have h0 : a.1 • d = d := MulAction.mem_stabilizer_iff.1 a.2
  have h1 : (a.1 • d).1.L = d.1.L := by rw [h0]
  rw [rlc_smul_val, Deco.L_act] at h1
  rw [← rlc_ratHom_apply, rlc_ratHom_stabRat]
  conv_rhs => rw [← h1]
  rw [mem_gmap, LinearEquiv.symm_apply_apply]

end Cls

section Base

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Pl E))

theorem base_L : (Deco.base E n ST SG).L = baseLb E n ST := rfl

theorem base_Lsh : (Deco.base E n ST SG).Lsh = baseSh E n ST := rfl

theorem rlc_dualSet (L : Submodule (𝓞 E) (Fin n → E)) :
    Formalism.BasicNotions.dualSet (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) L =
      (Formalism.HermitianLatticesTheory.dual (hStd E n) L : Set (Fin n → E)) := by
  ext y
  show (∀ x ∈ L, Formalism.UG.hform (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) x y ∈ (algebraMap (𝓞 E) E).range) ↔
    y ∈ Formalism.HermitianLatticesTheory.dual (hStd E n) L
  rw [mem_dual]
  refine forall₂_congr fun x _ => ?_
  rw [Submodule.mem_one, hform_one]
  rfl

theorem rlc_span_dualSet (L : Submodule (𝓞 E) (Fin n → E)) :
    Submodule.span (𝓞 E) (Formalism.BasicNotions.dualSet (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) L) =
      Formalism.HermitianLatticesTheory.dual (hStd E n) L := by
  rw [rlc_dualSet, Submodule.span_eq]

theorem baseDual_eq : baseDual hc n ST = baseSh E n ST := rlc_span_dualSet hc n _

theorem baseLb_lattice : Submodule.IsLattice E (baseLb E n ST) :=
  (Deco.base_ok (E := E) (n := n) (ST := ST) (SG := ∅)).L_lattice

theorem baseLb_fin : Module.Finite (𝓞 E) (baseLb E n ST) := Module.Finite.iff_fg.2 (baseLb_lattice n ST).fg

theorem baseLb_span : Submodule.span E (baseLb E n ST : Set (Fin n → E)) = ⊤ := (baseLb_lattice n ST).span_eq_top

theorem baseLb_int : ∀ x ∈ baseLb E n ST,
    x ∈ Formalism.BasicNotions.dualSet (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) (baseLb E n ST) := by
  intro x hx
  rw [rlc_dualSet]
  exact (Deco.base_ok (E := E) (n := n) (ST := ST) (SG := ∅)).L_le_Lsh hx

theorem baseLb_dual {T : ℕ} {pi : 𝓞 E} (hpi : ∀ P ∈ ST, pi ∈ P.asIdeal) (hT : pi * cO E pi = (T : 𝓞 E)) :
    ∀ y ∈ Formalism.BasicNotions.dualSet (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) (baseLb E n ST),
      (T : E) • y ∈ baseLb E n ST := by
  intro y hy
  rw [rlc_dualSet] at hy
  have h := (Deco.base_ok (E := E) (n := n) (ST := ST) (SG := ∅)).smul_Lsh_mem_L (pi := pi) (fun P => hpi P.1 P.2) hy
  rw [hT] at h
  have e : ((T : 𝓞 E) • y : Fin n → E) = (T : E) • y := by
    rw [← algebraMap_smul E (T : 𝓞 E) y, map_natCast]
  rw [← e]
  exact h

theorem rlc_relIndex (L M : Submodule (𝓞 E) (Fin n → E)) :
    L.toAddSubgroup.relIndex M.toAddSubgroup = Nat.card (M ⧸ L.submoduleOf M) := rfl

theorem baseLb_index (hcj : ∀ P Q : ST, Q.1 ≠ conjPrime₂ P.1) :
    (baseLb E n ST).toAddSubgroup.relIndex
      (Submodule.span (𝓞 E) (Formalism.BasicNotions.dualSet (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) (baseLb E n ST))).toAddSubgroup =
      ∏ P : ST, Nat.card (𝓞 E ⧸ P.1.asIdeal) ^ 2 := by
  rw [rlc_span_dualSet, rlc_relIndex]
  exact (Deco.base_ok (E := E) (n := n) (ST := ST) (SG := ∅)).card_Lsh_quot_L hcj

end Base

section Hat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Pl E))

theorem rlc_mem_baseLb (x : Fin n → E) :
    x ∈ baseLb E n ST ↔ ∃ r : Fin n → 𝓞 E, (∀ i, algebraMap (𝓞 E) E (r i) = x i) ∧ ∀ P ∈ ST, r (lastIdx n) ∈ P.asIdeal := by
  classical
  have hok := Deco.base_ok (E := E) (n := n) (ST := ST) (SG := ∅)
  have hf : ∀ (r : Fin n → 𝓞 E), (∀ i, algebraMap (𝓞 E) E (r i) = x i) → ∀ P : ST,
      (Deco.base E n ST (∅ : Finset (Pl E))).f P x = Ideal.Quotient.mk P.1.asIdeal (r (lastIdx n)) := by
    intro r hr P
    have hx : x ∈ stdLat E n := (mem_stdLat x).2 fun i => ⟨r i, hr i⟩
    show (if x ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (stdLat E n) then redP P.1 (x (lastIdx n)) else 0) = _
    rw [if_pos (le_locP _ _ hx), ← hr, reduction_coe]
  unfold baseLb
  rw [hok.mem_L]
  constructor
  · rintro ⟨hx, h0⟩
    choose r hr using (mem_stdLat x).1 hx
    refine ⟨r, hr, fun P hP => ?_⟩
    have := h0 ⟨P, hP⟩
    rw [hf r hr] at this
    exact Ideal.Quotient.eq_zero_iff_mem.1 this
  · rintro ⟨r, hr, h0⟩
    refine ⟨(mem_stdLat x).2 fun i => ⟨r i, hr i⟩, fun P => ?_⟩
    rw [hf r hr]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (h0 P.1 P.2)

def rlc_I (ST : Finset (Pl E)) : Ideal (𝓞 E) := ST.inf fun P => P.asIdeal

theorem rlc_mem_I (a : 𝓞 E) : a ∈ rlc_I ST ↔ ∀ P ∈ ST, a ∈ P.asIdeal := Submodule.mem_finsetInf

theorem rlc_I_ne_bot : rlc_I ST ≠ ⊥ := by
  intro h
  have h1 : ∏ P ∈ ST, P.asIdeal ≤ rlc_I ST := Ideal.prod_le_inf
  rw [h, le_bot_iff] at h1
  exact (Finset.prod_ne_zero_iff.2 fun P _ => P.ne_bot) h1

theorem rlc_resS_of_mem {P : Pl E} {t : Formalism.L2.Herm.intAf F E} (h : t ∈ Formalism.L2.DIV.idS F P.asIdeal) :
    Formalism.L2.DIV.resS F P t = 0 := by
  unfold Formalism.L2.DIV.resS
  rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 h, map_zero]

theorem rlc_mem_idS_I {t : Formalism.L2.Herm.intAf F E} (h : ∀ P ∈ ST, Formalism.L2.DIV.resS F P t = 0) :
    t ∈ Formalism.L2.DIV.idS F (rlc_I ST) := by
  obtain ⟨q, hq⟩ := Formalism.L2.DIV.cmpS_surj (F := F) (rlc_I ST) (rlc_I_ne_bot ST) (Ideal.Quotient.mk _ t)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hq' : Ideal.Quotient.mk (Formalism.L2.DIV.idS F (rlc_I ST)) (Formalism.L2.DIV.oToS F E a) = Ideal.Quotient.mk _ t := hq
  have hd : Formalism.L2.DIV.oToS F E a - t ∈ Formalism.L2.DIV.idS F (rlc_I ST) := Ideal.Quotient.eq.1 hq'
  have ha : a ∈ rlc_I ST := by
    rw [rlc_mem_I]
    intro P hP
    have hle : Formalism.L2.DIV.idS F (rlc_I ST) ≤ Formalism.L2.DIV.idS F P.asIdeal :=
      Ideal.map_mono (Finset.inf_le (f := fun P : Pl E => P.asIdeal) hP)
    have h1 := rlc_resS_of_mem (hle hd)
    rw [map_sub, h P hP, sub_zero, Formalism.L2.DIV.resS_oToS] at h1
    exact Ideal.Quotient.eq_zero_iff_mem.1 h1
  have h2 : Formalism.L2.DIV.oToS F E a ∈ Formalism.L2.DIV.idS F (rlc_I ST) := Ideal.mem_map_of_mem _ ha
  have : t = Formalism.L2.DIV.oToS F E a - (Formalism.L2.DIV.oToS F E a - t) := by ring
  rw [this]
  exact Ideal.sub_mem _ h2 hd

theorem rlc_single_mem (i : Fin n) (a : 𝓞 E) (h : i = lastIdx n → ∀ P ∈ ST, a ∈ P.asIdeal) :
    (Pi.single i (iA F E (algebraMap (𝓞 E) E a)) : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) ∈
      Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (baseLb E n ST) := by
  classical
  refine Submodule.subset_span ⟨Pi.single i (algebraMap (𝓞 E) E a), ?_, ?_⟩
  · refine (rlc_mem_baseLb n ST _).2 ⟨Pi.single i a, fun j => ?_, fun P hP => ?_⟩
    · by_cases hj : j = i
      · subst hj; simp
      · simp [Pi.single_eq_of_ne hj]
    · by_cases hj : lastIdx n = i
      · rw [hj, Pi.single_eq_same]; exact h hj.symm P hP
      · rw [Pi.single_eq_of_ne hj]; exact Ideal.zero_mem _
  · funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Pi.single_eq_of_ne hj]

theorem rlc_single_smul (i : Fin n) (c : Formalism.L2.Herm.intAf F E) (t : E ⊗[F] Formalism.L2.Herm.Af F) :
    (Pi.single i ((c : E ⊗[F] Formalism.L2.Herm.Af F) * t) : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) = c • Pi.single i t := by
  classical
  funext j
  by_cases hj : j = i
  · subst hj
    show _ = (c : E ⊗[F] Formalism.L2.Herm.Af F) * _
    simp
  · show _ = (c : E ⊗[F] Formalism.L2.Herm.Af F) * _
    simp [Pi.single_eq_of_ne hj]

theorem rlc_mem_hat_baseLb (z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) :
    z ∈ Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (baseLb E n ST) ↔
      ∃ h : ∀ i, z i ∈ Formalism.L2.Herm.intAf F E, ∀ P ∈ ST, Formalism.L2.DIV.resS F P ⟨z (lastIdx n), h _⟩ = 0 := by
  classical
  constructor
  · intro hz
    refine Submodule.span_induction (p := fun z _ => ∃ h : ∀ i, z i ∈ Formalism.L2.Herm.intAf F E,
      ∀ P ∈ ST, Formalism.L2.DIV.resS F P ⟨z (lastIdx n), h _⟩ = 0) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨r, hr, h0⟩ := (rlc_mem_baseLb n ST x).1 hx
      refine ⟨fun i => by show iA F E (x i) ∈ _; rw [← hr]; exact iA_mem _, fun P hP => ?_⟩
      have e : (⟨iA F E (x (lastIdx n)), by rw [← hr]; exact iA_mem _⟩ : Formalism.L2.Herm.intAf F E) =
          Formalism.L2.DIV.oToS F E (r (lastIdx n)) :=
        Subtype.ext (show iA F E (x (lastIdx n)) = iA F E (algebraMap (𝓞 E) E (r (lastIdx n))) by rw [hr])
      show Formalism.L2.DIV.resS F P ⟨iA F E (x (lastIdx n)), _⟩ = 0
      rw [e, Formalism.L2.DIV.resS_oToS]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (h0 P hP)
    · exact ⟨fun _ => Subring.zero_mem _, fun P _ => map_zero (Formalism.L2.DIV.resS F P)⟩
    · rintro a b _ _ ⟨ha, ha0⟩ ⟨hb, hb0⟩
      refine ⟨fun i => Subring.add_mem _ (ha i) (hb i), fun P hP => ?_⟩
      have e : (⟨(a + b) (lastIdx n), Subring.add_mem _ (ha _) (hb _)⟩ : Formalism.L2.Herm.intAf F E) =
          ⟨a (lastIdx n), ha _⟩ + ⟨b (lastIdx n), hb _⟩ := rfl
      rw [e, map_add, ha0 P hP, hb0 P hP, add_zero]
    · rintro c a _ ⟨ha, ha0⟩
      refine ⟨fun i => Subring.mul_mem _ c.2 (ha i), fun P hP => ?_⟩
      have e : (⟨(c • a) (lastIdx n), Subring.mul_mem _ c.2 (ha _)⟩ : Formalism.L2.Herm.intAf F E) =
          c * ⟨a (lastIdx n), ha _⟩ := rfl
      rw [e, map_mul, ha0 P hP, mul_zero]
  · rintro ⟨h, h0⟩
    have hsum : z = ∑ i, Pi.single i (z i) := by
      funext j
      rw [Finset.sum_apply, Finset.sum_eq_single j]
      · simp
      · intro i _ hij; exact Pi.single_eq_of_ne hij.symm _
      · intro hj; exact absurd (Finset.mem_univ _) hj
    rw [hsum]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : i = lastIdx n
    · subst hi
      have ht := rlc_mem_idS_I ST h0
      have hmap : Formalism.L2.DIV.idS F (rlc_I ST) = Ideal.span (Formalism.L2.DIV.oToS F E '' (rlc_I ST : Set (𝓞 E))) := rfl
      rw [hmap] at ht
      suffices key : ∀ t ∈ Ideal.span (Formalism.L2.DIV.oToS F E '' (rlc_I ST : Set (𝓞 E))),
          (Pi.single (lastIdx n) (t : E ⊗[F] Formalism.L2.Herm.Af F) : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) ∈
            Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (baseLb E n ST) from key _ ht
      intro t ht'
      refine Submodule.span_induction (p := fun (t : Formalism.L2.Herm.intAf F E) _ => (Pi.single (lastIdx n) (t : E ⊗[F] Formalism.L2.Herm.Af F) :
        Fin n → E ⊗[F] Formalism.L2.Herm.Af F) ∈
        Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (baseLb E n ST)) ?_ ?_ ?_ ?_ ht'
      · rintro _ ⟨a, ha, rfl⟩
        exact rlc_single_mem n ST _ a fun _ => (rlc_mem_I ST a).1 ha
      · show (Pi.single (lastIdx n) (0 : E ⊗[F] Formalism.L2.Herm.Af F) : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) ∈ _
        rw [Pi.single_zero]; exact Submodule.zero_mem _
      · intro a b _ _ ha hb
        show (Pi.single (lastIdx n) ((a : E ⊗[F] Formalism.L2.Herm.Af F) + b) : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) ∈ _
        rw [Pi.single_add]; exact Submodule.add_mem _ ha hb
      · intro c a _ ha
        show (Pi.single (lastIdx n) ((c : E ⊗[F] Formalism.L2.Herm.Af F) * a) : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) ∈ _
        rw [rlc_single_smul]; exact Submodule.smul_mem _ c ha
    · have h1 := rlc_single_mem (F := F) n ST i 1 fun h' => absurd h' hi
      have h2 := Submodule.smul_mem _ (⟨z i, h i⟩ : Formalism.L2.Herm.intAf F E) h1
      rw [← rlc_single_smul, map_one, map_one, mul_one] at h2
      exact h2

theorem decoRaw_L {x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hx : x ∈ UAd hc n) :
    (decoRaw ST SG x).L = Formalism.UG.CS.globLat x (baseLb E n ST) := by
  classical
  have hok := decorated_lattice_exists hc n ST SG x hx
  ext v
  rw [hok.mem_L]
  have hg : v ∈ Formalism.UG.CS.globLat x (baseLb E n ST) ↔
      pullV x v ∈ Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (baseLb E n ST) := Iff.rfl
  rw [hg, rlc_mem_hat_baseLb]
  have hf : ∀ (h : ∀ i, pullV x v i ∈ Formalism.L2.Herm.intAf F E) (P : ST),
      (decoRaw ST SG x).f P v = Formalism.L2.DIV.resS F P.1 ⟨pullV x v (lastIdx n), h _⟩ := by
    intro h P
    have hv : v ∈ Formalism.UG.CS.globLat x (stdLat E n) := (mem_globLat x v).2 h
    show (if v ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (Formalism.UG.CS.globLat x (stdLat E n)) then
      redA P.1 (pullV x v (lastIdx n)) else 0) = _
    rw [if_pos (le_locP _ _ hv), redA_int]
  constructor
  · rintro ⟨hN, h0⟩
    have h := (mem_globLat x v).1 hN
    exact ⟨h, fun P hP => by rw [← hf h ⟨P, hP⟩]; exact h0 ⟨P, hP⟩⟩
  · rintro ⟨h, h0⟩
    exact ⟨(mem_globLat x v).2 h, fun P => by rw [hf h P]; exact h0 P.1 P.2⟩

theorem decoRaw_carries {x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hx : x ∈ UAd hc n) :
    Formalism.L2.Herm.Carries x (baseLb E n ST) (decoRaw ST SG x).L := by
  rw [decoRaw_L hc n ST SG hx]
  intro z
  exact Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.integral_adele_approximation_holds F E (Fin n) (baseLb E n ST) (baseLb_fin n ST)
    (baseLb_span n ST) x z

theorem levU_y_lat (hS : DecoPtSurj hc n ST SG) (d : DecoSet E n ST SG) (x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    x ∈ Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) d.1.L ↔
    ((((ptOf hc n ST SG d : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))⁻¹ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
      Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ x ∈
      Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) (baseLb E n ST) := by
  have h := decoRaw_carries hc n ST SG (ptOf hc n ST SG d).2 x
  rw [← rlc_decoOf_val hc n ST SG (ptOf hc n ST SG d).2, decoOf_ptOf hc n ST SG hS] at h
  exact h

end Hat

section Fin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Pl E)) (H : Subgroup (GLG E n SG))

theorem decoCl_finite (hE : PosStar E) : Finite (DecoCl n ST SG H) := by
  have h := DecoSet.finite_orbits (ST := ST) (SG := SG) (n := n) hE ((⊤ : Subgroup (UF E n)).prod H)
    (fun g => ⟨Subgroup.mem_top _, Subgroup.one_mem _⟩)
  have hrel : ∀ d d' : DecoSet E n ST SG,
      (MulAction.orbitRel ((⊤ : Subgroup (UF E n)).prod H) (DecoSet E n ST SG)) d d' →
      (MulAction.orbitRel (UF E n × H) (DecoSet E n ST SG)) d d' := by
    intro d d' hdd
    obtain ⟨a, ha⟩ := MulAction.orbitRel_apply.1 hdd
    exact MulAction.orbitRel_apply.2 ⟨(a.1.1, ⟨a.1.2, a.2.2⟩), ha⟩
  refine Finite.of_surjective (Quotient.map' (s₁ := MulAction.orbitRel ((⊤ : Subgroup (UF E n)).prod H) (DecoSet E n ST SG))
    (s₂ := MulAction.orbitRel (UF E n × H) (DecoSet E n ST SG)) id hrel) ?_
  intro c
  induction c using Quotient.inductionOn' with
  | h d => exact ⟨Quotient.mk'' d, rfl⟩

theorem adCl_finite (hE : PosStar E) : Finite (AdCl hc n ST SG H) :=
  have := decoCl_finite n ST SG H hE
  Finite.of_injective _ (adToCls_injective hc n ST SG H)

theorem adToCls_one : adToCls hc n ST SG H (Quotient.mk'' (1 : UAd hc n)) = decoCls n ST SG H (DecoSet.base E n ST SG) := by
  rw [adToCls_mk]
  exact congrArg _ (decoOf_one ST SG)

end Fin

section AtPrimes

variable {X : Fields} {Pr : Primes X} (hc : Formalism.BasicNotions.CMData X.F X.E) (n : ℕ) [NeZero n]

theorem colBase_dual (hPr : Pr.Ok) (u : Pr.Word) :
    ∀ y ∈ Formalism.BasicNotions.dualSet (hc.sig : X.E →+* X.E) (1 : Matrix (Fin n) (Fin n) X.E) (baseLb X.E n (Pr.vT u)),
      (Pr.T u : X.E) • y ∈ baseLb X.E n (Pr.vT u) :=
  baseLb_dual hc n (Pr.vT u) (fun _ hP => decoFin_mem_of_mem_divs hP) (hPr.piT_norm u)

theorem colBase_index (hPr : Pr.Ok) (u : Pr.Word) :
    (baseLb X.E n (Pr.vT u)).toAddSubgroup.relIndex
      (Submodule.span (𝓞 X.E) (Formalism.BasicNotions.dualSet (hc.sig : X.E →+* X.E) (1 : Matrix (Fin n) (Fin n) X.E)
        (baseLb X.E n (Pr.vT u)))).toAddSubgroup = Pr.T u ^ (2 * X.f) := by
  rw [rlc_span_dualSet, rlc_relIndex]
  exact card_Lsh_quot_L_of_ok hPr u (DecoSet.base X.E n (Pr.vT u) Pr.vGs)

end AtPrimes

end Formalism.L2.Col
